-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.kaehler_finrank_eq_of_finite_transcendence_basis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T06:45:12.753732+00:00
-- url     : https://prove2.me/submissions/f73220bd-99bf-45e3-b99b-5cfda7000be7

import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.FieldTheory.FinTrdeg
import Mathlib
open scoped KaehlerDifferential

namespace A3S51G
open Algebra MvPolynomial

theorem main {k K : Type*} [Field k] [CharZero k] [Field K] [Algebra k K] {ι : Type*} [Fintype ι]
    (x : ι → K) (hx : IsTranscendenceBasis k x) :
    Module.finrank K (Ω[K⁄k]) = Fintype.card ι := by
  classical
  let P := MvPolynomial ι k
  let L := FractionRing P
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  have hinj : Function.Injective (aeval x : P →ₐ[k] K) :=
    algebraicIndependent_iff_injective_aeval.1 hx.1
  let φ : L →ₐ[k] K := IsFractionRing.liftAlgHom (K := L) hinj
  letI : Algebra L K := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k L K := IsScalarTower.of_algebraMap_eq fun c => by
    change _ = φ (algebraMap k L c); rw [φ.commutes]
  let Rx := Algebra.adjoin k (Set.range x)
  let e := hx.1.aevalEquiv
  letI : Algebra Rx L := ((algebraMap P L).comp e.symm.toRingHom).toAlgebra
  haveI : IsScalarTower Rx L K := IsScalarTower.of_algebraMap_eq fun r => by
    change (r : K) = φ (algebraMap P L (e.symm r))
    rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
    conv_lhs => rw [← e.apply_symm_apply r]
    rfl
  haveI : Algebra.IsAlgebraic Rx K := hx.isAlgebraic
  have hRxL : Function.Injective (algebraMap Rx L) :=
    (IsFractionRing.injective P L).comp e.symm.injective
  haveI : Algebra.IsAlgebraic L K := Algebra.IsAlgebraic.extendScalars hRxL
  haveI : Algebra.IsSeparable L K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyEtale L K := Algebra.FormallyEtale.of_isSeparable L K
  haveI : Algebra.FormallyEtale P L := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  have h1 := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k L K).finrank_eq
  have h2 := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k P L).finrank_eq
  rw [← h1, Module.finrank_baseChange, ← h2, Module.finrank_baseChange,
    Module.finrank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis k ι)]

theorem toNat {k K : Type*} [Field k] [CharZero k] [Field K] [Algebra k K]
    (hfin : Algebra.trdeg k K < Cardinal.aleph0) :
    Module.finrank K (Ω[K⁄k]) = (Algebra.trdeg k K).toNat := by
  classical
  obtain ⟨u, hu⟩ := exists_isTranscendenceBasis k K
  have hc := hu.cardinalMk_eq_trdeg
  have hfu : u.Finite := by
    rw [← Set.finite_coe_iff, ← Cardinal.mk_lt_aleph0_iff, hc]; exact hfin
  haveI : Fintype u := hfu.fintype
  rw [main _ hu, ← hc, Cardinal.mk_fintype, Cardinal.toNat_natCast]

end A3S51G

theorem solution {K : Type*} [Field K] [Algebra Complex K] {n : ℕ} {x : Fin n → K}
    (hx : IsTranscendenceBasis Complex x) : Module.finrank K (Ω[K⁄Complex]) = n := by
  simpa using A3S51G.main x hx
