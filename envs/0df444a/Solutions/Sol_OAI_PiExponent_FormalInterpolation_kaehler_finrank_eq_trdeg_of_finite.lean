-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.kaehler_finrank_eq_trdeg_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:50:53.332269+00:00
-- url     : https://prove2.me/submissions/a0acd575-a49e-47b3-9671-73eedf00deab

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib
open scoped KaehlerDifferential

namespace A3S50KT
open Algebra MvPolynomial

theorem main {K : Type*} [Field K] [Algebra Complex K] {ι : Type*} [Fintype ι] (x : ι → K)
    (hx : IsTranscendenceBasis Complex x) :
    Module.finrank K (Ω[K⁄Complex]) = Fintype.card ι := by
  classical
  let P := MvPolynomial ι Complex
  let L := FractionRing P
  have hinj : Function.Injective (aeval x : P →ₐ[Complex] K) :=
    algebraicIndependent_iff_injective_aeval.1 hx.1
  let φ : L →ₐ[Complex] K := IsFractionRing.liftAlgHom (K := L) hinj
  letI : Algebra L K := φ.toRingHom.toAlgebra
  haveI : IsScalarTower Complex L K := IsScalarTower.of_algebraMap_eq fun c => by
    change _ = φ (algebraMap Complex L c); rw [φ.commutes]
  -- K algebraic over L
  let Rx := Algebra.adjoin Complex (Set.range x)
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
  have h1 := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale Complex L K).finrank_eq
  have h2 := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale Complex P L).finrank_eq
  rw [← h1, Module.finrank_baseChange, ← h2, Module.finrank_baseChange,
    Module.finrank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis Complex ι)]

end A3S50KT

theorem solution {K : Type*} [Field K] [Algebra Complex K]
    (hfin : Algebra.trdeg Complex K < Cardinal.aleph0) :
    Module.finrank K (Ω[K⁄Complex]) = (Algebra.trdeg Complex K).toNat := by
  classical
  obtain ⟨u, hu⟩ := exists_isTranscendenceBasis Complex K
  have hc := hu.cardinalMk_eq_trdeg
  have hfu : u.Finite := by
    rw [← Set.finite_coe_iff, ← Cardinal.mk_lt_aleph0_iff, hc]; exact hfin
  haveI : Fintype u := hfu.fintype
  rw [A3S50KT.main _ hu, ← hc, Cardinal.mk_fintype, Cardinal.toNat_natCast]
