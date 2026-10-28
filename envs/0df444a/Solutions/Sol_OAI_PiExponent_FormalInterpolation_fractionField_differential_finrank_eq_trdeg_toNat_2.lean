-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.fractionField_differential_finrank_eq_trdeg_toNat
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T06:45:32.162982+00:00
-- url     : https://prove2.me/submissions/7058ed07-1a00-48d1-98dc-02d8f08752ed

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib
open scoped BigOperators
open scoped KaehlerDifferential
open OAI.PiExponent.FormalInterpolation

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

namespace A3S51F
theorem fin {m : Nat} (P : Ideal (MvPolynomial (Fin (Nat.succ m)) Complex)) [P.IsPrime] :
    Algebra.trdeg Complex (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P) < Cardinal.aleph0 := by
  classical
  set K := logarithmicPrimeField P
  set R := MvPolynomial (Fin (m + 1)) Complex
  set A := R ⧸ P
  let x : Fin (m + 1) → K := fun i => algebraMap R K (MvPolynomial.X i)
  let t : Set K := Set.range x
  -- every image of a polynomial lies in adjoin ℂ t
  have hmem : ∀ p : R, algebraMap R K p ∈ Algebra.adjoin Complex t := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [show algebraMap R K (MvPolynomial.C a) = algebraMap Complex K a from
        (IsScalarTower.algebraMap_apply Complex R K a).symm]
      exact Subalgebra.algebraMap_mem _ a
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp =>
      rw [map_mul]; exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hA : ∀ a : A, algebraMap A K a ∈ Algebra.adjoin Complex t := by
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : algebraMap A K (Ideal.Quotient.mk P p) = algebraMap R K p := by
      rw [IsScalarTower.algebraMap_apply R A K]; rfl
    rw [this]; exact hmem p
  haveI : Algebra.IsAlgebraic (Algebra.adjoin Complex t) K := by
    constructor
    intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    have hb0 : algebraMap A K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    let a' : Algebra.adjoin Complex t := ⟨_, hA a⟩
    let b' : Algebra.adjoin Complex t := ⟨_, hA b⟩
    refine ⟨Polynomial.C b' * Polynomial.X - Polynomial.C a', ?_, ?_⟩
    · intro h
      have := congrArg (Polynomial.coeff · 1) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
        if_neg one_ne_zero, sub_zero, Polynomial.coeff_zero] at this
      exact hb0 (congrArg Subtype.val this)
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      change algebraMap A K b * (algebraMap A K a / algebraMap A K b) - algebraMap A K a = 0
      rw [mul_div_cancel₀ _ hb0, sub_self]
  refine lt_of_le_of_lt (Algebra.IsAlgebraic.trdeg_le_cardinalMk Complex t) ?_
  exact (Set.finite_range x).lt_aleph0
end A3S51F

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
      (Ω[OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P⁄Complex]) =
      (Algebra.trdeg Complex
        (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)).toNat :=
  A3S51G.toNat (A3S51F.fin P)
