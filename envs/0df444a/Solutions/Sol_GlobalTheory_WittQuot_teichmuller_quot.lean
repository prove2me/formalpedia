-- Prove2me | solution 1 for GlobalTheory.WittQuot.teichmuller_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:46:47.809862+00:00
-- url     : https://prove2.me/submissions/d4802c55-fde6-47e5-a31e-4861a75e3802

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursion
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TeichmullerQuot
import Theorems.Thm_ReciprocityTheory_PGsh_a0
import Theorems.Thm_ReciprocityTheory_PGsh_teichSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.WittQuot
private lemma wS_mul (p : ℕ) [hp : Fact p.Prime] (n : ℕ) : (p : MvPolynomial (Fin n) ℤ) * wS p n =
    (∑ j, (MvPolynomial.X j) ^ p) - (∑ j, MvPolynomial.X j) ^ p := by
  set q : MvPolynomial (Fin n) ℤ := (∑ j, (MvPolynomial.X j) ^ p) - (∑ j, MvPolynomial.X j) ^ p with hq
  have hd : MvPolynomial.C (p : ℤ) ∣ q := by
    rw [MvPolynomial.C_dvd_iff_zmod, hq]
    simp only [map_sub, map_sum, map_pow, MvPolynomial.map_X]
    rw [sum_pow_char, sub_self]
  rw [MvPolynomial.C_dvd_iff_dvd_coeff] at hd
  conv_rhs => rw [q.as_sum]
  change _ * ∑ m ∈ q.support, MvPolynomial.monomial m (q.coeff m / (p : ℤ)) = _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← map_natCast (MvPolynomial.C : ℤ →+* _), MvPolynomial.C_mul_monomial,
    Int.mul_ediv_cancel' (hd m)]
private lemma teich_decomp (p : ℕ) [Fact p.Prime] {K : Type} [CommRing K] [CharP K p]
    [PerfectRing K p] (x : WittVector p K) :
    ∃ y : WittVector p K, x = WittVector.teichmuller p (x.coeff 0) + p * y := by
  have hmem : x - WittVector.teichmuller p (x.coeff 0) ∈
      Ideal.span {(p : WittVector p K) ^ 1} := by
    rw [WittVector.mem_span_p_pow_iff_le_coeff_eq_zero,
      ← WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero]
    intro i hi
    obtain rfl : i = 0 := by omega
    rw [WittVector.teichmuller_coeff_zero]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨w, ?_⟩
  rw [pow_one] at hw
  rw [mul_comm, hw]; abel
end GlobalTheory.WittQuot
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WittQuot
namespace GlobalTheory.WittQuot
theorem _root_.solution :
  (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (ϖ : PreTilt O p), ϖ.untilt = (p : O) →
    ∀ (W : Type) [CommRing W] (pr : Ainf.A p O →+* W), Function.Surjective pr →
    RingHom.ker pr = Ideal.span {(p : Ainf.A p O) ^ 2, WittVector.teichmuller p ϖ} →
    (∀ w : W, ∃ c : PreTilt O p, ∃ c' : W, w = pr (WittVector.teichmuller p c) + p * c') ∧
    (∀ (n : ℕ) (a : Fin n → PreTilt O p), ∑ j, pr (WittVector.teichmuller p (a j)) = pr (WittVector.teichmuller p (∑ j, a j)) +
      p * pr (WittVector.teichmuller p (MvPolynomial.eval₂ (Int.castRingHom (PreTilt O p)) (fun j => (frobeniusEquiv (PreTilt O p) p).symm (a j)) (wS p n)))) ∧
    (∀ c : PreTilt O p, WittVector.fontaineTheta O p (WittVector.teichmuller p c) ∈ Ideal.span {(p : O)} → pr (WittVector.teichmuller p c) = 0)) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε ϖ hϖ W _ pr hpr hker
  have hp2 : pr ((p : Ainf.A p O) ^ 2) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.subset_span (by simp)
  have hϖ0 : pr (WittVector.teichmuller p ϖ) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.subset_span (by simp)
  refine ⟨fun w => ?_, fun n a => ?_, fun c hc => ?_⟩
  · obtain ⟨x, rfl⟩ := hpr w
    obtain ⟨y, hy⟩ := teich_decomp p x
    refine ⟨x.coeff 0, pr y, ?_⟩
    conv_lhs => rw [hy]
    rw [map_add, map_mul, map_natCast]
  · obtain ⟨w, hw⟩ := ((teichSum p (Fin n) Finset.univ).2 (PreTilt O p) a (wS p n) (wS_mul p n)).1
    have h := congrArg pr hw
    rw [map_sum, map_add, map_add, map_mul, map_mul, hp2, zero_mul, add_zero, map_natCast] at h
    rw [h, MvPolynomial.aeval_def]
    rfl
  · have hK := ((a0 p C v O hv).2.2.1 ϖ hϖ).2.2
    have hm : WittVector.teichmuller p c ∈
        Ideal.span {(p : WittVector p (PreTilt O p)), WittVector.teichmuller p ϖ} := by
      rw [← hK, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hc
    obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp hm
    have h := congrArg (WittVector.constantCoeff (p := p) (R := PreTilt O p)) hxy
    rw [map_add, map_mul, map_mul, map_natCast, CharP.cast_eq_zero, mul_zero, zero_add] at h
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h
    rw [← h, map_mul, map_mul, hϖ0, mul_zero]
end GlobalTheory.WittQuot
