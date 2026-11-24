-- Prove2me | solution 1 for GlobalTheory.ClassMin.finite_affine_sublevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:27:48.368717+00:00
-- url     : https://prove2.me/submissions/2da67603-20fd-47df-bbd0-58a3bb7b2ae7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_exists_mul_sum_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Matrix Filter
open scoped TensorProduct
variable {X : Type*} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  {Q : QuadraticMap ℤ X ℝ}
namespace GlobalTheory.ClassMin
theorem _root_.solution (hQ : (realExtension Q).PosDef) {t : ℝ} (ht : 0 < t) (ν : X →+ ℝ)
    (r : ℝ) : {x | t * Q x + ν x ≤ r}.Finite := by
  let e := Module.Free.chooseBasis ℤ X
  obtain ⟨c, hc, h⟩ := exists_mul_sum_sq_le hQ e
  have hs : 0 < t * c := mul_pos ht hc
  set s := t * c with hsdef
  obtain ⟨K, hK⟩ := exists_int_gt ((r + ∑ i, ν (e i) ^ 2 / (2 * s)) / (s / 2))
  rw [div_lt_iff₀ (by positivity)] at hK
  refine Set.Finite.of_injOn (f := e.equivFun) (t := Set.pi Set.univ fun _ => Set.Icc (-K) K) ?_
    e.equivFun.injective.injOn (Set.Finite.pi fun _ => Set.finite_Icc _ _)
  intro a ha i _
  have hν : ν a = ∑ i, (e.repr a i : ℝ) * ν (e i) := by
    conv_lhs => rw [← e.sum_repr a, map_sum]
    simp only [map_zsmul, zsmul_eq_mul]
  have h1 : s / 2 * ∑ i, (e.repr a i : ℝ) ^ 2 ≤
      s * ∑ i, (e.repr a i : ℝ) ^ 2 + ν a + ∑ i, ν (e i) ^ 2 / (2 * s) := by
    rw [hν, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have : s * (e.repr a j : ℝ) ^ 2 + (e.repr a j : ℝ) * ν (e j) + ν (e j) ^ 2 / (2 * s)
        - s / 2 * (e.repr a j : ℝ) ^ 2 = (s * e.repr a j + ν (e j)) ^ 2 / (2 * s) := by
      field_simp
      ring
    have h0 : 0 ≤ (s * e.repr a j + ν (e j)) ^ 2 / (2 * s) := by positivity
    linarith
  have h2 : s * ∑ i, (e.repr a i : ℝ) ^ 2 ≤ t * Q a := by
    rw [hsdef, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h a) ht.le
  have h3 : (e.repr a i : ℝ) ^ 2 ≤ ∑ i, (e.repr a i : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun i => (e.repr a i : ℝ) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  have ha' : t * Q a + ν a ≤ r := ha
  have h4 : (e.repr a i : ℝ) ^ 2 < K := by
    refine lt_of_mul_lt_mul_left (a := s / 2) ?_ (by positivity)
    nlinarith
  have h5 : (e.repr a i) ^ 2 < K := by exact_mod_cast h4
  rw [Module.Basis.equivFun_apply]
  constructor <;> nlinarith [Int.le_self_sq (e.repr a i), Int.le_self_sq (-e.repr a i)]
end GlobalTheory.ClassMin
