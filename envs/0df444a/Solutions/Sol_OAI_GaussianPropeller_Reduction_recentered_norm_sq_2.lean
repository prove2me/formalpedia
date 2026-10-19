-- Prove2me | solution 2 for OAI.GaussianPropeller.Reduction.recentered_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:44:01.461565+00:00
-- url     : https://prove2.me/submissions/7ca780b9-8ae8-45fb-a959-6426f093c2ad

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Deletion.lean:L65-L98
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.recentered_norm_sq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion

-- ---- from OAI.Probability.GaussianPropeller.Deletion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open scoped RealInnerProductSpace

namespace GaussianPropeller.Reduction

variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
lemma sum_erase_zero (z : Fin k → Space d) (hz : ∑ j, z j = 0) (i : Fin k) :
    ∑ j ∈ Finset.univ.erase i, z j = -z i := by
  classical
  have hh := Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
  rw [hz] at hh
  exact eq_neg_of_add_eq_zero_left hh

omit [NeZero k] in
lemma recentered_norm_sq (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) :
    ‖recentered z i‖^2 = (∑ j, ‖z j‖^2) -
      ((k:ℝ)/((k:ℝ)-1)) * ‖z i‖^2 := by
  classical
  let b : ℝ := ((k:ℝ)-1)⁻¹
  have hk' : (k:ℝ)-1 ≠ 0 := by exact_mod_cast (show (k:ℤ)-1 ≠ 0 by omega)
  have he : ‖recentered z i‖^2 =
      ∑ j ∈ Finset.univ.erase i, ‖z j + b • z i‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ j, ‖if j = i then 0 else z j + b • z i‖^2) = _
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [ite_true, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ite_eq_right (Finset.ne_of_mem_erase hj)]
  rw [he]
  simp_rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hn := Finset.sum_erase_add Finset.univ (fun j => ‖z j‖^2) (Finset.mem_univ i)
  have hi : ∑ j ∈ Finset.univ.erase i, 2 * (b * ⟪z j,z i⟫) = -2*b*‖z i‖^2 := by
    simp_rw [← mul_assoc]
    rw [← Finset.mul_sum, ← sum_inner, sum_erase_zero z hz i, inner_neg_left,
      real_inner_self_eq_norm_sq]
    ring
  rw [hi, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  dsimp [b]
  rw [← hn]
  field_simp
  ring

end GaussianPropeller.Reduction

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.recentered_norm_sq := @_root_.OAI.GaussianPropeller.Reduction.recentered_norm_sq
