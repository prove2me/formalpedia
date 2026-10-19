-- Prove2me | solution 1 for OAI.MainGap.exists_norming_positive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T10:59:34.667077+00:00
-- url     : https://prove2.me/submissions/0ae929f6-23b5-4ce3-8bc4-d4346338a8af

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/PositiveFunctional.lean:L53-L89
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.exists_norming_positive. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.PositiveFunctional ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

lemma norm_add_one_of_nonneg [Nontrivial A] {d : A} (hd : 0 ≤ d) :
    ‖d + 1‖ = ‖d‖ + 1 := by
  apply le_antisymm
  · simpa using norm_add_le d 1
  have hh := norm_apply_le_norm_cfc (fun t : ℝ => t + 1) d
    (CStarAlgebra.norm_mem_spectrum_of_nonneg (a := d) hd)
  have he : cfc (fun t : ℝ => t + 1) d = d + 1 := by
    rw [cfc_add_const (1 : ℝ) (fun t : ℝ => t) d, cfc_id' ℝ d, map_one]
  simpa only [he, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖d‖ + 1)] using hh

lemma real_norm_one_positive (F : A →L[ℝ] ℝ) (hF : ‖F‖ ≤ 1) (h1 : F 1 = 1)
    {h : A} (hh : 0 ≤ h) : 0 ≤ F h := by
  have hu : h ≤ algebraMap ℝ A ‖h‖ :=
    IsSelfAdjoint.le_algebraMap_norm_self (a := h) (.of_nonneg hh)
  have hp : 0 ≤ algebraMap ℝ A ‖h‖ - h := sub_nonneg.mpr hu
  have hb : ‖algebraMap ℝ A ‖h‖ - h‖ ≤ ‖h‖ :=
    (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _) hp).2 (sub_le_self _ hh)
  have he := F.le_opNorm (algebraMap ℝ A ‖h‖ - h)
  have hx : F (algebraMap ℝ A ‖h‖ - h) = ‖h‖ - F h := by
    rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_eq_mul, mul_one]
  have : F (algebraMap ℝ A ‖h‖ - h) ≤ ‖h‖ :=
    (le_abs_self _).trans (he.trans ((mul_le_mul_of_nonneg_right hF (norm_nonneg _)).trans
      (by simpa using hb)))
  linarith

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_realPartCLM : ‖(realPartCLM : A →L[ℝ] A)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  simpa using realPart.norm_le a

lemma exists_norming_positive [Nontrivial A] {d : A} (hd : 0 ≤ d) :
    ∃ f : A →ₚ[ℂ] ℂ, (∀ a, ‖f a‖ ≤ ‖a‖) ∧ f d = (‖d‖ : ℂ) := by
  obtain ⟨F, hF, hFd⟩ := exists_dual_vector'' ℝ (d + 1)
  have hFa (a : A) : F a ≤ ‖a‖ :=
    (le_abs_self _).trans ((F.le_opNorm a).trans
      (by simpa using mul_le_mul_of_nonneg_right hF (norm_nonneg a)))
  have h1 : F 1 = 1 := by
    rw [map_add, norm_add_one_of_nonneg hd] at hFd
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hFd
    have h1' := hFa 1
    have hd' := hFa d
    simp only [norm_one] at h1'
    linarith
  have hFd' : F d = ‖d‖ := by
    rw [map_add, norm_add_one_of_nonneg hd, h1] at hFd
    simpa only [RCLike.ofReal_real_eq_id, id_eq, add_left_inj] using hFd
  let G : A →L[ℝ] ℝ := F.comp realPartCLM
  let H : A →L[ℂ] ℂ := StrongDual.extendRCLike G
  have hG : ‖G‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hF norm_realPartCLM (norm_nonneg _) zero_le_one).trans (by norm_num))
  have hH (a : A) (ha : IsSelfAdjoint a) : H a = (F a : ℂ) := by
    simp [H, StrongDual.extendRCLike_apply, G, ha.coe_realPart, realPart_I_smul,
      ha.imaginaryPart]
  let f : A →ₚ[ℂ] ℂ :=
    { H.toLinearMap with
      monotone' := fun a b hab => by
        have hn : 0 ≤ H (b - a) := by
          rw [hH _ (.of_nonneg (sub_nonneg.mpr hab))]
          exact_mod_cast real_norm_one_positive F hF h1 (sub_nonneg.mpr hab)
        change H a ≤ H b
        simpa only [map_sub, sub_nonneg] using hn }
  refine ⟨f, fun a => ?_, ?_⟩
  · change ‖H a‖ ≤ ‖a‖
    exact (H.le_opNorm a).trans (by
      simpa [H] using mul_le_mul_of_nonneg_right hG (norm_nonneg a))
  · change H d = _
    rw [hH d (.of_nonneg hd), hFd']
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution : type_of% @_root_.OAI.MainGap.exists_norming_positive := @_root_.OAI.MainGap.exists_norming_positive
