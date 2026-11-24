-- Prove2me | solution 1 for GlobalTheory.ThetaGen.exists_succ_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:43:11.781282+00:00
-- url     : https://prove2.me/submissions/ab420ff4-2889-47b8-bd2f-53f86822f77d

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow
import Theorems.Thm_GlobalTheory_ThetaGen_homog_mul
import Theorems.Thm_GlobalTheory_ThetaGen_mem_of_homog_mem_iSup
import Theorems.Thm_GlobalTheory_ThetaGen_gradedRing_le_iSup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaGen
variable {X : Type}
variable (R : ℕ → Submodule ℂ (X → ℂ))
namespace GlobalTheory.ThetaGen
theorem _root_.solution (h1 : (1 : X → ℂ) ∈ R 0)
    (hmul : ∀ a b, R a * R b ≤ R (a + b)) (A : Subalgebra ℂ (ℂ × X → ℂ))
    (hA : A ≤ Algebra.adjoin ℂ {F | ∃ f ∈ R 1, F = homog 1 f})
    (M : Submodule A (ℂ × X → ℂ)) (hM : M.FG) (hMR : ∀ F, F ∈ M ↔ F ∈ gradedRing R) :
    ∃ e, ∀ d, e ≤ d → R (d + 1) ≤ R 1 * R d := by
  let N : ℕ →o Submodule A (ℂ × X → ℂ) :=
    ⟨fun e => Submodule.span A {F | ∃ d ≤ e, ∃ f ∈ R d, F = homog d f}, fun a b hab =>
      Submodule.span_mono (by
        rintro _ ⟨d, hd, h⟩
        exact ⟨d, hd.trans hab, h⟩)⟩
  have hN : ⨆ e, N e = M := by
    apply le_antisymm
    · refine iSup_le fun e => Submodule.span_le.2 ?_
      rintro _ ⟨d, -, f, hf, rfl⟩
      exact (hMR _).2 (Algebra.subset_adjoin ⟨d, f, hf, rfl⟩)
    · intro F hF
      have := gradedRing_le_iSup R h1 hmul ((hMR F).1 hF)
      clear hF
      induction this using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨d, f, hf, rfl⟩ := hx
        exact Submodule.mem_iSup_of_mem d (Submodule.subset_span ⟨d, le_rfl, f, hf, rfl⟩)
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | smul c x _ hx => exact Submodule.smul_of_tower_mem _ c hx
  obtain ⟨e, he⟩ := hM.stabilizes_of_iSup_eq N hN
  refine ⟨e, fun d hd f hf => ?_⟩
  let T : ℕ → Submodule ℂ (X → ℂ) := fun k => if k ≤ e then R k else R 1 * R (k - 1)
  have hTR : ∀ k, T k ≤ R k := by
    intro k
    simp only [T]
    split_ifs with hk
    · exact le_rfl
    · have := hmul 1 (k - 1)
      rwa [show 1 + (k - 1) = k by omega] at this
  have hRT : ∀ k, R 1 * R k ≤ T (1 + k) := by
    intro k
    simp only [T]
    split_ifs with hk
    · exact hmul 1 k
    · simp
  let W : Submodule ℂ (ℂ × X → ℂ) := ⨆ k, (T k).map (homogL k)
  have hAW : ∀ a ∈ Algebra.adjoin ℂ {F | ∃ f ∈ R 1, F = homog 1 f}, ∀ w ∈ W, a * w ∈ W := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨s, hs, rfl⟩ := hx
      intro w hw
      induction hw using Submodule.iSup_induction' with
      | mem k F hF =>
        obtain ⟨v, hv, rfl⟩ := hF
        refine Submodule.mem_iSup_of_mem (1 + k) ⟨s * v, hRT k (Submodule.mul_mem_mul hs (hTR k hv)), ?_⟩
        exact (homog_mul _ _ _ _).symm
      | zero => simp
      | add F G _ _ hF hG => rw [mul_add]; exact add_mem hF hG
    | algebraMap c => intro w hw; rw [← Algebra.smul_def]; exact W.smul_mem c hw
    | add x y _ _ hx hy => intro w hw; rw [add_mul]; exact add_mem (hx w hw) (hy w hw)
    | mul x y _ _ hx hy => intro w hw; rw [mul_assoc]; exact hx _ (hy w hw)
  have hNW : ∀ F ∈ N e, F ∈ W := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, v, hv, rfl⟩ := hx
      exact Submodule.mem_iSup_of_mem k ⟨v, by simpa [T, hk] using hv, rfl⟩
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact hAW a (hA a.2) x hx
  have hmem : homog (d + 1) f ∈ N e := by
    rw [← he, hMR]
    exact Algebra.subset_adjoin ⟨d + 1, f, hf, rfl⟩
  have := mem_of_homog_mem_iSup T (d + 1) f (hNW _ hmem)
  simpa [T, show ¬ (d + 1 ≤ e) by omega] using this
end GlobalTheory.ThetaGen
