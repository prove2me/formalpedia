-- Prove2me | solution 1 for GlobalTheory.FinEt.IsSplitOfRank.succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:09.94294+00:00
-- url     : https://prove2.me/submissions/3ab86a5d-8594-40f3-a0b3-feaa4e410666

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}
namespace GlobalTheory.FinEt
namespace IsSplitOfRank
theorem _root_.solution {X V S : Scheme.{u}} {p : X ⟶ S} (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S)
    [IsOpenImmersion σ] (j : V ⟶ X) [IsOpenImmersion j] (hj : Set.range j = (Set.range σ)ᶜ)
    {n : ℕ} (h : IsSplitOfRank (j ≫ p) n) : IsSplitOfRank p (n + 1) := by
  rw [isSplitOfRank_iff] at h ⊢
  obtain ⟨s, hs, ho, hx⟩ := h
  refine ⟨Fin.cons σ fun i ↦ s i ≫ j, fun i ↦ ?_, fun i ↦ ?_, fun x ↦ ?_⟩
  · induction i using Fin.cases <;> simp [hσ, hs]
  · induction i using Fin.cases
    · simpa
    · simp only [Fin.cons_succ]; infer_instance
  by_cases hxσ : x ∈ Set.range σ
  · refine ⟨0, by simpa using hxσ, fun i hi ↦ ?_⟩
    induction i using Fin.cases
    · rfl
    · simp only [Fin.cons_succ] at hi
      obtain ⟨y, rfl⟩ := hi
      rw [Scheme.Hom.comp_apply] at hxσ
      exact ((hj.le ⟨_, rfl⟩) hxσ).elim
  · obtain ⟨v, rfl⟩ := hj.ge hxσ
    obtain ⟨i, ⟨y, rfl⟩, hi⟩ := hx v
    refine ⟨i.succ, ?_, fun k hk ↦ ?_⟩
    · simp only [Fin.cons_succ]
      exact ⟨y, Scheme.Hom.comp_apply _ _ _⟩
    induction k using Fin.cases
    · exact (hxσ (by simpa using hk)).elim
    · simp only [Fin.cons_succ] at hk
      obtain ⟨z, hz⟩ := hk
      rw [Scheme.Hom.comp_apply] at hz
      rw [hi _ ⟨z, j.isOpenEmbedding.injective hz⟩]
end IsSplitOfRank
end GlobalTheory.FinEt
