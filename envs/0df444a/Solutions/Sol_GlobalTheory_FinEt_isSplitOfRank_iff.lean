-- Prove2me | solution 1 for GlobalTheory.FinEt.isSplitOfRank_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:39.134587+00:00
-- url     : https://prove2.me/submissions/d5dc223e-74d0-4f95-b84b-3d1bdea29d4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_iff_exists_iso

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
theorem _root_.solution {X S : Scheme.{u}} (p : X ⟶ S) (n : ℕ) :
    IsSplitOfRank p n ↔ ∃ s : Fin n → (S ⟶ X), (∀ i, s i ≫ p = 𝟙 S) ∧
      (∀ i, IsOpenImmersion (s i)) ∧ ∀ x : X, ∃! i, x ∈ Set.range (s i) := by
  constructor
  · rw [isSplitOfRank_iff_exists_iso]
    rintro ⟨e, he⟩
    refine ⟨fun i ↦ Sigma.ι (fun _ : Fin n ↦ S) i ≫ e.hom, fun i ↦ by simp [he],
      fun i ↦ inferInstance, fun x ↦ ?_⟩
    obtain ⟨x, rfl⟩ := e.hom.surjective x
    obtain ⟨i, y, hy⟩ := (sigmaOpenCover fun _ : Fin n ↦ S).exists_eq x
    obtain rfl : Sigma.ι (fun _ : Fin n ↦ S) i y = x := hy
    refine ⟨i, ⟨y, Scheme.Hom.comp_apply _ _ _⟩, ?_⟩
    rintro j ⟨z, hz⟩
    rw [Scheme.Hom.comp_apply] at hz
    have := (sigmaι_eq_iff _ _ _ _ _).mp (e.hom.isOpenEmbedding.injective hz)
    exact congr(($this).1)
  · rintro ⟨s, hs, ho, hx⟩
    refine ⟨s, hs, nonempty_isColimit_cofanMk_of s ?_ ?_⟩
    · rw [eq_top_iff]
      intro x _
      obtain ⟨i, hi⟩ := (hx x).exists
      exact Opens.mem_iSup.mpr ⟨i, hi⟩
    · intro i j hij
      rw [Function.onFun, disjoint_iff, eq_bot_iff]
      rintro x ⟨hi, hj⟩
      exact (hij ((hx x).unique hi hj)).elim
end GlobalTheory.FinEt
