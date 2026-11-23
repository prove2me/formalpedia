-- Prove2me | solution 1 for GlobalTheory.FinEt.IsSplitOfRank.exists_of_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:13.929814+00:00
-- url     : https://prove2.me/submissions/cdba6fe3-51ff-42d4-9f55-6a42fe734017

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_iff
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_succ

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
theorem _root_.solution {X S : Scheme.{u}} {p : X ⟶ S} {n : ℕ}
    (h : IsSplitOfRank p (n + 1)) :
    ∃ (σ : S ⟶ X) (_ : IsOpenImmersion σ) (V : X.Opens), σ ≫ p = 𝟙 S ∧
      Set.range V.ι = (Set.range σ)ᶜ ∧ IsSplitOfRank (V.ι ≫ p) n := by
  rw [isSplitOfRank_iff] at h
  obtain ⟨s, hs, ho, hx⟩ := h
  let V : X.Opens := ⨆ i : Fin n, (s i.succ).opensRange
  have hV (x : X) : x ∈ Set.range V.ι ↔ ∃ i : Fin n, x ∈ Set.range (s i.succ) := by
    rw [Scheme.Opens.range_ι]
    exact Opens.mem_iSup
  have hle (i : Fin n) : Set.range (s i.succ) ⊆ Set.range V.ι := fun x hx ↦ (hV x).mpr ⟨i, hx⟩
  have hfac (i : Fin n) := IsOpenImmersion.lift_fac V.ι (s i.succ) (hle i)
  refine ⟨s 0, ho 0, V, hs 0, ?_, ?_⟩
  · ext x
    rw [hV]
    constructor
    · rintro ⟨i, hi⟩ h0
      exact Fin.succ_ne_zero i ((hx x).unique hi h0)
    · intro h0
      obtain ⟨i, hi⟩ := (hx x).exists
      induction i using Fin.cases
      · exact (h0 hi).elim
      · exact ⟨_, hi⟩
  rw [isSplitOfRank_iff]
  refine ⟨fun i ↦ IsOpenImmersion.lift V.ι (s i.succ) (hle i), fun i ↦ ?_, fun i ↦ ?_,
    fun v ↦ ?_⟩
  · rw [← Category.assoc, hfac, hs]
  · have : IsOpenImmersion (IsOpenImmersion.lift V.ι (s i.succ) (hle i) ≫ V.ι) := by
      rw [hfac]; exact ho _
    exact IsOpenImmersion.of_comp _ V.ι
  have key (i : Fin n) : v ∈ Set.range (IsOpenImmersion.lift V.ι (s i.succ) (hle i)) ↔
      V.ι v ∈ Set.range (s i.succ) := by
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [← Scheme.Hom.comp_apply, hfac]⟩
    · rintro ⟨y, hy⟩
      refine ⟨y, V.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hfac, hy]
  simp only [key]
  obtain ⟨i, hi⟩ := (hV _).mp ⟨v, rfl⟩
  exact ⟨i, hi, fun j hj ↦ Fin.succ_injective _ ((hx _).unique hj hi)⟩
end IsSplitOfRank
end GlobalTheory.FinEt
