-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RegSeq.exists_ofList_append_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:06.886707+00:00
-- url     : https://prove2.me/submissions/4fe63a1c-7d13-43a8-973a-3d6c04e3d3e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WeaklyRegularOfCotangentIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing RingTheory.Sequence
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RegSeq
namespace GlobalTheory.CompanionTheory.RegSeq
theorem _root_.solution {R : Type} [CommRing R] [IsRegularLocalRing R] {r : ℕ}
    (f : Fin r → R) (hf : ∀ i, f i ∈ maximalIdeal R)
    (hli : LinearIndependent (ResidueField R)
      (fun i => ((maximalIdeal R).toCotangent ⟨f i, hf i⟩ : CotangentSpace R))) :
    ∃ ys : List R, Ideal.ofList (List.ofFn f ++ ys) = maximalIdeal R ∧
      (List.ofFn f ++ ys).length = (maximalIdeal R).spanFinrank := by
  classical
  let W : Submodule (ResidueField R) (CotangentSpace R) :=
    Submodule.span (ResidueField R) (Set.range (fun i => ((maximalIdeal R).toCotangent ⟨f i, hf i⟩ : CotangentSpace R)))
  let c := Module.finBasis (ResidueField R) (CotangentSpace R ⧸ W)
  have hsurj : ∀ q : CotangentSpace R ⧸ W, ∃ x : maximalIdeal R,
      W.mkQ ((maximalIdeal R).toCotangent x : CotangentSpace R) = q := by
    intro q
    obtain ⟨w, rfl⟩ := W.mkQ_surjective q
    obtain ⟨x, rfl⟩ := (maximalIdeal R).toCotangent_surjective w
    exact ⟨x, rfl⟩
  choose g hg using hsurj
  let s : Set (maximalIdeal R) :=
    Set.range (fun i => (⟨f i, hf i⟩ : maximalIdeal R)) ∪ Set.range (fun j => g (c j))
  let T : Submodule (ResidueField R) (CotangentSpace R) :=
    Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' s)
  have hWT : W ≤ T := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨⟨f i, hf i⟩, Or.inl ⟨i, rfl⟩, rfl⟩
  have hT : T = ⊤ := by
    have h1 : Submodule.map W.mkQ T = ⊤ := by
      rw [eq_top_iff, ← c.span_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨(maximalIdeal R).toCotangent (g (c j)), Submodule.subset_span ⟨g (c j), Or.inr ⟨j, rfl⟩, rfl⟩, hg _⟩
    have h2 := Submodule.comap_map_mkQ W T
    rw [h1, Submodule.comap_top] at h2
    rw [eq_top_iff, h2]
    exact sup_le hWT le_rfl
  have hspan : Submodule.span R s = ⊤ := IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp hT
  have hm : maximalIdeal R = Ideal.span (Subtype.val '' s) := by
    have h3 := congrArg (Submodule.map (maximalIdeal R).subtype) hspan
    rw [Submodule.map_span, Submodule.map_subtype_top, Submodule.coe_subtype] at h3
    exact h3.symm
  refine ⟨List.ofFn (fun j => (g (c j)).val), ?_, ?_⟩
  · apply le_antisymm
    · unfold Ideal.ofList
      rw [Ideal.span_le]
      intro x hx
      have hx' : x ∈ List.ofFn f ++ List.ofFn (fun j => (g (c j)).val) := hx
      rcases List.mem_append.mp hx' with h | h
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
        exact hf i
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
        exact (g (c j)).2
    · refine le_trans hm.le ?_
      unfold Ideal.ofList
      apply Ideal.span_mono
      rintro _ ⟨x, hx | hx, rfl⟩
      · obtain ⟨i, rfl⟩ := hx
        exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
      · obtain ⟨j, rfl⟩ := hx
        exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  · rw [List.length_append, List.length_ofFn, List.length_ofFn,
      IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    have h1 := Submodule.finrank_quotient_add_finrank W
    have h2 : Module.finrank (ResidueField R) W = r := by
      simpa using finrank_span_eq_card hli
    omega
end GlobalTheory.CompanionTheory.RegSeq
