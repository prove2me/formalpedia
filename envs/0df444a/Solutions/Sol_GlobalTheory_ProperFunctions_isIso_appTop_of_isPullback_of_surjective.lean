-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:54:10.158152+00:00
-- url     : https://prove2.me/submissions/d8336204-e43a-439a-8951-9c0652566464

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_of_isPushout_of_faithfullyFlat
import Theorems.Thm_GlobalTheory_ProperFunctions_appLE_top_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {p : X ⟶ S} {q : Y ⟶ T}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution (H : IsPullback g q p f) [IsAffine S]
    [IsAffine T] [Flat f] [Surjective f] [QuasiCompact p] [IsIso q.appTop] : IsIso p.appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have hUY : (⊤ : Y.Opens) = g ⁻¹ᵁ ⊤ ⊓ q ⁻¹ᵁ ⊤ := by simp
  let σ := pushoutSection H (le_preimage_top f ⊤) (le_preimage_top p ⊤) hUY
  have : Mono σ := mono_pushoutSection_of_isCompact_of_flat_right H _ _ hUY
    (isAffineOpen_top S) (isAffineOpen_top T) (by simpa using isCompact_univ)
  have hq : IsIso (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)) := by rw [appLE_top_top]; infer_instance
  have h1 : pushout.inr _ _ ≫ σ = q.appLE ⊤ ⊤ (le_preimage_top q ⊤) := pushout.inr_desc _ _ _
  have : IsSplitEpi σ :=
    ⟨⟨inv (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)) ≫ pushout.inr _ _,
      by rw [Category.assoc, h1, IsIso.inv_hom_id]⟩⟩
  have : IsIso σ := isIso_of_mono_of_isSplitEpi σ
  have h2 : IsPushout p.appTop f.appTop g.appTop q.appTop := by
    simpa only [appLE_top_top] using (isIso_pushoutSection_iff ..).mp this
  exact isIso_of_isPushout_of_faithfullyFlat h2
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨‹_›, ‹_›⟩)
end GlobalTheory.ProperFunctions
