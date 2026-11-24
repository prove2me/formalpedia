-- Prove2me | solution 1 for GlobalTheory.isIso_toNormalization_morphismRestrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:04:55.117301+00:00
-- url     : https://prove2.me/submissions/bfbcba7d-d46a-478c-ac95-3c9d73b84eb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Theorems.Thm_GlobalTheory_exists_iso_normalization_of_isPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
attribute [instance] PreservesNormalization.isIso_normalizationPullback
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (V : Y.Opens) [IsIntegralHom (f ∣_ V)] :
    IsIso (f.toNormalization ∣_ (f.fromNormalization ⁻¹ᵁ V)) := by
  let W := f.fromNormalization ⁻¹ᵁ V
  have h' : IsPullback W.ι (f.fromNormalization ∣_ V) f.fromNormalization V.ι :=
    (isPullback_morphismRestrict _ _).flip
  have h : IsPullback (f.toNormalization ⁻¹ᵁ W).ι (f.toNormalization ∣_ W ≫
      f.fromNormalization ∣_ V) f V.ι := by
    simpa using (isPullback_morphismRestrict f.toNormalization W).flip.paste_vert h'
  have key : ∀ f₀ : X ⟶ Y, f₀ = f → IsIntegralHom (f₀ ∣_ V) := by
    rintro _ rfl; infer_instance
  have : IsIntegralHom (f.toNormalization ∣_ W ≫ f.fromNormalization ∣_ V) := by
    have := key _ f.toNormalization_fromNormalization
    rwa [morphismRestrict_comp] at this
  obtain ⟨i, hi, -⟩ := exists_iso_normalization_of_isPullback h h' (e := f.toNormalization ∣_ W)
    (by simp) rfl
  rw [← hi]
  infer_instance
end GlobalTheory
