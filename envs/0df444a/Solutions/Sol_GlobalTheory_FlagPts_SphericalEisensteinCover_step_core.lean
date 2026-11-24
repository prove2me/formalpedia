-- Prove2me | solution 1 for GlobalTheory.FlagPts.SphericalEisensteinCover.step_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:32:28.133861+00:00
-- url     : https://prove2.me/submissions/de2cceb7-c448-4573-848f-49db7fb349e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAdaptedFrameBigCell
import Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_disj_sup
import Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_finrank_sup_span
import Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_spanFrom_update_of_lt
import Theorems.Thm_GlobalTheory_FlagPts_SphericalEisensteinCover_spanFrom_update_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.SphericalEisensteinCover
variable {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
namespace GlobalTheory.FlagPts.SphericalEisensteinCover
theorem _root_.solution (Fs : ℕ → Submodule k W) (hmono : ∀ m, Fs m ≤ Fs (m + 1)) (A : Submodule k W)
    (f : ℕ → W) (m : ℕ) (hmN : m < finrank k W) (v : W)
    (hv1 : v ∉ Fs m ⊔ spanFrom k f (finrank k W) (m + 1))
    (hv2 : v ∉ A ⊔ spanFrom k f (finrank k W) (m + 1)) (hinv : Inv Fs A f (m + 1)) :
    Inv Fs A (Function.update f m v) m := by
  intro m' hm'
  rcases hm'.eq_or_lt with rfl | hlt
  · rw [spanFrom_update_self f _ _ v hmN]
    obtain ⟨h1, h2, h3⟩ := hinv (_ + 1) le_rfl
    refine ⟨disj_sup _ _ _ (Disjoint.mono_left (hmono _) h1) hv1, disj_sup _ _ _ h2 hv2, ?_⟩
    rw [finrank_sup_span _ _ (fun h => hv2 (Submodule.mem_sup_right h)), h3]
    omega
  · rw [spanFrom_update_of_lt f _ _ _ v hlt]
    exact hinv m' hlt
end GlobalTheory.FlagPts.SphericalEisensteinCover
