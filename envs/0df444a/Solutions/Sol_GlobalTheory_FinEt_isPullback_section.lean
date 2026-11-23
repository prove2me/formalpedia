-- Prove2me | solution 1 for GlobalTheory.FinEt.isPullback_section
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:11.350079+00:00
-- url     : https://prove2.me/submissions/98740f4e-cc79-4582-8e28-62f756302231

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed

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
theorem _root_.solution {X S X' S' : Scheme.{u}} {a : X' ⟶ X} {q : X' ⟶ S'} {p : X ⟶ S}
    {t : S' ⟶ S} (H : IsPullback a q p t) (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S) :
    IsPullback (H.lift (t ≫ σ) (𝟙 S') (by simp [hσ])) t a σ := by
  refine IsPullback.of_right (h₁₂ := q) (v₁₃ := t) (h₂₂ := p) ?_ (by simp) H.flip
  rw [H.lift_snd, hσ]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩
end GlobalTheory.FinEt
