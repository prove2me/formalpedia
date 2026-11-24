-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmBracket.ds_bracket
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:01:26.358515+00:00
-- url     : https://prove2.me/submissions/d51703f8-63d2-42e4-b5a8-ed136ee7c399

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExt
import Theorems.Thm_GlobalTheory_CompanionTheory_SmBracket_fderiv_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_SmBracket_hasDerivAt_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_SmBracket_ds_ds
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmBracket
open CompanionTheory.D.Upq.Sm
open PI.UpqRep (UJset IsURepOn inG)
open PI.PhMeasCore (dsig smoothVecs)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
namespace GlobalTheory.CompanionTheory.SmBracket
theorem _root_.solution (h : RepOn G σ) {X Y : Mat n} (hX : ∀ t, ex X t ∈ G) (hY : ∀ t, ex Y t ∈ G)
    (hXY : ∀ t, ex (X * Y - Y * X) t ∈ G) {v : H} (hv : IsSm G σ v) :
    ds σ X (ds σ Y v) - ds σ Y (ds σ X v) = ds σ (X * Y - Y * X) v := by
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hv 1 h.one_mem
  have h2 := hasDerivAt_ext h (f := fun x => σ x v) hXY h.one_mem hU h1 hF hfF
  simp only [Matrix.one_mul] at h2
  have e : ds σ (X * Y - Y * X) v = fderiv ℝ F 1 (X * Y - Y * X) := h2.deriv
  let L : Mat n →L[ℝ] Mat n := (LinearMap.mulRight ℝ Y).toContinuousLinearMap
  have hL : ∀ x, L x = x * Y := by intro x; simp [L]
  let M : Mat n →L[ℝ] Mat n := (LinearMap.mulRight ℝ X).toContinuousLinearMap
  have hM : ∀ x, M x = x * X := by intro x; simp [M]
  rw [ds_ds h hX hY hv hU h1 hF hfF L hL, ds_ds h hY hX hv hU h1 hF hfF M hM, e]
  exact fderiv_comm (hF.contDiffAt (hU.mem_nhds h1)) L M ((hM 1).trans (Matrix.one_mul X))
    ((hL 1).trans (Matrix.one_mul Y)) (congrArg₂ (· - ·) (hL X) (hM Y))
end GlobalTheory.CompanionTheory.SmBracket
