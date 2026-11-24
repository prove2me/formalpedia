-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmBracket.ds_ds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:38:51.688787+00:00
-- url     : https://prove2.me/submissions/c858b371-b9d2-44cc-bbcb-cc9edec90099

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HasDerivAtExt
import Theorems.Thm_GlobalTheory_CompanionTheory_SmBracket_hasDerivAt_ext
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_differentiableAt
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
theorem _root_.solution (h : RepOn G σ) {X Y : Mat n} (hX : ∀ t, ex X t ∈ G) (hY : ∀ t, ex Y t ∈ G) {v : H}
    (hv : IsSm G σ v) {F : Mat n → H} {U : Set (Mat n)} (hU : IsOpen U) (h1 : (1 : Mat n) ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ x ∈ U, x ∈ G → σ x v = F x) (L : Mat n →L[ℝ] Mat n)
    (hL : ∀ x, L x = x * Y) :
    ds σ X (ds σ Y v) = fderiv ℝ (fun g => fderiv ℝ F g (L g)) 1 X := by
  have hG : ContDiffOn ℝ ∞ (fun g => fderiv ℝ F g (L g)) U :=
    (hF.fderiv_of_isOpen hU (by simp)).clm_apply L.contDiff.contDiffOn
  have hGe : ∀ g ∈ U, g ∈ G → σ g (ds σ Y v) = fderiv ℝ F g (L g) := by
    intro g hg hgG
    rw [apply_ds h hY hgG (hv.differentiableAt h hY), hL]
    exact (hasDerivAt_ext h (f := fun x => σ x v) hY hgG hU hg hF hfF).deriv
  have h2 := hasDerivAt_ext h (f := fun g => σ g (ds σ Y v)) hX h.one_mem hU h1 hG hGe
  simp only [Matrix.one_mul] at h2
  exact h2.deriv
end GlobalTheory.CompanionTheory.SmBracket
