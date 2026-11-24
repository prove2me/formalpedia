-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.bdet_cGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:24:56.863618+00:00
-- url     : https://prove2.me/submissions/a98002f8-09b4-4b68-8605-ee19221c5086

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_det_block
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_bdet_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Plucker
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
namespace GlobalTheory.CompanionTheory.Plucker
theorem _root_.solution (t₀ : Sub ι m) (g : GL ι R) : bdet ({t₀} : Set (Sub ι m)) (cGL m g) = bdet (t₀.1 : Set ι) g := by
  refine bdet_eq ?_
  intro _ _ _ _
  rw [det_block t₀ _ rfl, det_eq_elem_of_subsingleton _ (⟨t₀, rfl⟩ : ({t₀} : Set (Sub ι m)))]
  rfl
end GlobalTheory.CompanionTheory.Plucker
