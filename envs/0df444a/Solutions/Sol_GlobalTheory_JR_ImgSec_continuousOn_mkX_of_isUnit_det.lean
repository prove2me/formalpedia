-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.continuousOn_mkX_of_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:50:19.054657+00:00
-- url     : https://prove2.me/submissions/7a20e6f3-26d1-4fed-8c93-b0cc78030932

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOnHermitianBlockMatrixOfInvariants
import Theorems.Thm_GlobalTheory_JR_ImgSec_continuousStar
import Theorems.Thm_GlobalTheory_JR_ImgSec_continuous_hankelShift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ImgSec
namespace GlobalTheory.JR.ImgSec
theorem _root_.solution (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (h : Inv r F → Matrix (Fin r) (Fin r) E)
    (hc : ContinuousOn h Ω) (hd : ∀ a ∈ Ω, IsUnit (h a).det) :
    ContinuousOn (fun a => GlobalTheory.JR.ImgSec.mkX a (h a)) Ω := by
  haveI := GlobalTheory.JR.ImgSec.continuousStar (E := E) F
  have hinv : ContinuousOn (fun a => (h a)⁻¹) Ω := by
    intro a ha
    exact (continuousAt_matrix_inv (h a)
      (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ (hd a ha).ne_zero)).comp_continuousWithinAt (hc a ha)
  have hmap : Continuous (fun a : Inv r F => (hankelShift a).map (algebraMap F E)) :=
    continuous_matrix fun i j => (continuous_algebraMap F E).comp
      ((continuous_apply_apply i j).comp continuous_hankelShift)
  have h1 : ContinuousOn (fun a => star (h a)⁻¹ * (hankelShift a).map (algebraMap F E) * (h a)⁻¹) Ω :=
    (hinv.star.mul hmap.continuousOn).mul hinv
  have h2 : ContinuousOn (fun a => h a *ᵥ (e1 : Fin r → E)) Ω := by
    exact (continuous_id.matrix_mulVec continuous_const).comp_continuousOn hc
  have h3 : Continuous (fun a : Inv r F => a.2.2) := continuous_snd.comp continuous_snd
  have h1' : ContinuousOn (fun a => (GlobalTheory.JR.ImgSec.mkX a (h a)).1) Ω := by
    intro a ha
    exact Topology.IsInducing.subtypeVal.continuousWithinAt_iff.2 (h1 a ha)
  exact h1'.prodMk (h2.prodMk h3.continuousOn)
end GlobalTheory.JR.ImgSec
