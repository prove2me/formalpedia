-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.concaveOn_logCorrectedPerspective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:43:52.277978+00:00
-- url     : https://prove2.me/submissions/85b15c98-c764-431f-90b1-3b1715b3179f

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/PerspectiveCalculus.lean:L72-L96
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.concaveOn_logCorrectedPerspective. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_ComparisonEstimates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_concaveOn_Ioi_of_hasDerivAt2_nonpos_except

-- ---- from OAI.InformationTheory.BooleanNoise.PerspectiveCalculus ----
namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

private theorem hasDerivAt_const_quotient (x v : ℝ) (hv : 0 < v) :
    HasDerivAt (fun w : ℝ => x / w) (-x / v ^ 2) v := by
  convert! (hasDerivAt_const v x).div (hasDerivAt_id v) (ne_of_gt hv) using 1
  simp

theorem hasDerivAt_logCorrectedPerspective (f f' : ℝ → ℝ) (x C : ℝ)
    {v : ℝ} (hv : 0 < v) (hf : HasDerivAt f (f' (x / v)) (x / v)) :
    HasDerivAt (logCorrectedPerspective f x C)
      (logCorrectedPerspectiveDeriv f f' x C v) v := by
  have hi := hasDerivAt_const_quotient x v hv
  have hp := (hasDerivAt_id v).mul (hf.comp v hi)
  have hl := ((hasDerivAt_id v).mul (Real.hasDerivAt_log (ne_of_gt hv))).const_mul C
  convert! hp.sub hl using 1
  · ext w
    change w * f (x / w) - C * w * Real.log w =
      w * f (x / w) - C * (w * Real.log w)
    ring
  · dsimp only [logCorrectedPerspectiveDeriv, id_eq, Function.comp_def]
    field_simp [ne_of_gt hv]
    ring

theorem hasDerivAt_logCorrectedPerspectiveDeriv (f f' f'' : ℝ → ℝ) (x C : ℝ)
    {v : ℝ} (hv : 0 < v) (hf : HasDerivAt f (f' (x / v)) (x / v))
    (hf' : HasDerivAt f' (f'' (x / v)) (x / v)) :
    HasDerivAt (logCorrectedPerspectiveDeriv f f' x C)
      (logCorrectedPerspectiveSecondDeriv f'' x C v) v := by
  have hi := hasDerivAt_const_quotient x v hv
  have hfirst := hf.comp v hi
  have hsecond := hi.mul (hf'.comp v hi)
  have hlog := ((Real.hasDerivAt_log (ne_of_gt hv)).add_const 1).const_mul C
  convert! (hfirst.sub hsecond).sub hlog using 1
  dsimp only [logCorrectedPerspectiveSecondDeriv, Function.comp_apply]
  field_simp [ne_of_gt hv]
  ring

theorem continuousOn_logCorrectedPerspectiveDeriv (f f' : ℝ → ℝ) (x C : ℝ)
    (hx : 0 < x) (hf : ∀ y, 0 < y → HasDerivAt f (f' y) y)
    (hf' : ContinuousOn f' (Ioi 0)) :
    ContinuousOn (logCorrectedPerspectiveDeriv f f' x C) (Ioi 0) := by
  have hi : ContinuousOn (fun v : ℝ => x / v) (Ioi 0) :=
    continuousOn_const.div continuousOn_id (fun _ hv => ne_of_gt hv)
  have hmap : MapsTo (fun v : ℝ => x / v) (Ioi 0) (Ioi 0) :=
    fun _ hv => div_pos hx hv
  have hcf : ContinuousOn f (Ioi 0) :=
    fun y hy => (hf y hy).continuousAt.continuousWithinAt
  have hl : ContinuousOn Real.log (Ioi 0) :=
    continuousOn_id.log (fun _ hv => ne_of_gt hv)
  exact ((hcf.comp hi hmap).sub (hi.mul (hf'.comp hi hmap))).sub
    (continuousOn_const.mul (hl.add continuousOn_const))

theorem concaveOn_logCorrectedPerspective (f f' f'' : ℝ → ℝ)
    (x C join : ℝ) (hx : 0 < x) (hjoin : 0 < join)
    (hf : ∀ y, 0 < y → HasDerivAt f (f' y) y)
    (hcf' : ContinuousOn f' (Ioi 0))
    (hf' : ∀ y, 0 < y → y ≠ join → HasDerivAt f' (f'' y) y)
    (hcurv : ∀ y, 0 < y → y ≠ join → y ^ 2 * f'' y ≤ C) :
    ConcaveOn ℝ (Ioi 0) (logCorrectedPerspective f x C) := by
  have hneq {v : ℝ} (hv : 0 < v) (hvc : v ≠ x / join) : x / v ≠ join := by
    intro heq
    apply hvc
    apply (eq_div_iff (ne_of_gt hjoin)).mpr
    have h := (div_eq_iff (ne_of_gt hv)).mp heq
    linarith
  apply concaveOn_Ioi_of_hasDerivAt2_nonpos_except
    (logCorrectedPerspective f x C) (logCorrectedPerspectiveDeriv f f' x C)
    (logCorrectedPerspectiveSecondDeriv f'' x C) 0 (x / join)
  · intro v hv
    exact hasDerivAt_logCorrectedPerspective f f' x C hv (hf _ (div_pos hx hv))
  · exact continuousOn_logCorrectedPerspectiveDeriv f f' x C hx hf hcf'
  · intro v hv hvc
    exact hasDerivAt_logCorrectedPerspectiveDeriv f f' f'' x C hv
      (hf _ (div_pos hx hv)) (hf' _ (div_pos hx hv) (hneq hv hvc))
  · intro v hv hvc
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hcurv _ (div_pos hx hv) (hneq hv hvc))) hv.le

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.concaveOn_logCorrectedPerspective := @_root_.OAI.LeanBlast.CourtadeKumar.concaveOn_logCorrectedPerspective
