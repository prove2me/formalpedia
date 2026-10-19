-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.oddWindow_triple_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:02:58.073011+00:00
-- url     : https://prove2.me/submissions/114be019-c31b-48d3-8621-7eddc231a718

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/SignedExpansion.lean:L27-L45
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.oddWindow_triple_integrable. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Theorems.Thm_OAI_TriangularHilbert_Heat_density_triple_integrable

-- ---- from OAI.Analysis.TriangularHilbert.MeshMass ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section

lemma continuous_density (σ : ℝ) : Continuous (density σ) := by
  unfold density
  fun_prop

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SignedWindowScalar ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_dilation {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (t : ℝ) :
    density (q*s) t = (Real.sqrt s)⁻¹ * density q (t/Real.sqrt s) := by
  have hr : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hsq := Real.sq_sqrt hs.le
  have he : -(t/Real.sqrt s)^2/(2*q) = -t^2/(2*(q*s)) := by
    field_simp
    nlinarith [hsq]
  unfold density
  rw [show 2*Real.pi*(q*s)=s*(2*Real.pi*q) by ring,Real.sqrt_mul hs.le,he]
  simp only [mul_inv_rev]
  ring

lemma density_one_lambda (z : ℝ) :
    density 1 z = Real.sqrt (11/10) * Real.exp (-z^2/22) * density (11/10) z := by
  have hr : Real.sqrt (11/10) ≠ 0 := by positivity
  have hp : Real.sqrt (2*Real.pi) ≠ 0 := by positivity
  have hn : 2*Real.pi*(11/10) = (11/10)*(2*Real.pi) := by ring
  unfold density
  rw [hn,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 11/10)]
  simp only [mul_one,mul_inv_rev]
  have he : -z^2/22 + -z^2/(2*(11/10)) = -z^2/(2*1) := by ring
  calc
    _ = (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-z^2/22 + -z^2/(2*(11/10))) := by rw [he]; simp
    _ = _ := by rw [Real.exp_add]; field_simp

lemma density_lambda_relation {s : ℝ} (hs : 0 < s) (t : ℝ) :
    density s t = Real.sqrt (11/10) * Real.exp (-(t/Real.sqrt s)^2/22) * density ((11/10)*s) t := by
  have h1 := density_dilation hs (by norm_num : (0:ℝ)<1) t
  rw [one_mul] at h1
  rw [h1,density_dilation hs (by norm_num : (0:ℝ)<11/10),density_one_lambda]
  ring

lemma windowRatio_eq {s : ℝ} (hs : 0 < s) (t : ℝ) :
    windowRatio s t = Real.sqrt (11/10)*(t/Real.sqrt s)*Real.exp (-(t/Real.sqrt s)^2/22) := by
  unfold windowRatio oddWindow
  rw [density_lambda_relation hs t]
  have hn : density ((11/10)*s) t ≠ 0 := (density_pos (by positivity) t).ne'
  rw [← mul_assoc, mul_div_cancel_right₀ _ hn]
  ring

lemma abs_mul_exp_square_le (z : ℝ) : |z| *Real.exp (-z^2/22) ≤ 22 := by
  have h := Real.add_one_le_exp (z^2/22)
  have hp := Real.exp_pos (-z^2/22)
  have ha : |z| ≤ 22*(z^2/22+1) := by nlinarith [sq_nonneg (|z|-1),sq_abs z]
  have he : Real.exp (z^2/22) * Real.exp (-z^2/22) = 1 := by rw [← Real.exp_add,show z^2/22 + -z^2/22 = 0 by ring,Real.exp_zero]
  have hb := mul_le_mul_of_nonneg_right h hp.le
  rw [he] at hb
  have hc := mul_le_mul_of_nonneg_right ha hp.le
  nlinarith

lemma abs_windowRatio_le {s : ℝ} (hs : 0 < s) (t : ℝ) : |windowRatio s t| ≤ 44 := by
  rw [windowRatio_eq hs t,abs_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_pos (Real.exp_pos _)]
  have h := abs_mul_exp_square_le (t/Real.sqrt s)
  have hr : Real.sqrt (11/10) ≤ 2 := by rw [Real.sqrt_le_iff]; norm_num
  have hn := Real.sqrt_nonneg (11/10)
  nlinarith

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SignedExpansion ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section

lemma density_mul_windowRatio {s : ℝ} (hs : 0 < s) (t : ℝ) :
    density ((11/10)*s) t * windowRatio s t = oddWindow s t := by
  unfold windowRatio
  exact mul_div_cancel₀ _ (density_pos (by positivity) _).ne'

lemma abs_oddWindow_le {s : ℝ} (hs : 0 < s) (t : ℝ) :
    |oddWindow s t| ≤ 44*density ((11/10)*s) t := by
  rw [← density_mul_windowRatio hs t,abs_mul,abs_of_nonneg (density_nonneg (by positivity) _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (abs_windowRatio_le hs t) (density_nonneg (by positivity) t)

lemma continuous_oddWindow (s : ℝ) : Continuous (oddWindow s) := by
  unfold oddWindow
  exact (continuous_id.div_const _).mul (continuous_density s)

lemma oddWindow_triple_integrable {s : ℝ} (hs : 0 < s) (a b c : ℝ) :
    Integrable (fun z : ℝ×ℝ => oddWindow s (a-z.1)*oddWindow s (b-z.2)*oddWindow s (c+z.1+z.2)) := by
  have hi := (density_triple_integrable (by positivity : 0 < (11/10)*s)
    (by positivity : 0 < (11/10)*s) (by positivity : 0 < (11/10)*s) a b c).const_mul (44^3:ℝ)
  apply hi.mono'
  · exact (((continuous_oddWindow s).comp (continuous_const.sub continuous_fst)).mul
      ((continuous_oddWindow s).comp (continuous_const.sub continuous_snd)) |>.mul
        ((continuous_oddWindow s).comp ((continuous_const.add continuous_fst).add continuous_snd))).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs,abs_mul,abs_mul]
    have h0 := abs_oddWindow_le hs (a-z.1)
    have h1 := abs_oddWindow_le hs (b-z.2)
    have h2 := abs_oddWindow_le hs (c+z.1+z.2)
    have hd0 := density_nonneg (by positivity : 0 ≤ (11/10)*s) (a-z.1)
    have hd1 := density_nonneg (by positivity : 0 ≤ (11/10)*s) (b-z.2)
    calc
      _ ≤ (44*density ((11/10)*s) (a-z.1))*(44*density ((11/10)*s) (b-z.2))*(44*density ((11/10)*s) (c+z.1+z.2)) := by gcongr
      _ = _ := by ring

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.oddWindow_triple_integrable := @_root_.OAI.TriangularHilbert.Heat.oddWindow_triple_integrable
