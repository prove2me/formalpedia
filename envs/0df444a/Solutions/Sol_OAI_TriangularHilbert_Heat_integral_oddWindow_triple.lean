-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.integral_oddWindow_triple
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:06:37.648983+00:00
-- url     : https://prove2.me/submissions/fe0f212c-a0fd-4920-9a87-c80e2d40c25c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/SignedConvolution.lean:L75-L93
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.integral_oddWindow_triple. The node keeps its source
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Theorems.Thm_OAI_TriangularHilbert_Heat_density_product
import Theorems.Thm_OAI_TriangularHilbert_Heat_oddWindow_triple_integrable

-- ---- from OAI.Analysis.TriangularHilbert.Gaussian ----
namespace OAI

section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TriangularHilbert.Heat

theorem density_eq_gaussianPDFReal {σ : ℝ} (hσ : 0 ≤ σ) :
    density σ = ProbabilityTheory.gaussianPDFReal 0 ⟨σ, hσ⟩ := by
  ext t
  change (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-t^2 / (2*σ)) =
    (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-(t-0)^2 / (2*σ))
  rw [sub_zero]

theorem density_integrable {σ : ℝ} (hσ : 0 ≤ σ) : Integrable (density σ) := by
  rw [density_eq_gaussianPDFReal hσ]
  exact ProbabilityTheory.integrable_gaussianPDFReal 0 _

end TriangularHilbert.Heat
end
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.MeshMass ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section

lemma integral_density {σ : ℝ} (hσ : 0 < σ) : (∫ t, density σ t) = 1 := by
  rw [density_eq_gaussianPDFReal hσ.le]
  apply ProbabilityTheory.integral_gaussianPDFReal_eq_one
  intro he
  have he' : σ = 0 := congrArg (fun r : NNReal => (r : ℝ)) he
  exact hσ.ne' he'

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianConvolution ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_neg (σ x : ℝ) : density σ (-x) = density σ x := by
  simp [density]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianMoments ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
open scoped NNReal
noncomputable section

lemma integrable_pow_density {s : ℝ} (hs : 0 < s) (n : ℕ) :
    Integrable (fun x : ℝ => x^n*density s x) := by
  have hi : Integrable (fun x : ℝ => x^n*Real.exp (-(1/(2*s))*x^2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq (by positivity : 0 < 1/(2*s)) (by have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n; linarith : -1 < (n:ℝ)))
  convert hi.mul_const (Real.sqrt (2*Real.pi*s))⁻¹ using 1
  funext x
  unfold density
  rw [show -(1/(2*s))*x^2 = -x^2/(2*s) by ring]
  ring

lemma integral_density_first (s : ℝ) : (∫ x : ℝ, x*density s x) = 0 := by
  have he := integral_neg_eq_self (fun x : ℝ => x*density s x) volume
  simp only [density_neg,neg_mul,integral_neg] at he
  linarith

lemma integral_density_third (s : ℝ) : (∫ x : ℝ, x^3*density s x) = 0 := by
  have he := integral_neg_eq_self (fun x : ℝ => x^3*density s x) volume
  simp only [density_neg,neg_pow,show (-1:ℝ)^3 = -1 by norm_num,neg_mul,one_mul,integral_neg] at he
  linarith

lemma integral_density_second {s : ℝ} (hs : 0 < s) : (∫ x : ℝ, x^2*density s x) = s := by
  let v : ℝ≥0 := ⟨s,hs.le⟩
  have hv : v ≠ 0 := by
    intro he
    have h := congrArg (fun q : ℝ≥0 => (q:ℝ)) he
    exact hs.ne' h
  have hh := ProbabilityTheory.variance_fun_id_gaussianReal (μ:=0) (v:=v)
  rw [ProbabilityTheory.variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at hh
  simp only [ProbabilityTheory.integral_id_gaussianReal,sub_zero] at hh
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv] at hh
  change (∫ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 v x * (x^2)) = s at hh
  change (∫ x : ℝ, x^2*density s x) = s
  convert hh using 1
  congr 1
  funext x
  change x^2*((Real.sqrt (2*Real.pi*s))⁻¹*Real.exp (-x^2/(2*s))) =
    ((Real.sqrt (2*Real.pi*s))⁻¹*Real.exp (-((x-0)^2)/(2*s)))*x^2
  simp only [sub_zero]
  ring

lemma integral_cubic_density {s : ℝ} (hs : 0 < s) (c0 c1 c2 c3 : ℝ) :
    (∫ x : ℝ, cubic c0 c1 c2 c3 x*density s x) = c0+c2*s := by
  have h0 := (density_integrable hs.le).const_mul c0
  have h1 : Integrable (fun x : ℝ => c1*(x*density s x)) := by simpa only [pow_one] using (integrable_pow_density hs 1).const_mul c1
  have h2 := (integrable_pow_density hs 2).const_mul c2
  have h3 := (integrable_pow_density hs 3).const_mul c3
  have he (x : ℝ) : cubic c0 c1 c2 c3 x*density s x =
      (c0*density s x+c1*(x*density s x))+c2*(x^2*density s x)+c3*(x^3*density s x) := by unfold cubic; ring
  simp_rw [he]
  have e3 := integral_add ((h0.add h1).add h2) h3
  have e2 := integral_add (h0.add h1) h2
  have e1 := integral_add h0 h1
  dsimp only [Pi.add_apply] at e1 e2 e3
  rw [e3,e2,e1]
  simp only [integral_const_mul,integral_density hs,integral_density_first,integral_density_second hs,integral_density_third,mul_one,mul_zero,add_zero]

lemma integral_shifted_cubic_density {s : ℝ} (hs : 0 < s) (c0 c1 c2 c3 m : ℝ) :
    (∫ x : ℝ, cubic c0 c1 c2 c3 (x-m)*density s (x-m)) = c0+c2*s := by
  rw [integral_sub_right_eq_self (fun x : ℝ => cubic c0 c1 c2 c3 x*density s x),integral_cubic_density hs]
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SignedConvolution ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_equal_pair {s : ℝ} (hs : 0 < s) (a b p : ℝ) :
    density s (a-p)*density s (b+p) =
      density (2*s) (a+b)*density (s/2) (p-(a-b)/2) := by
  rw [show b+p = -((-b)-p) by ring,density_neg,density_product hs hs]
  congr 1
  · congr 1 <;> ring
  · congr 1
    · field_simp; ring
    · field_simp; ring

lemma weighted_signed_pair {s : ℝ} (hs : 0 < s) (a b p : ℝ) :
    (a-p)*(b+p)*density s (a-p)*density s (b+p) =
      density (2*s) (a+b)*(cubic ((a+b)^2/4) 0 (-1) 0 (p-(a-b)/2)*density (s/2) (p-(a-b)/2)) := by
  rw [mul_assoc ((a-p)*(b+p)),density_equal_pair hs]
  unfold cubic
  ring

lemma integral_signed_pair {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    (∫ p : ℝ, (a-p)*(b+p)*density s (a-p)*density s (b+p)) =
      ((a+b)^2/4-s/2)*density (2*s) (a+b) := by
  simp_rw [weighted_signed_pair hs]
  rw [integral_const_mul,integral_shifted_cubic_density (by positivity : 0 < s/2)]
  ring

lemma integral_oddWindow_pair {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    (∫ p : ℝ, oddWindow s (a-p)*oddWindow s (b+p)) =
      (((a+b)^2/4-s/2)*density (2*s) (a+b))/s := by
  have hr := (Real.sqrt_pos.mpr hs).ne'
  have he (p : ℝ) : oddWindow s (a-p)*oddWindow s (b+p) =
      ((a-p)*(b+p)*density s (a-p)*density s (b+p))/s := by
    unfold oddWindow
    field_simp
    rw [Real.sq_sqrt hs.le]
    ring
  simp_rw [he]
  rw [integral_div,integral_signed_pair hs]

lemma density_one_two_pair {s : ℝ} (hs : 0 < s) (a b p : ℝ) :
    density s (a-p)*density (2*s) (b+p) =
      density (3*s) (a+b)*density (2*s/3) (p-(2*a-b)/3) := by
  rw [show b+p = -((-b)-p) by ring,density_neg,density_product hs (by positivity : 0 < 2*s)]
  congr 1
  · congr 1 <;> ring
  · congr 1
    · field_simp; ring
    · field_simp; ring

lemma weighted_signed_outer {s : ℝ} (hs : 0 < s) (a b p : ℝ) :
    (a-p)*density s (a-p)*(((b+p)^2/4-s/2)*density (2*s) (b+p)) =
      density (3*s) (a+b)*(cubic ((a+b)^3/27-(a+b)*s/6) (s/2) (-(a+b)/4) (-1/4)
        (p-(2*a-b)/3)*density (2*s/3) (p-(2*a-b)/3)) := by
  calc
    _ = ((a-p)*((b+p)^2/4-s/2))*(density s (a-p)*density (2*s) (b+p)) := by ring
    _ = _ := by rw [density_one_two_pair hs]; unfold cubic; ring

lemma integral_signed_outer {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    (∫ p : ℝ, (a-p)*density s (a-p)*(((b+p)^2/4-s/2)*density (2*s) (b+p))) =
      ((a+b)^3/27-(a+b)*s/3)*density (3*s) (a+b) := by
  simp_rw [weighted_signed_outer hs]
  rw [integral_const_mul,integral_shifted_cubic_density (by positivity : 0 < 2*s/3)]
  ring

lemma integral_oddWindow_triple {s : ℝ} (hs : 0 < s) (a b c : ℝ) :
    (∫ z : ℝ×ℝ, oddWindow s (a-z.1)*oddWindow s (b-z.2)*oddWindow s (c+z.1+z.2)) =
      signedKernel s (a+b+c) := by
  rw [Measure.volume_eq_prod,integral_prod _ (oddWindow_triple_integrable hs a b c)]
  have inner (p : ℝ) : (∫ q : ℝ, oddWindow s (a-p)*oddWindow s (b-q)*oddWindow s (c+p+q)) =
      oddWindow s (a-p)*((((b+c+p)^2/4-s/2)*density (2*s) (b+c+p))/s) := by
    simp_rw [mul_assoc]
    rw [integral_const_mul,integral_oddWindow_pair hs]
    congr 3 <;> ring_nf
  simp_rw [inner]
  have he (p : ℝ) : oddWindow s (a-p)*((((b+c+p)^2/4-s/2)*density (2*s) (b+c+p))/s) =
      ((a-p)*density s (a-p)*(((b+c+p)^2/4-s/2)*density (2*s) (b+c+p)))/(s*Real.sqrt s) := by
    unfold oddWindow
    ring
  simp_rw [he]
  rw [integral_div,integral_signed_outer hs]
  unfold signedKernel
  rw [show a+(b+c) = a+b+c by ring]
  ring
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.integral_oddWindow_triple := @_root_.OAI.TriangularHilbert.Heat.integral_oddWindow_triple
