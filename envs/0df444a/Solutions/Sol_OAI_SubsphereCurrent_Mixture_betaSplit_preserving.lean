-- Prove2me | solution 1 for OAI.SubsphereCurrent.Mixture.betaSplit_preserving
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:38:20.392173+00:00
-- url     : https://prove2.me/submissions/03b2de36-9f7b-4d19-a6c5-1987d8606715

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Mixture/BetaTheory.lean:L448-L462
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Mixture.betaSplit_preserving. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine
import Definitions.Def_OAI_Probability_Subsphere_Estimates_FixedPrecision
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Haar
import Definitions.Def_OAI_Probability_Subsphere_Mixture_BetaTheory

-- ---- from OAI.Probability.Subsphere.Mixture.BetaTheory ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

section
open MeasureTheory Set
open scoped RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set Module
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

lemma betaSplitDeriv_apply (z h : ℝ × ℝ) : betaSplitDeriv z h =
    (z.2*h.1+z.1*h.2, -z.2*h.1+(1-z.1)*h.2) := rfl

lemma betaSplit_hasFDeriv (z : ℝ × ℝ) : HasFDerivAt betaSplit (betaSplitDeriv z) z := by
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).mul (hasFDerivAt_snd (𝕜 := ℝ) (p := z))
  have h2 := ((hasFDerivAt_const (1 : ℝ) z).sub (hasFDerivAt_fst (𝕜 := ℝ) (p := z))).mul
    (hasFDerivAt_snd (𝕜 := ℝ) (p := z))
  have hd : (z.1 • ContinuousLinearMap.snd ℝ ℝ ℝ + z.2 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      ((1-z.1) • ContinuousLinearMap.snd ℝ ℝ ℝ + z.2 • (0 - ContinuousLinearMap.fst ℝ ℝ ℝ)) =
      betaSplitDeriv z := by
    ext <;> simp [betaSplitDeriv_apply]
  rw [← hd]
  exact h1.prodMk h2

lemma betaSplit_det (z : ℝ × ℝ) : (betaSplitDeriv z).det = z.2 := by
  change LinearMap.det (betaSplitDeriv z).toLinearMap = _
  rw [← LinearMap.det_toMatrix (Basis.finTwoProd ℝ)]
  have he : LinearMap.toMatrix (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ)
      (betaSplitDeriv z).toLinearMap = !![z.2,z.1;-z.2,1-z.1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply,betaSplitDeriv_apply,
      Basis.coe_finTwoProd_repr]
  rw [he,Matrix.det_fin_two_of]
  ring

lemma betaJoin_split {z : ℝ × ℝ} (hz : z ∈ betaDomain) : betaJoin (betaSplit z) = z := by
  have hr : z.2 ≠ 0 := ne_of_gt hz.2
  ext <;> simp only [betaSplit,betaJoin]
  · have he : z.1*z.2+(1-z.1)*z.2 = z.2 := by ring
    rw [he,mul_div_cancel_right₀ _ hr]
  · ring

lemma betaSplit_join {z : ℝ × ℝ} (hz : z ∈ gammaDomain) : betaSplit (betaJoin z) = z := by
  have hr : z.1+z.2 ≠ 0 := ne_of_gt (add_pos hz.1 hz.2)
  ext <;> simp only [betaSplit,betaJoin] <;> field_simp
  ring

lemma betaSplit_image : betaSplit '' betaDomain = gammaDomain := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨mul_pos hw.1.1 hw.2,mul_pos (sub_pos.mpr hw.1.2) hw.2⟩
  · intro hz
    refine ⟨betaJoin z,?_,betaSplit_join hz⟩
    have hr : 0 < z.1 + z.2 := add_pos hz.1 hz.2
    exact ⟨⟨div_pos hz.1 hr,(div_lt_one hr).2 (by linarith [show 0 < z.2 from hz.2])⟩,hr⟩

lemma betaSplit_inj : InjOn betaSplit betaDomain := by
  intro x hx y hy h
  rw [← betaJoin_split hx,← betaJoin_split hy,h]

lemma lintegral_betaSplit (f : (ℝ × ℝ) → ℝ≥0∞) :
    (∫⁻ z in gammaDomain, f z) =
      ∫⁻ z in betaDomain, ENNReal.ofReal z.2 * f (betaSplit z) := by
  rw [← betaSplit_image]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (measurableSet_Ioo.prod measurableSet_Ioi)
    (fun z _ => (betaSplit_hasFDeriv z).hasFDerivWithinAt) betaSplit_inj]
  apply setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioi)
  intro z hz
  dsimp only
  rw [betaSplit_det,abs_of_pos hz.2]

end SubsphereCurrent.Mixture
end
end
section
/-! Exact beta/gamma independence and products, needed to identify the scalar
coordinate laws in the geometric comparison. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

lemma gammaPDF_measurable (a r : ℝ) : Measurable (gammaPDF a r) :=
  (measurable_gammaPDFReal a r).ennreal_ofReal
lemma betaPDF_measurable (a b : ℝ) : Measurable (betaPDF a b) :=
  (measurable_betaPDFReal a b).ennreal_ofReal

lemma gamma_beta_density {a b q r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hq : q ∈ Ioo (0 : ℝ) 1) (hr : 0 < r) :
    ENNReal.ofReal r * (gammaPDF a 1 (q*r) * gammaPDF b 1 ((1-q)*r)) =
      betaPDF a b q * gammaPDF (a+b) 1 r := by
  change 0 < q ∧ q < 1 at hq
  have hq0 : 0 < q := hq.1
  have hq1 : 0 < 1-q := sub_pos.mpr hq.2
  have hbeta : 0 < beta a b := beta_pos ha hb
  have hga := (Real.Gamma_pos_of_pos ha).ne'
  have hgb := (Real.Gamma_pos_of_pos hb).ne'
  have hg := (Real.Gamma_pos_of_pos (add_pos ha hb)).ne'
  have hp : r * r^(a-1) * r^(b-1) = r^(a+b-1) := by
    calc
      _ = r^(1 : ℝ) * r^(a-1) * r^(b-1) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hr,← Real.rpow_add hr]
        congr 1
        ring
  have he : Real.exp (-(q*r)) * Real.exp (-((1-q)*r)) = Real.exp (-r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [gammaPDF_of_nonneg (mul_pos hq0 hr).le,
    gammaPDF_of_nonneg (mul_pos hq1 hr).le,gammaPDF_of_nonneg hr.le,
    betaPDF,betaPDFReal,ite_eq_left hq,Real.one_rpow,one_mul]
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul hr.le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.mul_rpow hq0.le hr.le,Real.mul_rpow hq1.le hr.le]
  calc
    _ = (1/Real.Gamma a / Real.Gamma b) * q^(a-1) * (1-q)^(b-1) *
      (r*r^(a-1)*r^(b-1)) * (Real.exp (-(q*r))*Real.exp (-((1-q)*r))) := by ring
    _ = _ := by
      rw [hp,he]
      unfold beta
      field_simp [hga,hgb,hg]

lemma lintegral_gamma_eq {f : ℝ → ℝ≥0∞} (hf : Measurable f) (a : ℝ) :
    (∫⁻ x, f x ∂gammaMeasure a 1) = ∫⁻ x in Ioi (0 : ℝ), gammaPDF a 1 x * f x := by
  rw [gammaMeasure,lintegral_withDensity_eq_lintegral_mul volume (gammaPDF_measurable _ _) hf,
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr_ae
  have hn : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
  filter_upwards [hn] with x hx
  by_cases hp : 0 < x
  · simp [hp]
  · have hneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    simp [hp,gammaPDF_of_neg hneg]

lemma gammaMeasure_restrict_density (a : ℝ) :
    gammaMeasure a 1 = (volume.restrict (Ioi (0 : ℝ))).withDensity (gammaPDF a 1) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_gamma_eq hf,lintegral_withDensity_eq_lintegral_mul _ (gammaPDF_measurable _ _) hf]
  rfl

lemma betaMeasure_restrict_density (a b : ℝ) :
    betaMeasure a b = (volume.restrict (Ioo (0 : ℝ) 1)).withDensity (betaPDF a b) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [betaMeasure,lintegral_withDensity_eq_lintegral_mul _ (betaPDF_measurable _ _) hf,
    lintegral_withDensity_eq_lintegral_mul _ (betaPDF_measurable _ _) hf,
    ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro x
  by_cases h : 0 < x ∧ x < 1
  · simp [h]
  · simp [Set.indicator,betaPDF,betaPDFReal,h]

lemma lintegral_gamma_prod {f : (ℝ × ℝ) → ℝ≥0∞} (hf : Measurable f) (a b : ℝ) :
    (∫⁻ z, f z ∂(gammaMeasure a 1).prod (gammaMeasure b 1)) =
      ∫⁻ z in gammaDomain, (gammaPDF a 1 z.1 * gammaPDF b 1 z.2) * f z := by
  rw [gammaMeasure_restrict_density,gammaMeasure_restrict_density,
    prod_withDensity (gammaPDF_measurable _ _) (gammaPDF_measurable _ _),
    Measure.prod_restrict,← Measure.volume_eq_prod,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun z : ℝ × ℝ => gammaPDF a 1 z.1 * gammaPDF b 1 z.2) from
        ((gammaPDF_measurable _ _).comp measurable_fst).mul
          ((gammaPDF_measurable _ _).comp measurable_snd)) hf]
  rfl

lemma lintegral_beta_gamma {f : (ℝ × ℝ) → ℝ≥0∞} (hf : Measurable f) (a b c : ℝ) :
    (∫⁻ z, f z ∂(betaMeasure a b).prod (gammaMeasure c 1)) =
      ∫⁻ z in betaDomain, (betaPDF a b z.1 * gammaPDF c 1 z.2) * f z := by
  rw [betaMeasure_restrict_density,gammaMeasure_restrict_density,
    prod_withDensity (betaPDF_measurable _ _) (gammaPDF_measurable _ _),
    Measure.prod_restrict,← Measure.volume_eq_prod,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun z : ℝ × ℝ => betaPDF a b z.1 * gammaPDF c 1 z.2) from
        ((betaPDF_measurable _ _).comp measurable_fst).mul
          ((gammaPDF_measurable _ _).comp measurable_snd)) hf]
  rfl

/-- The exact beta/gamma change of variables as a positive-measure identity. -/
lemma betaSplit_preserving {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    MeasurePreserving betaSplit ((betaMeasure a b).prod (gammaMeasure (a+b) 1))
      ((gammaMeasure a 1).prod (gammaMeasure b 1)) := by
  have hm : Measurable betaSplit := by unfold betaSplit; fun_prop
  refine ⟨hm,?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hm,lintegral_beta_gamma (f := fun z => f (betaSplit z)) (hf.comp hm),lintegral_gamma_prod hf,
    lintegral_betaSplit]
  apply setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioi)
  intro z hz
  change (betaPDF a b z.1 * gammaPDF (a+b) 1 z.2) * f (betaSplit z) =
    ENNReal.ofReal z.2 * ((gammaPDF a 1 (z.1*z.2) * gammaPDF b 1 ((1-z.1)*z.2)) * f (betaSplit z))
  rw [← gamma_beta_density ha hb hz.1 hz.2,mul_assoc]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end
section
/-! Actual squared-projection beta law of the normalized Haar sphere. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Mixture
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Mixture
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Mixture.betaSplit_preserving := @_root_.OAI.SubsphereCurrent.Mixture.betaSplit_preserving
