-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.Herglotz.compact_stieltjes_representation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:24:19.618986+00:00
-- url     : https://prove2.me/submissions/f028005f-89ea-441a-8faa-ba94fbb23885

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Herglotz.lean:L1188-L1209
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.Herglotz.compact_stieltjes_representation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_continuousAt_compactIntegral
import Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_pick_divided_difference_of_continuous

-- ---- from OAI.Analysis.Herglotz ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal

namespace EntropyPhotonNumber.Herglotz

section Density
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem integral_densityMeasure (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) (g : X → ℝ) :
    (∫ x, g x ∂(densityMeasure μ f : Measure X)) = ∫ x, f x * g x ∂μ := by
  change (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x => ENNReal.ofReal (f x)) from
      ENNReal.measurable_ofReal.comp f.continuous.measurable)
    (by simp : ∀ᵐ x ∂μ, ENNReal.ofReal (f x) < ∞)]
  simp only [ENNReal.toReal_ofReal (hf _), smul_eq_mul]

theorem mass_densityMeasure (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    ((densityMeasure μ f).mass : ℝ) = ∫ x, f x ∂μ := by
  have h := integral_densityMeasure μ f hf (fun _ => 1)
  simpa only [integral_const, smul_eq_mul, mul_one, FiniteMeasure.measureReal_eq_coe_coeFn,
    FiniteMeasure.mass] using h
end Density

section WeakIntegral
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X]

end WeakIntegral

attribute [local instance] OAI.EntropyPhotonNumber.Herglotz.instMeasureSpaceElemRealAngle
theorem approachRadius_tendsto : Tendsto approachRadius atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun _ => by linarith) tendsto_natCast_atTop_atTop
  change Tendsto (fun n : ℕ => 1 - ((n : ℝ) + 2)⁻¹) atTop (𝓝 1)
  simpa only [Function.comp_apply, sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_inv_atTop_zero.comp hn)

theorem boundaryWeight_pos (θ : Angle) : 0 < boundaryWeight θ := by
  dsimp [boundaryWeight]
  positivity

theorem pick_divided_difference {P : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P {s | 0 < s.im})
    (hn : ∀ s : ℂ, 0 < s.im → 0 ≤ (P s).im)
    (hR : ∀ x : ℝ, 0 < x → AnalyticAt ℂ P (x : ℂ) ∧ (P (x : ℂ)).im = 0) :
    ∃ μ : FiniteMeasure Angle, ∀ s : ℂ, 0 < s.im →
      P s - P 1 = (s - 1) * compactIntegral μ s :=
  pick_divided_difference_of_continuous hP hn
    (fun x hx => ⟨(hR x hx).1.continuousAt, (hR x hx).2⟩)

theorem upper_boundary_eq {F G : ℂ → ℂ} {x : ℝ}
    (hF : ContinuousAt F (x : ℂ)) (hG : ContinuousAt G (x : ℂ))
    (he : ∀ s : ℂ, 0 < s.im → F s = G s) : F (x : ℂ) = G (x : ℂ) := by
  let z : ℕ → ℂ := fun n => (x : ℂ) + ((1 - approachRadius n : ℝ) : ℂ) * I
  have hz : Tendsto z atTop (𝓝 (x : ℂ)) := by
    simpa [z] using (tendsto_const_nhds (x := (x : ℂ))).add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := (1 : ℝ))).sub approachRadius_tendsto)).mul_const I)
  have hi (n : ℕ) : 0 < (z n).im := by
    simpa [z] using sub_pos.mpr (approachRadius_mem n).2
  exact tendsto_nhds_unique (hF.tendsto.comp hz)
    ((hG.tendsto.comp hz).congr (fun n => (he _ (hi n)).symm))

theorem resolventDensity_nonneg {A : ℝ} (hA : 0 < A) (θ : Angle) :
    0 ≤ resolventDensity A hA θ := by
  dsimp [resolventDensity]
  exact div_nonneg (mul_nonneg hA.le (boundaryWeight_pos θ).le)
    (by nlinarith [(boundaryParameter_mem θ).1])

theorem mass_resolventMeasure (μ : FiniteMeasure Angle) {A : ℝ} (hA : 0 < A) :
    ((resolventMeasure μ A hA).mass : ℝ) =
      A * ∫ θ : Angle, boundaryWeight θ / (1 + A * boundaryParameter θ) ∂(μ : Measure Angle) := by
  rw [resolventMeasure, mass_densityMeasure _ _ (resolventDensity_nonneg hA), ← integral_const_mul]
  congr 1
  ext θ
  simp only [resolventDensity, ContinuousMap.coe_mk, mul_div_assoc]

theorem resolvent_algebra (μ : FiniteMeasure Angle) {A x : ℝ} (hA : 0 < A) (hx : 0 < x) :
    (x - 1) * (∫ θ : Angle, boundaryWeight θ / (1 + (x - 1) * boundaryParameter θ) ∂(μ : Measure Angle)) =
      ((resolventMeasure μ A hA).mass : ℝ) -
        (1 - (x - 1) / A) * ∫ θ : Angle, realResolvent x hx θ ∂(resolventMeasure μ A hA : Measure Angle) := by
  rw [resolventMeasure, mass_densityMeasure _ _ (resolventDensity_nonneg hA),
    integral_densityMeasure _ _ (resolventDensity_nonneg hA), ← integral_const_mul,
    ← integral_const_mul, ← integral_sub]
  · apply integral_congr_ae
    filter_upwards with θ
    have hd := (real_compactDen_pos (boundaryParameter_mem θ) hx).ne'
    have hdA : 1 + A * boundaryParameter θ ≠ 0 := by
      nlinarith [(boundaryParameter_mem θ).1]
    dsimp [realResolvent, resolventDensity]
    field_simp [hd, hdA, hA.ne']
    have hdA' : 1 + boundaryParameter θ * A ≠ 0 := by simpa [mul_comm] using hdA
    field_simp [hdA']
    ring
  · exact (resolventDensity A hA).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (((resolventDensity A hA).continuous.mul (realResolvent x hx).continuous).const_mul _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem compact_stieltjes_of_difference {R : ℝ → ℝ} (μ : FiniteMeasure Angle)
    (hR : ∀ x : ℝ, 0 < x → 0 ≤ R x)
    (he : ∀ x : ℝ, 0 < x → R x = R 1 - (x - 1) *
      ∫ θ : Angle, boundaryWeight θ / (1 + (x - 1) * boundaryParameter θ) ∂(μ : Measure Angle)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ν : FiniteMeasure Angle,
      ∀ x : ℝ, 0 < x → R x = c + ∫ θ : Angle, (1 + (x - 1) * boundaryParameter θ)⁻¹ ∂(ν : Measure Angle) := by
  let νs : ℕ → FiniteMeasure Angle := fun n => resolventMeasure μ ((n : ℝ) + 1) (by positivity)
  let C : ℝ≥0 := ⟨R 1, hR 1 (by norm_num)⟩
  have hm (n : ℕ) : (νs n).mass ≤ C := by
    change ((νs n).mass : ℝ) ≤ (C : ℝ)
    rw [show νs n = resolventMeasure μ ((n : ℝ) + 1) (by positivity) from rfl,
      mass_resolventMeasure]
    have hr := hR ((n : ℝ) + 2) (by positivity)
    rw [he _ (by positivity)] at hr
    dsimp [C]
    rw [show (n : ℝ) + 2 - 1 = (n : ℝ) + 1 by ring] at hr
    exact sub_nonneg.mp hr
  obtain ⟨ν, hν, hc⟩ :=
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace Angle C).exists_mapClusterPt
      (u := νs) (f := atTop) (by
        rw [Filter.le_principal_iff]
        change ∀ᶠ n : ℕ in atTop, (νs n).mass ≤ C
        exact Eventually.of_forall hm)
  let l : Filter ℕ := Filter.comap νs (𝓝 ν) ⊓ atTop
  have : NeBot l := neBot_inf_comap_iff_map'.mpr hc
  have hνs : Tendsto νs l (𝓝 ν) := tendsto_comap.mono_left inf_le_left
  have hmass : Tendsto (fun n => ((νs n).mass : ℝ)) l (𝓝 (ν.mass : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp
      (FiniteMeasure.continuous_mass.continuousAt.tendsto.comp hνs)
  refine ⟨R 1 - (ν.mass : ℝ), sub_nonneg.mpr (show (ν.mass : ℝ) ≤ R 1 from hν), ν, ?_⟩
  intro x hx
  have hi := (FiniteMeasure.continuous_integral_continuousMap (realResolvent x hx)).continuousAt.tendsto.comp hνs
  have hf : Tendsto (fun n : ℕ => 1 - (x - 1) / ((n : ℝ) + 1)) l (𝓝 1) := by
    have hd : Tendsto (fun n : ℕ => (x - 1) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_const_div_atTop_nhds_zero_nat (x - 1)).comp (tendsto_add_atTop_nat 1)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hd.mono_left inf_le_right)
  have hlim := ((tendsto_const_nhds (x := R 1)).sub hmass).add (hf.mul hi)
  simp only [one_mul] at hlim
  apply tendsto_nhds_unique tendsto_const_nhds (hlim.congr (fun n => ?_))
  rw [he x hx, resolvent_algebra μ (by positivity : 0 < (n : ℝ) + 1) hx]
  change R 1 - ((νs n).mass : ℝ) + (1 - (x - 1) / ((n : ℝ) + 1)) * _ =
    R 1 - (((νs n).mass : ℝ) - (1 - (x - 1) / ((n : ℝ) + 1)) * _)
  dsimp only [Function.comp_apply, νs]
  ring

theorem compactIntegral_real (μ : FiniteMeasure Angle) (x : ℝ) :
    compactIntegral μ (x : ℂ) =
      ((∫ θ : Angle, boundaryWeight θ / (1 + (x - 1) * boundaryParameter θ) ∂(μ : Measure Angle) : ℝ) : ℂ) := by
  rw [compactIntegral, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with θ
  simp only [compactKernel, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_one]

theorem compact_stieltjes_representation {R : ℂ → ℂ}
    (hR : AnalyticOnNhd ℂ R {s | 0 < s.im})
    (hn : ∀ s : ℂ, 0 < s.im → (R s).im ≤ 0)
    (hp : ∀ x : ℝ, 0 < x → AnalyticAt ℂ R (x : ℂ) ∧ (R (x : ℂ)).im = 0 ∧ 0 ≤ (R (x : ℂ)).re) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ν : FiniteMeasure Angle,
      ∀ x : ℝ, 0 < x → (R (x : ℂ)).re = c +
        ∫ θ : Angle, (1 + (x - 1) * boundaryParameter θ)⁻¹ ∂(ν : Measure Angle) := by
  obtain ⟨μ, hμ⟩ := pick_divided_difference (P := fun s => -R s)
    (fun s hs => (hR s hs).neg) (fun s hs => by simpa using hn s hs)
    (fun x hx => ⟨(hp x hx).1.neg, by simp [(hp x hx).2.1]⟩)
  have he (s : ℂ) (hs : 0 < s.im) : R s = R 1 - (s - 1) * compactIntegral μ s := by
    have := hμ s hs
    linear_combination -this
  have hb (x : ℝ) (hx : 0 < x) : R (x : ℂ) = R 1 - ((x : ℂ) - 1) * compactIntegral μ (x : ℂ) :=
    upper_boundary_eq (hp x hx).1.continuousAt
      (continuousAt_const.sub ((continuousAt_id.sub continuousAt_const).mul
        (continuousAt_compactIntegral μ (by simpa using hx)))) he
  apply compact_stieltjes_of_difference (R := fun x : ℝ => (R (x : ℂ)).re) μ
    (fun x hx => (hp x hx).2.2)
  intro x hx
  rw [hb x hx, compactIntegral_real]
  simp

end EntropyPhotonNumber.Herglotz

end

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.Herglotz
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
attribute [local instance] OAI.EntropyPhotonNumber.Herglotz.instMeasureSpaceElemRealAngle


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.Herglotz.compact_stieltjes_representation := @_root_.OAI.EntropyPhotonNumber.Herglotz.compact_stieltjes_representation
