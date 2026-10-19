-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Sampling.curved_average_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:48:27.838998+00:00
-- url     : https://prove2.me/submissions/a8d0e112-fc16-44a2-a031-c1b526aef595

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SamplingEnergy.lean:L14-L56
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Sampling.curved_average_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_uniform_poisson_chirp

-- ---- from OAI.Analysis.Littlewood.SamplingTail ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open MeasureTheory FourierTransform Filter Topology Complex
open scoped BigOperators FourierTransform SchwartzMap ContDiff
open QuadraticTail

lemma stationaryWave_norm (g : ℝ → ℂ) (N β b : ℝ) (l : ℤ) :
    ‖stationaryWave g N β b l‖=‖g (((l : ℝ)-b)/β)‖/Real.sqrt |β| := by
  rw [stationaryWave,norm_mul,norm_div,norm_realPhase,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- from OAI.Analysis.Littlewood.SamplingEnergy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

/-- The off-diagonal average with nonzero curvature, used in the sampled
energy calculation. The amplitude bound is later applied to the squared cutoff. -/
theorem curved_average_zero {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {A D β : ℝ} (hA : 0≤A) (hD : 0≤D)
    (hsupp : tsupport g⊆Set.Icc (-A) A) (hbound : ∀ x, ‖g x‖≤D)
    (hβ : β≠0) (b : ℝ) :
    Tendsto (fun N : ℕ ↦ ‖(1/(N : ℂ))*(∑' k : ℤ,
      g ((k : ℝ)/N)*phase (β/N) (-b) k)‖) atTop (𝓝 0) := by
  obtain ⟨J,C,hC,herr⟩ := uniform_poisson_chirp hg hgs hA (abs_nonneg b) hsupp hβ
  let R := (J.card : ℝ)*D/Real.sqrt |β|+C
  have hR : 0≤R := by dsimp [R]; positivity
  have ht : Tendsto (fun N : ℕ ↦ R/Real.sqrt (N : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop R
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ norm_nonneg _)) ?_ ht
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : 1≤(N : ℝ) := by exact_mod_cast hN
  have hN0 : 0<(N : ℝ) := by positivity
  have hsN : 0<Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have he := (herr N b hNr le_rfl).2
  let S : ℂ := ∑' k : ℤ, g ((k : ℝ)/N)*phase (β/N) (-b) k
  have hw : ‖∑ l∈J, stationaryWave g N β b l‖≤(J.card : ℝ)*D/Real.sqrt |β| := by
    calc
      _ ≤ ∑ l∈J, ‖stationaryWave g N β b l‖ := norm_sum_le _ _
      _ ≤ ∑ _l∈J, D/Real.sqrt |β| := Finset.sum_le_sum (fun l _ ↦ by
        rw [stationaryWave_norm]; exact div_le_div_of_nonneg_right (hbound _) (Real.sqrt_nonneg _))
      _ = _ := by simp; ring
  have he' : ‖(1/(Real.sqrt (N : ℝ) : ℂ))*S‖≤R := by
    have hh := norm_add_le ((1/(Real.sqrt (N : ℝ) : ℂ))*S-∑ l∈J, stationaryWave g N β b l)
      (∑ l∈J, stationaryWave g N β b l)
    rw [sub_add_cancel] at hh
    have hdiv : C/(N : ℝ)≤C := (div_le_iff₀ hN0).mpr (by nlinarith)
    dsimp [R]
    linarith
  have heq : ‖(1/(N : ℂ))*S‖=‖(1/(Real.sqrt (N : ℝ) : ℂ))*S‖/Real.sqrt (N : ℝ) := by
    simp only [norm_mul,norm_div,norm_one,Complex.norm_natCast,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hsN]
    have hsq := Real.sq_sqrt hN0.le
    field_simp
    rw [hsq]
    ring
  change ‖(1/(N : ℂ))*S‖≤_
  rw [heq]
  exact div_le_div_of_nonneg_right he' hsN.le

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.curved_average_zero := @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.curved_average_zero
