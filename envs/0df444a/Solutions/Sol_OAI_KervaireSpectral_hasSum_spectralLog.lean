-- Prove2me | solution 1 for OAI.KervaireSpectral.hasSum_spectralLog
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:00:54.346169+00:00
-- url     : https://prove2.me/submissions/eb035c0b-6bb3-4779-a028-4923e7f76066

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/SpectralApproximation.lean:L32-L71
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.hasSum_spectralLog. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation

-- ---- from OAI.GroupTheory.Kervaire.TraceCalculus ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireTraceCalculus
open scoped Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedRing E]
  [NormedAlgebra 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Complex
variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

end Complex

section PositiveTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
open scoped ComplexOrder

attribute [local instance] OAI.KervaireTraceCalculus.instContinuousFunctionalCalculusRealIsSelfAdjoint_oAI
end PositiveTrace
section RealPath
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem norm_log_coeff_le (a : ℂ) (n : ℕ) :
    ‖a ^ (n + 1) / (n + 1)‖ ≤ ‖a‖ ^ (n + 1) := by
  rw [norm_div, norm_pow]
  have hn : (1 : ℝ) ≤ ‖(n : ℂ) + 1‖ := by
    rw [← Nat.cast_add_one, Complex.norm_natCast]
    exact_mod_cast Nat.succ_pos n
  exact (div_le_self (pow_nonneg (norm_nonneg a) _) hn)

end RealPath
section Cayley
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end Cayley
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A]

end KervaireTraceCalculus

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.SpectralApproximation ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Uniform absolute convergence of the Mercator expansion in continuous calculus. -/
theorem hasSum_spectralLog (U : Operator H) (hU : U ∈ unitary (Operator H))
    {a : ℂ} (ha : ‖a‖ < 1) :
    HasSum (fun n : ℕ => (a ^ (n+1) / (n+1)) •
      ((ContinuousMap.id ℂ).restrict (spectrum ℂ U)) ^ (n+1)) (spectralLog U hU a ha) := by
  let Z : C(spectrum ℂ U, ℂ) := (ContinuousMap.id ℂ).restrict (spectrum ℂ U)
  have hZ : ‖Z‖ ≤ 1 := by
    apply (Z.norm_le zero_le_one).mpr
    intro z
    exact (CStarRing.norm_of_mem_unitary
      (spectrum_subset_unitary_of_mem_unitary hU z.property)).le
  have hs : Summable (fun n : ℕ => (a ^ (n+1) / (n+1)) • Z ^ (n+1)) := by
    apply Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (norm_nonneg a) ha).comp_injective
        (fun i j h => Nat.add_right_cancel h))
    intro n
    rw [norm_smul]
    calc
      ‖a ^ (n+1) / (n+1)‖ * ‖Z ^ (n+1)‖ ≤ ‖a‖ ^ (n+1) * 1 :=
        mul_le_mul (norm_log_coeff_le a n)
          ((norm_pow_le' Z (Nat.succ_pos n)).trans
            (by simpa using pow_le_pow_left₀ (norm_nonneg Z) hZ (n+1)))
          (norm_nonneg _) (by positivity)
      _ = ‖a‖ ^ (n+1) := mul_one _
  have he : (∑' n : ℕ, (a ^ (n+1) / (n+1)) • Z ^ (n+1)) = spectralLog U hU a ha := by
    ext z
    have h := (ContinuousMap.evalCLM ℂ z).map_tsum hs
    rw [ContinuousMap.evalCLM_apply] at h
    rw [h]
    have haz : ‖a * (z : ℂ)‖ < 1 := by
      rw [norm_mul, CStarRing.norm_of_mem_unitary
        (spectrum_subset_unitary_of_mem_unitary hU z.property), mul_one]
      exact ha
    change (∑' n : ℕ, (a ^ (n+1) / (n+1)) * (z : ℂ) ^ (n+1)) =
      -Complex.log (1 - a * z)
    convert (Complex.hasSum_taylorSeries_neg_log' haz).tsum_eq using 1
    apply tsum_congr
    intro n
    rw [mul_pow, div_mul_eq_mul_div]
  exact he ▸ hs.hasSum

end KervaireSpectral

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireSpectral
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open KervaireTraceCalculus KervaireScalarPhase


theorem solution : type_of% @_root_.OAI.KervaireSpectral.hasSum_spectralLog := @_root_.OAI.KervaireSpectral.hasSum_spectralLog
