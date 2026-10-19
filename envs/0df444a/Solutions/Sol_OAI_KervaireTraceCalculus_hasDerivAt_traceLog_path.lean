-- Prove2me | solution 1 for OAI.KervaireTraceCalculus.hasDerivAt_traceLog_path
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:54:28.001626+00:00
-- url     : https://prove2.me/submissions/5db087f5-55f4-4533-b6b9-a07c32943f19

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/TraceCalculus.lean:L172-L201
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireTraceCalculus.hasDerivAt_traceLog_path. The node keeps its source
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
import Theorems.Thm_OAI_KervaireTraceCalculus_hasDerivAt_trace_real_exp_path_pow

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

omit [CompleteSpace A] in
theorem summable_traceLog [NormOneClass A] (τ : A →L[ℂ] ℂ) {a : ℂ} (ha : ‖a‖ < 1)
    {U : A} (hU : ‖U‖ ≤ 1) :
    Summable (fun n : ℕ => (a ^ (n + 1) / (n + 1)) * τ (U ^ (n + 1))) := by
  apply Summable.of_norm_bounded
    (((summable_geometric_of_norm_lt_one ha).norm.comp_injective
      (fun i j h => Nat.add_right_cancel h)).mul_right ‖τ‖)
  intro n
  simp only [norm_pow]
  rw [norm_mul]
  apply mul_le_mul (norm_log_coeff_le a n) ?_ (norm_nonneg _) (by positivity)
  calc
    ‖τ (U ^ (n + 1))‖ ≤ ‖τ‖ * ‖U ^ (n + 1)‖ := τ.le_opNorm _
    _ ≤ ‖τ‖ * 1 := by
      gcongr
      exact (norm_pow_le _ _).trans (by simpa using pow_le_pow_left₀ (norm_nonneg U) hU (n+1))
    _ = ‖τ‖ := mul_one _

omit [CompleteSpace A] in
theorem norm_trace_pow_mul_le [NormOneClass A] (τ : A →L[ℂ] ℂ)
    {U : A} (hU : ‖U‖ ≤ 1) (C : A) (n : ℕ) :
    ‖τ (U ^ n * C)‖ ≤ ‖τ‖ * ‖C‖ := by
  calc
    ‖τ (U ^ n * C)‖ ≤ ‖τ‖ * ‖U ^ n * C‖ := τ.le_opNorm _
    _ ≤ ‖τ‖ * (‖U ^ n‖ * ‖C‖) := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖τ‖ * (1 * ‖C‖) := by
      gcongr
      exact (norm_pow_le _ _).trans (by simpa using pow_le_pow_left₀ (norm_nonneg U) hU n)
    _ = ‖τ‖ * ‖C‖ := by rw [one_mul]

/-- Uniform geometric bounds justify differentiating the regularized trace.
Only real time is needed, so the unitary path is uniformly bounded. -/
theorem hasDerivAt_traceLog_path [NormOneClass A] (τ : A →L[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (U C : A)
    (hb : ∀ t : ℝ, ‖U * NormedSpace.exp (t • C)‖ ≤ 1)
    {a : ℂ} (ha : ‖a‖ < 1) (t : ℝ) :
    HasDerivAt (fun t : ℝ => traceLog τ a (U * NormedSpace.exp (t • C)))
      (∑' n : ℕ, a ^ (n + 1) * τ ((U * NormedSpace.exp (t • C)) ^ (n + 1) * C)) t := by
  unfold traceLog
  have hs : Summable (fun n : ℕ => ‖a‖ ^ (n+1) * (‖τ‖ * ‖C‖)) :=
    ((summable_geometric_of_lt_one (norm_nonneg a) ha).comp_injective
      (show Function.Injective (fun i : ℕ => i+1) from
        fun i j h => Nat.add_right_cancel h)).mul_right _
  refine hasDerivAt_tsum
    (g := fun (n : ℕ) (x : ℝ) => (a ^ (n+1) / (n+1)) *
      τ ((U * NormedSpace.exp (x • C)) ^ (n+1)))
    (g' := fun (n : ℕ) (x : ℝ) => a ^ (n+1) *
      τ ((U * NormedSpace.exp (x • C)) ^ (n+1) * C))
    (y₀ := (0 : ℝ)) hs ?_ ?_ ?_ t
  · intro n x
    have h := (hasDerivAt_trace_real_exp_path_pow τ hτ U C x (n+1)).const_mul
      (a ^ (n+1) / (n+1))
    apply h.congr_deriv
    rw [Nat.cast_add_one, ← mul_assoc, div_mul_cancel₀]
    exact_mod_cast Nat.succ_ne_zero n
  · intro n x
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (norm_trace_pow_mul_le τ (hb x) C (n+1))
      (pow_nonneg (norm_nonneg a) _)
  · exact summable_traceLog τ ha (hb 0)

end RealPath
section Cayley
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end Cayley
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A]

end KervaireTraceCalculus

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireTraceCalculus
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped Topology


theorem solution : type_of% @_root_.OAI.KervaireTraceCalculus.hasDerivAt_traceLog_path := @_root_.OAI.KervaireTraceCalculus.hasDerivAt_traceLog_path
