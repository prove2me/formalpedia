-- Prove2me | solution 2 for OAI.KervaireTraceCalculus.hasDerivAt_trace_real_exp_path_pow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:52:55.838385+00:00
-- url     : https://prove2.me/submissions/17bef291-7176-4fe2-ae7e-c38d5af47f09

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/TraceCalculus.lean:L110-L128
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireTraceCalculus.hasDerivAt_trace_real_exp_path_pow. The node keeps its source
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
import Theorems.Thm_OAI_KervaireTraceCalculus_hasDerivAt_trace_pow

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

/-- The same tracial differentiation formula for a real time parameter. -/
theorem hasDerivAt_trace_real_exp_path_pow (τ : A →L[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (U C : A) (t : ℝ) (n : ℕ) :
    HasDerivAt (fun y : ℝ => τ ((U * NormedSpace.exp (y • C)) ^ n))
      ((n : ℂ) * τ ((U * NormedSpace.exp (t • C)) ^ n * C)) t := by
  have hp := (hasDerivAt_exp_smul_const C t).const_mul U
  have h := hasDerivAt_trace_pow (τ.restrictScalars ℝ) hτ hp n
  by_cases hn : n = 0
  · subst n
    simpa using h
  · apply h.congr_deriv
    change n • τ ((U * NormedSpace.exp (t • C)) ^ (n - 1) *
      (U * (NormedSpace.exp (t • C) * C))) = _
    rw [nsmul_eq_mul]
    congr 1
    congr 1
    rw [← mul_assoc U, ← mul_assoc, ← pow_succ]
    congr 2
    omega

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


theorem solution : type_of% @_root_.OAI.KervaireTraceCalculus.hasDerivAt_trace_real_exp_path_pow := @_root_.OAI.KervaireTraceCalculus.hasDerivAt_trace_real_exp_path_pow
