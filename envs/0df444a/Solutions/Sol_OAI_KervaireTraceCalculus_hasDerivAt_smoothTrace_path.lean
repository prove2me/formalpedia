-- Prove2me | solution 1 for OAI.KervaireTraceCalculus.hasDerivAt_smoothTrace_path
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:59:11.176041+00:00
-- url     : https://prove2.me/submissions/6c2f2736-c86e-48eb-99ed-3f7e6a4c629d

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/TraceCalculus.lean:L287-L314
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireTraceCalculus.hasDerivAt_smoothTrace_path. The node keeps its source
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
import Theorems.Thm_OAI_KervaireTraceCalculus_hasDerivAt_traceLog_path

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

end RealPath
section Cayley
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end Cayley
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A]

omit [PartialOrder A] [StarOrderedRing A] [Nontrivial A] in
/-- Summing the derivative of the logarithm produces the Cayley series inside
 the algebra. -/
theorem trace_deriv_series (τ : A →L[ℂ] ℂ) {a : ℂ} {W : A} (C : A)
    (haW : ‖a • W‖ < 1) :
    (∑' n : ℕ, a ^ (n+1) * τ (W ^ (n+1) * C)) =
      τ ((∑' n : ℕ, (a • W) ^ (n+1)) * C) := by
  let Φ : A →L[ℂ] ℂ := τ.comp ((ContinuousLinearMap.mul ℂ A).flip C)
  have hsum : Summable (fun n : ℕ => (a • W) ^ (n+1)) :=
    (summable_geometric_of_norm_lt_one haW).comp_injective
      (fun i j h => Nat.add_right_cancel h)
  have he := Φ.map_tsum hsum
  simpa [Φ, smul_pow, smul_mul_assoc] using he.symm

omit [Nontrivial A] in
/-- Positive generators give a unitary path at all real times. -/
theorem exp_phaseVelocity_mem_unitary {B : A} (hB : 0 ≤ B) (t : ℝ) :
    NormedSpace.exp (t • phaseVelocity B) ∈ unitary A := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  simp [phaseVelocity, star_smul, hB.star_eq]

/-- The exact derivative of the regularized phase along a positive path. -/
theorem hasDerivAt_smoothTrace_path (τ : A →L[ℂ] ℂ)
    (ht : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    {U B : A} (hU : U ∈ unitary A) (hB : 0 ≤ B)
    {a : ℂ} (ha : ‖a‖ < 1) (t : ℝ) :
    HasDerivAt (fun t : ℝ => smoothTrace τ a
      (U * NormedSpace.exp (t • phaseVelocity B)))
      (-2 * (τ ((∑' n : ℕ, (a • (U * NormedSpace.exp
        (t • phaseVelocity B))) ^ (n+1)) * B)).re) t := by
  have hb : ∀ t : ℝ, ‖U * NormedSpace.exp (t • phaseVelocity B)‖ ≤ 1 := by
    intro t
    exact (CStarRing.norm_of_mem_unitary ((unitary A).mul_mem hU
      (exp_phaseVelocity_mem_unitary hB t))).le
  have hn : ‖a • (U * NormedSpace.exp (t • phaseVelocity B))‖ < 1 := by
    rw [norm_smul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hb t)) ha
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_traceLog_path τ ht U (phaseVelocity B) hb ha t)
  have hd := (h.div_const Real.pi).const_sub ((τ 1).re / 2)
  apply hd.congr_deriv
  rw [trace_deriv_series τ (phaseVelocity B) hn]
  change -((τ ((∑' n : ℕ, (a • (U * NormedSpace.exp
    (t • phaseVelocity B))) ^ (n+1)) * phaseVelocity B)).im / Real.pi) = _
  have hev (T : A) : (τ (T * phaseVelocity B)).im =
      (2 * Real.pi) * (τ (T * B)).re := by
    simp [phaseVelocity, Complex.mul_im]
  rw [hev]
  field_simp

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


theorem solution : type_of% @_root_.OAI.KervaireTraceCalculus.hasDerivAt_smoothTrace_path := @_root_.OAI.KervaireTraceCalculus.hasDerivAt_smoothTrace_path
