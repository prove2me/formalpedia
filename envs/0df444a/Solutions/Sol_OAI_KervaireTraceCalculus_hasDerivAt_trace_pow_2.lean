-- Prove2me | solution 2 for OAI.KervaireTraceCalculus.hasDerivAt_trace_pow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:48:36.019701+00:00
-- url     : https://prove2.me/submissions/58342b22-3bb6-4dc0-b329-d8aa6e649194

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/TraceCalculus.lean:L23-L40
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireTraceCalculus.hasDerivAt_trace_pow. The node keeps its source
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

/-- The derivative of a trace of a noncommutative power has its usual scalar form. -/
theorem hasDerivAt_trace_pow (τ : E →L[𝕜] F)
    (hτ : ∀ a b : E, τ (a * b) = τ (b * a))
    {f : 𝕜 → E} {f' : E} {x : 𝕜} (hf : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (fun y => τ (f y ^ n)) (n • τ (f x ^ (n - 1) * f')) x := by
  have h := τ.hasFDerivAt.comp_hasDerivAt x (hf.fun_pow' n)
  apply h.congr_deriv
  rw [map_sum]
  have hs : ∀ i ∈ Finset.range n,
      τ (f x ^ (n.pred - i) * f' * f x ^ i) = τ (f x ^ (n - 1) * f') := by
    intro i hi
    rw [hτ (_ * _) _, ← mul_assoc, ← pow_add]
    have hi' := Finset.mem_range.mp hi
    have he : i + (n.pred - i) = n - 1 := by
      simp only [Nat.pred_eq_sub_one]
      omega
    rw [he]
  simp only [Finset.sum_congr rfl hs, Finset.sum_const, Finset.card_range]

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


theorem solution : type_of% @_root_.OAI.KervaireTraceCalculus.hasDerivAt_trace_pow := @_root_.OAI.KervaireTraceCalculus.hasDerivAt_trace_pow
