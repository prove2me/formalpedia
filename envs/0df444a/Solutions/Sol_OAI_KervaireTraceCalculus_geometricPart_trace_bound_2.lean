-- Prove2me | solution 2 for OAI.KervaireTraceCalculus.geometricPart_trace_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:57:22.014604+00:00
-- url     : https://prove2.me/submissions/fb540e63-5737-41a5-97f9-9fc15e6b3ce3

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/TraceCalculus.lean:L233-L251
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireTraceCalculus.geometricPart_trace_bound. The node keeps its source
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
import Theorems.Thm_OAI_KervaireTraceCalculus_geometricPart_realpart_nonneg
import Theorems.Thm_OAI_KervaireTraceCalculus_trace_mul_nonneg

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

/-- The Cayley positivity gives the exact one-sided phase derivative bound. -/
theorem geometricPart_trace_bound (τ : A →L[ℂ] ℂ)
    (ht : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (hp : ∀ X : A, 0 ≤ (τ (star X * X)).re)
    (hs : ∀ X : A, τ (star X) = star (τ X))
    {B : A} (hB : 0 ≤ B) (Z : A) (hZ : ‖Z‖ < 1) :
    -2 * (τ ((∑' n : ℕ, Z ^ (n+1)) * B)).re ≤ (τ B).re := by
  let Q : A := ∑' n : ℕ, Z ^ (n+1)
  have hh := trace_mul_nonneg τ ht hp hB (geometricPart_realpart_nonneg Z hZ)
  have hq : τ (star Q * B) = star (τ (Q * B)) := by
    calc
      τ (star Q * B) = τ (B * star Q) := ht _ _
      _ = τ (star (Q * B)) := by rw [star_mul, hB.star_eq]
      _ = star (τ (Q * B)) := hs _
  change 0 ≤ (τ ((1 + Q + star Q) * B)).re at hh
  simp only [add_mul, one_mul, map_add, hq, Complex.add_re,
    Complex.star_def, Complex.conj_re] at hh
  change -2 * (τ (Q * B)).re ≤ (τ B).re
  linarith

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


theorem solution : type_of% @_root_.OAI.KervaireTraceCalculus.geometricPart_trace_bound := @_root_.OAI.KervaireTraceCalculus.geometricPart_trace_bound
