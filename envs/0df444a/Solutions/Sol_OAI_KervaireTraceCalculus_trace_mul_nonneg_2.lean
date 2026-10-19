-- Prove2me | solution 2 for OAI.KervaireTraceCalculus.trace_mul_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:50:14.640012+00:00
-- url     : https://prove2.me/submissions/dc0eb10d-152a-49c9-b09d-b09edf2bcb98

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/TraceCalculus.lean:L72-L91
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireTraceCalculus.trace_mul_nonneg. The node keeps its source
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

section Complex
variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

end Complex

section PositiveTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
open scoped ComplexOrder

attribute [local instance] OAI.KervaireTraceCalculus.instContinuousFunctionalCalculusRealIsSelfAdjoint_oAI
/-- Tracial positivity applies to a product of positive elements even when they
 do not commute. -/
theorem trace_mul_nonneg (τ : A →L[ℂ] ℂ)
    (ht : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (hp : ∀ X : A, 0 ≤ (τ (star X * X)).re)
    {B D : A} (hB : 0 ≤ B) (hD : 0 ≤ D) : 0 ≤ (τ (D * B)).re := by
  let S := CFC.sqrt B
  let Q := CFC.sqrt D
  have hS : star S = S := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).star_eq
  have hQ : star Q = Q := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg D)).star_eq
  have hSS : S * S = B := CFC.sqrt_mul_sqrt_self B hB
  have hQQ : Q * Q = D := CFC.sqrt_mul_sqrt_self D hD
  have hh : τ (star (Q * S) * (Q * S)) = τ (D * B) := by
    rw [star_mul, hS, hQ]
    calc
      τ (S * Q * (Q * S)) = τ (S * (Q * Q) * S) := by simp only [mul_assoc]
      _ = τ ((D * S) * S) := by rw [hQQ, mul_assoc, ht S]
      _ = τ (D * B) := by rw [mul_assoc, hSS]
  rw [← hh]
  exact hp (Q * S)

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
open scoped ComplexOrder
attribute [local instance] OAI.KervaireTraceCalculus.instContinuousFunctionalCalculusRealIsSelfAdjoint_oAI


theorem solution : type_of% @_root_.OAI.KervaireTraceCalculus.trace_mul_nonneg := @_root_.OAI.KervaireTraceCalculus.trace_mul_nonneg
