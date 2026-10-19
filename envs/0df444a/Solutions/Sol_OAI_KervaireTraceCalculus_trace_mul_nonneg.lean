-- Prove2me | solution 1 for OAI.KervaireTraceCalculus.trace_mul_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:19:41.7759+00:00
-- url     : https://prove2.me/submissions/af594336-1bc9-4238-8f48-f483978fc868

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

open OAI OAI.KervaireTraceCalculus
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped Topology
attribute [local instance] OAI.KervaireTraceCalculus.instContinuousFunctionalCalculusRealIsSelfAdjoint_oAI
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedRing E]
  [NormedAlgebra 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
open scoped ComplexOrder
theorem solution (τ : A →L[ℂ] ℂ)
    (ht : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (hp : ∀ X : A, 0 ≤ (τ (star X * X)).re)
    {B D : A} (hB : 0 ≤ B) (hD : 0 ≤ D) : 0 ≤ (τ (D * B)).re := by
  set sB := CFC.sqrt B
  set sD := CFC.sqrt D
  have hB2 : sB * sB = B := CFC.sqrt_mul_sqrt_self B hB
  have hD2 : sD * sD = D := CFC.sqrt_mul_sqrt_self D hD
  have hsB : IsSelfAdjoint sB := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)
  have hsD : IsSelfAdjoint sD := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg D)
  have h : τ (D * B) = τ (star (sD * sB) * (sD * sB)) := by
    rw [star_mul, hsB.star_eq, hsD.star_eq, ← hB2, ← hD2]
    rw [show sD * sD * (sB * sB) = (sD * sD * sB) * sB by noncomm_ring, ht]
    congr 1; noncomm_ring
  rw [h]; exact hp _
