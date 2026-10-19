-- Prove2me | solution 2 for OAI.KervaireTraceCalculus.geometricPart_realpart_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:56:01.642808+00:00
-- url     : https://prove2.me/submissions/83b0429c-ce3b-4c0e-9709-e0046c825e52

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/TraceCalculus.lean:L207-L231
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireTraceCalculus.geometricPart_realpart_nonneg. The node keeps its source
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
end PositiveTrace
section RealPath
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

end RealPath
section Cayley
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The Hermitian part of the Cayley transform is nonnegative.  This algebraic
Neumann-series argument is valid in every C-star algebra, not just matrices. -/
theorem geometricPart_realpart_nonneg (Z : A) (hZ : ‖Z‖ < 1) :
    0 ≤ 1 + (∑' n : ℕ, Z ^ (n+1)) + star (∑' n : ℕ, Z ^ (n+1)) := by
  let P : A := ∑' n : ℕ, Z ^ n
  have hD : 0 ≤ 1 - star Z * Z := by
    apply sub_nonneg.mpr
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg Z)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg Z]
  have hZP : Z * P = P - 1 := by
    exact (geom_series_mul_shift Z hZ).trans (geom_series_succ Z hZ)
  have hpos := star_left_conjugate_nonneg hD P
  have he : star P * (1 - star Z * Z) * P = P + star P - 1 := by
    calc
      star P * (1 - star Z * Z) * P = star P * P - star (Z * P) * (Z * P) := by
        rw [star_mul]
        noncomm_ring
      _ = P + star P - 1 := by
        rw [hZP, star_sub, star_one]
        noncomm_ring
  rw [he] at hpos
  rw [geom_series_succ Z hZ, star_sub, star_one]
  convert hpos using 1
  noncomm_ring

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


theorem solution : type_of% @_root_.OAI.KervaireTraceCalculus.geometricPart_realpart_nonneg := @_root_.OAI.KervaireTraceCalculus.geometricPart_realpart_nonneg
