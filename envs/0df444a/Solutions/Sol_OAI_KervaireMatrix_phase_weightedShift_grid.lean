-- Prove2me | solution 1 for OAI.KervaireMatrix.phase_weightedShift_grid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:27:01.075982+00:00
-- url     : https://prove2.me/submissions/de6655f3-5167-4503-9841-8e7f097a2ea6

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/WeightedCycles.lean:L72-L93
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireMatrix.phase_weightedShift_grid. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Theorems.Thm_OAI_KervaireMatrix_phase_grid
import Theorems.Thm_OAI_KervaireMatrix_phase_weightedShift_root

-- ---- from OAI.GroupTheory.Kervaire.MatrixShifts ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireMatrix

section
open KervaireRegular
open scoped Classical
variable {D A : Type*}

variable [Fintype D]

variable [Group A]

end

open KervaireRegular
open scoped Classical
variable {D A : Type*} [Group A]

variable [Fintype D]

end KervaireMatrix
namespace KervaireSpectral
theorem scalarRotation_grid_pow (j d : ℕ) (hd : 0 < d) :
    scalarRotation ((j : ℝ)/d)^d = 1 := by
  rw [← scalarRotation_nat_mul]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [mul_div_cancel₀ _ hd', scalarRotation_nat]
end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.WeightedCycles ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireMatrix
open KervaireRegular KervaireSpectral
variable {A : Type*} [Group A]

/-- The exact first half of the boundary-cycle phase computation. -/
theorem phase_weightedShift_grid (n : ℕ) (u : Fin (n+1) → ℂ)
    (a : Fin (n+1) → A) (hu : ∀ i, u i ∈ unitary ℂ) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (finRotate (n+1)) u a hu)
    let _ := isStarNormal_of_mem_unitary (pow_mem (weightedShift_unitary (finRotate (n+1)) u a hu) (n+1))
    (n+1 : ℝ) * KervaireMatrix.phase (weightedShift (finRotate (n+1)) u a) =
      (n+1 : ℝ) * (n : ℝ)/2 +
        KervaireMatrix.phase ((weightedShift (finRotate (n+1)) u a)^(n+1)) := by
  let T := weightedShift (finRotate (n+1)) u a
  have hT := weightedShift_unitary (finRotate (n+1)) u a hu
  let _ := isStarNormal_of_mem_unitary hT
  let _ := isStarNormal_of_mem_unitary (pow_mem hT (n+1))
  have h := phase_grid T hT (n+1) (Nat.succ_pos n)
  have he (j : Fin (n+1)) :
      KervaireMatrix.phase (scalarRotation ((j.val : ℝ)/(n+1)) • T) =
        KervaireMatrix.phase T :=
    phase_weightedShift_root n _ (by simpa using scalarRotation_grid_pow j.val (n+1) (Nat.succ_pos n))
      (scalarRotation_unitary _) u a hu
  simp only [Nat.cast_add, Nat.cast_one] at h
  simp_rw [he] at h
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h

end KervaireMatrix
namespace KervaireSpectral
open KervaireTraceCalculus
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

end KervaireSpectral

namespace KervaireRegular
open KervaireSpectral
open scoped Classical
variable {A : Type*} [Group A]

end KervaireRegular

namespace KervaireMatrix
open KervaireRegular KervaireSpectral
variable {D A : Type*} [Fintype D] [Group A]

end KervaireMatrix
namespace KervaireCycle
open Fin.NatCast
variable {D B : Type*} [Monoid B]

end KervaireCycle

namespace KervaireMatrix
open KervaireRegular KervaireCycle
variable {D A : Type*} [Fintype D] [Group A]

end KervaireMatrix
namespace KervaireCycle
variable {D B : Type*} [Monoid B]

end KervaireCycle

namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireCycle
open Fin.NatCast
variable {A : Type*} [Group A]

end KervaireMatrix

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireMatrix
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open KervaireRegular KervaireSpectral


theorem solution : type_of% @_root_.OAI.KervaireMatrix.phase_weightedShift_grid := @_root_.OAI.KervaireMatrix.phase_weightedShift_grid
