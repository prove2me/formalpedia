-- Prove2me | solution 1 for OAI.Kervaire.coefficient_injective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:40:39.097836+00:00
-- url     : https://prove2.me/submissions/3d7b1ecb-5641-4663-a267-63aa987a99fc

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Main.lean:L86-L88
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.Kervaire.coefficient_injective.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_Kervaire_coefficient_injective) verbatim and is proved by it.
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
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal
import Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow
import Definitions.Def_OAI_GroupTheory_Kervaire_RelatorRigidity
import Definitions.Def_OAI_GroupTheory_Kervaire_VertexJoin
import Definitions.Def_OAI_GroupTheory_Kervaire_Circles
import Definitions.Def_OAI_GroupTheory_Kervaire_Splicing
import Definitions.Def_OAI_GroupTheory_Kervaire_Capping
import Definitions.Def_OAI_GroupTheory_Kervaire_OuterRibbon
import Definitions.Def_OAI_GroupTheory_Kervaire_RibbonProducts
import Definitions.Def_OAI_GroupTheory_Kervaire_Conjugation
import Definitions.Def_OAI_GroupTheory_Kervaire_Inversion
import Definitions.Def_OAI_GroupTheory_Kervaire_Realization
import Definitions.Def_OAI_GroupTheory_Kervaire_Annulus
import Definitions.Def_OAI_GroupTheory_Kervaire_WordNormalization
import Theorems.Thm_OAI_Kervaire_coefficient_injective_iff
import Theorems.Thm_OAI_Kervaire_normalClosure_coefficient_eq_one

-- ---- from OAI.GroupTheory.Kervaire.Main ----
namespace OAI

section
noncomputable section

namespace KervaireRibbon
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {I : Type} {A : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Group A]

end KervaireRibbon

namespace Kervaire
open Monoid Multiplicative Equiv
open KervaireRibbon
open scoped Classical

universe u

theorem coefficient_injective (A : Type u) [Group A] (w : WordGroup A)
    (hw : Unimodular w) : Function.Injective (coefficientMap w) :=
  (coefficient_injective_iff w).mpr (normalClosure_coefficient_eq_one w hw)

end Kervaire

end
end

end OAI

-- ---- mission target ----
open OAI OAI.Kervaire
universe u
open Monoid Multiplicative Equiv
open KervaireRibbon
open scoped Classical

namespace OAI
namespace Kervaire
theorem _root_.solution (A : Type u) [Group A] (w : WordGroup A)
    (hw : Unimodular w) : Function.Injective (coefficientMap w) := by
  first
    | exact OAI.Kervaire.coefficient_injective A w hw
    | exact OAI.Kervaire.coefficient_injective
    | (apply OAI.Kervaire.coefficient_injective <;> assumption)
    | (intros; apply OAI.Kervaire.coefficient_injective <;> assumption)
end Kervaire
end OAI
