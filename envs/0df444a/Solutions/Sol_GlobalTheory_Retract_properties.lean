-- Prove2me | solution 1 for GlobalTheory.Retract.properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:06:43.573543+00:00
-- url     : https://prove2.me/submissions/93285b2f-3d10-4ae0-a8b9-67a2bac0f7a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_locallyOfFiniteType
import Theorems.Thm_GlobalTheory_Retract_locallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_flat
import Theorems.Thm_GlobalTheory_Retract_smooth
import Theorems.Thm_GlobalTheory_Retract_etale
import Theorems.Thm_GlobalTheory_Retract_surjective_retraction
import Theorems.Thm_GlobalTheory_Retract_isClosedImmersion_section
import Theorems.Thm_GlobalTheory_Retract_quasiCompact
import Theorems.Thm_GlobalTheory_Retract_isSeparated
import Theorems.Thm_GlobalTheory_Retract_universallyClosed
import Theorems.Thm_GlobalTheory_Retract_isProper
import Theorems.Thm_GlobalTheory_Retract_isFinite
import Theorems.Thm_GlobalTheory_Retract_geometricallyConnected

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {i : X ⟶ Y} {r : Y ⟶ X}
  (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
include hir hr
namespace GlobalTheory.Retract
theorem _root_.solution :
    (LocallyOfFiniteType g → LocallyOfFiniteType f) ∧
    (LocallyOfFinitePresentation g → LocallyOfFinitePresentation f) ∧
    (Flat g → Flat f) ∧ (Smooth g → Smooth f) ∧ (Etale g → Etale f) ∧
    (QuasiCompact g → QuasiCompact f) ∧ (IsSeparated g → IsSeparated f) ∧
    (UniversallyClosed g → UniversallyClosed f) ∧ (IsProper g → IsProper f) ∧
    (IsFinite g → IsFinite f) ∧ (GeometricallyConnected g → GeometricallyConnected f) ∧
    Surjective r ∧ (IsSeparated g → IsClosedImmersion i) :=
  ⟨fun _ ↦ locallyOfFiniteType hir hr, fun _ ↦ locallyOfFinitePresentation hir hr,
    fun _ ↦ flat hir hr, fun _ ↦ smooth hir hr, fun _ ↦ etale hir hr,
    fun _ ↦ quasiCompact hir hr, fun _ ↦ isSeparated hir hr, fun _ ↦ universallyClosed hir hr,
    fun _ ↦ isProper hir hr, fun _ ↦ isFinite hir hr, fun _ ↦ geometricallyConnected hir hr,
    surjective_retraction hir, fun _ ↦ isClosedImmersion_section hir hr⟩
end GlobalTheory.Retract
