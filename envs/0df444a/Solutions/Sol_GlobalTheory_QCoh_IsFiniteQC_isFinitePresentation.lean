-- Prove2me | solution 1 for GlobalTheory.QCoh.IsFiniteQC.isFinitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:06:07.184454+00:00
-- url     : https://prove2.me/submissions/632ce57c-352c-4893-8c41-97f873456d7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.QCoh
namespace IsFiniteQC
theorem _root_.solution [IsLocallyNoetherian X] [IsFiniteQC F] :
    F.IsFinitePresentation := by
  have H (U : X.affineOpens) : ∃ P : (F.over U.1).Presentation, P.IsFinite := by
    have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    obtain ⟨s, hs⟩ := ((isFiniteQC_Spec_iff (F.restrict U.2.fromSpec)).1 inferInstance).fg_top
    obtain ⟨t, ht⟩ := IsNoetherian.noetherian (LinearMap.ker (Finsupp.linearCombination Γ(X, U.1)
      (Subtype.val : ↥(s : Set Γ(F.restrict U.2.fromSpec, ⊤)) → Γ(F.restrict U.2.fromSpec, ⊤))))
    obtain ⟨P, hP, hP'⟩ := exists_presentation_over U.2 (F := F) s hs t ht
    exact ⟨P, ⟨⟨hP ▸ inferInstance⟩, ⟨hP' ▸ inferInstance⟩⟩⟩
  choose P hP using H
  let q : SheafOfModules.QuasicoherentData.{u, u, u, u} (R := X.ringCatSheaf) F :=
    { I := ↥X.affineOpens, X := fun U ↦ U.1, presentation := P
      coversTop := by rw [Opens.coversTop_iff]; exact iSup_affineOpens_eq_top X }
  have hq : q.IsFinitePresentation :=
    SheafOfModules.QuasicoherentData.IsFinitePresentation.mk.{u, u, u, u} (q := q) hP
  exact SheafOfModules.IsFinitePresentation.mk.{u, u, u} (Exists.intro q hq)
end IsFiniteQC
end GlobalTheory.QCoh
