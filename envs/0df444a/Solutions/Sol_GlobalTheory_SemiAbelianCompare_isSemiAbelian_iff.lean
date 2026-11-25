-- Prove2me | solution 1 for GlobalTheory.SemiAbelianCompare.isSemiAbelian_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:10:35.316457+00:00
-- url     : https://prove2.me/submissions/98436517-6654-48d5-9b03-53fd2992fe80

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianSchemes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuasiCompactIffLocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_SemiAbelianCompare_geometricallyConnected_of_isAlgClosed
import Theorems.Thm_GlobalTheory_SemiAbelianCompare_isTorusExtension_iff
import Theorems.Thm_GlobalTheory_SemiAbelianCompare_geometricallyConnected_of_torusExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G
open GlobalTheory GlobalTheory.SemiAbelianCompare
namespace GlobalTheory.SemiAbelianCompare
theorem _root_.solution {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    Semi.IsSemiAbelian G ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsSemiAbelianScheme G := by
  constructor
  · intro h
    have := h.smooth
    have := h.comm
    exact ⟨h.smooth, h.separated, inferInstance, h.quasiCompact, h.comm,
      fun k _ _ s => (isTorusExtension_iff _).1 ⟨inferInstance, h.fibres k s⟩⟩
  · intro h
    have hf := fun (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ S) =>
      ((isTorusExtension_iff _).2 (h.geometricFibre k s)).2
    refine ⟨h.comm, h.smooth, h.separated, h.quasiCompact,
      geometricallyConnected_of_isAlgClosed _ fun k _ _ s => ?_, hf⟩
    obtain ⟨E⟩ := hf k s
    have := geometricallyConnected_of_torusExtension E
    exact GeometricallyConnected.connectedSpace_of_subsingleton ((Over.pullback s).obj G).hom
end GlobalTheory.SemiAbelianCompare
