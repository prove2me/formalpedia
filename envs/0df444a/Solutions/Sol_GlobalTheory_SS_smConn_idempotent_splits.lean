-- Prove2me | solution 1 for GlobalTheory.SS.smConn_idempotent_splits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:06:45.556828+00:00
-- url     : https://prove2.me/submissions/1f124ea0-aa4a-4093-8a7e-63aba85f7f01

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmConnIdempotentSplits
import Theorems.Thm_GlobalTheory_SS_IdemSplit_isMonHom_sec
import Theorems.Thm_GlobalTheory_SS_IdemSplit_isMonHom_ret
import Theorems.Thm_GlobalTheory_SS_IdemSplit_isComm
import Theorems.Thm_GlobalTheory_Retract_geometricallyConnected
import Theorems.Thm_GlobalTheory_Retract_isSeparated
import Theorems.Thm_GlobalTheory_Retract_quasiCompact
import Theorems.Thm_GlobalTheory_Retract_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], SmConn G → ∀ e : G ⟶ G, IsMonHom e → e ≫ e = e → ∃ (G₁ : Over S) (_ : GrpObj G₁) (i : G₁ ⟶ G) (r : G ⟶ G₁), SmConn G₁ ∧ IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 G₁ ∧ r ≫ i = e := by
  intro S G _ hG e he hee
  obtain ⟨hc, hs, hsep, hqc, hgc⟩ := hG
  let i := equalizer.ι e (𝟙 G)
  let r : G ⟶ equalizer e (𝟙 G) := equalizer.lift e (by simp [hee])
  have hri : r ≫ i = e := equalizer.lift_ι _ _
  have hir : i ≫ r = 𝟙 _ := by
    rw [← cancel_mono i, Category.assoc, hri, Category.id_comp]
    simpa using equalizer.condition e (𝟙 G)
  haveI : IsMonHom (r ≫ i) := by rw [hri]; exact he
  have hl : i.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, hir, Over.id_left]
  have hw := Over.w r
  exact ⟨_, IdemSplit.grpObj i r hir, i, r,
    ⟨IdemSplit.isComm i r hir, GlobalTheory.Retract.smooth hl hw, GlobalTheory.Retract.isSeparated hl hw,
      GlobalTheory.Retract.quasiCompact hl hw, GlobalTheory.Retract.geometricallyConnected hl hw⟩,
    IdemSplit.isMonHom_sec i r hir, IdemSplit.isMonHom_ret i r hir, hir, hri⟩
end GlobalTheory.SS
