-- Prove2me | solution 1 for GlobalTheory.Models.good_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:02:24.83905+00:00
-- url     : https://prove2.me/submissions/b4979d96-f605-446f-9e7b-f07d803bc51d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteSeparableCompositum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GoodPullback
import Theorems.Thm_GlobalTheory_AbLocusPull_abLocus_sections_pull
import Theorems.Thm_GlobalTheory_splitFibres_of_isGrpPullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory GlobalTheory.Models
namespace GlobalTheory.Models
theorem _root_.solution : Out.GtBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (_ : SABMap t' t f), Good t → Good t' := by
  intro hB E _ _ _ H X X' t t' f m hg
  obtain ⟨hA, hS, hT⟩ := hg
  obtain ⟨cm, cart, base, act, lin⟩ := m
  have hpb := GlobalTheory.AbLocusPull.abLocus_sections_pull X X' f t.G t'.G cm.F t.semi cart
  refine ⟨hpb.1 hA, GlobalTheory.splitFibres_of_isGrpPullback hB X X' f t.G t'.G cm.F cart hS,
    hpb.2 t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ?_ hT⟩
  obtain ⟨w, hw, -⟩ := lin
  exact ⟨w, hw⟩
end GlobalTheory.Models
