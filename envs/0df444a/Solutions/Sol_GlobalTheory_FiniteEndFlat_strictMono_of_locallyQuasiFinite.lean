-- Prove2me | solution 1 for GlobalTheory.FiniteEndFlat.strictMono_of_locallyQuasiFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:08:05.994798+00:00
-- url     : https://prove2.me/submissions/3e1190eb-97d9-420d-bdf6-668b678a433d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.FiniteEndFlat
namespace GlobalTheory.FiniteEndFlat
theorem _root_.solution {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyQuasiFinite f] :
    StrictMono (f : X → Y) := by
  intro x y hxy
  have h : y ⤳ x := hxy.le
  refine lt_of_le_not_ge (show f y ⤳ f x from h.map f.continuous) fun h' => hxy.not_ge ?_
  have e : f y = f x := ((h.map f.continuous).antisymm h').eq
  have hd := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have h2 : (⟨y, e⟩ : f ⁻¹' {f x}) ⤳ ⟨x, rfl⟩ := (subtype_specializes_iff _ _).mpr h
  have : y = x := congrArg Subtype.val h2.eq
  exact this.le
end GlobalTheory.FiniteEndFlat
