-- Prove2me | solution 1 for GlobalTheory.EpsThick.comb_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:45:23.299875+00:00
-- url     : https://prove2.me/submissions/5c118f13-8524-40c5-b8ce-120cd57869bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure
import Theorems.Thm_GlobalTheory_EpsThick_comb_bijective_of_isAffineOpen
import Theorems.Thm_GlobalTheory_EpsThick_res_comb
import Theorems.Thm_GlobalTheory_EpsThick_le_iSup_affine
import Theorems.Thm_GlobalTheory_EpsThick_comb_injective

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.EpsThick
variable {R : Type} [CommRing R] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp R} {π : Y' ⟶ Sp (DualNumber R)} {ρ : Y' ⟶ Y}
namespace GlobalTheory.EpsThick
theorem _root_.solution (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R)))) (O : Y.Opens) :
    Function.Surjective (comb π ρ O) := by
  intro F
  choose s hs using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} =>
    (comb_bijective_of_isAffineOpen H U.2.1).2 ((Y'.presheaf.map (homOfLE (ρ.preimage_mono U.2.2)).op).hom F)
  have key : ∀ U V : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      ((Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (s U).1,
        (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (s U).2) =
      ((Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (s V).1,
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (s V).2) := fun U V => by
    apply comb_injective H
    rw [← res_comb, ← res_comb, hs, hs, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (s U).1) fun U V => congrArg Prod.fst (key U V)
  obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (s U).2) fun U V => congrArg Prod.snd (key U V)
  refine ⟨(a, b), ?_⟩
  refine Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} => ρ ⁻¹ᵁ U.1) _
    (fun U => homOfLE (ρ.preimage_mono U.2.2)) ?_ _ _ fun U => ?_
  · rw [← Scheme.Hom.preimage_iSup]
    exact ρ.preimage_mono (le_iSup_affine O)
  · refine (res_comb U.2.2 (a, b)).trans (Eq.trans ?_ (hs U))
    exact congrArg _ (Prod.ext (ha U) (hb U))
end GlobalTheory.EpsThick
