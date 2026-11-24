-- Prove2me | solution 1 for GlobalTheory.SectionsDescent.glue_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:54:57.673489+00:00
-- url     : https://prove2.me/submissions/e55965a9-34e6-4f5e-ab73-920882c41630

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
import Theorems.Thm_GlobalTheory_SectionsDescent_rs_rs
import Theorems.Thm_GlobalTheory_SectionsDescent_le_iSup_affine
import Theorems.Thm_GlobalTheory_SectionsDescent_ext_affine

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
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.SectionsDescent
open GlobalTheory.FieldBaseChange
namespace GlobalTheory.SectionsDescent
theorem _root_.solution {X : Scheme.{0}} (U : X.Opens)
    (f : ∀ (V : X.Opens), IsAffineOpen V → V ≤ U → Γ(X, V))
    (hf : ∀ V W hV hW (hVU : V ≤ U) (h : W ≤ V), rs h (f V hV hVU) = f W hW (h.trans hVU)) :
    ∃ y : Γ(X, U), ∀ V hV (h : V ≤ U), rs h y = f V hV h := by
  obtain ⟨y, hy, -⟩ := X.sheaf.existsUnique_gluing'
    (fun V : {V : X.Opens // IsAffineOpen V ∧ V ≤ U} => V.1) U (fun V => homOfLE V.2.2) (le_iSup_affine U)
    (fun V => f V.1 V.2.1 V.2.2) (fun V V' => by
      refine ext_affine (X := X) (U := V.1 ⊓ V'.1) fun W hW h => ?_
      refine (rs_rs inf_le_left h _).trans (Eq.trans ?_ (rs_rs inf_le_right h _).symm)
      rw [hf _ _ _ hW, hf _ _ _ hW])
  exact ⟨y, fun V hV h => hy ⟨V, hV, h⟩⟩
end GlobalTheory.SectionsDescent
