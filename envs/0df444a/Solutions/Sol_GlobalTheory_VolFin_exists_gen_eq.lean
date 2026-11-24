-- Prove2me | solution 1 for GlobalTheory.VolFin.exists_gen_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:11:49.545483+00:00
-- url     : https://prove2.me/submissions/026403bc-042e-4cf1-8c6f-d2b671066c08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleGlobalSectionsFunctionFieldIff
import Theorems.Thm_GlobalTheory_VolFin_gen_rs
import Theorems.Thm_GlobalTheory_VolFin_eq_of_gen

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
open GlobalTheory.ZV
open GlobalTheory.AbLaw (rs pw)
noncomputable section
open GlobalTheory GlobalTheory.VolFin
variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
namespace GlobalTheory.VolFin
theorem _root_.solution (U : X.Opens) (f : X.functionField)
    (hf : ∀ x ∈ U, ∃ (V : X.Opens) (hx : x ∈ V) (a : Γ(X, V)), gen V (generic_mem hx) a = f) :
    ∃ a : Γ(X, U), ∀ hU, gen U hU a = f := by
  choose V hx a ha using hf
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun x : U => U ⊓ V x.1 x.2) U
    (fun x => homOfLE inf_le_left)
    (fun x hxU => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hxU, hx x hxU⟩)
    (fun x => rs X inf_le_right (a x.1 x.2))
    (fun x y => eq_of_gen (X := X) fun h =>
      ((gen_rs inf_le_left h _).trans ((gen_rs _ _ _).trans (ha _ _))).trans
        ((gen_rs inf_le_right h _).trans ((gen_rs _ _ _).trans (ha _ _))).symm)
  refine ⟨s, fun hU => ?_⟩
  have h1 : rs X (inf_le_left : U ⊓ V _ hU ≤ U) s = rs X inf_le_right (a _ hU) := hs ⟨_, hU⟩
  exact (gen_rs (inf_le_left : U ⊓ V _ hU ≤ U) ⟨hU, hx _ hU⟩ s).symm.trans
    ((congrArg _ h1).trans ((gen_rs _ _ _).trans (ha _ _)))
end GlobalTheory.VolFin
