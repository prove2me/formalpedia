-- Prove2me | solution 1 for GlobalTheory.VolFin.tr_linComb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:16.696854+00:00
-- url     : https://prove2.me/submissions/810b1b54-1026-4360-99cd-22334040a2d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleGlobalSectionsFunctionFieldIff
import Theorems.Thm_GlobalTheory_VolFin_gen_rs

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
omit [IsIntegral Y]
namespace GlobalTheory.VolFin
theorem _root_.solution (N : LB Y) (ψ : X ⟶ Y) (ε : ℤ) (e : ℕ) (hε : ε = e) (J J' : PUnit → N.ι)
    (h) (h') (h'') :
    tr (LB.LinComb N (K := PUnit) (fun _ => ψ) (fun _ => ε)) J J' h h' =
      gen (ψ ⁻¹ᵁ (N.U (J ⟨⟩) ⊓ N.U (J' ⟨⟩))) h'' ((ψ.app _).hom (N.g _ _).val) ^ e := by
  subst hε
  unfold tr LB.LinComb
  dsimp only
  rw [Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  exact congrArg (· ^ e) (gen_rs _ _ _)
end GlobalTheory.VolFin
