-- Prove2me | solution 1 for GlobalTheory.CharGerm.unitOf_eq_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:11:07.910527+00:00
-- url     : https://prove2.me/submissions/c6e7c1fb-b144-4188-b94a-bdd5f7195358

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfTorsionCharacters
import Theorems.Thm_P2M_GlobalTheory_CharGerm_comp___eq_e6cc225e6ef6
import Theorems.Thm_P2M_GlobalTheory_KernelNoTorsion_torsionLift___104fe53c2c33
import Theorems.Thm_P2M_GlobalTheory_KernelNoTorsion_torsion__pow_0f791edbd64c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CharGerm
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.KernelNoTorsion GlobalTheory.GmPoints
variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {p : ℕ}
  (χ : Tv G p)
namespace GlobalTheory.CharGerm
theorem _root_.solution {S : Type} [CommRing S] [Algebra R₀ S] {z : sp (R₀ := R₀) S ⟶ G} {N : ℕ}
    (w : sp (R₀ := R₀) S ⟶ torsion G (p ^ N)) (hw : w ≫ torsion.ι G (p ^ N) = z) :
    (unitOf (O := R₀) (w ≫ χ.χ N) : S) = val χ z := by
  have h : ∃ N : ℕ, z ^ (p ^ N) = 1 :=
    ⟨N, by rw [← hw, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one]⟩
  rw [val, dif_pos h, comp_χ_eq χ w (torsionLift z h.choose_spec) (by rw [hw, torsionLift_ι])]
end GlobalTheory.CharGerm
