-- Prove2me | solution 1 for GlobalTheory.FamPull.val_feUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:12:05.950856+00:00
-- url     : https://prove2.me/submissions/5ad34e37-e705-4f97-b6c7-ec124dcfa353

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDeg
import Theorems.Thm_GlobalTheory_TauPull_val_tau
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_val_famMult


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.FamPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable {D} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.FamPull
theorem _root_.solution (k : ℕ) (mu α : D.X) {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F) {z : T.left} {J}
    (hJ : Good D.P.L z J) :
    uVal D F k α (cP D _ mu) ρ z J * val (DegPre.famMult D F k mu α) (ρ ≫ fst _ _).left z J =
      feUnit D k mu α (ρ ≫ DegPre.prB D F) z J (fun χ => val (D.psi χ) ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J)
        (val D.rigK ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J) := by
  rw [val_famMult _ hJ, TauPull.val_tau _ hJ, uVal, comp_cP, comp_cP, feUnit]
  exact congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) (map_pow _ _ _) (map_pow _ _ _)))
end GlobalTheory.FamPull
