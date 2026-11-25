-- Prove2me | solution 1 for GlobalTheory.IotaInj.exists_val_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:16:19.234923+00:00
-- url     : https://prove2.me/submissions/7ebb8fdc-8d28-4c74-be10-3f62c35aabb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MemOfNonempty
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.IotaInj
open GlobalTheory.TorusExt
variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.IotaInj
theorem _root_.solution (D : DegPre R) {I : Ideal R} {χ : D.X} (hχ : D.PsiIn χ I) (hc : (D.c χ).left = eSec D.P.A)
    (j : D.P.L.ι) {V : (Spec (CommRingCat.of R)).Opens} (hV : IsAffineOpen V) (hle : V ≤ eSec D.P.A ⁻¹ᵁ D.P.L.U j)
    (y : Spec (CommRingCat.of F)) (hy : (jFK (R := R) F ≫ jK R) y ∈ V)
    (J : (Spec (CommRingCat.of F) ⟶ D.P.A.left) → D.P.L.ι) (hj : J ((jFK (R := R) F ≫ jK R) ≫ eSec D.P.A) = j) :
    ∃ r ∈ I.map (DegPre.toOpen V), (val (D.psi χ) (jFK (R := R) F) y J).val = gs (jFK (R := R) F ≫ jK R) y V r := by
  have hx : D.xK χ = jK R ≫ eSec D.P.A := by
    rw [← hc]; simp [DegPre.xK, ptK]
  have le' : jK R ⁻¹ᵁ V ≤ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => j) := fun x hxV =>
    Set.mem_iInter.2 fun k => by
      rw [hx]; exact hle hxV
  obtain ⟨r, hr, hψ⟩ := hχ (fun _ => j) V hV (by rw [hc]; exact hle) le'
  refine ⟨r, hr, ?_⟩
  have e := val_of (D.psi χ) (jFK (R := R) F) y J (fun _ => j) (fun _ => by
    rw [← hj]; exact congrArg J ((congrArg (jFK (R := R) F ≫ ·) hx).trans (Category.assoc _ _ _).symm))
  refine (congrArg Units.val e).trans ?_
  refine (gs_unit _ y _ (le' hy) _).symm.trans ((gs_res _ y le' hy _).symm.trans ?_)
  exact (congrArg (gs (jFK (R := R) F) y _) hψ.symm).trans (gs_pull _ (jK R) y V hy _)
end GlobalTheory.IotaInj
