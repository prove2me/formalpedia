-- Prove2me | solution 1 for GlobalTheory.ArcTransport.psi_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:29:56.014171+00:00
-- url     : https://prove2.me/submissions/76570518-1f3e-4430-b1ab-75d2378c3437

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
import Theorems.Thm_GlobalTheory_ArcTransport_genRel_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ArcTransport
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {Φ : D'.P.A.left ⟶ D.P.A.left}
variable {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
variable (gp : IsGrpPullback D'.P.A D.P.A (spMap f) Φ) (hT : (TF (R := R') F).hom ≫ spMap f = (TF (R := R) F).hom)
variable {e : D.X ≃+ D'.X} (hc : ∀ y, (D'.c (e y)).left ≫ Φ = spMap f ≫ (D.c y).left)
variable {w : LB.Iso D'.P.L (D.P.L.pull Φ)} (hw : PGen w)
variable {he : eSec D'.P.A ≫ Φ = spMap f ≫ eSec D.P.A}
  (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
    (rigPullOf Φ (spMap f) he D.P.L D.rig))
include hw
namespace GlobalTheory.ArcTransport
theorem _root_.solution {v : Fˣ} {χ : D.X} (hψ : GenRel w (LB.pullGen _ _ _ (D'.psi (e χ)) (jFK (R := R') F))
    (LB.pullGen _ _ _ (D.psi χ) (jFK (R := R) F)) (v : F)) {y : Sp F} {J J'} (hJ : Good D.P.L y J)
    (hJ' : Good D'.P.L y J') :
    (wVal w y J J' (cP D' _ (e χ)))⁻¹ * vK (D'.psi (e χ)) y J' = unitStk y v * vK (D.psi χ) y J := by
  have a₁ : jFK (R := R') F ≫ D'.xK (e χ) = (cP D' (TF (R := R') F) (e χ)).left := (Category.assoc _ _ _).symm
  have H := ((genRel_val hw D.P.isLB D'.P.isLB (pullGen_isGen _ _ _ _ (D'.psi_gen _) _)
    (pullGen_isGen _ _ _ _ (D.psi_gen _) _) v).1 hψ).2 y J J' hJ hJ'
  rw [Fintype.prod_unique, zpow_neg_one] at H
  have b₁ : vS (LB.pullGen _ _ _ (D'.psi (e χ)) (jFK (R := R') F)) y J' = vK (D'.psi (e χ)) y J' := val_pull hJ' _ _ _
  have b₂ : vS (LB.pullGen _ _ _ (D.psi χ) (jFK (R := R) F)) y J = vK (D.psi χ) y J := val_pull hJ _ _ _
  rw [← b₁, ← b₂, wVal, ← a₁]
  exact H
end GlobalTheory.ArcTransport
