-- Prove2me | solution 1 for GlobalTheory.ArcTransport.gtRel_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:29:21.269873+00:00
-- url     : https://prove2.me/submissions/1009d914-fa88-4c76-a3b0-3a2f3d3d6cf1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
import Theorems.Thm_GlobalTheory_ArcTransport_genRel_val
import Theorems.Thm_P2M_GlobalTheory_ArcTransport_gt__push_64b33aecfb9b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_gt


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
include hc hw
namespace GlobalTheory.ArcTransport
theorem _root_.solution (u : D.X → Fˣ) (g₀ : GtPtF D F) (g : GtPtF D' F) :
    GtRel w e u g₀ g ↔ pushF gp hT g.b = g₀.b ∧ ∀ χ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' →
      (wVal w y J J' (cP D' _ (e χ) * g.b))⁻¹ * wVal w y J J' (cP D' _ (e χ)) * wVal w y J J' g.b *
        (wVal w y J J' 1)⁻¹ * vS (g.s (e χ)) y J' = unitStk y (u χ) * vS (g₀.s χ) y J := by
  have key := fun χ => genRel_val hw D.P.isLB D'.P.isLB (g.isGen (e χ)) (g₀.isGen χ) (u χ)
  have pr := fun χ (y : Sp F) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι) (J' : (Sp F ⟶ D'.P.A.left) → D'.P.L.ι) =>
    prod_gt g.b (e χ) (fun q => Geo.Tor.gw w q y (J (q ≫ Φ)) (J' q))
  constructor
  · intro H
    exact ⟨Over.OverMorphism.ext ((H 0).1 2), fun χ y J J' hJ hJ' =>
      (congrArg (fun q : ((Sp F).presheaf.stalk y)ˣ => q * vS (g.s (e χ)) y J') (pr χ y J J').symm).trans (((key χ).1 (H χ)).2 y J J' hJ hJ')⟩
  · rintro ⟨hb, H⟩ χ
    exact (key χ).2 ⟨fun i => by rw [← hb]; exact gtφ_push gp hT hc _ _ i, fun y J J' hJ hJ' =>
      (congrArg (fun q : ((Sp F).presheaf.stalk y)ˣ => q * vS (g.s (e χ)) y J') (pr χ y J J')).trans (H χ y J J' hJ hJ')⟩
end GlobalTheory.ArcTransport
