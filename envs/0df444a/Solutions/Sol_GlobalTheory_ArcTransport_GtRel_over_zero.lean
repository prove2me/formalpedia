-- Prove2me | solution 1 for GlobalTheory.ArcTransport.GtRel.over_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:52:30.013842+00:00
-- url     : https://prove2.me/submissions/b50b9ab0-b998-4fe6-bacd-4738f9dbab9c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
import Theorems.Thm_GlobalTheory_ArcTransport_pushF_one
import Theorems.Thm_GlobalTheory_ArcTransport_pushF_injective
import Theorems.Thm_GlobalTheory_ArcTransport_gtRel_iff

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
include gp hT hc hw
namespace GlobalTheory.ArcTransport
namespace GtRel
theorem _root_.solution {u : D.X → Fˣ} {g₀ : GtPtF D F} {g : GtPtF D' F} (h : GtRel w e u g₀ g) (hb : g₀.b = 1) :
    g.b = 1 ∧ ∀ χ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' →
      vS (g.s (e χ)) y J' = unitStk y (u χ) * vS (g₀.s χ) y J := by
  obtain ⟨b₁, v₁⟩ := (gtRel_iff gp hT hc hw _ _ _).1 h
  have hb' : g.b = 1 := pushF_injective gp hT (by rw [pushF_one, b₁, hb])
  refine ⟨hb', fun χ y J J' hJ hJ' => ?_⟩
  have v := v₁ χ y J J' hJ hJ'
  rw [show cP D' (TF (R := R') F) (e χ) * g.b = cP D' _ (e χ) by rw [hb', _root_.mul_one],
    show wVal w y J J' g.b = wVal w y J J' 1 by rw [hb'], inv_mul_cancel, _root_.one_mul, mul_inv_cancel,
    _root_.one_mul] at v
  exact v
end GtRel
end GlobalTheory.ArcTransport
