-- Prove2me | solution 1 for GlobalTheory.ArcTransport.GtRel.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:43:53.569974+00:00
-- url     : https://prove2.me/submissions/c5c20bdc-b267-4182-ae94-d6583d0569fe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
import Theorems.Thm_P2M_GlobalTheory_ArcTransport_exists_good__b067f9275064
import Theorems.Thm_GlobalTheory_ArcTransport_pushF_injective
import Theorems.Thm_GlobalTheory_ArcTransport_gtRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
theorem _root_.solution {u : D.X → Fˣ} {g₀ : GtPtF D F} {g g' : GtPtF D' F} (h : GtRel w e u g₀ g)
    (h' : GtRel w e u g₀ g') : g = g' := by
  obtain ⟨b₁, v₁⟩ := (gtRel_iff gp hT hc hw u g₀ g).1 h
  obtain ⟨b₂, v₂⟩ := (gtRel_iff gp hT hc hw u g₀ g').1 h'
  have hb : g.b = g'.b := pushF_injective gp hT (b₁.trans b₂.symm)
  obtain ⟨b, s, hs, s0, sm⟩ := g
  obtain ⟨b', s', hs', s0', sm'⟩ := g'
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := funext fun χ => by
    obtain ⟨χ, rfl⟩ := e.surjective χ
    have : (s (e χ)).s = (s' (e χ)).s := funext fun j => unit_ext fun y hy => by
      obtain ⟨J, hJ⟩ := exists_good' D.P.isLB (Y := Sp F) y
      obtain ⟨J', hJ'⟩ := exists_good' D'.P.isLB (Y := Sp F) y
      have v : vS (s (e χ)) y J' = vS (s' (e χ)) y J' :=
        mul_left_cancel ((v₁ χ y J J' hJ hJ').trans (v₂ χ y J J' hJ hJ').symm)
      exact (gen_trans (hs _) (𝟙 _) y hy (hJ'.mem _ (𝟙 _))).trans ((congrArg _ v).trans
        (gen_trans (hs' _) (𝟙 _) y hy (hJ'.mem _ (𝟙 _))).symm)
    cases h₁ : s (e χ)
    cases h₂ : s' (e χ)
    rw [h₁, h₂] at this
    exact congrArg _ this
  rfl
end GtRel
end GlobalTheory.ArcTransport
