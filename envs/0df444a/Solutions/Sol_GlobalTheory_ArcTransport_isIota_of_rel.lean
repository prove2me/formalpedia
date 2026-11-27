-- Prove2me | solution 1 for GlobalTheory.ArcTransport.isIota_of_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:55:42.620898+00:00
-- url     : https://prove2.me/submissions/30f339da-a607-4892-91c0-b152893be182

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
import Theorems.Thm_GlobalTheory_ArcTransport_base_comm
import Theorems.Thm_GlobalTheory_ArcTransport_GtRel_isIota
import Theorems.Thm_GlobalTheory_ArcTransport_be_half
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff


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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {k : Type} [Field k] {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF)
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left} (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X)
  {F : Type} [Field F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F] (uF : F)
variable {a w e uF}
variable [IsAlgClosed F] {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A} (hW : WitData a P oP φ he w e)
  (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
    algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)))
  (hu : uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X))
include hW hF hu
namespace GlobalTheory.ArcTransport
theorem _root_.solution {x : a.D₀.X} {g₀ : GtPtF a.D₀ F} {g : GtPtF P.toPre F}
    (h : GtRel w e.toAddEquiv (fun z => Units.mk0 uF (u_ne_zero hu) ^ a.be x z) g₀ g) (hι : GtPtF.IsIota x g₀) :
    GtPtF.IsIota (e x) g := by
  obtain ⟨gp, hw, hr, -, hc, hψ⟩ := hW
  refine GtRel.isIota gp (base_comm hF) (e := e.toAddEquiv) hc ((isGen_iff w).1 hw) hr
    (v := fun y => Units.mk0 uF (u_ne_zero hu) ^ (a.be y y / 2)) (fun χ => ?_) (fun χ => ?_) h hι
  · rw [Units.val_zpow_eq_zpow_val]
    exact hψ F uF hF hu χ
  · rw [be_half, zpow_add, zpow_add]
end GlobalTheory.ArcTransport
