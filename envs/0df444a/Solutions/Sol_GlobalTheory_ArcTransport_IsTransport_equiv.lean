-- Prove2me | solution 1 for GlobalTheory.ArcTransport.IsTransport.equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:02:24.456554+00:00
-- url     : https://prove2.me/submissions/5d727abf-9bba-450f-ae83-31eb23f2ccef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
import Theorems.Thm_GlobalTheory_ArcTransport_base_comm
import Theorems.Thm_GlobalTheory_ArcTransport_exists_gtRel
import Theorems.Thm_GlobalTheory_ArcTransport_GtRel_isAdd
import Theorems.Thm_GlobalTheory_ArcTransport_gtRel_zpow
import Theorems.Thm_GlobalTheory_ArcTransport_isIota_of_rel
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
namespace IsTransport
theorem _root_.solution (hG : GlobalFnsSt) {n : ℕ} (hn₀ : 0 < n) (hn : n ∣ l.M') {q₀ q₀' : QkPt a.D₀ F n}
    {q q' : QkPt P.toPre F n} (h : IsTransport a w e uF q₀ q) (h' : IsTransport a w e uF q₀' q')
    (H : QkPt.Equiv a.D₀ F q₀ q₀') : QkPt.Equiv P.toPre F q q' := by
  have hι' := fun x g₀ g => isIota_of_rel hW hF hu (x := x) (g₀ := g₀) (g := g)
  obtain ⟨gp, hw, hr, -, hc, hψ⟩ := hW
  have hT := base_comm hF
  have hw' := (isGen_iff w).1 hw
  obtain ⟨z, hy, g₀, hι, hadd⟩ := H
  obtain ⟨g, hg⟩ := exists_gtRel gp hT (e := e.toAddEquiv) hc hw' hG
    (fun χ => Units.mk0 uF (u_ne_zero hu) ^ a.be z χ) (fun x y => by rw [map_add, zpow_add]) g₀
  refine ⟨e z, by rw [h'.1, h.1, hy, map_add, map_nsmul], g, hι' z g₀ g hg hι, ?_⟩
  refine GtRel.isAdd gp hT (e := e.toAddEquiv) hc hw' hG (fun χ => ?_) ((gtRel_zpow (u_ne_zero hu) _ _ _).2 h.2) hg
    ((gtRel_zpow (u_ne_zero hu) _ _ _).2 h'.2) hadd
  rw [← zpow_add, hy, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul,
    Int.add_mul_ediv_left _ _ (Int.natCast_ne_zero.2 hn₀.ne')]
end IsTransport
end GlobalTheory.ArcTransport
