-- Prove2me | solution 1 for GlobalTheory.ArcTransport.IsTransport.torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:09:41.994465+00:00
-- url     : https://prove2.me/submissions/d84de268-181f-445c-9488-455ba1aaa8c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
import Theorems.Thm_GlobalTheory_ArcTransport_base_comm
import Theorems.Thm_GlobalTheory_ArcTransport_GtRel_torus
import Theorems.Thm_GlobalTheory_ArcTransport_gtRel_zpow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
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
theorem _root_.solution {n : ℕ} {q₀ : QkPt a.D₀ F n} {q : QkPt P.toPre F n} (h : IsTransport a w e uF q₀ q)
    (hy : q₀.y = 0) {t : a.D₀.X → F} (hb : q₀.g.b = DegPre.zeroF a.D₀ F)
    (ht : ∀ χ j, LB.Coh a.D₀.P.L (DegPre.gtφ a.D₀ F q₀.g.b χ) j →
      ⊤ ≤ LB.wchart a.D₀.P.L (DegPre.gtφ a.D₀ F q₀.g.b χ) j → valF (𝟙 (Sp F)) _ ((q₀.g.s χ).s j).val = t χ) :
    q.y = 0 ∧ q.g.b = DegPre.zeroF P.toPre F ∧ ∀ χ j, LB.Coh P.toPre.P.L (DegPre.gtφ P.toPre F q.g.b χ) j →
      ⊤ ≤ LB.wchart P.toPre.P.L (DegPre.gtφ P.toPre F q.g.b χ) j →
      valF (𝟙 (Sp F)) _ ((q.g.s χ).s j).val = t (e.symm χ) := by
  obtain ⟨gp, hw, -, -, hc, -⟩ := hW
  obtain ⟨h₁, h₂⟩ := GtRel.torus gp (base_comm hF) (e := e.toAddEquiv) hc ((isGen_iff w).1 hw)
    ((gtRel_zpow (u_ne_zero hu) _ _ _).2 h.2) hb ht
  refine ⟨by rw [h.1, hy, map_zero], h₁, fun χ j hj hle => (h₂ χ j hj hle).trans ?_⟩
  rw [hy, map_zero, LinearMap.zero_apply, Int.zero_ediv, zpow_zero, Units.val_one, _root_.one_mul]
  rfl
end IsTransport
end GlobalTheory.ArcTransport
