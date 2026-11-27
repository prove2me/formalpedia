-- Prove2me | solution 1 for GlobalTheory.ArcTransport.transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:20:29.977599+00:00
-- url     : https://prove2.me/submissions/02185450-6c85-470d-b640-064364a56b3e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
import Theorems.Thm_GlobalTheory_ArcTransport_GtRel_unique
import Theorems.Thm_GlobalTheory_ArcTransport_GtRel_torus
import Theorems.Thm_GlobalTheory_ArcTransport_exists_transport
import Theorems.Thm_GlobalTheory_ArcTransport_IsTransport_b_comp
import Theorems.Thm_GlobalTheory_ArcTransport_IsTransport_unique
import Theorems.Thm_GlobalTheory_ArcTransport_IsTransport_equiv
import Theorems.Thm_GlobalTheory_ArcTransport_IsTransport_torus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
namespace GlobalTheory.ArcTransport
theorem _root_.solution (hG : GlobalFnsSt) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) (hW : WitData a P oP φ he w e)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F] (uF : F)
    (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)))
    (hu : uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X))
    (n : ℕ) (hn₀ : 0 < n) (hn : n ∣ l.M') :
    (∀ q₀ : QkPt a.D₀ F n, ∃ q : QkPt P.toPre F n, IsTransport a w e uF q₀ q) ∧
    (∀ (q₀ : QkPt a.D₀ F n) (q : QkPt P.toPre F n), IsTransport a w e uF q₀ q → q.g.b.left ≫ φ = q₀.g.b.left) ∧
    (∀ (q₀ : QkPt a.D₀ F n) (q q' : QkPt P.toPre F n), IsTransport a w e uF q₀ q → IsTransport a w e uF q₀ q' →
      q = q') ∧
    (∀ (q₀ q₀' : QkPt a.D₀ F n) (q q' : QkPt P.toPre F n), IsTransport a w e uF q₀ q → IsTransport a w e uF q₀' q' →
      QkPt.Equiv a.D₀ F q₀ q₀' → QkPt.Equiv P.toPre F q q') ∧
    ∀ (q₀ : QkPt a.D₀ F n) (q : QkPt P.toPre F n) (t : a.D₀.X → F), IsTransport a w e uF q₀ q → q₀.y = 0 →
      (q₀.g.b = DegPre.zeroF a.D₀ F ∧ ∀ χ j, LB.Coh a.D₀.P.L (DegPre.gtφ a.D₀ F q₀.g.b χ) j →
        ⊤ ≤ LB.wchart a.D₀.P.L (DegPre.gtφ a.D₀ F q₀.g.b χ) j → valF (𝟙 (Sp F)) _ ((q₀.g.s χ).s j).val = t χ) →
      q.y = 0 ∧ q.g.b = DegPre.zeroF P.toPre F ∧ ∀ χ j, LB.Coh P.toPre.P.L (DegPre.gtφ P.toPre F q.g.b χ) j →
        ⊤ ≤ LB.wchart P.toPre.P.L (DegPre.gtφ P.toPre F q.g.b χ) j →
        valF (𝟙 (Sp F)) _ ((q.g.s χ).s j).val = t (e.symm χ) :=
  ⟨exists_transport hW hF hu hG hn, fun _ _ h => h.b_comp, fun _ _ _ h h' => h.unique hW hF hu h',
    fun _ _ _ _ h h' H => h.equiv hW hF hu hG hn₀ hn h' H, fun _ _ _ h hy ht => h.torus hW hF hu hy ht.1 ht.2⟩
end GlobalTheory.ArcTransport
