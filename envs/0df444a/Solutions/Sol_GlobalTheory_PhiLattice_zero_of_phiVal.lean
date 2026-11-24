-- Prove2me | solution 1 for GlobalTheory.PhiLattice.zero_of_phiVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:43:44.070798+00:00
-- url     : https://prove2.me/submissions/a77f0ba7-ac26-426d-b7ef-347410fdcf68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LatticePartCongrOfPhiRel
import Theorems.Thm_GlobalTheory_PhiLattice_trPt_inv_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_sval_zero_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sec_ext_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PhiLattice
open ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.PhiLattice
theorem _root_.solution {n : ℕ} (p p' : QkPt D F n)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n)))
    (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n)))
    {s t : Fam D F n} (h : PhiVal p w s.s t.s) (h' : PhiVal p' w' s.s t.s) {α α' : D.X}
    (e : α' + p'.y = α + p.y) (h0 : ∀ j, (s.s α).f j = 0) : ∀ j, (s.s α').f j = 0 := by
  intro j
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  have e₁ := h α _ rfl _ (DegPre.trPt D F p'.g.b⁻¹) y J hJ
  have e₂ := h' α' _ e _ (DegPre.trPt D F p'.g.b⁻¹) y J hJ
  rw [UUA.sval_zero_of h0 _ y J (hJ.mem _ _), MulZeroClass.zero_mul] at e₁
  rw [e₁, trPt_inv_comp, Over.id_left] at e₂
  rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]
  exact (Units.mul_left_eq_zero _).1 e₂.symm
end GlobalTheory.PhiLattice
