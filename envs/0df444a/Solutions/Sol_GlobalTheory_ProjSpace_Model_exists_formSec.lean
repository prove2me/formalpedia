-- Prove2me | solution 1 for GlobalTheory.ProjSpace.Model.exists_formSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:36:12.593775+00:00
-- url     : https://prove2.me/submissions/2c53c1d1-0d2e-4bf2-b005-cd42a521a8ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsFormOfEqRatioPowMul
import Theorems.Thm_GlobalTheory_ProjSpace_Model_resG_overlap_injective
import Theorems.Thm_GlobalTheory_ProjSpace_Model_exists_form_of_eq_ratio_pow_mul
import Theorems.Thm_GlobalTheory_ProjSpace_gradedMap_apply
import Theorems.Thm_GlobalTheory_ProjSpace_resG_formOn
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_appLinearBase_apply
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ProjSpace.gradedMap_apply
attribute [local simp] GlobalTheory.QCoh.Qcqs.appLinearBase_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace GlobalTheory.ProjSpace.Model
variable {R : Type} [CommRing R] {N : ℕ}
namespace GlobalTheory.ProjSpace.Model
theorem _root_.solution (n : ℕ) (s : (lbPow (O1 R (N + 1)) n).Sec) :
    ∃ f, ∃ hf : (f : MvPolynomial (Fin (N + 2)) R).IsHomogeneous n, s = formSec n f hf := by
  have hU := On_U R (N + 1) n
  have hc : ∀ i j : PUnit → Fin (N + 2),
      resG _ (inf_le_left.trans (hU i).le : _ ⊓ (On R (N + 1) n).U j ≤ _) (resG _ (hU i).ge (s.f i)) =
      ratioOn _ _ (inf_le_left.trans (hU i).le) (j PUnit.unit) ^ n *
        resG _ (inf_le_right.trans (hU j).le) (resG _ (hU j).ge (s.f j)) := by
    intro i j
    have e := On_g R (N + 1) n i j
    rw [zpow_natCast] at e
    have e' := (congrArg Units.val e).trans (Units.val_pow_eq_pow_val _ _)
    exact (s.compat i j).trans (congrArg (· * _) e')
  obtain ⟨f, hf, h0⟩ := exists_form_of_eq_ratio_pow_mul (i := 0) (j := 1) (by simp) n _ _
    (by rw [hU, hU]) _ _ (hc (fun _ => 0) (fun _ => 1))
  refine ⟨f, hf, ?_⟩
  have hk : ∀ k : PUnit → Fin (N + 2), resG _ (hU k).ge (s.f k) =
      formOn (chart R (N + 1) (k PUnit.unit)) _ le_rfl n f hf := by
    intro k
    refine resG_overlap_injective (k PUnit.unit) 0
      (inf_le_left.trans (hU k).le : _ ⊓ (On R (N + 1) n).U (fun _ => (0 : Fin (N + 2))) ≤ _) (by rw [hU, hU]) ?_
    rw [hc k (fun _ => 0), h0, resG_formOn, resG_formOn]
    exact (formOn_eq_ratioOn_pow_mul _ hf).symm
  obtain ⟨sf, sc⟩ := s
  have : sf = (formSec n f hf).f := funext fun k => by
    have e : sf k = resG _ (hU k).le (resG _ (hU k).ge (sf k)) := rfl
    exact e.trans (congrArg (resG _ (hU k).le) (hk k))
  subst this
  rfl
end GlobalTheory.ProjSpace.Model
