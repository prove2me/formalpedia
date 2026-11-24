-- Prove2me | solution 1 for GlobalTheory.GLDoubling.nabs_det_torusElt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:55:16.749826+00:00
-- url     : https://prove2.me/submissions/5a9c43e3-f77d-4c65-8ceb-c3506ae9809c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Theorems.Thm_GlobalTheory_GLDoubling_nabs_unif
import Theorems.Thm_GlobalTheory_GLDoubling_val_torusElt
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG
open scoped NNReal Pointwise
open GlobalTheory GlobalTheory.GLDoubling
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n]
variable {k n}
namespace GlobalTheory.GLDoubling
theorem _root_.solution {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (e : n → ℤ) :
    nabs k (GeneralLinearGroup.det (torusElt k n ϖ e)) = (resCard k : ℝ) ^ (-∑ i, e i) := by
  have h1 : GeneralLinearGroup.det (torusElt k n ϖ e) = ϖ ^ ∑ i, e i := by
    ext
    rw [GeneralLinearGroup.val_det_apply, val_torusElt, det_diagonal, Units.val_zpow_eq_zpow_val]
    induction (Finset.univ : Finset n) using Finset.induction_on with
    | empty => simp
    | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ ϖ.ne_zero, ih]
  have h2 := nabs_unif hϖ
  unfold nabs at h2 ⊢
  rw [h1, map_zpow, NNReal.coe_zpow, h2, _root_.inv_zpow']
end GlobalTheory.GLDoubling
