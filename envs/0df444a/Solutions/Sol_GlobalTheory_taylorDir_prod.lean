-- Prove2me | solution 1 for GlobalTheory.taylorDir_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:21.843624+00:00
-- url     : https://prove2.me/submissions/175d4607-7665-4e13-b484-19d317b878cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero



set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {σ W : Type*} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
variable (u : σ → W) {f g : W → ℂ}
namespace GlobalTheory
theorem _root_.solution {κ : Type*} (s : Finset κ) {F : κ → W → ℂ}
    (hF : ∀ k ∈ s, AnalyticAt ℂ (F k) 0) :
    taylorDir u (fun z => ∏ k ∈ s, F k z) = ∏ k ∈ s, taylorDir u (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hs : ∀ k ∈ s, AnalyticAt ℂ (F k) 0 := fun k hk => hF k (Finset.mem_insert_of_mem hk)
    simp only [Finset.prod_insert hj]
    rw [← ih hs]
    exact taylorDir_mul u (hF j (Finset.mem_insert_self _ _)) (Finset.analyticAt_fun_prod _ hs)
end GlobalTheory
