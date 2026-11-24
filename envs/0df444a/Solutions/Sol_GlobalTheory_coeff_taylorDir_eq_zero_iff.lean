-- Prove2me | solution 1 for GlobalTheory.coeff_taylorDir_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:20.942491+00:00
-- url     : https://prove2.me/submissions/25c9e5f3-78f4-451c-b492-ed7e48a70691

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_ofFn
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
theorem _root_.solution (hu : Submodule.span ℂ (Set.range u) = ⊤)
    (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    (∀ m : σ →₀ ℕ, m.degree = n → MvPowerSeries.coeff m (taylorDir u f) = 0) ↔
      iteratedFDeriv ℂ n f 0 = 0 := by
  classical
  have hdeg : ∀ m : σ →₀ ℕ, Multiset.card (Finsupp.toMultiset m) = m.degree := fun m => by
    rw [Finsupp.card_toMultiset]; rfl
  constructor
  · intro h
    refine ContinuousMultilinearMap.toMultilinearMap_injective
      (MultilinearMap.ext_of_span_eq_top (g := fun _ => u) (fun _ => hu) fun j => ?_)
    have hl : ((List.ofFn j : List σ) : Multiset σ) =
        Finsupp.toMultiset (Multiset.toFinsupp (List.ofFn j : List σ)) := by simp
    have h1 := h (Multiset.toFinsupp (List.ofFn j : List σ)) (by rw [← hdeg, ← hl]; simp)
    rw [coeff_taylorDir_eq_lineDerivList u hf hl, List.map_ofFn, lineDerivList_ofFn hf,
      mul_eq_zero_iff_left (inv_ne_zero (cast_prod_factorial_ne_zero _))] at h1
    exact h1
  · rintro h m rfl
    rw [← hdeg] at h
    rw [coeff_taylorDir, dirPolyDeriv_monomial_one, h]
    simp
end GlobalTheory
