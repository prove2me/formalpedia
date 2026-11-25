-- Prove2me | solution 1 for GlobalTheory.DiagBlock.restrictExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:58:30.375857+00:00
-- url     : https://prove2.me/submissions/622d5e97-16d5-4a0a-9a6d-b7cfd0ec4964

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Theorems.Thm_GlobalTheory_DiagBlock_restr_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
namespace GlobalTheory.DiagBlock
private lemma coeff_mvExp' {C : Type} [Field C] {σ : Type} (h : MvPowerSeries σ C)
    (m : σ →₀ ℕ) : MvPowerSeries.coeff m (mvExp h) =
      ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (h ^ k) / (k.factorial : C) := rfl
section Kill
variable {R : Type} [CommRing R] {σ : Type}
end Kill
end GlobalTheory.DiagBlock
end
end

set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
namespace GlobalTheory.DiagBlock
theorem _root_.solution : RestrictExp := by
  intro C _ _ n0 n hn h
  ext m
  rw [restr_eq, restr_eq, MvPowerSeries.coeff_killCompl, coeff_mvExp', coeff_mvExp']
  have hdeg : (Finsupp.embDomain ⟨embV hn, embV_inj hn⟩ m).degree = m.degree := by
    rw [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]
  rw [hdeg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_pow, MvPowerSeries.coeff_killCompl]
end GlobalTheory.DiagBlock
