-- Prove2me | solution 1 for NemytskiiLebesgue.ennreal_holderTriple_of_lt_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:28.368709+00:00
-- url     : https://prove2.me/submissions/74b7524c-9f8b-4171-841b-fef4591dc31e

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Lipschitz

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped NNReal ENNReal
namespace NemytskiiLebesgue
theorem _root_.solution
    {p α : ℝ} (hp : 0 < p) (hα : 0 < α) :
    ENNReal.HolderTriple ↱(p / α) ↱p ↱(p / (α + 1)) := by
  constructor
  rw [ENNReal.ofReal_div_of_pos, ENNReal.ofReal_div_of_pos] <;> try positivity
  rw [←ENNReal.toReal_eq_toReal_iff'] <;> norm_num
  · rw [ENNReal.toReal_add] <;> norm_num [hp, hα]
    rw [ENNReal.toReal_ofReal hα.le,
        ENNReal.toReal_ofReal hp.le,
        ENNReal.toReal_ofReal (by positivity)]
    ring
  · grind
  · exact RCLike.ofReal_pos.→ hp
end NemytskiiLebesgue
