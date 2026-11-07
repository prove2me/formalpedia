-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.K_column_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T17:05:39.51589+00:00
-- url     : https://prove2.me/submissions/9f2b0e98-4f58-4ac5-a937-66b08f17a8b1

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_Numerical_inflate_contains_e
import Theorems.Thm_OAI_SharpPlanar_basis_rule_value_e
import Theorems.Thm_OAI_SharpPlanar_complexBasisMoment_ofReal_e
import Theorems.Thm_OAI_SharpPlanar_complexBasis_rule_error_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Entries of the cardinal interpolation operator

The columns of the interpolation operator are cardinal basis functions, and
certified quadrature controls their value and derivative entries.
-/

namespace SharpPlanar
open IntegerBasis IntegerIntervals IntegerGrid


lemma density_column (n : Node) (d : Bool) (j : ℕ) (t : ℝ) :
    density (positiveData (columnVector n d)) j t = basisFunction d n.val j t := by
  classical
  unfold density positiveData columnVector
  simp only [Complex.ofReal_zero, zero_mul, zero_add]
  rw [tsum_eq_single n]
  · cases d <;> simp [basisFunction,lp.single_apply]
  · intro k hk
    have hf : (k,false) ≠ (n,d) := fun h => hk (congrArg Prod.fst h)
    have ht : (k,true) ≠ (n,d) := fun h => hk (congrArg Prod.fst h)
    simp [Pi.single_eq_of_ne hf,Pi.single_eq_of_ne ht]

lemma K_column_integral (n : Node) (d e : Bool) (m : ℕ) :
    K (positiveData (columnVector n d)) (if e then 1 else 0) m =
      (∑ j : Fin 6, pieceIntegral (complexBasisMoment d e n.val j.val m) j.val).re := by
  unfold K positiveData
  simp only [Complex.ofReal_zero,zero_mul,zero_add]
  rw [← Finset.sum_range (fun j => pieceIntegral (complexBasisMoment d e n.val j m) j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  unfold pieceIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [complexBasisMoment_ofReal_e,show density { C := 0, c₀ := 0, d₀ := 0, x := columnVector n d } j t = basisFunction d n.val j t from density_column n d j t]
  unfold kernelMoment basisMoment
  (cases e <;> simp); ring


lemma K_column_rule_error {n : Node} {m : ℕ} (hn : n.val ≤ 100) (hm : m ≤ 100)
    (d e : Bool) :
    |K (positiveData (columnVector n d)) (if e then 1 else 0) m -
      (momentRuleValue quadraturePoint fejerWeight n.val m d e).re| < 1/10^22 := by
  rw [K_column_integral,← basis_rule_value_e]
  exact (Complex.abs_re_le_norm _).trans_lt (complexBasis_rule_error_e hn hm d e)

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_NodeIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
namespace Numerical

lemma K_column_contains_e_oai {n : Node} {m : ℕ} (hn : n.val ≤ 100) (hm : m ≤ 100)
    (d e : Bool) {a : CBox}
    (ha : a.Contains (momentRuleValue quadraturePoint fejerWeight n.val m d e)) :
    (inflate a.re).Contains (K (positiveData (columnVector n d)) (if e then 1 else 0) m) :=
  inflate_contains_e ha.1 (K_column_rule_error hn hm d e)

end Numerical
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.K_column_contains_e_oai := @OAI.SharpPlanar.Numerical.K_column_contains_e_oai
