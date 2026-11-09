-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.K_column_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T08:58:13.196205+00:00
-- url     : https://prove2.me/submissions/45c004f5-2c3c-48bf-961d-de69ae04d529

import Mathlib
import Definitions.Def_OAIQ098G004
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_Numerical_inflate_contains_g
import Theorems.Thm_OAI_SharpPlanar_complexBasis_rule_error_g
import Theorems.Thm_OAI_SharpPlanar_complexLambda_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_complexZ_ofReal_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerAlpha IntegerCompact

lemma complexU_ofReal (n j : ℕ) (t : ℝ) : complexU n j t = u n j t := rfl
lemma complexV_ofReal (n j : ℕ) (t : ℝ) : complexV n j t = v n j t := rfl
lemma complexBasisMoment_ofReal (d e : Bool) (n j m : ℕ) (t : ℝ) :
    complexBasisMoment d e n j m t = basisMoment d e n j m t := by
  unfold complexBasisMoment complexBasis basisMoment basisFunction complexTransformedFactor
  rw [complexU_ofReal,complexV_ofReal,complexLambda_ofReal_g,complexZ_ofReal_g]
  cases d <;> cases e <;> simp <;> ring


end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quadrature enclosures for cardinal moments

The certified quadrature grid and cardinal basis enclosures bound the finite moment rule.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerAlpha IntegerGrid IntegerCompact

lemma basis_rule_value (n m : ℕ) (d e : Bool) :
    (∑ j : Fin 6, pieceRule (complexBasisMoment d e n j.val m) j.val) =
      momentRuleValue quadraturePoint fejerWeight n m d e := by
  unfold pieceRule momentRuleValue
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  have ht : diskAffine j.val (fejerNode v.val) = (quadraturePoint j.val v.val:ℂ) := by
    unfold diskAffine diskCenter quadraturePoint
    push_cast
    ring
  rw [ht,complexBasisMoment_ofReal]

end SharpPlanar

end OAI
end

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
  rw [complexBasisMoment_ofReal,show density { C := 0, c₀ := 0, d₀ := 0, x := columnVector n d } j t = basisFunction d n.val j t from density_column n d j t]
  unfold kernelMoment basisMoment
  (cases e <;> simp); ring


lemma K_column_rule_error {n : Node} {m : ℕ} (hn : n.val ≤ 100) (hm : m ≤ 100)
    (d e : Bool) :
    |K (positiveData (columnVector n d)) (if e then 1 else 0) m -
      (momentRuleValue quadraturePoint fejerWeight n.val m d e).re| < 1/10^22 := by
  rw [K_column_integral,← basis_rule_value]
  exact (Complex.abs_re_le_norm _).trans_lt (complexBasis_rule_error_g hn hm d e)

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

lemma K_column_contains_g_oai {n : Node} {m : ℕ} (hn : n.val ≤ 100) (hm : m ≤ 100)
    (d e : Bool) {a : CBox}
    (ha : a.Contains (momentRuleValue quadraturePoint fejerWeight n.val m d e)) :
    (inflate a.re).Contains (K (positiveData (columnVector n d)) (if e then 1 else 0) m) :=
  inflate_contains_g ha.1 (K_column_rule_error hn hm d e)

end Numerical
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.K_column_contains_g_oai := @OAI.SharpPlanar.Numerical.K_column_contains_g_oai
