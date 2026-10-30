-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_head_max_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:28:27.625956+00:00
-- url     : https://prove2.me/submissions/310dac0f-f2d9-443c-ba6d-ff00ccee422c

import Mathlib
import Definitions.Def_OAIQ081S078
import Definitions.Def_OAIQ081S089
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProducedHeads_problem_computed_energies
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProducedHeads_source_max_le_of_energy

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramWeights
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit positive denominator and bit bounds for the two rational weights. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram

theorem Weights.ofFractions_incidence (xn xd yn yd : ℕ) (hxd : 0 < xd) (hyd : 0 < yd) :
    ((yn : ℚ)/yd)^2 =
      ((Weights.ofFractions xn xd yn yd hxd hyd).incidence : ℚ) /
        (Weights.ofFractions xn xd yn yd hxd hyd).denominator := by
  have hx : (xd : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hxd
  have hy : (yd : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hyd
  simp only [Weights.ofFractions, Nat.cast_mul, Nat.cast_pow]
  field_simp


theorem Weights.ofFractions_head (xn xd yn yd : ℕ) (hxd : 0 < xd) (hyd : 0 < yd) :
    ((xn : ℚ)/xd)^2 =
      ((Weights.ofFractions xn xd yn yd hxd hyd).head : ℚ) /
        (Weights.ofFractions xn xd yn yd hxd hyd).denominator := by
  have hx : (xd : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hxd
  have hy : (yd : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hyd
  simp only [Weights.ofFractions, Nat.cast_mul, Nat.cast_pow]
  field_simp


end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedHeadsScope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native scope selector has precisely the rational weights required by
the correlated-packing proof. All lists here are the actual producer lists. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProducedHeads
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes PackingProgram
open PackingProgram.Assembly

theorem complete_alphabet_length {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    (a::tail).length=r^Q := by
  have he : (a::tail).toFinset=Finset.univ :=
    Finset.eq_univ_of_forall (fun z => List.mem_toFinset.mpr (haC z))
  calc
    _ = (a::tail).toFinset.card := (List.toFinset_card_of_nodup haN).symm
    _ = r^Q := by rw [he]; simp

theorem problem_x_eq (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    problemX p=(p.incidences:ℚ)/((p.s:ℚ)*(a::tail).length^2) := by
  unfold problemX
  rw [complete_alphabet_length a tail haN haC]
  simp only [card_universalType,Nat.cast_pow]
  rw [show p.Q*(1+1)=p.Q*2 by omega,pow_mul]
  ring

theorem problem_weight_head (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    (problemX p)^2=((problemWeights p a tail).head:ℚ)/(problemWeights p a tail).denominator := by
  rw [problem_x_eq p a tail haN haC]
  simpa only [problemWeights,Scope.weights,Nat.cast_mul,Nat.cast_pow] using
    Weights.ofFractions_head p.incidences (p.s*(a::tail).length^2) p.n (2*p.r)
      (Nat.mul_pos p.hs (pow_pos (by simp) 2)) (Nat.mul_pos (by decide) p.hr)

theorem problem_weight_incidence (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    ((p.n:ℚ)/(2*(p.r:ℚ)))^2=((problemWeights p a tail).incidence:ℚ)/
      (problemWeights p a tail).denominator := by
  simpa only [problemWeights,Scope.weights,Nat.cast_mul,Nat.cast_ofNat] using
    Weights.ofFractions_incidence p.incidences (p.s*(a::tail).length^2) p.n (2*p.r)
      (Nat.mul_pos p.hs (pow_pos (by simp) 2)) (Nat.mul_pos (by decide) p.hr)

theorem problem_head_max_bound_oai (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) (B b : ℕ)
    (hB : ∀ v,(Finset.univ.filter fun i =>
      PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le i=v).card ≤ B)
    (hb : ∀ e,(Finset.univ.filter fun i =>
      PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le i=e).card ≤ b)
    (hM : 0 < p.incidences) (hn : 0 < p.n)
    (hlarge : 4*(B+b)*(p.r^(2*p.Q))^2*p.s^2 ≤ p.incidences)
    (hhead : 16*p.Q*p.r^2 ≤ p.n) (low : Fin p.n → Bool) :
    (maxSelected p.n p.Q p.r ((p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
      (HeadIdentifierProgram.lowBits low) : ℚ) ≤ 3*(p.n:ℚ)/(2*(p.r:ℚ)) := by
  have hg := problem_computed_energies p a tail haN haC B b hB hb hM hn hlarge hhead
  apply source_max_le_of_energy
    (PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le)
    (PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le)
    a tail (Scope.terms p.scopes p.n p.mask p.Q) (problemWeights p a tail) (problemX p) p.hr
    (problem_weight_incidence p a tail) (problem_weight_head p a tail haN haC) low
  exact hg.2

end SubexponentialSAT.SqrtLog.LayoutProducedHeads

end
end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_head_max_bound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_head_max_bound_oai
