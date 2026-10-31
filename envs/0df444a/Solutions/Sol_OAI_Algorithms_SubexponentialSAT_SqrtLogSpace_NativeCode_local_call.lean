-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.local_call
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:52:05.636784+00:00
-- url     : https://prove2.me/submissions/32f25fc4-308f-4d90-beeb-77b78853d890

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S152
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LocalCode_exists_local_code_log_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SparseCodeSearch_local_search_runs

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StructuredSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix resource preservation for the actual finite instruction linker.
The source bound concerns every intermediate configuration. Unassigned caller
stacks retain their original contents. Local runtime bounds may be used for
polynomial subroutines, but no accumulated outer-loop time appears here. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

open BitProgram

/-- Every prefix of a relocated source execution is exactly the relocation of
the same-length source prefix, including a halt changed to a return jump. -/
theorem relocate_trace_prefix {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps prefixSteps : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b) {intermediate : Cfg R S L}
    (hle : prefixSteps ≤ steps)
    (hp : Trace q prefixSteps
      (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate) :
    ∃ source, Trace p prefixSteps a source ∧
      intermediate = ProgramLinking.embedCfg register stack label returnPc frame source := by
  obtain ⟨source, hsource⟩ := trace_prefix_exists tr hle
  refine ⟨source, hsource, ?_⟩
  exact trace_same_length_unique hp
    (ProgramLinking.relocate_trace p q register stack label returnPc frame
      hregister hstack hcode hsource)

/-- Port embedding preserves a uniform local stack bound and the caller's
off-port bound separately. It never charges the caller's frame repeatedly. -/
theorem relocate_trace_stack_bound {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace q prefixSteps
        (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound := by
  intro prefixSteps intermediate hle hp i
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix p q register stack label
    returnPc frame hregister hstack hcode tr hle hp
  by_cases hi : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [ProgramLinking.embedCfg_stack register stack label returnPc frame source hstack]
    exact (hsource prefixSteps source hle hs j).trans (Nat.le_max_left _ _)
  · rw [ProgramLinking.embedCfg_stack_frame register stack label returnPc frame source i hi]
    exact (hframe i).trans (Nat.le_max_right _ _)

theorem liftProgram_stack_bound {r s l R S : ℕ}
    (p : Program r s l) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : Cfg R S l)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (ProgramLinking.liftProgram p register stack) prefixSteps
        (ProgramLinking.embedCfg register stack id none frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound :=
  relocate_trace_stack_bound p _ register stack id none frame hregister hstack
    (fun _ => rfl) tr hsource hframe

/-- A structured call retains its callee's every-prefix stack bound in the
actual caller table. The table premise is the same one used by eval_trace. -/
theorem call_stack_bound {r s l L : ℕ} (routine : Program r s l)
    (caller : Program r s L) (label : Fin l → Fin L) (exit : Fin L)
    (hcode : ∀ pc, caller.code (label pc) =
      StructuredCalls.code (.call routine) label exit pc)
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (tr : Trace routine steps (a.withPC (some routine.entry)) (b.withPC none))
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace routine prefixSteps (a.withPC (some routine.entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace caller prefixSteps (a.withPC (some (label routine.entry))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp i
  have hinitial : ProgramLinking.embedCfg id id label (some exit)
      (a.withPC (some (label routine.entry))) (a.withPC (some routine.entry)) =
      a.withPC (some (label routine.entry)) := by
    simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc,
      StructuredProgram.State.withPC]
  rw [← hinitial] at hp
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix routine caller id id label
    (some exit) (a.withPC (some (label routine.entry)))
    Function.injective_id Function.injective_id hcode tr hle hp
  simpa [ProgramLinking.embedCfg] using hsource prefixSteps source hle hs i

/-- The final concrete halt instruction changes no stack and preserves the
bound already established through the command's exit boundary. -/
theorem compiled_halt_stack_bound {r s : ℕ} {command : StructuredCalls.Cmd r s}
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval command steps a b) (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled command inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled command inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Trace (StructuredCalls.compiled command inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled command inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp
  by_cases hbefore : prefixSteps ≤ steps
  · exact hsource prefixSteps intermediate hbefore hp
  · have hlast : prefixSteps = steps + 1 := by omega
    subst prefixSteps
    have heq := trace_same_length_unique hp
      (StructuredCalls.compiled_halt_trace heval inputStack outputStack)
    rw [heq]
    have hend := hsource steps (b.withPC (some (StructuredCalls.exitAddress command))) le_rfl
      (StructuredCalls.compiled_trace heval inputStack outputStack)
    exact hend

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CayleyCharacters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.instDecidableGood _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Real Walsh characters of the Boolean cube, with unnormalized Fourier sums. -/
namespace SubexponentialSAT.SqrtLog.Cayley
open scoped BigOperators

theorem character_eq_one_or_neg_one {r : ℕ} (a x : Cube r) :
    character a x = 1 ∨ character a x = -1 := by
  have h := character_sq a x
  rcases sq_eq_one_iff.mp h with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem character_sum {r : ℕ} (a : Cube r) :
    (∑ x : Cube r, character a x) = if a = 0 then (Fintype.card (Cube r) : ℝ) else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  · rw [ite_eq_right ha]
    unfold character
    rw [← Fintype.prod_sum (fun j (z : ZMod 2) => bitSign (a j * z))]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    have hlocal : ∀ b : ZMod 2, b ≠ 0 → (∑ z : ZMod 2, bitSign (b * z)) = 0 := by
      intro b hb
      have hb1 : b = 1 := by
        apply ZMod.val_injective
        rw [ZMod.val_one]
        have hval : b.val ≠ 0 := fun h => hb ((ZMod.val_eq_zero b).mp h)
        have hlt := b.val_lt
        omega
      subst b
      have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
        decide
      rw [hu]
      rw [Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
      rw [one_mul, one_mul, bitSign_zero, bitSign_one]
      norm_num
    exact hlocal (a j) hj

theorem character_sum_of_ne_zero {r : ℕ} (a : Cube r) (ha : a ≠ 0) :
    (∑ x : Cube r, character a x) = 0 := by rw [character_sum, ite_eq_right ha]

end SubexponentialSAT.SqrtLog.Cayley

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_WalshExistenceCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fully finite exponential-moment sampling. No measure space or randomized
algorithm is involved: all averages below are sums over finite function spaces. -/

namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators

variable {X A : Type*} [Fintype X] [Fintype A]

theorem sum_exp_le (f : X → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (hzero : ∑ x, f x = 0) (t : ℝ) :
    (∑ x, Real.exp (t * f x)) ≤
      (Fintype.card X : ℝ) * Real.exp (t ^ 2 / 2) := by
  calc
    (∑ x, Real.exp (t * f x)) ≤
        ∑ x, (Real.cosh t + f x * Real.sinh t) := by
      apply Finset.sum_le_sum
      intro x _
      simpa [mul_comm] using Real.exp_mul_le_cosh_add_mul_sinh (hf x) t
    _ = (Fintype.card X : ℝ) * Real.cosh t := by
      simp [Finset.sum_add_distrib, ← Finset.sum_mul, hzero]
    _ ≤ (Fintype.card X : ℝ) * Real.exp (t ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq t) (by positivity)

theorem sum_exp_samples_le (f : X → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (hzero : ∑ x, f x = 0) (D : ℕ) (t : ℝ) :
    (∑ s : Fin D → X, Real.exp (t * ∑ i, f (s i))) ≤
      (Fintype.card X : ℝ) ^ D * Real.exp ((D : ℝ) * t ^ 2 / 2) := by
  classical
  have heq : (∑ s : Fin D → X, Real.exp (t * ∑ i, f (s i))) =
      (∑ x, Real.exp (t * f x)) ^ D := by
    simp_rw [Finset.mul_sum, Real.exp_sum]
    rw [← Fintype.prod_sum (fun (_ : Fin D) (x : X) => Real.exp (t * f x))]
    simp
  rw [heq]
  calc
    (∑ x, Real.exp (t * f x)) ^ D ≤
        ((Fintype.card X : ℝ) * Real.exp (t ^ 2 / 2)) ^ D := by
      exact pow_le_pow_left₀ (by positivity) (sum_exp_le f hf hzero t) D
    _ = (Fintype.card X : ℝ) ^ D * Real.exp ((D : ℝ) * t ^ 2 / 2) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring

theorem sum_potential_le (f : A → X → ℝ) (hf : ∀ a x, |f a x| ≤ 1)
    (hzero : ∀ a, ∑ x, f a x = 0) (D : ℕ) (ε : ℝ) :
    (∑ s : Fin D → X, potential f D ε s) ≤
      (Fintype.card X : ℝ) ^ D *
        (2 * Fintype.card A * Real.exp ((D : ℝ) * ε ^ 2 / 2)) := by
  classical
  unfold potential
  rw [Finset.sum_comm]
  calc
    (∑ a, ∑ s : Fin D → X,
        (Real.exp (ε * ∑ i, f a (s i)) + Real.exp (-ε * ∑ i, f a (s i)))) ≤
        ∑ _a : A, (2 * (Fintype.card X : ℝ) ^ D *
          Real.exp ((D : ℝ) * ε ^ 2 / 2)) := by
      apply Finset.sum_le_sum
      intro a _
      rw [Finset.sum_add_distrib]
      have hp := sum_exp_samples_le (f a) (hf a) (hzero a) D ε
      have hn := sum_exp_samples_le (f a) (hf a) (hzero a) D (-ε)
      simp only [neg_sq] at hn
      linarith
    _ = _ := by simp; ring

theorem exists_samples [Nonempty X] (f : A → X → ℝ)
    (hf : ∀ a x, |f a x| ≤ 1) (hzero : ∀ a, ∑ x, f a x = 0)
    (D : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hbudget : 2 * (Fintype.card A : ℝ) < Real.exp ((D : ℝ) * ε ^ 2 / 2)) :
    ∃ s : Fin D → X, ∀ a, |∑ i, f a (s i)| ≤ ε * D := by
  classical
  by_contra h
  push Not at h
  have hpoint (s : Fin D → X) :
      Real.exp ((D : ℝ) * ε ^ 2) ≤ potential f D ε s := by
    obtain ⟨a, ha⟩ := h s
    have hterm : Real.exp ((D : ℝ) * ε ^ 2) ≤
        Real.exp (ε * ∑ i, f a (s i)) + Real.exp (-ε * ∑ i, f a (s i)) := by
      rcases le_total 0 (∑ i, f a (s i)) with hp | hn
      · rw [abs_of_nonneg hp] at ha
        have he := mul_le_mul_of_nonneg_left (le_of_lt ha) hε
        have : Real.exp ((D : ℝ) * ε ^ 2) ≤
            Real.exp (ε * ∑ i, f a (s i)) := by
          apply Real.exp_le_exp.mpr
          nlinarith
        linarith [Real.exp_pos (-ε * ∑ i, f a (s i))]
      · rw [abs_of_nonpos hn] at ha
        have he := mul_le_mul_of_nonneg_left (le_of_lt ha) hε
        have : Real.exp ((D : ℝ) * ε ^ 2) ≤
            Real.exp (-ε * ∑ i, f a (s i)) := by
          apply Real.exp_le_exp.mpr
          nlinarith
        linarith [Real.exp_pos (ε * ∑ i, f a (s i))]
    apply hterm.trans
    unfold potential
    exact Finset.single_le_sum
      (f := fun b : A => Real.exp (ε * ∑ i, f b (s i)) +
        Real.exp (-ε * ∑ i, f b (s i)))
      (fun b _ => by positivity) (Finset.mem_univ a)
  have hlo := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Fin D → X))) => hpoint s)
  have hhi := sum_potential_le f hf hzero D ε
  have hcard : (Fintype.card X : ℝ) ^ D > 0 := by
    exact pow_pos (by exact_mod_cast Fintype.card_pos) D
  have hstrict : (Fintype.card X : ℝ) ^ D *
      (2 * Fintype.card A * Real.exp ((D : ℝ) * ε ^ 2 / 2)) <
      (Fintype.card X : ℝ) ^ D * Real.exp ((D : ℝ) * ε ^ 2) := by
    apply mul_lt_mul_of_pos_left _ hcard
    have hh := mul_lt_mul_of_pos_right hbudget (Real.exp_pos ((D : ℝ) * ε ^ 2 / 2))
    rw [← Real.exp_add] at hh
    convert hh using 1 ; congr 1 ; ring
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow] at hlo
  linarith

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_WalshExistence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Existence and finite executable search for a small Walsh spectrum. -/
namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators
open Cayley

theorem exists_smallWalsh_of_budget (r D : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hbudget : 2 * (Fintype.card {a : Cube r // a ≠ 0} : ℝ) <
      Real.exp ((D : ℝ) * ε ^ 2 / 2)) :
    ∃ s : Fin D → Cube r, SmallWalsh s ε := by
  classical
  obtain ⟨s, hs⟩ := exists_samples
    (fun (a : {a : Cube r // a ≠ 0}) x => character a.val x)
    (by
      intro a x
      rcases character_eq_one_or_neg_one a.val x with h | h <;> rw [h] <;> norm_num)
    (fun a => character_sum_of_ne_zero a.val a.property) D ε hε hbudget
  refine ⟨s, ?_⟩
  intro a ha
  simpa [walsh] using hs ⟨a, ha⟩

theorem exists_smallWalsh (r D q : ℕ) (hq : 1 ≤ q)
    (hD : 8 * q ^ 2 * (r + 1) ≤ D) :
    ∃ s : Fin D → Cube r, SmallWalsh s (1 / (q : ℝ)) := by
  classical
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  apply exists_smallWalsh_of_budget r D (1 / (q : ℝ)) (by positivity)
  have hc : (Fintype.card {a : Cube r // a ≠ 0} : ℝ) ≤ (2 : ℝ) ^ r := by
    have hn := Fintype.card_subtype_le (fun a : Cube r => a ≠ 0)
    rw [cube_card] at hn
    exact_mod_cast hn
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hpow : (2 : ℝ) ^ (r + 1) ≤ Real.exp ((r : ℝ) + 1) := by
    calc
      (2 : ℝ) ^ (r + 1) ≤ (Real.exp 1) ^ (r + 1) :=
        pow_le_pow_left₀ (by norm_num) htwo _
      _ = Real.exp ((r : ℝ) + 1) := by rw [← Real.exp_nat_mul]; simp
  have hident : ((8 * q ^ 2 * (r + 1) : ℕ) : ℝ) * (1 / (q : ℝ)) ^ 2 / 2 =
      4 * ((r : ℝ) + 1) := by
    push_cast
    field_simp
    ring
  have hhalf : 4 * ((r : ℝ) + 1) ≤ (D : ℝ) * (1 / (q : ℝ)) ^ 2 / 2 := by
    rw [← hident]
    gcongr
  calc
    2 * (Fintype.card {a : Cube r // a ≠ 0} : ℝ) ≤ 2 * (2 : ℝ) ^ r := by
      gcongr
    _ = (2 : ℝ) ^ (r + 1) := by rw [pow_succ]; ring
    _ ≤ Real.exp ((r : ℝ) + 1) := hpow
    _ < Real.exp (4 * ((r : ℝ) + 1)) := by
      apply Real.exp_lt_exp.mpr
      have : (0 : ℝ) ≤ r := by positivity
      linarith
    _ ≤ Real.exp ((D : ℝ) * (1 / (q : ℝ)) ^ 2 / 2) := Real.exp_le_exp.mpr hhalf

theorem good_iff_smallWalsh {r D q : ℕ} (hq : 1 ≤ q) (s : Fin D → Cube r) :
    Good q s ↔ SmallWalsh s (1 / (q : ℝ)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  constructor
  · intro h a ha
    have hi := h a ha
    have hr : (q : ℝ) * |(walshInt s a : ℝ)| ≤ (D : ℝ) := by exact_mod_cast hi
    rw [walshInt_cast] at hr
    simpa only [Fintype.card_fin, div_eq_mul_inv, one_mul, mul_one, mul_comm] using
      (le_div_iff₀ hqpos).mpr (show |walsh s a| * q ≤ (D : ℝ) by nlinarith)
  · intro h a ha
    have hr := h a ha
    simp only [Fintype.card_fin] at hr
    have hr' : |walsh s a| ≤ (D : ℝ) / q := by
      simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hr
    have hh := (le_div_iff₀ hqpos).mp hr'
    have hz : (q : ℝ) * |(walshInt s a : ℝ)| ≤ (D : ℝ) := by
      rw [walshInt_cast]
      nlinarith
    exact_mod_cast hz

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

theorem degree_le (m B : ℕ) : degree m B ≤ m := min_le_left _ _

theorem degree_le_power (m B : ℕ) : degree m B ≤ 2 ^ logSize m :=
  (degree_le m B).trans (lt_two_pow_logSize m).le

theorem eight_mul_le_degreeBound (m : ℕ) {B : ℕ} (hB : 0 < B) :
    8 * B ≤ degreeBound m B := by
  have hL : 1 ≤ logSize m := logSize_pos m
  have hq : B ≤ gapDenom m B := by unfold gapDenom; nlinarith
  have hqpos := gapDenom_pos m hB
  have hsq : gapDenom m B ≤ gapDenom m B ^ 2 := by nlinarith
  unfold degreeBound
  nlinarith

theorem dimensionFor_le (m : ℕ) {D r : ℕ} (hD : 0 < D)
    (hr : m ≤ D * 2 ^ r) : dimensionFor m D ≤ r := by
  simp only [dimensionFor, dite_eq_left hD]
  exact Nat.find_min' (exists_dimension m hD) hr

theorem dimensionFor_self {m : ℕ} (hm : 0 < m) : dimensionFor m m = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact dimensionFor_le m hm (by simp)

theorem dimensionFor_lt_logSize (m : ℕ) {D : ℕ} (hD : 2 ≤ D) :
    dimensionFor m D < logSize m := by
  have hm := lt_two_pow_logSize m
  have hw : m ≤ D * 2 ^ (Nat.log 2 m) := by
    unfold logSize at hm
    rw [pow_succ] at hm
    nlinarith
  have hd := dimensionFor_le m (by omega : 0 < D) hw
  unfold logSize
  omega

theorem dimension_lt_logSize {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    dimension m B < logSize m := by
  by_cases h : degreeBound m B ≤ m
  · have hD : 2 ≤ degreeBound m B := by
      have := eight_mul_le_degreeBound m hB
      omega
    simpa [dimension, degree, min_eq_right h] using dimensionFor_lt_logSize m hD
  · have hd : degree m B = m := min_eq_left (by omega)
    simpa [dimension, hd, dimensionFor_self hm] using logSize_pos m

theorem dimension_zero_of_small {m B : ℕ} (hm : 0 < m)
    (h : m ≤ degreeBound m B) : dimension m B = 0 := by
  simp [dimension, degree, min_eq_left h, dimensionFor_self hm]

theorem walsh_degree_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (hr : dimension m B ≠ 0) :
    8 * gapDenom m B ^ 2 * (dimension m B + 1) ≤ degree m B := by
  have hlarge : degreeBound m B ≤ m := by
    by_contra h
    exact hr (dimension_zero_of_small hm (by omega))
  have hrL : dimension m B + 1 ≤ logSize m := dimension_lt_logSize hm hB
  rw [degree, min_eq_right hlarge, degreeBound]
  exact Nat.mul_le_mul_left _ hrL

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

theorem localRows_lower {m B : ℕ} (hB : 0 < B) :
    degree m B ≤ 8 * B * localRows m B := by
  have hpos : 0 < 8 * B := by omega
  have hmod := Nat.mod_lt (degree m B) hpos
  have hdiv := Nat.mod_add_div (degree m B) (8 * B)
  unfold localRows
  nlinarith

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sparse rows from the candidates actually selected by the search

The construction below consumes the selected shifts and local matrix explicitly. Its
proofs need their checked Walsh and distance properties, not identity with the old
materialized search's selected candidates. The finite list of final rows is polynomial
size and can be retained; lists of all candidates and all test words cannot.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeProgram

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode
open scoped BigOperators

/-- Positive parameter values ensure that a checked graph and local code exist.
The actual streaming search must use completeness to select such candidates. -/
theorem candidates_exist {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    (∃ shifts : Fin (degree m B) → Cayley.Cube (dimension m B),
      WalshExistence.Good (gapDenom m B) shifts) ∧
    (∃ Q : CheckMatrix (Fin (localRows m B)) (Fin (degree m B)),
      HasDistance Q (degree m B / (100 * B * logSize m) + 1)) := by
  constructor
  · by_cases hr : dimension m B = 0
    · refine ⟨fun _ => 0, ?_⟩
      intro a ha
      apply False.elim (ha ?_)
      funext i
      have hi := i.isLt
      omega
    · obtain ⟨shifts, hs⟩ := WalshExistence.exists_smallWalsh _ _ _
        (gapDenom_pos m hB) (walsh_degree_bound hm hB hr)
      exact ⟨shifts, (WalshExistence.good_iff_smallWalsh (gapDenom_pos m hB) shifts).mpr hs⟩
  · exact LocalCode.exists_local_code_log_bound _ _ _ _ hB (logSize_pos m)
      (degree_le_power m B) (localRows_lower hB)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch

open BitProgram StructuredCalls CodeCandidateProgram


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram CodeChecks


/-- Supplied sparse-code parameters discharge pure local-code existence; the
machine still searches and checks its own actual output matrix. -/
theorem local_parameters_runs {m occurrence : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (A : ℕ) (a : State 16 48)
    (ha : LocalMatrixReady (SparseCode.localRows m occurrence) (SparseCode.degree m occurrence)
      (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) a)
    (hab : ∀ i, (a.stacks i).length ≤ A)
    (hdim : a.stacks 46 = List.replicate
      (SparseCode.localRows m occurrence * SparseCode.degree m occurrence) true)
    (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
    ∃ (n : ℕ) (out : State 16 48) (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
      n ≤ localTime A (SparseCode.localRows m occurrence) (SparseCode.degree m occurrence)
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      Eval localSearch n a out ∧ out.stacks 18 = matrixFrames Q ∧
      SparseCode.HasDistance Q
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      LocalMatrixReady (SparseCode.localRows m occurrence) (SparseCode.degree m occurrence)
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) out ∧
      (∀ i, i ≠ 18 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ boundary A
        (SparseCode.localRows m occurrence * SparseCode.degree m occurrence)) ∧
      ∀ k c, k ≤ n → Trace (compiled localSearch 46 18) k
        (a.withPC (some (compiled localSearch 46 18).entry)) c →
        ∀ i, (c.stacks i).length ≤ localSpace A (SparseCode.localRows m occurrence)
          (SparseCode.degree m occurrence)
          (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) :=
  local_search_runs _ _ _ A (SparseCodeProgram.candidates_exist hm hocc).2
    a ha hab hdim h40 h41 h42

/-- The concrete search's whole matrix readback and uniform storage survive
its actual embedding into the shared leaf ABI. The final callee halt is paid. -/
theorem leaf_call_resources (routine : Cmd 16 48) (output : Fin 48)
    (a : State 40 896) (small : State 16 48) {n A B : ℕ}
    (he : Eval routine n (projectState leafRegisters leafStacks a) small)
    (hframe : ∀ i, i ≠ output → small.stacks i = (projectState leafRegisters leafStacks a).stacks i)
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hspace : ∀ k c, k ≤ n → Trace (compiled routine 46 output) k
      ((projectState leafRegisters leafStacks a).withPC (some (compiled routine 46 output).entry)) c →
      ∀ i, (c.stacks i).length ≤ B) :
    ∃ out, Eval (leafCall routine output) (n + 1) a out ∧
      out.stacks (leafStacks output) = small.stacks output ∧
      (∀ i, i ≠ leafStacks output → out.stacks i = a.stacks i) ∧
      (∀ i, 16 ≤ i.val → out.regs i = a.regs i) ∧
      ∀ k c, k ≤ n + 1 → Trace (compiled (leafCall routine output) (leafStacks 46) (leafStacks output)) k
        (a.withPC (some (compiled (leafCall routine output) (leafStacks 46) (leafStacks output)).entry)) c →
        ∀ i, (c.stacks i).length ≤ max B A := by
  let out := embedState leafRegisters leafStacks a small
  have ht := compiled_halt_trace he 46 output
  have hs := StructuredSpace.compiled_halt_stack_bound he 46 output hspace
  have hc := eval_call_from_state (compiled routine 46 output) leafRegisters leafStacks a
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) ht
  have hinitial : ProgramLinking.embedCfg leafRegisters leafStacks id none
      (a.withPC (none : Option (Fin (size routine + 1))))
      ((projectState leafRegisters leafStacks a).withPC (some (compiled routine 46 output).entry)) =
      a.withPC (some (compiled routine 46 output).entry) := by
    change (embedState leafRegisters leafStacks a (projectState leafRegisters leafStacks a)).withPC _ = _
    rw [embedState_project leafRegisters leafStacks a (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _)]
    rfl
  have hlift := ProgramLinking.liftProgram_trace (compiled routine 46 output) leafRegisters leafStacks
    (a.withPC none) (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) ht
  rw [hinitial] at hlift
  have hlift' : Trace (ProgramLinking.liftProgram (compiled routine 46 output) leafRegisters leafStacks)
      (n + 1) (a.withPC (some (compiled routine 46 output).entry)) (out.withPC none) := by
    simpa [out, embedState, ProgramLinking.embedCfg, ProgramLinking.relocatePc,
      StructuredProgram.State.withPC] using hlift
  have hliftspace := StructuredSpace.liftProgram_stack_bound
    (compiled routine 46 output) leafRegisters leafStacks (a.withPC none)
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _) ht hs ha
  rw [hinitial] at hliftspace
  refine ⟨out, hc, embedState_stack leafRegisters leafStacks a small (Fin.castAdd_injective _ _) output,
    ?_, ?_, ?_⟩
  · intro i hi
    by_cases hport : ∃ j, leafStacks j = i
    · obtain ⟨j, rfl⟩ := hport
      have hj : j ≠ output := by intro h; exact hi (congrArg leafStacks h)
      exact (embedState_stack leafRegisters leafStacks a small (Fin.castAdd_injective _ _) j).trans
        (hframe j hj)
    · exact embedState_stack_frame leafRegisters leafStacks a small i hport
  · intro i hi
    apply embedState_register_frame leafRegisters leafStacks a small i
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega
  · exact StructuredSpace.call_stack_bound
      (ProgramLinking.liftProgram (compiled routine 46 output) leafRegisters leafStacks)
      (compiled (leafCall routine output) (leafStacks 46) (leafStacks output))
      (siteAddress (leafCall routine output)) (exitAddress (leafCall routine output))
      (compiled_site (leafCall routine output) (leafStacks 46) (leafStacks output)) hlift' hliftspace


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed physical stages for the streamed local-code and graph-code searches.
The retained search state is confined to the lower48 leaf stacks; selected
matrices are saved outside that bank before its paid cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode

open BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafOuterProgram SqrtLog.CodeSearchProgram

theorem local_call_oai {m occurrence : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (A : ℕ) (a : Data)
    (hready : CodeChecks.LocalMatrixReady (SparseCode.localRows m occurrence)
      (SparseCode.degree m occurrence)
      (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1)
      (projectState SparseCodeSearch.leafRegisters SparseCodeSearch.leafStacks a))
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hdim : a.stacks 46 = List.replicate
      (SparseCode.localRows m occurrence * SparseCode.degree m occurrence) true)
    (h40 : a.stacks 40 = []) (h41 : a.stacks 41 = []) (h42 : a.stacks 42 = []) :
    ∃ (steps : ℕ) (out : Data)
      (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
      steps ≤ SparseCodeSearch.localTime A (SparseCode.localRows m occurrence)
        (SparseCode.degree m occurrence)
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) + 1 ∧
      Eval localCall steps a out ∧ out.stacks 18 = matrixFrames Q ∧
      SparseCode.HasDistance Q
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      (∀ i, i ≠ 18 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ SparseCodeSearch.boundary A
        (SparseCode.localRows m occurrence * SparseCode.degree m occurrence)) ∧
      ∀ k c, k ≤ steps → Trace (compiled localCall 784 788) k
        (a.withPC (some (compiled localCall 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ max
          (SparseCodeSearch.localSpace A (SparseCode.localRows m occurrence)
            (SparseCode.degree m occurrence)
            (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1)) A := by
  obtain ⟨steps, small, Q, ht, he, hQ, hgood, _, hf, hb, hspace⟩ :=
    SparseCodeSearch.local_parameters_runs hm hocc A
      (projectState SparseCodeSearch.leafRegisters SparseCodeSearch.leafStacks a)
      hready (fun i => ha (SparseCodeSearch.leafStacks i)) hdim h40 h41 h42
  obtain ⟨out, hoe, hout, hframe, _, hprefix⟩ := SparseCodeSearch.leaf_call_resources
    SparseCodeSearch.localSearch 18 a small he hf ha hspace
  refine ⟨steps + 1, out, Q, Nat.add_le_add_right ht 1, hoe, hout.trans hQ, hgood, hframe, ?_, hprefix⟩
  intro i
  by_cases hi : i = 18
  · subst i
    rw [show out.stacks 18 = small.stacks 18 from hout]
    exact hb 18
  · rw [hframe i hi]
    exact (ha i).trans (by unfold SparseCodeSearch.boundary; omega)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.local_call_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.local_call_oai
