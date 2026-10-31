-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:51:15.994746+00:00
-- url     : https://prove2.me/submissions/60d3e148-76c1-4502-b97d-a1bbcf9b9261

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DifferencePairsSpace_program_stack_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation_callback_cursor_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramStateFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable data projection and framing for genuine finite subroutine calls.
The projection/embedding functions specify states; executable code uses only
the fixed instruction-port relocation already proved by ProgramLinking. -/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

/-- Different finite execution derivations of the same structured command
must have the same final data. The existing source port supplies a concrete
compiled machine, and determinism is inherited from its actual transition. -/
theorem Eval.final_unique {r s : ℕ} (port : Fin s) {c : Cmd r s}
    {n m : ℕ} {a b d : State r s} (h : Eval c n a b) (g : Eval c m a d) : b = d := by
  have hb := compiled_halt_trace h port port
  have hd := compiled_halt_trace g port port
  have heq := Computation.RunsIn.terminal_unique
    (show RunsIn (compiled c port port) (n + 1)
      (a.withPC (some (compiled c port port).entry)) (b.withPC none) from
      ⟨n + 1, le_rfl, hb⟩)
    (show RunsIn (compiled c port port) (m + 1)
      (a.withPC (some (compiled c port port).entry)) (d.withPC none) from
      ⟨m + 1, le_rfl, hd⟩)
    (by simp [step, StructuredProgram.State.withPC])
    (by simp [step, StructuredProgram.State.withPC])
  exact congrArg StructuredProgram.State.ofCfg heq

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_BooleanDifferences
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Boolean finite differences (ETH, Lemma `boolean-differences`).
The finite sets in this module specify sums; they are not operational enumerators. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.BooleanDifferences

open scoped BigOperators

theorem pairFamily_eq_biUnion (n J : ℕ) :
    pairFamily n J = (supportFamily n J).biUnion
      (fun E => E.powerset.image (fun U => (E, U))) := by
  ext p
  rcases p with ⟨E, U⟩
  simp [Finset.mem_biUnion, Finset.mem_image]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.BooleanDifferences
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DifferencePairs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Pruned finite-difference traversal. `none`, `some false`, and `some true`
encode membership in neither set, in `E \ U`, and in `U`, respectively.
`words` specifies visit order; the streaming fold does not construct it. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairs

open scoped BigOperators
open BooleanDifferences

theorem words_nodup (n J : ℕ) : (words n J).Nodup := by
  induction n generalizing J with
  | zero => cases J <;> simp [words]
  | succ n ih =>
      cases J with
      | zero => simp
      | succ J =>
          simp only [words, List.nodup_append]
          refine ⟨⟨(ih (J + 1)).map (by intro a b h; exact List.cons.inj h |>.2),
            (ih J).map (by intro a b h; exact List.cons.inj h |>.2), ?_⟩,
            (ih J).map (by intro a b h; exact List.cons.inj h |>.2), ?_⟩
          · intro a ha b hb hab
            obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha
            obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
            simp at hab
          · intro a ha b hb hab
            obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
            rcases List.mem_append.mp ha with ha | ha <;>
              obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha <;>
              simp at hab

theorem pairCount_pos (n J : ℕ) (hJ : 0 < J) : 0 < pairCount n J := by
  have hw : List.replicate n none ∈ words n J := by simp [List.countP_replicate, hJ]
  rw [← words_length]
  exact List.length_pos_iff.mpr (by intro h; simp [h] at hw)

theorem pairCount_eq_sum (n J : ℕ) :
    pairCount n J = ∑ j ∈ Finset.range J, 2 ^ j * n.choose j := by
  have pascal (n J : ℕ) :
      (∑ j ∈ Finset.range (J + 1), 2 ^ j * (n + 1).choose j) =
        (∑ j ∈ Finset.range (J + 1), 2 ^ j * n.choose j) +
          2 * ∑ j ∈ Finset.range J, 2 ^ j * n.choose j := by
    induction J with
    | zero => simp
    | succ J ih =>
        rw [Finset.sum_range_succ _ (J + 1), ih,
          Nat.choose_succ_succ, Finset.sum_range_succ _ (J + 1),
          Finset.sum_range_succ _ J, pow_succ]
        ring
  induction n generalizing J with
  | zero =>
      cases J with
      | zero => simp
      | succ J => simp [pairCount, Finset.sum_range_succ']
  | succ n ih =>
      cases J with
      | zero => simp
      | succ J => rw [pairCount, ih, ih, pascal]

theorem pairFamily_card (n J : ℕ) : (pairFamily n J).card = pairCount n J := by
  rw [pairFamily_eq_biUnion]
  have disjoint : (↑(supportFamily n J) : Set (Finset (Fin n))).PairwiseDisjoint
      (fun E => E.powerset.image (fun U => (E, U))) := by
    intro E _ F _ hEF
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨U, _, hU⟩ := Finset.mem_image.mp hp
    obtain ⟨V, _, hV⟩ := Finset.mem_image.mp hq
    exact hEF (congrArg Prod.fst (hU.trans hV.symm))
  rw [Finset.card_biUnion disjoint]
  simp_rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
    Finset.card_powerset]
  have hdisjoint : (↑(Finset.range J) : Set ℕ).PairwiseDisjoint
      (fun j => (Finset.univ : Finset (Fin n)).powersetCard j) := by
    intro i _ j _ hij
    exact Finset.pairwise_disjoint_powersetCard _ hij
  have hs : supportFamily n J = (Finset.range J).disjiUnion
      (fun j => (Finset.univ : Finset (Fin n)).powersetCard j) hdisjoint := by
    ext E
    rw [mem_supportFamily, Finset.mem_disjiUnion]
    constructor
    · intro hE
      exact ⟨E.card, Finset.mem_range.mpr hE,
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ E, rfl⟩⟩
    · rintro ⟨j, hj, hE⟩
      exact (Finset.mem_powersetCard.mp hE).2 ▸ Finset.mem_range.mp hj
  rw [hs, Finset.sum_disjiUnion, pairCount_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := Finset.sum_powersetCard j (Finset.univ : Finset (Fin n)) (fun a => 2 ^ a)
  rw [nsmul_eq_mul] at h
  simpa [Nat.mul_comm] using h

theorem countP_ofFn {α : Type*} (p : α → Bool) (n : ℕ) (f : Fin n → α) :
    (List.ofFn f).countP p = ∑ i, if p (f i) then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.ofFn_succ, List.countP_cons, Fin.sum_univ_succ, ih]
      omega

@[simp] theorem encodePair_weight {n : ℕ} (E U : Finset (Fin n)) :
    (encodePair E U).countP Option.isSome = E.card := by
  rw [encodePair, countP_ofFn]
  have h (i : Fin n) :
      (if (if i ∈ E then some (decide (i ∈ U)) else none).isSome then 1 else 0) =
        (if i ∈ E then 1 else 0 : ℕ) := by
    by_cases hi : i ∈ E <;> simp [hi]
  simp_rw [h]
  simp

@[simp] theorem encodePair_outer_count {n : ℕ} (E U : Finset (Fin n)) :
    ((encodePair E U).map Option.isSome).reverse.count true = E.card := by
  simp [List.count_eq_countP, List.countP_map, Function.comp_def]

theorem encodePair_injective {n : ℕ} {E U F V : Finset (Fin n)}
    (hU : U ⊆ E) (hV : V ⊆ F) (h : encodePair E U = encodePair F V) :
    E = F ∧ U = V := by
  have hf := List.ofFn_injective h
  have hE : E = F := by
    ext i
    have hi := congrArg Option.isSome (congrFun hf i)
    by_cases he : i ∈ E <;> by_cases hf : i ∈ F <;> simp_all
  subst F
  refine ⟨rfl, ?_⟩
  ext i
  have hi := congrFun hf i
  by_cases he : i ∈ E
  · simpa [he] using hi
  · have hu : i ∉ U := fun h => he (hU h)
    have hv : i ∉ V := fun h => he (hV h)
    simp [hu, hv]

theorem encoded_pairs_eq_words (n J : ℕ) :
    (pairFamily n J).image (fun p => encodePair p.1 p.2) = (words n J).toFinset := by
  have hsub : (pairFamily n J).image (fun p => encodePair p.1 p.2) ⊆
      (words n J).toFinset := by
    intro w hw
    obtain ⟨⟨E, U⟩, hEU, rfl⟩ := Finset.mem_image.mp hw
    simp only [List.mem_toFinset, mem_words]
    exact ⟨by simp [encodePair], by rw [encodePair_weight]; exact (mem_pairFamily.mp hEU).1⟩
  have hinj : Set.InjOn (fun p : Finset (Fin n) × Finset (Fin n) => encodePair p.1 p.2)
      (pairFamily n J : Set _) := by
    intro p hp q hq heq
    rcases p with ⟨E, U⟩
    rcases q with ⟨F, V⟩
    obtain ⟨rfl, rfl⟩ := encodePair_injective (mem_pairFamily.mp hp).2
      (mem_pairFamily.mp hq).2 heq
    rfl
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_image_iff.mpr hinj, List.toFinset_card_of_nodup (words_nodup n J),
    words_length, pairFamily_card]

theorem calls_le (n J : ℕ) (hJ : 0 < J) :
    calls n J ≤ (3 * n + 1) * pairCount n J := by
  induction n generalizing J with
  | zero => cases J <;> simp_all [calls, pairCount]
  | succ n ih =>
      cases J with
      | zero => omega
      | succ J =>
          have hl := ih (J + 1) (Nat.succ_pos J)
          have hp := pairCount_pos n (J + 1) (Nat.succ_pos J)
          cases J with
          | zero => simp only [calls, pairCount, calls_zero, pairCount_zero]; nlinarith
          | succ J =>
              have hr := ih (J + 1) (Nat.succ_pos J)
              simp only [calls, pairCount]
              nlinarith

theorem fold_eq_foldl {α : Type*} (visit : List (Option Bool) → α → α)
    (n J : ℕ) (pre : List (Option Bool)) (acc : α) :
    fold visit n J pre acc =
      (words n J).foldl (fun a w => visit (pre ++ w) a) acc := by
  induction n generalizing J pre acc with
  | zero => cases J <;> simp [fold, words]
  | succ n ih =>
      cases J with
      | zero => simp [fold]
      | succ J => simp [fold, words, ih, List.foldl_append, List.foldl_map]

/-- The reference visit order contains each admissible pair exactly once. -/
theorem sum_words_eq_sum_pairs {A : Type*} [AddCommMonoid A]
    (n J : ℕ) (f : List (Option Bool) → A) :
    ((words n J).map f).sum = ∑ p ∈ pairFamily n J, f (encodePair p.1 p.2) := by
  classical
  rw [← List.sum_toFinset f (words_nodup n J), ← encoded_pairs_eq_words]
  apply Finset.sum_image
  intro p hp q hq heq
  obtain ⟨he, hu⟩ := encodePair_injective (mem_pairFamily.mp hp).2
    (mem_pairFamily.mp hq).2 heq
  exact Prod.ext he hu

/-- A decoded accumulator may have a validity condition; it is retained at
all callback boundaries, while the decoded result is the exact pair sum. -/
theorem fold_decode_sum {A B : Type*} [AddCommMonoid B]
    (visit : List (Option Bool) → A → A) (decode : A → B) (P : A → Prop)
    (f : List (Option Bool) → B) (n J : ℕ) (acc : A) (ha : P acc)
    (step : ∀ w ∈ words n J, ∀ a, P a →
      P (visit w a) ∧ decode (visit w a) = decode a + f w) :
    P (fold visit n J [] acc) ∧
      decode (fold visit n J [] acc) =
        decode acc + ∑ p ∈ pairFamily n J, f (encodePair p.1 p.2) := by
  have hlist : ∀ (ws : List (List (Option Bool))) (a : A), P a →
      (∀ w ∈ ws, ∀ b, P b → P (visit w b) ∧ decode (visit w b) = decode b + f w) →
      P (ws.foldl (fun b w => visit w b) a) ∧
        decode (ws.foldl (fun b w => visit w b) a) = decode a + (ws.map f).sum := by
    intro ws
    induction ws with
    | nil => intro a ha _; exact ⟨ha, by simp⟩
    | cons w ws ih =>
        intro a ha hs
        obtain ⟨ha', he⟩ := hs w (by simp) a ha
        obtain ⟨hf, hv⟩ := ih (visit w a) ha' (fun v hv => hs v (by simp [hv]))
        refine ⟨hf, ?_⟩
        simpa [he, add_assoc] using hv
  simpa [fold_eq_foldl, sum_words_eq_sum_pairs] using hlist (words n J) acc ha step

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairs
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DifferencePairsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite control for the pruned pair DFS. Four protected stacks hold
remaining depth, remaining strict budget, and the two current masks. The masks
also encode the DFS phases `00`, `10`, `11`; no completed-pair list is retained.
The callback receives the masks in reverse coordinate order. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram

open OAI.Algorithms.SubexponentialSAT.StructuredProgram (Atom)
open OAI.Algorithms.SubexponentialSAT.StructuredCalls

variable {r s : ℕ}

theorem atoms_eval (code : List (Atom r s)) (a : State r s) :
    Eval (atoms code) code.length a (code.foldl (fun d op => op.eval d) a) := by
  apply Eval.base
  induction code generalizing a with
  | nil => exact StructuredProgram.Eval.skip a
  | cons op code ih =>
      simpa only [List.foldr_cons, List.foldl_cons, List.length_cons, Nat.add_comm]
        using (StructuredProgram.Eval.atom op a).seq (ih (op.eval a))

theorem pushBit_eval (p : Ports r s) (i : Fin 4) (b : Bool) (d : State r s) :
    Eval (pushBit p i b) 2 d (pushed p i b d) := by
  simpa [pushBit, pushed, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, BitProgram.execInstr] using
    atoms_eval [.set (p.register 2) b, .push (p.stack i) (p.register 2)] d

theorem enter_eval (p : Ports r s) (e u : Bool) (d : State r s) :
    Eval (enter p e u) 5 d (entered p e u d) :=
  (pushBit_eval p 2 e d).seq
    ((pushBit_eval p 3 u _).seq (atoms_eval [.set (p.register 0) true] _))

theorem body_descend (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = true) (b : Bool) (rest : List Bool)
    (hn : d.stacks (p.stack 0) = b :: rest) :
    Eval (body p callback) 8 d (descended p d) := by
  have hp : (popped p 0 2 d).regs (p.register 3) = true := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hn]
  exact .ite_true hd ((atoms_eval [.pop (p.stack 0) (p.register 2) (p.register 3)] d).seq
    (.ite_true hp (enter_eval p false false (popped p 0 2 d))))

theorem body_callback (p : Ports r s) (callback : Cmd r s) (d e : State r s)
    (hd : d.regs (p.register 0) = true) (hn : d.stacks (p.stack 0) = [])
    (t : ℕ) (hc : Eval callback t (popped p 0 2 d) e) :
    Eval (body p callback) (t + 5) d (returned p e) := by
  have h := Eval.ite_true (yes := descend p callback) (no := backtrack p) hd
    (Eval.seq (atoms_eval [.pop (p.stack 0) (p.register 2) (p.register 3)] d)
      (Eval.ite_false (yes := enter p false false) (test := p.register 3)
        (by simp [Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
          BitProgram.execInstr, BitProgram.readRegs, hn])
        (hc.seq (atoms_eval [.set (p.register 0) false, .set (p.register 1) true] e))))
  convert h using 1
  · rfl
  · simp only [List.length_cons, List.length_nil]
    omega
  · rfl

theorem body_finish (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = false) (es us : List Bool)
    (he : d.stacks (p.stack 2) = true :: es)
    (hu : d.stacks (p.stack 3) = true :: us) :
    Eval (body p callback) 10 d (finished p d) := by
  have hp : (popped p 2 4 d).regs (p.register 3) = true := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have he' : (backed p d).regs (p.register 4) = true := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have hu' : (backed p d).regs (p.register 2) = true := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hu]
  exact .ite_false hd
    ((atoms_eval [.pop (p.stack 2) (p.register 4) (p.register 3)] d).seq
      (.ite_true hp
        ((atoms_eval [.pop (p.stack 3) (p.register 2) (p.register 3)] _).seq
          (.ite_true he' (.ite_true hu'
            ((pushBit_eval p 1 true _).seq (pushBit_eval p 0 true _)))))))

theorem body_next_inner (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = false) (es us : List Bool)
    (he : d.stacks (p.stack 2) = true :: es)
    (hu : d.stacks (p.stack 3) = false :: us) :
    Eval (body p callback) 11 d (entered p true true (backed p d)) := by
  have hp : (popped p 2 4 d).regs (p.register 3) = true := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have he' : (backed p d).regs (p.register 4) = true := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have hu' : (backed p d).regs (p.register 2) = false := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hu]
  exact .ite_false hd
    ((atoms_eval [.pop (p.stack 2) (p.register 4) (p.register 3)] d).seq
      (.ite_true hp
        ((atoms_eval [.pop (p.stack 3) (p.register 2) (p.register 3)] _).seq
          (.ite_true he' (.ite_false hu' (enter_eval p true true _))))))

theorem body_next_outer (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = false) (es bs : List Bool) (b c : Bool)
    (he : d.stacks (p.stack 2) = false :: es)
    (hb : d.stacks (p.stack 1) = b :: c :: bs) :
    Eval (body p callback) 13 d (entered p true false (testedOutside p d)) := by
  have hp : (popped p 2 4 d).regs (p.register 3) = true := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have he' : (backed p d).regs (p.register 4) = false := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have hb' : (testedOutside p d).regs (p.register 3) = true := by
    simp [testedOutside, backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hb]
  exact .ite_false hd
    ((atoms_eval [.pop (p.stack 2) (p.register 4) (p.register 3)] d).seq
      (.ite_true hp
        ((atoms_eval [.pop (p.stack 3) (p.register 2) (p.register 3)] _).seq
          (.ite_false he'
            ((atoms_eval [.pop (p.stack 1) (p.register 2) (p.register 3),
              .peek (p.stack 1) (p.register 2) (p.register 3)] _).seq
              (.ite_true hb' (enter_eval p true false _)))))))

theorem body_prune (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = false) (es : List Bool) (b : Bool)
    (he : d.stacks (p.stack 2) = false :: es) (hb : d.stacks (p.stack 1) = [b]) :
    Eval (body p callback) 12 d (pruned p d) := by
  have hp : (popped p 2 4 d).regs (p.register 3) = true := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have he' : (backed p d).regs (p.register 4) = false := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have hb' : (testedOutside p d).regs (p.register 3) = false := by
    simp [testedOutside, backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hb]
  exact .ite_false hd
    ((atoms_eval [.pop (p.stack 2) (p.register 4) (p.register 3)] d).seq
      (.ite_true hp
        ((atoms_eval [.pop (p.stack 3) (p.register 2) (p.register 3)] _).seq
          (.ite_false he'
            ((atoms_eval [.pop (p.stack 1) (p.register 2) (p.register 3),
              .peek (p.stack 1) (p.register 2) (p.register 3)] _).seq
              (.ite_false hb' ((pushBit_eval p 1 true _).seq (pushBit_eval p 0 true _))))))))

theorem body_stop (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = false) (he : d.stacks (p.stack 2) = []) :
    Eval (body p callback) 4 d (stopped p d) := by
  have hp : (popped p 2 4 d).regs (p.register 3) = false := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  exact .ite_false hd
    ((atoms_eval [.pop (p.stack 2) (p.register 4) (p.register 3)] d).seq
      (.ite_false hp (atoms_eval [.set (p.register 1) false] _)))

theorem cursor_descend (p : Ports r s) (n J : ℕ) (pre : List (Option Bool))
    (d : State r s) (h : Cursor p (n + 1) J pre true d) :
    Cursor p n J (pre ++ [none]) true (descended p d) := by
  rcases h with ⟨h0, h1, h2, h3, hm, ha⟩
  constructor <;>
    simp [descended, entered, popped, pushed, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, BitProgram.execInstr,
      BitProgram.readRegs, h0, h1, h2, h3, ha, List.replicate_succ]

theorem cursor_next_inner (p : Ports r s) (n J : ℕ) (pre : List (Option Bool))
    (d : State r s) (h : Cursor p n J (pre ++ [some false]) false d) :
    Cursor p n J (pre ++ [some true]) true (entered p true true (backed p d)) := by
  rcases h with ⟨h0, h1, h2, h3, hm, ha⟩
  constructor <;>
    simp [entered, backed, popped, pushed, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, BitProgram.execInstr,
      BitProgram.readRegs, h0, h1, h2, h3, ha]

theorem cursor_next_outer (p : Ports r s) (n J : ℕ) (pre : List (Option Bool))
    (d : State r s) (h : Cursor p n (J + 2) (pre ++ [none]) false d) :
    Cursor p n (J + 1) (pre ++ [some false]) true
      (entered p true false (testedOutside p d)) := by
  rcases h with ⟨h0, h1, h2, h3, hm, ha⟩
  constructor <;>
    simp [entered, testedOutside, backed, popped, pushed, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, BitProgram.execInstr,
      BitProgram.readRegs, h0, h1, h2, h3, ha, List.replicate_succ]

theorem cursor_finished (p : Ports r s) (n J : ℕ) (pre : List (Option Bool))
    (d : State r s) (h : Cursor p n J (pre ++ [some true]) false d) :
    Cursor p (n + 1) (J + 1) pre false (finished p d) := by
  rcases h with ⟨h0, h1, h2, h3, hm, ha⟩
  constructor <;>
    simp [finished, backed, popped, pushed, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, BitProgram.execInstr,
      BitProgram.readRegs, h0, h1, h2, h3, hm, ha, List.replicate_succ]

theorem cursor_pruned (p : Ports r s) (n : ℕ) (pre : List (Option Bool))
    (d : State r s) (h : Cursor p n 1 (pre ++ [none]) false d) :
    Cursor p (n + 1) 1 pre false (pruned p d) := by
  rcases h with ⟨h0, h1, h2, h3, hm, ha⟩
  constructor <;>
    simp [pruned, testedOutside, backed, popped, pushed, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, BitProgram.execInstr,
      BitProgram.readRegs, h0, h1, h2, h3, hm, ha, List.replicate_succ]

theorem BodyTrace.trans {p : Ports r s} {callback : Cmd r s}
    {n m : ℕ} {a b c : State r s}
    (h : BodyTrace p callback n a b) (g : BodyTrace p callback m b c) :
    BodyTrace p callback (n + m) a c := by
  induction h with
  | refl => simpa using g
  | cons ha hab _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        BodyTrace.cons ha hab (ih g)

theorem BodyTrace.while_eval {p : Ports r s} {callback : Cmd r s}
    {n : ℕ} {a b : State r s} (h : BodyTrace p callback n a b)
    (hb : b.regs (p.register 1) = false) :
    Eval (.while (p.register 1) (body p callback)) (n + 1) a b := by
  induction h with
  | refl => exact Eval.while_false hb
  | cons ha hab _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Eval.while_true ha hab (ih hb)

theorem BodyTrace.single {p : Ports r s} {callback : Cmd r s}
    {n : ℕ} {a b : State r s} (ha : a.regs (p.register 1) = true)
    (he : Eval (body p callback) n a b) : BodyTrace p callback (n + 1) a b := by
  simpa using BodyTrace.cons ha he (BodyTrace.refl b)

theorem command_eval_zero (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hbudget : d.stacks (p.stack 1) = []) :
    Eval (command p callback) 4 d (initialized p d) := by
  have hfalse : (initialized p d).regs (p.register 1) = false := by
    simp [initialized, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hbudget]
  exact (atoms_eval [.peek (p.stack 1) (p.register 2) (p.register 3),
    .copy (p.register 1) (p.register 3), .set (p.register 0) true] d).seq
      (Eval.while_false hfalse)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DifferencePairsRelational
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Relational accumulator correctness for the existing four-stack pair DFS.
Only the proof invariant is generalized: the actual commands, branch order,
callback states and all-prefix space theorem are unchanged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsRelational

open BitProgram StructuredCalls DifferencePairsProgram
open StructuredProgram (Atom)

variable {r s : ℕ} {α : Type*}

/-- Erasing the semantic value supplies exactly the existing resource
contract. Its auxiliary byte observation is the preserved depth controller;
the resource theorem does not require an off-controller output port. -/
theorem CallbackSpec.erased (p : Ports r s) (callback : Cmd r s)
    (visit : List (Option Bool) → α → α) (C N : ℕ) (I : α → State r s → Prop)
    (spec : CallbackSpec p callback visit C N I) :
    DifferencePairsProgram.CallbackSpec p callback (p.stack 0) (fun _ word => word)
      C N (fun d => ∃ value, I value d) := by
  constructor
  · intro d e hf hd
    obtain ⟨value,hvalue⟩ := hd
    exact ⟨value,spec.stable value d e hf hvalue⟩
  · intro J pre d hn hc hd
    obtain ⟨value,hvalue⟩ := hd
    obtain ⟨t,e,ht,he,hf,hI⟩ := spec.run J pre value d hn hc hvalue
    exact ⟨t,e,ht,he,hf,hf 0,visit pre value,hI⟩

/-- The same actual subtree traversal realizes the semantic fold, while its
dictionary witnesses may vary at every callback. -/
theorem subtree (p : Ports r s) (callback : Cmd r s)
    (visit : List (Option Bool) → α → α) (C N : ℕ)
    (I : α → State r s → Prop) (spec : CallbackSpec p callback visit C N I)
    (n J : ℕ) (pre : List (Option Bool)) (value : α) (d : State r s)
    (hsize : n + pre.length = N) (h : Cursor p n (J+1) pre true d) (hi : I value d) :
    ∃ t e, BodyTrace p callback t d e ∧ Cursor p n (J+1) pre false e ∧
      t ≤ (C+46)*DifferencePairs.calls n (J+1) ∧
      I (DifferencePairs.fold visit n (J+1) pre value) e := by
  induction n generalizing J pre value d with
  | zero =>
      obtain ⟨t,e,ht,he,hf,hIe⟩ := spec.run J pre value d (by simpa using hsize) h hi
      have hr : Cursor p 0 (J+1) pre false (returned p e) :=
        ⟨(hf 0).trans h.depth,(hf 1).trans h.budget,(hf 2).trans h.outer,
          (hf 3).trans h.inner,returned_descending p e,returned_active p e⟩
      refine ⟨t+6,returned p e,?_,hr,?_,?_⟩
      · simpa [Nat.add_assoc] using BodyTrace.single h.active
          (body_callback p callback d e h.descending (by simpa using h.depth) t he)
      · simp only [DifferencePairs.calls]
        omega
      · exact spec.stable _ e _ (fun _ _ => rfl) hIe
  | succ n ih =>
      have hs : n+(pre++[none]).length=N := by
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hsize
      have hd := cursor_descend p n (J+1) pre d h
      have hid : I value (descended p d) := spec.stable value d _ (by
        intro o ho
        simp [descended,ho]) hi
      obtain ⟨t₀,e₀,he₀,hc₀,ht₀,hi₀⟩ := ih J (pre++[none]) value (descended p d) hs hd hid
      have hdtrace := BodyTrace.single h.active (body_descend p callback d h.descending true
        (List.replicate n true) (by simpa [List.replicate_succ] using h.depth))
      cases J with
      | zero =>
          have hb := body_prune p callback e₀ hc₀.descending
            (pre.map Option.isSome).reverse true
            (by simpa using hc₀.outer) (by simpa using hc₀.budget)
          have hr := cursor_pruned p n pre e₀ hc₀
          refine ⟨9+t₀+13,pruned p e₀,
            (hdtrace.trans he₀).trans (BodyTrace.single hc₀.active hb),hr,?_,?_⟩
          · simp only [DifferencePairs.calls,DifferencePairs.calls_zero]
            nlinarith
          · have hsemantic := spec.stable _ e₀ (pruned p e₀)
              (by intro o ho; simp [pruned,backed,ho]) hi₀
            simpa only [DifferencePairs.fold] using hsemantic
      | succ J =>
          have hb₁ := body_next_outer p callback e₀ hc₀.descending
            (pre.map Option.isSome).reverse (List.replicate J true) true true
            (by simpa using hc₀.outer) (by simpa [List.replicate_succ] using hc₀.budget)
          have hc₁ := cursor_next_outer p n J pre e₀ hc₀
          have hi₁ : I (DifferencePairs.fold visit n (J+2) (pre++[none]) value)
              (entered p true false (testedOutside p e₀)) :=
            spec.stable _ e₀ _ (by intro o ho; simp [testedOutside_stacks,backed,ho]) hi₀
          obtain ⟨t₁,e₁,he₁,hc₁',ht₁,hi₁'⟩ := ih J (pre++[some false]) _
            (entered p true false (testedOutside p e₀))
            (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hsize) hc₁ hi₁
          have hb₂ := body_next_inner p callback e₁ hc₁'.descending
            (pre.map Option.isSome).reverse (pre.map (fun a => a.getD false)).reverse
            (by simpa using hc₁'.outer) (by simpa using hc₁'.inner)
          have hc₂ := cursor_next_inner p n (J+1) pre e₁ hc₁'
          have hi₂ := spec.stable _ e₁ (entered p true true (backed p e₁))
            (by intro o ho; simp [backed,ho]) hi₁'
          obtain ⟨t₂,e₂,he₂,hc₂',ht₂,hi₂'⟩ := ih J (pre++[some true]) _
            (entered p true true (backed p e₁))
            (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hsize) hc₂ hi₂
          have hb₃ := body_finish p callback e₂ hc₂'.descending
            (pre.map Option.isSome).reverse (pre.map (fun a => a.getD false)).reverse
            (by simpa using hc₂'.outer) (by simpa using hc₂'.inner)
          have hr := cursor_finished p n (J+1) pre e₂ hc₂'
          refine ⟨9+t₀+14+t₁+12+t₂+11,finished p e₂,
            (((((hdtrace.trans he₀).trans (BodyTrace.single hc₀.active hb₁)).trans he₁).trans
              (BodyTrace.single hc₁'.active hb₂)).trans he₂).trans
              (BodyTrace.single hc₂'.active hb₃),hr,?_,?_⟩
          · simp only [DifferencePairs.calls]
            nlinarith
          · exact spec.stable _ e₂ _ (by intro o ho; simp [finished,backed,ho]) hi₂'

/-- Actual command execution and semantic accumulator correctness, before
the single compiler halt step. -/
theorem command_eval (p : Ports r s) (callback : Cmd r s)
    (visit : List (Option Bool) → α → α) (C n J : ℕ)
    (I : α → State r s → Prop) (spec : CallbackSpec p callback visit C n I)
    (value : α) (d : State r s)
    (hdepth : d.stacks (p.stack 0)=List.replicate n true)
    (hbudget : d.stacks (p.stack 1)=List.replicate (J+1) true)
    (he : d.stacks (p.stack 2)=[]) (hu : d.stacks (p.stack 3)=[]) (hi : I value d) :
    ∃ t e, t ≤ (C+46)*DifferencePairs.calls n (J+1)+9 ∧
      Eval (command p callback) t d e ∧
      (∀ i,e.stacks (p.stack i)=d.stacks (p.stack i)) ∧
      I (DifferencePairs.fold visit n (J+1) [] value) e := by
  have hcursor : Cursor p n (J+1) [] true (initialized p d) := by
    constructor
    · exact hdepth
    · exact hbudget
    · exact he
    · exact hu
    · simp [initialized, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
        BitProgram.execInstr]
    · simp [initialized, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
        BitProgram.execInstr, BitProgram.readRegs, hbudget, List.replicate_succ]
  have hii : I value (initialized p d) := spec.stable value d _ (fun _ _ => rfl) hi
  obtain ⟨t,e,ht,hc,hb,hIe⟩ := subtree p callback visit C n I spec n J [] value
    (initialized p d) (by simp) hcursor hii
  have hend := body_stop p callback e hc.descending (by simpa using hc.outer)
  have hstop : (stopped p e).regs (p.register 1)=false := by
    simp [stopped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr]
  have hw := (ht.trans (BodyTrace.single hc.active hend)).while_eval hstop
  have hinit := atoms_eval [.peek (p.stack 1) (p.register 2) (p.register 3),
    .copy (p.register 1) (p.register 3),.set (p.register 0) true] d
  have hall : Eval (command p callback) (t+9) d (stopped p e) := by
    simpa [command,initialized,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using hinit.seq hw
  refine ⟨t+9,stopped p e,by omega,hall,?_,?_⟩
  · intro i
    fin_cases i <;>
      simp [stopped, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
        BitProgram.execInstr, hc.depth, hc.budget, hc.outer, hc.inner, hdepth, hbudget,
        he, hu]
  · exact spec.stable _ e _ (by
      intro o ho
      simp [stopped, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
        BitProgram.execInstr, ho]) hIe

/-- Relational correctness, exact native time and all-prefix space refer to
one execution of the unchanged pair iterator, including J=0 and J>N. -/
theorem program_resources (p : Ports r s) (callback : Cmd r s)
    (visit : List (Option Bool) → α → α) (I : α → State r s → Prop)
    (C N J B D : ℕ) (spec : CallbackSpec p callback visit C N I)
    (hcallback : ∀ value j pre a b t, pre.length=N →
      (j+1)+pre.countP Option.isSome=J → Cursor p 0 (j+1) pre true a → I value a →
      (∀ i, (a.stacks i).length ≤ B) → Eval callback t (popped p 0 2 a) b →
      (∀ i, (b.stacks i).length ≤ B) ∧
      ∀ elapsed z, elapsed ≤ t → Trace (compiled callback (p.stack 0) (p.stack 2)) elapsed
        ((popped p 0 2 a).withPC (some (compiled callback (p.stack 0) (p.stack 2)).entry)) z →
        ∀ i, (z.stacks i).length ≤ D)
    (value : α) (a : State r s) (ha : ∀ i, (a.stacks i).length ≤ B) (hi : I value a)
    (hdepth : a.stacks (p.stack 0)=List.replicate N true)
    (hbudget : a.stacks (p.stack 1)=List.replicate J true)
    (houter : a.stacks (p.stack 2)=[]) (hinner : a.stacks (p.stack 3)=[]) :
    ∃ t e, Eval (command p callback) t a e ∧ t + 1 ≤ cost C N J ∧
      Trace (program p callback) (t+1)
        (a.withPC (some (program p callback).entry)) (e.withPC none) ∧
      (∀ i,e.stacks (p.stack i)=a.stacks (p.stack i)) ∧
      I (DifferencePairs.fold visit N J [] value) e ∧
      ∀ elapsed z, elapsed ≤ t + 1 → Trace (program p callback) elapsed
        (a.withPC (some (program p callback).entry)) z →
        ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
  have hex : ∃ t e, Eval (command p callback) t a e ∧ t + 1 ≤ cost C N J ∧
      (∀ i,e.stacks (p.stack i)=a.stacks (p.stack i)) ∧
      I (DifferencePairs.fold visit N J [] value) e := by
    cases J with
    | zero =>
        exact ⟨4,initialized p a,command_eval_zero p callback a (by simpa using hbudget),
          by simp [cost],fun _ => rfl,by
            simpa only [DifferencePairs.fold] using
              spec.stable value a (initialized p a) (fun _ _ => rfl) hi⟩
    | succ J =>
        obtain ⟨t,e,ht,he,hf,hIe⟩ := command_eval p callback visit C N J I spec value a
          hdepth hbudget houter hinner hi
        refine ⟨t,e,he,?_,hf,hIe⟩
        have hc := DifferencePairs.calls_le N (J+1) (Nat.succ_pos J)
        unfold cost
        nlinarith
  obtain ⟨t,e,he,ht,hf,hIe⟩ := hex
  refine ⟨t,e,he,ht,compiled_halt_trace he (p.stack 0) (p.stack 2),hf,hIe,?_⟩
  apply DifferencePairsSpace.program_stack_bound p callback (p.stack 0) (fun _ word => word)
    (fun d => ∃ value,I value d) C N J B D (spec.erased p callback visit C N I)
    ?_ he ha ⟨value,hi⟩ hdepth hbudget houter hinner
  intro j pre d b steps hn hj hc hd hb heval
  obtain ⟨v,hv⟩ := hd
  exact hcallback v j pre d b steps hn hj hc hv hb heval

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsRelational
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryPairCommit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The signed finite-difference term is committed to the actual node word.
The pair product and the node sum use the same stored dictionaries as their
validity and readout witnesses. Marker readout remains additive. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram
open TruncatedRingProgram QueryProgram QueryTupleState

namespace NodeAccumulatorMeaning

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {value : Truncated (q.p.model.O q.p.t) q.J} {a b : Data}
    (h : NodeAccumulatorMeaning q value a) (hf : b.stacks 850=a.stacks 850) :
    NodeAccumulatorMeaning q value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

end NodeAccumulatorMeaning

open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryReadyConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query-entry facts from the actual arithmetic and native cache
producers. Pair masks are installed by the paid pair-start command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram LeafProgram LeafProgram.PreparedSource
open LeafHeadSetupProgram QueryTupleState
open ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem CommonReady.frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {P : ℕ} {a b : State 40 896}
    (h : CommonReady q node H high P a) (hf : ∀ i∈commonPorts, b.stacks i=a.stacks i) :
    CommonReady q node H high P b := by
  refine {
    lifting := h.lifting
    generatedTheta := h.generatedTheta
    sourceMinus := h.sourceMinus
    ambient := (hf 128 (by decide)).trans h.ambient
    theta := (hf 78 (by decide)).trans h.theta
    modulus := (hf 194 (by decide)).trans h.modulus
    table := (hf 201 (by decide)).trans h.table
    width := (hf 202 (by decide)).trans h.width
    scalarZero := (hf 203 (by decide)).trans h.scalarZero
    degree := (hf 204 (by decide)).trans h.degree
    one := (hf 207 (by decide)).trans h.one
    minus := (hf 211 (by decide)).trans h.minus
    precision := (hf 212 (by decide)).trans h.precision
    order := (hf 243 (by decide)).trans h.order
    zero := (hf 280 (by decide)).trans h.zero
    code := (hf 281 (by decide)).trans h.code
    clauses := (hf 700 (by decide)).trans h.clauses
    rows := (hf 701 (by decide)).trans h.rows
    rowCount := (hf 704 (by decide)).trans h.rowCount
    markedIndex := (hf 705 (by decide)).trans h.markedIndex
    markedFlag := (hf 706 (by decide)).trans h.markedFlag
    indexModulus := (congrArg BinaryArithmetic.toNat (hf 707 (by decide))).trans h.indexModulus
    indexWidth := (congrArg List.length (hf 708 (by decide))).trans h.indexWidth
    highMask := (hf 702 (by decide)).trans h.highMask
    highBits := (hf 703 (by decide)).trans h.highBits
    colors := (hf 130 (by decide)).trans h.colors
    nodes := (hf 131 (by decide)).trans h.nodes
    typeWidth := (hf 132 (by decide)).trans h.typeWidth
    positive := (hf 710 (by decide)).trans h.positive
    negative := (hf 711 (by decide)).trans h.negative
    sourceWidth := (hf 140 (by decide)).trans h.sourceWidth
    power := (hf 712 (by decide)).trans h.power
    powerNegative := h.powerNegative
    radius := (hf 138 (by decide)).trans h.radius
    offset := (hf 139 (by decide)).trans h.offset
    metadata := (hf 135 (by decide)).trans h.metadata
    plans := (hf 136 (by decide)).trans h.plans
    inverses := (hf 713 (by decide)).trans h.inverses
    negatives := (hf 714 (by decide)).trans h.negatives
    differences := (hf 715 (by decide)).trans h.differences
    ringWidth := (hf 717 (by decide)).trans h.ringWidth
    rowWidth := (hf 716 (by decide)).trans h.rowWidth
    inverseDenominator := (hf 728 (by decide)).trans h.inverseDenominator
    cacheCaps := ?_
    ambientCap := ?_
    oneCap := ?_ }
  · intro p hp
    have hm : p.1.castAdd 128∈commonPorts := by
      simp only [LeafNodeCacheProgram.directCopies, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [hf _ hm]
    exact h.cacheCaps p hp
  · rw [hf 128 (by decide)]
    exact h.ambientCap
  · rw [hf 207 (by decide)]
    exact h.oneCap

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual finite-difference callback uses the physical pair masks and
one semantic node accumulator. The reference support decoding below is used
only in the proof; the executed controller retains its four finite words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram QueryTupleState QueryPairCommit QueryReadyConstruction
open SignatureTupleSource
open scoped BigOperators
open SqrtLog.ProgramTapeReplay

theorem inner_subset (N : ℕ) (word : List (Option Bool)) :
    inner N word ⊆ outer N word := by
  intro i hi
  simp only [inner,Finset.mem_filter,Finset.mem_univ,true_and] at hi
  simp only [outer,Finset.mem_filter,Finset.mem_univ,true_and]
  change (word.getD i.val none).getD false=true at hi
  cases h : word.getD i.val none with
  | none => rw [h] at hi; cases hi
  | some b => simp

theorem encode_decoded (N : ℕ) (word : List (Option Bool)) (hlen : word.length=N) :
    DifferencePairs.encodePair (outer N word) (inner N word)=word := by
  subst N
  calc
    _=List.ofFn word.get := by
      unfold DifferencePairs.encodePair
      apply congrArg List.ofFn
      funext i
      have hd : word.getD i.val none=word.get i := List.getD_eq_getElem _ _ i.isLt
      simp only [outer,inner,Finset.mem_filter,Finset.mem_univ,true_and,hd]
      cases h : word.get i with
      | none => simp
      | some b => cases b <;> simp
    _=word := List.ofFn_get word

theorem decoded_encode {N : ℕ} (E U : Finset (Fin N)) (hU : U⊆E) :
    outer N (DifferencePairs.encodePair E U)=E ∧
      inner N (DifferencePairs.encodePair E U)=U := by
  apply DifferencePairs.encodePair_injective (inner_subset N _) hU
  exact encode_decoded N _ (by simp [DifferencePairs.encodePair])

/-- The verified native order visits each support pair once, uniformly for
J=0 and J>N. No byte-level representative of a ring element is selected. -/
theorem fold_signed_sum {R : Type*} [CommRing R] (N J : ℕ)
    (value : Finset (Fin N) → Finset (Fin N) → R) (total : R) :
    DifferencePairs.fold (visit N value) N J [] total = total+
      ∑ pair ∈ BooleanDifferences.pairFamily N J,
        (-1)^(pair.1.card-pair.2.card)*value pair.1 pair.2 := by
  have h := (DifferencePairs.fold_decode_sum (visit N value) id (fun _ => True)
    (fun word => (-1)^((outer N word).card-(inner N word).card)*
      value (outer N word) (inner N word)) N J total True.intro
    (fun _ _ _ _ => ⟨True.intro,rfl⟩)).2
  dsimp only [id] at h
  rw [h]
  apply congrArg (fun x => total+x)
  apply Finset.sum_congr rfl
  intro pair hp
  obtain ⟨he,hu⟩ := decoded_encode pair.1 pair.2
    (BooleanDifferences.mem_pairFamily.mp hp).2
  rw [he,hu]

theorem Invariant.stable {r Q n d P F : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {source : ProducedSource}
    {origin a b : State 40 896} {total : Truncated (q.p.model.O q.p.t) q.J}
    (h : Invariant q node H high P F source origin total a)
    (hf : ∀ i,(∀ j,i≠QueryStreamProgram.pairPorts.stack j) → b.stacks i=a.stacks i) :
    Invariant q node H high P F source origin total b := by
  have hout (i : Fin 896) (hi : (i.val < 832) ∨ (836 ≤ i.val)) :
      ∀ j,i≠QueryStreamProgram.pairPorts.stack j := by
    intro j he
    have hv := congrArg Fin.val he
    change i.val=832+j.val at hv
    have hj := j.isLt
    omega
  refine ⟨h.common.frame ?_,h.accumulator.frame (hf 850 (hout 850 (by decide))),
    (fun i hi => by rw [hf i hi]; exact h.compact i hi),?_,?_⟩
  · intro i hi
    have hc : ∀ j ∈ commonPorts,j.val<832 := by simp [commonPorts,Fin.coe_ofNat_eq_mod]
    exact hf i (hout i (Or.inl (hc i hi)))
  · constructor
    intro i hi
    exact (hf (SignatureHeadLoader.lowStacks i) (hout _ (Or.inl (by
      change i.val<832
      have := i.isLt
      omega)))).trans (h.masters.stored i hi)
  · intro i hi
    have hc : ∀ j ∈ framePorts,(j.val < 832) ∨ (836 ≤ j.val) := by
      simp [framePorts,Fin.coe_ofNat_eq_mod]
    exact (hf i (hout i (hc i hi))).trans (h.frame i hi)

/-- The fixed native pair traversal computes its complete signed tuple sum.
Correctness, measured time, and every source-prefix stack bound refer to this
same run; no tuple evaluator, callback or byte-family service is a premise. -/
theorem run_oai (s : ProducedSource) {d M F S Z B width height : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : SignatureTupleComplete.RetainedCap s F)
    (hheads : ∀ depth < s.input.r,s.headSize depth ≤ height)
    (a : State 40 896) (total : Truncated (q.p.model.O q.p.t) q.J)
    (hi : Invariant q s.input.node H high M F s a total a)
    (hm : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (haddress : a.stacks 649=List.replicate s.base true)
    (ha : ∀ i,(a.stacks i).length ≤ F)
    (hdepth : a.stacks 832=List.replicate (s.input.n-H.card) true)
    (hbudget : a.stacks 833=List.replicate q.J true)
    (houter : a.stacks 834=[]) (hinner : a.stacks 835=[]) :
    ∃ steps b, Eval QueryStreamProgram.pairs steps a b ∧
      Trace (compiled QueryStreamProgram.pairs 832 834) (steps+1)
        (a.withPC (some (compiled QueryStreamProgram.pairs 832 834).entry)) (b.withPC none) ∧
      Invariant q s.input.node H high M F s a
        (total+∑ pair ∈ BooleanDifferences.pairFamily (s.input.n-H.card) q.J,
          (-1)^(pair.1.card-pair.2.card)*pairValue s q H high owner head facts pair.1 pair.2) b ∧
      (∀ j,b.stacks (QueryStreamProgram.pairPorts.stack j)=a.stacks (QueryStreamProgram.pairPorts.stack j)) ∧
      (∀ i,(b.stacks i).length ≤ F) ∧
      steps+1 ≤ DifferencePairsProgram.cost
        (callbackBudget s q (s.input.n-H.card) F S Z B height) (s.input.n-H.card) q.J ∧
      ∀ elapsed cfg,elapsed ≤ steps+1 → Trace (compiled QueryStreamProgram.pairs 832 834) elapsed
        (a.withPC (some (compiled QueryStreamProgram.pairs 832 834).entry)) cfg →
        ∀ i,(cfg.stacks i).length ≤ max (callbackSpace s q (s.input.n-H.card) F B) (896*F+13) := by
  let I := Invariant q s.input.node H high M F s a
  let update := visit (s.input.n-H.card) (pairValue s q H high owner head facts)
  let C := callbackBudget s q (s.input.n-H.card) F S Z B height
  let D := callbackSpace s q (s.input.n-H.card) F B
  have spec : DifferencePairsRelational.CallbackSpec QueryStreamProgram.pairPorts
      QueryStreamProgram.pairCallback update C (s.input.n-H.card) I := by
    constructor
    · intro value d e hf hI
      exact hI.stable hf
    · intro J word value d hn hc hI
      obtain ⟨t,e,he,ht,hf,hIe,_hp⟩ := callback_cursor_run s q H high owner head facts caps cap
        hheads a d value hI hm haddress (J+1) word hn hc
      exact ⟨t,e,ht,he,hf,hIe⟩
  have hcallback : ∀ value j word d e t,word.length=s.input.n-H.card →
      (j+1)+word.countP Option.isSome=q.J →
      DifferencePairsProgram.Cursor QueryStreamProgram.pairPorts 0 (j+1) word true d →
      I value d → (∀ i,(d.stacks i).length ≤ F) →
      Eval QueryStreamProgram.pairCallback t
        (DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 d) e →
      (∀ i,(e.stacks i).length ≤ F) ∧
      ∀ elapsed cfg,elapsed ≤ t → Trace (compiled QueryStreamProgram.pairCallback 832 834) elapsed
        ((DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 d).withPC
          (some (compiled QueryStreamProgram.pairCallback 832 834).entry)) cfg →
        ∀ i,(cfg.stacks i).length ≤ D := by
    intro value j word d e t hn _hj hc hI hb he
    obtain ⟨t',e',he',_ht,_hf,_hIe,hp⟩ := callback_cursor_run s q H high owner head facts caps cap
      hheads a d value hI hm haddress (j+1) word hn hc
    have ht := StreamResources.eval_steps_eq (0 : Fin 896) 0 he he'
    have ho := he.final_unique (0 : Fin 896) he'
    subst t'
    subst e'
    exact ⟨(hp hb).1,fun elapsed cfg hk hz i => (hp hb).2.bound elapsed cfg (by omega) hz i⟩
  obtain ⟨steps,b,he,ht,htrace,hf,hIb,hspace⟩ := DifferencePairsRelational.program_resources
    QueryStreamProgram.pairPorts QueryStreamProgram.pairCallback update I C (s.input.n-H.card) q.J F D
    spec hcallback total a ha hi hdepth hbudget houter hinner
  have hbound : ∀ i,(b.stacks i).length ≤ F := by
    intro i
    by_cases hc : ∃ j,i=QueryStreamProgram.pairPorts.stack j
    · obtain ⟨j,rfl⟩ := hc
      rw [hf j]
      exact ha _
    · exact hIb.compact i (fun j he => hc ⟨j,he⟩)
  have hsemantic := hIb
  rw [show DifferencePairs.fold update (s.input.n-H.card) q.J [] total =
      total+∑ pair ∈ BooleanDifferences.pairFamily (s.input.n-H.card) q.J,
        (-1)^(pair.1.card-pair.2.card)*pairValue s q H high owner head facts pair.1 pair.2
      from fold_signed_sum _ _ _ _] at hsemantic
  exact ⟨steps,b,he,htrace,hsemantic,hf,hbound,ht,hspace⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.run_oai
