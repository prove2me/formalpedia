-- Prove2me | solution 1 for OAI.OptimalMaxCut.LongCode.InstanceAdapter.exists_encoded_gridComputer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:09:13.159995+00:00
-- url     : https://prove2.me/submissions/8317d723-5143-455c-8726-ef9a4e42ba00

import Mathlib
import Definitions.Def_OptimalMaxCut
import Definitions.Def_OAIQ087A029
import Definitions.Def_OAIQ087A031
import Definitions.Def_OAIQ087A032

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Rename
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset

 theorem quotient_sum (a b : ℕ) (hb : 0 < b) :
    (∑ i ∈ range a, if (i+1)*b ≤ a then (1:ℕ) else 0) = a/b := by
  have hcond (i : ℕ) : (i+1)*b ≤ a ↔ i < a/b := by
    rw [← Nat.le_div_iff_mul_le hb, Nat.add_one_le_iff]
  simp_rw [hcond]
  rw [sum_boole]
  have hs : {i ∈ range a | i < a/b} = range (a/b) := by
    ext i; simp only [mem_filter, mem_range]
    exact and_iff_right_of_imp (fun hi => hi.trans_le (Nat.div_le_self _ _))
  simp only [hs, card_range, Nat.cast_id]

@[simp] theorem quotient_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (quotient a b).eval input args = a.eval input args / b.eval input args := by
  simp only [quotient, eval, positive_eval, le_eval, rename_eval, bind]
  by_cases hb : b.eval input args = 0
  · simp [hb]
  · simp only [hb, ne_eq, not_false_eq_true, ↓reduceIte, one_mul]
    simpa using quotient_sum (a.eval input args) (b.eval input args) (by omega)

@[simp] theorem remainder_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (remainder a b).eval input args = a.eval input args % b.eval input args := by
  simp only [remainder, eval, quotient_eval]
  exact Nat.mod_eq_sub_div_mul.symm

end OptimalMaxCut.CounterMachine.Expr

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BitValue
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset

 theorem wordValue_true (s : List Bool) (k : ℕ) :
    wordValue (true::s) k = (if k=0 then 1 else 0)+wordValue s k := by
  rw [wordValue, List.length_cons, sum_range_succ']
  simp [wordValue, eq_comm, add_comm]

 theorem wordValue_false_succ (s : List Bool) (k : ℕ) :
    wordValue (false::s) (k+1) = wordValue s k := by
  rw [wordValue, List.length_cons, sum_range_succ']
  simp [wordValue, Nat.add_comm 1]

 theorem wordValue_block_zero (n : ℕ) (s : List Bool) :
    wordValue (List.replicate n true ++ false::s) 0 = n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, List.cons_append, wordValue_true, ↓reduceIte, ih]; omega

 theorem wordValue_block_succ (n k : ℕ) (s : List Bool) :
    wordValue (List.replicate n true ++ false::s) (k+1) = wordValue s k := by
  induction n with
  | zero => simpa using wordValue_false_succ s k
  | succ n ih => simp [List.replicate_succ, wordValue_true, ih]

 theorem wordValue_encoded (words : List ℕ) (k : ℕ) :
    wordValue (unaryWords words) k = (words[k]?).getD 0 := by
  induction words generalizing k with
  | nil => simp [unaryWords]
  | cons n words ih =>
    cases k with
    | zero => simpa [unaryWords, List.append_assoc] using wordValue_block_zero n (unaryWords words)
    | succ k =>
      simp only [unaryWords, List.flatMap_cons, List.append_assoc, List.singleton_append]
      change wordValue (List.replicate n true ++ false :: unaryWords words) (k+1) = _
      rw [wordValue_block_succ, ih]
      simp

end OptimalMaxCut.CounterMachine.Expr

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Divides
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

theorem indicator_and (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then (1:ℕ) else 0)*(if Q then 1 else 0) = if P ∧ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP,hQ]

@[simp] theorem divides_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (divides a b).eval input args = if a.eval input args ∣ b.eval input args then 1 else 0 := by
  simp [divides, eval, Nat.dvd_iff_mod_eq_zero]

@[simp] theorem prime_eval (n : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (prime n).eval input args = if (n.eval input args).Prime then 1 else 0 := by
  simp only [prime, eval, le_eval, divides_eval, rename_eval, bind]
  have h : (∑ i ∈ range (n.eval input args),
      (if 2 ≤ i then 1 else 0) * (if i ∣ n.eval input args then 1 else 0) : ℕ) = 0 ↔
      ∀ i, 2 ≤ i → i < n.eval input args → ¬ i ∣ n.eval input args := by
    rw [sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
    constructor
    · intro h i hi hn hd
      have hh := h i (mem_range.mpr hn)
      simp [hi, hd] at hh
    · intro h i hi
      by_cases h2 : 2 ≤ i
      · simp [h2, h i h2 (mem_range.mp hi)]
      · simp [h2]
  have hx : (if 2 ≤ n.eval input args then 1 else 0) *
      (if (∑ i ∈ range (n.eval input args),
        (if 2 ≤ i then 1 else 0)*(if i ∣ n.eval input args then 1 else 0) : ℕ)=0 then 1 else 0) =
        (if (n.eval input args).Prime then 1 else 0) := by
    simp only [h]
    exact (indicator_and _ _).trans (by simp only [Nat.prime_def_lt'])
  exact hx

@[simp] theorem powTwo_eval (n : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (powTwo n).eval input args = if ∃ k : ℕ, n.eval input args = 2^k then 1 else 0 := by
  let N := n.eval input args
  have h : (∑ i ∈ range (N+1), (if i.Prime then 1 else 0)*
      ((if i ∣ N then 1 else 0)*(if (if i=2 then 1 else 0)=0 then 1 else 0)) : ℕ) = 0 ↔
      ∀ i ≤ N, i.Prime → i ∣ N → i=2 := by
    rw [sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
    constructor
    · intro h i hi hp hd
      have hh := h i (mem_range.mpr (by omega))
      by_contra hn
      simp [hp,hd,hn] at hh
    · intro h i hi
      by_cases hp : i.Prime <;> by_cases hd : i ∣ N <;> simp_all
      exact h i (by omega) hp hd
  have hh : (N ≠ 0 ∧ ∀ i ≤ N, i.Prime → i ∣ N → i=2) ↔ ∃ k : ℕ, N=2^k := by
    constructor
    · rintro ⟨hn,hp⟩
      exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn (fun {d} hd hdn => hp d (Nat.le_of_dvd (by omega) hdn) hd hdn)⟩
    · rintro ⟨k,hk⟩
      rw [hk]
      refine ⟨by positivity, ?_⟩
      intro i hi hp hd
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
  simp only [powTwo, eval, positive_eval, prime_eval, divides_eval, equal_eval, rename_eval, bind]
  change (if N ≠ 0 then 1 else 0)*(if _=0 then 1 else 0) = if ∃ k, N=2^k then 1 else 0
  have hx : (if N ≠ 0 then 1 else 0)*(if
      (∑ i ∈ range (N+1), (if i.Prime then 1 else 0)*
      ((if i ∣ N then 1 else 0)*(if (if i=2 then 1 else 0)=0 then 1 else 0)) : ℕ) = 0
      then 1 else 0) = (if ∃ k, N=2^k then 1 else 0) := by
    simp only [h]
    exact (indicator_and _ _).trans (by simp only [hh])
  exact hx

 theorem count_powers (N : ℕ) :
    (∑ i ∈ range (N+1), if ∃ k : ℕ, i=2^k then (1:ℕ) else 0) = N.size := by
  rw [sum_boole]
  have hb : {i ∈ range (N+1) | ∃ k : ℕ, i=2^k} = (range N.size).image (fun k => 2^k) := by
    ext i
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hi,k,rfl⟩
      exact ⟨k, Nat.lt_size.mpr (by omega), rfl⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨by have := Nat.lt_size.mp hk; omega, k, rfl⟩
  rw [hb, card_image_of_injective _ (by intro a b h; exact (Nat.pow_right_injective (by omega : 2 ≤ 2)) h), card_range, Nat.cast_id]

@[simp] theorem size_eval (n : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (size n).eval input args = (n.eval input args).size := by
  simp only [size, eval, powTwo_eval, bind]
  exact count_powers (n.eval input args)

 theorem digitPower_eval (n i : Expr) (input : List Bool) (args : ℕ → ℕ)
    (hi : i.eval input args < (n.eval input args).size) :
    (digitPower n i).eval input args = 2^(i.eval input args) := by
  simp only [digitPower, eval, powTwo_eval, size_eval, equal_eval, rename_eval, bind]
  let N := n.eval input args
  let I := i.eval input args
  have hpow : 2^I ∈ range (N+1) := mem_range.mpr (by have hh := Nat.lt_size.mp hi; change 2^I ≤ N at hh; omega)
  rw [sum_eq_single_of_mem (2^I) hpow]
  · simp [Nat.size_pow, I]
  · intro b hb hne
    by_cases hp : ∃ k : ℕ, b=2^k
    · obtain ⟨k,rfl⟩ := hp
      have hk : k ≠ I := by rintro rfl; exact hne rfl
      simp only [Nat.size_pow, Nat.add_right_cancel_iff]
      have hk' : k ≠ i.eval input (fun j => args j) := hk
      simp [hk']
    · simp [hp]

 theorem digit_eval (n i : Expr) (input : List Bool) (args : ℕ → ℕ)
    (hi : i.eval input args < (n.eval input args).size) :
    (digit n i).eval input args = n.eval input args / 2^(i.eval input args) % 2 := by
  simp [digit, eval, digitPower_eval n i input args hi]

end OptimalMaxCut.CounterMachine.Expr

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_ListSum
attribute [-instance] _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

 theorem least_eval (bound predicate : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (least bound predicate).eval input args =
      ∑ i ∈ range (bound.eval input args),
        if predicate.eval input (bind args i) ≠ 0 ∧
          ∀ j < i, predicate.eval input (bind args j) = 0 then i else 0 := by
  have hb (i j : ℕ) : (fun k => bind (bind args i) j (match k with
      | 0 => 0
      | k+1 => k+2)) = bind args j := by
    funext k; cases k <;> rfl
  simp only [least, eval, positive_eval, rename_eval]
  apply sum_congr rfl
  intro i hi
  have hz : (∑ j ∈ range i,
      if predicate.eval input (bind args j) ≠ 0 then (1:ℕ) else 0) = 0 ↔
      ∀ j < i, predicate.eval input (bind args j)=0 := by
    simp only [sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _), mem_range]
    simp
  have key : (∑ x ∈ range (bind args i 0), if predicate.eval input (fun m => bind (bind args i) x (match m with
      | 0 => 0
      | m+1 => m+2)) ≠ 0 then (1:ℕ) else 0) =
      ∑ j ∈ range i, if predicate.eval input (bind args j) ≠ 0 then (1:ℕ) else 0 := by
    apply sum_congr rfl
    intro x _
    rw [hb i x]
  refine Eq.trans (congrArg (fun s => bind args i 0 * ((if predicate.eval input (bind args i) ≠ 0 then 1 else 0) * if s = 0 then 1 else 0)) key) ?_
  change i * ((if predicate.eval input (bind args i) ≠ 0 then 1 else 0) *
    (if (∑ j ∈ range i, if predicate.eval input (bind args j) ≠ 0 then (1:ℕ) else 0)=0 then 1 else 0)) = _
  simp only [hz]
  rw [indicator_and]
  split_ifs <;> simp

end OptimalMaxCut.CounterMachine.Expr

namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

theorem least_eq (bound predicate : Expr) (input : List Bool) (args : ℕ → ℕ) (k : ℕ)
    (hk : k < bound.eval input args)
    (hp : predicate.eval input (bind args k) ≠ 0)
    (he : ∀ j < k, predicate.eval input (bind args j) = 0) :
    (least bound predicate).eval input args = k := by
  rw [least_eval, sum_eq_single_of_mem k (mem_range.mpr hk)]
  · exact ite_eq_left ⟨hp, he⟩
  · intro j hj hne
    by_cases h : j < k
    · simp [he j h]
    · have hkj : k < j := by omega
      split_ifs with hgood
      · exact False.elim (hp (hgood.2 k hkj))
      · rfl

end OptimalMaxCut.CounterMachine.Expr
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

namespace Represented
variable {f g h : List Bool → (ℕ → ℕ) → ℕ}
theorem const (n : ℕ) : Represented (fun _ _ => n) := ⟨.const n, by intros; rfl⟩
theorem arg (k : ℕ) : Represented (fun _ a => a k) := ⟨.arg k, by intros; rfl⟩
theorem word (hf : Represented f) : Represented (fun s a => wordValue s (f s a)) := by
  obtain ⟨e,he⟩ := hf; exact ⟨Expr.word e, by intros; simp [he]⟩
theorem add (hf : Represented f) (hg : Represented g) : Represented (fun s a => f s a+g s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨.add e d, by intros; simp [eval,he,hd]⟩
theorem sub (hf : Represented f) (hg : Represented g) : Represented (fun s a => f s a-g s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨.sub e d, by intros; simp [eval,he,hd]⟩
theorem mul (hf : Represented f) (hg : Represented g) : Represented (fun s a => f s a*g s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨.mul e d, by intros; simp [eval,he,hd]⟩
theorem div (hf : Represented f) (hg : Represented g) : Represented (fun s a => f s a/g s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨quotient e d, by intros; simp [he,hd]⟩
theorem mod (hf : Represented f) (hg : Represented g) : Represented (fun s a => f s a%g s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨remainder e d, by intros; simp [he,hd]⟩
theorem pow (hf : Represented f) (n : ℕ) : Represented (fun s a => f s a^n) := by
  obtain ⟨e,he⟩ := hf; exact ⟨power e n, by intros; simp [he]⟩
theorem eq (hf : Represented f) (hg : Represented g) :
    Represented (fun s a => if f s a=g s a then 1 else 0) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨equal e d, by intros; simp [he,hd]⟩
theorem lt (hf : Represented f) (hg : Represented g) :
    Represented (fun s a => if f s a<g s a then 1 else 0) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; exact ⟨Expr.lt e d, by intros; simp [he,hd]⟩
theorem cond (hf : Represented f) (hg : Represented g) (hh : Represented h) :
    Represented (fun s a => if f s a ≠ 0 then g s a else h s a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg; obtain ⟨c,hc⟩ := hh
  exact ⟨Expr.cond e d c, by intros; simp [he,hd,hc]⟩
theorem sum (hf : Represented f) (hg : Represented g) :
    Represented (fun s a => ∑ i ∈ range (f s a), g s (bind a i)) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg
  exact ⟨.sum e d, by intros; simp [eval,he,hd]⟩
theorem finiteSum {I : Type} [Fintype I] {f : I → List Bool → (ℕ → ℕ) → ℕ}
    (hf : ∀ i, Represented (f i)) : Represented (fun s a => ∑ i, f i s a) := by
  choose e he using hf
  exact ⟨Expr.finiteSum e, by intros; simp [he]⟩
theorem rename (hf : Represented f) (r : ℕ → ℕ) :
    Represented (fun s a => f s (fun k => a (r k))) := by
  obtain ⟨e,he⟩ := hf
  exact ⟨e.rename r, by intros; simp [he]⟩
theorem congr (hf : Represented f) (h : ∀ s a, f s a=g s a) : Represented g := by
  obtain ⟨e,he⟩ := hf; exact ⟨e, fun s a => (he s a).trans (h s a)⟩
end Represented
end OptimalMaxCut.CounterMachine.Expr
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.Unweighted
attribute [local instance] Classical.propDecidable

 theorem roundedWeights_integer {I : Type} [Fintype I] {N : ℕ}
    (p : Law I) (endpoints : I → Fin N × Fin N) (v0 : Fin N)
    (P : ℕ) (hP : 0 < P) (u v : Fin N) :
    roundedWeights p endpoints v0 P hP u v =
      if u=v then 0 else
        ((∑ i : I, ((if endpoints i = (u,v) then ⌊(P:ℚ)*p.weight i⌋₊ else 0) +
          (if endpoints i = (v,u) then ⌊(P:ℚ)*p.weight i⌋₊ else 0)) : ℕ) : ℚ) / P := by
  by_cases huv : u=v
  · simp [roundedWeights, aggregate, huv]
  · simp only [roundedWeights, aggregate, huv, ↓reduceIte, Law.push, Fintype.sum_option,
      Law.grid, Law.gridWeight]
    have hn : (v0,v0) ≠ (u,v) := by rintro ⟨⟩; exact huv rfl
    have hn' : (v0,v0) ≠ (v,u) := by rintro ⟨⟩; exact huv rfl
    simp only [hn, hn', ↓reduceIte, zero_add, Nat.cast_sum, Nat.cast_add]
    rw [Finset.sum_add_distrib, add_div, Finset.sum_div, Finset.sum_div]
    congr 1 <;> (apply Finset.sum_congr rfl; intro i hi; split_ifs <;> simp)

namespace InstanceAdapter
variable {q : ℕ}

 theorem degree_eq (g : MaxCutGames.Foundations.Target.Instance q) (y : Fin g.vertices) :
    degree g y = Law.fiberSize (fun e : Fin g.constraints.length => g.constraints[e].target) y := by
  let : Nonempty (Fin g.constraints.length) := Fin.pos_iff_nonempty.mp g.constraintCount_positive
  simp only [degree, Law.fiberSize_eq_sum, Fin.getElem_fin]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp_all

 theorem sampleLaw_weight (g : MaxCutGames.Foundations.Target.Instance q) (t : ℚ)
    (ht : t ∈ Set.Icc (-1:ℚ) 1) (y : Fin g.vertices) (e f : Fin g.constraints.length)
    (x z : Cube (Fin q)) :
    ((ofInstance g).sampleLaw t ht).weight (y,e,f,x,z) =
      if g.constraints[e].target=y ∧ g.constraints[f].target=y then
        (degree g y : ℚ) * (jointLaw t ht q).weight (x,z) /
          ((g.constraints.length:ℚ)*(degree g y:ℚ)^2)
      else 0 := by
  let : Nonempty (Fin g.constraints.length) := Fin.pos_iff_nonempty.mp g.constraintCount_positive
  simp only [Game.sampleLaw, Law.bind, ofInstance, Law.fiberMarginal, Law.fiberConditional,
    Fintype.card_fin, ← degree_eq]
  simp only [Fin.getElem_fin] at *
  by_cases hd : degree g y = 0
  · simp [hd]
  · have hdQ : (degree g y:ℚ) ≠ 0 := by exact_mod_cast hd
    by_cases he : g.constraints[e.val].target=y <;> by_cases hf : g.constraints[f.val].target=y <;>
      simp [hd,he,hf] ; field_simp

end InstanceAdapter
end OptimalMaxCut.LongCode
namespace OptimalMaxCut.LongCode.InstanceAdapter
open scoped BigOperators
open Finset MaxCutGames.Foundations.Target MaxCutGames.Foundations.Hastad
open CounterMachine.Expr
attribute [local instance] Classical.propDecidable

theorem flatMap_getD {A B : Type} (l : List A) (f : A → List B) (d : B) (r : ℕ)
    (hf : ∀ a ∈ l, (f a).length=r) (e : Fin l.length) (j : ℕ) (hj : j < r) :
    ((l.flatMap f)[e.val*r+j]?).getD d = ((f l[e])[j]?).getD d := by
  induction l with
  | nil => exact e.elim0
  | cons a l ih =>
    rcases e with ⟨e,he⟩
    simp only [Fin.getElem_fin] at *
    cases e with
    | zero => simp only [List.flatMap_cons, zero_mul, zero_add, List.getElem_cons_zero]
              rw [List.getElem?_append_left (by simpa [hf a (by simp)] using hj)]
    | succ e =>
      have ha := hf a (by simp)
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by rw [ha]; nlinarith)]
      have hx : (e+1)*r+j-(f a).length=e*r+j := by rw [ha, Nat.add_mul]; omega
      rw [hx]
      exact ih (fun b hb => hf b (by simp [hb])) ⟨e,by simpa using he⟩

theorem word_header {q : ℕ} (g : Instance q) :
    wordValue (bits g) 0 = g.vertices ∧ wordValue (bits g) 1 = q ∧
      wordValue (bits g) 2 = g.constraints.length := by
  simp [bits,wordValue_encoded,words]

theorem word_row {q : ℕ} (g : Instance q) (e : Fin g.constraints.length)
    (j : ℕ) (hj : j<q+2) :
    wordValue (bits g) (3+e.val*(q+2)+j) = ((rowWords g.constraints[e])[j]?).getD 0 := by
  rw [bits, wordValue_encoded]
  simp only [words, List.cons_append, List.nil_append]
  have hx : 3+e.val*(q+2)+j = (e.val*(q+2)+j)+1+1+1 := by omega
  rw [hx]
  simp only [List.getElem?_cons_succ]
  exact flatMap_getD g.constraints rowWords 0 (q+2) (by intros; simp) e j hj

 theorem row_source {q : ℕ} (g : Instance q) (e : Fin g.constraints.length) :
    wordValue (bits g) (3+e.val*(q+2)) = g.constraints[e].source.val := by
  simpa [rowWords] using word_row g e 0 (by omega)
 theorem row_target {q : ℕ} (g : Instance q) (e : Fin g.constraints.length) :
    wordValue (bits g) (3+e.val*(q+2)+1) = g.constraints[e].target.val := by
  simpa [rowWords] using word_row g e 1 (by omega)
 theorem row_image {q : ℕ} (g : Instance q) (e : Fin g.constraints.length) (i : Fin q) :
    wordValue (bits g) (3+e.val*(q+2)+(2+i.val)) = g.constraints[e].permutation.images[i].val := by
  have h := word_row g e (2+i.val) (by omega)
  simpa [rowWords, Nat.add_comm 2] using h

end OptimalMaxCut.LongCode.InstanceAdapter
namespace OptimalMaxCut.CounterMachine.Expr.Represented
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {f g h j : List Bool → (ℕ → ℕ) → ℕ}
theorem iteEq (hf : Represented f) (hg : Represented g) (hh : Represented h) (hj : Represented j) :
    Represented (fun s a => if f s a=g s a then h s a else j s a) := by
  exact (cond (eq hf hg) hh hj).congr (by intros; split_ifs <;> simp_all)
theorem iteAndEq {v w : List Bool → (ℕ → ℕ) → ℕ}
    (hf : Represented f) (hg : Represented g) (hh : Represented h) (hj : Represented j)
    (hv : Represented v) (hw : Represented w) :
    Represented (fun s a => if f s a=g s a ∧ h s a=j s a then v s a else w s a) := by
  exact (cond ((eq hf hg).mul (eq hh hj)) hv hw).congr (by intros; split_ifs <;> simp_all)
theorem bounded {F : List Bool → (ℕ → ℕ) → ℕ → ℕ}
    (hb : Represented f)
    (hF : Represented (fun s a => F s (fun k => a (k+1)) (a 0))) :
    Represented (fun s a => ∑ i ∈ range (f s a), F s a i) := by
  exact (sum hb hF).congr (by intros; rfl)
end OptimalMaxCut.CounterMachine.Expr.Represented

namespace OptimalMaxCut.RawGrid
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open CounterMachine.Expr LongCode
attribute [local instance] Classical.propDecidable

namespace Rep
open CounterMachine.Expr.Represented
variable {f g h : List Bool → (ℕ → ℕ) → ℕ}
theorem vertices : Represented (fun s _ => RawGrid.vertices s) := word (Represented.const 0)
theorem edges : Represented (fun s _ => RawGrid.edges s) := word (Represented.const 2)
theorem row (q : ℕ) (hf : Represented f) (hg : Represented g) :
    Represented (fun s a => RawGrid.row q s (f s a) (g s a)) :=
  word (((Represented.const 3).add (hf.mul (Represented.const (q+2)))).add hg)
theorem degree (q : ℕ) (hy : Represented f) : Represented (fun s a => RawGrid.degree q s (f s a)) := by
  apply bounded edges
  exact eq (row q (Represented.arg 0) (Represented.const 1)) (hy.rename Nat.succ)
theorem lookup {q : ℕ} (x : Cube (Fin q)) (hj : Represented f) :
    Represented (fun s a => RawGrid.lookup x (f s a)) := by
  exact Represented.finiteSum (fun i => iteEq (Represented.const i.val) hj (Represented.const (finTwoEquiv.symm (x i)).val) (Represented.const 0))
theorem permCode {q : ℕ} (x : Cube (Fin q)) (he : Represented f) :
    Represented (fun s a => RawGrid.permCode s (f s a) x) := by
  exact Represented.finiteSum (fun i => (lookup x (row q he (Represented.const (2+i.val)))).mul (Represented.const (2^i.val)))
theorem query {q : ℕ} (x : Cube (Fin q)) (he : Represented f) :
    Represented (fun s a => RawGrid.query s (f s a) x) :=
  (permCode x he).add ((Represented.const (2^q)).mul (row q he (Represented.const 0)))
theorem gridSize (q K : ℕ) : Represented (fun s _ => RawGrid.gridSize q K s) :=
  (Represented.const (K+1)).mul ((vertices.mul (edges.mul (edges.mul (Represented.const (2^q*2^q))))).add (Represented.const 1))
theorem atom {q : ℕ} (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ)
    (x z : Cube (Fin q)) (hy : Represented f) (he : Represented g) (hf : Represented h) :
    Represented (fun s a => RawGrid.atom t ht K s (f s a) (g s a) (h s a) x z) := by
  refine iteAndEq (row q he (Represented.const 1)) hy (row q hf (Represented.const 1)) hy ?_ (Represented.const 0)
  exact ((gridSize q K).mul (degree q hy) |>.mul (Represented.const ((jointLaw t ht q).weight (x,z)).num.toNat)).div
    (((Represented.const ((jointLaw t ht q).weight (x,z)).den).mul edges).mul ((degree q hy).pow 2))

theorem weights (q : ℕ) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ)
    (hu : Represented f) (hv : Represented g) :
    Represented (fun s a => RawGrid.weights q t ht K s (f s a) (g s a)) := by
  refine iteEq hu hv (Represented.const 0) ?_
  apply bounded vertices
  apply bounded edges
  apply bounded edges
  apply Represented.finiteSum
  intro x
  apply Represented.finiteSum
  intro z
  let hu' := hu.rename (fun j => j+3)
  let hv' := hv.rename (fun j => j+3)
  have hA := atom t ht K x z (Represented.arg 2) (Represented.arg 1) (Represented.arg 0)
  exact (iteAndEq (query x (Represented.arg 1)) hu' (query (antipode z) (Represented.arg 0)) hv' hA (Represented.const 0)).add
    (iteAndEq (query x (Represented.arg 1)) hv' (query (antipode z) (Represented.arg 0)) hu' hA (Represented.const 0))
end Rep
end OptimalMaxCut.RawGrid

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_VerticesBits
attribute [-instance] _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.RawGrid
open scoped BigOperators
open Finset MaxCutGames.Foundations.Target MaxCutGames.Foundations.Hastad
open LongCode LongCode.InstanceAdapter CounterMachine.Expr
attribute [local instance] Classical.propDecidable

@[simp] theorem vertices_bits {q : ℕ} (g : Instance q) : vertices (bits g) = g.vertices := (word_header g).1
@[simp] theorem edges_bits {q : ℕ} (g : Instance q) : edges (bits g) = g.constraints.length := (word_header g).2.2
@[simp] theorem row_source {q : ℕ} (g : Instance q) (e : Fin g.constraints.length) :
    row q (bits g) e 0 = g.constraints[e].source.val := by
  simpa [row] using InstanceAdapter.row_source g e
@[simp] theorem row_target {q : ℕ} (g : Instance q) (e : Fin g.constraints.length) :
    row q (bits g) e 1 = g.constraints[e].target.val := InstanceAdapter.row_target g e
@[simp] theorem row_image {q : ℕ} (g : Instance q) (e : Fin g.constraints.length) (i : Fin q) :
    row q (bits g) e (2+i.val) = g.constraints[e].permutation.images[i].val := InstanceAdapter.row_image g e i

@[simp] theorem degree_bits {q : ℕ} (g : Instance q) (y : Fin g.vertices) :
    degree q (bits g) y = InstanceAdapter.degree g y := by
  rw [degree, edges_bits, ← Fin.sum_univ_eq_sum_range]
  unfold InstanceAdapter.degree
  apply sum_congr rfl
  intro e he
  rw [row_target]
  simp only [Fin.val_inj]

@[simp] theorem permCode_bits {q : ℕ} (g : Instance q) (e : Fin g.constraints.length)
    (x : Cube (Fin q)) :
    permCode (bits g) e x = (cubeEquiv q (cubePerm (MaxCutGames.Explicit.MachineOutputContract.permutationEquiv g.constraints[e].permutation) x)).val := by
  simp only [permCode, row_image, lookup_fin, cubeEquiv, Equiv.trans_apply, finFunctionFinEquiv_apply]
  rfl

@[simp] theorem query_bits {q : ℕ} (g : Instance q) (e : Fin g.constraints.length)
    (x : Cube (Fin q)) :
    query (bits g) e x = (vertexEquiv g.vertices q
      (g.constraints[e].source,cubePerm (MaxCutGames.Explicit.MachineOutputContract.permutationEquiv g.constraints[e].permutation) x)).val := by
  simp only [query, permCode_bits, row_source]
  rfl

@[simp] theorem gridSize_bits {q : ℕ} (g : Instance q) (K : ℕ) :
    gridSize q K (bits g) = Game.gridSize (Fin g.vertices) (Fin g.constraints.length) q K := by
  simp [gridSize, Game.gridSize, Game.Sample, vertices_bits, edges_bits]

 theorem rational_floor (c : ℚ) (hc : 0 ≤ c) (P d m : ℕ) :
    ⌊(P:ℚ)*((d:ℚ)*c/((m:ℚ)*(d:ℚ)^2))⌋₊ =
      P*d*c.num.toNat/(c.den*m*d^2) := by
  have hn : ((c.num.toNat:ℕ):ℚ) = (c.num:ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hc)
  have hc' : c = ((c.num.toNat:ℕ):ℚ)/c.den := by rw [hn, Rat.num_div_den]
  conv_lhs => rw [hc']
  have he : (P:ℚ)*((d:ℚ)*(((c.num.toNat:ℕ):ℚ)/c.den)/((m:ℚ)*(d:ℚ)^2)) =
      ((P*d*c.num.toNat:ℕ):ℚ)/((c.den*m*d^2:ℕ):ℚ) := by
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, Nat.floor_div_natCast, Nat.floor_natCast]

@[simp] theorem atom_bits {q : ℕ} (g : Instance q) (t : ℚ)
    (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ) (y : Fin g.vertices)
    (e f : Fin g.constraints.length) (x z : Cube (Fin q)) :
    atom t ht K (bits g) y e f x z =
      ⌊(Game.gridSize (Fin g.vertices) (Fin g.constraints.length) q K:ℚ)*
        ((ofInstance g).sampleLaw t ht).weight (y,e,f,x,z)⌋₊ := by
  rw [InstanceAdapter.sampleLaw_weight]
  simp only [atom, row_target, Fin.val_inj, gridSize_bits, degree_bits, edges_bits]
  split_ifs
  · exact (rational_floor _ ((jointLaw t ht q).nonneg _) _ _ _).symm
  · simp

/-- Byte-oriented integer aggregation is exactly the rational rounded law.
This identity is independent of computational complexity assumptions. -/
theorem weights_bits {q : ℕ} (g : Instance q) (t : ℚ)
    (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ)
    (anchor : Fin (g.vertices*2^q)) (u v : Fin (g.vertices*2^q)) :
    (ofInstance g).gridWeights t ht (vertexEquiv g.vertices q) anchor K u v =
      (weights q t ht K (bits g) u.val v.val : ℚ) / gridSize q K (bits g) := by
  rw [Game.gridWeights, roundedWeights_integer, gridSize_bits]
  by_cases huv : u=v
  · subst v; simp [weights]
  · have hval : u.val ≠ v.val := fun h => huv (Fin.ext h)
    simp only [huv, ↓reduceIte, weights, hval, vertices_bits, edges_bits]
    congr 2
    rw [Fintype.sum_prod_type]
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro y hy
    rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro e he
    rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro f hf
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro x hx
    apply sum_congr rfl
    intro z hz
    simp only [query_bits, atom_bits, Game.queries, ofInstance, Prod.mk.injEq, ← Fin.val_inj]

end OptimalMaxCut.RawGrid

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_FramedLen
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine
open scoped BigOperators
namespace Expr

@[simp] theorem framedLen_eval (n : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (framedLen n).eval input args = 2*(n.eval input args).size+1 := by
  simp [framedLen, eval]

 theorem framedBit_eval (n i : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (framedBit n i).eval input args =
      if i.eval input args < 2*(n.eval input args).size then
        if i.eval input args % 2 = 0 then 1 else n.eval input args / 2^(i.eval input args/2) % 2
      else 0 := by
  simp only [framedBit, cond_eval, lt_eval, eval, equal_eval, remainder_eval, size_eval]
  by_cases hi : i.eval input args < 2*(n.eval input args).size
  · simp only [hi, ↓reduceIte]
    by_cases h2 : i.eval input args % 2 = 0
    · simp [h2]
    · simp only [h2, ↓reduceIte]
      have hsmall : (quotient i (.const 2)).eval input args < (n.eval input args).size := by
        simp only [quotient_eval, eval]; omega
      simpa [quotient_eval, eval] using digit_eval n (quotient i (.const 2)) input args hsmall
  · simp [hi]
end Expr

 theorem frame_get (s : List Bool) (i : ℕ) :
    ((frame s)[i]?).getD false =
      if i<2*s.length then if i%2=0 then true else (s[i/2]?).getD false else false := by
  induction s generalizing i with
  | nil => simp [frame]
  | cons b s ih =>
    rcases i with _|_ | i
    · simp [frame]
    · simp [frame]; omega
    · simp only [frame, List.getElem?_cons_succ, ih, List.length_cons]
      have hdiv : (i+1+1)/2 = i/2+1 := by omega
      have hmod : (i+1+1)%2 = i%2 := by omega
      have hlt : i+1+1 < 2*(s.length+1) ↔ i<2*s.length := by omega
      simp only [hdiv,hmod,hlt,List.getElem?_cons_succ]

 theorem frame_bits_get (n i : ℕ) :
    ((frame n.bits)[i]?).getD false =
      decide ((if i<2*n.size then if i%2=0 then 1 else n/2^(i/2)%2 else 0 : ℕ) ≠ 0) := by
  rw [frame_get, Nat.size_eq_bits_len]
  by_cases hi : i<2*n.size <;> by_cases h2 : i%2=0 <;> simp only [hi,h2,↓reduceIte]
  · rfl
  · change n.bits.getI (i/2) = _
    rw [← Nat.testBit_eq_inth, Nat.testBit_eq_decide_div_mod_eq]
    simp only [Nat.mod_two_ne_zero]
  · rfl
  · rfl

end OptimalMaxCut.CounterMachine

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Arithmetic_Prime
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr.Represented
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {f g : List Bool → (ℕ → ℕ) → ℕ}
theorem framedLen (hf : Represented f) : Represented (fun s a => 2*(f s a).size+1) := by
  obtain ⟨e,he⟩ := hf; exact ⟨Expr.framedLen e, by intros; simp [he]⟩
theorem framedBit (hf : Represented f) (hg : Represented g) :
    Represented (fun s a => if g s a < 2*(f s a).size then
      if g s a % 2=0 then 1 else f s a / 2^(g s a/2)%2 else 0) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg
  exact ⟨Expr.framedBit e d, by intros; simp [Expr.framedBit_eval,he,hd]⟩
theorem iteLt {h j : List Bool → (ℕ → ℕ) → ℕ}
    (hf : Represented f) (hg : Represented g) (hh : Represented h) (hj : Represented j) :
    Represented (fun s a => if f s a<g s a then h s a else j s a) := by
  exact (cond (lt hf hg) hh hj).congr (by intros; split_ifs <;> simp_all)
theorem searchPrime (hf : Represented f) : Represented (fun s a => Unweighted.searchPrime (f s a)) := by
  obtain ⟨e,he⟩ := hf
  let b : Expr := .add (.mul (.const 2) (.add e (.const 1))) (.const 1)
  let p : Expr := .mul (Expr.lt (.add (e.rename Nat.succ) (.const 1)) (.arg 0)) (Expr.prime (.arg 0))
  refine ⟨least b p, ?_⟩
  intro s a
  let m := f s a
  have hs : ((List.range (2*(m+1)+1)).find? (fun q => decide (m+1<q ∧ q.Prime))).isSome := by
    obtain ⟨q,hq,hm,hb⟩ := Nat.exists_prime_lt_and_le_two_mul (m+1) (by omega)
    exact List.find?_isSome.mpr ⟨q,List.mem_range.mpr (by omega),by simp [hm,hq]⟩
  cases hh : ((List.range (2*(m+1)+1)).find? (fun q => decide (m+1<q ∧ q.Prime))) with
  | none => rw [hh] at hs; contradiction
  | some k =>
    have hp := List.find?_eq_some_iff_getElem.mp hh
    obtain ⟨i,hi,hik,hmin⟩ := hp.2
    have hik' : i=k := by simpa using hik
    subst i
    have hk : k<2*(m+1)+1 := by simpa using hi
    have hp' : m+1<k ∧ k.Prime := by simpa using hp.1
    change (least b p).eval s a = Unweighted.searchPrime m
    rw [Unweighted.searchPrime, hh]
    apply least_eq
    · simpa [b,eval,he,m] using hk
    · simp [p,eval,lt_eval,prime_eval,rename_eval,bind,he,hp',m]
    · intro j hj
      have hmin' : ¬ (m+1<j ∧ j.Prime) := by
        intro hbad
        have hh' := hmin j hj
        simp [hbad] at hh'
      simp only [p,eval,lt_eval,prime_eval,rename_eval,bind,he]
      by_cases hl : m+1<j <;> by_cases hp : j.Prime <;> simp_all [m]

end OptimalMaxCut.CounterMachine.Expr.Represented

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Param
attribute [-instance] _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.RawGrid
open scoped BigOperators
open Finset CounterMachine.Expr
attribute [local instance] Classical.propDecidable

namespace Rep
open CounterMachine.Expr.Represented
variable {f g h : List Bool → (ℕ → ℕ) → ℕ}
theorem param (q K : ℕ) : Represented (fun s _ => RawGrid.param q K s) :=
  searchPrime ((Represented.const K).mul (((vertices.mul (Represented.const (2^q))).add (Represented.const 1)).pow 2))
theorem size (q K : ℕ) : Represented (fun s _ => RawGrid.size q K s) :=
  (vertices.mul (Represented.const (2^q))).mul ((param q K).pow 6)
theorem scale (q K : ℕ) : Represented (fun s _ => RawGrid.scale q K s) := (param q K).pow 12
theorem coordinate (k : ℕ) (hp : Represented f) (hi : Represented g) :
    Represented (fun s a => RawGrid.coordinate (f s a) (g s a) k) :=
  ((hi.mod (hp.pow 6)).div (hp.pow k)).mod hp
theorem pairing (hp : Represented f) (hi : Represented g) (hj : Represented h) :
    Represented (fun s a => RawGrid.pairing (f s a) (g s a) (h s a)) :=
  (Represented.finiteSum (fun k : Fin 6 => (coordinate k.val hp hi).mul (coordinate k.val hp hj))).mod hp
theorem adjacency (q : ℕ) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K L : ℕ)
    (hi : Represented f) (hj : Represented g) :
    Represented (fun s a => RawGrid.adjacency q t ht K L s (f s a) (g s a)) := by
  let hp := param q L
  let hu := hi.div (hp.pow 6)
  let hv := hj.div (hp.pow 6)
  apply iteEq hu hv (Represented.const 0)
  apply bounded ((hp.mul (weights q t ht K hu hv)).div (gridSize q K))
  exact eq ((Represented.arg 0).mod hp) (pairing hp (hi.rename Nat.succ) (hj.rename Nat.succ))
theorem frameValue (hn : Represented f) (hi : Represented g) :
    Represented (fun s a => RawGrid.frameValue (f s a) (g s a)) := framedBit hn hi
theorem length (q L : ℕ) : Represented (fun s _ => RawGrid.length q L s) :=
  ((framedLen (size q L)).add (framedLen (scale q L))).add ((size q L).pow 2)
theorem entry (q : ℕ) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K L : ℕ)
    (hi : Represented f) : Represented (fun s a => RawGrid.entry q t ht K L s (f s a)) := by
  let hn := size q L
  let hd := framedLen hn
  let he := framedLen (scale q L)
  apply iteLt hi hd (frameValue hn hi)
  apply iteLt hi (hd.add he) (frameValue (scale q L) (hi.sub hd))
  exact adjacency q t ht K L (((hi.sub hd).sub he).div hn) (((hi.sub hd).sub he).mod hn)
end Rep
end OptimalMaxCut.RawGrid

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_VecEquivSymmVal
attribute [-instance] _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.Unweighted
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {p : ℕ} [Fact p.Prime]
 theorem vecEquiv_symm_val (x : Fin (p^6)) (k : Fin 6) :
    ((vecEquiv (p := p)).symm x k).val = x.val / p^k.val % p := by
  change ((ZMod.finEquiv p) ((finFunctionFinEquiv (m := p) (n := 6)).symm x k)).val = _
  cases p with
  | zero => exact False.elim (Nat.not_prime_zero Fact.out)
  | succ p => rfl
 theorem vertexEquiv_symm_first {N : ℕ} (i : Fin (N*p^6)) :
    ((vertexEquiv N).symm i).1.val = i.val / p^6 := rfl
 theorem vertexEquiv_symm_second {N : ℕ} (i : Fin (N*p^6)) (k : Fin 6) :
    (((vertexEquiv N).symm i).2 k).val = RawGrid.coordinate p i.val k.val := by
  exact vecEquiv_symm_val _ _
 theorem dot_val (x y : Vec p) : (dot x y).val = (∑ k : Fin 6, (x k).val*(y k).val)%p := by
  have he : dot x y = ((∑ k : Fin 6, (x k).val*(y k).val : ℕ) : ZMod p) := by
    simp only [Nat.cast_sum,Nat.cast_mul,ZMod.natCast_zmod_val,dot]
  rw [he, ZMod.val_natCast]
 theorem residue_membership (a : ZMod p) (w : ℚ) :
    a ∈ residueSet w ↔ ∃ r < ⌊(p:ℚ)*w⌋₊, r%p=a.val := by
  simp only [residueSet,mem_image,mem_range]
  constructor
  · rintro ⟨r,hr,he⟩
    exact ⟨r,hr,by simpa only [ZMod.val_natCast] using congrArg ZMod.val he⟩
  · rintro ⟨r,hr,he⟩
    exact ⟨r,hr,ZMod.val_injective p (by simpa only [ZMod.val_natCast] using he)⟩
end OptimalMaxCut.Unweighted

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_AdjacencyBits
attribute [-instance] _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.RawGrid
open scoped BigOperators
open Finset MaxCutGames.Foundations.Target MaxCutGames.Foundations.Hastad
open LongCode LongCode.InstanceAdapter CounterMachine.Expr
attribute [local instance] Classical.propDecidable

 theorem adjacency_bits {q : ℕ} (g : Instance q) (t : ℚ)
    (ht : t ∈ Set.Icc (-1:ℚ) 1) (K L : ℕ)
    (anchor : Fin (g.vertices*2^q))
    (i j : Fin ((g.vertices*2^q)*(Unweighted.searchPrime (L*(g.vertices*2^q+1)^2))^6)) :
    let w := (ofInstance g).gridWeights t ht (vertexEquiv g.vertices q) anchor K
    let out := Unweighted.deterministicOutput L w (aggregate_symm _)
    out.graph.adj i j = decide (adjacency q t ht K L (bits g) i.val j.val ≠ 0) := by
  dsimp only
  let p := Unweighted.searchPrime (L*(g.vertices*2^q+1)^2)
  let : Fact p.Prime := ⟨(Unweighted.searchPrime_spec _).1⟩
  have hparam : param q L (bits g) = p := by simp [param,p]
  change decide (_ ∧ _ ∈ _) = _
  apply Bool.decide_congr
  rw [Unweighted.residue_membership]
  rw [weights_bits]
  have hf : ⌊(p:ℚ)*((weights q t ht K (bits g) (i.val/p^6) (j.val/p^6):ℕ):ℚ)/
      (gridSize q K (bits g):ℚ)⌋₊ = p*weights q t ht K (bits g) (i.val/p^6) (j.val/p^6)/gridSize q K (bits g) := by
    rw [← Nat.cast_mul,Nat.floor_div_natCast,Nat.floor_natCast]
  have hd : (Unweighted.dot ((Unweighted.vertexEquiv (g.vertices*2^q)).symm i).2
      ((Unweighted.vertexEquiv (g.vertices*2^q)).symm j).2).val = pairing p i.val j.val := by
    rw [Unweighted.dot_val]
    simp only [Unweighted.vertexEquiv_symm_second,pairing]
    rfl
  simp only [mul_div_assoc, Unweighted.vertexEquiv_symm_first] at *
  rw [hf,hd]
  have hne : ((Unweighted.vertexEquiv (g.vertices*2^q)).symm i).1 ≠
      ((Unweighted.vertexEquiv (g.vertices*2^q)).symm j).1 ↔ i.val/p^6 ≠ j.val/p^6 := by
    rw [ne_eq, Fin.ext_iff]
    rfl
  rw [hne]
  unfold adjacency
  rw [hparam]
  change (_ ∧ _) ↔ ((if i.val/p^6=j.val/p^6 then 0 else _) ≠ 0)
  by_cases hij : i.val/p^6=j.val/p^6
  · simp [hij]
  · simp only [ne_eq,hij,not_false_eq_true,true_and,ite_false]
    simp only [sum_eq_zero_iff,mem_range,ite_eq_right_iff,one_ne_zero,imp_false,not_forall,not_not]
    constructor
    · rintro ⟨r,hr,he⟩; exact ⟨r,hr,he⟩
    · rintro ⟨r,hr,he⟩; exact ⟨r,hr,he⟩
end OptimalMaxCut.RawGrid

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Anchor
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut
open scoped BigOperators
open LongCode.InstanceAdapter CounterMachine
attribute [local instance] Classical.propDecidable

theorem nameBits_getD (n i : ℕ) :
    ((MaxCutGames.BinaryEncoding.nameBits n)[i]?).getD false =
      decide (RawGrid.frameValue n i ≠ 0) := by
  have he (s : List Bool) : MaxCutGames.BinaryEncoding.frame s = CounterMachine.frame s := by
    induction s with
    | nil => rfl
    | cons b s ih => simp only [MaxCutGames.BinaryEncoding.frame,CounterMachine.frame,ih]
  unfold MaxCutGames.BinaryEncoding.nameBits
  rw [he]
  exact CounterMachine.frame_bits_get n i

theorem Graph.table_getD (G : Graph) (i j : ℕ) (hi : i<G.vertices) (hj : j<G.vertices) :
    (((List.finRange G.vertices).flatMap (fun u =>
      (List.finRange G.vertices).map (fun v => G.adj u v)))[i*G.vertices+j]?).getD false =
      G.adj ⟨i,hi⟩ ⟨j,hj⟩ := by
  have h := flatMap_getD (List.finRange G.vertices)
    (fun u => (List.finRange G.vertices).map (fun v => G.adj u v)) false G.vertices
    (by intros; simp) ⟨i,by simpa using hi⟩ j hj
  simpa [Fin.getElem_fin, List.getElem?_eq_getElem, hj] using h

namespace RawGrid
open LongCode.InstanceAdapter MaxCutGames.Foundations.Target
@[simp] theorem size_bits {q : ℕ} (g : Instance q) (L : ℕ) :
    size q L (bits g) = g.vertices*2^q*(Unweighted.searchPrime (L*(g.vertices*2^q+1)^2))^6 := by
  simp [size,param]

 theorem graph_size {q : ℕ} (g : Instance q) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ) :
    (gridGraph g t ht K).graph.vertices = size q (K+1) (bits g) := by
  simp [gridGraph,LongCode.Game.gridOutput,Unweighted.deterministicOutput,
    Unweighted.blowupOutput,Unweighted.blowupGraph]

 theorem graph_scale {q : ℕ} (g : Instance q) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ) :
    (gridGraph g t ht K).scale = scale q (K+1) (bits g) := by
  simp [gridGraph,LongCode.Game.gridOutput,Unweighted.deterministicOutput,
    Unweighted.blowupOutput,scale,param]

 theorem bits_length {q : ℕ} (g : Instance q) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ) :
    (gridGraph g t ht K).bits.length = length q (K+1) (bits g) := by
  rw [ScaledGraph.bits_length_exact, graph_size, graph_scale]; rfl

 theorem graph_adj {q : ℕ} (g : Instance q) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ)
    (i j : Fin (gridGraph g t ht K).graph.vertices) :
    (gridGraph g t ht K).graph.adj i j =
      decide (adjacency q t ht K (K+1) (bits g) i.val j.val ≠ 0) :=
  adjacency_bits g t ht K (K+1) (anchor g) i j

 theorem bits_getD {q : ℕ} (g : Instance q) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ)
    (i : ℕ) (hi : i<length q (K+1) (bits g)) :
    (((gridGraph g t ht K).bits)[i]?).getD false =
      decide (entry q t ht K (K+1) (bits g) i ≠ 0) := by
  let G := gridGraph g t ht K
  let d := 2*(size q (K+1) (bits g)).size+1
  let e := 2*(scale q (K+1) (bits g)).size+1
  have hd : (MaxCutGames.BinaryEncoding.nameBits G.graph.vertices).length = d := by
    rw [nameBits_length_exact,graph_size]
  have he : (MaxCutGames.BinaryEncoding.nameBits G.scale).length = e := by
    rw [nameBits_length_exact,graph_scale]
  simp only [ScaledGraph.bits, List.append_assoc]
  unfold entry
  by_cases hid : i<d
  · rw [List.getElem?_append_left (by rwa [hd]), nameBits_getD, graph_size]
    simp only [show i<2*(size q (K+1) (bits g)).size+1 from hid,↓reduceIte]
  · rw [List.getElem?_append_right (by rw [hd]; omega),hd]
    by_cases hie : i<d+e
    · rw [List.getElem?_append_left (by rw [he]; omega),nameBits_getD,graph_scale]
      simp only [show ¬i<2*(size q (K+1) (bits g)).size+1 from hid,↓reduceIte,
        show i<(2*(size q (K+1) (bits g)).size+1)+(2*(scale q (K+1) (bits g)).size+1) from hie,↓reduceIte]
      rfl
    · rw [List.getElem?_append_right (by rw [he]; omega),he]
      simp only [show ¬i<2*(size q (K+1) (bits g)).size+1 from hid,↓reduceIte,
        show ¬i<(2*(size q (K+1) (bits g)).size+1)+(2*(scale q (K+1) (bits g)).size+1) from hie,↓reduceIte]
      have hlen : i-d-e < G.graph.vertices^2 := by
        rw [graph_size]; dsimp [length,d,e] at *; omega
      have hn : 0<G.graph.vertices := by nlinarith
      have hij : i-d-e < G.graph.vertices*G.graph.vertices := by simpa only [pow_two] using hlen
      have hrow := (Nat.div_lt_iff_lt_mul hn).mpr hij
      have hcol := Nat.mod_lt (i-d-e) hn
      have h := G.graph.table_getD ((i-d-e)/G.graph.vertices) ((i-d-e)%G.graph.vertices) hrow hcol
      rw [Nat.mul_comm ((i-d-e)/G.graph.vertices) _, Nat.div_add_mod] at h
      rw [h,graph_adj]
      simp only [G,graph_size,d,e]
end RawGrid
end OptimalMaxCut

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Printer
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine
open Turing Polynomial Command

 theorem tableComputer_finiteAlphabet (len bit : Expr) (k : (tableComputer len bit).tm.K) :
    Finite ((tableComputer len bit).tm.Γ k) := inferInstanceAs (Finite Bool)

end OptimalMaxCut.CounterMachine

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Arithmetic_GridComputer
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode.InstanceAdapter
open scoped BigOperators
open MaxCutGames.Foundations.Target CounterMachine Turing
attribute [local instance] Classical.propDecidable

theorem exists_gridComputer (q : ℕ) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ) :
    ∃ pc : TM2ComputableInPolyTime (bits : Instance q → List Bool) ScaledGraph.bits
      (fun g => gridGraph g t ht K), ∀ k, Finite (pc.tm.Γ k) := by
  obtain ⟨len,hlen⟩ := RawGrid.Rep.length q (K+1)
  obtain ⟨bit,hbit⟩ := RawGrid.Rep.entry q t ht K (K+1) (Expr.Represented.arg 0)
  have htable (g : Instance q) : table len bit (bits g) = (gridGraph g t ht K).bits := by
    apply List.ext_getElem
    · simp only [table,List.length_ofFn,hlen,RawGrid.bits_length]
    · intro i hi hj
      have hi' : i<RawGrid.length q (K+1) (bits g) := by
        simpa only [RawGrid.bits_length] using hj
      have hh := RawGrid.bits_getD g t ht K i hi'
      rw [List.getElem?_eq_getElem hj] at hh
      simp only [Option.getD_some] at hh
      simp only [table,List.getElem_ofFn,hbit]
      exact hh.symm
  let first := tableComputer len bit
  let pc : TM2ComputableInPolyTime (bits : Instance q → List Bool) ScaledGraph.bits
      (fun g => gridGraph g t ht K) := {
    tm := first.tm
    inputAlphabet := first.inputAlphabet
    outputAlphabet := first.outputAlphabet
    time := first.time
    outputsFun := fun g => by
      have hh := first.outputsFun (bits g)
      change TM2OutputsInTime first.tm ((bits g).map first.inputAlphabet.symm)
        (some ((table len bit (bits g)).map first.outputAlphabet.symm)) _ at hh
      rw [htable] at hh
      exact hh }
  exact ⟨pc, tableComputer_finiteAlphabet len bit⟩

end OptimalMaxCut.LongCode.InstanceAdapter

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace OptimalMaxCut.LongCode.InstanceAdapter
open MaxCutGames.Foundations.Target MaxCutGames.Foundations.Complexity

theorem bits_eq_gameBits {q : ℕ} (g : Instance q) : bits g = gameBits g := by
  have hw (l : List ℕ) : CounterMachine.Expr.unaryWords l = encodeWords l := by
    induction l with
    | nil => rfl
    | cons n l ih =>
      simp only [CounterMachine.Expr.unaryWords,List.flatMap_cons,encodeWords,encodeWord] at *
      rw [ih]
  unfold bits gameBits
  rw [hw]
  rfl

 theorem exists_encoded_gridComputer_oai (q : ℕ) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ) :
    ∃ pc : Turing.TM2ComputableInPolyTime (gameBits : Instance q → List Bool) ScaledGraph.bits
      (fun g => gridGraph g t ht K), MachineFiniteAlphabet.FiniteAlphabet pc.tm := by
  obtain ⟨pc,hpc⟩ := exists_gridComputer q t ht K
  let pc' : Turing.TM2ComputableInPolyTime (gameBits : Instance q → List Bool) ScaledGraph.bits
      (fun g => gridGraph g t ht K) := {
    tm := pc.tm
    inputAlphabet := pc.inputAlphabet
    outputAlphabet := pc.outputAlphabet
    time := pc.time
    outputsFun := fun g => by simpa only [bits_eq_gameBits] using pc.outputsFun g }
  exact ⟨pc',hpc⟩
end OptimalMaxCut.LongCode.InstanceAdapter

end

end OAI
end

theorem solution : type_of% @OAI.OptimalMaxCut.LongCode.InstanceAdapter.exists_encoded_gridComputer_oai := @OAI.OptimalMaxCut.LongCode.InstanceAdapter.exists_encoded_gridComputer_oai
