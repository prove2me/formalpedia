-- Prove2me | solution 1 for OAI.Problem355.heilbronn_power_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T19:17:36.609902+00:00
-- url     : https://prove2.me/submissions/cd7e9ac9-5523-452d-a76d-4d82ca4679cd

import Mathlib
import Definitions.Def_HeilbronnTriangle
import Definitions.Def_OAIQWHT000
import Theorems.Thm_OAI_Problem355_UniformFixedFiberCount_matrix_fiber_le

section
-- module Solutions.OAIQW_Problem355.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LiftingProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem355.LiftingProbability

 theorem inclusionMass_nonneg {Ω B : Type*} [Fintype Ω]
    (w : Ω → ℝ) (V : Ω → Finset B) (hw : ∀ ω, 0 ≤ w ω) (b : Fin 3 → B) :
    0 ≤ inclusionMass w V b := by
  classical
  unfold inclusionMass
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp_all

theorem mainMass_nonneg {A : Type*} (O : Finset A) (a : A) : 0 ≤ mainMass O a := by
  classical
  unfold mainMass
  split_ifs <;> positivity

theorem auxiliaryMass_nonneg {Ω B : Type*} [Fintype Ω]
    (w : Ω → ℝ) (V : Ω → Finset B) (s : ℕ) (hw : ∀ ω, 0 ≤ w ω) (b : Fin 3 → B) :
    0 ≤ auxiliaryMass w V s b :=
  div_nonneg (inclusionMass_nonneg w V hw b) (pow_nonneg (Nat.cast_nonneg _) _)

theorem liftedMass_nonneg {X A Ω B : Type*} [Fintype Ω]
    (f : X → A) (g : X → (Fin 3 → B))
    (O : Finset A) (w : Ω → ℝ) (V : Ω → Finset B) (s M : ℕ)
    (hw : ∀ ω, 0 ≤ w ω) (x : X) :
    0 ≤ liftedMass f g O w V s M x :=
  div_nonneg (mul_nonneg (mainMass_nonneg O (f x))
    (auxiliaryMass_nonneg w V s hw (g x))) (Nat.cast_nonneg _)

theorem lifting_normalization (h q L s o : ℝ) (z : ℝ)
    (hh : h ≠ 0) (hq : q ≠ 0) (hL : L ≠ 0) (hs : s ≠ 0) (ho : o ≠ 0) :
    (1 / o) * (z / s ^ 3) / L ^ 9 =
      h ^ 9 / ((L * (h * q)) ^ 9 * o) * ((q ^ 3 / s) ^ 3 * z) := by
  field_simp

theorem liftedMass_eq_weight {X A Ω B : Type*} [Fintype Ω] [DecidableEq A]
    (f : X → A) (g : X → (Fin 3 → B))
    (O : Finset A) (hO : O.Nonempty) (w : Ω → ℝ) (V : Ω → Finset B)
    (s h q L : ℕ) (hs : 0 < s) (hh : 0 < h) (hq : 0 < q) (hL : 0 < L) (x : X) :
    liftedMass f g O w V s (L ^ 9) x =
      if f x ∈ O then
        (h : ℝ) ^ 9 / ((L * (h * q) : ℕ) ^ 9 * (O.card : ℝ)) *
          auxiliaryWeight q s w V (g x)
      else 0 := by
  classical
  unfold liftedMass residueMass mainMass auxiliaryMass auxiliaryWeight
  split_ifs with hx
  · simp only [Nat.cast_pow, Nat.cast_mul]
    apply lifting_normalization
    · exact_mod_cast Nat.ne_of_gt hh
    · exact_mod_cast Nat.ne_of_gt hq
    · exact_mod_cast Nat.ne_of_gt hL
    · exact_mod_cast Nat.ne_of_gt hs
    · exact_mod_cast Finset.card_ne_zero.mpr hO
  · simp

theorem exact_lifting_identity {X A Ω B : Type*} [Fintype Ω] [DecidableEq A]
    (f : X → A) (g : X → (Fin 3 → B))
    (O : Finset A) (hO : O.Nonempty) (w : Ω → ℝ) (V : Ω → Finset B)
    (s h q L : ℕ) (hs : 0 < s) (hh : 0 < h) (hq : 0 < q) (hL : 0 < L)
    (E : Finset X) :
    (∑ x ∈ E, liftedMass f g O w V s (L ^ 9) x) =
      (h : ℝ) ^ 9 / ((L * (h * q) : ℕ) ^ 9 * (O.card : ℝ)) *
        ∑ x ∈ E.filter (fun x => f x ∈ O), auxiliaryWeight q s w V (g x) := by
  classical
  simp_rw [liftedMass_eq_weight f g O hO w V s h q L hs hh hq hL]
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

theorem product_conditionalColumnMass {X A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : X → A) (g : X → B) (a : Fin 3 → A) (V : Finset B) (s L : ℕ)
    (x : Fin 3 → X) :
    (∏ i, conditionalColumnMass f g (a i) V s L (x i)) =
      if (fun i => f (x i)) = a ∧ TripleIn V (fun i => g (x i)) then
        1 / ((s : ℝ) ^ 3 * (L : ℝ) ^ 9) else 0 := by
  classical
  have hp : (∀ i, f (x i) = a i ∧ g (x i) ∈ V) ↔
      (fun i => f (x i)) = a ∧ TripleIn V (fun i => g (x i)) := by
    simp only [TripleIn, funext_iff, forall_and]
  by_cases hall : ∀ i, f (x i) = a i ∧ g (x i) ∈ V
  · calc
      (∏ i, conditionalColumnMass f g (a i) V s L (x i)) =
          ∏ _i : Fin 3, (1 : ℝ) / ((s : ℝ) * (L : ℝ) ^ 3) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [conditionalColumnMass, hall i]
      _ = _ := by simp [hp.mp hall, mul_pow, ← pow_mul]
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    have hz : conditionalColumnMass f g (a i) V s L (x i) = 0 := by
      simp [conditionalColumnMass, hi]
    have hzero : (∏ i, conditionalColumnMass f g (a i) V s L (x i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    have hnot : ¬ ((fun i => f (x i)) = a ∧ TripleIn V (fun i => g (x i))) :=
      fun h => hall (hp.mpr h)
    rw [hzero]
    simp [hnot]

theorem sum_independent_indicators {Θ Ω : Type*} [Fintype Θ] [Fintype Ω]
    (ρ : Θ → ℝ) (w : Ω → ℝ) (P : Θ → Prop) (Q : Ω → Prop)
    [DecidablePred P] [DecidablePred Q] (K : ℝ) :
    (∑ θ, ρ θ * ∑ ω, w ω * (if P θ ∧ Q ω then K else 0)) =
      (∑ θ, if P θ then ρ θ else 0) * (∑ ω, if Q ω then w ω else 0) * K := by
  classical
  calc
    (∑ θ, ρ θ * ∑ ω, w ω * (if P θ ∧ Q ω then K else 0)) =
        ∑ θ, (if P θ then ρ θ else 0) * ((∑ ω, if Q ω then w ω else 0) * K) := by
      apply Finset.sum_congr rfl
      intro θ hθ
      by_cases hP : P θ
      · simp only [hP, true_and, ite_true]
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hQ : Q ω <;> simp [hQ]
      · simp [hP]
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

theorem averaged_columns_eq_liftedMass
    {X A B Θ Ω : Type*} [Fintype Θ] [Fintype Ω]
    (f : X → A) (g : X → B) (F : Θ → (Fin 3 → A))
    (ρ : Θ → ℝ) (w : Ω → ℝ) (V : Ω → Finset B)
    (O : Finset (Fin 3 → A)) (s L : ℕ)
    (hpush : ∀ a, pushforwardMass ρ F a = mainMass O a)
    (x : Fin 3 → X) :
    (∑ θ, ρ θ * ∑ ω, w ω *
      ∏ i, conditionalColumnMass f g (F θ i) (V ω) s L (x i)) =
      liftedMass (fun x i => f (x i)) (fun x i => g (x i))
        O w V s (L ^ 9) x := by
  classical
  simp_rw [product_conditionalColumnMass]
  rw [sum_independent_indicators]
  have hmain : (∑ θ, if (fun i => f (x i)) = F θ then ρ θ else 0) =
      mainMass O (fun i => f (x i)) := by
    calc
      (∑ θ, if (fun i => f (x i)) = F θ then ρ θ else 0) =
          pushforwardMass ρ F (fun i => f (x i)) := by
        unfold pushforwardMass
        apply Finset.sum_congr rfl
        intro θ hθ
        by_cases h : (fun i => f (x i)) = F θ <;> simp [h]
      _ = _ := hpush _
  rw [hmain]
  unfold liftedMass residueMass auxiliaryMass inclusionMass
  simp only [Nat.cast_pow, div_eq_mul_inv, mul_inv_rev]
  ring

end Problem355.LiftingProbability

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DigitUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.Digits

theorem take_eq_of_ofDigits_mod_eq {b j : ℕ} (hb : 1 < b)
    {A B : List ℕ} (hlen : A.length = B.length)
    (hA : ∀ a ∈ A, a < b) (hB : ∀ a ∈ B, a < b)
    (hmod : Nat.ofDigits b A % b ^ j = Nat.ofDigits b B % b ^ j) :
    A.take j = B.take j := by
  apply Nat.ofDigits_inj_of_len_eq hb
  · simp [hlen]
  · exact fun a ha => hA a (List.mem_of_mem_take ha)
  · exact fun a ha => hB a (List.mem_of_mem_take ha)
  · simpa only [Nat.ofDigits_mod_pow_eq_ofDigits_take j (by omega) A hA,
      Nat.ofDigits_mod_pow_eq_ofDigits_take j (by omega) B hB] using hmod

theorem initial_digits_eq_of_sum_mod_eq {b k j : ℕ} (hb : 1 < b)
    {d e : Fin k → ℕ} (hd : ∀ i, d i < b) (he : ∀ i, e i < b)
    (hmod : (∑ i : Fin k, d i * b ^ i.val) % b ^ j =
      (∑ i : Fin k, e i * b ^ i.val) % b ^ j) :
    ∀ i : Fin k, i.val < j → d i = e i := by
  have htake : (List.ofFn d).take j = (List.ofFn e).take j := by
    apply take_eq_of_ofDigits_mod_eq hb (by simp)
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact hd i
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact he i
    · simpa only [ofDigits_ofFn_eq_sum] using hmod
  intro i hi
  have hget := congrArg (fun l : List ℕ => l[i.val]?) htake
  simpa [List.getElem?_take, hi] using hget

end Problem355.Digits

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DivisorMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


open scoped BigOperators

namespace Problem355.DivisorMoment

theorem weighted_power_moment_le_geom_sum
    {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (b : Ω → ℕ)
    (B ρ : ℝ) (k : ℕ)
    (hp : ∀ ω, 0 ≤ p ω) (hB : 0 ≤ B)
    (hb : ∀ ω, b ω ≤ k)
    (htail : ∀ j, j ≤ k →
      (∑ ω, if j ≤ b ω then p ω else 0) ≤ ρ ^ j) :
    (∑ ω, p ω * B ^ b ω) ≤
      ∑ j ∈ Finset.range (k + 1), (B * ρ) ^ j := by
  classical
  calc
    (∑ ω, p ω * B ^ b ω) ≤
        ∑ ω, p ω * (∑ j ∈ Finset.range (k + 1),
          if j ≤ b ω then B ^ j else 0) := by
      apply Finset.sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (hp ω)
      have hsingle := Finset.single_le_sum
        (s := Finset.range (k + 1))
        (f := fun j => if j ≤ b ω then B ^ j else 0)
        (fun j _ => by split_ifs <;> positivity)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (hb ω)))
      simpa using hsingle
    _ = ∑ j ∈ Finset.range (k + 1),
        B ^ j * (∑ ω, if j ≤ b ω then p ω else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro ω _
      split_ifs <;> simp [mul_comm]
    _ ≤ ∑ j ∈ Finset.range (k + 1), B ^ j * ρ ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (htail j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
        (pow_nonneg hB j)
    _ = ∑ j ∈ Finset.range (k + 1), (B * ρ) ^ j := by
      simp_rw [mul_pow]

theorem weighted_power_moment_le_inv
    {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (b : Ω → ℕ)
    (B ρ : ℝ) (k : ℕ)
    (hp : ∀ ω, 0 ≤ p ω) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hb : ∀ ω, b ω ≤ k)
    (htail : ∀ j, j ≤ k →
      (∑ ω, if j ≤ b ω then p ω else 0) ≤ ρ ^ j)
    (hsmall : B * ρ < 1) :
    (∑ ω, p ω * B ^ b ω) ≤ 1 / (1 - B * ρ) := by
  apply (weighted_power_moment_le_geom_sum p b B ρ k hp hB hb htail).trans
  simpa using
    (geom_sum_Ico_le_of_lt_one (m := 0) (n := k + 1)
      (mul_nonneg hB hρ) hsmall)

theorem normalized_power_moment_le_inv
    {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (b : Ω → ℕ)
    (B ρ : ℝ) (k : ℕ)
    (hp : ∀ ω, 0 ≤ p ω) (hmass : ∑ ω, p ω = 1)
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (hb : ∀ ω, b ω ≤ k)
    (htail : ∀ j, 1 ≤ j → j ≤ k →
      (∑ ω, if j ≤ b ω then p ω else 0) ≤ ρ ^ j)
    (hsmall : B * ρ < 1) :
    (∑ ω, p ω * B ^ b ω) ≤ 1 / (1 - B * ρ) := by
  apply weighted_power_moment_le_inv p b B ρ k hp hB hρ hb _ hsmall
  intro j hj
  rcases j with _ | j
  · simp [hmass]
  · exact htail (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) hj

theorem normalized_power_moment_le_two
    {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (b : Ω → ℕ)
    (B ρ : ℝ) (k : ℕ)
    (hp : ∀ ω, 0 ≤ p ω) (hmass : ∑ ω, p ω = 1)
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (hb : ∀ ω, b ω ≤ k)
    (htail : ∀ j, 1 ≤ j → j ≤ k →
      (∑ ω, if j ≤ b ω then p ω else 0) ≤ ρ ^ j)
    (hsmall : B * ρ ≤ 1 / 2) :
    (∑ ω, p ω * B ^ b ω) ≤ 2 := by
  have heta : B * ρ < 1 := lt_of_le_of_lt hsmall (by norm_num)
  apply (normalized_power_moment_le_inv p b B ρ k hp hmass hB hρ hb
    htail heta).trans
  apply (div_le_iff₀ (sub_pos.mpr heta)).mpr
  nlinarith

end Problem355.DivisorMoment

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ConditionalDigits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.ConditionalDigits

open scoped BigOperators

theorem card_residue_event_le {α ι X : Type*} [Fintype α] [Fintype ι] [Fintype X]
    {B j k : ℕ} (hB : 1 < B) (hj : j ≤ k)
    (digit : ι → Fin k → X → Fin B)
    (hinj : ∀ i u, Function.Injective (digit i u))
    (target : α → ι → ℕ)
    (bad : Finset (α × (ι → Fin k → X)))
    (hbad : ∀ z ∈ bad, ∀ i,
      (∑ u : Fin k, (digit i u (z.2 i u)).val * B ^ u.val) % B ^ j =
        target z.1 i) :
    bad.card ≤ Fintype.card α * Fintype.card X ^ (Fintype.card ι * (k - j)) := by
  classical
  let lift : Fin (k - j) → Fin k := fun u => ⟨j + u.val, by omega⟩
  let tail : (α × (ι → Fin k → X)) → (α × (ι → Fin (k - j) → X)) :=
    fun z => (z.1, fun i u => z.2 i (lift u))
  have hcard := Finset.card_le_card_of_injOn
    (s := bad) (t := Finset.univ) tail
    (by intro z hz; exact Finset.mem_univ _)
  have htail : Set.InjOn tail (bad : Set (α × (ι → Fin k → X))) := by
    intro z hz z' hz' hzz'
    have hfst : z.1 = z'.1 :=
      congrArg (fun y : α × (ι → Fin (k - j) → X) => y.1) hzz'
    have hsnd := congrArg (fun y : α × (ι → Fin (k - j) → X) => y.2) hzz'
    apply Prod.ext hfst
    funext i
    have hmod :
        (∑ u : Fin k, (digit i u (z.2 i u)).val * B ^ u.val) % B ^ j =
        (∑ u : Fin k, (digit i u (z'.2 i u)).val * B ^ u.val) % B ^ j := by
      rw [hbad z hz i, hbad z' hz' i, hfst]
    have hfirst := Digits.initial_digits_eq_of_sum_mod_eq hB
      (fun u => (digit i u (z.2 i u)).isLt)
      (fun u => (digit i u (z'.2 i u)).isLt) hmod
    funext u
    by_cases hu : u.val < j
    · apply hinj i u
      apply Fin.ext
      exact hfirst u hu
    · let v : Fin (k - j) := ⟨u.val - j, by omega⟩
      have hlift : lift v = u := by
        apply Fin.ext
        dsimp [lift, v]
        omega
      have hv := congrFun (congrFun hsnd i) v
      change z.2 i (lift v) = z'.2 i (lift v) at hv
      simpa only [hlift] using hv
  simpa [← pow_mul, Nat.mul_comm] using hcard htail

theorem residue_event_probability_le {α ι X : Type*}
    [Fintype α] [Nonempty α] [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X]
    {B j k : ℕ} (hB : 1 < B) (hj : j ≤ k)
    (digit : ι → Fin k → X → Fin B)
    (hinj : ∀ i u, Function.Injective (digit i u))
    (target : α → ι → ℕ)
    (bad : Finset (α × (ι → Fin k → X)))
    (hbad : ∀ z ∈ bad, ∀ i,
      (∑ u : Fin k, (digit i u (z.2 i u)).val * B ^ u.val) % B ^ j =
        target z.1 i) :
    (bad.card : ℝ) / Fintype.card (α × (ι → Fin k → X)) ≤
      1 / (Fintype.card X : ℝ) ^ (Fintype.card ι * j) := by
  have hcard := card_residue_event_le hB hj digit hinj target bad hbad
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hden : (Fintype.card (α × (ι → Fin k → X)) : ℝ) =
      (Fintype.card α : ℝ) * (Fintype.card X : ℝ) ^ (Fintype.card ι * k) := by
    simp [← pow_mul, Nat.mul_comm]
  rw [hden]
  apply (div_le_div_iff₀ (by positivity) (pow_pos hX _)).mpr
  simp only [one_mul]
  calc
    (bad.card : ℝ) * (Fintype.card X : ℝ) ^ (Fintype.card ι * j) ≤
        ((Fintype.card α : ℝ) *
          (Fintype.card X : ℝ) ^ (Fintype.card ι * (k - j))) *
            (Fintype.card X : ℝ) ^ (Fintype.card ι * j) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = (Fintype.card α : ℝ) * (Fintype.card X : ℝ) ^ (Fintype.card ι * k) := by
      rw [mul_assoc, ← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hj]

theorem unit_equation_event_probability_le {α ι X : Type*}
    [Fintype α] [Nonempty α] [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X]
    {B j k : ℕ} (hB : 1 < B) (hj : j ≤ k)
    (digit : ι → Fin k → X → Fin B)
    (hinj : ∀ i v, Function.Injective (digit i v))
    (pivot : α → (ZMod (B ^ j))ˣ) (rhs : α → ι → ZMod (B ^ j))
    (bad : Finset (α × (ι → Fin k → X)))
    (hbad : ∀ z ∈ bad, ∀ i,
      (pivot z.1 : ZMod (B ^ j)) *
        ((∑ v : Fin k, (digit i v (z.2 i v)).val * B ^ v.val : ℕ) : ZMod (B ^ j)) =
          rhs z.1 i) :
    (bad.card : ℝ) / Fintype.card (α × (ι → Fin k → X)) ≤
      1 / (Fintype.card X : ℝ) ^ (Fintype.card ι * j) := by
  apply residue_event_probability_le hB hj digit hinj
    (fun a i => ((↑((pivot a)⁻¹) : ZMod (B ^ j)) * rhs a i).val) bad
  intro z hz i
  have heq :
      ((∑ v : Fin k, (digit i v (z.2 i v)).val * B ^ v.val : ℕ) : ZMod (B ^ j)) =
        (↑((pivot z.1)⁻¹) : ZMod (B ^ j)) * rhs z.1 i := by
    calc
      _ = (↑((pivot z.1)⁻¹) : ZMod (B ^ j)) *
          ((pivot z.1 : ZMod (B ^ j)) *
            ((∑ v : Fin k, (digit i v (z.2 i v)).val * B ^ v.val : ℕ) : ZMod (B ^ j))) := by
        simp
      _ = _ := by rw [hbad z hz i]
  simpa only [ZMod.val_natCast] using congrArg ZMod.val heq

theorem conditional_divisor_moment_le_two {α ι X : Type*}
    [Fintype α] [Nonempty α] [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X]
    {B k : ℕ} (hB : 1 < B)
    (digit : ι → Fin k → X → Fin B)
    (hinj : ∀ i v, Function.Injective (digit i v))
    (b : (α × (ι → Fin k → X)) → ℕ) (hb : ∀ z, b z ≤ k)
    (hconstraints : ∀ j, 1 ≤ j → j ≤ k →
      ∃ pivot : α → (ZMod (B ^ j))ˣ, ∃ rhs : α → ι → ZMod (B ^ j),
        ∀ z, j ≤ b z → ∀ i,
          (pivot z.1 : ZMod (B ^ j)) *
            ((∑ v : Fin k, (digit i v (z.2 i v)).val * B ^ v.val : ℕ) : ZMod (B ^ j)) =
              rhs z.1 i)
    (hsmall : (B : ℝ) * (1 / (Fintype.card X : ℝ)) ^ Fintype.card ι ≤ 1 / 2) :
    (∑ z : α × (ι → Fin k → X),
      (1 / (Fintype.card (α × (ι → Fin k → X)) : ℝ)) * (B : ℝ) ^ b z) ≤ 2 := by
  classical
  have hcard : (0 : ℝ) < Fintype.card (α × (ι → Fin k → X)) := by
    exact_mod_cast Fintype.card_pos
  apply DivisorMoment.normalized_power_moment_le_two
    (fun _ : α × (ι → Fin k → X) => 1 / (Fintype.card (α × (ι → Fin k → X)) : ℝ))
    b (B : ℝ) ((1 / (Fintype.card X : ℝ)) ^ Fintype.card ι) k
  · intro z
    positivity
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel hcard.ne'
  · positivity
  · positivity
  · exact hb
  · intro j hjpos hj
    obtain ⟨pivot, rhs, hequations⟩ := hconstraints j hjpos hj
    let bad : Finset (α × (ι → Fin k → X)) := Finset.univ.filter (fun z => j ≤ b z)
    have hprob := unit_equation_event_probability_le hB hj digit hinj pivot rhs bad
      (by intro z hz; exact hequations z (Finset.mem_filter.mp hz).2)
    have hsum :
        (∑ z : α × (ι → Fin k → X),
          if j ≤ b z then 1 / (Fintype.card (α × (ι → Fin k → X)) : ℝ) else 0) =
        (bad.card : ℝ) / Fintype.card (α × (ι → Fin k → X)) := by
      rw [← Finset.sum_filter]
      simp [bad, div_eq_mul_inv]
    rw [hsum]
    simpa only [← pow_mul, one_div_pow] using hprob
  · exact hsmall

end Problem355.ConditionalDigits

end OAI
end

section
-- module Solutions.OAIQW_Problem355.RankOneMinors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.UnitPivot

variable {R : Type*} [CommRing R]
variable {m n : Type*}

theorem entry_eq_of_pivot_minor (A : Matrix m n R) (p : m) (q : n)
    (u : Rˣ) (hp : A p q = (u : R)) (i : m) (j : n)
    (hminor : A p q * A i j = A i q * A p j) :
    A i j = A i q * (↑(u⁻¹) : R) * A p j := by
  calc
    A i j = (↑(u⁻¹) : R) * ((u : R) * A i j) := by simp
    _ = (↑(u⁻¹) : R) * (A i q * A p j) := by rw [← hp, hminor]
    _ = A i q * (↑(u⁻¹) : R) * A p j := by ring

theorem minorsVanish_iff_pivot (A : Matrix m n R) (p : m) (q : n)
    (u : Rˣ) (hp : A p q = (u : R)) :
    MinorsVanish A ↔ ∀ i j, A p q * A i j = A i q * A p j := by
  constructor
  · intro h i j
    simpa [mul_comm] using h p i q j
  · intro h i k j l
    rw [entry_eq_of_pivot_minor A p q u hp i j (h i j),
      entry_eq_of_pivot_minor A p q u hp k l (h k l),
      entry_eq_of_pivot_minor A p q u hp i l (h i l),
      entry_eq_of_pivot_minor A p q u hp k j (h k j)]
    ring

end Problem355.UnitPivot

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ConditionalMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.ConditionalMatrix

open scoped BigOperators

theorem moment_le_two {X : Type*} [Fintype X] [Nonempty X]
    {B k : ℕ} (hB : B.Prime) (hk : 0 < k)
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (hinj : ∀ a c v, Function.Injective (digit a c v))
    (hpos : ∀ a c v x, 0 < (digit a c v x).val)
    (b : Draw X k → ℕ) (hb : ∀ z, b z ≤ k)
    (hminor : ∀ j, 1 ≤ j → j ≤ k → ∀ z, j ≤ b z →
      UnitPivot.MinorsVanish (residueMatrix digit z j))
    (hsmall : (B : ℝ) * (1 / (Fintype.card X : ℝ)) ^ 4 ≤ 1 / 2) :
    (∑ z : Draw X k, (1 / (Fintype.card (Draw X k) : ℝ)) * (B : ℝ) ^ b z) ≤ 2 := by
  classical
  apply ConditionalDigits.conditional_divisor_moment_le_two hB.one_lt
    (fun i v x => digit i.1.succ i.2.succ v x)
    (fun i v => hinj i.1.succ i.2.succ v) b hb
  · intro j hjpos hj
    let row : Header X k → Fin 3 → ℕ :=
      fun a c => ∑ v : Fin k, (digit 0 c v (a.1 c v)).val * B ^ v.val
    let col : Header X k → Fin 2 → ℕ :=
      fun a i => ∑ v : Fin k, (digit i.succ 0 v (a.2 i v)).val * B ^ v.val
    have hunit (a : Header X k) : IsUnit ((row a 0 : ℕ) : ZMod (B ^ j)) :=
      encoded_isUnit hB hk hjpos (fun v => digit 0 0 v (a.1 0 v))
        (fun v => hpos 0 0 v (a.1 0 v))
    let pivot : Header X k → (ZMod (B ^ j))ˣ := fun a => (hunit a).unit
    refine ⟨pivot, fun a i =>
      (col a i.1 : ZMod (B ^ j)) * (row a i.2.succ : ZMod (B ^ j)), ?_⟩
    intro z hz i
    have hpivot : (pivot z.1 : ZMod (B ^ j)) = (row z.1 0 : ZMod (B ^ j)) :=
      (hunit z.1).unit_spec
    rw [hpivot]
    have h := hminor j hjpos hj z hz 0 i.1.succ 0 i.2.succ
    change (row z.1 0 : ZMod (B ^ j)) *
        ((∑ v : Fin k, (digit i.1.succ i.2.succ v (z.2 i v)).val * B ^ v.val : ℕ) : ZMod (B ^ j)) =
      (row z.1 i.2.succ : ZMod (B ^ j)) * (col z.1 i.1 : ZMod (B ^ j)) at h
    exact h.trans (mul_comm _ _)
  · simpa using hsmall

theorem array_moment_le_two {X : Type*} [Fintype X] [Nonempty X]
    {B k : ℕ} (hB : B.Prime) (hk : 0 < k)
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (hinj : ∀ a c v, Function.Injective (digit a c v))
    (hpos : ∀ a c v x, 0 < (digit a c v x).val)
    (b : (Fin 3 → Fin 3 → Fin k → X) → ℕ) (hb : ∀ f, b f ≤ k)
    (hminor : ∀ j, 1 ≤ j → j ≤ k → ∀ f, j ≤ b f →
      UnitPivot.MinorsVanish (arrayMatrix digit f j))
    (hsmall : (B : ℝ) * (1 / (Fintype.card X : ℝ)) ^ 4 ≤ 1 / 2) :
    (∑ f : Fin 3 → Fin 3 → Fin k → X,
      (1 / (Fintype.card (Fin 3 → Fin 3 → Fin k → X) : ℝ)) * (B : ℝ) ^ b f) ≤ 2 := by
  have h := moment_le_two hB hk digit hinj hpos (fun z => b (drawEquiv z))
    (fun z => hb (drawEquiv z))
    (fun j hj hk z hz => hminor j hj hk (drawEquiv z) hz) hsmall
  have hcard := Fintype.card_congr (drawEquiv (X := X) (k := k))
  rw [hcard] at h
  have hsum := (drawEquiv (X := X) (k := k)).sum_comp
    (fun f => (1 / (Fintype.card (Fin 3 → Fin 3 → Fin k → X) : ℝ)) * (B : ℝ) ^ b f)
  rw [← hsum]
  exact h

lemma prescribedDigit_injective {r m B k : ℕ} [NeZero r] (hbound : r * m < B)
    (residue : Fin 3 → Fin 3 → Fin k → ZMod r) (a c : Fin 3) (v : Fin k) :
    Function.Injective (prescribedDigit hbound residue a c v) := by
  intro x y hxy
  apply (DigitUnits.digitFiberEquiv (residue a c v) m).injective
  apply Subtype.ext
  exact congrArg Fin.val hxy

lemma prescribedDigit_residue {r m B k : ℕ} [NeZero r] (hbound : r * m < B)
    (residue : Fin 3 → Fin 3 → Fin k → ZMod r) (a c : Fin 3) (v : Fin k) (x : Fin m) :
    ((prescribedDigit hbound residue a c v x).val : ZMod r) = residue a c v :=
  (DigitUnits.digitFiberEquiv_bounds (residue a c v) m x).2.2

end Problem355.ConditionalMatrix

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ConditionalSamples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.ConditionalSamples

noncomputable section

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

lemma sum_productWeight (μ : α → ℝ) (hμ : ∑ a, μ a = 1) :
    ∑ x : ι → α, productWeight μ x = 1 := by
  classical
  have h := (Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset α))
    (fun _ a => μ a)).symm
  simpa [productWeight, hμ] using h

omit [Fintype α] [DecidableEq ι] in
lemma productWeight_nonneg (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (x : ι → α) :
    0 ≤ productWeight μ x :=
  Finset.prod_nonneg fun i _ => hμ (x i)

omit [Fintype α] [DecidableEq ι] in
lemma productWeight_split (μ : α → ℝ) (p : ι → Prop) [DecidablePred p]
    (x : ι → α) : productWeight μ x =
      productWeight μ (fun i : {i // p i} => x i) *
        productWeight μ (fun i : {i // ¬p i} => x i) := by
  exact (Fintype.prod_subtype_mul_prod_subtype p (fun i => μ (x i))).symm

lemma sum_productWeight_restrict (μ : α → ℝ) (hμ : ∑ a, μ a = 1)
    (p : ι → Prop) [DecidablePred p] (F : ({i // p i} → α) → ℝ) :
    (∑ x : ι → α, productWeight μ x * F (fun i => x i)) =
      ∑ y : {i // p i} → α, productWeight μ y * F y := by
  classical
  let e := Equiv.piEquivPiSubtypeProd p (fun _ : ι => α)
  calc
    (∑ x : ι → α, productWeight μ x * F (fun i => x i)) =
        ∑ yz : ({i // p i} → α) × ({i // ¬p i} → α),
          (productWeight μ yz.1 * productWeight μ yz.2) * F yz.1 := by
      apply Fintype.sum_equiv e
      intro x
      rw [productWeight_split μ p x]
      rfl
    _ = ∑ y : {i // p i} → α, productWeight μ y * F y := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro y _
      calc
        (∑ z : {i // ¬p i} → α,
            (productWeight μ y * productWeight μ z) * F y) =
            ∑ z : {i // ¬p i} → α,
              (productWeight μ y * F y) * productWeight μ z := by
          apply Finset.sum_congr rfl
          intro z _
          ring
        _ = productWeight μ y * F y := by
          rw [← Finset.mul_sum, sum_productWeight μ hμ, mul_one]

lemma sum_productWeight_comp {κ : Type*} [Fintype κ] [DecidableEq κ]
    (μ : α → ℝ) (hμ : ∑ a, μ a = 1) (e : κ → ι)
    (he : Function.Injective e) (F : (κ → α) → ℝ) :
    (∑ x : ι → α, productWeight μ x * F (x ∘ e)) =
      ∑ y : κ → α, productWeight μ y * F y := by
  classical
  let : Fintype (Set.range e) := Subtype.fintype _
  let er : κ ≃ Set.range e := Equiv.ofInjective e he
  let ar := Equiv.piCongrLeft (fun _ : Set.range e => α) er
  have hrestrict := sum_productWeight_restrict μ hμ
    (fun i => i ∈ Set.range e) (fun y => F (fun j => y (er j)))
  change (∑ x : ι → α, productWeight μ x * F (x ∘ e)) = _ at hrestrict
  rw [hrestrict]
  apply Fintype.sum_equiv ar.symm
  intro y
  have hprod : productWeight μ y = productWeight μ (ar.symm y) := by
    exact (er.prod_comp (fun i => μ (y i))).symm
  rw [hprod]
  rfl

variable {Θ : Type*}

omit [Fintype α] [DecidableEq ι] in
lemma sharedWeight_nonneg (ρ : Θ → ℝ) (μ : Θ → α → ℝ)
    (hρ : ∀ θ, 0 ≤ ρ θ) (hμ : ∀ θ a, 0 ≤ μ θ a) (z : Θ × (ι → α)) :
    0 ≤ sharedWeight ρ μ z :=
  mul_nonneg (hρ z.1) (productWeight_nonneg (μ z.1) (hμ z.1) z.2)

lemma sum_sharedWeight [Fintype Θ] (ρ : Θ → ℝ) (μ : Θ → α → ℝ)
    (hρ : ∑ θ, ρ θ = 1) (hμ : ∀ θ, ∑ a, μ θ a = 1) :
    ∑ z : Θ × (ι → α), sharedWeight ρ μ z = 1 := by
  classical
  simp only [sharedWeight, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, sum_productWeight _ (hμ _), mul_one]
  exact hρ

lemma shared_marginal [Fintype Θ] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Θ → ℝ) (μ : Θ → α → ℝ) (hμ : ∀ θ, ∑ a, μ θ a = 1)
    (e : κ → ι) (he : Function.Injective e) (F : Θ → (κ → α) → ℝ) :
    (∑ z : Θ × (ι → α), sharedWeight ρ μ z * F z.1 (z.2 ∘ e)) =
      ∑ z : Θ × (κ → α), sharedWeight ρ μ z * F z.1 z.2 := by
  classical
  simp only [sharedWeight, Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ _
  rw [sum_productWeight_comp (μ θ) (hμ θ) e he (F θ)]

lemma shared_pair_marginal [Fintype Θ]
    (ρ : Θ → ℝ) (μ : Θ → α → ℝ) (hμ : ∀ θ, ∑ a, μ θ a = 1)
    {i j : ι} (hij : i ≠ j) (F : Θ → α → α → ℝ) :
    (∑ z : Θ × (ι → α), sharedWeight ρ μ z * F z.1 (z.2 i) (z.2 j)) =
      ∑ z : Θ × (Fin 2 → α), sharedWeight ρ μ z * F z.1 (z.2 0) (z.2 1) := by
  have he : Function.Injective (![i, j] : Fin 2 → ι) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  simpa using shared_marginal ρ μ hμ (![i, j] : Fin 2 → ι) he
    (fun θ x => F θ (x 0) (x 1))

lemma shared_triple_marginal [Fintype Θ]
    (ρ : Θ → ℝ) (μ : Θ → α → ℝ) (hμ : ∀ θ, ∑ a, μ θ a = 1)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (F : Θ → α → α → α → ℝ) :
    (∑ z : Θ × (ι → α), sharedWeight ρ μ z * F z.1 (z.2 i) (z.2 j) (z.2 k)) =
      ∑ z : Θ × (Fin 3 → α),
        sharedWeight ρ μ z * F z.1 (z.2 0) (z.2 1) (z.2 2) := by
  have he : Function.Injective (![i, j, k] : Fin 3 → ι) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  simpa using shared_marginal ρ μ hμ (![i, j, k] : Fin 3 → ι) he
    (fun θ x => F θ (x 0) (x 1) (x 2))

end
end Problem355.ConditionalSamples

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DigitColumnLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.DigitColumnLaw

noncomputable section
open scoped BigOperators

lemma productWeight_uniform {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (s : ι → α) :
    ConditionalSamples.productWeight (uniformWeight α) s = uniformWeight (ι → α) s := by
  simp [ConditionalSamples.productWeight, uniformWeight]

theorem expectation_triple {Λ X : Type*} [Fintype Λ] [Fintype X] {k : ℕ}
    (F : (Fin 3 → Λ) → Array X k → ℝ) :
    (∑ s : Fin 3 → Latent Λ X k,
      ConditionalSamples.productWeight (uniformWeight (Latent Λ X k)) s *
        F (tripleEquiv s).1 (tripleEquiv s).2) =
      ∑ labels : Fin 3 → Λ, uniformWeight (Fin 3 → Λ) labels *
        ∑ f : Array X k, uniformWeight (Array X k) f * F labels f := by
  simp_rw [productWeight_uniform]
  have hcard := Fintype.card_congr (tripleEquiv (Λ := Λ) (X := X) (k := k))
  have hsum := (tripleEquiv (Λ := Λ) (X := X) (k := k)).sum_comp
    (fun t => (1 / (Fintype.card (Fin 3 → Latent Λ X k) : ℝ)) * F t.1 t.2)
  change (∑ s : Fin 3 → Latent Λ X k,
    (1 / (Fintype.card (Fin 3 → Latent Λ X k) : ℝ)) *
      F (tripleEquiv s).1 (tripleEquiv s).2) = _
  rw [hsum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro labels _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [hcard]
  simp only [uniformWeight, Fintype.card_prod, Nat.cast_mul, one_div, mul_inv_rev]
  ring

end
end Problem355.DigitColumnLaw

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DigitObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.DigitEncoding

open Finset

theorem no_small_representative {h τ s x : ℤ}
    (hh : 0 < h) (hτ : 2 * τ < h)
    (hs : 2 * |s| < h) (hsτ : τ < |s|)
    (hx : x ≡ s [ZMOD h]) : τ < |x| := by
  by_contra hn
  have hxτ : |x| ≤ τ := le_of_not_gt hn
  obtain ⟨m, hm⟩ := Int.modEq_iff_dvd.mp hx
  by_cases hm0 : m = 0
  · subst m
    simp only [mul_zero, sub_eq_zero] at hm
    subst s
    omega
  · have hm1 : 1 ≤ |m| := Int.one_le_abs hm0
    have htri : |s - x| ≤ |s| + |x| := abs_sub s x
    rw [hm, abs_mul, abs_of_pos hh] at htri
    have hsmall : 2 * |x| < h :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hxτ (by omega)) hτ
    nlinarith only [hsmall, hs, htri, hm1, hh]

theorem partial_sum_bound (B : ℤ) (hB : 2 ≤ B) (E : ℕ → ℤ)
    (k : ℕ) (hE : ∀ i < k, 50 * |E i| ≤ 3 * (B - 1)) :
    50 * |∑ i ∈ range k, E i * B ^ i| ≤ 3 * (B ^ k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (fun i hi => hE i (Nat.lt_succ_of_lt hi))
    have hk := hE k (Nat.lt_succ_self k)
    have hpow : 0 ≤ B ^ k := pow_nonneg (by omega) k
    have htri := abs_add_le (∑ i ∈ range k, E i * B ^ i) (E k * B ^ k)
    rw [abs_mul, abs_of_nonneg hpow] at htri
    rw [sum_range_succ, pow_succ]
    nlinarith

theorem distinguished_digit_bound (B : ℤ) (hB : 2 ≤ B) (E : ℕ → ℤ)
    (k : ℕ) (hE : ∀ i < k, 50 * |E i| ≤ 3 * (B - 1))
    (hk : E k ≠ 0) :
    47 * B ^ k + 3 ≤ 50 * |∑ i ∈ range (k + 1), E i * B ^ i| := by
  have hprev := partial_sum_bound B hB E k hE
  have hpow : 0 ≤ B ^ k := pow_nonneg (by omega) k
  have hk1 : 1 ≤ |E k| := Int.one_le_abs hk
  have htri := abs_sub (∑ i ∈ range (k + 1), E i * B ^ i)
    (∑ i ∈ range k, E i * B ^ i)
  rw [sum_range_succ, add_sub_cancel_left, abs_mul, abs_of_nonneg hpow] at htri
  rw [sum_range_succ]
  nlinarith

theorem digit_obstruction (B : ℤ) (hB : 2 ≤ B) (E : ℕ → ℤ)
    (k : ℕ) (hE : ∀ i < k + 1, 50 * |E i| ≤ 3 * (B - 1))
    (hk : E k ≠ 0) {x : ℤ}
    (hx : x ≡ ∑ i ∈ range (k + 1), E i * B ^ i [ZMOD B ^ (k + 1)]) :
    B ^ k / 2 < |x| := by
  have hfull := partial_sum_bound B hB E (k + 1) hE
  have hlead := distinguished_digit_bound B hB E k
    (fun i hi => hE i (Nat.lt_succ_of_lt hi)) hk
  have hp : 0 < B ^ k := pow_pos (by omega) k
  have hh : 0 < B ^ (k + 1) := pow_pos (by omega) (k + 1)
  have hdiv : 2 * (B ^ k / 2) ≤ B ^ k := by omega
  have hsmall : 2 * (B ^ k / 2) < B ^ (k + 1) := by
    rw [pow_succ]
    nlinarith
  apply no_small_representative hh hsmall _ _ hx
  · nlinarith
  · nlinarith

theorem sum_modEq_prefix (B : ℤ) (E : ℕ → ℤ) (k m : ℕ) (hkm : k ≤ m) :
    (∑ i ∈ range m, E i * B ^ i) ≡
      (∑ i ∈ range k, E i * B ^ i) [ZMOD B ^ k] := by
  induction m, hkm using Nat.le_induction with
  | base => exact Int.ModEq.refl _
  | succ m hkm ih =>
    rw [sum_range_succ]
    have hdvd : B ^ k ∣ E m * B ^ m :=
      dvd_mul_of_dvd_right (pow_dvd_pow B hkm) _
    simpa using ih.add hdvd.modEq_zero_int

theorem polynomial_eval_modEq_prefix (p : Polynomial ℤ) (B : ℤ) (k : ℕ) :
    p.eval B ≡ (∑ i ∈ range k, p.coeff i * B ^ i) [ZMOD B ^ k] := by
  rw [Polynomial.eval_eq_sum_range' (n := max (p.natDegree + 1) k)
    (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _))]
  exact sum_modEq_prefix B p.coeff k _ (le_max_right _ _)

theorem polynomial_obstruction (p : Polynomial ℤ) (B : ℤ) (hB : 2 ≤ B)
    (k : ℕ) (hE : ∀ i ≤ k, 50 * |p.coeff i| ≤ 3 * (B - 1))
    (hk : p.coeff k ≠ 0) {x : ℤ}
    (hx : x ≡ p.eval B [ZMOD B ^ (k + 1)]) : B ^ k / 2 < |x| := by
  exact digit_obstruction B hB p.coeff k
    (fun i hi => hE i (Nat.lt_succ_iff.mp hi)) hk
    (hx.trans (polynomial_eval_modEq_prefix p B (k + 1)))

theorem coefficient_bound_normalized {B L k e : ℤ}
    (hbase : 100 * k ^ 2 * L ^ 3 < B)
    (he : |e| ≤ 6 * k ^ 2 * L ^ 3) :
    50 * |e| ≤ 3 * (B - 1) := by
  have hbase' : 100 * k ^ 2 * L ^ 3 ≤ B - 1 := by omega
  nlinarith

theorem determinant_modEq_of_specialLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ℕ) (G : Matrix.SpecialLinearGroup ι (ZMod h))
    (A C : Matrix ι ι ℤ)
    (hAC : A.map (Int.castRingHom (ZMod h)) =
      (G : Matrix ι ι (ZMod h)) * C.map (Int.castRingHom (ZMod h))) :
    A.det ≡ C.det [ZMOD h] := by
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_det, Int.cast_det]
  change (A.map (Int.castRingHom (ZMod h))).det =
    (C.map (Int.castRingHom (ZMod h))).det
  rw [hAC, Matrix.det_mul, G.det_coe, one_mul]

end Problem355.DigitEncoding

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DigitEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.DigitEncoding

theorem matched_indices {T a b c : ℕ} (ha : a < T) (hc : c < T)
    (h : a + T * b = (T + 1) * c) : a = c ∧ b = c := by
  have h' : a + T * b = c + T * c := by nlinarith
  have hmod := congrArg (fun x : ℕ => x % T) h'
  have hac : a = c := by
    simpa [Nat.add_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] using hmod
  subst a
  constructor
  · rfl
  · have hT : 0 < T := Nat.zero_lt_of_lt hc
    nlinarith

end Problem355.DigitEncoding

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DesignatedCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.DesignatedCoefficient

open Polynomial

theorem position_sum_matching (T : ℕ) (v : Fin 3 → Fin T) :
    position T 0 (v 0) + position T 1 (v 1) + position T 2 (v 2) = T ^ 2 ↔
      v 0 = v 1 ∧ v 1 = v 2 := by
  have hle : (T + 1) * (v 2).val ≤ T ^ 2 := by
    have hv : (v 2).val + 1 ≤ T := (v 2).isLt
    have hh := Nat.mul_le_mul_left (T + 1) hv
    nlinarith
  have hsub := Nat.sub_add_cancel hle
  change (v 0).val + T * (v 1).val + (T ^ 2 - (T + 1) * (v 2).val) = T ^ 2 ↔
    v 0 = v 1 ∧ v 1 = v 2
  constructor
  · intro h
    have hm := DigitEncoding.matched_indices (v 0).isLt (v 2).isLt
      (show (v 0).val + T * (v 1).val = (T + 1) * (v 2).val by omega)
    exact ⟨Fin.ext (hm.1.trans hm.2.symm), Fin.ext hm.2⟩
  · rintro ⟨h01, h12⟩
    have hv0 : (v 0).val = (v 2).val := congrArg Fin.val (h01.trans h12)
    have hv1 : (v 1).val = (v 2).val := congrArg Fin.val h12
    rw [hv0, hv1]
    nlinarith

theorem sum_diagonal {R : Type*} [AddCommMonoid R] (T : ℕ)
    (F : (Fin 3 → Fin T) → R) :
    (∑ v : Fin 3 → Fin T, if v 0 = v 1 ∧ v 1 = v 2 then F v else 0) =
      ∑ a : Fin T, F (fun _ => a) := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun a _ => fun _ : Fin 3 => a)
  · intro a ha
    simp
  · intro a ha b hb hab
    exact congrFun hab 0
  · intro v hv
    rcases Finset.mem_filter.mp hv with ⟨_, h01, h12⟩
    refine ⟨v 0, Finset.mem_univ _, ?_⟩
    funext i
    fin_cases i <;> simp_all
  · intro a ha
    rfl

theorem det_monomial_rows {R : Type*} [CommRing R]
    (v : Fin 3 → ℕ) (A : Matrix (Fin 3) (Fin 3) R) :
    Matrix.det (Matrix.of (fun i j => monomial (v i) (A i j))) =
      monomial (v 0 + v 1 + v 2) A.det := by
  simp only [Matrix.det_fin_three, Matrix.of_apply, Polynomial.monomial_mul_monomial, map_add, map_sub]

theorem designated_coefficient {R : Type*} [CommRing R] (T : ℕ)
    (f : Fin 3 → Fin T → Fin 3 → R) :
    (Matrix.det (polynomialMatrix T f)).coeff (T ^ 2) =
      ∑ a : Fin T, Matrix.det (Matrix.of (fun i j => f i a j)) := by
  classical
  have hm := (Matrix.detRowAlternating (n := Fin 3) (R := R[X])).toMultilinearMap.map_sum_finset
    (fun i (a : Fin T) j => monomial (position T i a) (f i a j))
    (fun _ => Finset.univ)
  change Matrix.det (Matrix.of (fun i => ∑ a : Fin T, fun j =>
    monomial (position T i a) (f i a j))) = _ at hm
  have hrows : (fun i => ∑ a : Fin T, fun j =>
      monomial (position T i a) (f i a j)) = polynomialMatrix T f := by
    funext i j
    simp only [Finset.sum_apply, polynomialMatrix]
  rw [hrows, Fintype.piFinset_univ] at hm
  change (polynomialMatrix T f).det = _ at hm
  rw [hm, Polynomial.finsetSum_coeff]
  change (∑ v : Fin 3 → Fin T,
    (Matrix.det (Matrix.of (fun i j => monomial (position T i (v i)) (f i (v i) j)))).coeff
      (T ^ 2)) = _
  calc
    _ = ∑ v : Fin 3 → Fin T,
        if v 0 = v 1 ∧ v 1 = v 2 then Matrix.det (Matrix.of (fun i j => f i (v i) j)) else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      have hdet := det_monomial_rows (fun i => position T i (v i))
        (Matrix.of (fun i j => f i (v i) j))
      simp only [Matrix.of_apply] at hdet
      rw [hdet, Polynomial.coeff_monomial]
      by_cases h : v 0 = v 1 ∧ v 1 = v 2
      · have hp := (position_sum_matching T v).mpr h
        rw [ite_eq_left hp, ite_eq_left h]
      · have hp : ¬ (position T 0 (v 0) + position T 1 (v 1) +
            position T 2 (v 2) = T ^ 2) := fun hp => h ((position_sum_matching T v).mp hp)
        rw [ite_eq_right hp, ite_eq_right h]
    _ = _ := sum_diagonal T (fun v => Matrix.det (Matrix.of (fun i j => f i (v i) j)))

theorem map_designated_coefficient {R : Type*} [CommRing R] (φ : ℤ →+* R)
    (T : ℕ) (P : Matrix (Fin 3) (Fin 3) ℤ[X])
    (f : Fin 3 → Fin T → Fin 3 → R)
    (hmap : ∀ i j, (P i j).map φ = polynomialMatrix T f i j) :
    φ (P.det.coeff (T ^ 2)) = ∑ a : Fin T, Matrix.det (Matrix.of (fun i j => f i a j)) := by
  have hm : P.det.map φ = Matrix.det (Matrix.of (fun i j => (P i j).map φ)) :=
    (Polynomial.mapRingHom φ).map_det P
  have hmatrix : (fun i j => (P i j).map φ) = polynomialMatrix T f := by
    funext i j
    exact hmap i j
  rw [hmatrix] at hm
  rw [← Polynomial.coeff_map, hm]
  exact designated_coefficient T f

theorem designated_coefficient_ne_zero {R : Type*} [CommRing R] (φ : ℤ →+* R)
    (T : ℕ) (P : Matrix (Fin 3) (Fin 3) ℤ[X])
    (f : Fin 3 → Fin T → Fin 3 → R)
    (hmap : ∀ i j, (P i j).map φ = polynomialMatrix T f i j)
    (hne : (∑ a : Fin T, Matrix.det (Matrix.of (fun i j => f i a j))) ≠ 0) :
    P.det.coeff (T ^ 2) ≠ 0 := by
  intro hz
  apply hne
  rw [← map_designated_coefficient φ T P f hmap, hz, map_zero]

end Problem355.DesignatedCoefficient

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DeterminantCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.DigitCoefficients
noncomputable section
open scoped BigOperators
open Polynomial

lemma coeff_digitPolynomial (k u : ℕ) (a : ℕ → ℤ) :
    (digitPolynomial k a).coeff u = if u < k then a u else 0 := by
  classical
  simp [digitPolynomial, Polynomial.coeff_monomial]

lemma abs_coeff_digitPolynomial_le (k : ℕ) (a : ℕ → ℤ) (L : ℤ)
    (hL : 0 ≤ L) (ha : ∀ i < k, |a i| ≤ L) (u : ℕ) :
    |(digitPolynomial k a).coeff u| ≤ L := by
  rw [coeff_digitPolynomial]
  split_ifs with h
  · exact ha u h
  · simpa using hL

lemma abs_coeff_digitPolynomial_mul_le (k : ℕ) (a : ℕ → ℤ)
    (q : ℤ[X]) (L M : ℤ) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (ha : ∀ i < k, |a i| ≤ L) (hq : ∀ i, |q.coeff i| ≤ M) (u : ℕ) :
    |(digitPolynomial k a * q).coeff u| ≤ (k : ℤ) * L * M := by
  classical
  unfold digitPolynomial
  rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
  calc
    |∑ i ∈ Finset.range k, ((monomial i (a i)) * q).coeff u| ≤
        ∑ i ∈ Finset.range k, |((monomial i (a i)) * q).coeff u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range k, L * M := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
      split_ifs with h
      · rw [abs_mul]
        exact mul_le_mul (ha i (Finset.mem_range.mp hi)) (hq (u-i))
          (abs_nonneg _) hL
      · simp only [mul_zero, abs_zero]
        exact mul_nonneg hL hM
    _ = (k : ℤ) * L * M := by simp; ring

lemma abs_coeff_triple_digitPolynomial_le (k : ℕ) (a b c : ℕ → ℤ)
    (L : ℤ) (hL : 0 ≤ L)
    (ha : ∀ i < k, |a i| ≤ L) (hb : ∀ i < k, |b i| ≤ L)
    (hc : ∀ i < k, |c i| ≤ L) (u : ℕ) :
    |(digitPolynomial k a * digitPolynomial k b * digitPolynomial k c).coeff u|
      ≤ (k : ℤ)^2 * L^3 := by
  rw [mul_assoc]
  have hbc : ∀ i, |(digitPolynomial k b * digitPolynomial k c).coeff i|
      ≤ (k : ℤ) * L * L :=
    abs_coeff_digitPolynomial_mul_le k b (digitPolynomial k c) L L hL hL hb
      (abs_coeff_digitPolynomial_le k c L hL hc)
  have h := abs_coeff_digitPolynomial_mul_le k a
    (digitPolynomial k b * digitPolynomial k c) L ((k : ℤ) * L * L)
    hL (by positivity) ha hbc u
  convert h using 1; ring

theorem abs_coeff_determinantPolynomial_le (k : ℕ)
    (d : Fin 3 → Fin 3 → ℕ → ℤ) (L : ℤ) (hL : 0 ≤ L)
    (hd : ∀ i j v, v < k → |d i j v| ≤ L) (u : ℕ) :
    |(determinantPolynomial k d).coeff u| ≤ 6 * (k : ℤ)^2 * L^3 := by
  have ht (i j m n s t : Fin 3) := abs_le.mp
    (abs_coeff_triple_digitPolynomial_le k (d i j) (d m n) (d s t)
      L hL (hd i j) (hd m n) (hd s t) u)
  have h₁ := ht 0 0 1 1 2 2
  have h₂ := ht 0 0 1 2 2 1
  have h₃ := ht 0 1 1 0 2 2
  have h₄ := ht 0 1 1 2 2 0
  have h₅ := ht 0 2 1 0 2 1
  have h₆ := ht 0 2 1 1 2 0
  unfold determinantPolynomial
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub]
  apply abs_le.mpr
  constructor <;> nlinarith

lemma eval_digitPolynomial (k : ℕ) (a : ℕ → ℤ) (B : ℤ) :
    (digitPolynomial k a).eval B = ∑ i ∈ Finset.range k, a i * B^i := by
  simp [digitPolynomial, Polynomial.eval_finsetSum]

lemma eval_determinantPolynomial (k : ℕ) (d : Fin 3 → Fin 3 → ℕ → ℤ) (B : ℤ) :
    (determinantPolynomial k d).eval B =
      Matrix.det (Matrix.of (fun i j => ∑ v ∈ Finset.range k, d i j v * B^v)) := by
  simp only [determinantPolynomial, Matrix.det_fin_three, Matrix.of_apply, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_mul, eval_digitPolynomial]

end
end Problem355.DigitCoefficients

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PrescribedDigits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.DesignatedCoefficient
open Polynomial

lemma last_position_product_le (T : ℕ) (a : Fin T) :
    (T + 1) * a.val ≤ T ^ 2 := by
  have ha : a.val + 1 ≤ T := a.isLt
  have h := Nat.mul_le_mul_left (T + 1) ha
  nlinarith

lemma position_injective (T : ℕ) (i : Fin 3) :
    Function.Injective (position T i) := by
  intro a b hab
  apply Fin.ext
  have hT : 0 < T := Nat.zero_lt_of_lt a.isLt
  fin_cases i
  · exact hab
  · change T * a.val = T * b.val at hab
    nlinarith
  · change T ^ 2 - (T + 1) * a.val = T ^ 2 - (T + 1) * b.val at hab
    have ha := Nat.sub_add_cancel (last_position_product_le T a)
    have hb := Nat.sub_add_cancel (last_position_product_le T b)
    nlinarith

lemma position_lt (T : ℕ) (i : Fin 3) (a : Fin T) :
    position T i a < T ^ 2 + 1 := by
  have hT : 0 < T := Nat.zero_lt_of_lt a.isLt
  fin_cases i
  · change a.val < T ^ 2 + 1
    have ha := a.isLt
    nlinarith
  · change T * a.val < T ^ 2 + 1
    have ha := Nat.mul_lt_mul_of_pos_left a.isLt hT
    nlinarith
  · change T ^ 2 - (T + 1) * a.val < T ^ 2 + 1
    exact Nat.lt_succ_of_le (Nat.sub_le _ _)

theorem map_eq_polynomialMatrix_of_coefficients {R : Type*} [CommRing R]
    (φ : ℤ →+* R) (T : ℕ) (P : Matrix (Fin 3) (Fin 3) ℤ[X])
    (f : Fin 3 → Fin T → Fin 3 → R)
    (hdesignated : ∀ i j a, φ ((P i j).coeff (position T i a)) = f i a j)
    (hzero : ∀ i j n, (∀ a : Fin T, position T i a ≠ n) →
      φ ((P i j).coeff n) = 0) :
    ∀ i j, (P i j).map φ = polynomialMatrix T f i j := by
  classical
  intro i j
  ext n
  rw [Polynomial.coeff_map]
  change φ ((P i j).coeff n) =
    (∑ a : Fin T, monomial (position T i a) (f i a j)).coeff n
  rw [Polynomial.finsetSum_coeff]
  by_cases hn : ∃ a : Fin T, position T i a = n
  · obtain ⟨a, rfl⟩ := hn
    rw [hdesignated]
    symm
    rw [Finset.sum_eq_single a]
    · simp
    · intro b hb hba
      rw [Polynomial.coeff_monomial, ite_eq_right]
      exact fun h => hba (position_injective T i h)
    · simp
  · have hn' : ∀ a : Fin T, position T i a ≠ n := by simpa using hn
    rw [hzero i j n hn']
    symm
    apply Finset.sum_eq_zero
    intro a ha
    rw [Polynomial.coeff_monomial, ite_eq_right (hn' a)]

theorem digitPolynomial_map_eq {R : Type*} [CommRing R] (φ : ℤ →+* R)
    (T : ℕ) (d : Fin 3 → Fin 3 → ℕ → ℤ)
    (f : Fin 3 → Fin T → Fin 3 → R)
    (hdesignated : ∀ i j a, φ (d i j (position T i a)) = f i a j)
    (hzero : ∀ i j n, n < T ^ 2 + 1 →
      (∀ a : Fin T, position T i a ≠ n) → φ (d i j n) = 0) :
    ∀ i j, (DigitCoefficients.digitPolynomial (T ^ 2 + 1) (d i j)).map φ =
      polynomialMatrix T f i j := by
  apply map_eq_polynomialMatrix_of_coefficients φ T
    (fun i j => DigitCoefficients.digitPolynomial (T ^ 2 + 1) (d i j)) f
  · intro i j a
    rw [DigitCoefficients.coeff_digitPolynomial, ite_eq_left (position_lt T i a)]
    exact hdesignated i j a
  · intro i j n hn
    rw [DigitCoefficients.coeff_digitPolynomial]
    split_ifs with hnk
    · exact hzero i j n hnk hn
    · exact map_zero φ

theorem digit_det_designated_coefficient_ne_zero {R : Type*} [CommRing R]
    (φ : ℤ →+* R) (T : ℕ) (d : Fin 3 → Fin 3 → ℕ → ℤ)
    (f : Fin 3 → Fin T → Fin 3 → R)
    (hdesignated : ∀ i j a, φ (d i j (position T i a)) = f i a j)
    (hzero : ∀ i j n, n < T ^ 2 + 1 →
      (∀ a : Fin T, position T i a ≠ n) → φ (d i j n) = 0)
    (hne : (∑ a : Fin T, Matrix.det (fun i j => f i a j)) ≠ 0) :
    (DigitCoefficients.determinantPolynomial (T ^ 2 + 1) d).coeff (T ^ 2) ≠ 0 := by
  exact designated_coefficient_ne_zero φ T
    (fun i j => DigitCoefficients.digitPolynomial (T ^ 2 + 1) (d i j)) f
    (digitPolynomial_map_eq φ T d f hdesignated hzero) hne

end Problem355.DesignatedCoefficient

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.EncodedDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.EncodedDeterminant

open Polynomial DigitCoefficients DesignatedCoefficient DigitEncoding

theorem encoded_polynomial_obstruction {R : Type*} [CommRing R]
    (φ : ℤ →+* R) (T : ℕ) (B L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
    (hbase : 100 * ((T ^ 2 + 1 : ℕ) : ℤ) ^ 2 * L ^ 3 < B)
    (d : Fin 3 → Fin 3 → ℕ → ℤ) (f : Fin 3 → Fin T → Fin 3 → R)
    (hd : ∀ i j v, v < T ^ 2 + 1 → |d i j v| ≤ L)
    (hdesignated : ∀ i j a, φ (d i j (position T i a)) = f i a j)
    (hzero : ∀ i j n, n < T ^ 2 + 1 →
      (∀ a : Fin T, position T i a ≠ n) → φ (d i j n) = 0)
    (hne : (∑ a : Fin T, Matrix.det (fun i j => f i a j)) ≠ 0)
    {x : ℤ}
    (hx : x ≡ (determinantPolynomial (T ^ 2 + 1) d).eval B
      [ZMOD B ^ (T ^ 2 + 1)]) :
    B ^ (T ^ 2) / 2 < |x| := by
  apply polynomial_obstruction (determinantPolynomial (T ^ 2 + 1) d)
    B hB (T ^ 2) _ _ hx
  · intro n hn
    exact coefficient_bound_normalized hbase
      (abs_coeff_determinantPolynomial_le (T ^ 2 + 1) d L hL hd n)
  · exact digit_det_designated_coefficient_ne_zero φ T d f hdesignated hzero hne

end Problem355.EncodedDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LabelResidues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.LabelResidues

open DesignatedCoefficient EncodedDeterminant

@[simp]
theorem residue_at_position {R Λ : Type*} [AddCommMonoid R] (T : ℕ)
    (f : Fin 3 → Fin T → Λ → R) (i : Fin 3) (a : Fin T) (x : Λ) :
    residue T f i (position T i a) x = f i a x := by
  classical
  unfold residue
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    exact ite_eq_right (fun h => hba (position_injective T i h))
  · simp

theorem residue_eq_zero {R Λ : Type*} [AddCommMonoid R] (T : ℕ)
    (f : Fin 3 → Fin T → Λ → R) (i : Fin 3) (v : ℕ) (x : Λ)
    (hv : ∀ a : Fin T, position T i a ≠ v) : residue T f i v x = 0 := by
  simp [residue, hv]

theorem labeled_polynomial_obstruction {R Λ : Type*} [CommRing R]
    (φ : ℤ →+* R) (T : ℕ) (B L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
    (hbase : 100 * ((T ^ 2 + 1 : ℕ) : ℤ) ^ 2 * L ^ 3 < B)
    (f : Fin 3 → Fin T → Λ → R) (labels : Fin 3 → Λ)
    (d : Fin 3 → Fin 3 → ℕ → ℤ)
    (hd : ∀ i j v, v < T ^ 2 + 1 → |d i j v| ≤ L)
    (hresidue : ∀ i j v, v < T ^ 2 + 1 → φ (d i j v) = residue T f i v (labels j))
    (hne : (∑ a : Fin T, Matrix.det (fun i j => f i a (labels j))) ≠ 0)
    {x : ℤ} (hx : x ≡ (DigitCoefficients.determinantPolynomial (T ^ 2 + 1) d).eval B
      [ZMOD B ^ (T ^ 2 + 1)]) : B ^ (T ^ 2) / 2 < |x| := by
  apply encoded_polynomial_obstruction φ T B L hB hL hbase d
    (fun i a j => f i a (labels j)) hd _ _ hne hx
  · intro i j a
    rw [hresidue i j (position T i a) (position_lt T i a), residue_at_position]
  · intro i j v hv hn
    rw [hresidue i j v hv, residue_eq_zero T f i v (labels j) hn]

theorem labeled_polynomial_obstruction_of_length {R Λ : Type*} [CommRing R]
    (φ : ℤ →+* R) (T K : ℕ) (hK : K = T ^ 2 + 1)
    (B L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
    (hbase : 100 * (K : ℤ) ^ 2 * L ^ 3 < B)
    (f : Fin 3 → Fin T → Λ → R) (labels : Fin 3 → Λ)
    (d : Fin 3 → Fin 3 → ℕ → ℤ)
    (hd : ∀ i j v, v < K → |d i j v| ≤ L)
    (hresidue : ∀ i j v, v < K → φ (d i j v) = residue T f i v (labels j))
    (hne : (∑ a : Fin T, Matrix.det (fun i j => f i a (labels j))) ≠ 0)
    {x : ℤ} (hx : x ≡ (DigitCoefficients.determinantPolynomial K d).eval B
      [ZMOD B ^ K]) : B ^ (K - 1) / 2 < |x| := by
  subst K
  simpa only [Nat.add_sub_cancel] using
    labeled_polynomial_obstruction φ T B L hB hL hbase f labels d hd hresidue hne hx

end Problem355.LabelResidues

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NormFoundation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.NormFoundation

open Matrix

theorem det_momentMatrix {K : Type*} [CommRing K] (x y z : K) :
    (momentMatrix x y z).det = (y - x) * (z - x) * (z - y) := by
  rw [Matrix.det_fin_three]
  simp [momentMatrix]
  ring

theorem det_momentMatrix_ne_zero {K : Type*} [CommRing K] [IsDomain K]
    {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (momentMatrix x y z).det ≠ 0 := by
  rw [det_momentMatrix]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hxy.symm)
    (sub_ne_zero.mpr hxz.symm)) (sub_ne_zero.mpr hyz.symm)

theorem norm_det_momentMatrix_ne_zero {F K : Type*} [Field F] [Field K]
    [Algebra F K] [Module.Finite F K]
    {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Algebra.norm F (momentMatrix x y z).det ≠ 0 := by
  exact Algebra.norm_ne_zero_iff.mpr (det_momentMatrix_ne_zero hxy hxz hyz)

end Problem355.NormFoundation

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NormPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.NormPolynomial

open scoped BigOperators

variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K]

omit [FiniteDimensional F K] in

theorem eval_conjugate (P : MvPolynomial V K) (x : V → F) (σ : K ≃ₐ[F] K) :
    MvPolynomial.eval (algebraMap F K ∘ x) (MvPolynomial.map σ.toRingHom P) =
      σ (MvPolynomial.eval (algebraMap F K ∘ x) P) := by
  simpa [Function.comp_def] using
    (MvPolynomial.map_eval σ.toRingHom (algebraMap F K ∘ x) P).symm

theorem eval_galoisProduct [IsGalois F K] (P : MvPolynomial V K) (x : V → F) :
    MvPolynomial.eval (algebraMap F K ∘ x) (galoisProduct (F := F) P) =
      algebraMap F K (Algebra.norm F (MvPolynomial.eval (algebraMap F K ∘ x) P)) := by
  rw [galoisProduct, map_prod, Algebra.norm_eq_prod_automorphisms]
  exact Finset.prod_congr rfl (fun σ _ => eval_conjugate P x σ)

theorem eval_normPolynomial [IsGalois F K] (P : MvPolynomial V K) (x : V → F) :
    MvPolynomial.eval x (normPolynomial (F := F) P) =
      Algebra.norm F (MvPolynomial.eval (algebraMap F K ∘ x) P) := by
  apply (algebraMap F K).injective
  rw [MvPolynomial.eval₂_comp, ← MvPolynomial.eval_map, map_normPolynomial,
    eval_galoisProduct]

theorem rename_galoisProduct_of_odd [IsGalois F K]
    (hodd : Odd (Module.finrank F K)) (P : MvPolynomial V K) (f : V → V)
    (hP : MvPolynomial.rename f P = -P) :
    MvPolynomial.rename f (galoisProduct (F := F) P) =
      -galoisProduct (F := F) P := by
  classical
  rw [galoisProduct, map_prod]
  simp_rw [← MvPolynomial.map_rename, hP, map_neg]
  rw [Finset.prod_neg]
  have hcard : Fintype.card (K ≃ₐ[F] K) = Module.finrank F K := by
    simpa only [Nat.card_eq_fintype_card] using IsGalois.card_aut_eq_finrank F K
  simp only [Finset.card_univ, hcard, hodd.neg_one_pow, neg_one_mul]

theorem rename_normPolynomial_of_odd [IsGalois F K]
    (hodd : Odd (Module.finrank F K)) (P : MvPolynomial V K) (f : V → V)
    (hP : MvPolynomial.rename f P = -P) :
    MvPolynomial.rename f (normPolynomial (F := F) P) =
      -normPolynomial (F := F) P := by
  apply MvPolynomial.map_injective (algebraMap F K) (algebraMap F K).injective
  rw [MvPolynomial.map_rename, map_normPolynomial, map_neg, map_normPolynomial]
  exact rename_galoisProduct_of_odd hodd P f hP

end Problem355.NormPolynomial

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NormDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem355.NormDeterminant

open Matrix
open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [Field K]

theorem rename_determinantPolynomial (β : ι → K) (e : Equiv.Perm (Fin 3)) :
    MvPolynomial.rename (groupRename (ι := ι) e) (determinantPolynomial β) =
      Equiv.Perm.sign e * determinantPolynomial β := by
  rw [determinantPolynomial, AlgHom.map_det]
  change Matrix.det (Matrix.of (fun i j =>
    MvPolynomial.rename (groupRename (ι := ι) e) (coordinateForm β j i))) = _
  simp_rw [rename_coordinateForm]
  exact Matrix.det_permute' e (Matrix.of (fun i j => coordinateForm β j i))

theorem swap_determinantPolynomial (β : ι → K) {a b : Fin 3} (hab : a ≠ b) :
    MvPolynomial.rename (groupRename (ι := ι) (Equiv.swap a b))
      (determinantPolynomial β) = -determinantPolynomial β := by
  rw [rename_determinantPolynomial, Equiv.Perm.sign_swap hab]
  simp

theorem eval_determinantPolynomial (β : ι → K) (x : Variables ι → K) :
    MvPolynomial.eval x (determinantPolynomial β) =
      Matrix.det (Matrix.of (fun i j => ∑ ν, β ν * x (j, i, ν))) := by
  rw [determinantPolynomial, RingHom.map_det]
  congr 1
  ext i j
  simp [coordinateForm, RingHom.mapMatrix_apply]

variable {F : Type*} [Field F] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]

theorem swap_normDeterminantPolynomial (β : ι → K)
    (hodd : Odd (Module.finrank F K)) {a b : Fin 3} (hab : a ≠ b) :
    MvPolynomial.rename (groupRename (ι := ι) (Equiv.swap a b))
      (normDeterminantPolynomial (F := F) β) =
        -normDeterminantPolynomial (F := F) β :=
  NormPolynomial.rename_normPolynomial_of_odd hodd _ _
    (swap_determinantPolynomial β hab)

omit [FiniteDimensional F K] [IsGalois F K] in

theorem eval_determinantPolynomial_matrixCoordinates (b : Module.Basis ι F K)
    (A : Matrix (Fin 3) (Fin 3) K) :
    MvPolynomial.eval (algebraMap F K ∘ matrixCoordinates b A)
      (determinantPolynomial b) = A.det := by
  rw [eval_determinantPolynomial]
  congr 1
  ext i j
  simpa [matrixCoordinates, Function.comp_def, Algebra.smul_def, mul_comm] using
    b.sum_repr (A i j)

theorem eval_normDeterminantPolynomial_matrixCoordinates (b : Module.Basis ι F K)
    (A : Matrix (Fin 3) (Fin 3) K) :
    MvPolynomial.eval (matrixCoordinates b A)
      (normDeterminantPolynomial (F := F) b) = Algebra.norm F A.det := by
  rw [normDeterminantPolynomial, NormPolynomial.eval_normPolynomial,
    eval_determinantPolynomial_matrixCoordinates]

theorem eval_normDeterminantPolynomial_ne_zero (b : Module.Basis ι F K)
    {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    MvPolynomial.eval (matrixCoordinates b (NormFoundation.momentMatrix x y z))
      (normDeterminantPolynomial (F := F) b) ≠ 0 := by
  rw [eval_normDeterminantPolynomial_matrixCoordinates]
  exact NormFoundation.norm_det_momentMatrix_ne_zero hxy hxz hyz

omit [Fintype ι] [FiniteDimensional F K] [IsGalois F K] in
theorem labelTriple_eq_matrixCoordinates (b : Module.Basis ι F K) (x y z : K) :
    labelTriple b x y z = matrixCoordinates b (NormFoundation.momentMatrix x y z) := by
  funext v
  rcases v with ⟨j, i, ν⟩
  fin_cases j <;> fin_cases i <;>
    simp [labelTriple, labelCoordinates, matrixCoordinates,
      NormFoundation.momentColumn, NormFoundation.momentMatrix]

theorem eval_normDeterminantPolynomial_labels_ne_zero (b : Module.Basis ι F K)
    {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    MvPolynomial.eval (labelTriple b x y z)
      (normDeterminantPolynomial (F := F) b) ≠ 0 := by
  rw [labelTriple_eq_matrixCoordinates]
  exact eval_normDeterminantPolynomial_ne_zero b hxy hxz hyz

end Problem355.NormDeterminant

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.FiniteFieldLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.FiniteFieldLabels

variable (p : ℕ) [Fact p.Prime]

theorem card_label : Nat.card (Label p) = p ^ heilbronnD :=
  GaloisField.card p heilbronnD (by norm_num [heilbronnD])

theorem finrank_label : Module.finrank (ZMod p) (Label p) = heilbronnD :=
  GaloisField.finrank p (by norm_num [heilbronnD])

theorem swap_labelNormPolynomial {a b : Fin 3} (hab : a ≠ b) :
    MvPolynomial.rename (NormDeterminant.groupRename (Equiv.swap a b))
      (labelNormPolynomial p) = -labelNormPolynomial p := by
  apply NormDeterminant.swap_normDeterminantPolynomial _ _ hab
  rw [finrank_label]
  norm_num [heilbronnD]

theorem eval_labelNormPolynomial_ne_zero {x y z : Label p}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    MvPolynomial.eval (fun v => labelVector p (![x, y, z] v.1) v.2)
      (labelNormPolynomial p) ≠ 0 :=
  NormDeterminant.eval_normDeterminantPolynomial_labels_ne_zero (labelBasis p)
    hxy hxz hyz

end Problem355.FiniteFieldLabels

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NormHomogeneity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem355.NormHomogeneity
open scoped BigOperators
open MvPolynomial

lemma isWeightedHomogeneous_map {R S V M : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] (f : R →+* S) {w : V → M} {P : MvPolynomial V R} {d : M}
    (hP : P.IsWeightedHomogeneous w d) : (P.map f).IsWeightedHomogeneous w d := by
  intro m hm
  apply hP
  intro hz
  apply hm
  simp [MvPolynomial.coeff_map, hz]

lemma isWeightedHomogeneous_of_map {R S V M : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] (f : R →+* S) (hf : Function.Injective f)
    {w : V → M} {P : MvPolynomial V R} {d : M}
    (hP : (P.map f).IsWeightedHomogeneous w d) : P.IsWeightedHomogeneous w d := by
  intro m hm
  apply hP
  intro hz
  apply hm
  apply hf
  simpa only [MvPolynomial.coeff_map, map_zero] using hz

open NormDeterminant
variable {ι K : Type*} [Fintype ι] [Field K]

lemma coordinateForm_isWeightedHomogeneous (β : ι → K) (g j i : Fin 3) :
    (coordinateForm β j i).IsWeightedHomogeneous (groupWeight g)
      (if j = g then 1 else 0) := by
  classical
  apply IsWeightedHomogeneous.sum
  intro ν hν
  simpa only [groupWeight] using
    (isWeightedHomogeneous_X (R := K) (groupWeight g) (j, i, ν)).C_mul (β ν)

theorem determinantPolynomial_isWeightedHomogeneous (β : ι → K) (g : Fin 3) :
    (determinantPolynomial β).IsWeightedHomogeneous (groupWeight g) 1 := by
  classical
  rw [determinantPolynomial, Matrix.det_apply']
  apply IsWeightedHomogeneous.sum
  intro σ hσ
  have hp : (∏ j : Fin 3, coordinateForm β j (σ j)).IsWeightedHomogeneous
      (groupWeight g) 1 := by
    simpa using IsWeightedHomogeneous.prod Finset.univ
      (fun j : Fin 3 => coordinateForm β j (σ j))
      (fun j : Fin 3 => if j = g then 1 else 0)
      (fun j _ => coordinateForm_isWeightedHomogeneous β g j (σ j))
  simpa using hp.C_mul ((Equiv.Perm.sign σ : ℤ) : K)

variable {F : Type*} [Field F] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]

theorem galoisProduct_isWeightedHomogeneous {V M : Type*} [AddCommMonoid M]
    {w : V → M} {P : MvPolynomial V K} {d : M}
    (hP : P.IsWeightedHomogeneous w d) :
    (NormPolynomial.galoisProduct (F := F) P).IsWeightedHomogeneous w
      (Module.finrank F K • d) := by
  classical
  have hcard : Fintype.card (K ≃ₐ[F] K) = Module.finrank F K := by
    simpa only [Nat.card_eq_fintype_card] using IsGalois.card_aut_eq_finrank F K
  unfold NormPolynomial.galoisProduct
  simpa only [Finset.sum_const, Finset.card_univ, hcard] using
    IsWeightedHomogeneous.prod Finset.univ
      (fun σ : K ≃ₐ[F] K => MvPolynomial.map σ.toRingHom P)
      (fun _ => d) (fun σ _ => isWeightedHomogeneous_map σ.toRingHom hP)

theorem normPolynomial_isWeightedHomogeneous {V M : Type*} [AddCommMonoid M]
    {w : V → M} {P : MvPolynomial V K} {d : M}
    (hP : P.IsWeightedHomogeneous w d) :
    (NormPolynomial.normPolynomial (F := F) P).IsWeightedHomogeneous w
      (Module.finrank F K • d) := by
  apply isWeightedHomogeneous_of_map (algebraMap F K) (algebraMap F K).injective
  rw [NormPolynomial.map_normPolynomial]
  exact galoisProduct_isWeightedHomogeneous hP

theorem normDeterminantPolynomial_isWeightedHomogeneous (β : ι → K) (g : Fin 3) :
    (normDeterminantPolynomial (F := F) β).IsWeightedHomogeneous
      (groupWeight g) (Module.finrank F K) := by
  simpa [normDeterminantPolynomial] using
    normPolynomial_isWeightedHomogeneous (F := F)
      (determinantPolynomial_isWeightedHomogeneous β g)

end Problem355.NormHomogeneity

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PolynomialCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem355.PolynomialCoefficients

open MvPolynomial

variable {σ R : Type*}

lemma combine_injective : Function.Injective
    (fun t : (σ →₀ ℕ) × (σ →₀ ℕ) × (σ →₀ ℕ) => combine t.1 t.2.1 t.2.2) := by
  intro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have ha : a = a' := by
    ext i
    exact congrArg (fun d => d (0, i)) h
  have hb : b = b' := by
    ext i
    exact congrArg (fun d => d (1, i)) h
  have hc : c = c' := by
    ext i
    exact congrArg (fun d => d (2, i)) h
  simp only [Prod.mk.injEq]
  exact ⟨ha, hb, hc⟩

lemma combine_curry (d : (Fin 3 × σ) →₀ ℕ) :
    combine (d.curry 0) (d.curry 1) (d.curry 2) = d := by
  ext ⟨i, s⟩
  fin_cases i <;> rfl

lemma combine_index_injective {ι : Type*} (e : ι → σ →₀ ℕ)
    (he : Function.Injective e) : Function.Injective
      (fun t : ι × ι × ι => combine (e t.1) (e t.2.1) (e t.2.2)) := by
  intro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h' : (e a, e b, e c) = (e a', e b', e c') :=
    @combine_injective σ (e a, e b, e c) (e a', e b', e c') h
  simp only [Prod.mk.injEq] at h' ⊢
  exact ⟨he h'.1, he h'.2.1, he h'.2.2⟩

lemma curry_degree_eq_weight [Fintype σ] (d : (Fin 3 × σ) →₀ ℕ) (j : Fin 3) :
    (d.curry j).degree =
      Finsupp.weight (fun v : Fin 3 × σ => if v.1 = j then (1 : ℕ) else 0) d := by
  classical
  rw [Finsupp.degree_eq_sum, Finsupp.weight_apply,
    Finsupp.sum_fintype _ _ (by intro i; simp), Fintype.sum_prod_type]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

section Expansion

variable [CommSemiring R]

lemma expansion_of_support {ι : Type*} [Fintype ι]
    (P : MvPolynomial σ R) (e : ι → σ →₀ ℕ) (he : Function.Injective e)
    (hP : ∀ d ∈ P.support, d ∈ Set.range e) :
    P = ∑ i, monomial (e i) (P.coeff (e i)) := by
  classical
  calc
    P = ∑ d ∈ P.support, monomial d (P.coeff d) := P.as_sum
    _ = ∑ d ∈ Finset.univ.image e, monomial d (P.coeff d) := by
      apply Finset.sum_subset
      · intro d hd
        obtain ⟨i, rfl⟩ := hP d hd
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      · intro d _ hd
        simp [MvPolynomial.notMem_support_iff.mp hd]
    _ = _ := Finset.sum_image (fun i _ j _ hij => he hij)

lemma three_group_expansion {ι : Type*} [Fintype ι]
    (P : MvPolynomial (Fin 3 × σ) R) (e : ι → σ →₀ ℕ)
    (he : Function.Injective e)
    (hP : ∀ d ∈ P.support, ∀ j : Fin 3, d.curry j ∈ Set.range e) :
    P = ∑ a, ∑ b, ∑ c,
      monomial (combine (e a) (e b) (e c))
        (P.coeff (combine (e a) (e b) (e c))) := by
  classical
  have hsupport : ∀ d ∈ P.support, d ∈ Set.range
      (fun t : ι × ι × ι => combine (e t.1) (e t.2.1) (e t.2.2)) := by
    intro d hd
    obtain ⟨a, ha⟩ := hP d hd 0
    obtain ⟨b, hb⟩ := hP d hd 1
    obtain ⟨c, hc⟩ := hP d hd 2
    refine ⟨(a, b, c), ?_⟩
    simp only [ha, hb, hc]
    exact combine_curry d
  simpa only [Fintype.sum_prod_type] using
    expansion_of_support P _ (combine_index_injective e he) hsupport

lemma inGroup_apply_ne (i j : Fin 3) (hij : i ≠ j) (a : σ →₀ ℕ) (s : σ) :
    inGroup i a (j, s) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨t, ht⟩
  exact hij (Prod.mk.inj ht).1

lemma combine_eq_add (a b c : σ →₀ ℕ) :
    combine a b c = inGroup 0 a + inGroup 1 b + inGroup 2 c := by
  ext ⟨i, s⟩
  fin_cases i <;>
    simp [inGroup_apply_ne, show (0 : Fin 3) ≠ 1 by decide,
      show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide,
      show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide]

lemma groupMonomial_eq (j : Fin 3) (a : σ →₀ ℕ) :
    groupMonomial (R := R) j a = monomial (inGroup j a) 1 := by
  rw [groupMonomial, rename_monomial, inGroup]

lemma monomial_combine (a b c : σ →₀ ℕ) (r : R) :
    monomial (combine a b c) r =
      C r * groupMonomial 0 a * groupMonomial 1 b * groupMonomial 2 c := by
  rw [combine_eq_add]
  simp only [groupMonomial_eq, C_mul_monomial, monomial_mul, mul_one]

lemma eval_monomial_combine (a b c : σ →₀ ℕ) (r : R)
    (x : Fin 3 × σ → R) :
    eval x (monomial (combine a b c) r) =
      r * eval (fun s => x (0, s)) (monomial a 1) *
        eval (fun s => x (1, s)) (monomial b 1) *
        eval (fun s => x (2, s)) (monomial c 1) := by
  rw [monomial_combine]
  simp [groupMonomial, eval_rename, Function.comp_def]

lemma eval_three_group_expansion {ι : Type*} [Fintype ι]
    (P : MvPolynomial (Fin 3 × σ) R) (e : ι → σ →₀ ℕ)
    (he : Function.Injective e)
    (hP : ∀ d ∈ P.support, ∀ j : Fin 3, d.curry j ∈ Set.range e)
    (x : Fin 3 × σ → R) :
    eval x P = ∑ a, ∑ b, ∑ c,
      P.coeff (combine (e a) (e b) (e c)) *
        eval (fun s => x (0, s)) (monomial (e a) 1) *
        eval (fun s => x (1, s)) (monomial (e b) 1) *
        eval (fun s => x (2, s)) (monomial (e c) 1) := by
  conv_lhs => rw [three_group_expansion P e he hP]
  simp only [map_sum, eval_monomial_combine]

end Expansion

variable [CommRing R]

lemma coeff_mapDomain_eq_neg (e : Equiv.Perm σ) (P : MvPolynomial σ R)
    (hP : rename e P = -P) (d : σ →₀ ℕ) :
    P.coeff (d.mapDomain e) = -P.coeff d := by
  have h := coeff_rename_mapDomain e e.injective P d
  rw [hP, coeff_neg] at h
  exact neg_eq_iff_eq_neg.mp h

lemma tensorCoeff_swap01 (P : MvPolynomial (Fin 3 × σ) R)
    (hP : rename (groupSwap (σ := σ) 0 1) P = -P) (a b c : σ →₀ ℕ) :
    tensorCoeff P b a c = -tensorCoeff P a b c := by
  simpa [tensorCoeff] using
    coeff_mapDomain_eq_neg (groupSwap 0 1) P hP (combine a b c)

lemma tensorCoeff_swap12 (P : MvPolynomial (Fin 3 × σ) R)
    (hP : rename (groupSwap (σ := σ) 1 2) P = -P) (a b c : σ →₀ ℕ) :
    tensorCoeff P a c b = -tensorCoeff P a b c := by
  simpa [tensorCoeff] using
    coeff_mapDomain_eq_neg (groupSwap 1 2) P hP (combine a b c)

end Problem355.PolynomialCoefficients

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NormDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.NormDecomposition

open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [CommRing R]

private theorem sum_swap_first (f : ι → ι → ι → R) :
    (∑ i, ∑ j, ∑ k, f j i k) = ∑ i, ∑ j, ∑ k, f i j k := by
  rw [Finset.sum_comm]

private theorem sum_swap_last (f : ι → ι → ι → R) :
    (∑ i, ∑ j, ∑ k, f i k j) = ∑ i, ∑ j, ∑ k, f i j k := by
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

private theorem sum_rotate (f : ι → ι → ι → R) :
    (∑ i, ∑ j, ∑ k, f k i j) = ∑ i, ∑ j, ∑ k, f i j k := by
  calc
    (∑ i, ∑ j, ∑ k, f k i j) = ∑ i, ∑ j, ∑ k, f j i k :=
      sum_swap_last (fun i j k => f j i k)
    _ = ∑ i, ∑ j, ∑ k, f i j k := sum_swap_first f

private theorem sum_rotate' (f : ι → ι → ι → R) :
    (∑ i, ∑ j, ∑ k, f j k i) = ∑ i, ∑ j, ∑ k, f i j k := by
  calc
    (∑ i, ∑ j, ∑ k, f j k i) = ∑ i, ∑ j, ∑ k, f i k j :=
      sum_swap_first (fun i j k => f i k j)
    _ = ∑ i, ∑ j, ∑ k, f i j k := sum_swap_last f

private theorem sum_reverse (f : ι → ι → ι → R) :
    (∑ i, ∑ j, ∑ k, f k j i) = ∑ i, ∑ j, ∑ k, f i j k := by
  calc
    (∑ i, ∑ j, ∑ k, f k j i) = ∑ i, ∑ j, ∑ k, f j k i :=
      sum_swap_last (fun i j k => f j k i)
    _ = ∑ i, ∑ j, ∑ k, f i j k := sum_rotate' f

variable [LinearOrder ι]

omit [Fintype ι] in
private theorem partition_pointwise (f : ι → ι → ι → R)
    (h12 : ∀ i k, f i i k = 0) (h13 : ∀ i j, f i j i = 0)
    (h23 : ∀ i j, f i j j = 0) (i j k : ι) :
    f i j k =
      (if i < j ∧ j < k then f i j k else 0) +
      (if i < k ∧ k < j then f i j k else 0) +
      (if j < i ∧ i < k then f i j k else 0) +
      (if j < k ∧ k < i then f i j k else 0) +
      (if k < i ∧ i < j then f i j k else 0) +
      (if k < j ∧ j < i then f i j k else 0) := by
  rcases lt_trichotomy i j with hij | hij | hij
  · rcases lt_trichotomy j k with hjk | hjk | hjk
    · simp only [hij, hjk, lt_trans hij hjk, and_self, ite_true,
        not_lt_of_gt hij, not_lt_of_gt hjk, not_lt_of_gt (lt_trans hij hjk),
        false_and, and_false, ite_false, add_zero]
    · subst k
      simp [h23]
    · rcases lt_trichotomy i k with hik | hik | hik
      · simp [hij, hjk, hik, not_lt_of_gt hij, not_lt_of_gt hjk, not_lt_of_gt hik]
      · subst k
        simp [h13]
      · simp [hij, hjk, hik, not_lt_of_gt hij, not_lt_of_gt hjk, not_lt_of_gt hik]
  · subst j
    simp [h12]
  · rcases lt_trichotomy i k with hik | hik | hik
    · simp [hij, hik, lt_trans hij hik, not_lt_of_gt hij, not_lt_of_gt hik,
        not_lt_of_gt (lt_trans hij hik)]
    · subst k
      simp [h13]
    · rcases lt_trichotomy j k with hjk | hjk | hjk
      · simp [hij, hik, hjk, not_lt_of_gt hij, not_lt_of_gt hik, not_lt_of_gt hjk]
      · subst k
        simp [h23]
      · simp [hij, hik, hjk, not_lt_of_gt hij, not_lt_of_gt hik, not_lt_of_gt hjk]

theorem sum_eq_six_increasing (f : ι → ι → ι → R)
    (h12 : ∀ i k, f i i k = 0) (h13 : ∀ i j, f i j i = 0)
    (h23 : ∀ i j, f i j j = 0) :
    (∑ i, ∑ j, ∑ k, f i j k) =
      increasingSum f + increasingSum (fun i j k => f i k j) +
      increasingSum (fun i j k => f j i k) +
      increasingSum (fun i j k => f k i j) +
      increasingSum (fun i j k => f j k i) +
      increasingSum (fun i j k => f k j i) := by
  have h132 : increasingSum (fun i j k => f i k j) =
      ∑ i, ∑ j, ∑ k, if i < k ∧ k < j then f i j k else 0 :=
    sum_swap_last (fun i j k => if i < k ∧ k < j then f i j k else 0)
  have h213 : increasingSum (fun i j k => f j i k) =
      ∑ i, ∑ j, ∑ k, if j < i ∧ i < k then f i j k else 0 :=
    sum_swap_first (fun i j k => if j < i ∧ i < k then f i j k else 0)
  have h312 : increasingSum (fun i j k => f k i j) =
      ∑ i, ∑ j, ∑ k, if j < k ∧ k < i then f i j k else 0 :=
    sum_rotate (fun i j k => if j < k ∧ k < i then f i j k else 0)
  have h231 : increasingSum (fun i j k => f j k i) =
      ∑ i, ∑ j, ∑ k, if k < i ∧ i < j then f i j k else 0 :=
    sum_rotate' (fun i j k => if k < i ∧ i < j then f i j k else 0)
  have h321 : increasingSum (fun i j k => f k j i) =
      ∑ i, ∑ j, ∑ k, if k < j ∧ j < i then f i j k else 0 :=
    sum_reverse (fun i j k => if k < j ∧ j < i then f i j k else 0)
  rw [h132, h213, h312, h231, h321]
  unfold increasingSum
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact partition_pointwise f h12 h13 h23 i j k

theorem alternating_triple_sum (c : ι → ι → ι → R)
    (h12 : ∀ i k, c i i k = 0) (h13 : ∀ i j, c i j i = 0)
    (h23 : ∀ i j, c i j j = 0)
    (hs12 : ∀ i j k, c j i k = -c i j k)
    (hs23 : ∀ i j k, c i k j = -c i j k)
    (x y z : ι → R) :
    (∑ i, ∑ j, ∑ k, c i j k * x i * y j * z k) =
      increasingSum (fun i j k => c i j k *
        Matrix.det !![x i, y i, z i; x j, y j, z j; x k, y k, z k]) := by
  rw [sum_eq_six_increasing
    (fun i j k => c i j k * x i * y j * z k)
    (by intro i k; simp [h12])
    (by intro i j; simp [h13])
    (by intro i j; simp [h23])]
  unfold increasingSum
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : i < j ∧ j < k
  · simp [h, Matrix.det_fin_three]
    have h132 := hs23 i j k
    have h213 := hs12 i j k
    have h312 : c k i j = c i j k := by rw [hs12, h132, neg_neg]
    have h231 : c j k i = c i j k := by rw [hs23, h213, neg_neg]
    have h321 : c k j i = -c i j k := by rw [hs12, h231]
    rw [h132, h213, h312, h231, h321]
    ring
  · simp [h]

end Problem355.NormDecomposition

end OAI
end

section
-- module Solutions.OAIQW_Problem355.TripleEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.NormDecomposition

open scoped BigOperators

variable {ι : Type*} [LinearOrder ι]

variable [Fintype ι]

variable {R : Type*} [CommRing R]

theorem increasingSum_eq_sum_triples (f : ι → ι → ι → R) :
    increasingSum f = ∑ t : IncreasingTriple ι, f t.val.1 t.val.2.1 t.val.2.2 := by
  unfold increasingSum
  simpa only [Finset.sum_filter, Fintype.sum_prod_type] using
    (Finset.sum_subtype
      (Finset.univ.filter (fun t : ι × ι × ι => t.1 < t.2.1 ∧ t.2.1 < t.2.2))
      (fun _ => by simp)
      (fun t : ι × ι × ι => f t.1 t.2.1 t.2.2))

theorem increasingSum_eq_sum_fin (f : ι → ι → ι → R) :
    increasingSum f = ∑ a : Fin (Nat.choose (Fintype.card ι) 3),
      let t := (increasingTripleEquivFin (ι := ι)).symm a
      f t.val.1 t.val.2.1 t.val.2.2 := by
  rw [increasingSum_eq_sum_triples]
  exact ((increasingTripleEquivFin (ι := ι)).symm.sum_comp
    (fun t : IncreasingTriple ι => f t.val.1 t.val.2.1 t.val.2.2)).symm

theorem alternating_sum_eq_sum_determinants {X : Type*}
    (c : ι → ι → ι → R) (m : ι → X → R)
    (h12 : ∀ i k, c i i k = 0) (h13 : ∀ i j, c i j i = 0)
    (h23 : ∀ i j, c i j j = 0)
    (hs12 : ∀ i j k, c j i k = -c i j k)
    (hs23 : ∀ i j k, c i k j = -c i j k) (x y z : X) :
    (∑ i, ∑ j, ∑ k, c i j k * m i x * m j y * m k z) =
      ∑ a : Fin (Nat.choose (Fintype.card ι) 3),
        Matrix.det !![
          decompositionRows c m a 0 x, decompositionRows c m a 0 y,
            decompositionRows c m a 0 z;
          decompositionRows c m a 1 x, decompositionRows c m a 1 y,
            decompositionRows c m a 1 z;
          decompositionRows c m a 2 x, decompositionRows c m a 2 y,
            decompositionRows c m a 2 z] := by
  rw [alternating_triple_sum c h12 h13 h23 hs12 hs23
    (fun i => m i x) (fun i => m i y) (fun i => m i z),
    increasingSum_eq_sum_fin]
  apply Finset.sum_congr rfl
  intro a _
  simp [decompositionRows, Matrix.det_fin_three]
  ring

end Problem355.NormDecomposition

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NormEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.NormEncoding

open scoped BigOperators
open MvPolynomial

theorem monomialExponent_injective : Function.Injective monomialExponent :=
  Subtype.val_injective.comp Monomials.heilbronnCoordinateMonomialEquiv.symm.injective

variable (p : ℕ) [Fact p.Prime]

theorem monomialExponent_covers (d : (Fin 3 × Coordinate) →₀ ℕ)
    (hd : d ∈ (FiniteFieldLabels.labelNormPolynomial p).support) (j : Fin 3) :
    d.curry j ∈ Set.range monomialExponent := by
  have hdegree : (d.curry j).degree = heilbronnD := by
    rw [PolynomialCoefficients.curry_degree_eq_weight]
    change Finsupp.weight (NormHomogeneity.groupWeight j) d = heilbronnD
    have h := NormHomogeneity.normDeterminantPolynomial_isWeightedHomogeneous
      (FiniteFieldLabels.labelBasis p) j
      (MvPolynomial.mem_support_iff.mp hd)
    simpa only [FiniteFieldLabels.finrank_label] using h
  let m : Monomials.DegreeIndex Coordinate heilbronnD := ⟨d.curry j, hdegree⟩
  refine ⟨Monomials.heilbronnCoordinateMonomialEquiv m, ?_⟩
  simp [monomialExponent, m]

theorem normCoefficient_swap01 (i j k : Fin heilbronnM) :
    normCoefficient p j i k = -normCoefficient p i j k := by
  apply PolynomialCoefficients.tensorCoeff_swap01
  exact FiniteFieldLabels.swap_labelNormPolynomial p (by decide : (0 : Fin 3) ≠ 1)

theorem normCoefficient_swap12 (i j k : Fin heilbronnM) :
    normCoefficient p i k j = -normCoefficient p i j k := by
  apply PolynomialCoefficients.tensorCoeff_swap12
  exact FiniteFieldLabels.swap_labelNormPolynomial p (by decide : (1 : Fin 3) ≠ 2)

theorem eval_labelNormPolynomial_eq_sum (x y z : FiniteFieldLabels.Label p) :
    MvPolynomial.eval (fun v => FiniteFieldLabels.labelVector p (![x, y, z] v.1) v.2)
      (FiniteFieldLabels.labelNormPolynomial p) =
      ∑ i, ∑ j, ∑ k, normCoefficient p i j k * monomialValue p i x *
        monomialValue p j y * monomialValue p k z := by
  simpa [normCoefficient, PolynomialCoefficients.tensorCoeff, monomialValue] using
    PolynomialCoefficients.eval_three_group_expansion
      (FiniteFieldLabels.labelNormPolynomial p) monomialExponent monomialExponent_injective
      (monomialExponent_covers p)
      (fun v => FiniteFieldLabels.labelVector p (![x, y, z] v.1) v.2)

theorem two_ne_zero (hp : 2 < p) : (2 : ZMod p) ≠ 0 := by
  change ((2 : ℕ) : ZMod p) ≠ 0
  intro h
  exact Nat.not_dvd_of_pos_of_lt (by decide) hp
    ((ZMod.natCast_eq_zero_iff 2 p).mp h)

private theorem eq_zero_of_eq_neg {R : Type*} [CommRing R] [NoZeroDivisors R]
    (h2 : (2 : R) ≠ 0) (a : R) (ha : a = -a) : a = 0 := by
  have h : (2 : R) * a = 0 := by linear_combination ha
  exact (mul_eq_zero.mp h).resolve_left h2

theorem normCoefficient_diag01 (hp : 2 < p) (i k : Fin heilbronnM) :
    normCoefficient p i i k = 0 :=
  eq_zero_of_eq_neg (two_ne_zero p hp) _ (normCoefficient_swap01 p i i k)

theorem normCoefficient_diag12 (hp : 2 < p) (i j : Fin heilbronnM) :
    normCoefficient p i j j = 0 :=
  eq_zero_of_eq_neg (two_ne_zero p hp) _ (normCoefficient_swap12 p i j j)

theorem normCoefficient_diag02 (hp : 2 < p) (i j : Fin heilbronnM) :
    normCoefficient p i j i = 0 := by
  rw [normCoefficient_swap01, normCoefficient_diag12 p hp, neg_zero]

private theorem matrix_of_label_values {R X : Type*} (f : Fin 3 → X → R) (x y z : X) :
    (fun i j => f i (![x, y, z] j)) =
      !![f 0 x, f 0 y, f 0 z; f 1 x, f 1 y, f 1 z; f 2 x, f 2 y, f 2 z] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem sum_normRowFunctions_eq_eval (hp : 2 < p) (x y z : FiniteFieldLabels.Label p) :
    (∑ a : Fin heilbronnT,
      Matrix.det (fun i j => normRowFunctions p i a (![x, y, z] j))) =
      MvPolynomial.eval (fun v => FiniteFieldLabels.labelVector p (![x, y, z] v.1) v.2)
        (FiniteFieldLabels.labelNormPolynomial p) := by
  have h := NormDecomposition.alternating_sum_eq_sum_determinants
    (normCoefficient p) (monomialValue p)
    (normCoefficient_diag01 p hp) (normCoefficient_diag02 p hp)
    (normCoefficient_diag12 p hp) (normCoefficient_swap01 p)
    (normCoefficient_swap12 p) x y z
  rw [← eval_labelNormPolynomial_eq_sum p x y z] at h
  rw [h]
  simp_rw [normRowFunctions, matrix_of_label_values]
  apply Fintype.sum_equiv determinantIndexEquiv.symm
  intro a
  rfl

theorem sum_normRowFunctions_ne_zero (hp : 2 < p)
    {x y z : FiniteFieldLabels.Label p} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (∑ a : Fin heilbronnT,
      Matrix.det (fun i j => normRowFunctions p i a (![x, y, z] j))) ≠ 0 := by
  rw [sum_normRowFunctions_eq_eval p hp]
  exact FiniteFieldLabels.eval_labelNormPolynomial_ne_zero p hxy hxz hyz

end Problem355.NormEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355

private lemma squareAddOne_def (t : ℕ) : squareAddOne t = t ^ 2 + 1 := rfl

lemma heilbronnK_eq : heilbronnK = heilbronnT ^ 2 + 1 := by
  with_unfolding_all exact squareAddOne_def heilbronnT

end Problem355

namespace Problem355.Parameters

lemma base_le_previous_power {B k : ℕ} (hB : 1 ≤ B) (hk : 2 ≤ k) :
    B ≤ B ^ (k - 1) := by
  have h : 1 ≤ k - 1 := by omega
  simpa using (pow_le_pow_right' hB h)

lemma threshold_pos {B k : ℕ} (hB : 3 ≤ B) (hk : 2 ≤ k) :
    0 < threshold B k := by
  have h := base_le_previous_power (by omega : 1 ≤ B) hk
  unfold threshold
  omega

lemma previous_power_le_three_threshold {B k : ℕ} (hB : 3 ≤ B) (hk : 2 ≤ k) :
    B ^ (k - 1) ≤ 3 * threshold B k := by
  have h := base_le_previous_power (by omega : 1 ≤ B) hk
  unfold threshold
  omega

lemma twice_threshold_lt_power {B k : ℕ} (hB : 3 ≤ B) (hk : 2 ≤ k) :
    2 * threshold B k < B ^ k := by
  have hm := base_le_previous_power (by omega : 1 ≤ B) hk
  have he : k = (k - 1) + 1 := by omega
  have hpowe : B ^ k = B ^ (k - 1) * B := by nth_rw 1 [he]; rw [pow_succ]
  rw [hpowe]
  unfold threshold
  have hd : 2 * (B ^ (k - 1) / 2) ≤ B ^ (k - 1) := by omega
  have hp : 0 < B ^ (k - 1) := by omega
  nlinarith

lemma power_le_three_base_threshold {B k : ℕ} (hB : 3 ≤ B) (hk : 2 ≤ k) :
    B ^ k ≤ 3 * B * threshold B k := by
  have h := previous_power_le_three_threshold hB hk
  have he : k = (k - 1) + 1 := by omega
  calc
    B ^ k = B ^ (k - 1) * B := by nth_rw 1 [he]; rw [pow_succ]
    _ ≤ (3 * threshold B k) * B := Nat.mul_le_mul_right B h
    _ = 3 * B * threshold B k := by ring

lemma box_polynomial_bound {B r q k : ℕ}
    (hB : B ≤ r ^ 31) (hq : q ≤ (B ^ k) ^ 101) :
    (B ^ k * q) ^ 10 ≤ r ^ (31620 * k) := by
  calc
    (B ^ k * q) ^ 10 ≤ (B ^ k * (B ^ k) ^ 101) ^ 10 := by gcongr
    _ = B ^ (1020 * k) := by ring
    _ ≤ (r ^ 31) ^ (1020 * k) := Nat.pow_le_pow_left hB _
    _ = r ^ (31620 * k) := by rw [← pow_mul]; congr 1; ring

end Problem355.Parameters

end OAI
end

section
-- module Solutions.OAIQW_Problem355.MainResidueSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.MainResidueSystem

open FiniteFieldLabels

variable (p : ℕ) [Fact p.Prime]

theorem norm_rows_separate (hp : 2 < p) (labels : Fin 3 → Label p)
    (hinj : Function.Injective labels) :
    (∑ a : Fin heilbronnT,
      Matrix.det (fun i j => NormEncoding.normRowFunctions p i a (labels j))) ≠ 0 := by
  have h01 : labels 0 ≠ labels 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h)
  have h02 : labels 0 ≠ labels 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h)
  have h12 : labels 1 ≠ labels 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h)
  have hlabels : (![labels 0, labels 1, labels 2] : Fin 3 → Label p) = labels := by
    funext i
    fin_cases i <;> rfl
  simpa only [hlabels] using NormEncoding.sum_normRowFunctions_ne_zero p hp h01 h02 h12

theorem small_det_forces_repeated_labels (hp : 2 < p)
    (B : ℕ) (L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
    (hbase : 100 * (heilbronnK : ℤ) ^ 2 * L ^ 3 < B)
    (labels : Fin 3 → Label p) (d : Fin 3 → Fin 3 → ℕ → ℤ)
    (hd : ∀ i j v, v < heilbronnK → |d i j v| ≤ L)
    (hresidue : ∀ i j v, v < heilbronnK →
      (Int.castRingHom (ZMod p)) (d i j v) = prescribedResidue p i v (labels j))
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (h : ℕ) (hh : h = B ^ heilbronnK)
    (G : Matrix.SpecialLinearGroup (Fin 3) (ZMod h))
    (hAC : A.map (Int.castRingHom (ZMod h)) =
      (G : Matrix (Fin 3) (Fin 3) (ZMod h)) *
        (Matrix.map (fun i j => ∑ v ∈ Finset.range heilbronnK, d i j v * (B : ℤ) ^ v)
          (Int.castRingHom (ZMod h))))
    (hsmall : |A.det| ≤ (B : ℤ) ^ (heilbronnK - 1) / 2) :
    ∃ i j : Fin 3, i ≠ j ∧ labels i = labels j := by
  classical
  by_contra hn
  have hinj : Function.Injective labels := by
    intro i j hij
    by_contra hne
    exact hn ⟨i, j, hne, hij⟩
  have hmod := DigitEncoding.determinant_modEq_of_specialLinear h G A
    (fun i j => ∑ v ∈ Finset.range heilbronnK, d i j v * (B : ℤ) ^ v) hAC
  have hpoly : A.det ≡ (DigitCoefficients.determinantPolynomial heilbronnK d).eval
      (B : ℤ) [ZMOD (B : ℤ) ^ heilbronnK] := by
    suffices ∀ (length modulus : ℕ), modulus = B ^ length →
        A.det ≡ Matrix.det (fun i j => ∑ v ∈ Finset.range length,
          d i j v * (B : ℤ) ^ v) [ZMOD modulus] →
        A.det ≡ (DigitCoefficients.determinantPolynomial length d).eval
          (B : ℤ) [ZMOD (B : ℤ) ^ length] from this heilbronnK h hh hmod
    intro length modulus hmodulus hdet
    rw [DigitCoefficients.eval_determinantPolynomial]
    change A.det ≡ Matrix.det (fun i j => ∑ v ∈ Finset.range length,
      d i j v * (B : ℤ) ^ v) [ZMOD (B : ℤ) ^ length]
    simpa only [hmodulus, Nat.cast_pow] using hdet
  have hout := LabelResidues.labeled_polynomial_obstruction_of_length
    (Int.castRingHom (ZMod p)) heilbronnT heilbronnK heilbronnK_eq (B : ℤ) L (by exact_mod_cast hB) hL hbase
    (NormEncoding.normRowFunctions p) labels d hd hresidue
    (norm_rows_separate p hp labels hinj) hpoly
  apply (not_lt_of_ge hsmall)
  exact hout

end Problem355.MainResidueSystem

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PrimeParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.PrimeParameters

theorem exists_base_prime (k r : ℕ) (hk : 0 < k) (hr : 0 < r) :
    ∃ B : ℕ, B.Prime ∧ 100 * k ^ 2 * r ^ 30 < B ∧
      B ≤ 200 * k ^ 2 * r ^ 30 := by
  obtain ⟨B, hB, hlo, hhi⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (100 * k ^ 2 * r ^ 30) (by positivity)
  refine ⟨B, hB, hlo, ?_⟩
  nlinarith only [hhi]

theorem exists_base_prime_le_pow (k r : ℕ) (hk : 0 < k)
    (hr : 200 * k ^ 2 ≤ r) :
    ∃ B : ℕ, B.Prime ∧ 100 * k ^ 2 * r ^ 30 < B ∧
      B ≤ 200 * k ^ 2 * r ^ 30 ∧ B ≤ r ^ 31 := by
  have hk2 : 0 < k ^ 2 := by positivity
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  obtain ⟨B, hB, hlo, hhi⟩ := exists_base_prime k r hk hr0
  refine ⟨B, hB, hlo, hhi, hhi.trans ?_⟩
  calc
    200 * k ^ 2 * r ^ 30 ≤ r * r ^ 30 := Nat.mul_le_mul_right _ hr
    _ = r ^ 31 := by ring

theorem exists_auxiliary_prime (h : ℕ) (hh : 2 ≤ h) :
    ∃ q : ℕ, q.Prime ∧ h ^ 100 < q ∧ q ≤ 2 * h ^ 100 ∧
      q ≤ h ^ 101 ∧ h.Coprime q := by
  have hh0 : 0 < h := by omega
  obtain ⟨q, hq, hlo, hhi⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (h ^ 100) (by positivity)
  have hhpow : h ≤ h ^ 100 := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < h) (by norm_num : 1 ≤ 100))
  refine ⟨q, hq, hlo, hhi, ?_, ?_⟩
  · calc
      q ≤ 2 * h ^ 100 := hhi
      _ ≤ h * h ^ 100 := Nat.mul_le_mul_right _ hh
      _ = h ^ 101 := by ring
  · exact (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hh0 (hhpow.trans_lt hlo))).symm

theorem auxiliary_prime_large (h q : ℕ) (hh : 2 ≤ h) (hq : h ^ 100 < q) :
    2000 * (h ^ 2) ^ 2 ≤ q := by
  have hpow : 2000 ≤ h ^ 96 := by
    calc
      2000 ≤ 2 ^ 96 := by norm_num
      _ ≤ h ^ 96 := Nat.pow_le_pow_left hh 96
  have hprod : 2000 * h ^ 4 ≤ h ^ 96 * h ^ 4 :=
    Nat.mul_le_mul_right _ hpow
  have heq : h ^ 96 * h ^ 4 = h ^ 100 := by ring
  have heq' : (h ^ 2) ^ 2 = h ^ 4 := by ring
  rw [heq']
  exact (hprod.trans_eq heq).trans hq.le

theorem exists_prime_parameters (k r : ℕ) (hk : 0 < k)
    (hr : 200 * k ^ 2 ≤ r) :
    ∃ B q : ℕ, B.Prime ∧ q.Prime ∧
      100 * k ^ 2 * r ^ 30 < B ∧ B ≤ 200 * k ^ 2 * r ^ 30 ∧
      B ≤ r ^ 31 ∧ (B ^ k) ^ 100 < q ∧ q ≤ 2 * (B ^ k) ^ 100 ∧
      q ≤ (B ^ k) ^ 101 ∧ (B ^ k).Coprime q ∧
      2000 * ((B ^ k) ^ 2) ^ 2 ≤ q := by
  obtain ⟨B, hB, hlo, hhi, hpoly⟩ := exists_base_prime_le_pow k r hk hr
  have hBk : 2 ≤ B ^ k := by
    calc
      2 ≤ B := hB.two_le
      _ ≤ B ^ k := by
        simpa using Nat.pow_le_pow_right hB.pos hk
  obtain ⟨q, hq, hqlo, hqhi, hqpoly, hcop⟩ := exists_auxiliary_prime (B ^ k) hBk
  exact ⟨B, q, hB, hq, hlo, hhi, hpoly, hqlo, hqhi, hqpoly, hcop,
    auxiliary_prime_large (B ^ k) q hBk hqlo⟩

theorem digit_moment_parameter_le_half (k r B : ℕ) (hk : 0 < k)
    (hr : 400 * k ^ 2 ≤ r) (hB : B ≤ 200 * k ^ 2 * r ^ 30) :
    (B : ℝ) * ((r : ℝ) / (r : ℝ) ^ 10) ^ 4 ≤ 1 / 2 := by
  have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hrpos
  have hr1 : 1 ≤ (r : ℝ) := by exact_mod_cast hrpos
  have hc : (400 : ℝ) * (k : ℝ) ^ 2 ≤ (r : ℝ) ^ 6 := by
    calc
      (400 : ℝ) * (k : ℝ) ^ 2 ≤ (r : ℝ) := by exact_mod_cast hr
      _ ≤ (r : ℝ) ^ 6 := by
        simpa using pow_le_pow_right₀ hr1 (by norm_num : 1 ≤ 6)
  have hb : (B : ℝ) ≤ 200 * (k : ℝ) ^ 2 * (r : ℝ) ^ 30 := by exact_mod_cast hB
  have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (r : ℝ) ^ 30)
  have heq : (r : ℝ) ^ 6 * (r : ℝ) ^ 30 = (r : ℝ) ^ 36 := by ring
  rw [heq] at hm
  have hid : (B : ℝ) * ((r : ℝ) / (r : ℝ) ^ 10) ^ 4 =
      (B : ℝ) / (r : ℝ) ^ 36 := by
    field_simp
  rw [hid]
  apply (div_le_iff₀ (by positivity : 0 < (r : ℝ) ^ 36)).2
  nlinarith only [hb, hm]

theorem exists_odd_prime_sequence :
    ∃ r : ℕ → ℕ, Filter.Tendsto r Filter.atTop Filter.atTop ∧
      ∀ j, (r j).Prime ∧ Odd (r j) ∧ j ≤ r j := by
  choose r hr using fun j : ℕ => Nat.exists_infinite_primes (max j 3)
  refine ⟨r, ?_, ?_⟩
  · exact Filter.tendsto_atTop_mono (fun j => (Nat.le_max_left j 3).trans (hr j).1)
      Filter.tendsto_id
  · intro j
    have hthree : 3 ≤ r j := (Nat.le_max_right j 3).trans (hr j).1
    exact ⟨(hr j).2, (hr j).2.odd_of_ne_two (by omega),
      (Nat.le_max_left j 3).trans (hr j).1⟩

end Problem355.PrimeParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ParameterSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Parameters

lemma exists_primeParameterData {k r : ℕ} (hk : 2 ≤ k)
    (hr : 400 * k ^ 2 ≤ r) : Nonempty (PrimeParameterData k r) := by
  have hr' : 200 * k ^ 2 ≤ r := by nlinarith only [hr]
  obtain ⟨B, q, hB, hq, hlo, hhi, hpoly, hqlo, hqhi, hqpoly, hcop, hlarge⟩ :=
    PrimeParameters.exists_prime_parameters k r (by omega) hr'
  exact ⟨⟨hk, hr', hr, B, q, hB, hq, hlo, hhi, hpoly, hqlo, hqhi, hqpoly, hcop, hlarge⟩⟩

namespace PrimeParameterData

variable {k r : ℕ} (P : PrimeParameterData k r)

lemma M_le_N : P.M ≤ P.N := by
  unfold N
  simpa using Nat.pow_le_pow_right P.M_pos (by norm_num : 1 ≤ 10)

lemma N_pos : 0 < P.N := lt_of_lt_of_le P.M_pos P.M_le_N

lemma tau_pos : 0 < P.tau := threshold_pos P.base_ge_three P.two_le_k

lemma twice_tau_lt_h : 2 * P.tau < P.h :=
  twice_threshold_lt_power P.base_ge_three P.two_le_k

lemma tau_lt_h : P.tau < P.h := by
  have h := P.twice_tau_lt_h
  omega

lemma tau_le_cube : P.tau ≤ P.N ^ 3 := by
  calc
    P.tau ≤ P.h := P.tau_lt_h.le
    _ ≤ P.M := P.h_le_M
    _ ≤ P.N := P.M_le_N
    _ ≤ P.N ^ 3 := by
      simpa using Nat.pow_le_pow_right P.N_pos (by norm_num : 1 ≤ 3)

lemma box_polynomial : P.N ≤ r ^ (31620 * k) :=
  box_polynomial_bound P.base_polynomial P.auxiliary_polynomial

lemma base_lower_original : 100 * k ^ 2 * (r ^ 10) ^ 3 < P.B := by
  convert P.base_lower using 1; ring

lemma tau_lt_q : P.tau < P.q := by
  calc
    P.tau < P.h := P.tau_lt_h
    _ ≤ P.h ^ 100 := by
      simpa using Nat.pow_le_pow_right (by have := P.h_ge_three; omega : 0 < P.h)
        (by norm_num : 1 ≤ 100)
    _ < P.q := P.auxiliary_lower

lemma digit_moment_bound :
    (P.B : ℝ) * ((r : ℝ) / (r : ℝ) ^ 10) ^ 4 ≤ 1 / 2 :=
  PrimeParameters.digit_moment_parameter_le_half k r P.B
    (by have := P.two_le_k; omega) P.large_for_moment P.base_upper

lemma real_bounds :
    (1 : ℝ) ≤ (P.N : ℝ) ∧ (1 : ℝ) ≤ (P.tau : ℝ) ∧
      (P.tau : ℝ) ≤ (P.N : ℝ) ^ 3 ∧ (r : ℝ) ≤ (P.M : ℝ) ∧
      (P.N : ℝ) ≤ (r : ℝ) ^ (31620 * k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast P.N_pos
  · exact_mod_cast P.tau_pos
  · exact_mod_cast P.tau_le_cube
  · exact_mod_cast P.r_le_M
  · exact_mod_cast P.box_polynomial

end PrimeParameterData

lemma exists_parameter_sequence {k : ℕ} (hk : 2 ≤ k) :
    ∃ r : ℕ → ℕ, ∃ _P : (j : ℕ) → PrimeParameterData k (r j),
      Filter.Tendsto r Filter.atTop Filter.atTop ∧
      ∀ j, (r j).Prime ∧ Odd (r j) ∧ j ≤ r j := by
  classical
  obtain ⟨r0, hr0, hprime⟩ := PrimeParameters.exists_odd_prime_sequence
  let r : ℕ → ℕ := fun j => r0 (j + 400 * k ^ 2)
  have hj (j : ℕ) : j ≤ r j := by
    exact (Nat.le_add_right j (400 * k ^ 2)).trans (hprime (j + 400 * k ^ 2)).2.2
  have hlarge (j : ℕ) : 400 * k ^ 2 ≤ r j := by
    exact (Nat.le_add_left (400 * k ^ 2) j).trans (hprime (j + 400 * k ^ 2)).2.2
  let P : (j : ℕ) → PrimeParameterData k (r j) :=
    fun j => Classical.choice (exists_primeParameterData hk (hlarge j))
  refine ⟨r, P, Filter.tendsto_atTop_mono hj Filter.tendsto_id, ?_⟩
  intro j
  exact ⟨(hprime (j + 400 * k ^ 2)).1, (hprime (j + 400 * k ^ 2)).2.1, hj j⟩

lemma exists_heilbronn_parameter_sequence :
    ∃ r : ℕ → ℕ, ∃ _P : (j : ℕ) → PrimeParameterData heilbronnK (r j),
      Filter.Tendsto r Filter.atTop Filter.atTop ∧
      ∀ j, (r j).Prime ∧ Odd (r j) ∧ j ≤ r j :=
  exists_parameter_sequence (k := heilbronnK) heilbronnK_ge_two

end Problem355.Parameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.MinorInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.UnitPivot

open Matrix

variable {R : Type*} [CommRing R]
variable {m n l : Type*}

theorem MinorsVanish.mul_left [Fintype m]
    {A : Matrix m n R} (hA : MinorsVanish A) (P : Matrix l m R) :
    MinorsVanish (P * A) := by
  intro i k j t
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  calc
    (P i b * A b j) * (P k a * A a t) =
        (P i b * P k a) * (A b j * A a t) := by ring
    _ = (P i b * P k a) * (A b t * A a j) := by rw [hA b a j t]
    _ = (P i b * A b t) * (P k a * A a j) := by ring

theorem minorsVanish_transpose_iff (A : Matrix m n R) :
    MinorsVanish A.transpose ↔ MinorsVanish A := by
  constructor <;> intro h i k j t
  · simpa only [Matrix.transpose_apply, mul_comm] using h j t i k
  · simpa only [Matrix.transpose_apply, mul_comm] using h j t i k

theorem MinorsVanish.mul_right [Fintype n]
    {A : Matrix m n R} (hA : MinorsVanish A) (Q : Matrix n l R) :
    MinorsVanish (A * Q) := by
  apply (minorsVanish_transpose_iff _).mp
  rw [Matrix.transpose_mul]
  exact ((minorsVanish_transpose_iff A).mpr hA).mul_left Q.transpose

theorem minorsVanish_unit_mul_iff [Fintype m] [DecidableEq m]
    (P : Matrix.GeneralLinearGroup m R) (A : Matrix m n R) :
    MinorsVanish ((P : Matrix m m R) * A) ↔ MinorsVanish A := by
  constructor
  · intro h
    have hh := h.mul_left (↑(P⁻¹) : Matrix m m R)
    simpa only [← Matrix.mul_assoc, P.inv_mul, Matrix.one_mul] using hh
  · exact fun h => h.mul_left _

theorem minorsVanish_mul_unit_iff [Fintype n] [DecidableEq n]
    (A : Matrix m n R) (Q : Matrix.GeneralLinearGroup n R) :
    MinorsVanish (A * (Q : Matrix n n R)) ↔ MinorsVanish A := by
  constructor
  · intro h
    have hh := h.mul_right (↑(Q⁻¹) : Matrix n n R)
    simpa only [Matrix.mul_assoc, Q.mul_inv, Matrix.mul_one] using hh
  · exact fun h => h.mul_right _

theorem minorsVanish_equivalent_iff [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (P : Matrix.GeneralLinearGroup m R) (Q : Matrix.GeneralLinearGroup n R)
    (A : Matrix m n R) :
    MinorsVanish ((P : Matrix m m R) * A * (Q : Matrix n n R)) ↔
      MinorsVanish A := by
  rw [minorsVanish_mul_unit_iff, minorsVanish_unit_mul_iff]

theorem minorsVanish_diagonal_three_iff (D E : R) :
    MinorsVanish (Matrix.diagonal ![1, D, E]) ↔ D = 0 ∧ E = 0 := by
  rw [minorsVanish_iff_pivot _ 0 0 (1 : Rˣ) (by simp)]
  constructor
  · intro h
    exact ⟨by simpa using h 1 1, by simpa using h 2 2⟩
  · rintro ⟨rfl, rfl⟩ i j
    fin_cases i <;> fin_cases j <;> simp

theorem minorsVanish_map_of_diagonal_form_iff
    {S : Type*} [CommRing S] (f : R →+* S)
    (D E : R) (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
    (C : Matrix (Fin 3) (Fin 3) R)
    (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * Matrix.diagonal ![1, D, E] *
      (Q : Matrix (Fin 3) (Fin 3) R)) :
    MinorsVanish (C.map f) ↔ f D = 0 ∧ f E = 0 := by
  have hd : (Matrix.diagonal ![1, D, E]).map f = Matrix.diagonal ![1, f D, f E] := by
    rw [Matrix.diagonal_map (map_zero f)]
    congr 1
    funext i
    fin_cases i <;> simp
  have hmap : C.map f =
      (Matrix.GeneralLinearGroup.map f P : Matrix (Fin 3) (Fin 3) S) *
        Matrix.diagonal ![1, f D, f E] *
        (Matrix.GeneralLinearGroup.map f Q : Matrix (Fin 3) (Fin 3) S) := by
    rw [hC, Matrix.map_mul, Matrix.map_mul]
    rw [hd]
    rfl
  rw [hmap, minorsVanish_equivalent_iff, minorsVanish_diagonal_three_iff]

theorem minorsVanish_reduce_prime_power_iff
    {p k b e j : ℕ} (hp : p.Prime) (hbe : b ≤ e) (hjk : j ≤ k)
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k)))
    (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k))) *
      Matrix.diagonal ![1, ((p ^ b : ℕ) : ZMod (p ^ k)),
        ((p ^ e : ℕ) : ZMod (p ^ k))] *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))) :
    MinorsVanish (C.map (ZMod.castHom (Nat.pow_dvd_pow p hjk) (ZMod (p ^ j)))) ↔
      j ≤ b := by
  rw [minorsVanish_map_of_diagonal_form_iff _ _ _ P Q C hC]
  simp only [map_natCast, ZMod.natCast_eq_zero_iff,
    Nat.pow_dvd_pow_iff_le_right hp.one_lt]
  omega

end Problem355.UnitPivot

end OAI
end

section
-- module Solutions.OAIQW_Problem355.RepeatedLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem355.Sampling

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem sum_repeated_labels_le (f : α → α → α → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ a b c, f a b c ≤ M)
    (hzero : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → f a b c = 0) :
    (∑ a, ∑ b, ∑ c, f a b c) ≤ 3 * (Fintype.card α : ℝ) ^ 2 * M := by
  have hpoint (a b c : α) : f a b c ≤
      (if a = b then M else 0) + (if a = c then M else 0) +
        (if b = c then M else 0) := by
    have hf := hbound a b c
    by_cases hab : a = b
    · simp only [ite_eq_left hab]
      split_ifs <;> linarith
    by_cases hac : a = c
    · simp only [ite_eq_right hab, ite_eq_left hac, zero_add]
      split_ifs <;> linarith
    by_cases hbc : b = c
    · simp only [ite_eq_right hab, ite_eq_right hac, ite_eq_left hbc, zero_add]
      exact hf
    simp only [ite_eq_right hab, ite_eq_right hac, ite_eq_right hbc, add_zero,
      hzero a b c hab hac hbc, le_refl]
  calc
    (∑ a, ∑ b, ∑ c, f a b c) ≤
        ∑ a : α, ∑ b : α, ∑ c : α,
          ((if a = b then M else 0) + (if a = c then M else 0) +
            (if b = c then M else 0)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact Finset.sum_le_sum fun c hc => hpoint a b c
    _ = 3 * (Fintype.card α : ℝ) ^ 2 * M := by
      simp only [Finset.sum_add_distrib]
      simp
      ring

theorem average_repeated_labels_le [Nonempty α]
    (f : α → α → α → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ a b c, f a b c ≤ M)
    (hzero : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → f a b c = 0) :
    (∑ a, ∑ b, ∑ c, f a b c) / (Fintype.card α : ℝ) ^ 3 ≤
      3 * M / (Fintype.card α : ℝ) := by
  have hcard : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ (pow_pos hcard 3)).2
  calc
    (∑ a, ∑ b, ∑ c, f a b c) ≤
        3 * (Fintype.card α : ℝ) ^ 2 * M :=
      sum_repeated_labels_le f M hM hbound hzero
    _ = 3 * M / (Fintype.card α : ℝ) * (Fintype.card α : ℝ) ^ 3 := by
      field_simp

end Problem355.Sampling

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ConditionalSmith
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.ConditionalMatrix

open scoped BigOperators

theorem arrayMatrix_map {X : Type*} {B k j : ℕ} (hjk : j ≤ k)
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (f : Fin 3 → Fin 3 → Fin k → X) :
    (arrayMatrix digit f k).map (ZMod.castHom (Nat.pow_dvd_pow B hjk) (ZMod (B ^ j))) =
      arrayMatrix digit f j := by
  ext a c
  simp only [Matrix.map_apply, arrayMatrix, map_natCast]

theorem array_moment_le_two_of_diagonal {X : Type*} [Fintype X] [Nonempty X]
    {B k : ℕ} (hB : B.Prime) (hk : 0 < k)
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (hinj : ∀ a c v, Function.Injective (digit a c v))
    (hpos : ∀ a c v x, 0 < (digit a c v x).val)
    (b e : (Fin 3 → Fin 3 → Fin k → X) → ℕ)
    (hbe : ∀ f, b f ≤ e f) (hek : ∀ f, e f ≤ k)
    (P Q : (Fin 3 → Fin 3 → Fin k → X) →
      Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hdiag : ∀ f, arrayMatrix digit f k =
      (P f : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
        Matrix.diagonal ![1, ((B ^ b f : ℕ) : ZMod (B ^ k)),
          ((B ^ e f : ℕ) : ZMod (B ^ k))] *
      (Q f : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))))
    (hsmall : (B : ℝ) * (1 / (Fintype.card X : ℝ)) ^ 4 ≤ 1 / 2) :
    (∑ f : Fin 3 → Fin 3 → Fin k → X,
      (1 / (Fintype.card (Fin 3 → Fin 3 → Fin k → X) : ℝ)) * (B : ℝ) ^ b f) ≤ 2 := by
  apply array_moment_le_two hB hk digit hinj hpos b
    (fun f => (hbe f).trans (hek f)) _ hsmall
  intro j hjpos hj f hbf
  have h := (UnitPivot.minorsVanish_reduce_prime_power_iff hB (hbe f) hj
    (P f) (Q f) (arrayMatrix digit f k) (hdiag f)).mpr hbf
  simpa only [arrayMatrix_map hj] using h

end Problem355.ConditionalMatrix

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ZModAnnihilator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355

theorem card_matrix_fixed_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) [NeZero m] (d : ι → ℕ) :
    Nat.card {A : Matrix ι ι (ZMod m) //
      A * Matrix.diagonal (fun j => (d j : ZMod m)) =
        Matrix.diagonal (fun j => (d j : ZMod m))} =
      (∏ j, Nat.gcd m (d j)) ^ Fintype.card ι := by
  rw [Nat.card_congr (matrixFixedDiagonalEquiv (fun j => (d j : ZMod m)))]
  rw [Nat.card_fun, Nat.card_pi, Nat.card_eq_fintype_card]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simpa only [mul_comm] using zmod_card_mul_eq_zero m (d j)

theorem card_matrix_fixed_diagonal_three (m D E : ℕ) [NeZero m]
    (hD : D ∣ m) (hE : E ∣ m) :
    Nat.card {A : Matrix (Fin 3) (Fin 3) (ZMod m) //
      A * Matrix.diagonal ![1, (D : ZMod m), (E : ZMod m)] =
        Matrix.diagonal ![1, (D : ZMod m), (E : ZMod m)]} = D ^ 3 * E ^ 3 := by
  have hv : (fun j : Fin 3 => (![1, D, E] j : ZMod m)) =
      ![1, (D : ZMod m), (E : ZMod m)] := by
    funext j
    fin_cases j <;> simp
  have hc := card_matrix_fixed_diagonal (ι := Fin 3) m ![1, D, E]
  rw [hv] at hc
  simpa [Fin.prod_univ_succ, Nat.gcd_eq_right hD, Nat.gcd_eq_right hE,
    mul_pow] using hc

theorem card_unit_matrix_fixed_diagonal_three_le (m D E : ℕ) [NeZero m]
    (hD : D ∣ m) (hE : E ∣ m) :
    Nat.card {A : (Matrix (Fin 3) (Fin 3) (ZMod m))ˣ //
      (A : Matrix (Fin 3) (Fin 3) (ZMod m)) *
          Matrix.diagonal ![1, (D : ZMod m), (E : ZMod m)] =
        Matrix.diagonal ![1, (D : ZMod m), (E : ZMod m)]} ≤ D ^ 3 * E ^ 3 := by
  rw [← card_matrix_fixed_diagonal_three m D E hD hE]
  apply Nat.card_le_card_of_injective (fun A => ⟨(A.1 : Matrix _ _ _), A.2⟩)
  intro A B h
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val h

end Problem355

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DiagonalDetImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.DiagonalDetImage

open Matrix

variable {R : Type*} [CommRing R]

theorem finalDiagonalUnit_fixes (D E : R) (u : Rˣ)
    (hu : ((u : R) - 1) * E = 0) :
    (finalDiagonalUnit u : Matrix (Fin 3) (Fin 3) R) * diagonalThree D E =
      diagonalThree D E := by
  have huE : (u : R) * E = E := by
    simpa [sub_mul, sub_eq_zero] using hu
  rw [finalDiagonalUnit_val, diagonalThree, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [huE]

theorem mem_determinantValues (D E : R) (u : Rˣ)
    (hu : ((u : R) - 1) * E = 0) : u ∈ determinantValues D E :=
  ⟨finalDiagonalUnit u, finalDiagonalUnit_fixes D E u hu, finalDiagonalUnit_det u⟩

theorem card_determinantValues_lower [Fintype R] (D E : R) :
    Nat.card {u : Rˣ // ((u : R) - 1) * E = 0} ≤
      Nat.card (determinantValues D E) := by
  classical
  apply Nat.card_le_card_of_injective
    (fun u => (⟨u.val, mem_determinantValues D E u.val u.property⟩ : determinantValues D E))
  intro u v h
  apply Subtype.ext
  exact congrArg (fun w : determinantValues D E => w.val) h

theorem isUnit_one_add_of_annihilates_prime_power
    {p k e : ℕ} (hp : p.Prime) (he : e < k)
    (x : ZMod (p ^ k)) (hx : x * (p ^ e : ℕ) = 0) :
    IsUnit (1 + x) := by
  have hp0 : 0 < p := hp.pos
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le e) he
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcast : ((x.val * p ^ e : ℕ) : ZMod (p ^ k)) = 0 := by
    simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using hx
  have hd : p ^ k ∣ x.val * p ^ e :=
    (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have hd' : p ^ (k - e) ∣ x.val := by
    apply Nat.dvd_of_mul_dvd_mul_right (pow_pos hp0 e)
    simpa only [← pow_add, Nat.sub_add_cancel he.le] using hd
  have hpval : p ∣ x.val :=
    (dvd_pow_self p (by omega : k - e ≠ 0)).trans hd'
  have hpnot : ¬ p ∣ 1 + x.val := by
    intro h
    have hpone : p ∣ 1 := (Nat.dvd_add_iff_left hpval).mpr h
    exact hp.not_dvd_one hpone
  have hu : IsUnit ((1 + x.val : ℕ) : ZMod (p ^ k)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk).mpr hpnot
  simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] using hu

theorem card_congruenceUnits_eq_annihilator
    {p k e : ℕ} (hp : p.Prime) (he : e < k) :
    Nat.card {u : (ZMod (p ^ k))ˣ //
      ((u : ZMod (p ^ k)) - 1) * (p ^ e : ℕ) = 0} =
    Nat.card {x : ZMod (p ^ k) // x * (p ^ e : ℕ) = 0} := by
  exact (Nat.card_congr (annihilatorEquivCongruenceUnits ((p ^ e : ℕ) : ZMod (p ^ k))
    (isUnit_one_add_of_annihilates_prime_power hp he))).symm

theorem card_congruenceUnits_prime_power
    {p k e : ℕ} (hp : p.Prime) (he : e < k) :
    Nat.card {u : (ZMod (p ^ k))ˣ //
      ((u : ZMod (p ^ k)) - 1) * (p ^ e : ℕ) = 0} = p ^ e := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [card_congruenceUnits_eq_annihilator hp he]
  simpa only [Nat.cast_pow, mul_comm] using
    Problem355.zmod_card_pow_mul_eq_zero p k e he.le

theorem determinantValues_zero (D : R) :
    determinantValues D 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro u
  exact mem_determinantValues D 0 u (by simp)

theorem card_determinantValues_prime_power_lower
    {p k e : ℕ} (hp : p.Prime) (he : e < k) (D : ZMod (p ^ k)) :
    p ^ e ≤ Nat.card (determinantValues D ((p ^ e : ℕ) : ZMod (p ^ k))) := by
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  simpa only [card_congruenceUnits_prime_power hp he] using
    card_determinantValues_lower D ((p ^ e : ℕ) : ZMod (p ^ k))

theorem card_determinantValues_ratio
    {p k e : ℕ} (hp : p.Prime) (he : e ≤ k) (D : ZMod (p ^ k)) :
    p ^ e * Nat.card (ZMod (p ^ k))ˣ ≤
      p ^ k * Nat.card (determinantValues D ((p ^ e : ℕ) : ZMod (p ^ k))) := by
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rcases he.eq_or_lt with rfl | he
  · simp only [ZMod.natCast_self, determinantValues_zero]
    rw [Nat.card_congr (Equiv.Set.univ _)]
  · have h1 := card_determinantValues_prime_power_lower hp he D
    have h2 : Nat.card (ZMod (p ^ k))ˣ ≤ p ^ k := by
      simpa only [Nat.card_zmod] using
        Nat.card_le_card_of_injective
          (fun u : (ZMod (p ^ k))ˣ => (u : ZMod (p ^ k))) Units.val_injective
    exact (Nat.mul_le_mul_left (p ^ e) h2).trans
      (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (p ^ k) h1)

theorem determinant_mem_of_diagonal_form
    (D E : R) (P Q : Matrix.GeneralLinearGroup (Fin 3) R)
    (C : Matrix (Fin 3) (Fin 3) R)
    (hC : C = (P : Matrix (Fin 3) (Fin 3) R) * diagonalThree D E *
      (Q : Matrix (Fin 3) (Fin 3) R))
    (u : Rˣ) (hu : u ∈ determinantValues D E) :
    u ∈ (MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 3) R) C).map
      Matrix.GeneralLinearGroup.det := by
  rcases hu with ⟨g, hg, hdet⟩
  apply Subgroup.mem_map.mpr
  refine ⟨P * g * P⁻¹, ?_, ?_⟩
  · apply MulAction.mem_stabilizer_iff.mpr
    change (↑(P * g * P⁻¹) : Matrix (Fin 3) (Fin 3) R) * C = C
    rw [hC]
    simp only [Units.val_mul]
    calc
      ((P : Matrix (Fin 3) (Fin 3) R) * ↑g * ↑(P⁻¹)) *
          (↑P * diagonalThree D E * ↑Q) =
          (P : Matrix (Fin 3) (Fin 3) R) *
            (↑g * diagonalThree D E) * ↑Q := by
        have hc : (↑(P⁻¹) : Matrix (Fin 3) (Fin 3) R) *
            ((↑P : Matrix (Fin 3) (Fin 3) R) * (diagonalThree D E * (Q : Matrix (Fin 3) (Fin 3) R))) =
            diagonalThree D E * (Q : Matrix (Fin 3) (Fin 3) R) := by
          rw [← Matrix.mul_assoc, P.inv_mul, Matrix.one_mul]
        simpa only [Matrix.mul_assoc] using
          congrArg (fun M : Matrix (Fin 3) (Fin 3) R =>
            (P : Matrix (Fin 3) (Fin 3) R) * ((g : Matrix (Fin 3) (Fin 3) R) * M)) hc
      _ = _ := by rw [hg]
  · simp only [map_mul, map_inv]
    rw [mul_right_comm, mul_inv_cancel, one_mul, hdet]

theorem card_stabilizer_det_image_ratio_of_diagonal_form
    {p k e : ℕ} (hp : p.Prime) (he : e ≤ k)
    (D : ZMod (p ^ k))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k)))
    (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k))) *
      diagonalThree D ((p ^ e : ℕ) : ZMod (p ^ k)) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))) :
    p ^ e * Nat.card (ZMod (p ^ k))ˣ ≤
      p ^ k * Nat.card
        ((MulAction.stabilizer
          (Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k))) C).map
            Matrix.GeneralLinearGroup.det) := by
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply (card_determinantValues_ratio hp he D).trans
  apply Nat.mul_le_mul_left
  apply Nat.card_le_card_of_injective
    (fun u : determinantValues D ((p ^ e : ℕ) : ZMod (p ^ k)) =>
      (⟨u.val, determinant_mem_of_diagonal_form D _ P Q C hC u.val u.property⟩ :
        (MulAction.stabilizer
          (Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k))) C).map
            Matrix.GeneralLinearGroup.det))
  intro u v h
  apply Subtype.ext
  exact congrArg (fun w :
    ((MulAction.stabilizer
      (Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k))) C).map
        Matrix.GeneralLinearGroup.det) => w.val) h

end Problem355.DiagonalDetImage

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.OrbitCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.OrbitCardinality

variable {G U X : Type*} [Group G] [Group U] [MulAction G X]

theorem relIndex_mul_index_comm (H N : Subgroup G) :
    H.relIndex N * N.index = H.index * N.relIndex H := by
  calc
    H.relIndex N * N.index = (H ⊓ N).index := by
      rw [← Subgroup.inf_relIndex_right H N]
      exact Subgroup.relIndex_mul_index inf_le_right
    _ = N.relIndex H * H.index := by
      rw [← Subgroup.inf_relIndex_left H N]
      exact (Subgroup.relIndex_mul_index inf_le_left).symm
    _ = H.index * N.relIndex H := Nat.mul_comm _ _

theorem stabilizer_subgroup (N : Subgroup G) (x : X) :
    (MulAction.stabilizer G x).subgroupOf N = MulAction.stabilizer N x := by
  ext g
  rfl

theorem kernel_orbit_card_mul_card (f : G →* U) (hf : Function.Surjective f) (x : X) :
    Nat.card (MulAction.orbit f.ker x) * Nat.card U =
      Nat.card (MulAction.orbit G x) * Nat.card ((MulAction.stabilizer G x).map f) := by
  have h := relIndex_mul_index_comm (MulAction.stabilizer G x) f.ker
  rw [Subgroup.relIndex, stabilizer_subgroup, MulAction.index_stabilizer,
    Subgroup.index_ker, f.range_eq_top_of_surjective hf,
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup U) ≃* U).toEquiv,
    MulAction.index_stabilizer, Subgroup.relIndex_ker] at h
  exact h

theorem card_orbit_fiber (x y : X) (hy : y ∈ MulAction.orbit G x) :
    Nat.card {g : G // g • x = y} = Nat.card (MulAction.stabilizer G x) := by
  obtain ⟨g, rfl⟩ := hy
  exact Nat.card_congr (orbitFiberEquivStabilizer x g)

theorem orbit_card_mul_stabilizer_card (x : X) :
    Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) =
      Nat.card G := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G x)

theorem orbit_bound_of_cardinal_estimates
    {o small total stab image u h D E c : ℝ}
    (ho : 0 ≤ o) (hu : 0 < u) (hh : 0 < h) (hD : 0 < D) (hE : 0 < E)
    (horbit : o * stab = total) (hkernel : small * u = o * image)
    (htotal : c * h ^ 9 ≤ total) (hstab : stab ≤ D ^ 3 * E ^ 3)
    (himage : E * u ≤ h * image) :
    c * h ^ 8 / (D ^ 3 * E ^ 2) ≤ small := by
  have hmul : (c * h ^ 8) * (h * E * u) ≤
      (small * (D ^ 3 * E ^ 2)) * (h * E * u) := by
    calc
      (c * h ^ 8) * (h * E * u) = c * h ^ 9 * (E * u) := by ring
      _ ≤ total * (E * u) := mul_le_mul_of_nonneg_right htotal (by positivity)
      _ = o * stab * (E * u) := by rw [horbit]
      _ ≤ o * (D ^ 3 * E ^ 3) * (E * u) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hstab ho
        · positivity
      _ ≤ o * (D ^ 3 * E ^ 3) * (h * image) :=
        mul_le_mul_of_nonneg_left himage (by positivity)
      _ = (o * image) * (D ^ 3 * E ^ 3) * h := by ring
      _ = (small * u) * (D ^ 3 * E ^ 3) * h := by rw [hkernel]
      _ = (small * (D ^ 3 * E ^ 2)) * (h * E * u) := by ring
  apply (div_le_iff₀ (show 0 < D ^ 3 * E ^ 2 by positivity)).2
  exact le_of_mul_le_mul_right hmul (by positivity)

theorem kernel_orbit_bound [Finite G] [Finite U]
    (f : G →* U) (hf : Function.Surjective f) (x : X)
    {h D E c : ℝ} (hh : 0 < h) (hD : 0 < D) (hE : 0 < E)
    (htotal : c * h ^ 9 ≤ (Nat.card G : ℝ))
    (hstab : (Nat.card (MulAction.stabilizer G x) : ℝ) ≤ D ^ 3 * E ^ 3)
    (himage : E * (Nat.card U : ℝ) ≤
      h * (Nat.card ((MulAction.stabilizer G x).map f) : ℝ)) :
    c * h ^ 8 / (D ^ 3 * E ^ 2) ≤ (Nat.card (MulAction.orbit f.ker x) : ℝ) := by
  have hu : (0 : ℝ) < Nat.card U := by exact_mod_cast Nat.card_pos (α := U)
  have horbit : (Nat.card (MulAction.orbit G x) : ℝ) *
      Nat.card (MulAction.stabilizer G x) = Nat.card G := by
    exact_mod_cast orbit_card_mul_stabilizer_card (G := G) x
  have hkernel : (Nat.card (MulAction.orbit f.ker x) : ℝ) * Nat.card U =
      (Nat.card (MulAction.orbit G x) : ℝ) *
        Nat.card ((MulAction.stabilizer G x).map f) := by
    exact_mod_cast kernel_orbit_card_mul_card f hf x
  exact orbit_bound_of_cardinal_estimates (Nat.cast_nonneg _) hu hh hD hE
    horbit hkernel htotal hstab himage

end Problem355.OrbitCardinality

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PrimePowerGL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PrimePowerGL

open Matrix

theorem prime_power_reflects_units (p k : ℕ) (hp : p.Prime) (hk : 0 < k)
    (x : ZMod (p ^ k)) :
    IsUnit (ZMod.castHom (dvd_pow_self p (Nat.ne_zero_of_lt hk)) (ZMod p) x) ↔
      IsUnit x := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp0⟩
  conv_rhs => rw [← ZMod.natCast_zmod_val x]
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  simp only [map_natCast]
  rw [ZMod.isUnit_iff_coprime, ZMod.isUnit_iff_coprime,
    Nat.coprime_pow_right_iff hk]

theorem card_units_of_surjective {R S : Type*} [Ring R] [Ring S]
    [Fintype R] [Fintype S] (f : R →+* S)
    (hf : Function.Surjective f) (hu : ∀ x, IsUnit (f x) → IsUnit x) :
    Nat.card Rˣ = Nat.card Sˣ * Nat.card f.toAddMonoidHom.ker := by
  classical
  let : Fintype Sˣ := Fintype.ofFinite _
  calc
    Nat.card Rˣ = ∑ y : Sˣ, Nat.card {x : R // f x = (y : S)} := by
      rw [Nat.card_congr (unitsEquivSigmaFiber f hu), Nat.card_sigma]
    _ = ∑ _ : Sˣ, Nat.card f.toAddMonoidHom.ker := by
      apply Finset.sum_congr rfl
      intro y hy
      exact Nat.card_congr (fiberEquivKer f.toAddMonoidHom hf y)
    _ = Nat.card Sˣ * Nat.card f.toAddMonoidHom.ker := by
      simp [Nat.card_eq_fintype_card]

theorem card_matrix_kernel {R S n : Type*} [Ring R] [Ring S]
    [Fintype n] [DecidableEq n] (f : R →+* S) :
    Nat.card (f.mapMatrix (m := n)).toAddMonoidHom.ker =
      Nat.card f.toAddMonoidHom.ker ^ (Fintype.card n * Fintype.card n) := by
  rw [Nat.card_congr (matrixKernelEquiv f), Nat.card_fun, Nat.card_fun,
    ← pow_mul, Nat.card_eq_fintype_card (α := n)]

theorem card_GL_of_surjective {R S n : Type*} [CommRing R] [CommRing S]
    [Fintype R] [Fintype S] [Fintype n] [DecidableEq n] (f : R →+* S)
    (hf : Function.Surjective f) (hu : ∀ x, IsUnit (f x) → IsUnit x) :
    Nat.card (GL n R) = Nat.card (GL n S) *
      Nat.card f.toAddMonoidHom.ker ^ (Fintype.card n * Fintype.card n) := by
  have hfM : Function.Surjective (f.mapMatrix (m := n)) := by
    intro A
    choose B hB using fun i j => hf (A i j)
    exact ⟨B, by ext i j; exact hB i j⟩
  have huM : ∀ A : Matrix n n R, IsUnit (f.mapMatrix A) → IsUnit A := by
    intro A hA
    rw [Matrix.isUnit_iff_isUnit_det] at hA ⊢
    apply hu
    rwa [RingHom.map_det]
  change Nat.card (Matrix n n R)ˣ = _
  rw [card_units_of_surjective (f.mapMatrix) hfM huM, card_matrix_kernel]

theorem card_prime_power_kernel (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    Nat.card (ZMod.castHom (dvd_pow_self p (Nat.ne_zero_of_lt hk))
      (ZMod p)).toAddMonoidHom.ker = p ^ (k - 1) := by
  let f := ZMod.castHom (dvd_pow_self p (Nat.ne_zero_of_lt hk)) (ZMod p)
  have hf : Function.Surjective f := ZMod.castHom_surjective _
  have hrange : f.toAddMonoidHom.range = ⊤ := AddMonoidHom.range_eq_top.mpr hf
  have h := f.toAddMonoidHom.ker.card_mul_index
  rw [AddSubgroup.index_ker, hrange] at h
  rw [Nat.card_congr AddSubgroup.topEquiv.toEquiv] at h
  simp only [Nat.card_zmod] at h
  apply Nat.eq_of_mul_eq_mul_right hp.pos
  calc
    Nat.card f.toAddMonoidHom.ker * p = p ^ k := h
    _ = p ^ (k - 1) * p := by
      rw [← pow_succ]
      congr 1
      omega

theorem card_GL_prime_power (p k : ℕ) (hp : p.Prime) (hk : 0 < k)
    (n : Type*) [Fintype n] [DecidableEq n] :
    Nat.card (GL n (ZMod (p ^ k))) =
      Nat.card (GL n (ZMod p)) * p ^ ((k - 1) * (Fintype.card n * Fintype.card n)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let f := ZMod.castHom (dvd_pow_self p (Nat.ne_zero_of_lt hk)) (ZMod p)
  rw [card_GL_of_surjective f (ZMod.castHom_surjective _) (fun x hx =>
    (prime_power_reflects_units p k hp hk x).mp hx)]
  rw [card_prime_power_kernel p k hp hk, ← pow_mul]

theorem card_GL_three_field (F : Type*) [Field F] [Fintype F] :
    Nat.card (GL (Fin 3) F) =
      (Fintype.card F ^ 3 - 1) * (Fintype.card F ^ 3 - Fintype.card F) *
        (Fintype.card F ^ 3 - Fintype.card F ^ 2) := by
  simp [Matrix.card_GL_field, Fin.prod_univ_succ, mul_assoc]

theorem card_GL_three_field_lower (F : Type*) [Field F] [Fintype F] :
    (21 / 64 : ℝ) * (Fintype.card F : ℝ) ^ 9 ≤
      (Nat.card (GL (Fin 3) F) : ℝ) := by
  let q := Fintype.card F
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hq0 : 0 < q := by omega
  have h1 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq0
  have hq3 : q ≤ q ^ 3 := Nat.le_pow (by norm_num)
  have hq23 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right hq0 (by norm_num)
  rw [card_GL_three_field]
  change (21 / 64 : ℝ) * (q : ℝ) ^ 9 ≤
    (((q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 3 - q ^ 2) : ℕ) : ℝ)
  push_cast [Nat.cast_sub h1, Nat.cast_sub hq3, Nat.cast_sub hq23]
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqnonneg : (0 : ℝ) ≤ q := by positivity
  have hpow2 : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hpow3 : (8 : ℝ) ≤ (q : ℝ) ^ 3 := by
    nlinarith [mul_le_mul hpow2 hqr (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ 2)]
  have ha : (7 / 8 : ℝ) * (q : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 - 1 := by nlinarith
  have hb : (3 / 4 : ℝ) * (q : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 - q := by
    nlinarith [mul_le_mul_of_nonneg_right hpow2 hqnonneg]
  have hc : (1 / 2 : ℝ) * (q : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 - (q : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hqr (sq_nonneg (q : ℝ))]
  calc
    (21 / 64 : ℝ) * (q : ℝ) ^ 9 =
      ((7 / 8 : ℝ) * (q : ℝ) ^ 3) * ((3 / 4 : ℝ) * (q : ℝ) ^ 3) *
        ((1 / 2 : ℝ) * (q : ℝ) ^ 3) := by ring
    _ ≤ ((q : ℝ) ^ 3 - 1) * ((q : ℝ) ^ 3 - q) *
        ((q : ℝ) ^ 3 - (q : ℝ) ^ 2) := by
      apply mul_le_mul
      · exact mul_le_mul ha hb (by positivity) (by linarith [ha])
      · exact hc
      · positivity
      · exact mul_nonneg (by linarith [ha]) (by linarith [hb])

theorem card_GL_three_prime_power_lower (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (21 / 64 : ℝ) * ((p ^ k : ℕ) : ℝ) ^ 9 ≤
      (Nat.card (GL (Fin 3) (ZMod (p ^ k))) : ℝ) := by
  have : Fact p.Prime := ⟨hp⟩
  have hfield := card_GL_three_field_lower (ZMod p)
  simp only [ZMod.card] at hfield
  rw [card_GL_prime_power p k hp hk (Fin 3)]
  simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
  norm_num only [show 3 * 3 = 9 by norm_num]
  have hpow : ((p : ℝ) ^ k) ^ 9 =
      (p : ℝ) ^ 9 * (p : ℝ) ^ ((k - 1) * 9) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hpow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hfield (by positivity)

end Problem355.PrimePowerGL

end OAI
end

section
-- module Solutions.OAIQW_Problem355.StabilizerConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355

theorem card_unit_left_stabilizer_eq {M : Type*} [Monoid M]
    (P Q : Mˣ) (D : M) :
    Nat.card {A : Mˣ // (A : M) * ((P : M) * D * (Q : M)) =
      (P : M) * D * (Q : M)} =
      Nat.card {A : Mˣ // (A : M) * D = D} :=
  (Nat.card_congr (unitLeftStabilizerEquiv P Q D)).symm

theorem card_unit_matrix_stabilizer_le_of_diagonalization
    (m D E : ℕ) [NeZero m] (hD : D ∣ m) (hE : E ∣ m)
    (C : Matrix (Fin 3) (Fin 3) (ZMod m))
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod m))ˣ)
    (hC : C = (P : Matrix _ _ _) *
      Matrix.diagonal ![1, (D : ZMod m), (E : ZMod m)] * (Q : Matrix _ _ _)) :
    Nat.card {A : (Matrix (Fin 3) (Fin 3) (ZMod m))ˣ //
      (A : Matrix (Fin 3) (Fin 3) (ZMod m)) * C = C} ≤ D ^ 3 * E ^ 3 := by
  subst C
  rw [card_unit_left_stabilizer_eq]
  exact card_unit_matrix_fixed_diagonal_three_le m D E hD hE

end Problem355

end OAI
end

section
-- module Solutions.OAIQW_Problem355.OrbitEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.Section04Orbit

open Matrix

variable {R : Type*} [CommRing R]

theorem slOrbit_eq_kernel_orbit (C : Matrix (Fin 3) (Fin 3) R) :
    slOrbit C = MulAction.orbit
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 3) R →* Rˣ).ker C := by
  ext M
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨⟨Matrix.SpecialLinearGroup.toGL g, ?_⟩, rfl⟩
    exact Matrix.SpecialLinearGroup.coeToGL_det g
  · rintro ⟨g, rfl⟩
    have hd : (g.1 : Matrix (Fin 3) (Fin 3) R).det = 1 := by
      exact congrArg Units.val g.2
    exact ⟨⟨g.1.val, hd⟩, rfl⟩

theorem slOrbit_lower_bound_of_diagonal_form
    {p k b e : ℕ} (hp : p.Prime) (hb : b ≤ k) (he : e ≤ k)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k)))
    (hC : C = (P : Matrix _ _ _) *
      Matrix.diagonal ![1, ((p ^ b : ℕ) : ZMod (p ^ k)), ((p ^ e : ℕ) : ZMod (p ^ k))] *
      (Q : Matrix _ _ _))
    {c : ℝ}
    (hGL : c * ((p ^ k : ℕ) : ℝ) ^ 9 ≤
      (Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k))) : ℝ)) :
    c * ((p ^ k : ℕ) : ℝ) ^ 8 /
      (((p ^ b : ℕ) : ℝ) ^ 3 * ((p ^ e : ℕ) : ℝ) ^ 2) ≤
        (Nat.card (slOrbit C) : ℝ) := by
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hs := Problem355.card_unit_matrix_stabilizer_le_of_diagonalization
    (p ^ k) (p ^ b) (p ^ e) (pow_dvd_pow p hb) (pow_dvd_pow p he) C P Q hC
  have hi := DiagonalDetImage.card_stabilizer_det_image_ratio_of_diagonal_form
    hp he ((p ^ b : ℕ) : ZMod (p ^ k)) P Q C hC
  rw [slOrbit_eq_kernel_orbit]
  apply OrbitCardinality.kernel_orbit_bound Matrix.GeneralLinearGroup.det
      Matrix.GeneralLinearGroup.det_surjective C
      (by exact_mod_cast pow_pos hp.pos k)
      (by exact_mod_cast pow_pos hp.pos b)
      (by exact_mod_cast pow_pos hp.pos e) hGL
  · exact_mod_cast hs
  · exact_mod_cast hi

theorem slOrbit_lower_bound
    {p k b e : ℕ} (hp : p.Prime) (hk : 0 < k) (hb : b ≤ k) (he : e ≤ k)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k)))
    (hC : C = (P : Matrix _ _ _) *
      Matrix.diagonal ![1, ((p ^ b : ℕ) : ZMod (p ^ k)), ((p ^ e : ℕ) : ZMod (p ^ k))] *
      (Q : Matrix _ _ _)) :
    (21 / 64 : ℝ) * ((p ^ k : ℕ) : ℝ) ^ 8 /
      (((p ^ b : ℕ) : ℝ) ^ 3 * ((p ^ e : ℕ) : ℝ) ^ 2) ≤
        (Nat.card (slOrbit C) : ℝ) :=
  slOrbit_lower_bound_of_diagonal_form hp hb he C P Q hC
    (PrimePowerGL.card_GL_three_prime_power_lower p k hp hk)

end Problem355.Section04Orbit

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PrimePowerData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355

namespace PrimePowerData

variable {p k : ℕ} {C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k))}

theorem orbit_lower_bound (d : PrimePowerData p k C) (hp : p.Prime) (hk : 0 < k) :
    (21 / 64 : ℝ) * ((p ^ k : ℕ) : ℝ) ^ 8 /
      (((p ^ d.b : ℕ) : ℝ) ^ 3 * ((p ^ d.e : ℕ) : ℝ) ^ 2) ≤
        (Nat.card (Section04Orbit.slOrbit C) : ℝ) :=
  Section04Orbit.slOrbit_lower_bound hp hk d.b_le_k d.e_le_k
    C d.left d.right d.diagonalization

end PrimePowerData

end Problem355

end OAI
end

section
-- module Solutions.OAIQW_Problem355.SmithDigitMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.PrimePowerData

open scoped BigOperators

theorem array_moment_le_two {X : Type*} [Fintype X] [Nonempty X]
    {B k : ℕ} (hB : B.Prime) (hk : 0 < k)
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (hinj : ∀ a c v, Function.Injective (digit a c v))
    (hpos : ∀ a c v x, 0 < (digit a c v x).val)
    (d : ∀ f : Fin 3 → Fin 3 → Fin k → X,
      PrimePowerData B k (ConditionalMatrix.arrayMatrix digit f k))
    (hsmall : (B : ℝ) * (1 / (Fintype.card X : ℝ)) ^ 4 ≤ 1 / 2) :
    (∑ f : Fin 3 → Fin 3 → Fin k → X,
      (1 / (Fintype.card (Fin 3 → Fin 3 → Fin k → X) : ℝ)) *
        (B : ℝ) ^ (d f).b) ≤ 2 := by
  exact ConditionalMatrix.array_moment_le_two_of_diagonal hB hk digit hinj hpos
    (fun f => (d f).b) (fun f => (d f).e) (fun f => (d f).b_le_e)
    (fun f => (d f).e_le_k) (fun f => (d f).left) (fun f => (d f).right)
    (fun f => (d f).diagonalization) hsmall

end Problem355.PrimePowerData

end OAI
end

section
-- module Solutions.OAIQW_Problem355.MainDigitLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT Problem355.heilbronnM

namespace Problem355.MainDigitLaw

open Parameters FiniteFieldLabels
open scoped BigOperators

variable {r : ℕ} [Fact r.Prime]

variable (D : PrimeParameterData heilbronnK r)

lemma digit_injective (label : Label r) (a : Fin 3) (v : Fin heilbronnK) :
    Function.Injective (digit D label a v) :=
  ConditionalMatrix.prescribedDigit_injective (alphabet_bound D)
    (fun i _ w => MainResidueSystem.finiteResidue r i w label) a 0 v

lemma digit_le (label : Label r) (a : Fin 3) (v : Fin heilbronnK)
    (x : Sample r) : (digit D label a v x).val ≤ r ^ 10 := by
  have hb := (DigitUnits.digitFiberEquiv_bounds
    (MainResidueSystem.finiteResidue r a v label) (r ^ 9) x).2.1
  change (digit D label a v x).val ≤ r * r ^ 9 at hb
  convert hb using 1
  ring

lemma digit_residue (label : Label r) (a : Fin 3) (v : Fin heilbronnK)
    (x : Sample r) :
    ((digit D label a v x).val : ZMod r) =
      MainResidueSystem.finiteResidue r a v label :=
  ConditionalMatrix.prescribedDigit_residue (alphabet_bound D)
    (fun i _ w => MainResidueSystem.finiteResidue r i w label) a 0 v x

omit [Fact r.Prime] in
lemma moment_parameter :
    (D.B : ℝ) * (1 / (Fintype.card (Sample r) : ℝ)) ^ 4 ≤ 1 / 2 := by
  have hr : (r : ℝ) ≠ 0 := by exact_mod_cast D.r_pos.ne'
  have hid : (r : ℝ) / (r : ℝ) ^ 10 = 1 / (r : ℝ) ^ 9 := by
    field_simp
  simpa only [Sample, Fintype.card_fin, Nat.cast_pow, hid] using D.digit_moment_bound

theorem conditional_moment (labels : Fin 3 → Label r) :
    (∑ f : Array r, DigitColumnLaw.uniformWeight (Array r) f *
      (D.B : ℝ) ^ (smith D labels f).b) ≤ 2 := by
  let : NeZero (r ^ 9) := ⟨pow_ne_zero _ D.r_pos.ne'⟩
  exact PrimePowerData.array_moment_le_two (X := Sample r) (B := D.B) (k := heilbronnK)
    D.base_prime heilbronnK_pos
    (arrayDigit D labels) (fun a c v => digit_injective D (labels c) a v)
    (fun a c v x => digit_positive D (labels c) a v x)
    (smith D labels) (moment_parameter D)

end Problem355.MainDigitLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.FiniteMixtures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.ConditionalSamples

noncomputable section

variable {α β ι : Type*}

lemma productWeight_mixture [Fintype ι] [DecidableEq ι] [Fintype β]
    (p : β → ℝ) (ν : β → α → ℝ) (x : ι → α) :
    productWeight (mixtureWeight p ν) x =
      ∑ labels : ι → β, productWeight p labels * ∏ i, ν (labels i) (x i) := by
  classical
  unfold productWeight mixtureWeight
  have h := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset β))
    (fun i b => p b * ν b (x i))
  simpa [Finset.prod_mul_distrib] using h

lemma expectation_productWeight_mixture
    [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]
    (p : β → ℝ) (ν : β → α → ℝ) (F : (ι → α) → ℝ) :
    (∑ x : ι → α, productWeight (mixtureWeight p ν) x * F x) =
      ∑ labels : ι → β, productWeight p labels *
        ∑ x : ι → α, (∏ i, ν (labels i) (x i)) * F x := by
  simp_rw [productWeight_mixture, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro labels _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end
end Problem355.ConditionalSamples

end OAI
end

section
-- module Solutions.OAIQW_Problem355.FinalScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355

theorem scaled_area_implies_power_bound
    {n r a A : ℝ} (hn : 0 < n) (hr : 64 ≤ r) (hA : 0 < A)
    (hnA : n ≤ Real.rpow r A) (harea : r ^ 2 / 64 ≤ n ^ 2 * a) :
    Real.rpow n (-2 + 1 / A) ≤ a := by
  simp only [Real.rpow_eq_pow] at hnA ⊢
  have hr0 : 0 ≤ r := by linarith
  have hroot : n ^ (1 / A) ≤ r := by
    have h := Real.rpow_le_rpow (le_of_lt hn) hnA (le_of_lt (one_div_pos.mpr hA))
    rw [← Real.rpow_mul hr0, mul_one_div_cancel (ne_of_gt hA), Real.rpow_one] at h
    exact h
  have hrsq : r ≤ r ^ 2 / 64 := by nlinarith
  rw [show -2 + 1 / A = 1 / A - 2 by ring,
    Real.rpow_sub hn, Real.rpow_two]
  apply (div_le_iff₀ (sq_pos_of_pos hn)).2
  calc
    n ^ (1 / A) ≤ r := hroot
    _ ≤ r ^ 2 / 64 := hrsq
    _ ≤ n ^ 2 * a := harea
    _ = a * n ^ 2 := mul_comm _ _

theorem scaled_area_implies_heilbronn_power
    {n r a K : ℝ} (hn : 0 < n) (hr : 64 ≤ r) (hK : 0 < K)
    (hnK : n ≤ Real.rpow r (100000 * K))
    (harea : r ^ 2 / 64 ≤ n ^ 2 * a) :
    Real.rpow n (-2 + 1 / (100000 * K)) ≤ a := by
  apply scaled_area_implies_power_bound hn hr (mul_pos (by norm_num) hK) hnK harea

theorem sample_size_scaled_area
    {n r N τ a : ℝ} (hr : 0 ≤ r) (hN : 0 < N) (hτ : 0 < τ)
    (hsample : r * Real.sqrt (N ^ 3 / τ) / 2 ≤ n)
    (harea : τ / (16 * N ^ 3) ≤ a) :
    r ^ 2 / 64 ≤ n ^ 2 * a := by
  have hsize : 0 ≤ r * Real.sqrt (N ^ 3 / τ) / 2 := by positivity
  have hsq : (r * Real.sqrt (N ^ 3 / τ) / 2) ^ 2 ≤ n ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsample) (add_nonneg hsize (hsize.trans hsample))]
  have hscale : 0 ≤ τ / (16 * N ^ 3) := by positivity
  calc
    r ^ 2 / 64 = (r * Real.sqrt (N ^ 3 / τ) / 2) ^ 2 *
        (τ / (16 * N ^ 3)) := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ N ^ 3 / τ)]
      field_simp
      ring
    _ ≤ n ^ 2 * (τ / (16 * N ^ 3)) := mul_le_mul_of_nonneg_right hsq hscale
    _ ≤ n ^ 2 * a := mul_le_mul_of_nonneg_left harea (sq_nonneg n)

end Problem355

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.Deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.Alteration

theorem exists_large_subset_avoiding {α : Type*} (S : Finset α)
    (F : Finset (Finset α)) (hne : ∀ B ∈ F, B.Nonempty) :
    ∃ T : Finset α, T ⊆ S ∧ S.card ≤ T.card + F.card ∧
      ∀ B ∈ F, ¬ B ⊆ T := by
  classical
  let chooseVertex (B : {B // B ∈ F}) : α := (hne B.1 B.2).choose
  have chooseVertex_mem (B : {B // B ∈ F}) : chooseVertex B ∈ B.1 :=
    (hne B.1 B.2).choose_spec
  let D : Finset α := F.attach.image chooseVertex
  have hD : D.card ≤ F.card := by
    calc
      D.card ≤ F.attach.card := Finset.card_image_le
      _ = F.card := Finset.card_attach
  refine ⟨S \ D, Finset.sdiff_subset, ?_, ?_⟩
  · exact (Finset.card_le_card_sdiff_add_card (s := S) (t := D)).trans (Nat.add_le_add_left hD _)
  · intro B hB hBT
    let b : {B // B ∈ F} := ⟨B, hB⟩
    have hbD : chooseVertex b ∈ D := Finset.mem_image.mpr ⟨b, Finset.mem_attach _ _, rfl⟩
    exact (Finset.mem_sdiff.mp (hBT (chooseVertex_mem b))).2 hbD

theorem exists_subset_card_eq_avoiding {α : Type*} (S : Finset α)
    (F : Finset (Finset α)) (hne : ∀ B ∈ F, B.Nonempty)
    (n : ℕ) (hbudget : n + F.card ≤ S.card) :
    ∃ T : Finset α, T ⊆ S ∧ T.card = n ∧ ∀ B ∈ F, ¬ B ⊆ T := by
  obtain ⟨U, hUS, hcard, havoid⟩ := exists_large_subset_avoiding S F hne
  have hnU : n ≤ U.card := by omega
  obtain ⟨T, hTU, hTcard⟩ := Finset.exists_subset_card_eq hnU
  exact ⟨T, hTU.trans hUS, hTcard, fun B hB hBT => havoid B hB (hBT.trans hTU)⟩

end Problem355.Alteration

end OAI
end

section
-- module Solutions.OAIQW_Problem355.SampleDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.Alteration

theorem pair_mem_collisionEdges {ι β : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → β)
    {i j : ι} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) (hf : f i = f j) :
    {i, j} ∈ collisionEdges S f := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair hij⟩, ?_⟩
  · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hi hj
  · exact ⟨i, by simp, j, by simp, hij, hf⟩

theorem triple_mem_badTripleEdges {ι β : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → β)
    (bad : β → β → β → Prop) {i j k : ι}
    (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hbad : bad (f i) (f j) (f k)) :
    {i, j, k} ∈ badTripleEdges S f bad := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨?_,
    Finset.card_triple_eq_three_iff.mpr ⟨hij, hik, hjk⟩⟩, ?_⟩
  · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hi (And.intro hj hk)
  · exact ⟨i, by simp, j, by simp, k, by simp, hij, hik, hjk, hbad⟩

theorem exists_sample_subset_avoiding {ι β : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → β)
    (bad : β → β → β → Prop) (n : ℕ)
    (hbudget : n + (collisionEdges S f).card + (badTripleEdges S f bad).card ≤ S.card) :
    ∃ T : Finset ι, T ⊆ S ∧ T.card = n ∧ Set.InjOn f (T : Set ι) ∧
      ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T,
        i ≠ j → i ≠ k → j ≠ k → ¬ bad (f i) (f j) (f k) := by
  classical
  let F := collisionEdges S f ∪ badTripleEdges S f bad
  have hne : ∀ e ∈ F, e.Nonempty := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · have hc : e.card = 2 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
      exact Finset.card_pos.mp (by omega)
    · have hc : e.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
      exact Finset.card_pos.mp (by omega)
  have hFcard : F.card ≤ (collisionEdges S f).card + (badTripleEdges S f bad).card :=
    Finset.card_union_le _ _
  obtain ⟨T, hTS, hcard, havoid⟩ :=
    exists_subset_card_eq_avoiding S F hne n (by omega)
  refine ⟨T, hTS, hcard, ?_, ?_⟩
  · intro i hi j hj hf
    change i ∈ T at hi
    change j ∈ T at hj
    by_contra hij
    have he : {i, j} ∈ F := Finset.mem_union_left _
      (pair_mem_collisionEdges S f (hTS hi) (hTS hj) hij hf)
    exact havoid _ he (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hi hj)
  · intro i hi j hj k hk hij hik hjk hbad
    have he : {i, j, k} ∈ F := Finset.mem_union_right _
      (triple_mem_badTripleEdges S f bad (hTS hi) (hTS hj) (hTS hk) hij hik hjk hbad)
    exact havoid _ he (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hi (And.intro hj hk))

end Problem355.Alteration

end OAI
end

section
-- module Solutions.OAIQW_Problem355.RandomAlteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.Alteration

theorem weighted_card_eq_sum {Ω α : Type*} [DecidableEq α] (outcomes : Finset Ω) (E : Finset α)
    (weight : Ω → ℝ) (A : Ω → Finset α)
    (hA : ∀ ω ∈ outcomes, A ω ⊆ E) :
    (∑ ω ∈ outcomes, weight ω * (A ω).card) =
      ∑ a ∈ E, ∑ ω ∈ outcomes, if a ∈ A ω then weight ω else 0 := by
  classical
  calc
    (∑ ω ∈ outcomes, weight ω * (A ω).card) =
        ∑ ω ∈ outcomes, ∑ a ∈ E, if a ∈ A ω then weight ω else 0 := by
      apply Finset.sum_congr rfl
      intro ω hω
      have hfilter : E.filter (fun a => a ∈ A ω) = A ω := by
        ext a
        simp only [Finset.mem_filter]
        exact ⟨And.right, fun ha => ⟨hA ω hω ha, ha⟩⟩
      have hcard : ((A ω).card : ℝ) = ∑ a ∈ E, if a ∈ A ω then 1 else 0 := by
        rw [Finset.sum_boole, hfilter]
      rw [hcard, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> simp
    _ = _ := Finset.sum_comm

theorem weighted_card_le {Ω α : Type*} [DecidableEq α] (outcomes : Finset Ω) (E : Finset α)
    (weight : Ω → ℝ) (A : Ω → Finset α) (bound : ℝ)
    (hA : ∀ ω ∈ outcomes, A ω ⊆ E)
    (hmarginal : ∀ a ∈ E,
      (∑ ω ∈ outcomes, if a ∈ A ω then weight ω else 0) ≤ bound) :
    (∑ ω ∈ outcomes, weight ω * (A ω).card) ≤ (E.card : ℝ) * bound := by
  classical
  rw [weighted_card_eq_sum outcomes E weight A hA]
  calc
    (∑ a ∈ E, ∑ ω ∈ outcomes, if a ∈ A ω then weight ω else 0) ≤
        ∑ _a ∈ E, bound := Finset.sum_le_sum hmarginal
    _ = _ := by simp

theorem exists_nat_lt_of_weighted_sum_lt {Ω : Type*} (outcomes : Finset Ω)
    (weight : Ω → ℝ) (g : Ω → ℕ) (m : ℕ)
    (hweight : ∀ ω ∈ outcomes, 0 ≤ weight ω)
    (hnorm : ∑ ω ∈ outcomes, weight ω = 1)
    (hmean : (∑ ω ∈ outcomes, weight ω * g ω) < (m : ℝ)) :
    ∃ ω ∈ outcomes, g ω < m := by
  by_contra hnone
  push Not at hnone
  have hle : (m : ℝ) ≤ ∑ ω ∈ outcomes, weight ω * g ω := by
    calc
      (m : ℝ) = ∑ ω ∈ outcomes, weight ω * m := by
        rw [← Finset.sum_mul, hnorm, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun ω hω =>
        mul_le_mul_of_nonneg_left (by exact_mod_cast hnone ω hω) (hweight ω hω)
  exact (not_lt_of_ge hle) hmean

theorem exists_good_sample_of_marginal_bounds {Ω ι β : Type*} [DecidableEq ι]
    (outcomes : Finset Ω) (weight : Ω → ℝ) (S : Finset ι)
    (f : Ω → ι → β) (bad : β → β → β → Prop) (n : ℕ)
    (hweight : ∀ ω ∈ outcomes, 0 ≤ weight ω)
    (hnorm : ∑ ω ∈ outcomes, weight ω = 1)
    (hn : n ≤ S.card) (p q : ℝ)
    (hpair : ∀ e ∈ S.powersetCard 2,
      (∑ ω ∈ outcomes, if e ∈ collisionEdges S (f ω) then weight ω else 0) ≤ p)
    (htriple : ∀ e ∈ S.powersetCard 3,
      (∑ ω ∈ outcomes, if e ∈ badTripleEdges S (f ω) bad then weight ω else 0) ≤ q)
    (hsmall : (Nat.choose S.card 2 : ℝ) * p + (Nat.choose S.card 3 : ℝ) * q <
      ((S.card - n + 1 : ℕ) : ℝ)) :
    ∃ ω ∈ outcomes, ∃ T : Finset ι, T ⊆ S ∧ T.card = n ∧
      Set.InjOn (f ω) (T : Set ι) ∧
      ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T,
        i ≠ j → i ≠ k → j ≠ k → ¬ bad (f ω i) (f ω j) (f ω k) := by
  classical
  have hpairMean := weighted_card_le outcomes (S.powersetCard 2) weight
    (fun ω => collisionEdges S (f ω)) p
    (fun ω _ => Finset.filter_subset _ _) hpair
  have htripleMean := weighted_card_le outcomes (S.powersetCard 3) weight
    (fun ω => badTripleEdges S (f ω) bad) q
    (fun ω _ => Finset.filter_subset _ _) htriple
  simp only [Finset.card_powersetCard] at hpairMean htripleMean
  let g : Ω → ℕ := fun ω =>
    (collisionEdges S (f ω)).card + (badTripleEdges S (f ω) bad).card
  have hmean : (∑ ω ∈ outcomes, weight ω * g ω) < ((S.card - n + 1 : ℕ) : ℝ) := by
    calc
      (∑ ω ∈ outcomes, weight ω * g ω) =
          (∑ ω ∈ outcomes, weight ω * (collisionEdges S (f ω)).card) +
          (∑ ω ∈ outcomes, weight ω * (badTripleEdges S (f ω) bad).card) := by
        simp only [g, Nat.cast_add, mul_add, Finset.sum_add_distrib]
      _ ≤ (Nat.choose S.card 2 : ℝ) * p + (Nat.choose S.card 3 : ℝ) * q :=
        add_le_add hpairMean htripleMean
      _ < _ := hsmall
  obtain ⟨ω, hω, hg⟩ := exists_nat_lt_of_weighted_sum_lt outcomes weight g
    (S.card - n + 1) hweight hnorm hmean
  have hbudget : n + (collisionEdges S (f ω)).card +
      (badTripleEdges S (f ω) bad).card ≤ S.card := by
    dsimp [g] at hg
    omega
  obtain ⟨T, hTS, hcard, hinj, hgood⟩ :=
    exists_sample_subset_avoiding S (f ω) bad n hbudget
  exact ⟨ω, hω, T, hTS, hcard, hinj, hgood⟩

end Problem355.Alteration

end OAI
end

section
-- module Solutions.OAIQW_Problem355.GeometricAlteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.Alteration

theorem image_configuration {ι : Type*} (T : Finset ι) (f : ι → Point) (a : ℝ)
    (hinj : Set.InjOn f (T : Set ι))
    (hsquare : ∀ i ∈ T, pointInUnitSquare (f i))
    (hgood : ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T,
      i ≠ j → i ≠ k → j ≠ k → ¬ smallTriangle a (f i) (f j) (f k)) :
    ∃ P : Finset Point, P.card = T.card ∧ pointsInUnitSquare P ∧
      triangleAreasAtLeast P a := by
  classical
  refine ⟨T.image f, Finset.card_image_of_injOn hinj, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact hsquare i hi
  · intro p hp q hq r hr hpq hpr hqr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
    have hij : i ≠ j := fun h => hpq (congrArg f h)
    have hik : i ≠ k := fun h => hpr (congrArg f h)
    have hjk : j ≠ k := fun h => hqr (congrArg f h)
    apply le_of_not_gt
    intro harea
    exact hgood i hi j hj k hk hij hik hjk ⟨hpq, hpr, hqr, harea⟩

theorem exists_point_configuration_of_marginal_bounds
    {Ω ι : Type*} [DecidableEq ι]
    (outcomes : Finset Ω) (weight : Ω → ℝ) (S : Finset ι)
    (f : Ω → ι → Point) (n : ℕ) (a : ℝ)
    (hweight : ∀ ω ∈ outcomes, 0 ≤ weight ω)
    (hnorm : ∑ ω ∈ outcomes, weight ω = 1)
    (hsquare : ∀ ω ∈ outcomes, ∀ i ∈ S, pointInUnitSquare (f ω i))
    (hn : n ≤ S.card) (p q : ℝ)
    (hpair : ∀ e ∈ S.powersetCard 2,
      (∑ ω ∈ outcomes, if e ∈ collisionEdges S (f ω) then weight ω else 0) ≤ p)
    (htriple : ∀ e ∈ S.powersetCard 3,
      (∑ ω ∈ outcomes,
        if e ∈ badTripleEdges S (f ω) (smallTriangle a) then weight ω else 0) ≤ q)
    (hsmall : (Nat.choose S.card 2 : ℝ) * p + (Nat.choose S.card 3 : ℝ) * q <
      ((S.card - n + 1 : ℕ) : ℝ)) :
    ∃ P : Finset Point, P.card = n ∧ pointsInUnitSquare P ∧
      triangleAreasAtLeast P a := by
  obtain ⟨ω, hω, T, hTS, hcard, hinj, hgood⟩ :=
    exists_good_sample_of_marginal_bounds outcomes weight S f (smallTriangle a) n
      hweight hnorm hn p q hpair htriple hsmall
  obtain ⟨P, hPcard, hPsquare, hParea⟩ := image_configuration T (f ω) a hinj
    (fun i hi => hsquare ω hω i (hTS hi)) hgood
  exact ⟨P, hPcard.trans hcard, hPsquare, hParea⟩

end Problem355.Alteration

end OAI
end

section
-- module Solutions.OAIQW_Problem355.SamplingErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.SamplingErrors

lemma log_bound_of_polynomial_bound {r N : ℝ} {m : ℕ}
    (hr : 1 ≤ r) (hN1 : 1 ≤ N) (hN : N ≤ r ^ m) :
    0 ≤ Real.log (2 * N) ∧ Real.log (2 * N) ≤ (m + 1 : ℝ) * r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN1
  have hlogr : Real.log r ≤ r := Real.log_le_self hr0.le
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogN : Real.log N ≤ (m : ℝ) * Real.log r := by
    simpa only [Real.log_pow] using Real.log_le_log hN0 hN
  constructor
  · apply Real.log_nonneg
    linarith
  · rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne']
    have hm : (m : ℝ) * Real.log r ≤ (m : ℝ) * r :=
      mul_le_mul_of_nonneg_left hlogr (Nat.cast_nonneg m)
    nlinarith

lemma pair_error_le {r H n : ℝ} (hr : 1 ≤ r) (hH : r ≤ H)
    (hn : n ≤ r * H ^ 15) :
    n * H ^ 6 / (H ^ 10) ^ 3 ≤ 1 / r ^ 8 := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hH0 : 0 < H := hr0.trans_le hH
  calc
    n * H ^ 6 / (H ^ 10) ^ 3 ≤
        (r * H ^ 15) * H ^ 6 / (H ^ 10) ^ 3 := by
      gcongr
    _ = r / H ^ 9 := by field_simp
    _ ≤ r / r ^ 9 := by gcongr
    _ = 1 / r ^ 8 := by field_simp

lemma triple_error_le {r N n τ h B L A : ℝ}
    (hr : 1 ≤ r) (hN : 0 < N) (ht : 0 < τ)
    (hh0 : 0 ≤ h)
    (hn : n ^ 2 * τ ≤ r ^ 2 * N ^ 3)
    (hh : h ≤ 3 * B * τ) (hB : B ≤ r ^ 31)
    (hL : L ^ 2 ≤ A ^ 2 * r ^ 2) :
    n ^ 2 * L ^ 2 * h / (N ^ 3 * r ^ 41) ≤ 3 * A ^ 2 / r ^ 6 := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hn' : n ^ 2 ≤ r ^ 2 * N ^ 3 / τ := (le_div_iff₀ ht).mpr hn
  calc
    n ^ 2 * L ^ 2 * h / (N ^ 3 * r ^ 41) ≤
        (r ^ 2 * N ^ 3 / τ) * (A ^ 2 * r ^ 2) * (3 * B * τ) /
          (N ^ 3 * r ^ 41) := by
      gcongr
    _ ≤ (r ^ 2 * N ^ 3 / τ) * (A ^ 2 * r ^ 2) * (3 * r ^ 31 * τ) /
          (N ^ 3 * r ^ 41) := by
      gcongr
    _ = 3 * A ^ 2 / r ^ 6 := by field_simp

lemma sample_le_power {r H n τ : ℝ} (hr : 1 ≤ r) (hH : r ≤ H)
    (ht : 1 ≤ τ) (hn : n ^ 2 * τ ≤ r ^ 2 * (H ^ 10) ^ 3) :
    n ≤ r * H ^ 15 := by
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr
  have hH0 : 0 ≤ H := hr0.trans hH
  have hnn : n ^ 2 ≤ n ^ 2 * τ := le_mul_of_one_le_right (sq_nonneg n) ht
  have heq : (r * H ^ 15) ^ 2 = r ^ 2 * (H ^ 10) ^ 3 := by ring
  have hpos : 0 ≤ r * H ^ 15 := by positivity
  nlinarith

lemma triple_error_log_le {r H n τ h B : ℝ} {m : ℕ}
    (hr : 1 ≤ r) (hH : r ≤ H) (ht : 1 ≤ τ) (hh0 : 0 ≤ h)
    (hn : n ^ 2 * τ ≤ r ^ 2 * (H ^ 10) ^ 3)
    (hh : h ≤ 3 * B * τ) (hB : B ≤ r ^ 31)
    (hpoly : H ^ 10 ≤ r ^ m) :
    n ^ 2 * (Real.log (2 * H ^ 10)) ^ 2 * h /
      ((H ^ 10) ^ 3 * r ^ 41) ≤ 3 * (m + 1 : ℝ) ^ 2 / r ^ 6 := by
  have hH1 : 1 ≤ H := hr.trans hH
  have hN1 : 1 ≤ H ^ 10 := one_le_pow₀ hH1
  have hlog := log_bound_of_polynomial_bound hr hN1 hpoly
  apply triple_error_le hr (lt_of_lt_of_le (by norm_num) hN1)
    (lt_of_lt_of_le (by norm_num) ht) hh0 hn hh hB
  simpa only [mul_pow] using (sq_le_sq₀ hlog.1 (by positivity)).mpr hlog.2

lemma errors_small {r A Cpair Ctriple epair etriple : ℝ}
    (hr : 1 ≤ r) (hCp : 0 ≤ Cpair) (hCt : 0 ≤ Ctriple)
    (hp : epair ≤ 1 / r ^ 8) (ht : etriple ≤ 3 * A ^ 2 / r ^ 6)
    (hlarge : 4 * Cpair + 24 * Ctriple * A ^ 2 < r) :
    4 * Cpair * epair + 8 * Ctriple * etriple < 1 := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hr8 : r ≤ r ^ 8 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hr (by norm_num : 1 ≤ 8))
  have hr6 : r ≤ r ^ 6 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hr (by norm_num : 1 ≤ 6))
  calc
    4 * Cpair * epair + 8 * Ctriple * etriple ≤
        4 * Cpair * (1 / r ^ 8) + 8 * Ctriple * (3 * A ^ 2 / r ^ 6) :=
      add_le_add (mul_le_mul_of_nonneg_left hp (by positivity))
        (mul_le_mul_of_nonneg_left ht (by positivity))
    _ = (4 * Cpair) / r ^ 8 + (24 * Ctriple * A ^ 2) / r ^ 6 := by ring
    _ ≤ (4 * Cpair) / r + (24 * Ctriple * A ^ 2) / r :=
      add_le_add (div_le_div_of_nonneg_left (by positivity) hr0 hr8)
        (div_le_div_of_nonneg_left (by positivity) hr0 hr6)
    _ = (4 * Cpair + 24 * Ctriple * A ^ 2) / r := by ring
    _ < 1 := (div_lt_one hr0).mpr hlarge

theorem relative_error_lt_one {r H n τ h B Cpair Ctriple : ℝ} {m : ℕ}
    (hr : 1 ≤ r) (hH : r ≤ H) (ht : 1 ≤ τ) (hh0 : 0 ≤ h)
    (hn : n ^ 2 * τ ≤ r ^ 2 * (H ^ 10) ^ 3)
    (hh : h ≤ 3 * B * τ) (hB : B ≤ r ^ 31)
    (hpoly : H ^ 10 ≤ r ^ m)
    (hCp : 0 ≤ Cpair) (hCt : 0 ≤ Ctriple)
    (hlarge : 4 * Cpair + 24 * Ctriple * (m + 1 : ℝ) ^ 2 < r) :
    4 * Cpair * (n * H ^ 6 / (H ^ 10) ^ 3) +
      8 * Ctriple * (n ^ 2 * (Real.log (2 * H ^ 10)) ^ 2 * h /
        ((H ^ 10) ^ 3 * r ^ 41)) < 1 := by
  exact errors_small hr hCp hCt
    (pair_error_le hr hH (sample_le_power hr hH ht hn))
    (triple_error_log_le hr hH ht hh0 hn hh hB hpoly) hlarge

end Problem355.SamplingErrors

end OAI
end

section
-- module Solutions.OAIQW_Problem355.FinalSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.FinalSampling

open Finset

lemma deletion_margin {n : ℕ} {p q : ℝ} (hn : 0 < n)
    (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hrelative : 4 * (n : ℝ) * p + 8 * (n : ℝ) ^ 2 * q < 1) :
    (Nat.choose (2 * n) 2 : ℝ) * p + (Nat.choose (2 * n) 3 : ℝ) * q <
      ((2 * n - n + 1 : ℕ) : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc2 : (Nat.choose (2 * n) 2 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by
    have hc : (Nat.choose (2 * n) 2 : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast Nat.choose_le_pow (2 * n) 2
    norm_num [mul_pow] at hc
    exact hc
  have hc3 : (Nat.choose (2 * n) 3 : ℝ) ≤ 8 * (n : ℝ) ^ 3 := by
    have hc : (Nat.choose (2 * n) 3 : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ 3 := by
      exact_mod_cast Nat.choose_le_pow (2 * n) 3
    norm_num [mul_pow] at hc
    exact hc
  calc
    (Nat.choose (2 * n) 2 : ℝ) * p + (Nat.choose (2 * n) 3 : ℝ) * q ≤
        4 * (n : ℝ) ^ 2 * p + 8 * (n : ℝ) ^ 3 * q :=
      add_le_add (mul_le_mul_of_nonneg_right hc2 hp)
        (mul_le_mul_of_nonneg_right hc3 hq)
    _ = (4 * (n : ℝ) * p + 8 * (n : ℝ) ^ 2 * q) * n := by ring
    _ < (n : ℝ) := by simpa using mul_lt_mul_of_pos_right hrelative hn0
    _ < ((2 * n - n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show n < 2 * n - n + 1 by omega)

end Problem355.FinalSampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AlterationAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

open Filter
open scoped Topology

namespace Problem355

theorem sample_half_le_nat_floor {a : ℝ} (ha : 2 ≤ a) :
    a / 2 ≤ (⌊a⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one a
  linarith

theorem floor_sample_properties {α : Type*} {l : Filter α} {a : α → ℝ}
    (ha : Tendsto a l atTop) :
    Tendsto (fun i => ⌊a i⌋₊) l atTop ∧
      (∀ᶠ i in l, 3 ≤ ⌊a i⌋₊ ∧ a i / 2 ≤ (⌊a i⌋₊ : ℝ)) := by
  have hf : Tendsto (fun i => ⌊a i⌋₊) l atTop := tendsto_nat_floor_atTop.comp ha
  refine ⟨hf, ?_⟩
  filter_upwards [hf.eventually_ge_atTop 3, ha.eventually_ge_atTop 2] with i hi hi'
  exact ⟨hi, sample_half_le_nat_floor hi'⟩

theorem tendsto_real_sample_atTop
    {α : Type*} {l : Filter α} {r N τ : α → ℝ}
    (hr : Tendsto r l atTop)
    (hscale : ∀ᶠ i in l, 0 < τ i ∧ τ i ≤ (N i) ^ 3) :
    Tendsto (fun i => r i * Real.sqrt ((N i) ^ 3 / τ i)) l atTop := by
  apply tendsto_atTop_mono' l ?_ hr
  filter_upwards [hr.eventually_ge_atTop 0, hscale] with i hri hi
  have hratio : (1 : ℝ) ≤ (N i) ^ 3 / τ i :=
    (le_div_iff₀ hi.1).2 (by simpa using hi.2)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt ((N i) ^ 3 / τ i) := by
    simpa using Real.sqrt_le_sqrt hratio
  simpa using mul_le_mul_of_nonneg_left hsqrt hri

theorem sample_floor_square_bound
    {r N τ : ℝ} (hr : 0 ≤ r) (hN : 0 ≤ N) (hτ : 0 < τ) :
    (⌊r * Real.sqrt (N ^ 3 / τ)⌋₊ : ℝ) ^ 2 * τ ≤ r ^ 2 * N ^ 3 := by
  have ha : 0 ≤ r * Real.sqrt (N ^ 3 / τ) := by positivity
  have hf := Nat.floor_le ha
  have hf0 : 0 ≤ (⌊r * Real.sqrt (N ^ 3 / τ)⌋₊ : ℝ) := Nat.cast_nonneg _
  have hsq : (⌊r * Real.sqrt (N ^ 3 / τ)⌋₊ : ℝ) ^ 2 ≤
      (r * Real.sqrt (N ^ 3 / τ)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hf) (add_nonneg ha hf0)]
  calc
    (⌊r * Real.sqrt (N ^ 3 / τ)⌋₊ : ℝ) ^ 2 * τ ≤
        (r * Real.sqrt (N ^ 3 / τ)) ^ 2 * τ :=
      mul_le_mul_of_nonneg_right hsq hτ.le
    _ = r ^ 2 * N ^ 3 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ N ^ 3 / τ)]
      field_simp

end Problem355

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.FinalScalingBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355

theorem triangleAreasAtLeast_of_scaled
    {P : Finset Point} {n : ℕ} {r : ℝ} (hn : 3 ≤ n) (hr : 64 ≤ r)
    (hsize : (n : ℝ) ≤ Real.rpow r (100000 * (heilbronnK : ℝ)))
    (harea : ∀ p ∈ P, ∀ q ∈ P, ∀ s ∈ P,
      p ≠ q → p ≠ s → q ≠ s →
        r ^ 2 / 64 ≤ (n : ℝ) ^ 2 * triangleArea p q s) :
    triangleAreasAtLeast P (Real.rpow (n : ℝ) (-2 + heilbronnExponent)) := by
  have hK : 0 < (heilbronnK : ℝ) := by
    by_contra h
    have he : 100000 * (heilbronnK : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_gt h)
    have hp : Real.rpow r (100000 * (heilbronnK : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) he
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  intro p hp q hq s hs hpq hps hqs
  exact scaled_area_implies_heilbronn_power hn0 hr hK hsize
    (harea p hp q hq s hs hpq hps hqs)

theorem heilbronn_power_lower_bound_of_scaled_configurations
    (hconfig : ∀ m : ℕ, ∃ n : ℕ, ∃ P : Finset Point, ∃ r : ℝ,
      m ≤ n ∧ 3 ≤ n ∧ P.card = n ∧ pointsInUnitSquare P ∧
      64 ≤ r ∧ (n : ℝ) ≤ Real.rpow r (100000 * (heilbronnK : ℝ)) ∧
      (∀ p ∈ P, ∀ q ∈ P, ∀ s ∈ P,
        p ≠ q → p ≠ s → q ≠ s →
          r ^ 2 / 64 ≤ (n : ℝ) ^ 2 * triangleArea p q s)) :
    0 < heilbronnExponent ∧
      ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point,
        Filter.Tendsto n Filter.atTop Filter.atTop ∧
        ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧
          triangleAreasAtLeast (P j)
            (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
  obtain ⟨n₀, P₀, r₀, _, hn₀, _, _, hr₀, hsize₀, _⟩ := hconfig 0
  have hK : 0 < (heilbronnK : ℝ) := by
    by_contra h
    have he : 100000 * (heilbronnK : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_gt h)
    have hp : Real.rpow r₀ (100000 * (heilbronnK : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) he
    have hn' : (3 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
    linarith
  refine ⟨one_div_pos.mpr (mul_pos (by norm_num) hK), ?_⟩
  choose n P r hlarge hthree hcard hsquare hr hsize harea using hconfig
  refine ⟨n, P, Filter.tendsto_atTop_mono hlarge Filter.tendsto_id, ?_⟩
  intro j
  refine ⟨hthree j, hcard j, hsquare j, ?_⟩
  exact triangleAreasAtLeast_of_scaled (hthree j) (hr j) (hsize j) (harea j)

theorem heilbronn_power_lower_bound_of_floor_configurations
    (r N τ : ℕ → ℝ)
    (hr : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hscale : ∀ᶠ j in Filter.atTop, 0 < N j ∧ 0 < τ j ∧ τ j ≤ (N j) ^ 3)
    (hsize : ∀ᶠ j in Filter.atTop,
      (⌊r j * Real.sqrt ((N j) ^ 3 / τ j)⌋₊ : ℝ) ≤
        Real.rpow (r j) (100000 * (heilbronnK : ℝ)))
    (hconfig : ∀ᶠ j in Filter.atTop, ∃ P : Finset Point,
      P.card = ⌊r j * Real.sqrt ((N j) ^ 3 / τ j)⌋₊ ∧
      pointsInUnitSquare P ∧ triangleAreasAtLeast P (τ j / (16 * (N j) ^ 3))) :
    0 < heilbronnExponent ∧
      ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point,
        Filter.Tendsto n Filter.atTop Filter.atTop ∧
        ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧
          triangleAreasAtLeast (P j)
            (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
  have ha : Filter.Tendsto (fun j => r j * Real.sqrt ((N j) ^ 3 / τ j))
      Filter.atTop Filter.atTop := tendsto_real_sample_atTop hr (hscale.mono fun _ hj => hj.2)
  obtain ⟨hn, hfloor⟩ := floor_sample_properties ha
  apply heilbronn_power_lower_bound_of_scaled_configurations
  intro m
  have hevent := (hn.eventually_ge_atTop m).and
    (hfloor.and ((hr.eventually_ge_atTop 64).and (hscale.and (hsize.and hconfig))))
  obtain ⟨j, hm, ⟨hthree, hhalf⟩, hr64, ⟨hN, hτ, hτN⟩, hbound, P, hcard,
      hsquare, harea⟩ := hevent.exists
  refine ⟨⌊r j * Real.sqrt ((N j) ^ 3 / τ j)⌋₊, P, r j,
    hm, hthree, hcard, hsquare, hr64, hbound, ?_⟩
  intro p hp q hq s hs hpq hps hqs
  exact sample_size_scaled_area (by linarith) hN hτ hhalf
    (harea p hp q hq s hs hpq hps hqs)

end Problem355

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.SampleUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.Parameters

lemma sqrt_cube_div_le_square {N tau : ℝ} (hN : 1 ≤ N) (htau : 1 ≤ tau) :
    Real.sqrt (N ^ 3 / tau) ≤ N ^ 2 := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨sq_nonneg N, ?_⟩
  calc
    N ^ 3 / tau ≤ N ^ 3 := div_le_self (by positivity) htau
    _ ≤ N ^ 4 := pow_le_pow_right₀ hN (by norm_num)
    _ = (N ^ 2) ^ 2 := by ring

lemma sample_size_le_nat_power {n r N tau : ℝ} {k : ℕ}
    (hr : 1 ≤ r) (hN : 1 ≤ N) (htau : 1 ≤ tau) (hk : 1 ≤ k)
    (hbox : N ≤ r ^ (31620 * k))
    (hsample : n ≤ r * Real.sqrt (N ^ 3 / tau)) :
    n ≤ r ^ (100000 * k) := by
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr
  calc
    n ≤ r * Real.sqrt (N ^ 3 / tau) := hsample
    _ ≤ r * N ^ 2 := mul_le_mul_of_nonneg_left (sqrt_cube_div_le_square hN htau) hr0
    _ ≤ r * (r ^ (31620 * k)) ^ 2 := by gcongr
    _ = r ^ (63240 * k + 1) := by
      rw [← pow_mul]
      have he : 31620 * k * 2 = 63240 * k := by omega
      rw [he, pow_succ]
      ring
    _ ≤ r ^ (100000 * k) := pow_le_pow_right₀ hr (by omega)

lemma sample_size_le_real_power {n r N tau : ℝ} {k : ℕ}
    (hr : 1 ≤ r) (hN : 1 ≤ N) (htau : 1 ≤ tau) (hk : 1 ≤ k)
    (hbox : N ≤ r ^ (31620 * k))
    (hsample : n ≤ r * Real.sqrt (N ^ 3 / tau)) :
    n ≤ Real.rpow r (100000 * (k : ℝ)) := by
  have he : (100000 : ℝ) * (k : ℝ) = ((100000 * k : ℕ) : ℝ) := by norm_cast
  simp only [Real.rpow_eq_pow]
  rw [he, Real.rpow_natCast]
  exact sample_size_le_nat_power hr hN htau hk hbox hsample

end Problem355.Parameters

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ParameterConclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Parameters

namespace PrimeParameterData

variable {k r : ℕ}

lemma sampleCard_le_power (P : PrimeParameterData k r) :
    (P.sampleCard : ℝ) ≤ Real.rpow (r : ℝ) (100000 * (k : ℝ)) := by
  have hr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast P.r_pos
  obtain ⟨hN, ht, _, _, hbox⟩ := P.real_bounds
  apply sample_size_le_real_power hr hN ht (by have := P.two_le_k; omega) hbox
  exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg r) (Real.sqrt_nonneg _))

end PrimeParameterData

theorem heilbronn_power_lower_bound_of_parameter_configurations
    {r : ℕ → ℕ} (D : (j : ℕ) → PrimeParameterData heilbronnK (r j))
    (hr : Filter.Tendsto r Filter.atTop Filter.atTop)
    (hconfig : ∀ᶠ j in Filter.atTop, ∃ P : Finset Point,
      P.card = (D j).sampleCard ∧ pointsInUnitSquare P ∧
      triangleAreasAtLeast P ((D j).tau / (16 * ((D j).N : ℝ) ^ 3))) :
    0 < heilbronnExponent ∧
      ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point,
        Filter.Tendsto n Filter.atTop Filter.atTop ∧
        ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧
          triangleAreasAtLeast (P j)
            (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
  have hrR : Filter.Tendsto (fun j => (r j : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hr
  apply heilbronn_power_lower_bound_of_floor_configurations
    (fun j => (r j : ℝ)) (fun j => ((D j).N : ℝ))
    (fun j => ((D j).tau : ℝ)) hrR
  · exact Filter.Eventually.of_forall fun j =>
      ⟨Nat.cast_pos.mpr (D j).N_pos, Nat.cast_pos.mpr (D j).tau_pos,
        (D j).real_bounds.2.2.1⟩
  · exact Filter.Eventually.of_forall fun j => (D j).sampleCard_le_power
  · exact hconfig

theorem heilbronn_power_lower_bound_of_large_prime_configurations
    (hconstruction : ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → r.Prime → Odd r →
      ∀ D : PrimeParameterData heilbronnK r, ∃ P : Finset Point,
        P.card = D.sampleCard ∧ pointsInUnitSquare P ∧
        triangleAreasAtLeast P (D.tau / (16 * (D.N : ℝ) ^ 3))) :
    0 < heilbronnExponent ∧
      ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point,
        Filter.Tendsto n Filter.atTop Filter.atTop ∧
        ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧
          triangleAreasAtLeast (P j)
            (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
  obtain ⟨r0, hconstruction⟩ := hconstruction
  obtain ⟨r, D, hr, hprime⟩ := exists_heilbronn_parameter_sequence
  apply heilbronn_power_lower_bound_of_parameter_configurations D hr
  filter_upwards [hr.eventually_ge_atTop r0] with j hj
  exact hconstruction (r j) hj (hprime j).1 (hprime j).2.1 (D j)

end Problem355.Parameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.SharedGeometricAlteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


open Finset

noncomputable section

namespace Problem355.SharedGeometricAlteration

lemma triangleArea_swap_left (p q r : Point) : triangleArea p q r = triangleArea q p r := by
  unfold triangleArea
  have h : (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) =
      -((p.1 - q.1) * (r.2 - q.2) - (p.2 - q.2) * (r.1 - q.1)) := by ring
  rw [h, abs_neg]

lemma triangleArea_swap_right (p q r : Point) : triangleArea p q r = triangleArea p r q := by
  unfold triangleArea
  have h : (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) =
      -((r.1 - p.1) * (q.2 - p.2) - (r.2 - p.2) * (q.1 - p.1)) := by ring
  rw [h, abs_neg]

lemma pair_collision_iff {I : Type*} [DecidableEq I] (S : Finset I) (f : I → Point)
    {i j : I} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    {i, j} ∈ Alteration.collisionEdges S f ↔ f i = f j := by
  classical
  constructor
  · intro h
    simp only [Alteration.collisionEdges, mem_filter] at h
    obtain ⟨u, hu, v, hv, huv, he⟩ := h.2
    simp only [mem_insert, mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> aesop
  · exact Alteration.pair_mem_collisionEdges S f hi hj hij

lemma triple_bad_iff {I : Type*} [DecidableEq I] (S : Finset I) (f : I → Point)
    (a : ℝ) {i j k : I} (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    {i, j, k} ∈ Alteration.badTripleEdges S f (Alteration.smallTriangle a) ↔
      Alteration.smallTriangle a (f i) (f j) (f k) := by
  classical
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, w, hw, huv, huw, hvw, he⟩ := (mem_filter.mp h).2
    simp only [mem_insert, mem_singleton] at hu hv hw
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
      rcases hw with rfl | rfl | rfl <;>
      simp_all [Alteration.smallTriangle, ne_comm, triangleArea_swap_left, triangleArea_swap_right]
  · exact Alteration.triple_mem_badTripleEdges S f (Alteration.smallTriangle a)
      hi hj hk hij hik hjk

variable {Θ X : Type*} [Fintype Θ] [Fintype X]

theorem exists_configuration (m n : ℕ) (hn : n ≤ m) (a p q : ℝ)
    (ρ : Θ → ℝ) (μ : Θ → X → ℝ) (point : Θ → X → Point)
    (hρ0 : ∀ θ, 0 ≤ ρ θ) (hρ1 : ∑ θ, ρ θ = 1)
    (hμ0 : ∀ θ x, 0 ≤ μ θ x) (hμ1 : ∀ θ, ∑ x, μ θ x = 1)
    (hsquare : ∀ θ x, pointInUnitSquare (point θ x))
    (hpair : pairMass ρ μ point ≤ p) (htriple : tripleMass ρ μ point a ≤ q)
    (hbudget : (Nat.choose m 2 : ℝ) * p + (Nat.choose m 3 : ℝ) * q <
      ((m - n + 1 : ℕ) : ℝ)) :
    ∃ P : Finset Point, P.card = n ∧ pointsInUnitSquare P ∧ triangleAreasAtLeast P a := by
  classical
  let W : Θ × (Fin m → X) → ℝ := ConditionalSamples.sharedWeight ρ μ
  let f : (Θ × (Fin m → X)) → Fin m → Point := fun z i => point z.1 (z.2 i)
  apply Alteration.exists_point_configuration_of_marginal_bounds
    (univ : Finset (Θ × (Fin m → X))) W (univ : Finset (Fin m)) f n a
    (fun z _ => ConditionalSamples.sharedWeight_nonneg ρ μ hρ0 hμ0 z)
    (ConditionalSamples.sum_sharedWeight ρ μ hρ1 hμ1)
    (fun z _ i _ => hsquare z.1 (z.2 i)) (by simpa using hn) p q
  · intro e he
    obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp (mem_powersetCard.mp he).2
    have hiff (z : Θ × (Fin m → X)) :
        {i, j} ∈ Alteration.collisionEdges univ (f z) ↔
          point z.1 (z.2 i) = point z.1 (z.2 j) :=
      pair_collision_iff univ (f z) (mem_univ i) (mem_univ j) hij
    have hm := ConditionalSamples.shared_pair_marginal ρ μ hμ1 hij
      (fun θ x y => if point θ x = point θ y then (1 : ℝ) else 0)
    have heq : (∑ z : Θ × (Fin m → X),
        if {i, j} ∈ Alteration.collisionEdges univ (f z) then W z else 0) =
          pairMass ρ μ point := by
      simp_rw [hiff]
      simpa only [W, pairMass, mul_ite, mul_one, mul_zero] using hm
    exact heq.trans_le hpair
  · intro e he
    obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := card_eq_three.mp (mem_powersetCard.mp he).2
    have hiff (z : Θ × (Fin m → X)) :
        {i, j, k} ∈ Alteration.badTripleEdges univ (f z) (Alteration.smallTriangle a) ↔
          Alteration.smallTriangle a (point z.1 (z.2 i)) (point z.1 (z.2 j))
            (point z.1 (z.2 k)) :=
      triple_bad_iff univ (f z) a (mem_univ i) (mem_univ j) (mem_univ k) hij hik hjk
    have hm := ConditionalSamples.shared_triple_marginal ρ μ hμ1 hij hik hjk
      (fun θ x y z => if Alteration.smallTriangle a (point θ x) (point θ y) (point θ z)
        then (1 : ℝ) else 0)
    have heq : (∑ z : Θ × (Fin m → X),
        if {i, j, k} ∈ Alteration.badTripleEdges univ (f z) (Alteration.smallTriangle a)
          then W z else 0) = tripleMass ρ μ point a := by
      simp_rw [hiff]
      simpa only [W, tripleMass, mul_ite, mul_one, mul_zero] using hm
    exact heq.trans_le htriple
  · simpa using hbudget

end Problem355.SharedGeometricAlteration

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ParameterSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.ParameterSampling

open Parameters Parameters.PrimeParameterData

attribute [instance] PointLaw.environmentFintype PointLaw.columnFintype

lemma r_le_sampleCard {k r : ℕ} (D : PrimeParameterData k r) : r ≤ D.sampleCard := by
  have ht : (0 : ℝ) < D.tau := by exact_mod_cast D.tau_pos
  have hratio : (1 : ℝ) ≤ (D.N : ℝ) ^ 3 / D.tau :=
    (le_div_iff₀ ht).2 (by simpa using D.real_bounds.2.2.1)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt ((D.N : ℝ) ^ 3 / D.tau) := by
    simpa using Real.sqrt_le_sqrt hratio
  apply Nat.le_floor
  simpa using mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg r)

lemma relative_error_lt_one {k r : ℕ} (D : PrimeParameterData k r)
    {Cp Ct : ℝ} (hCp : 0 ≤ Cp) (hCt : 0 ≤ Ct)
    (hlarge : 4 * Cp + 24 * Ct * (31620 * k + 1 : ℝ) ^ 2 < r) :
    4 * (D.sampleCard : ℝ) * (Cp * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3) +
      8 * (D.sampleCard : ℝ) ^ 2 *
        (Ct * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
          ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41)) < 1 := by
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast D.r_pos
  have hM : (r : ℝ) ≤ D.M := by exact_mod_cast D.r_le_M
  have ht : (1 : ℝ) ≤ D.tau := D.real_bounds.2.1
  have hN : (D.N : ℝ) = (D.M : ℝ) ^ 10 := by simp only [N, Nat.cast_pow]
  have hs : (D.sampleCard : ℝ) ^ 2 * D.tau ≤ (r : ℝ) ^ 2 * ((D.M : ℝ) ^ 10) ^ 3 := by
    rw [← hN]
    exact sample_floor_square_bound (Nat.cast_nonneg r) (Nat.cast_nonneg D.N)
      (by exact_mod_cast D.tau_pos)
  have hh : (D.h : ℝ) ≤ 3 * (D.B : ℝ) * D.tau := by
    exact_mod_cast power_le_three_base_threshold D.base_ge_three D.two_le_k
  have hb : (D.B : ℝ) ≤ (r : ℝ) ^ 31 := by exact_mod_cast D.base_polynomial
  have hp : (D.M : ℝ) ^ 10 ≤ (r : ℝ) ^ (31620 * k) := by
    rw [← hN]
    exact D.real_bounds.2.2.2.2
  have hl : 4 * Cp + 24 * Ct * ((31620 * k : ℕ) + 1 : ℝ) ^ 2 < r := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlarge
  have he := SamplingErrors.relative_error_lt_one hr hM ht (Nat.cast_nonneg D.h)
    hs hh hb hp hCp hCt hl
  rw [← hN] at he
  convert he using 1; ring

theorem configuration_of_law {k r : ℕ} (D : PrimeParameterData k r)
    (L : PointLaw) {Cp Ct : ℝ} (hCp : 0 ≤ Cp) (hCt : 0 ≤ Ct)
    (hlarge : 4 * Cp + 24 * Ct * (31620 * k + 1 : ℝ) ^ 2 < r)
    (hpair : L.pairProbability ≤ Cp * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3)
    (htriple : L.tripleProbability (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
      Ct * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h / ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41)) :
    ∃ P : Finset Point, P.card = D.sampleCard ∧ pointsInUnitSquare P ∧
      triangleAreasAtLeast P (D.tau / (16 * (D.N : ℝ) ^ 3)) := by
  have hn : 0 < D.sampleCard := D.r_pos.trans_le (r_le_sampleCard D)
  have hbudget := FinalSampling.deletion_margin hn
    (show 0 ≤ Cp * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3 by positivity)
    (show 0 ≤ Ct * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
      ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41) by positivity)
    (relative_error_lt_one D hCp hCt hlarge)
  exact SharedGeometricAlteration.exists_configuration (2 * D.sampleCard) D.sampleCard
    (by omega) _ _ _ L.rho L.mu L.point L.rho_nonneg L.rho_sum L.mu_nonneg L.mu_sum
    L.in_square hpair htriple hbudget

theorem heilbronn_power_lower_bound_of_point_laws
    (Cp Ct : ℝ) (hCp : 0 ≤ Cp) (hCt : 0 ≤ Ct)
    (hconstruction : ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → r.Prime → Odd r →
      ∀ D : PrimeParameterData heilbronnK r, ∃ L : PointLaw,
        L.pairProbability ≤ Cp * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3 ∧
        L.tripleProbability (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
          Ct * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
            ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41)) :
    0 < heilbronnExponent ∧
      ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point,
        Filter.Tendsto n Filter.atTop Filter.atTop ∧
        ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧
          triangleAreasAtLeast (P j)
            (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
  obtain ⟨r0, hc⟩ := hconstruction
  obtain ⟨r1, hr1⟩ := exists_nat_gt
    (4 * Cp + 24 * Ct * (31620 * (heilbronnK : ℝ) + 1) ^ 2)
  apply heilbronn_power_lower_bound_of_large_prime_configurations
  refine ⟨max r0 r1, ?_⟩
  intro r hr hp ho D
  obtain ⟨L, hpair, htriple⟩ := hc r ((le_max_left _ _).trans hr) hp ho D
  have hlarge : 4 * Cp + 24 * Ct * (31620 * (heilbronnK : ℝ) + 1) ^ 2 < r :=
    hr1.trans_le (by exact_mod_cast (le_max_right r0 r1).trans hr)
  exact configuration_of_law D L hCp hCt hlarge hpair htriple

end Problem355.ParameterSampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.GcdPairCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.GcdPairCount

open Finset

lemma sum_dvd_indicator (M d c : ℕ) :
    (∑ s ∈ Ioc 0 M, if d ∣ s then c else 0) = (M / d) * c := by
  rw [← Finset.sum_filter]
  simp [Nat.Ioc_filter_dvd_card_eq_div]

lemma common_divisor_square_sum (M d : ℕ) :
    (∑ s ∈ Ioc 0 M, ∑ t ∈ Ioc 0 M,
      if d ∣ s ∧ d ∣ t then d ^ 2 else 0) = (d * (M / d)) ^ 2 := by
  simp_rw [ite_and]
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp_rw [sum_dvd_indicator]
  ring

theorem sum_gcd_sq_le_cube (M : ℕ) :
    (∑ s ∈ Ioc 0 M, ∑ t ∈ Ioc 0 M, (Nat.gcd s t) ^ 2) ≤ M ^ 3 := by
  have hpoint (s : ℕ) (hs : s ∈ Ioc 0 M) (t : ℕ) (ht : t ∈ Ioc 0 M) :
      (Nat.gcd s t) ^ 2 ≤ ∑ d ∈ Ioc 0 M,
        if d ∣ s ∧ d ∣ t then d ^ 2 else 0 := by
    have hs' := Finset.mem_Ioc.mp hs
    have hg : Nat.gcd s t ∈ Ioc 0 M := by
      exact Finset.mem_Ioc.mpr ⟨Nat.gcd_pos_of_pos_left t hs'.1,
        (Nat.gcd_le_left t hs'.1).trans hs'.2⟩
    have h := Finset.single_le_sum
      (f := fun d => if d ∣ s ∧ d ∣ t then d ^ 2 else 0)
      (fun _ _ => Nat.zero_le _) hg
    simpa [Nat.gcd_dvd_left, Nat.gcd_dvd_right] using h
  calc
    (∑ s ∈ Ioc 0 M, ∑ t ∈ Ioc 0 M, (Nat.gcd s t) ^ 2)
        ≤ ∑ s ∈ Ioc 0 M, ∑ t ∈ Ioc 0 M, ∑ d ∈ Ioc 0 M,
            if d ∣ s ∧ d ∣ t then d ^ 2 else 0 := by
      exact Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun t ht => hpoint s hs t ht
    _ = ∑ s ∈ Ioc 0 M, ∑ d ∈ Ioc 0 M, ∑ t ∈ Ioc 0 M,
          if d ∣ s ∧ d ∣ t then d ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_comm
    _ = ∑ d ∈ Ioc 0 M, ∑ s ∈ Ioc 0 M, ∑ t ∈ Ioc 0 M,
          if d ∣ s ∧ d ∣ t then d ^ 2 else 0 := Finset.sum_comm
    _ = ∑ d ∈ Ioc 0 M, (d * (M / d)) ^ 2 := by
      exact Finset.sum_congr rfl fun d hd => common_divisor_square_sum M d
    _ ≤ ∑ d ∈ Ioc 0 M, M ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.pow_le_pow_left (Nat.mul_div_le M d) 2
    _ = M ^ 3 := by simp [pow_succ, Nat.mul_comm]

end Problem355.GcdPairCount

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ProportionalPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


open Finset

noncomputable section

namespace Problem355.ProportionalPairs

theorem proportional_parameter (a b x y : ℕ) (ha : 0 < a) (_hb : 0 < b)
    (hx : x < a) (hxy : a * y = b * x) :
    ∃ k < Nat.gcd a b,
      x = (a / Nat.gcd a b) * k ∧ y = (b / Nat.gcd a b) * k := by
  let g := Nat.gcd a b
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hag : g * (a / g) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hbg : g * (b / g) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hap : 0 < a / g := by nlinarith
  have hxy' : (a / g) * y = (b / g) * x := by
    apply Nat.mul_left_cancel hg
    simpa only [← mul_assoc, hag, hbg] using hxy
  have hd : a / g ∣ x :=
    (Nat.coprime_div_gcd_div_gcd hg).dvd_of_dvd_mul_left
      ⟨y, hxy'.symm⟩
  obtain ⟨k, hk⟩ := hd
  refine ⟨k, ?_, hk, ?_⟩
  · nlinarith
  · apply Nat.mul_left_cancel hap
    rw [hxy', hk]
    ring

theorem card_coordinate_pairs_le_gcd (N a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hNa : N ≤ a) :
    ((range N ×ˢ range N).filter fun p : ℕ × ℕ => a * p.2 = b * p.1).card ≤
      Nat.gcd a b := by
  let S := (range N ×ˢ range N).filter fun p : ℕ × ℕ => a * p.2 = b * p.1
  let g := Nat.gcd a b
  let f : ℕ × ℕ → ℕ := fun p => p.1 / (a / g)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hag : g * (a / g) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hap : 0 < a / g := by nlinarith
  have hparam (p : ℕ × ℕ) (hp : p ∈ S) :
      ∃ k < g, p.1 = (a / g) * k ∧ p.2 = (b / g) * k := by
    have hp' := mem_filter.mp hp
    have hxp := mem_range.mp (mem_product.mp hp'.1).1
    exact proportional_parameter a b p.1 p.2 ha hb (lt_of_lt_of_le hxp hNa) hp'.2
  have hf (p : ℕ × ℕ) (hp : p ∈ S) : f p < g := by
    obtain ⟨k, hk, hx, hy⟩ := hparam p hp
    simpa only [f, hx, Nat.mul_div_right _ hap] using hk
  have hinj : Set.InjOn f ↑S := by
    intro p hp q hq hpq
    obtain ⟨k, hk, hx, hy⟩ := hparam p hp
    obtain ⟨l, hl, qx, qy⟩ := hparam q hq
    have hkl : k = l := by
      simpa only [f, hx, qx, Nat.mul_div_right _ hap] using hpq
    apply Prod.ext <;> simp_all
  simpa only [card_range] using
    (Finset.card_le_card_of_injOn f (fun p hp => mem_range.mpr (hf p hp)) hinj)

theorem sum_gcd_sq_le_cube_of_subset (M : ℕ) (H : Finset ℕ)
    (hH : H ⊆ Ico 1 (M + 1)) :
    (∑ a ∈ H, ∑ b ∈ H, Nat.gcd a b ^ 2) ≤ M ^ 3 := by
  calc
    _ ≤ ∑ a ∈ H, ∑ b ∈ Ico 1 (M + 1), Nat.gcd a b ^ 2 := by
      exact sum_le_sum fun a _ => sum_le_sum_of_subset hH
    _ ≤ ∑ a ∈ Ico 1 (M + 1), ∑ b ∈ Ico 1 (M + 1), Nat.gcd a b ^ 2 :=
      sum_le_sum_of_subset hH
    _ ≤ M ^ 3 := by
      have heq : Ico 1 (M + 1) = Ioc 0 M := by
        ext a
        simp only [mem_Ico, mem_Ioc]
        omega
      rw [heq]
      exact GcdPairCount.sum_gcd_sq_le_cube M

theorem card_proportionalPairParameters_le (N : ℕ) (hN : 0 < N) :
    (proportionalPairParameters N).card ≤ 8 * N ^ 3 := by
  have hH : Ico N (2 * N) ⊆ Ico 1 (2 * N + 1) := by
    intro a ha
    simp only [mem_Ico] at ha ⊢
    omega
  calc
    _ = ∑ a ∈ Ico N (2 * N), ∑ b ∈ Ico N (2 * N),
        (coordinatePairs N a b).card ^ 2 := by
      simp only [proportionalPairParameters, card_sigma, card_product, pow_two]
    _ ≤ ∑ a ∈ Ico N (2 * N), ∑ b ∈ Ico N (2 * N), Nat.gcd a b ^ 2 := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      apply Nat.pow_le_pow_left
      exact card_coordinate_pairs_le_gcd N a b
        (lt_of_lt_of_le hN (mem_Ico.mp ha).1)
        (lt_of_lt_of_le hN (mem_Ico.mp hb).1) (mem_Ico.mp ha).1
    _ ≤ (2 * N) ^ 3 := sum_gcd_sq_le_cube_of_subset (2 * N) _ hH
    _ = 8 * N ^ 3 := by ring

theorem card_proportionalPairs_le (N : ℕ) (hN : 0 < N) :
    (proportionalPairs N).card ≤ 8 * N ^ 3 := by
  let f : NatColumn × NatColumn → Σ _a : ℕ, Σ _b : ℕ, (ℕ × ℕ) × (ℕ × ℕ) :=
    fun p => ⟨p.1.2, p.2.2, (p.1.1.1, p.2.1.1), (p.1.1.2, p.2.1.2)⟩
  have hf : Set.MapsTo f ↑(proportionalPairs N) ↑(proportionalPairParameters N) := by
    intro p hp
    change p ∈ proportionalPairs N at hp
    change f p ∈ proportionalPairParameters N
    have hfilter := Finset.mem_filter.mp hp
    have hpairs := Finset.mem_product.mp hfilter.1
    have hleft := Finset.mem_product.mp hpairs.1
    have hright := Finset.mem_product.mp hpairs.2
    have hleftCoords := Finset.mem_product.mp hleft.1
    have hrightCoords := Finset.mem_product.mp hright.1
    simp only [f, proportionalPairParameters, mem_sigma, mem_product,
      coordinatePairs, mem_filter]
    exact ⟨hleft.2, hright.2,
      ⟨⟨hleftCoords.1, hrightCoords.1⟩, hfilter.2.1⟩,
      ⟨⟨hleftCoords.2, hrightCoords.2⟩, hfilter.2.2⟩⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨⟨px, py⟩, pz⟩, ⟨⟨qx, qy⟩, qz⟩⟩
      ⟨⟨⟨rx, ry⟩, rz⟩, ⟨⟨sx, sy⟩, sz⟩⟩ h
    simp only [f, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at h ⊢
    tauto
  exact (card_le_card_of_injOn f hf hinj.injOn).trans
    (card_proportionalPairParameters_le N hN)

theorem project_eq_iff_proportional (u v : NatColumn) (hu : 0 < u.2) (hv : 0 < v.2) :
    project u = project v ↔ Proportional u v := by
  have hu' : (u.2 : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have hv' : (v.2 : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  simp only [project, Prod.mk.injEq, div_eq_div_iff hu' hv', Proportional]
  constructor
  · rintro ⟨hx, hy⟩
    norm_cast at hx hy
    constructor <;> nlinarith
  · rintro ⟨hx, hy⟩
    constructor
    · exact_mod_cast (show u.1.1 * v.2 = v.1.1 * u.2 by nlinarith)
    · exact_mod_cast (show u.1.2 * v.2 = v.1.2 * u.2 by nlinarith)

theorem card_equal_projection_pairs_le (N : ℕ) (hN : 0 < N) :
    ((columnBox N ×ˢ columnBox N).filter fun p => project p.1 = project p.2).card ≤
      8 * N ^ 3 := by
  classical
  have heq : ((columnBox N ×ˢ columnBox N).filter fun p => project p.1 = project p.2) =
      proportionalPairs N := by
    ext p
    simp only [mem_filter, proportionalPairs]
    constructor
    · rintro ⟨hp, he⟩
      have hp' := mem_product.mp hp
      have hu := (mem_product.mp hp'.1).2
      have hv := (mem_product.mp hp'.2).2
      exact ⟨hp, (project_eq_iff_proportional _ _
        (lt_of_lt_of_le hN (mem_Ico.mp hu).1)
        (lt_of_lt_of_le hN (mem_Ico.mp hv).1)).mp he⟩
    · rintro ⟨hp, he⟩
      have hp' := mem_product.mp hp
      have hu := (mem_product.mp hp'.1).2
      have hv := (mem_product.mp hp'.2).2
      exact ⟨hp, (project_eq_iff_proportional _ _
        (lt_of_lt_of_le hN (mem_Ico.mp hu).1)
        (lt_of_lt_of_le hN (mem_Ico.mp hv).1)).mpr he⟩
  rw [heq]
  exact card_proportionalPairs_le N hN

end Problem355.ProportionalPairs

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LiftCollisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


open Finset

noncomputable section

namespace Problem355.LiftCollisions

lemma nonneg_of_inBox {N : ℕ} {u : Column} (hu : InBox N u) : ∀ i, 0 ≤ u i := by
  intro i
  fin_cases i <;> dsimp <;> simp only [InBox] at hu <;> omega

lemma intColumn_natColumn {u : Column} (hu : ∀ i, 0 ≤ u i) :
    intColumn (natColumn u) = u := by
  funext i
  fin_cases i <;> simp [intColumn, natColumn, Int.toNat_of_nonneg (hu _)]

lemma natColumn_mem_box {N : ℕ} {u : Column} (hu : InBox N u) :
    natColumn u ∈ ProportionalPairs.columnBox N := by
  simp only [natColumn, ProportionalPairs.columnBox, mem_product, mem_range, mem_Ico]
  simp only [InBox] at hu
  omega

lemma project_intColumn (u : ProportionalPairs.NatColumn) :
    project (intColumn u) = ProportionalPairs.project u := by
  simp [project, intColumn, ProportionalPairs.project]

lemma project_natColumn {u : Column} (hu : ∀ i, 0 ≤ u i) :
    ProportionalPairs.project (natColumn u) = project u := by
  rw [← project_intColumn, intColumn_natColumn hu]

theorem card_equal_projection_pairs_le (N : ℕ) (hN : 0 < N)
    (U V : Finset Column) (hU : ∀ u ∈ U, InBox N u) (hV : ∀ v ∈ V, InBox N v) :
    ((U ×ˢ V).filter fun p => project p.1 = project p.2).card ≤ 8 * N ^ 3 := by
  classical
  let f : Column × Column → ProportionalPairs.NatColumn × ProportionalPairs.NatColumn :=
    fun p => (natColumn p.1, natColumn p.2)
  let T := ((ProportionalPairs.columnBox N ×ˢ ProportionalPairs.columnBox N).filter
    fun p => ProportionalPairs.project p.1 = ProportionalPairs.project p.2)
  let S := ((U ×ˢ V).filter fun p => project p.1 = project p.2)
  have hf : Set.MapsTo f ↑S ↑T := by
    intro p hp
    change p ∈ S at hp
    change f p ∈ T
    obtain ⟨hp, he⟩ := mem_filter.mp hp
    obtain ⟨hu, hv⟩ := mem_product.mp hp
    have hbu := hU p.1 hu
    have hbv := hV p.2 hv
    exact mem_filter.mpr ⟨mem_product.mpr ⟨natColumn_mem_box hbu, natColumn_mem_box hbv⟩,
      by simpa only [f, project_natColumn (nonneg_of_inBox hbu),
        project_natColumn (nonneg_of_inBox hbv)] using he⟩
  have hi : Set.InjOn f ↑S := by
    intro p hp q hq hpq
    change p ∈ S at hp
    change q ∈ S at hq
    have hp' := mem_product.mp (mem_filter.mp hp).1
    have hq' := mem_product.mp (mem_filter.mp hq).1
    have h1 := congrArg (fun z => intColumn z.1) hpq
    have h2 := congrArg (fun z => intColumn z.2) hpq
    simp only [f, intColumn_natColumn (nonneg_of_inBox (hU _ hp'.1)),
      intColumn_natColumn (nonneg_of_inBox (hU _ hq'.1))] at h1
    simp only [f, intColumn_natColumn (nonneg_of_inBox (hV _ hp'.2)),
      intColumn_natColumn (nonneg_of_inBox (hV _ hq'.2))] at h2
    exact Prod.ext h1 h2
  exact (card_le_card_of_injOn f hf hi).trans
    (ProportionalPairs.card_equal_projection_pairs_le N hN)

end Problem355.LiftCollisions

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegerSamplingPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem355.IntegerSamplingPairs

open LiftCollisions

theorem collisionMass_le {X : Type*} [Fintype X]
    (col : X → Column) (hcol : Function.Injective col)
    (N Q L : ℕ) (hQ : 0 < Q) (hL : 0 < L) (hN : N = Q * L)
    (hbox : ∀ x, InBox N (col x)) (p q : X → ℝ)
    (hq0 : ∀ x, 0 ≤ q x)
    (hp : ∀ x, p x ≤ 1 / (L : ℝ) ^ 3)
    (hq : ∀ x, q x ≤ 1 / (L : ℝ) ^ 3) :
    collisionMass col p q ≤ 8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
  classical
  let U := Finset.univ.image col
  let S : Finset (X × X) := Finset.univ.filter
    (fun z => project (col z.1) = project (col z.2))
  let T := (U ×ˢ U).filter (fun z => project z.1 = project z.2)
  let f : X × X → Column × Column := fun z => (col z.1, col z.2)
  have hf : Set.MapsTo f ↑S ↑T := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨z.1, Finset.mem_univ _, rfl⟩,
       Finset.mem_image.mpr ⟨z.2, Finset.mem_univ _, rfl⟩⟩,
      (Finset.mem_filter.mp hz).2⟩
  have hi : Set.InjOn f ↑S := by
    intro a ha b hb hab
    exact Prod.ext (hcol (congrArg Prod.fst hab)) (hcol (congrArg Prod.snd hab))
  have hU : ∀ u ∈ U, InBox N u := by
    intro u hu
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
    exact hbox x
  have hNpos : 0 < N := by rw [hN]; positivity
  have hcount : (S.card : ℝ) ≤ 8 * (N : ℝ) ^ 3 := by
    exact_mod_cast (Finset.card_le_card_of_injOn f hf hi).trans
      (card_equal_projection_pairs_le N hNpos U U hU hU)
  have hsum : collisionMass col p q = ∑ z ∈ S, p z.1 * q z.2 := by
    simp only [collisionMass, S, Finset.sum_filter, Fintype.sum_prod_type]
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hQne : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  rw [hsum]
  calc
    (∑ z ∈ S, p z.1 * q z.2) ≤
        ∑ _z ∈ S, (1 / (L : ℝ) ^ 3) * (1 / (L : ℝ) ^ 3) := by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul (hp z.1) (hq z.2) (hq0 z.2) (by positivity)
    _ = (S.card : ℝ) * ((1 / (L : ℝ) ^ 3) * (1 / (L : ℝ) ^ 3)) := by simp
    _ ≤ (8 * (N : ℝ) ^ 3) * ((1 / (L : ℝ) ^ 3) * (1 / (L : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
      rw [hN]
      push_cast
      field_simp

theorem conditionalColumnMass_le {X A B : Type*}
    (f : X → A) (g : X → B) (a : A) (V : Finset B)
    (s L : ℕ) (hs : 0 < s) (x : X) :
    LiftingProbability.conditionalColumnMass f g a V s L x ≤ 1 / (L : ℝ) ^ 3 := by
  classical
  unfold LiftingProbability.conditionalColumnMass
  split_ifs
  · have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
    by_cases hL : L = 0
    · simp [hL]
    · apply one_div_le_one_div_of_le (by positivity)
      nlinarith [pow_nonneg (Nat.cast_nonneg L : (0 : ℝ) ≤ L) 3]
  · positivity

theorem mixture_mass_le {I X : Type*} [Fintype I]
    (w : I → ℝ) (p : I → X → ℝ) (C : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hp : ∀ i x, p i x ≤ C) (x : X) :
    (∑ i, w i * p i x) ≤ C := by
  calc
    (∑ i, w i * p i x) ≤ ∑ i, w i * C :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hp i x) (hw0 i))
    _ = C := by rw [← Finset.sum_mul, hw, one_mul]

theorem collisionMass_eq_finTwo {X : Type*} [Fintype X]
    (col : X → Column) (p : X → ℝ) :
    collisionMass col p p =
      ∑ x : Fin 2 → X, (∏ i, p (x i)) *
        (if project (col (x 0)) = project (col (x 1)) then 1 else 0) := by
  classical
  symm
  calc
    _ = ∑ z : X × X,
        if project (col z.1) = project (col z.2) then p z.1 * p z.2 else 0 := by
      apply Fintype.sum_equiv (finTwoArrowEquiv X)
      intro x
      simp only [Fin.prod_univ_two]
      change (p (x 0) * p (x 1)) * (if _ then 1 else 0) = _
      split_ifs <;> simp_all
    _ = collisionMass col p p := by
      simp only [collisionMass, Fintype.sum_prod_type]

theorem boxColumn_injective (N : ℕ) :
    Function.Injective (@boxColumn N) := by
  intro x y h
  funext i
  exact Subtype.ext (congrFun h i)

theorem boxColumn_inBox {N : ℕ}
    (x : IntegerSampling.Box N 3 (IntegerSampling.samplingShift N)) :
    InBox N (boxColumn x) := by
  have hx := (x 0).property
  have hy := (x 1).property
  have hz : (N : ℤ) ≤ (x 2).val ∧ (x 2).val < (N : ℤ) + N := (x 2).property
  simp [IntegerSampling.samplingShift] at hx hy
  change 0 ≤ (x 0).val ∧ (x 0).val < N ∧ 0 ≤ (x 1).val ∧ (x 1).val < N ∧
    (N : ℤ) ≤ (x 2).val ∧ (x 2).val < 2 * N
  omega

theorem box_finTwo_collision_le (N Q L : ℕ)
    (hQ : 0 < Q) (hL : 0 < L) (hN : N = Q * L)
    (p : IntegerSampling.Box N 3 (IntegerSampling.samplingShift N) → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp : ∀ x, p x ≤ 1 / (L : ℝ) ^ 3) :
    (∑ x : Fin 2 → IntegerSampling.Box N 3 (IntegerSampling.samplingShift N),
      (∏ i, p (x i)) *
        (if IntegerSampling.project (x 0) = IntegerSampling.project (x 1) then 1 else 0)) ≤
      8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
  have H := collisionMass_le boxColumn (boxColumn_injective N)
    N Q L hQ hL hN boxColumn_inBox p p hp0 hp hp
  rw [collisionMass_eq_finTwo] at H
  simp only [project_boxColumn] at H
  convert H using 1
  congr 1

end Problem355.IntegerSamplingPairs

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegerSharedCollisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.IntegerSamplingPairs

theorem pairMass_eq_average {Θ X : Type*} [Fintype Θ] [Fintype X]
    (rho : Θ → ℝ) (mu : Θ → X → ℝ) (point : Θ → X → Point) :
    SharedGeometricAlteration.pairMass rho mu point =
      ∑ θ, rho θ * ∑ x : Fin 2 → X, (∏ i, mu θ (x i)) *
        (if point θ (x 0) = point θ (x 1) then 1 else 0) := by
  classical
  simp only [SharedGeometricAlteration.pairMass, Fintype.sum_prod_type,
    ConditionalSamples.sharedWeight, ConditionalSamples.productWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ hθ
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

theorem shared_box_pairMass_le {Θ : Type*} [Fintype Θ]
    (N Q L : ℕ) (hQ : 0 < Q) (hL : 0 < L) (hN : N = Q * L)
    (rho : Θ → ℝ)
    (mu : Θ → IntegerSampling.Box N 3 (IntegerSampling.samplingShift N) → ℝ)
    (hrho0 : ∀ θ, 0 ≤ rho θ) (hrho : ∑ θ, rho θ = 1)
    (hmu0 : ∀ θ x, 0 ≤ mu θ x)
    (hmu : ∀ θ x, mu θ x ≤ 1 / (L : ℝ) ^ 3) :
    SharedGeometricAlteration.pairMass rho mu (fun _ => IntegerSampling.project) ≤
      8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3 := by
  rw [pairMass_eq_average]
  calc
    _ ≤ ∑ θ, rho θ * (8 * (Q : ℝ) ^ 6 / (N : ℝ) ^ 3) := by
      apply Finset.sum_le_sum
      intro θ hθ
      apply mul_le_mul_of_nonneg_left _ (hrho0 θ)
      exact box_finTwo_collision_le N Q L hQ hL hN (mu θ) (hmu0 θ) (hmu θ)
    _ = _ := by rw [← Finset.sum_mul, hrho, one_mul]

theorem shared_mixture_columnLaw_pairMass_le {Θ I : Type*}
    [Fintype Θ] [Fintype I]
    (h q L : ℕ) (hh : 0 < h) (hq : 0 < q) (hL : 0 < L)
    (rho : Θ → ℝ) (hrho0 : ∀ θ, 0 ≤ rho θ) (hrho : ∑ θ, rho θ = 1)
    (w : Θ → I → ℝ) (hw0 : ∀ θ i, 0 ≤ w θ i) (hw : ∀ θ, ∑ i, w θ i = 1)
    (a : Θ → I → Fin 3 → ZMod h)
    (V : Θ → I → Finset (Fin 3 → ZMod q))
    (s : Θ → I → ℕ) (hs : ∀ θ i, 0 < s θ i) :
    SharedGeometricAlteration.pairMass rho
      (fun θ x => ∑ i, w θ i * IntegerSampling.columnLaw h q L
        (IntegerSampling.samplingShift (L * (h * q))) (a θ i) (V θ i) (s θ i) x)
      (fun _ => IntegerSampling.project) ≤
      8 * ((h * q : ℕ) : ℝ) ^ 6 / ((L * (h * q) : ℕ) : ℝ) ^ 3 := by
  apply shared_box_pairMass_le _ (h * q) L (Nat.mul_pos hh hq) hL
    (Nat.mul_comm _ _) rho _ hrho0 hrho
  · intro θ x
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 θ i)
      (IntegerSampling.columnLaw_nonneg h q L _ (a θ i) (V θ i) (s θ i) x))
  · intro θ
    apply mixture_mass_le (w θ) _ _ (hw0 θ) (hw θ)
    intro i x
    exact conditionalColumnMass_le _ _ (a θ i) (V θ i) (s θ i) L (hs θ i) x

end Problem355.IntegerSamplingPairs

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegerPointLawPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.IntegerPointLaw

open IntegerSampling ConditionalSamples ParameterSampling

theorem ofMixture_pairProbability_le {Θ D : Type} [Fintype Θ] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (rho : Θ → ℝ) (p : D → ℝ)
    (a : Θ → D → Fin 3 → ZMod h)
    (V : Θ → Finset (Fin 3 → ZMod q))
    (hrho : ∀ θ, 0 ≤ rho θ) (hsum : ∑ θ, rho θ = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ θ, (V θ).card = s) :
    (ofMixture h q L s hc hL hs rho p a V hrho hsum hp hpsum hV).pairProbability ≤
      8 * ((h * q : ℕ) : ℝ) ^ 6 / ((L * (h * q) : ℕ) : ℝ) ^ 3 := by
  exact IntegerSamplingPairs.shared_mixture_columnLaw_pairMass_le
    h q L (NeZero.pos h) (NeZero.pos q) hL rho hrho hsum
    (fun _ => p) (fun _ => hp) (fun _ => hpsum) a (fun θ _ => V θ)
    (fun _ _ => s) (fun _ _ => hs)

theorem ofSpecialLinear_pairProbability_le {Ω D : Type}
    [Fintype Ω] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ ω, (V ω).card = s) :
    (ofSpecialLinear h q L s hc hL hs w p c V hw hwsum hp hpsum hV).pairProbability ≤
      8 * ((h * q : ℕ) : ℝ) ^ 6 / ((L * (h * q) : ℕ) : ℝ) ^ 3 := by
  unfold ofSpecialLinear ofIndependentEnvironments
  apply ofMixture_pairProbability_le

end Problem355.IntegerPointLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PrimeLiftParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Parameters.PrimeParameterData

variable {k r : ℕ} (D : PrimeParameterData k r)

lemma liftMultiplicity_mul_moduli :
    D.liftMultiplicity * (D.h * D.q) = D.N := by
  change D.M ^ 9 * D.M = D.M ^ 10
  exact (pow_succ D.M 9).symm

end Problem355.Parameters.PrimeParameterData

namespace Problem355.PrimeLiftParameters

open Parameters Parameters.PrimeParameterData ParameterSampling

variable {k r : ℕ}

theorem pairProbability_le (D : PrimeParameterData k r)
    {Ω Δ : Type} [Fintype Ω] [Fintype Δ]
    (s : ℕ) (hs : 0 < s)
    (w : Ω → ℝ) (p : Δ → ℝ)
    (c : Δ → Fin 3 → ZMod D.h)
    (V : Ω → Finset (Fin 3 → ZMod D.q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ δ, 0 ≤ p δ) (hpsum : ∑ δ, p δ = 1)
    (hV : ∀ ω, (V ω).card = s) :
    (pointLaw D s hs w p c V hw hwsum hp hpsum hV).pairProbability ≤
      8 * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3 := by
  let : NeZero D.h := ⟨ne_of_gt D.h_pos⟩
  let : NeZero D.q := ⟨D.auxiliary_prime.ne_zero⟩
  have hpair := IntegerPointLaw.ofSpecialLinear_pairProbability_le
    D.h D.q D.liftMultiplicity s D.coprime D.liftMultiplicity_pos hs
    w p c V hw hwsum hp hpsum hV
  simpa only [pointLaw, D.liftMultiplicity_mul_moduli, M] using hpair

end Problem355.PrimeLiftParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ActualPointLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT Problem355.heilbronnM

namespace Problem355.ActualPointLaw

open Parameters FiniteFieldLabels

section WithAuxiliary
variable {r : ℕ} [Fact r.Prime] [Fintype (Label r)]

theorem withAuxiliary_pairProbability_le
    (D : PrimeParameterData heilbronnK r)
    [Fact D.q.Prime] (A : AuxiliarySampling.Law D.q (D.h ^ 2)) :
    (withAuxiliary D A).pairProbability ≤
      8 * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3 := by
  unfold withAuxiliary
  apply PrimeLiftParameters.pairProbability_le

end WithAuxiliary

variable {r : ℕ} [Fact r.Prime]

theorem pairProbability_le (D : PrimeParameterData heilbronnK r) :
    (pointLaw D).pairProbability ≤ 8 * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3 := by
  let : Fintype (Label r) := Fintype.ofFinite (Label r)
  let : Fact D.q.Prime := ⟨D.auxiliary_prime⟩
  unfold pointLaw
  apply withAuxiliary_pairProbability_le

end Problem355.ActualPointLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.BadTripleAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.Sampling

open Finset

variable {α Ω : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype Ω]

theorem lifting_weighted_count_bound
    {h N D E orbit c₀ C L mass : ℝ}
    (hh : 0 < h) (hN : 0 < N) (hD : 0 < D) (hE : 0 < E)
    (ho : 0 < orbit) (hc₀ : 0 < c₀)
    (hmass : 0 ≤ mass)
    (horbit : c₀ * h ^ 8 / (D ^ 3 * E ^ 2) ≤ orbit)
    (hcount : mass ≤ C * L ^ 2 * N ^ 6 / (D ^ 2 * E ^ 2)) :
    h ^ 9 / (N ^ 9 * orbit) * mass ≤
      (C / c₀) * L ^ 2 * h * D / N ^ 3 := by
  have hinv : 1 / orbit ≤ (D ^ 3 * E ^ 2) / (c₀ * h ^ 8) := by
    apply (div_le_div_iff₀ ho (by positivity)).2
    have hl := (div_le_iff₀ (by positivity : 0 < D ^ 3 * E ^ 2)).1 horbit
    simpa only [one_mul, mul_one, mul_comm] using hl
  calc
    h ^ 9 / (N ^ 9 * orbit) * mass = (h ^ 9 / N ^ 9) * (1 / orbit) * mass := by
      ring
    _ ≤ (h ^ 9 / N ^ 9) * ((D ^ 3 * E ^ 2) / (c₀ * h ^ 8)) * mass :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv (by positivity)) hmass
    _ ≤ (h ^ 9 / N ^ 9) * ((D ^ 3 * E ^ 2) / (c₀ * h ^ 8)) *
        (C * L ^ 2 * N ^ 6 / (D ^ 2 * E ^ 2)) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = (C / c₀) * L ^ 2 * h * D / N ^ 3 := by
      field_simp

end Problem355.Sampling

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DigitBadTripleAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.DigitBadTripleAverage

open scoped BigOperators
open DigitColumnLaw

lemma injective_labels {Λ : Type*} {a b c : Λ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (![a, b, c] : Fin 3 → Λ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

end Problem355.DigitBadTripleAverage

namespace Problem355.DigitColumnLaw

open scoped BigOperators

theorem expectation_labels_le_of_repeated
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]
    (F : (Fin 3 → Λ) → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ l, F l ≤ M)
    (hzero : ∀ l, l 0 ≠ l 1 → l 0 ≠ l 2 → l 1 ≠ l 2 → F l = 0) :
    (∑ l : Fin 3 → Λ, uniformWeight (Fin 3 → Λ) l * F l) ≤
      3 * M / (Fintype.card Λ : ℝ) := by
  have h := Sampling.average_repeated_labels_le
    (fun a b c => F ![a, b, c]) M hM
    (fun a b c => hbound _) (fun a b c hab hac hbc => hzero _ hab hac hbc)
  have hs : (∑ l : Fin 3 → Λ, F l) = ∑ a, ∑ b, ∑ c, F ![a, b, c] := by
    calc
      _ = ∑ t : Λ × Λ × Λ, F ((labelsEquiv Λ).symm t) :=
        (labelsEquiv Λ).symm.sum_comp F |>.symm
      _ = _ := by simp only [Fintype.sum_prod_type]; rfl
  have he : (∑ l : Fin 3 → Λ, uniformWeight (Fin 3 → Λ) l * F l) =
      (∑ l : Fin 3 → Λ, F l) / (Fintype.card Λ : ℝ) ^ 3 := by
    unfold uniformWeight
    rw [← Finset.mul_sum]
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    ring
  rw [he, hs]
  exact h

theorem expectation_triple_le_of_repeated
    {Λ X : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] [Fintype X] {k : ℕ}
    (F : (Fin 3 → Λ) → Array X k → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ l, (∑ f : Array X k, uniformWeight (Array X k) f * F l f) ≤ M)
    (hzero : ∀ l f, l 0 ≠ l 1 → l 0 ≠ l 2 → l 1 ≠ l 2 → F l f = 0) :
    (∑ s : Fin 3 → Latent Λ X k,
      ConditionalSamples.productWeight (uniformWeight (Latent Λ X k)) s *
        F (tripleEquiv s).1 (tripleEquiv s).2) ≤
      3 * M / (Fintype.card Λ : ℝ) := by
  rw [expectation_triple]
  apply expectation_labels_le_of_repeated _ M hM hbound
  intro l hab hac hbc
  simp only [hzero l _ hab hac hbc, mul_zero, Finset.sum_const_zero]

theorem bad_triple_expectation_le
    {Λ X : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] [Fintype X] {k : ℕ}
    (D : (Fin 3 → Λ) → Array X k → ℝ)
    (p : (Fin 3 → Latent Λ X k) → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hmoment : ∀ l, (∑ f : Array X k, uniformWeight (Array X k) f * D l f) ≤ 2)
    (hbound : ∀ l f, p (tripleEquiv.symm (l, f)) ≤ A * D l f)
    (hzero : ∀ s, (s 0).1 ≠ (s 1).1 → (s 0).1 ≠ (s 2).1 →
      (s 1).1 ≠ (s 2).1 → p s = 0) :
    (∑ s : Fin 3 → Latent Λ X k,
      ConditionalSamples.productWeight (uniformWeight (Latent Λ X k)) s * p s) ≤
      6 * A / (Fintype.card Λ : ℝ) := by
  have h := expectation_triple_le_of_repeated
    (fun l f => p (tripleEquiv.symm (l, f))) (A * 2) (by positivity)
    (by
      intro l
      calc
        _ ≤ ∑ f : Array X k, uniformWeight (Array X k) f * (A * D l f) :=
          Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_left
            (hbound l f) (uniformWeight_nonneg _ f)
        _ = A * ∑ f : Array X k, uniformWeight (Array X k) f * D l f := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro f _
          ring
        _ ≤ A * 2 := mul_le_mul_of_nonneg_left (hmoment l) hA)
    (by intro l f hab hac hbc; exact hzero _ hab hac hbc)
  simpa only [Prod.mk.eta, Equiv.symm_apply_apply,
    show 3 * (A * 2) = 6 * A by ring] using h

end Problem355.DigitColumnLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.OrbitUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.OrbitUniform

variable {G X : Type*} [Group G] [MulAction G X]

theorem orbit_fiber_probability [Finite G] (x y : X)
    (hy : y ∈ MulAction.orbit G x) :
    (Nat.card {g : G // g • x = y} : ℝ) / Nat.card G =
      1 / Nat.card (MulAction.orbit G x) := by
  rw [OrbitCardinality.card_orbit_fiber x y hy,
    ← OrbitCardinality.orbit_card_mul_stabilizer_card (G := G) x, Nat.cast_mul]
  have hs : (Nat.card (MulAction.stabilizer G x) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := MulAction.stabilizer G x)).ne'
  rw [mul_comm (Nat.card (MulAction.orbit G x) : ℝ), div_mul_eq_div_div,
    div_self hs]

theorem uniform_mass_eq_fiber_probability [Fintype G] [DecidableEq X] (x y : X) :
    (∑ g : G, if g • x = y then (1 / (Nat.card G : ℝ)) else 0) =
      (Nat.card {g : G // g • x = y} : ℝ) / Nat.card G := by
  classical
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    mul_one_div]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem uniform_mass_of_mem_orbit [Fintype G] [DecidableEq X] (x y : X)
    (hy : y ∈ MulAction.orbit G x) :
    (∑ g : G, if g • x = y then (1 / (Nat.card G : ℝ)) else 0) =
      1 / Nat.card (MulAction.orbit G x) := by
  rw [uniform_mass_eq_fiber_probability]
  exact orbit_fiber_probability x y hy

theorem uniform_mass_of_not_mem_orbit [Fintype G] [DecidableEq X] (x y : X)
    (hy : y ∉ MulAction.orbit G x) :
    (∑ g : G, if g • x = y then (1 / (Nat.card G : ℝ)) else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro g _
  apply ite_eq_right
  intro hg
  exact hy ⟨g, hg⟩

end Problem355.OrbitUniform

end OAI
end

section
-- module Solutions.OAIQW_Problem355.OrbitSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.OrbitSampling

 theorem mem_orbitFinset {G X : Type*} [Group G] [MulAction G X] [Fintype X]
    (x y : X) : y ∈ orbitFinset G x ↔ y ∈ MulAction.orbit G x := by
  classical
  simp [orbitFinset]

 theorem orbitFinset_nonempty {G X : Type*} [Group G] [MulAction G X] [Fintype X]
    (x : X) : (orbitFinset G x).Nonempty := by
  exact ⟨x, (mem_orbitFinset x x).mpr (MulAction.mem_orbit_self x)⟩

 theorem card_orbitFinset {G X : Type*} [Group G] [MulAction G X] [Fintype X]
    (x : X) : (orbitFinset G x).card = Nat.card (MulAction.orbit G x) := by
  classical
  simp only [orbitFinset, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem uniform_pushforward {G X : Type*} [Group G] [Fintype G]
    [MulAction G X] [Fintype X] (x y : X) :
    LiftingProbability.pushforwardMass (fun _ : G => 1 / (Nat.card G : ℝ))
      (fun g => g • x) y = LiftingProbability.mainMass (orbitFinset G x) y := by
  classical
  have hsum : LiftingProbability.pushforwardMass (fun _ : G => 1 / (Nat.card G : ℝ))
      (fun g => g • x) y =
      ∑ g : G, if g • x = y then 1 / (Nat.card G : ℝ) else 0 := by
    unfold LiftingProbability.pushforwardMass
    apply Finset.sum_congr rfl
    intro g hg
    by_cases h : g • x = y
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hsum]
  by_cases hy : y ∈ MulAction.orbit G x
  · rw [OrbitUniform.uniform_mass_of_mem_orbit x y hy]
    have hym := (mem_orbitFinset x y).mpr hy
    simp [LiftingProbability.mainMass, hym, card_orbitFinset]
  · rw [OrbitUniform.uniform_mass_of_not_mem_orbit x y hy]
    have hym : y ∉ orbitFinset G x := mt (mem_orbitFinset x y).mp hy
    simp [LiftingProbability.mainMass, hym]

theorem sl_averaged_columns_eq_liftedMass {Ω : Type*} [Fintype Ω]
    (h q L : ℕ) [NeZero h] [NeZero q] (shift : Fin 3 → ℤ)
    (C : Fin 3 → Fin 3 → ZMod h) (w : Ω → ℝ)
    (V : Ω → Finset (Fin 3 → ZMod q)) (s : ℕ)
    (x : Fin 3 → IntegerSampling.Box (L * (h * q)) 3 shift) :
    (∑ G : MainGroup h, (1 / (Nat.card (MainGroup h) : ℝ)) *
      ∑ ω, w ω * ∏ i,
        IntegerSampling.columnLaw h q L shift ((G • C) i) (V ω) s (x i)) =
      LiftingProbability.liftedMass
        (fun x i => IntegerSampling.residue h (x i))
        (fun x i => IntegerSampling.residue q (x i))
        (orbitFinset (MainGroup h) C) w V s (L ^ 9) x := by
  classical
  exact LiftingProbability.averaged_columns_eq_liftedMass
    (IntegerSampling.residue h) (IntegerSampling.residue q)
    (fun G : MainGroup h => G • C) (fun _ => 1 / (Nat.card (MainGroup h) : ℝ))
    w V (orbitFinset (MainGroup h) C) s L (uniform_pushforward C) x

theorem integralMatrix_reduction_of_mem_orbit (h q L : ℕ) [NeZero h]
    (shift : Fin 3 → ℤ) (C : Fin 3 → Fin 3 → ZMod h)
    (x : Fin 3 → IntegerSampling.Box (L * (h * q)) 3 shift)
    (hx : (fun i => IntegerSampling.residue h (x i)) ∈ orbitFinset (MainGroup h) C) :
    ∃ G : MainGroup h, (integralMatrix x).map (Int.cast : ℤ → ZMod h) =
      G.val * Matrix.transpose C := by
  obtain ⟨G, hG⟩ := (mem_orbitFinset C _).mp hx
  refine ⟨G, ?_⟩
  change Matrix.transpose (fun i => IntegerSampling.residue h (x i)) = G.val * Matrix.transpose C
  rw [← hG, sl_action_transpose]

end Problem355.OrbitSampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.HomogeneousGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Homogeneous

theorem project_cross_eq (u v w : Column)
    (hu : u 2 ≠ 0) (hv : v 2 ≠ 0) (hw : w 2 ≠ 0) :
    ((v 0 / v 2 - u 0 / u 2) * (w 1 / w 2 - u 1 / u 2) -
      (v 1 / v 2 - u 1 / u 2) * (w 0 / w 2 - u 0 / u 2)) =
      (columns u v w).det / (u 2 * v 2 * w 2) := by
  simp [columns, Matrix.det_fin_three]
  field_simp
  ring

theorem project_area_eq (u v w : Column)
    (hu : 0 < u 2) (hv : 0 < v 2) (hw : 0 < w 2) :
    triangleArea (project u) (project v) (project w) =
      |(columns u v w).det| / (2 * u 2 * v 2 * w 2) := by
  unfold triangleArea project
  dsimp only
  rw [project_cross_eq u v w (ne_of_gt hu) (ne_of_gt hv) (ne_of_gt hw),
    abs_div, abs_of_pos (mul_pos (mul_pos hu hv) hw), div_div]
  congr 1
  ring

theorem project_area_lower_bound {N τ : ℝ} (hN : 0 < N) (hτ : 0 ≤ τ)
    (u v w : Column)
    (hu : N ≤ u 2) (hu' : u 2 ≤ 2 * N)
    (hv : N ≤ v 2) (hv' : v 2 ≤ 2 * N)
    (hw : N ≤ w 2) (hw' : w 2 ≤ 2 * N)
    (hdet : τ ≤ |(columns u v w).det|) :
    τ / (16 * N ^ 3) ≤ triangleArea (project u) (project v) (project w) := by
  have hu0 : 0 < u 2 := lt_of_lt_of_le hN hu
  have hv0 : 0 < v 2 := lt_of_lt_of_le hN hv
  have hw0 : 0 < w 2 := lt_of_lt_of_le hN hw
  have hden0 : 0 < 2 * u 2 * v 2 * w 2 := by positivity
  have hden : 2 * u 2 * v 2 * w 2 ≤ 16 * N ^ 3 := by
    calc
      2 * u 2 * v 2 * w 2 ≤ 2 * (2 * N) * (2 * N) * (2 * N) := by gcongr
      _ = 16 * N ^ 3 := by ring
  rw [project_area_eq u v w hu0 hv0 hw0]
  exact (div_le_div_of_nonneg_left hτ hden0 hden).trans
    (div_le_div_of_nonneg_right hdet hden0.le)

theorem project_area_lower_bound_of_box {N τ : ℝ} (hN : 0 < N) (hτ : 0 ≤ τ)
    {u v w : Column} (hu : InBox N u) (hv : InBox N v) (hw : InBox N w)
    (hdet : τ ≤ |(columns u v w).det|) :
    τ / (16 * N ^ 3) ≤ triangleArea (project u) (project v) (project w) :=
  project_area_lower_bound hN hτ u v w hu.2.2.2.2.1 hu.2.2.2.2.2.le
    hv.2.2.2.2.1 hv.2.2.2.2.2.le hw.2.2.2.2.1 hw.2.2.2.2.2.le hdet

end Problem355.Homogeneous

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.DeterminantResidue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem355.DeterminantResidue

lemma small_eq_of_modEq {h τ a b : ℤ} (hwidth : 2 * τ < h)
    (ha : |a| ≤ τ) (hb : |b| ≤ τ) (hab : a ≡ b [ZMOD h]) : a = b := by
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hdist : |b - a| < h := by
    rw [abs_lt]
    omega
  have hz := Int.eq_zero_of_abs_lt_dvd (Int.modEq_iff_dvd.mp hab) hdist
  omega

lemma small_eq_of_zmod_eq {h : ℕ} {τ a b : ℤ} (hwidth : 2 * τ < h)
    (ha : |a| ≤ τ) (hb : |b| ≤ τ) (hab : (a : ZMod h) = b) : a = b :=
  small_eq_of_modEq hwidth ha hb ((ZMod.intCast_eq_intCast_iff a b h).mp hab)

lemma small_filter_eq_fiber {α : Type*} [DecidableEq α] (s : Finset α)
    (d : α → ℤ) {h : ℕ} {τ : ℤ} (hwidth : 2 * τ < h)
    (c : ZMod h) (hres : ∀ x ∈ s, (d x : ZMod h) = c)
    {a : α} (ha : a ∈ s) (hasmall : |d a| ≤ τ) :
    s.filter (fun x => |d x| ≤ τ) = s.filter (fun x => d x = d a) := by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hsmall⟩
    exact ⟨hx, small_eq_of_zmod_eq hwidth hsmall hasmall
      ((hres x hx).trans (hres a ha).symm)⟩
  · rintro ⟨hx, heq⟩
    exact ⟨hx, heq ▸ hasmall⟩

lemma sum_small_le_of_fiber_bound {α : Type*} [DecidableEq α]
    (s : Finset α) (d : α → ℤ) (w : α → ℝ) {h : ℕ} {τ : ℤ}
    (hwidth : 2 * τ < h) (c : ZMod h)
    (hres : ∀ x ∈ s, (d x : ZMod h) = c) {B : ℝ} (hB : 0 ≤ B)
    (hfiber : ∀ t : ℤ, |t| ≤ τ → ∑ x ∈ s.filter (fun x => d x = t), w x ≤ B) :
    ∑ x ∈ s.filter (fun x => |d x| ≤ τ), w x ≤ B := by
  by_cases hempty : (s.filter (fun x => |d x| ≤ τ)).Nonempty
  · obtain ⟨a, ha⟩ := hempty
    have hamem := (Finset.mem_filter.mp ha).1
    have hasmall := (Finset.mem_filter.mp ha).2
    rw [small_filter_eq_fiber s d hwidth c hres hamem hasmall]
    exact hfiber (d a) hasmall
  · rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
    simpa using hB

end Problem355.DeterminantResidue

end OAI
end

section
-- module Solutions.OAIQW_Problem355.LiftedBadEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.LiftingProbability

open Finset

noncomputable section

 theorem auxiliaryWeight_nonneg {Ω B : Type*} [Fintype Ω]
    (q s : ℕ) (w : Ω → ℝ) (V : Ω → Finset B)
    (hw : ∀ ω, 0 ≤ w ω) (b : Fin 3 → B) :
    0 ≤ auxiliaryWeight q s w V b := by
  unfold auxiliaryWeight
  exact mul_nonneg (by positivity) (inclusionMass_nonneg w V hw b)

theorem lifted_small_event_eq_zero
    {X A Ω B : Type*} [DecidableEq X] [Fintype Ω]
    (f : X → A) (g : X → (Fin 3 → B)) (d : X → ℤ)
    (O : Finset A) (w : Ω → ℝ) (V : Ω → Finset B)
    (s M : ℕ) (S : Finset X) (τ : ℤ)
    (hlarge : ∀ x ∈ S, f x ∈ O → τ < |d x|) :
    (∑ x ∈ S.filter (fun x => |d x| ≤ τ), liftedMass f g O w V s M x) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x hx
  have hxS := (Finset.mem_filter.mp hx).1
  have hxτ := (Finset.mem_filter.mp hx).2
  have hnot : f x ∉ O := fun hf => (not_lt_of_ge hxτ) (hlarge x hxS hf)
  simp [liftedMass, residueMass, mainMass, hnot]

theorem lifted_small_event_le
    {X A Ω B : Type*} [DecidableEq X] [DecidableEq A] [Fintype Ω]
    (f : X → A) (g : X → (Fin 3 → B)) (d : X → ℤ)
    (O : Finset A) (hO : O.Nonempty) (w : Ω → ℝ) (V : Ω → Finset B)
    (s h q L : ℕ) (hs : 0 < s) (hh : 0 < h) (hq : 0 < q) (hL : 0 < L)
    (hw : ∀ ω, 0 ≤ w ω) (S : Finset X)
    {τ : ℤ} (hwidth : 2 * τ < h) (c : ZMod h)
    (hres : ∀ x ∈ S, f x ∈ O → (d x : ZMod h) = c)
    {D E c₀ C R : ℝ} (hD : 0 < D) (hE : 0 < E) (hc₀ : 0 < c₀) (hC : 0 ≤ C)
    (horbit : c₀ * (h : ℝ) ^ 8 / (D ^ 3 * E ^ 2) ≤ (O.card : ℝ))
    (hcount : ∀ t : ℤ, |t| ≤ τ →
      (∑ x ∈ (S.filter (fun x => f x ∈ O)).filter (fun x => d x = t),
        auxiliaryWeight q s w V (g x)) ≤
          C * R ^ 2 * ((L * (h * q) : ℕ) : ℝ) ^ 6 / (D ^ 2 * E ^ 2)) :
    (∑ x ∈ S.filter (fun x => |d x| ≤ τ), liftedMass f g O w V s (L ^ 9) x) ≤
      (C / c₀) * R ^ 2 * (h : ℝ) * D / ((L * (h * q) : ℕ) : ℝ) ^ 3 := by
  classical
  rw [exact_lifting_identity f g O hO w V s h q L hs hh hq hL]
  rw [Finset.filter_comm]
  apply Sampling.lifting_weighted_count_bound
  · exact_mod_cast hh
  · exact_mod_cast (Nat.mul_pos hL (Nat.mul_pos hh hq))
  · exact hD
  · exact hE
  · exact_mod_cast Finset.card_pos.mpr hO
  · exact hc₀
  · exact Finset.sum_nonneg fun x hx => auxiliaryWeight_nonneg q s w V hw (g x)
  · exact horbit
  · apply DeterminantResidue.sum_small_le_of_fiber_bound
      (S.filter (fun x => f x ∈ O)) d (fun x => auxiliaryWeight q s w V (g x))
      hwidth c
    · intro x hx
      exact hres x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
    · positivity
    · exact hcount

end
end Problem355.LiftingProbability

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ProjectiveBadEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.Homogeneous

open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

 theorem integer_columns_det (A : Matrix (Fin 3) (Fin 3) ℤ) :
    (columns (integerColumn A 0) (integerColumn A 1) (integerColumn A 2)).det =
      (A.det : ℝ) := by
  simp [columns, integerColumn, Matrix.det_fin_three]

theorem smallTriangle_low_determinant {N τ : ℝ} (hN : 0 < N) (hτ : 0 ≤ τ)
    {u v w : Column} (hu : InBox N u) (hv : InBox N v) (hw : InBox N w)
    (hsmall : Alteration.smallTriangle (τ / (16 * N ^ 3))
      (project u) (project v) (project w)) :
    projectedDistinct u v w ∧ |(columns u v w).det| < τ := by
  refine ⟨⟨hsmall.1, hsmall.2.1, hsmall.2.2.1⟩, ?_⟩
  by_contra hn
  have hbound := project_area_lower_bound_of_box hN hτ hu hv hw (le_of_not_gt hn)
  exact (not_le_of_gt hsmall.2.2.2) hbound

theorem smallTriangle_integer_determinant {N : ℝ} {τ : ℤ}
    (hN : 0 < N) (hτ : 0 ≤ τ) {u v w : Column}
    (hu : InBox N u) (hv : InBox N v) (hw : InBox N w)
    (d : ℤ) (hd : (columns u v w).det = (d : ℝ))
    (hsmall : Alteration.smallTriangle ((τ : ℝ) / (16 * N ^ 3))
      (project u) (project v) (project w)) :
    projectedDistinct u v w ∧ |d| ≤ τ := by
  have h := smallTriangle_low_determinant hN (by exact_mod_cast hτ) hu hv hw hsmall
  refine ⟨h.1, ?_⟩
  have hreal : |(d : ℝ)| < (τ : ℝ) := by simpa only [hd] using h.2
  have hint : |d| < τ := by exact_mod_cast hreal
  exact hint.le

end
end Problem355.Homogeneous

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegerPointLawTriples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.IntegerPointLaw

open IntegerSampling ConditionalSamples ParameterSampling
open Finset
attribute [local instance] Classical.propDecidable

theorem shared_mixture_expectation {Θ D X : Type*}
    [Fintype Θ] [Fintype D] [Fintype X]
    (rho : Θ → ℝ) (p : D → ℝ) (nu : Θ → D → X → ℝ)
    (F : (Fin 3 → X) → ℝ) :
    (∑ θ, rho θ * ∑ x : Fin 3 → X,
      productWeight (mixtureWeight p (nu θ)) x * F x) =
    ∑ d : Fin 3 → D, productWeight p d *
      ∑ x : Fin 3 → X, (∑ θ, rho θ * ∏ i, nu θ (d i) (x i)) * F x := by
  simp_rw [expectation_productWeight_mixture, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ _
  ring

theorem ofSpecialLinear_expectation {Ω D : Type} [Fintype Ω] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ ω, (V ω).card = s)
    (F : (Fin 3 → Box (L * (h * q)) 3 (samplingShift (L * (h * q)))) → ℝ) :
    let law := ofSpecialLinear h q L s hc hL hs w p c V hw hwsum hp hpsum hV
    (∑ z : law.Environment × (Fin 3 → law.Column),
      sharedWeight law.rho law.mu z * F z.2) =
    ∑ d : Fin 3 → D, productWeight p d *
      ∑ x, LiftingProbability.liftedMass
        (fun x i => residue h (x i)) (fun x i => residue q (x i))
        (OrbitSampling.orbitFinset (OrbitSampling.MainGroup h) (fun i => c (d i)))
        w V s (L ^ 9) x * F x := by
  classical
  dsimp only
  change (∑ z : (OrbitSampling.MainGroup h × Ω) ×
      (Fin 3 → Box (L * (h * q)) 3 (samplingShift (L * (h * q)))),
    ((1 / (Nat.card (OrbitSampling.MainGroup h) : ℝ)) * w z.1.2) *
      productWeight (mixtureWeight p (fun d => columnLaw h q L
        (samplingShift (L * (h * q))) (z.1.1 • c d) (V z.1.2) s)) z.2 * F z.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [mul_assoc]
  conv_lhs =>
    arg 2
    ext θ
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_assoc]
  rw [shared_mixture_expectation]
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  rw [Fintype.sum_prod_type]
  simpa only [Finset.mul_sum, mul_assoc, Pi.smul_apply] using
    (OrbitSampling.sl_averaged_columns_eq_liftedMass h q L
      (samplingShift (L * (h * q))) (fun i => c (d i)) w V s x)

theorem column_inBox {N : ℕ} (x : Box N 3 (samplingShift N)) :
    Homogeneous.InBox (N : ℝ) (fun i => ((x i).val : ℝ)) := by
  have hx : 0 ≤ (x 0).val ∧ (x 0).val < (N : ℤ) := by
    simpa [samplingShift] using (x 0).property
  have hy : 0 ≤ (x 1).val ∧ (x 1).val < (N : ℤ) := by
    simpa [samplingShift] using (x 1).property
  have hz : (N : ℤ) ≤ (x 2).val ∧ (x 2).val < (N : ℤ) + N :=
    (x 2).property
  unfold Homogeneous.InBox
  dsimp only
  refine ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2,
    by exact_mod_cast hy.1, by exact_mod_cast hy.2,
    by exact_mod_cast hz.1, ?_⟩
  have hh : ((x 2).val : ℝ) < (N : ℝ) + N := by exact_mod_cast hz.2
  linarith

theorem triangleEvent_implies_badDeterminantEvent {N : ℕ} (hN : 0 < N)
    {τ : ℤ} (hτ : 0 ≤ τ) (x : Fin 3 → Box N 3 (samplingShift N))
    (hx : triangleEvent ((τ : ℝ) / (16 * (N : ℝ) ^ 3)) x) :
    badDeterminantEvent τ x := by
  have hcol (j : Fin 3) : Homogeneous.InBox (N : ℝ)
      (Homogeneous.integerColumn (OrbitSampling.integralMatrix x) j) :=
    column_inBox (x j)
  have he := Homogeneous.smallTriangle_integer_determinant
    (by exact_mod_cast hN) hτ (hcol 0) (hcol 1) (hcol 2)
    (OrbitSampling.integralMatrix x).det
    (Homogeneous.integer_columns_det (OrbitSampling.integralMatrix x)) hx
  exact ⟨he.1.1, he.1.2.1, he.1.2.2, he.2⟩

theorem ofSpecialLinear_tripleProbability_eq {Ω D : Type} [Fintype Ω] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ ω, (V ω).card = s) (a : ℝ) :
    (ofSpecialLinear h q L s hc hL hs w p c V hw hwsum hp hpsum hV).tripleProbability a =
    ∑ d : Fin 3 → D, productWeight p d *
      ∑ x ∈ (Finset.univ : Finset (Fin 3 → Box (L * (h * q)) 3
        (samplingShift (L * (h * q))))).filter (triangleEvent a), LiftingProbability.liftedMass
        (fun x i => residue h (x i)) (fun x i => residue q (x i))
        (OrbitSampling.orbitFinset (OrbitSampling.MainGroup h) (fun i => c (d i)))
        w V s (L ^ 9) x := by
  classical
  have he := ofSpecialLinear_expectation h q L s hc hL hs w p c V
    hw hwsum hp hpsum hV (fun x => if triangleEvent a x then 1 else 0)
  unfold PointLaw.tripleProbability SharedGeometricAlteration.tripleMass
  change (∑ z : (OrbitSampling.MainGroup h × Ω) ×
      (Fin 3 → Box (L * (h * q)) 3 (samplingShift (L * (h * q)))),
    if triangleEvent a z.2 then
      sharedWeight (ofSpecialLinear h q L s hc hL hs w p c V hw hwsum hp hpsum hV).rho
        (ofSpecialLinear h q L s hc hL hs w p c V hw hwsum hp hpsum hV).mu z
    else 0) = _
  simp only [ofSpecialLinear, ofIndependentEnvironments, ofMixture,
    Finset.sum_filter, mul_ite, mul_one, mul_zero] at he ⊢
  convert he using 1
  all_goals congr 1

theorem ofSpecialLinear_tripleProbability_le_badDeterminant {Ω D : Type}
    [Fintype Ω] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ ω, (V ω).card = s) {τ : ℤ} (hτ : 0 ≤ τ) :
    (ofSpecialLinear h q L s hc hL hs w p c V hw hwsum hp hpsum hV).tripleProbability
      ((τ : ℝ) / (16 * ((L * (h * q) : ℕ) : ℝ) ^ 3)) ≤
    ∑ d : Fin 3 → D, productWeight p d *
      ∑ x ∈ (Finset.univ : Finset (Fin 3 → Box (L * (h * q)) 3
        (samplingShift (L * (h * q))))).filter (badDeterminantEvent τ),
        LiftingProbability.liftedMass
          (fun x i => residue h (x i)) (fun x i => residue q (x i))
          (OrbitSampling.orbitFinset (OrbitSampling.MainGroup h) (fun i => c (d i)))
          w V s (L ^ 9) x := by
  classical
  rw [ofSpecialLinear_tripleProbability_eq]
  apply Finset.sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ (productWeight_nonneg p hp d)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩
    exact triangleEvent_implies_badDeterminantEvent
      (mul_pos hL (mul_pos (NeZero.pos h) (NeZero.pos q))) hτ x
      (Finset.mem_filter.mp hx).2
  · intro x _ _
    exact LiftingProbability.liftedMass_nonneg _ _ _ w V s (L ^ 9) hw x

end Problem355.IntegerPointLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.MainDigitObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.MainDigitObstruction

open FiniteFieldLabels Parameters

lemma extendDigits_at {k : ℕ} (d : Fin k → ℕ) (v : Fin k) :
    extendDigits d v.val = (d v : ℤ) := by
  simp only [extendDigits, dite_eq_left v.isLt]

lemma sum_extendDigits {B k : ℕ} (d : Fin k → ℕ) :
    (∑ v ∈ Finset.range k, extendDigits d v * (B : ℤ) ^ v) =
      ((∑ v : Fin k, d v * B ^ v.val : ℕ) : ℤ) := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [extendDigits_at, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]

theorem finite_small_det_forces_repeated_labels
    {r : ℕ} [Fact r.Prime] (hr : 2 < r)
    (D : PrimeParameterData heilbronnK r)
    (h : ℕ) (hh : h = D.h)
    (labels : Fin 3 → Label r)
    (d : Fin 3 → Fin 3 → Fin heilbronnK → ℕ)
    (hd : ∀ i j v, d i j v ≤ r ^ 10)
    (hresidue : ∀ i j v, (d i j v : ZMod r) =
      MainResidueSystem.finiteResidue r i v (labels j))
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (G : Matrix.SpecialLinearGroup (Fin 3) (ZMod h))
    (hAC : A.map (Int.castRingHom (ZMod h)) =
      G.val * (Matrix.of (fun i j =>
        ((∑ v : Fin heilbronnK, d i j v * D.B ^ v.val : ℕ) : ZMod h)) :
          Matrix (Fin 3) (Fin 3) (ZMod h)))
    (hsmall : |A.det| ≤ (D.tau : ℤ)) :
    ∃ i j : Fin 3, i ≠ j ∧ labels i = labels j := by
  let ds : Fin 3 → Fin 3 → ℕ → ℤ := fun i j => extendDigits (d i j)
  refine MainResidueSystem.small_det_forces_repeated_labels r hr D.B
    (r ^ 10 : ℕ) (by have := D.base_ge_three; omega) (by positivity)
    (by exact_mod_cast D.base_lower_original) labels ds ?_ ?_ A h hh G ?_ ?_
  · intro i j v hv
    change |extendDigits (d i j) v| ≤ ((r ^ 10 : ℕ) : ℤ)
    rw [show extendDigits (d i j) v = (d i j ⟨v, hv⟩ : ℤ) by
      simp only [extendDigits, dite_eq_left hv]]
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast hd i j ⟨v, hv⟩
  · intro i j v hv
    change ((extendDigits (d i j) v : ℤ) : ZMod r) = _
    simpa only [extendDigits, dite_eq_left hv, Int.cast_natCast,
      MainResidueSystem.finiteResidue] using hresidue i j ⟨v, hv⟩
  · have hmatrix :
        Matrix.map (fun i j => ∑ v ∈ Finset.range heilbronnK,
          ds i j v * (D.B : ℤ) ^ v) (Int.castRingHom (ZMod h)) =
          Matrix.of (fun i j =>
            ((∑ v : Fin heilbronnK, d i j v * D.B ^ v.val : ℕ) : ZMod h)) := by
      ext i j
      change (((∑ v ∈ Finset.range heilbronnK,
        extendDigits (d i j) v * (D.B : ℤ) ^ v) : ℤ) : ZMod h) = _
      rw [sum_extendDigits]
      simp only [Int.cast_natCast, Matrix.of_apply]
    rw [hmatrix]
    exact hAC
  · simpa only [PrimeParameterData.tau, threshold, Int.natCast_div,
      Nat.cast_pow, Nat.cast_ofNat] using hsmall

end Problem355.MainDigitObstruction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.MainOrbitObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.MainOrbitObstruction

open OrbitSampling

lemma reduction_of_mem_orbit (h : ℕ) [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : columnResidue h A ∈ orbitFinset (MainGroup h) C) :
    ∃ G : MainGroup h, A.map (Int.castRingHom (ZMod h)) =
      G.val * Matrix.transpose C := by
  obtain ⟨G, hG⟩ := (mem_orbitFinset C _).mp hA
  refine ⟨G, ?_⟩
  change Matrix.transpose (columnResidue h A) = G.val * Matrix.transpose C
  rw [← hG, sl_action_transpose]

end Problem355.MainOrbitObstruction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.MainDigitOrbitObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT Problem355.heilbronnM

namespace Problem355.MainDigitOrbitObstruction

open Parameters FiniteFieldLabels MainDigitLaw OrbitSampling

attribute [local instance] Classical.propDecidable

variable {r : ℕ} [Fact r.Prime]
variable (D : PrimeParameterData heilbronnK r)

theorem small_det_forces_repeated_labels (hr : 2 < r)
    (h : ℕ) [NeZero h] (hh : h = D.h)
    (labels : Fin 3 → Label r) (f : MainDigitLaw.Array r)
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : MainOrbitObstruction.columnResidue h A ∈
      orbitFinset (MainGroup h) (columns D h labels f))
    (hsmall : |A.det| ≤ (D.tau : ℤ)) :
    ∃ i j : Fin 3, i ≠ j ∧ labels i = labels j := by
  obtain ⟨G, hG⟩ := MainOrbitObstruction.reduction_of_mem_orbit h
    (columns D h labels f) A hA
  exact MainDigitObstruction.finite_small_det_forces_repeated_labels hr D h hh labels
    (fun i j v => (digit D (labels j) i v (f i j v)).val)
    (fun i j v => digit_le D (labels j) i v (f i j v))
    (fun i j v => digit_residue D (labels j) i v (f i j v)) A G hG hsmall

theorem det_abs_gt_of_injective_labels (hr : 2 < r)
    (h : ℕ) [NeZero h] (hh : h = D.h)
    (labels : Fin 3 → Label r) (hinj : Function.Injective labels)
    (f : MainDigitLaw.Array r) (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : MainOrbitObstruction.columnResidue h A ∈
      orbitFinset (MainGroup h) (columns D h labels f)) :
    (D.tau : ℤ) < |A.det| := by
  by_contra hn
  obtain ⟨i, j, hij, heq⟩ := small_det_forces_repeated_labels D hr h hh labels f A hA
    (le_of_not_gt hn)
  exact hij (hinj heq)

end Problem355.MainDigitOrbitObstruction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.OrbitRowLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355.OrbitRowLattice

open Matrix

variable {R : Type*} [CommRing R]

theorem det_eq_of_mem_slOrbit
    {C A : Matrix (Fin 3) (Fin 3) R} (hA : A ∈ Section04Orbit.slOrbit C) :
    A.det = C.det := by
  obtain ⟨g, rfl⟩ := hA
  rw [Matrix.det_mul, g.property, one_mul]

theorem det_cast_eq_of_reduction_mem_slOrbit
    (h : ℕ) (C : Matrix (Fin 3) (Fin 3) (ZMod h))
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (hA : A.map (Int.castRingHom (ZMod h)) ∈ Section04Orbit.slOrbit C) :
    (A.det : ZMod h) = C.det := by
  have hd := det_eq_of_mem_slOrbit hA
  change (Int.castRingHom (ZMod h)) A.det = C.det
  rw [RingHom.map_det]
  exact hd

end Problem355.OrbitRowLattice

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ConditionalBadTripleBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.ConditionalBadTripleBound

open OrbitSampling IntegerSampling LiftingProbability

theorem card_sampling_orbit (h : ℕ) [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) :
    (orbitFinset (MainGroup h) C).card =
      Nat.card (Section04Orbit.slOrbit (Matrix.transpose C)) := by
  rw [card_orbitFinset]
  exact Nat.card_congr (orbitTransposeEquiv h C)

theorem sampling_orbit_lower_bound {p k : ℕ} [NeZero (p ^ k)]
    (hp : p.Prime) (hk : 0 < k)
    (C : Fin 3 → Fin 3 → ZMod (p ^ k))
    (d : PrimePowerData p k (Matrix.transpose C)) :
    (21 / 64 : ℝ) * ((p ^ k : ℕ) : ℝ) ^ 8 /
      (((p ^ d.b : ℕ) : ℝ) ^ 3 * ((p ^ d.e : ℕ) : ℝ) ^ 2) ≤
        ((orbitFinset (MainGroup (p ^ k)) C).card : ℝ) := by
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [card_sampling_orbit]
  exact d.orbit_lower_bound hp hk

theorem integral_det_residue (h q L : ℕ) [NeZero h]
    (shift : Fin 3 → ℤ) (C : Fin 3 → Fin 3 → ZMod h)
    (x : Fin 3 → Box (L * (h * q)) 3 shift)
    (hx : (fun i => residue h (x i)) ∈ orbitFinset (MainGroup h) C) :
    ((integralMatrix x).det : ZMod h) = (Matrix.transpose C).det := by
  obtain ⟨G, hG⟩ := integralMatrix_reduction_of_mem_orbit h q L shift C x hx
  apply OrbitRowLattice.det_cast_eq_of_reduction_mem_slOrbit h (Matrix.transpose C)
    (integralMatrix x)
  exact ⟨G, hG.symm⟩

theorem conditional_small_mass_le {Ω : Type*} [Fintype Ω]
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k)
    (q L s : ℕ) (hq : 0 < q) (hL : 0 < L) (hs : 0 < s)
    (shift : Fin 3 → ℤ) (C : Fin 3 → Fin 3 → ZMod (p ^ k))
    (d : PrimePowerData p k (Matrix.transpose C))
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω)
    (S : Finset (Fin 3 → Box (L * (p ^ k * q)) 3 shift))
    {τ : ℤ} (hwidth : 2 * τ < (p ^ k : ℕ))
    {K R : ℝ} (hK : 0 ≤ K)
    (hcount : ∀ t : ℤ, |t| ≤ τ →
      (∑ x ∈ (S.filter (fun x =>
        (fun i => residue (p ^ k) (x i)) ∈ orbitFinset (MainGroup (p ^ k)) C)).filter
          (fun x => (integralMatrix x).det = t),
        auxiliaryWeight q s w V (fun i => residue q (x i))) ≤
          K * R ^ 2 * ((L * (p ^ k * q) : ℕ) : ℝ) ^ 6 /
            (((p ^ d.b : ℕ) : ℝ) ^ 2 * ((p ^ d.e : ℕ) : ℝ) ^ 2)) :
    (∑ x ∈ S.filter (fun x => |(integralMatrix x).det| ≤ τ),
      liftedMass (fun x i => residue (p ^ k) (x i))
        (fun x i => residue q (x i)) (orbitFinset (MainGroup (p ^ k)) C)
        w V s (L ^ 9) x) ≤
      (K / (21 / 64)) * R ^ 2 * ((p ^ k : ℕ) : ℝ) * ((p ^ d.b : ℕ) : ℝ) /
        ((L * (p ^ k * q) : ℕ) : ℝ) ^ 3 := by
  classical
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  exact lifted_small_event_le (D := ((p ^ d.b : ℕ) : ℝ))
    (E := ((p ^ d.e : ℕ) : ℝ))
    (fun x i => residue (p ^ k) (x i)) (fun x i => residue q (x i))
    (fun x => (integralMatrix x).det)
    (orbitFinset (MainGroup (p ^ k)) C) (orbitFinset_nonempty C) w V
    s (p ^ k) q L hs (pow_pos hp.pos _) hq hL hw S hwidth
    (Matrix.transpose C).det
    (fun x _ hxo => integral_det_residue (p ^ k) q L shift C x hxo)
    (by exact_mod_cast pow_pos hp.pos d.b)
    (by exact_mod_cast pow_pos hp.pos d.e)
    (by norm_num) hK (sampling_orbit_lower_bound hp hk C d) hcount

end Problem355.ConditionalBadTripleBound

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AveragedBadTripleBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.ConditionalBadTripleBound

open OrbitSampling IntegerSampling LiftingProbability DigitColumnLaw

theorem averaged_small_mass_le
    {Λ X Ω : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]
    [Fintype X] [Fintype Ω]
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k)
    (q L s : ℕ) (hq : 0 < q) (hL : 0 < L) (hs : 0 < s)
    (shift : Fin 3 → ℤ)
    (c : Latent Λ X k → Fin 3 → ZMod (p ^ k))
    (d : (z : Fin 3 → Latent Λ X k) →
      PrimePowerData p k (Matrix.transpose (fun j => c (z j))))
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω)
    (S : Finset (Fin 3 → Box (L * (p ^ k * q)) 3 shift))
    {τ : ℤ} (hwidth : 2 * τ < (p ^ k : ℕ))
    {K R : ℝ} (hK : 0 ≤ K)
    (hmoment : ∀ labels : Fin 3 → Λ,
      (∑ f : Array X k, uniformWeight (Array X k) f *
        ((p ^ (d (tripleEquiv.symm (labels, f))).b : ℕ) : ℝ)) ≤ 2)
    (hseparate : ∀ z : Fin 3 → Latent Λ X k,
      (z 0).1 ≠ (z 1).1 → (z 0).1 ≠ (z 2).1 → (z 1).1 ≠ (z 2).1 →
      ∀ x ∈ S, (fun i => residue (p ^ k) (x i)) ∈
        orbitFinset (MainGroup (p ^ k)) (fun j => c (z j)) →
          τ < |(integralMatrix x).det|)
    (hcount : ∀ z : Fin 3 → Latent Λ X k, ∀ t : ℤ, |t| ≤ τ →
      (∑ x ∈ (S.filter (fun x => (fun i => residue (p ^ k) (x i)) ∈
        orbitFinset (MainGroup (p ^ k)) (fun j => c (z j)))).filter
          (fun x => (integralMatrix x).det = t),
        auxiliaryWeight q s w V (fun i => residue q (x i))) ≤
          K * R ^ 2 * ((L * (p ^ k * q) : ℕ) : ℝ) ^ 6 /
            (((p ^ (d z).b : ℕ) : ℝ) ^ 2 * ((p ^ (d z).e : ℕ) : ℝ) ^ 2)) :
    (∑ z : Fin 3 → Latent Λ X k,
      ConditionalSamples.productWeight (uniformWeight (Latent Λ X k)) z *
        smallMass (p ^ k) q L s shift (fun j => c (z j)) w V S τ) ≤
      6 * (K / (21 / 64)) * R ^ 2 * ((p ^ k : ℕ) : ℝ) /
        (((L * (p ^ k * q) : ℕ) : ℝ) ^ 3 * (Fintype.card Λ : ℝ)) := by
  classical
  let A : ℝ := (K / (21 / 64)) * R ^ 2 * ((p ^ k : ℕ) : ℝ) /
    ((L * (p ^ k * q) : ℕ) : ℝ) ^ 3
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h := bad_triple_expectation_le
    (fun labels f => ((p ^ (d (tripleEquiv.symm (labels, f))).b : ℕ) : ℝ))
    (fun z => smallMass (p ^ k) q L s shift (fun j => c (z j)) w V S τ)
    A hA hmoment (by
      intro labels f
      have hb := conditional_small_mass_le hp hk q L s hq hL hs shift
        (fun j => c ((tripleEquiv.symm (labels, f)) j))
        (d (tripleEquiv.symm (labels, f))) w V hw S hwidth hK
        (hcount (tripleEquiv.symm (labels, f)))
      unfold smallMass
      convert hb using 1; dsimp [A]; ring)
    (by
      intro z h01 h02 h12
      unfold smallMass
      exact lifted_small_event_eq_zero
        (fun x i => residue (p ^ k) (x i)) (fun x i => residue q (x i))
        (fun x => (integralMatrix x).det)
        (orbitFinset (MainGroup (p ^ k)) (fun j => c (z j)))
        w V s (L ^ 9) S τ (hseparate z h01 h02 h12))
  convert h using 1; dsimp [A]; ring

end Problem355.ConditionalBadTripleBound

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.PointLawBadTripleBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.IntegerPointLaw

open IntegerSampling ConditionalSamples ParameterSampling
open ConditionalBadTripleBound DigitColumnLaw OrbitSampling LiftingProbability
attribute [local instance] Classical.propDecidable

theorem badDeterminantEvent_filter (N : ℕ) (τ : ℤ) :
    Finset.univ.filter (badDeterminantEvent (N := N) τ) =
      (projectedDistinctTriples N).filter
        (fun x => |(OrbitSampling.integralMatrix x).det| ≤ τ) := by
  classical
  ext x
  simp only [projectedDistinctTriples, Finset.mem_filter, Finset.mem_univ,
    true_and, badDeterminantEvent, and_assoc]

theorem ofSpecialLinear_tripleProbability_le_smallMass {Ω D : Type}
    [Fintype Ω] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ ω, (V ω).card = s) {τ : ℤ} (hτ : 0 ≤ τ) :
    (ofSpecialLinear h q L s hc hL hs w p c V hw hwsum hp hpsum hV).tripleProbability
      ((τ : ℝ) / (16 * ((L * (h * q) : ℕ) : ℝ) ^ 3)) ≤
      ∑ z : Fin 3 → D, productWeight p z *
        smallMass h q L s (samplingShift (L * (h * q))) (fun j => c (z j))
          w V (projectedDistinctTriples (L * (h * q))) τ := by
  classical
  have hbound := ofSpecialLinear_tripleProbability_le_badDeterminant
    h q L s hc hL hs w p c V hw hwsum hp hpsum hV hτ
  simpa only [badDeterminantEvent_filter, smallMass] using hbound

theorem ofSpecialLinear_tripleProbability_le
    {Λ X Ω : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]
    [Fintype X] [Nonempty X] [Fintype Ω]
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k)
    (q L s : ℕ) [NeZero q] (hc : (p ^ k).Coprime q) (hq : 0 < q) (hL : 0 < L) (hs : 0 < s)
    (c : Latent Λ X k → Fin 3 → ZMod (p ^ k))
    (d : (z : Fin 3 → Latent Λ X k) →
      PrimePowerData p k (Matrix.transpose (fun j => c (z j))))
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hV : ∀ ω, (V ω).card = s)
    {τ : ℤ} (hτ : 0 ≤ τ) (hwidth : 2 * τ < (p ^ k : ℕ))
    {K R : ℝ} (hK : 0 ≤ K)
    (hmoment : ∀ labels : Fin 3 → Λ,
      (∑ f : Array X k, uniformWeight (Array X k) f *
        ((p ^ (d (tripleEquiv.symm (labels, f))).b : ℕ) : ℝ)) ≤ 2)
    (hseparate : ∀ z : Fin 3 → Latent Λ X k,
      (z 0).1 ≠ (z 1).1 → (z 0).1 ≠ (z 2).1 → (z 1).1 ≠ (z 2).1 →
      ∀ x ∈ projectedDistinctTriples (L * (p ^ k * q)), (fun i => residue (p ^ k) (x i)) ∈
        orbitFinset (MainGroup (p ^ k)) (fun j => c (z j)) →
          τ < |(integralMatrix x).det|)
    (hcount : ∀ z : Fin 3 → Latent Λ X k, ∀ t : ℤ, |t| ≤ τ →
      (∑ x ∈ ((projectedDistinctTriples (L * (p ^ k * q))).filter (fun x => (fun i => residue (p ^ k) (x i)) ∈
        orbitFinset (MainGroup (p ^ k)) (fun j => c (z j)))).filter
          (fun x => (integralMatrix x).det = t),
        auxiliaryWeight q s w V (fun i => residue q (x i))) ≤
          K * R ^ 2 * ((L * (p ^ k * q) : ℕ) : ℝ) ^ 6 /
            (((p ^ (d z).b : ℕ) : ℝ) ^ 2 * ((p ^ (d z).e : ℕ) : ℝ) ^ 2)) :
    (ofSpecialLinear (p ^ k) q L s hc hL hs w
      (uniformWeight (Latent Λ X k)) c V hw hwsum
      (uniformWeight_nonneg _) (sum_uniformWeight _) hV).tripleProbability
      ((τ : ℝ) / (16 * ((L * (p ^ k * q) : ℕ) : ℝ) ^ 3)) ≤
      6 * (K / (21 / 64)) * R ^ 2 * ((p ^ k : ℕ) : ℝ) /
        (((L * (p ^ k * q) : ℕ) : ℝ) ^ 3 * (Fintype.card Λ : ℝ)) := by
  classical
  apply le_trans (ofSpecialLinear_tripleProbability_le_smallMass
    (p ^ k) q L s hc hL hs w (uniformWeight (Latent Λ X k)) c V
    hw hwsum (uniformWeight_nonneg _) (sum_uniformWeight _) hV hτ)
  exact averaged_small_mass_le hp hk q L s hq hL hs
    (samplingShift (L * (p ^ k * q))) c d w V hw
    (projectedDistinctTriples (L * (p ^ k * q))) hwidth hK
    hmoment hseparate hcount

end Problem355.IntegerPointLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ActualPointLawTriples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT
  Problem355.heilbronnM

namespace Problem355.ActualPointLaw

open Parameters FiniteFieldLabels DigitColumnLaw OrbitSampling IntegerSampling
open scoped BigOperators

variable {r : ℕ} [Fact r.Prime]

theorem latentSmith_moment (D : PrimeParameterData heilbronnK r)
    (labels : Fin 3 → Label r) :
    (∑ f : MainDigitLaw.Array r,
      uniformWeight (MainDigitLaw.Array r) f *
        ((D.B ^ (latentSmith D (tripleEquiv.symm (labels, f))).b : ℕ) : ℝ)) ≤ 2 := by
  change (∑ f : MainDigitLaw.Array r,
    uniformWeight (MainDigitLaw.Array r) f *
      ((D.B ^ (MainDigitLaw.smith D labels f).b : ℕ) : ℝ)) ≤ 2
  simpa only [Nat.cast_pow] using
    MainDigitLaw.conditional_moment D labels

theorem two_lt_label_prime {r : ℕ} [Fact r.Prime]
    (D : PrimeParameterData heilbronnK r) : 2 < r := by
  have hk := D.two_le_k
  have hr := D.large_r
  have hk2 : 4 ≤ heilbronnK ^ 2 := by nlinarith
  omega

theorem latent_separation (D : PrimeParameterData heilbronnK r)
    [NeZero (D.B ^ heilbronnK)] (z : Fin 3 → MainDigitLaw.Latent r)
    (h01 : (z 0).1 ≠ (z 1).1) (h02 : (z 0).1 ≠ (z 2).1)
    (h12 : (z 1).1 ≠ (z 2).1)
    {N : ℕ} {shift : Fin 3 → ℤ} (x : Fin 3 → Box N 3 shift)
    (hx : (fun i => residue (D.B ^ heilbronnK) (x i)) ∈
      orbitFinset (MainGroup (D.B ^ heilbronnK)) (fun j => MainDigitLaw.column D (z j))) :
    (D.tau : ℤ) < |(integralMatrix x).det| := by
  have hinj : Function.Injective (fun i => (z i).1) := by
    have hz : (![ (z 0).1, (z 1).1, (z 2).1 ] : Fin 3 → Label r) =
        (fun i => (z i).1) := by
      funext i
      fin_cases i <;> rfl
    rw [← hz]
    exact DigitBadTripleAverage.injective_labels h01 h02 h12
  exact MainDigitOrbitObstruction.det_abs_gt_of_injective_labels D
    (two_lt_label_prime D) (D.B ^ heilbronnK) rfl (tripleEquiv z).1 hinj
    (tripleEquiv z).2 (integralMatrix x) hx

theorem withAuxiliary_tripleProbability_le_of_count
    [Fintype (Label r)] (D : PrimeParameterData heilbronnK r)
    [Fact D.q.Prime] (A : AuxiliarySampling.Law D.q (D.h ^ 2))
    {K : ℝ} (hK : 0 ≤ K) (hcount : WeightedFiberBound D A K) :
    (withAuxiliary D A).tripleProbability
      (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
      ((128 / 7 : ℝ) * K) * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
        ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41) := by
  classical
  let : NeZero (D.B ^ heilbronnK) := ⟨pow_ne_zero _ D.base_prime.ne_zero⟩
  let : NeZero (r ^ 9) := ⟨pow_ne_zero _ D.r_pos.ne'⟩
  let : NeZero D.q := ⟨D.auxiliary_prime.ne_zero⟩
  have hN : D.liftMultiplicity * (D.B ^ heilbronnK * D.q) = D.N :=
    D.liftMultiplicity_mul_moduli
  have hwidth : 2 * (D.tau : ℤ) < (D.B ^ heilbronnK : ℕ) := by
    exact_mod_cast D.twice_tau_lt_h
  have hcard : Fintype.card (Label r) = r ^ 41 := by
    rw [← Nat.card_eq_fintype_card, FiniteFieldLabels.card_label]
    rfl
  have hb := IntegerPointLaw.ofSpecialLinear_tripleProbability_le
    (R := Real.log (2 * (D.N : ℝ)))
    D.base_prime heilbronnK_pos D.q D.liftMultiplicity A.size
    D.coprime D.auxiliary_prime.pos D.liftMultiplicity_pos A.size_pos
    (MainDigitLaw.column D) (latentSmith D) A.weight A.sets
    A.weight_nonneg A.weight_sum A.sets_card
    (show (0 : ℤ) ≤ D.tau by positivity) hwidth hK
    (latentSmith_moment D)
    (fun z h01 h02 h12 x _ hx => latent_separation D z h01 h02 h12 x hx)
    (by
      unfold WeightedFiberBound at hcount
      rw [hN]
      exact hcount)
  have hcardreal : (Fintype.card (Label r) : ℝ) = (r : ℝ) ^ 41 := by
    rw [hcard, Nat.cast_pow]
  rw [hN, hcardreal, Int.cast_natCast] at hb
  change (withAuxiliary D A).tripleProbability
    (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
    6 * (K / (21 / 64)) * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
      ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41) at hb
  convert hb using 1; ring

theorem tripleProbability_le_of_count
    (D : PrimeParameterData heilbronnK r) {K : ℝ} (hK : 0 ≤ K)
    (hcount : ∀ A : @AuxiliarySampling.Law D.q (D.h ^ 2) ⟨D.auxiliary_prime⟩,
      @WeightedFiberBound r _ D ⟨D.auxiliary_prime⟩ A K) :
    (pointLaw D).tripleProbability (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
      ((128 / 7 : ℝ) * K) * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
        ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41) := by
  let : Fintype (Label r) := Fintype.ofFinite (Label r)
  let : Fact D.q.Prime := ⟨D.auxiliary_prime⟩
  unfold pointLaw
  exact withAuxiliary_tripleProbability_le_of_count D _ hK (hcount _)

end Problem355.ActualPointLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegerMatrixEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.IntegerMatrixEvents
attribute [local instance] Classical.propDecidable

open Finset Matrix
open IntegerSampling OrbitSampling

theorem integralMatrix_injective {N : ℕ} {shift : Fin 3 → ℤ} :
    Function.Injective (@integralMatrix N shift) := by
  intro x y h
  funext j i
  apply Subtype.ext
  exact congrFun (congrFun h i) j

theorem sum_image_integralMatrix {N : ℕ} {shift : Fin 3 → ℤ}
    (S : Finset (Fin 3 → Box N 3 shift)) (W : IntMatrix → ℝ) :
    (∑ x ∈ S, W (integralMatrix x)) =
      ∑ A ∈ S.image integralMatrix, W A := by
  classical
  rw [Finset.sum_image]
  exact fun x _ y _ h => integralMatrix_injective h

theorem image_matrix_event {N : ℕ} {shift : Fin 3 → ℤ}
    (P : IntMatrix → Prop) :
    ((Finset.univ : Finset (Fin 3 → Box N 3 shift)).filter
      (fun x => P (integralMatrix x))).image integralMatrix =
      (matrices N shift).filter P := by
  classical
  ext A
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    matrices]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, hx⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩

theorem sum_matrix_event {N : ℕ} {shift : Fin 3 → ℤ}
    (P : IntMatrix → Prop) (W : IntMatrix → ℝ) :
    (∑ x ∈ (Finset.univ : Finset (Fin 3 → Box N 3 shift)).filter
      (fun x => P (integralMatrix x)), W (integralMatrix x)) =
      ∑ A ∈ (matrices N shift).filter P, W A := by
  classical
  rw [sum_image_integralMatrix, image_matrix_event]

theorem sum_auxiliaryWeight_event {Ω : Type*} [Fintype Ω]
    {N : ℕ} {shift : Fin 3 → ℤ} (q s : ℕ)
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
    (P : IntMatrix → Prop) :
    (∑ x ∈ (Finset.univ : Finset (Fin 3 → Box N 3 shift)).filter
      (fun x => P (integralMatrix x)),
      LiftingProbability.auxiliaryWeight q s w V (fun j => residue q (x j))) =
      ∑ A ∈ (matrices N shift).filter P, matrixWeight q s w V A := by
  exact sum_matrix_event P (matrixWeight q s w V)

end Problem355.IntegerMatrixEvents

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.IntegerMatrixFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.IntegerMatrixEvents
open Finset Matrix IntegerSampling OrbitSampling
attribute [local instance] Classical.propDecidable

theorem sum_fixedDet_event {Ω : Type*} [Fintype Ω]
    (N h q s : ℕ) [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ)
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q)) :
    (∑ x ∈ (Finset.univ : Finset (Fin 3 → Box N 3 (samplingShift N))).filter
      (fun x => fixedDetProperty h C t (integralMatrix x)),
      LiftingProbability.auxiliaryWeight q s w V (fun j => residue q (x j))) =
      ∑ A ∈ fixedDetEvent N h C t, matrixWeight q s w V A := by
  exact sum_auxiliaryWeight_event q s w V (fixedDetProperty h C t)
theorem fixedDetProperty_integralMatrix {N h : ℕ} [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ)
    (x : Fin 3 → Box N 3 (samplingShift N)) :
    fixedDetProperty h C t (integralMatrix x) ↔
      Homogeneous.projectedDistinct (Homogeneous.integerColumn (integralMatrix x) 0)
        (Homogeneous.integerColumn (integralMatrix x) 1)
        (Homogeneous.integerColumn (integralMatrix x) 2) ∧
      (fun j => residue h (x j)) ∈ orbitFinset (MainGroup h) C ∧
      (integralMatrix x).det = t := by
  rfl

theorem fixedDetProperty_reduction {h : ℕ} [NeZero h]
    {C : Fin 3 → Fin 3 → ZMod h} {t : ℤ} {A : IntMatrix}
    (hA : fixedDetProperty h C t A) :
    A.map (Int.castRingHom (ZMod h)) ∈ Section04Orbit.slOrbit (Matrix.transpose C) := by
  obtain ⟨G, hG⟩ := (mem_orbitFinset C _).mp hA.2.1
  refine ⟨G, ?_⟩
  change G.val * Matrix.transpose C = A.map (Int.castRingHom (ZMod h))
  rw [← sl_action_transpose]
  exact congrArg Matrix.transpose hG

theorem fixedDetEvent_projections {N h : ℕ} [NeZero h]
    {C : Fin 3 → Fin 3 → ZMod h} {t : ℤ} {A : IntMatrix}
    (hA : A ∈ fixedDetEvent N h C t) (i j : Fin 3) (hij : i ≠ j) :
    Homogeneous.project (Homogeneous.integerColumn A i) ≠
      Homogeneous.project (Homogeneous.integerColumn A j) := by
  obtain ⟨h01, h02, h12⟩ := (Finset.mem_filter.mp hA).2.1
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact h01
  · exact h02
  · exact h01.symm
  · exact False.elim (hij rfl)
  · exact h12
  · exact h02.symm
  · exact h12.symm
  · exact False.elim (hij rfl)

theorem sum_fixedDet_nested_event {Ω : Type*} [Fintype Ω]
    (N h q s : ℕ) [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ)
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q)) :
    (∑ x ∈ (((Finset.univ : Finset (Fin 3 → Box N 3 (samplingShift N))).filter
      (fun x => project (x 0) ≠ project (x 1) ∧
        project (x 0) ≠ project (x 2) ∧ project (x 1) ≠ project (x 2))).filter
      (fun x => (fun j => residue h (x j)) ∈ orbitFinset (MainGroup h) C)).filter
      (fun x => (integralMatrix x).det = t),
      LiftingProbability.auxiliaryWeight q s w V (fun j => residue q (x j))) =
      ∑ A ∈ fixedDetEvent N h C t, matrixWeight q s w V A := by
  rw [← sum_fixedDet_event N h q s C t w V]
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      fixedDetProperty_integralMatrix, Homogeneous.projectedDistinct,
      integralMatrix_project]
    tauto
  · intro x hx
    rfl

end Problem355.IntegerMatrixEvents

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ZeroGlobalCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.ZeroGlobalCount

open Matrix PrimitiveNormal ZeroDeterminantCount
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma countConstant_nonneg {Ca Cg Cd : ℝ}
    (ha : 0 ≤ Ca) (hg : 0 ≤ Cg) (hd : 0 ≤ Cd) :
    0 ≤ countConstant Ca Cg Cd := by
  unfold countConstant planeConstant
  positivity

end Problem355.ZeroGlobalCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AuxiliaryZeroCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.AuxiliaryZeroCount

open Matrix PrimitiveNormal ZeroDeterminantCount LiftingProbability
open scoped BigOperators

lemma countConstant_nonneg : 0 ≤ countConstant :=
  ZeroGlobalCount.countConstant_nonneg (by norm_num) (by positivity) (by positivity)

end Problem355.AuxiliaryZeroCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.AnisotropicCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.Anisotropic

open Matrix
open scoped Matrix
open PrimitiveNormal

theorem anisotropic_constant_pos :
    0 < 35721000 * Real.pi ^ 3 / (Real.log 2) ^ 2 := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

end Problem355.Anisotropic

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.NonzeroWeightedCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.NonzeroWeightedCount

open Matrix
open scoped BigOperators Matrix

lemma anisotropicConstant_pos : 0 < anisotropicConstant :=
  Anisotropic.anisotropic_constant_pos

lemma latticeConstant_pos : 0 < latticeConstant := by
  unfold latticeConstant
  exact mul_pos (mul_pos anisotropicConstant_pos (by positivity)) (by norm_num)

lemma boxConstant_pos : 0 < boxConstant := by
  unfold boxConstant
  exact mul_pos (mul_pos latticeConstant_pos (by norm_num)) (by positivity)

end Problem355.NonzeroWeightedCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.UniformFixedFiberCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace Problem355.UniformFixedFiberCount

open Finset

lemma commonConstant_nonneg {Czero Cnonzero : ℝ}
    (hzero : 0 ≤ Czero) (hnonzero : 0 ≤ Cnonzero) :
    0 ≤ commonConstant Czero Cnonzero := by
  unfold commonConstant
  positivity

lemma countConstant_nonneg : 0 ≤ countConstant :=
  commonConstant_nonneg AuxiliaryZeroCount.countConstant_nonneg
    (mul_nonneg (by norm_num) NonzeroWeightedCount.boxConstant_pos.le)

end Problem355.UniformFixedFiberCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.TypedFixedFiberCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Problem355.TypedFixedFiberCount

open Matrix IntegerSampling OrbitSampling IntegerMatrixEvents
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem orbitEvent_filter_det (N h : ℕ) [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) (t : ℤ) :
    (orbitEvent N h C).filter (fun A => A.det = t) = fixedDetEvent N h C t := by
  ext A
  simp only [orbitEvent, fixedDetEvent, fixedDetProperty, Finset.mem_filter]
  tauto

theorem orbitEvent_reduction {N h : ℕ} [NeZero h]
    {C : Fin 3 → Fin 3 → ZMod h} {A : IntMatrix}
    (hA : A ∈ orbitEvent N h C) :
    A.map (Int.castRingHom (ZMod h)) ∈ Section04Orbit.slOrbit (transpose C) := by
  exact fixedDetProperty_reduction
    (show fixedDetProperty h C A.det A from ⟨(Finset.mem_filter.mp hA).2.1,
      (Finset.mem_filter.mp hA).2.2, rfl⟩)

theorem orbitEvent_box {N h : ℕ} [NeZero h]
    {C : Fin 3 → Fin 3 → ZMod h} {A : IntMatrix}
    (hA : A ∈ orbitEvent N h C) (j : Fin 3) :
    Homogeneous.InBox (N : ℝ) (fun i => (A i j : ℝ)) := by
  have hAm := (Finset.mem_filter.mp hA).1
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hAm
  exact IntegerPointLaw.column_inBox (x j)

theorem orbitEvent_projections {N h : ℕ} [NeZero h]
    {C : Fin 3 → Fin 3 → ZMod h} {A : IntMatrix}
    (hA : A ∈ orbitEvent N h C) (i j : Fin 3) (hij : i ≠ j) :
    Homogeneous.project (Homogeneous.integerColumn A i) ≠
      Homogeneous.project (Homogeneous.integerColumn A j) := by
  apply fixedDetEvent_projections (t := A.det) (h := h) (C := C) (N := N) _ i j hij
  rw [← orbitEvent_filter_det]
  exact Finset.mem_filter.mpr ⟨hA, rfl⟩

end Problem355.TypedFixedFiberCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.ActualWeightedFiberCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
attribute [local irreducible] Problem355.heilbronnT
  Problem355.heilbronnM

namespace Problem355.ActualPointLaw

open Matrix Parameters IntegerSampling OrbitSampling IntegerMatrixEvents
open TypedFixedFiberCount
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem weightedFiberBound_of_matrix_count (K : ℝ)
    (hraw : ∀ {B k q : ℕ} (_ : B.Prime) [Fact q.Prime],
      ∀ (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
        (d : PrimePowerData B k C)
        (L : AuxiliarySampling.Law q ((B ^ k) ^ 2)),
      (B ^ k).Coprime q → ((B : ℝ) ^ k) ^ 26 ≤ (q : ℝ) →
      ∀ (N : ℕ), 1 ≤ N → ∀ (S : Finset IntMatrix),
      (∀ A ∈ S, A.map (Int.castRingHom (ZMod (B ^ k))) ∈
        Section04Orbit.slOrbit C) →
      (∀ A ∈ S, ∀ j, Homogeneous.InBox (N : ℝ) (fun i => (A i j : ℝ))) →
      (∀ A ∈ S, ∀ i j : Fin 3, i ≠ j →
        PlaneRowTransport.projectedColumn A i ≠ PlaneRowTransport.projectedColumn A j) →
      ∀ t : ℤ, |t| < (q : ℤ) →
      (∑ A ∈ S.filter (fun A => A.det = t),
        LiftingProbability.auxiliaryWeight q L.size L.weight L.sets
          (A.map (Int.castRingHom (ZMod q))).col) ≤
        K * Real.log (2 * (N : ℝ)) ^ 2 * (N : ℝ) ^ 6 /
          ((B : ℝ) ^ d.b * (B : ℝ) ^ d.e) ^ 2)
    {r : ℕ} [Fact r.Prime] (D : PrimeParameterData heilbronnK r)
    [Fact D.q.Prime] (aux : AuxiliarySampling.Law D.q (D.h ^ 2)) :
    WeightedFiberBound D aux K := by
  classical
  let : NeZero D.B := ⟨D.base_prime.ne_zero⟩
  let : NeZero (D.B ^ heilbronnK) := ⟨pow_ne_zero _ D.base_prime.ne_zero⟩
  unfold WeightedFiberBound
  intro z t ht
  have hparam : ((D.B : ℝ) ^ heilbronnK) ^ 26 ≤ (D.q : ℝ) := by
    exact_mod_cast (Nat.pow_le_pow_right (pow_pos D.base_prime.pos heilbronnK)
      (by norm_num : 26 ≤ 100)).trans D.auxiliary_lower.le
  have htq : |t| < (D.q : ℤ) :=
    ht.trans_lt (by exact_mod_cast D.tau_lt_q)
  have hb := hraw D.base_prime
    (transpose (fun j => MainDigitLaw.column D (z j))) (latentSmith D z) aux
    D.coprime hparam D.N D.N_pos
    (orbitEvent D.N (D.B ^ heilbronnK) (fun j => MainDigitLaw.column D (z j)))
    (fun A hA => orbitEvent_reduction hA)
    (fun A hA j => orbitEvent_box hA j)
    (fun A hA i j hij => orbitEvent_projections hA i j hij) t htq
  change (∑ A ∈ (orbitEvent D.N (D.B ^ heilbronnK)
      (fun j => MainDigitLaw.column D (z j))).filter (fun A => A.det = t),
      matrixWeight D.q aux.size aux.weight aux.sets A) ≤ _ at hb
  rw [orbitEvent_filter_det, ← sum_fixedDet_nested_event] at hb
  have hden : ((D.B : ℝ) ^ (latentSmith D z).b *
      (D.B : ℝ) ^ (latentSmith D z).e) ^ 2 =
      (((D.B ^ (latentSmith D z).b : ℕ) : ℝ) ^ 2 *
        ((D.B ^ (latentSmith D z).e : ℕ) : ℝ) ^ 2) := by
    rw [Nat.cast_pow, Nat.cast_pow, mul_pow]
  rw [hden] at hb
  exact hb

end Problem355.ActualPointLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem355.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT
  Problem355.heilbronnM

namespace Problem355

theorem heilbronn_power_lower_bound_oai :
    0 < heilbronnExponent ∧ ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point, Filter.Tendsto n Filter.atTop Filter.atTop ∧ ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧ triangleAreasAtLeast (P j) (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
  let Ct : ℝ := (128 / 7 : ℝ) * UniformFixedFiberCount.countConstant
  have hCt : 0 ≤ Ct :=
    mul_nonneg (by norm_num) UniformFixedFiberCount.countConstant_nonneg
  apply ParameterSampling.heilbronn_power_lower_bound_of_point_laws
    8 Ct (by norm_num) hCt
  refine ⟨0, ?_⟩
  intro r _ hr _ D
  let : Fact r.Prime := ⟨hr⟩
  let : Fact D.q.Prime := ⟨D.auxiliary_prime⟩
  refine ⟨ActualPointLaw.pointLaw D, ActualPointLaw.pairProbability_le D, ?_⟩
  exact ActualPointLaw.tripleProbability_le_of_count D
    UniformFixedFiberCount.countConstant_nonneg
    (fun A => ActualPointLaw.weightedFiberBound_of_matrix_count
      UniformFixedFiberCount.countConstant
      @UniformFixedFiberCount.matrix_fiber_le D A)

end Problem355

end

end OAI
end

theorem solution : type_of% @OAI.Problem355.heilbronn_power_lower_bound_oai := @OAI.Problem355.heilbronn_power_lower_bound_oai
