-- Prove2me | solution 1 for OAI.MeanPayoff.Realizer.tree_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T01:11:43.887239+00:00
-- url     : https://prove2.me/submissions/55ed2cc5-625f-4d96-85a4-84176f31b6e5

import Mathlib
import Definitions.Def_RandomizedMeanPayoff
import Definitions.Def_OAIQ117R002

section
-- module Solutions.OAIQ117_RM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_FiniteBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff

theorem no_tight_sequence (G : Game) (p : Vec (Fin G.n))
    (v : ℕ → Fin G.n) (w : ℕ → ℤ)
    (h : ∀ k, p (v k) = (G.n + 1 : ℤ) * w k + 1 + p (v (k + 1))) : False := by
  have hmod : ∀ k : ℕ,
      p (v k) + (k : ℤ) ≡ p (v 0) [ZMOD (G.n + 1 : ℤ)] := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      apply Int.ModEq.trans _ ih
      apply Int.modEq_iff_dvd.mpr
      use w k
      have hk := h k
      push_cast
      linarith
  have hinj : Function.Injective (fun k : Fin (G.n + 1) => v k.val) := by
    intro i j hij
    change v i.val = v j.val at hij
    apply Fin.ext
    have hm := (hmod i.val).trans (hmod j.val).symm
    rw [hij] at hm
    have hc := Int.ModEq.add_left_cancel' (p (v j.val)) hm
    have hn : i.val ≡ j.val [MOD (G.n + 1)] :=
      Int.natCast_modEq_iff.mp (by simpa only [Nat.cast_add, Nat.cast_one] using hc)
    exact hn.eq_of_lt_of_lt i.isLt j.isLt
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hc
  omega

theorem comparison_step (G : Game) {a b y z : Vec (Fin G.n)}
    (hy : Subsolution (operator G) a b y)
    (hz : Supersolution (operator G) a b z)
    {d : ℤ} (hd : 0 < d) (hdev : ∀ j, y j - z j ≤ d)
    (i : Fin G.n) (hi : y i - z i = d) :
    ∃ e : Fin G.m, G.tail e = i ∧
      y (G.head e) - z (G.head e) = d ∧
      y i = transformed G e + y (G.head e) := by
  have hay : a i < y i := by have hzi : a i ≤ z i := hz.1.1 i; omega
  have hzb : z i < b i := by have hyi : y i ≤ b i := hy.1.2 i; omega
  have hys := hy.2 i hay
  have hzs := hz.2 i hzb
  have hmono : operator G y i ≤ operator G z i + d := by
    have hm := (operator_laws G).mono (a := y) (b := shift z d)
      (fun j => by have := hdev j; dsimp [shift]; omega) i
    rw [(operator_laws G).translation] at hm
    exact hm
  have hyeq : y i = operator G y i := by omega
  have hzeq : z i = operator G z i := by omega
  by_cases ho : G.maxOwner i = true
  · obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_sup' (outgoing_nonempty G i)
      (fun e => transformed G e + y (G.head e))
    have htail : G.tail e = i := (Finset.mem_filter.mp he).2
    have hye : y i = transformed G e + y (G.head e) := by
      rw [hyeq, operator, ite_eq_left ho]; exact heq
    have hzle : transformed G e + z (G.head e) ≤ z i := by
      rw [hzeq, operator, ite_eq_left ho]
      exact Finset.le_sup' (fun e => transformed G e + z (G.head e)) he
    exact ⟨e, htail, by have := hdev (G.head e); omega, hye⟩
  · obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_inf' (outgoing_nonempty G i)
      (fun e => transformed G e + z (G.head e))
    have htail : G.tail e = i := (Finset.mem_filter.mp he).2
    have hze : z i = transformed G e + z (G.head e) := by
      rw [hzeq, operator, ite_eq_right ho]; exact heq
    have hyle : y i ≤ transformed G e + y (G.head e) := by
      rw [hyeq, operator, ite_eq_right ho]
      exact Finset.inf'_le (fun e => transformed G e + y (G.head e)) he
    have hj := hdev (G.head e)
    exact ⟨e, htail, by omega, by omega⟩

theorem box_comparison (G : Game) {a b y z : Vec (Fin G.n)}
    (hy : Subsolution (operator G) a b y)
    (hz : Supersolution (operator G) a b z) : y ≤ z := by
  classical
  let : Nonempty (Fin G.n) := ⟨⟨0, G.positive⟩⟩
  let d : ℤ := Finset.univ.sup' Finset.univ_nonempty (fun i => y i - z i)
  have hdev : ∀ i, y i - z i ≤ d := fun i =>
    Finset.le_sup' (fun j => y j - z j) (Finset.mem_univ i)
  by_contra h
  change ¬ (∀ i, y i ≤ z i) at h
  obtain ⟨k, hk⟩ := not_forall.mp h
  have hd : 0 < d := by have := hdev k; omega
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin G.n))
    (fun i => y i - z i)
  let S := {i : Fin G.n // y i - z i = d}
  let s₀ : S := ⟨v, hv.symm⟩
  have hs : ∀ s : S, ∃ e : Fin G.m, G.tail e = s.val ∧
      y (G.head e) - z (G.head e) = d ∧
      y s.val = transformed G e + y (G.head e) :=
    fun s => comparison_step G hy hz hd hdev s.val s.property
  choose edge hedge using hs
  let next : S → S := fun s => ⟨G.head (edge s), (hedge s).2.1⟩
  let path : ℕ → S := fun k => next^[k] s₀
  apply no_tight_sequence G y (fun k => (path k).val)
    (fun k => G.weight (edge (path k)))
  intro k
  have heq := (hedge (path k)).2.2
  simpa only [path, Function.iterate_succ_apply', next, transformed] using heq

theorem transformed_le_bound (G : Game) (e : Fin G.m) : |transformed G e| ≤ weightBound G := by
  have h := Finset.le_sup (f := fun e : Fin G.m => (transformed G e).natAbs) (Finset.mem_univ e)
  have hc : ((transformed G e).natAbs : ℤ) ≤
      ((Finset.univ.sup (fun e : Fin G.m => (transformed G e).natAbs) : ℕ) : ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at hc
  exact hc.trans (le_max_right _ _)

end MeanPayoff

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Budgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff

namespace RandomTree

theorem expect_mono_all {α : Type} (t : RandomTree α) (f g : α → ℚ)
    (h : t.All (fun a => f a ≤ g a)) : expect t f ≤ expect t g := by
  induction t with
  | leaf a => exact h
  | coin l r hl hr =>
    have := hl h.1
    have := hr h.2
    simp only [expect_coin]
    linarith

theorem all_of_forall {α : Type} (t : RandomTree α) {P : α → Prop} (h : ∀ a, P a) :
    t.All P := by
  induction t with
  | leaf a => exact h a
  | coin l r hl hr => exact ⟨hl, hr⟩

theorem all_mono {α : Type} (t : RandomTree α) {P Q : α → Prop}
    (h : t.All P) (hPQ : ∀ a, P a → Q a) : t.All Q := by
  induction t with
  | leaf a => exact hPQ a h
  | coin l r hl hr => exact ⟨hl h.1, hr h.2⟩

open scoped Classical

theorem trials_length {α : Type} (t : RandomTree α) (J : ℕ) :
    (trials t J).All (fun as => as.length = J) := by
  induction J with
  | zero => rfl
  | succ j hj =>
    rw [trials, all_bind]
    apply all_of_forall
    intro a
    rw [map, all_bind]
    exact all_mono _ hj (fun as hs => by simp [All, hs])

end RandomTree
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace RandomTree

theorem trials_all {α : Type} (t : RandomTree α) {P : α → Prop}
    (h : t.All P) (J : ℕ) : (trials t J).All (fun as => ∀ a ∈ as, P a) := by
  induction J with
  | zero => simp [trials, All]
  | succ j hj =>
    rw [trials, all_bind]
    apply all_mono _ h
    intro a ha
    rw [map, all_bind]
    apply all_mono _ hj
    intro as has
    simpa [All] using (show ∀ b ∈ a :: as, P b by simp_all)

theorem all_and {α : Type} (t : RandomTree α) {P Q : α → Prop}
    (hp : t.All P) (hq : t.All Q) : t.All (fun a => P a ∧ Q a) := by
  induction t with
  | leaf a => exact ⟨hp, hq⟩
  | coin l r hl hr => exact ⟨hl hp.1 hq.1, hr hp.2 hq.2⟩

end RandomTree


end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Deviation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

namespace SolveBox

theorem radius_bounds {n Bmax : ℕ} (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) :
    I.width ≤ 64 * globalS Bmax * I.D ∧ globalS Bmax * I.D ≤ I.E ∧
    32 * globalS Bmax * I.D ≤ I.width ∧ 8 * I.E ≤ I.width := by
  have hs := globalS_large Bmax
  have hd := Nat.div_mul_le_self I.width (32 * globalS Bmax)
  have hdm := Nat.div_add_mod I.width (32 * globalS Bmax)
  have hdr := Nat.mod_lt I.width (show 0 < 32 * globalS Bmax by omega)
  have he := Nat.div_mul_le_self I.width 8
  have hem := Nat.div_add_mod I.width 8
  have her := Nat.mod_lt I.width (show 0 < 8 by omega)
  change I.width ≤ 64 * globalS Bmax * (I.width / (32 * globalS Bmax)) ∧
    globalS Bmax * (I.width / (32 * globalS Bmax)) ≤ I.width / 8 ∧
    32 * globalS Bmax * (I.width / (32 * globalS Bmax)) ≤ I.width ∧
    8 * (I.width / 8) ≤ I.width
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

end SolveBox

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Orientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

theorem clog_double_decrease {B C : ℕ} (hB : 1 < B) (hC : 2 * C ≤ B) :
    Nat.clog 2 C + 1 ≤ Nat.clog 2 B := by
  have hp := Nat.le_pow_clog (by norm_num : 1 < 2) B
  cases hk : Nat.clog 2 B with
  | zero => simp only [hk, pow_zero] at hp; omega
  | succ k =>
    rw [hk, pow_succ] at hp
    have hc : C ≤ 2 ^ k := by omega
    have hh := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr hc
    omega

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Volume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

theorem orientationTail_length (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (I : SolveBox G.n Bmax) (qs : List (BoxVector I))
    (child : BoxVector I → RandomTree (Orientation P)) (M : ℕ)
    (hm : ∀ q, (child q).All (fun O => O.exceptions.length ≤ M)) :
    (orientationTail G P I qs child).All (fun O => O.exceptions.length ≤ M + 2) := by
  unfold orientationTail
  dsimp only
  split_ifs
  · change 1 ≤ M + 2
    omega
  · change 1 ≤ M + 2
    omega
  · rw [RandomTree.all_bind]
    apply RandomTree.all_of_forall
    intro j
    rw [RandomTree.map, RandomTree.all_bind]
    apply RandomTree.all_mono _ (hm _)
    intro O hO
    change (O.exceptions ++ [_, _]).length ≤ M + 2
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem orient_length (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    (orient G P hR lower I).All (fun O => O.exceptions.length ≤ 2 * Nat.clog 2 I.width + 1) := by
  by_cases hsmall : I.width ≤ 128 * globalS Bmax
  · rw [orient, dite_eq_left hsmall]
    change (orientBase G P I).exceptions.length ≤ _
    unfold orientBase
    dsimp only
    split_ifs <;> change 1 ≤ _ <;> omega
  · have hB : 128 * globalS Bmax < I.width := Nat.lt_of_not_ge hsmall
    rw [orient, dite_eq_right hsmall]
    dsimp only
    rw [RandomTree.all_bind]
    with_reducible
      refine RandomTree.all_of_forall (centerSteps P hR lower I hB (globalS Bmax) I.midpoint) ?_
    intro qs
    have hr := (I.radius_bounds hB).2.2.2
    have hs := globalS_large Bmax
    have hc := clog_double_decrease (by omega : 1 < I.width) (by omega : 2 * (2 * I.E) ≤ I.width)
    apply RandomTree.all_mono _ (orientationTail_length G P I qs _ (2 * Nat.clog 2 (2 * I.E) + 1)
      (fun q => orient_length G P hR lower (I.wideCentered hB q.val)))
    intro O hO
    omega
termination_by I.width
decreasing_by exact I.E_smaller

theorem flatten_length_bound {α : Type} (ls : List (List α)) (M : ℕ)
    (h : ∀ l ∈ ls, l.length ≤ M) : ls.flatten.length ≤ ls.length * M := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    have hl := h l (List.mem_cons_self ..)
    have ht := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    nlinarith only [hl, ht]

theorem orientPlus_length (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    (orientPlus (orient G P hR lower I) (globalJ G.n Bmax)).All
      (fun O => O.exceptions.length ≤ globalListBound G.n Bmax) := by
  rw [orientPlus, RandomTree.map, RandomTree.all_bind]
  have hall := RandomTree.trials_all _ (orient_length G P hR lower I) (globalJ G.n Bmax)
  have hh := RandomTree.all_and _ (RandomTree.trials_length _ _) hall
  apply RandomTree.all_mono _ hh
  intro os hos
  change (os.map Orientation.exceptions).flatten.length ≤ _
  have hf := flatten_length_bound (os.map Orientation.exceptions) (2 * Nat.clog 2 I.width + 1)
    (by
      intro l hl
      obtain ⟨O, hO, rfl⟩ := List.mem_map.mp hl
      exact hos.2 O hO)
  simp only [List.length_map, hos.1] at hf
  have hc := Nat.clog_mono_right 2 (I.bounded.trans (Nat.le_succ Bmax))
  change Nat.clog 2 I.width ≤ Nat.clog 2 (Bmax + 1) at hc
  have hcg : 2 * Nat.clog 2 I.width + 1 ≤ 2 * globalG Bmax + 3 := by unfold globalG; omega
  exact hf.trans (Nat.mul_le_mul_left _ hcg)


open scoped Classical

end MeanPayoff

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_ErrorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace RandomTree

theorem map_bind {α β γ : Type} (t : RandomTree α) (f : α → RandomTree β) (g : β → γ) :
    (t.bind f).map g = t.bind (fun a => (f a).map g) := by
  induction t with
  | leaf a => rfl
  | coin l r il ir => simpa only [map, bind] using congrArg₂ coin il ir

end RandomTree

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_CountedTraversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

theorem rootBudgets_parameter (G : Game) : (rootBudgets G).parameter = (G.n : ℚ) ^ 3 := by
  simp [Budgets.parameter, Budgets.totalDensity, Budgets.density, mass, rootBudgets]
  ring

namespace Counted

@[simp] theorem erase_bind {α β : Type} (t : Counted α) (f : α → Counted β) :
    (t.bind f).erase = t.erase.bind (fun a => (f a).erase) := by
  simp [erase, bind, RandomTree.map_bind]

theorem bounded_pure {α : Type} (a : α) {N : ℕ} : (pure a).Bounded N := Nat.zero_le N

theorem bounded_lift {α : Type} (t : RandomTree α) : (lift t).Bounded 0 := by
  apply (RandomTree.all_map _ _ _).mpr
  exact RandomTree.all_of_forall _ (fun _ => le_rfl)

theorem bounded_mono {α : Type} {t : Counted α} {N M : ℕ} (h : t.Bounded N) (hle : N ≤ M) :
    t.Bounded M := RandomTree.all_mono _ h (fun _ hp => hp.trans hle)

theorem bounded_map {α β : Type} {t : Counted α} (f : α → β) {N : ℕ} (h : t.Bounded N) :
    (t.map f).Bounded N := (RandomTree.all_map _ _ _).mpr h

theorem bounded_charge {α : Type} {t : Counted α} (c : ℕ) {N : ℕ} (h : t.Bounded N) :
    (t.charge c).Bounded (c + N) := by
  apply (RandomTree.all_map _ _ _).mpr
  exact RandomTree.all_mono _ h (fun _ hp => Nat.add_le_add_left hp c)

theorem bounded_bind {α β : Type} {t : Counted α} (f : α → Counted β) {N M : ℕ}
    (h : t.Bounded N) (hf : ∀ a, (f a).Bounded M) : (t.bind f).Bounded (N + M) := by
  change (t.tree.bind _).All _
  rw [RandomTree.all_bind]
  apply RandomTree.all_mono _ h
  intro p hp
  apply (RandomTree.all_map _ _ _).mpr
  exact RandomTree.all_mono _ (hf p.1) (fun q hq => Nat.add_le_add hp hq)

theorem bounded_bind_qualified {α β : Type} {t : Counted α} (f : α → Counted β)
    (P : α → Prop) {N M : ℕ} (h : t.Bounded N) (hp : t.erase.All P)
    (hf : ∀ a, P a → (f a).Bounded M) : (t.bind f).Bounded (N + M) := by
  change (t.tree.bind _).All _
  rw [RandomTree.all_bind]
  have hP : t.tree.All (fun p => P p.1) := (RandomTree.all_map _ _ _).mp hp
  apply RandomTree.all_mono _ (RandomTree.all_and _ h hP)
  intro p hp
  apply (RandomTree.all_map _ _ _).mpr
  exact RandomTree.all_mono _ (hf p.1 hp.2) (fun q hq => Nat.add_le_add hp.1 hq)

@[simp] theorem erase_trials {α : Type} (t : Counted α) (J : ℕ) :
    (trials t J).erase = RandomTree.trials t.erase J := by
  induction J with
  | zero => rfl
  | succ J ih => simp [trials, RandomTree.trials, ih]

@[simp] theorem erase_traverse {α β : Type} (f : α → Counted β) (as : List α) :
    (traverse f as).erase = RandomTree.traverse (fun a => (f a).erase) as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [traverse, RandomTree.traverse, ih]

theorem bounded_trials {α : Type} {t : Counted α} {N : ℕ} (h : t.Bounded N) (J : ℕ) :
    (trials t J).Bounded (J * N) := by
  induction J with
  | zero => exact bounded_pure _
  | succ J ih =>
    simpa [trials, Nat.succ_mul, Nat.add_comm] using
      bounded_bind (fun a => (trials t J).map (a :: ·)) h (fun a => bounded_map _ ih)

theorem bounded_traverse {α β : Type} (f : α → Counted β) {N : ℕ}
    (h : ∀ a, (f a).Bounded N) (as : List α) : (traverse f as).Bounded (as.length * N) := by
  induction as with
  | nil => exact bounded_pure _
  | cons a as ih =>
    simpa only [traverse, List.length_cons, Nat.add_mul, one_mul, Nat.add_comm] using
      bounded_bind (fun b => (traverse f as).map (b :: ·)) (h a) (fun b => bounded_map _ ih)

end Counted
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_CountedRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff


@[simp] theorem SolveBox.erase_repeated {n Bmax : ℕ} (I : SolveBox n Bmax)
    (t : Counted (BoxVector I)) (J : ℕ) :
    (I.repeatedCounted t J).erase = I.repeated t.erase J := by
  simp [SolveBox.repeatedCounted, SolveBox.repeated]

theorem SolveBox.bounded_repeated {n Bmax : ℕ} (I : SolveBox n Bmax)
    {t : Counted (BoxVector I)} {N : ℕ} (h : t.Bounded N) (J : ℕ) :
    (I.repeatedCounted t J).Bounded (J * N) :=
  Counted.bounded_map _ (Counted.bounded_trials h J)

namespace CountedAlgorithm

@[simp] theorem erase_centerUpdate {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (q : BoxVector I) :
    (centerUpdate P hR lower I hB q).erase =
    MeanPayoff.centerUpdate P hR (eraseLower lower) I hB q := by
  simp [centerUpdate, MeanPayoff.centerUpdate, eraseLower]

@[simp] theorem erase_centerSteps {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (t : ℕ) (q : BoxVector I) :
    (centerSteps P hR lower I hB t q).erase =
    MeanPayoff.centerSteps P hR (eraseLower lower) I hB t q := by
  induction t generalizing q with
  | zero => rfl
  | succ t ih => simp only [centerSteps, MeanPayoff.centerSteps, Counted.erase_bind,
      erase_centerUpdate, Counted.erase_map, ih]

@[simp] theorem erase_orientationTail (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (I : SolveBox G.n Bmax) (qs : List (BoxVector I))
    (child : BoxVector I → Counted (Orientation P)) :
    (orientationTail G P I qs child).erase =
    MeanPayoff.orientationTail G P I qs (fun q => (child q).erase) := by
  unfold orientationTail MeanPayoff.orientationTail
  dsimp only
  split_ifs <;> simp

@[simp] theorem erase_orient (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    (orient G P hR lower I).erase = MeanPayoff.orient G P hR (eraseLower lower) I := by
  rw [orient, MeanPayoff.orient]
  split_ifs with h
  · rfl
  · simp only [Counted.erase_bind, erase_centerSteps, erase_orientationTail]
    apply congrArg (RandomTree.bind _)
    funext qs
    apply congrArg (MeanPayoff.orientationTail G P I qs)
    funext q
    exact erase_orient G P hR lower (I.wideCentered (lt_of_not_ge h) q.val)
termination_by I.width
 decreasing_by exact I.E_smaller

@[simp] theorem erase_orientPlus {n : ℕ} {P : Budgets n}
    (t : Counted (Orientation P)) (J : ℕ) :
    (orientPlus t J).erase = MeanPayoff.orientPlus t.erase J := by
  simp [orientPlus, MeanPayoff.orientPlus]

@[simp] theorem erase_tighten {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) :
    (tighten P hR lower I hB).erase = MeanPayoff.tighten P hR (eraseLower lower) I hB := by
  rw [tighten, MeanPayoff.tighten]
  simp only [Counted.erase_bind, SolveBox.erase_repeated]
  congr 1
  funext r₁
  split_ifs with h₁
  · simp only [Counted.erase_map, erase_tighten P hR lower (I.withFloor r₁) hB]
  · simp only [Counted.erase_bind, SolveBox.erase_repeated]
    congr 1
    funext r₂
    split_ifs with h₂
    · simp only [Counted.erase_map, erase_tighten P hR lower (I.withCeiling r₂) hB]
    · rfl
termination_by volume I.b I.a
 decreasing_by
  · apply volume_decreases r₁.property.1 r₁.property.2
    obtain ⟨i, hi⟩ := h₁
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega
  · apply volume_ceiling_decreases r₂.property.1 r₂.property.2
    obtain ⟨i, hi⟩ := h₂
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega

@[simp] theorem erase_finishChoice (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (hR : 1 ≤ P.parameter) (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) (O : Orientation P)
    (up : Counted (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : Counted (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le))) :
    (finishChoice G P hR lower I hB O up lo).erase =
    MeanPayoff.finishChoice G P hR (eraseLower lower) I hB O up.erase lo.erase := by
  unfold finishChoice MeanPayoff.finishChoice
  split_ifs <;> simp [eraseLower]

@[simp] theorem erase_solveWidth (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (hR : 1 ≤ P.parameter) (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    (solveWidth G P hR lower I).erase = MeanPayoff.solveWidth G P hR (eraseLower lower) I := by
  rw [solveWidth, MeanPayoff.solveWidth, Counted.erase_charge]
  split_ifs with hB
  · rfl
  · simp only [Counted.erase_bind, erase_tighten]
    congr 1
    funext T
    simp only [erase_orientPlus, erase_orient]
    congr 1
    funext O
    simp only [Counted.erase_map, erase_finishChoice]
    congr 2
    · exact erase_solveWidth G P hR lower _
    · exact erase_solveWidth G P hR lower _
termination_by I.width
 decreasing_by
  all_goals
    change T.box.C < I.width
    rw [← T.width_eq]
    exact T.box.C_smaller (by rw [T.width_eq]; omega)

@[simp] theorem erase_solve (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax) :
    (solve G P I).erase = MeanPayoff.solve G P I := by
  rw [solve, MeanPayoff.solve]
  split_ifs with hR
  · rfl
  · rw [erase_solveWidth]
    congr 1
    funext Q h K
    exact erase_solve G Q K
termination_by parameterRank P.parameter

end CountedAlgorithm
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

theorem volume_add {n : ℕ} {a r b : Vec (Fin n)} (har : a ≤ r) (hrb : r ≤ b) :
    volume b a = volume b r + volume r a := by
  unfold volume
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have ha : a i ≤ r i := har i
  have hb : r i ≤ b i := hrb i
  change (b i - a i).toNat = (b i - r i).toNat + (r i - a i).toNat
  omega

theorem volume_floor_drop {n Bmax : ℕ} (I : SolveBox n Bmax) (r : BoxVector I)
    (h : ∃ i, (I.delta : ℤ) ≤ r.val i - I.a i) :
    volume (I.withFloor r).b (I.withFloor r).a + I.delta ≤ volume I.b I.a := by
  obtain ⟨i, hi⟩ := h
  have hcoord : I.delta ≤ (r.val i - I.a i).toNat := by omega
  have hv : I.delta ≤ volume r.val I.a := hcoord.trans
    (Finset.single_le_sum (fun j _ => Nat.zero_le ((r.val j - I.a j).toNat)) (Finset.mem_univ i))
  have heq := volume_add r.property.1 r.property.2
  change volume I.b r.val + I.delta ≤ volume I.b I.a
  omega

theorem volume_ceiling_drop {n Bmax : ℕ} (I : SolveBox n Bmax) (r : BoxVector I)
    (h : ∃ i, (I.delta : ℤ) ≤ I.b i - r.val i) :
    volume (I.withCeiling r).b (I.withCeiling r).a + I.delta ≤ volume I.b I.a := by
  obtain ⟨i, hi⟩ := h
  have hcoord : I.delta ≤ (I.b i - r.val i).toNat := by omega
  have hv : I.delta ≤ volume I.b r.val := hcoord.trans
    (Finset.single_le_sum (fun j _ => Nat.zero_le ((I.b j - r.val j).toNat)) (Finset.mem_univ i))
  have heq := volume_add r.property.1 r.property.2
  change volume r.val I.a + I.delta ≤ volume I.b I.a
  omega

theorem quotient_drop {v w d : ℕ} (hd : 0 < d) (h : w + d ≤ v) : w / d + 1 ≤ v / d := by
  have hh := Nat.div_le_div_right (c := d) h
  rwa [Nat.add_div_right _ hd] at hh

namespace CountedAlgorithm

theorem bounded_centerUpdate {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox n Bmax) (hB : 128 * globalS Bmax < I.width) (q : BoxVector I) :
    (centerUpdate P hR lower I hB q).Bounded (2 * globalJ n Bmax * N) := by
  unfold centerUpdate
  apply Counted.bounded_mono (Counted.bounded_bind _ (SolveBox.bounded_repeated _ (hN _ _ _) _)
    (fun _ => Counted.bounded_map _ (SolveBox.bounded_repeated _ (hN _ _ _) _)))
  nlinarith

theorem bounded_centerSteps {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox n Bmax) (hB : 128 * globalS Bmax < I.width) (t : ℕ) (q : BoxVector I) :
    (centerSteps P hR lower I hB t q).Bounded (t * (2 * globalJ n Bmax * N)) := by
  induction t generalizing q with
  | zero => exact Counted.bounded_pure _
  | succ t ih =>
    unfold centerSteps
    apply Counted.bounded_mono (Counted.bounded_bind _
      (bounded_centerUpdate P hR lower hN I hB q) (fun q' => Counted.bounded_map _ (ih q')))
    simp only [Nat.add_mul, one_mul]
    omega

theorem bounded_orientationTail (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (I : SolveBox G.n Bmax) (qs : List (BoxVector I))
    (child : BoxVector I → Counted (Orientation P)) {N : ℕ} (hN : ∀ q, (child q).Bounded N) :
    (orientationTail G P I qs child).Bounded N := by
  unfold orientationTail
  dsimp only
  split_ifs
  · exact Counted.bounded_pure _
  · exact Counted.bounded_pure _
  · simpa only [zero_add] using Counted.bounded_bind _ (Counted.bounded_lift _)
      (fun j => Counted.bounded_map _ (hN _))

theorem bounded_orient (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox G.n Bmax) :
    (orient G P hR lower I).Bounded
      ((Nat.clog 2 I.width + 1) * (globalS Bmax * (2 * globalJ G.n Bmax * N))) := by
  induction I using (measure (fun I : SolveBox G.n Bmax => I.width)).wf.induction with
  | h I ih =>
      rw [orient]
      split_ifs with hB
      · exact Counted.bounded_pure _
      · have hb : 128 * globalS Bmax < I.width := lt_of_not_ge hB
        have hs := globalS_large Bmax
        have hr := (I.radius_bounds hb).2.2.2
        have hc := clog_double_decrease (by omega : 1 < I.width) (by omega : 2 * (2 * I.E) ≤ I.width)
        have hchild : ∀ q : BoxVector I,
            (orient G P hR lower (I.wideCentered hb q.val)).Bounded
              ((Nat.clog 2 (2 * I.E) + 1) * (globalS Bmax * (2 * globalJ G.n Bmax * N))) := by
          intro q
          exact ih (I.wideCentered hb q.val) (by exact I.E_smaller)
        have htail := fun qs => bounded_orientationTail G P I qs _ hchild
        have hineq : globalS Bmax * (2 * globalJ G.n Bmax * N) +
            (Nat.clog 2 (2 * I.E) + 1) * (globalS Bmax * (2 * globalJ G.n Bmax * N)) ≤
            (Nat.clog 2 I.width + 1) * (globalS Bmax * (2 * globalJ G.n Bmax * N)) := by
          calc
            _ = (Nat.clog 2 (2 * I.E) + 1 + 1) * (globalS Bmax * (2 * globalJ G.n Bmax * N)) := by ring
            _ ≤ _ := Nat.mul_le_mul_right _ (Nat.add_le_add_right hc 1)
        dsimp only
        with_reducible
          exact Counted.bounded_mono
            (Counted.bounded_bind
              (t := centerSteps P hR lower I hb (globalS Bmax) I.midpoint)
              (fun qs => orientationTail G P I qs (fun q => orient G P hR lower (I.wideCentered hb q.val)))
              (bounded_centerSteps P hR lower hN I hb (globalS Bmax) I.midpoint) htail) hineq

theorem bounded_orient_global (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox G.n Bmax) :
    (orient G P hR lower I).Bounded
      ((globalG Bmax + 1) * (globalS Bmax * (2 * globalJ G.n Bmax * N))) := by
  apply Counted.bounded_mono (bounded_orient G P hR lower hN I)
  apply Nat.mul_le_mul_right
  have hh := Nat.clog_mono_right 2 (show I.width ≤ Bmax + 1 from I.bounded.trans (Nat.le_succ Bmax))
  unfold globalG
  omega

theorem bounded_orientPlus {n : ℕ} {P : Budgets n} {t : Counted (Orientation P)}
    {N : ℕ} (hN : t.Bounded N) (J : ℕ) : (orientPlus t J).Bounded (J * N) :=
  Counted.bounded_map _ (Counted.bounded_trials hN J)

theorem bounded_tighten {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox n Bmax) (hB : 128 * globalS Bmax < I.width) :
    (tighten P hR lower I hB).Bounded
      ((volume I.b I.a / I.delta + 1) * (2 * globalJ n Bmax * N)) := by
  rw [tighten]
  refine Counted.bounded_mono (Counted.bounded_bind (M := globalJ n Bmax * N +
    (volume I.b I.a / I.delta) * (2 * globalJ n Bmax * N)) _
    (SolveBox.bounded_repeated _ (hN _ _ _) _) ?_) ?_
  · intro r₁
    split_ifs with h₁
    · have hv := quotient_drop (I.delta_positive hB) (volume_floor_drop I r₁ h₁)
      apply Counted.bounded_mono (Counted.bounded_map _
        (bounded_tighten P hR lower hN (I.withFloor r₁) hB))
      change (volume (I.withFloor r₁).b (I.withFloor r₁).a / I.delta + 1) * _ ≤ _
      exact (Nat.mul_le_mul_right _ hv).trans (Nat.le_add_left _ _)
    · refine Counted.bounded_mono (Counted.bounded_bind (M :=
        (volume I.b I.a / I.delta) * (2 * globalJ n Bmax * N)) _
        (SolveBox.bounded_repeated _ (hN _ _ _) _) ?_) ?_
      · intro r₂
        split_ifs with h₂
        · have hv := quotient_drop (I.delta_positive hB) (volume_ceiling_drop I r₂ h₂)
          apply Counted.bounded_mono (Counted.bounded_map _
            (bounded_tighten P hR lower hN (I.withCeiling r₂) hB))
          change (volume (I.withCeiling r₂).b (I.withCeiling r₂).a / I.delta + 1) * _ ≤ _
          exact Nat.mul_le_mul_right _ hv
        · exact Counted.bounded_pure _
      · exact le_rfl
  · nlinarith
termination_by volume I.b I.a
 decreasing_by
  · have hv := volume_floor_drop I r₁ h₁
    have hd := I.delta_positive hB
    omega
  · have hv := volume_ceiling_drop I r₂ h₂
    have hd := I.delta_positive hB
    omega

end CountedAlgorithm


theorem widthPotential_bound (s B : ℕ) (hs : 0 < s) :
    widthPotential s B < 8 * s * (Nat.log 2 B + 2) := by
  have hp : 0 < 2 ^ Nat.log 2 B := pow_pos (by norm_num) _
  have hb := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) B
  rw [pow_succ] at hb
  have hd : 8 * s * B / 2 ^ Nat.log 2 B < 16 * s := by
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    nlinarith
  unfold widthPotential
  nlinarith

theorem widthPotential_decreases {s B C : ℕ} (hs : 0 < s) (hC : 0 < C)
    (hCB : C < B) (hdrop : B ≤ 8 * s * (B - C)) :
    widthPotential s C < widthPotential s B := by
  have hB : 0 < B := hC.trans hCB
  have hp : 0 < 2 ^ Nat.log 2 B := pow_pos (by norm_num) _
  have hpb : 2 ^ Nat.log 2 B ≤ B := Nat.pow_log_le_self 2 (by omega)
  have hlog : Nat.log 2 C ≤ Nat.log 2 B := Nat.log_mono_right hCB.le
  have hlower : 8 * s ≤ (8 * s * B) / 2 ^ Nat.log 2 B := by
    apply (Nat.le_div_iff_mul_le hp).mpr
    exact Nat.mul_le_mul_left _ hpb
  rcases eq_or_lt_of_le hlog with heq | hlt
  · have hsub : 8 * s * C + 2 ^ Nat.log 2 B ≤ 8 * s * B := by
      have ht : C + (B - C) = B := Nat.add_sub_of_le hCB.le
      nlinarith
    have hdiv := Nat.div_le_div_right (c := 2 ^ Nat.log 2 B) hsub
    rw [Nat.add_div_right _ hp] at hdiv
    unfold widthPotential
    rw [heq]
    omega
  · have hc := widthPotential_bound s C hs
    have hm : 8 * s * (Nat.log 2 C + 2) ≤ 8 * s * (Nat.log 2 B + 1) := by
      apply Nat.mul_le_mul_left
      omega
    unfold widthPotential at hc ⊢
    nlinarith



theorem SolveBox.delta_lower {n Bmax : ℕ} (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) : I.width ≤ 8 * globalS Bmax * I.delta := by
  have hs := globalS_large Bmax
  have hp := I.delta_positive hB
  have hd := Nat.lt_mul_div_succ I.width (by omega : 0 < 4 * globalS Bmax)
  change I.width < 4 * globalS Bmax * (I.delta + 1) at hd
  nlinarith

theorem SolveBox.volume_width {n Bmax : ℕ} (I : SolveBox n Bmax) :
    volume I.b I.a ≤ n * I.width := by
  calc
    _ ≤ ∑ _i : Fin n, I.width := Finset.sum_le_sum (fun i _ => (Int.toNat_le).mpr (I.width_bound i))
    _ = _ := by simp

theorem SolveBox.tightening_passes {n Bmax : ℕ} (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) : volume I.b I.a / I.delta ≤ 8 * n * globalS Bmax := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (I.delta_positive hB)).mpr
  have hm := Nat.mul_le_mul_left n (I.delta_lower hB)
  have hv := I.volume_width
  have hd := I.delta_positive hB
  nlinarith

theorem SolveBox.C_potential {n Bmax : ℕ} (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) :
    widthPotential (globalS Bmax) I.C < widthPotential (globalS Bmax) I.width := by
  apply widthPotential_decreases (by have hh := globalS_large Bmax; omega)
    I.C_positive (I.C_smaller hB)
  have h := I.delta_lower hB
  have hd := I.delta_smaller
  have he : I.width - I.C = I.delta := by unfold SolveBox.C; omega
  simpa only [he, Nat.mul_assoc] using h

namespace CountedAlgorithm

theorem bounded_tighten_global {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox n Bmax) (hB : 128 * globalS Bmax < I.width) :
    (tighten P hR lower I hB).Bounded ((16 * n * globalS Bmax + 2) * globalJ n Bmax * N) := by
  apply Counted.bounded_mono (bounded_tighten P hR lower hN I hB)
  calc
    _ ≤ (8 * n * globalS Bmax + 1) * (2 * globalJ n Bmax * N) :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_right (I.tightening_passes hB) 1)
    _ = _ := by ring

theorem bounded_finishChoice (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (hR : 1 ≤ P.parameter) (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width) (O : Orientation P)
    (up : Counted (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : Counted (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le)))
    {M : ℕ} (hu : up.Bounded M) (hl : lo.Bounded M) :
    (finishChoice G P hR lower I hB O up lo).Bounded
      (O.exceptions.length * (globalJ G.n Bmax * N) + M) := by
  unfold finishChoice
  split_ifs
  · exact Counted.bounded_bind _
      (Counted.bounded_traverse _ (fun H => I.bounded_repeated (hN _ _ _) _) _)
      (fun _ => Counted.bounded_map _ hu)
  · exact Counted.bounded_bind _
      (Counted.bounded_traverse _ (fun H => I.bounded_repeated (hN _ _ _) _) _)
      (fun _ => Counted.bounded_map _ hl)

end CountedAlgorithm
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_RootBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

namespace CountedAlgorithm

theorem bounded_solveWidth (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox G.n Bmax) :
    (solveWidth G P hR lower I).Bounded
      ((widthPotential (globalS Bmax) I.width + 1) * (1 + auxiliaryCalls G.n Bmax * N)) := by
  rw [solveWidth]
  split_ifs with hB
  · apply Counted.bounded_mono (Counted.bounded_charge 1 (Counted.bounded_pure _ (N := 0)))
    exact Nat.mul_le_mul (by omega : 1 ≤ widthPotential (globalS Bmax) I.width + 1)
      (by omega : 1 ≤ 1 + auxiliaryCalls G.n Bmax * N)
  · have hb : 128 * globalS Bmax < I.width := lt_of_not_ge hB
    have htight := bounded_tighten_global P hR lower hN I hb
    have hafter : ∀ T : InnerBox I,
        ((orientPlus (orient G P hR lower T.box) (globalJ G.n Bmax)).bind fun O =>
          (finishChoice G P hR lower T.box (by rw [T.width_eq]; exact hb) O
            (solveWidth G P hR lower
              (T.box.capHigh T.box.C T.box.C_positive
                (T.box.C_smaller (by rw [T.width_eq]; exact hb)).le))
            (solveWidth G P hR lower
              (T.box.capLow T.box.C T.box.C_positive
                (T.box.C_smaller (by rw [T.width_eq]; exact hb)).le))).map T.include).Bounded
        (globalJ G.n Bmax * ((globalG Bmax + 1) * (globalS Bmax * (2 * globalJ G.n Bmax * N))) +
          (globalListBound G.n Bmax * (globalJ G.n Bmax * N) +
            widthPotential (globalS Bmax) I.width * (1 + auxiliaryCalls G.n Bmax * N))) := by
      intro T
      have hK : 128 * globalS Bmax < T.box.width := by rw [T.width_eq]; exact hb
      have hpot : widthPotential (globalS Bmax) T.box.C + 1 ≤
          widthPotential (globalS Bmax) I.width := by
        have hp := T.box.C_potential hK
        rw [T.width_eq] at hp
        omega
      have hup := bounded_solveWidth G P hR lower hN
        (T.box.capHigh T.box.C T.box.C_positive (T.box.C_smaller hK).le)
      have hlo := bounded_solveWidth G P hR lower hN
        (T.box.capLow T.box.C T.box.C_positive (T.box.C_smaller hK).le)
      have hmul := Nat.mul_le_mul_right (1 + auxiliaryCalls G.n Bmax * N) hpot
      have hu := Counted.bounded_mono hup hmul
      have hl := Counted.bounded_mono hlo hmul
      have horient := bounded_orientPlus (bounded_orient_global G P hR lower hN T.box) (globalJ G.n Bmax)
      have hlen : (orientPlus (orient G P hR lower T.box) (globalJ G.n Bmax)).erase.All
          (fun O => O.exceptions.length ≤ globalListBound G.n Bmax) := by
        rw [erase_orientPlus, erase_orient]
        exact MeanPayoff.orientPlus_length G P hR (eraseLower lower) T.box
      apply Counted.bounded_bind_qualified _ _ horient hlen
      intro O hO
      apply Counted.bounded_map
      apply Counted.bounded_mono (bounded_finishChoice G P hR lower hN T.box hK O _ _ hu hl)
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hO) _
    have hbind := Counted.bounded_bind _ htight hafter
    apply Counted.bounded_mono (Counted.bounded_charge 1 hbind)
    unfold auxiliaryCalls
    ring_nf
    omega
termination_by I.width
 decreasing_by
  all_goals
    change T.box.C < I.width
    rw [← T.width_eq]
    exact T.box.C_smaller hK

theorem bounded_solveWidth_global (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox G.n Bmax) :
    (solveWidth G P hR lower I).Bounded (chainBound Bmax * (1 + auxiliaryCalls G.n Bmax * N)) := by
  apply Counted.bounded_mono (bounded_solveWidth G P hR lower hN I)
  apply Nat.mul_le_mul_right
  have hp := widthPotential_bound (globalS Bmax) I.width (by have hs := globalS_large Bmax; omega)
  have hm := Nat.log_mono_right (b := 2) I.bounded
  have hh := Nat.mul_le_mul_left (8 * globalS Bmax) (Nat.add_le_add_right hm 2)
  unfold chainBound
  omega

theorem bounded_solve (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax) :
    (solve G P I).Bounded (callBound G.n Bmax (parameterRank P.parameter)) := by
  rw [solve]
  have hb : 1 ≤ callBase G.n Bmax := by unfold callBase; omega
  split_ifs with hR
  · apply Counted.bounded_mono (Counted.bounded_charge 1 (Counted.bounded_pure _ (N := 0)))
    have hh := Nat.one_le_pow (parameterRank P.parameter + 1) _ hb
    simpa only [callBound, Nat.add_zero] using hh
  · have hlow : LowerBound (P := P) (Bmax := Bmax) (fun Q _ K => solve G Q K)
        (callBase G.n Bmax ^ parameterRank P.parameter) := by
      intro Q hq K
      apply Counted.bounded_mono (bounded_solve G Q K)
      apply Nat.pow_le_pow_right hb
      omega
    apply Counted.bounded_mono
      (bounded_solveWidth_global G P (le_of_not_gt hR) _ hlow I)
    have hp : 1 ≤ callBase G.n Bmax ^ parameterRank P.parameter :=
      Nat.one_le_pow _ _ hb
    unfold callBound
    rw [pow_succ]
    have hkp := Nat.mul_le_mul_left (chainBound Bmax) hp
    have hf : chainBound Bmax * (auxiliaryCalls G.n Bmax + 1) ≤ callBase G.n Bmax := by
      unfold callBase
      omega
    calc
      _ ≤ (chainBound Bmax * (auxiliaryCalls G.n Bmax + 1)) *
          callBase G.n Bmax ^ parameterRank P.parameter := by nlinarith only [hkp]
      _ ≤ _ := by
        simpa only [Nat.mul_comm] using
          Nat.mul_le_mul_left (callBase G.n Bmax ^ parameterRank P.parameter) hf
termination_by parameterRank P.parameter

end CountedAlgorithm


theorem parameterRank_nat_bound (r : ℕ) :
    parameterRank (r : ℚ) ≤ 8 * Nat.clog 2 (r + 1) := by
  apply Nat.find_min' (parameter_rank_exists (r : ℚ))
  have hpow : (9 / 10 : ℚ) ^ 8 ≤ 1 / 2 := by norm_num
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ (9 / 10) ^ 8) hpow
    (Nat.clog 2 (r + 1))
  rw [← pow_mul] at hh
  have hr : (r : ℚ) < (2 : ℚ) ^ Nat.clog 2 (r + 1) := by
    exact_mod_cast (lt_of_lt_of_le (Nat.lt_succ_self r) (Nat.le_pow_clog (by norm_num : 1 < 2) (r + 1)))
  have hp := mul_lt_mul_of_pos_left hr
    (by positivity : (0 : ℚ) < (1 / 2 : ℚ) ^ Nat.clog 2 (r + 1))
  have he : (1 / 2 : ℚ) ^ Nat.clog 2 (r + 1) * (2 : ℚ) ^ Nat.clog 2 (r + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [he] at hp
  exact (mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg r)).trans_lt hp

theorem rootRank_bound (G : Game) :
    parameterRank (rootBudgets G).parameter ≤ 24 * Nat.clog 2 (G.n + 1) := by
  rw [rootBudgets_parameter]
  have hr := parameterRank_nat_bound (G.n ^ 3)
  have hc : Nat.clog 2 (G.n ^ 3 + 1) ≤ 3 * Nat.clog 2 (G.n + 1) := by
    apply (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr
    have hn := Nat.le_pow_clog (by norm_num : 1 < 2) (G.n + 1)
    have hp := Nat.pow_le_pow_left hn 3
    rw [← pow_mul, Nat.mul_comm (Nat.clog 2 (G.n + 1)) 3] at hp
    exact (by nlinarith : G.n ^ 3 + 1 ≤ (G.n + 1) ^ 3).trans hp
  have h := Nat.mul_le_mul_left 8 hc
  norm_num only [Nat.cast_pow] at hr
  omega


end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_InputSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

theorem input_n_le (G : Game) : G.n ≤ (input G).length := by
  simp only [input, List.length_append, List.length_ofFn]
  omega

theorem length_le_flatten {α : Type} {x : List α} {l : List (List α)}
    (h : x ∈ l) : x.length ≤ l.flatten.length := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have hh := ih h
      simp only [List.flatten_cons, List.length_append]
      omega

theorem input_weight_size_le (G : Game) (e : Fin G.m) :
    Nat.size ((G.weight e).natAbs + 1) ≤ (input G).length := by
  let f := fun e : Fin G.m =>
    encodeNat ((G.tail e).val + 1) ++ encodeNat ((G.head e).val + 1) ++ encodeInt (G.weight e)
  have hm : f e ∈ List.ofFn f := List.mem_ofFn.mpr ⟨e, rfl⟩
  have h := length_le_flatten hm
  dsimp [f] at h
  simp only [List.length_append, encodeNat_length, encodeInt_length] at h
  simp only [input, List.length_append, List.length_ofFn]
  omega

theorem input_weight_lt_pow (G : Game) (e : Fin G.m) :
    (G.weight e).natAbs + 1 < 2 ^ (input G).length :=
  Nat.size_le.mp (input_weight_size_le G e)



theorem input_weightBound_le (G : Game) :
    weightBound G ≤ ((G.n + 1) * 2 ^ (input G).length : ℕ) := by
  apply max_le
  · have hp : 1 ≤ 2 ^ (input G).length := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast (by nlinarith : 1 ≤ (G.n + 1) * 2 ^ (input G).length)
  · have hs : Finset.univ.sup (fun e : Fin G.m => (transformed G e).natAbs) ≤
        (G.n + 1) * 2 ^ (input G).length := by
      apply Finset.sup_le
      intro e _
      have hw := input_weight_lt_pow G e
      have ht := Int.natAbs_add_le ((G.n + 1) * G.weight e) 1
      simp only [Int.natAbs_mul, Int.natAbs_one] at ht
      change (transformed G e).natAbs ≤ _
      dsimp only [transformed]
      have hn : (G.n + 1 : ℤ) = ((G.n + 1 : ℕ) : ℤ) := by norm_cast
      rw [hn] at ht ⊢
      simp only [Int.natAbs_natCast] at ht
      exact ht.trans (by nlinarith)
    exact_mod_cast hs

theorem width_growth_bound {n w L : ℕ} (hn : n ≤ L) (hw : w ≤ (n + 1) * 2 ^ L) :
    8 * n * w ≤ 2 ^ (3 * L + 5) := by
  have hl : L + 1 ≤ 2 ^ (L + 1) := (Nat.lt_two_pow_self).le
  have hn2 : n * (n + 1) ≤ (L + 1) ^ 2 := by nlinarith
  have hb : 8 * n * w ≤ 8 * (L + 1) ^ 2 * 2 ^ L := by
    have hh := Nat.mul_le_mul_left (8 * n) hw
    have hh' := Nat.mul_le_mul_right (2 ^ L) (Nat.mul_le_mul_left 8 hn2)
    nlinarith only [hh, hh']
  have hp := Nat.pow_le_pow_left hl 2
  have hmul := Nat.mul_le_mul_left (8 * 2 ^ L) hp
  have hex : 8 * (2 ^ (L + 1)) ^ 2 * 2 ^ L = 2 ^ (3 * L + 5) := by
    rw [← pow_mul]
    calc
      _ = 2 ^ 3 * 2 ^ ((L + 1) * 2) * 2 ^ L := by rfl
      _ = 2 ^ (3 + (L + 1) * 2 + L) := by rw [← pow_add, ← pow_add]
      _ = _ := by congr 1; omega
  exact hb.trans (calc
    _ ≤ 8 * (2 ^ (L + 1)) ^ 2 * 2 ^ L := by
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
    _ = _ := hex)

theorem input_topWidth_le (G : Game) :
    (topWidth G).toNat ≤ 2 ^ (3 * (input G).length + 5) := by
  have hw := input_weightBound_le G
  have hw0 := (weightBound_positive G).le
  have hwN : (weightBound G).toNat ≤ (G.n + 1) * 2 ^ (input G).length :=
    Int.toNat_le.mpr hw
  have h := width_growth_bound (input_n_le G) hwN
  apply Int.toNat_le.mpr
  have hc : (8 : ℤ) * G.n * (weightBound G).toNat ≤ (2 : ℤ) ^ (3 * (input G).length + 5) :=
    by exact_mod_cast h
  rw [Int.toNat_of_nonneg hw0] at hc
  simpa only [topWidth, Nat.cast_pow, Nat.cast_ofNat] using hc

theorem input_globalG_le (G : Game) :
    globalG (topWidth G).toNat ≤ 3 * (input G).length + 7 := by
  have hb := input_topWidth_le G
  have hp : (topWidth G).toNat + 1 ≤ 2 ^ (3 * (input G).length + 6) := by
    rw [show 3 * (input G).length + 6 = (3 * (input G).length + 5) + 1 by omega, pow_succ]
    have hpos := Nat.one_le_pow (3 * (input G).length + 5) 2 (by norm_num)
    omega
  have hc := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr hp
  unfold globalG
  omega

theorem globalS_upper (Bmax : ℕ) : globalS Bmax < 2 ^ 18 * (globalG Bmax + 1) := by
  let a := 2 ^ 17 * (globalG Bmax + 1)
  have ha : 1 < a := by dsimp [a]; omega
  have he : 0 < Nat.clog 2 a :=
    (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mpr (by simpa using ha)
  have hh := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) ha
  calc
    globalS Bmax = 2 ^ (Nat.clog 2 a).pred * 2 := by
      change 2 ^ Nat.clog 2 a = _
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos he]
      rw [pow_succ]
    _ < a * 2 := Nat.mul_lt_mul_of_pos_right hh (by norm_num)
    _ = 2 ^ 18 * (globalG Bmax + 1) := by dsimp [a]; ring

theorem inputScale_large (G : Game) : 32 ≤ inputScale G := by unfold inputScale; omega

theorem inputScale_n (G : Game) : G.n + 1 ≤ inputScale G := by
  have hn := input_n_le G
  unfold inputScale
  omega

theorem inputScale_g (G : Game) : globalG (topWidth G).toNat + 1 ≤ inputScale G := by
  have hn := input_globalG_le G
  unfold inputScale
  omega

theorem inputScale_s (G : Game) : globalS (topWidth G).toNat ≤ inputScale G := by
  have hs := globalS_upper (topWidth G).toNat
  have hg := input_globalG_le G
  unfold inputScale
  omega

theorem inputScale_log (G : Game) : Nat.log 2 (topWidth G).toNat + 2 ≤ inputScale G := by
  have hm := Nat.log_mono_right (b := 2) (Nat.le_succ (topWidth G).toNat)
  change Nat.log 2 (topWidth G).toNat ≤ Nat.log 2 ((topWidth G).toNat + 1) at hm
  have hc := Nat.log_le_clog 2 ((topWidth G).toNat + 1)
  have hg := inputScale_g G
  unfold globalG at hg
  omega



theorem globalJ_scale {n B X : ℕ} (hX : 32 ≤ X) (hn : n + 1 ≤ X)
    (hs : globalS B ≤ X) : globalJ n B ≤ X ^ 14 := by
  have hx : 1 ≤ X := by omega
  have hp : globalS B * (n + 1) ≤ X ^ 2 := by nlinarith
  have hp6 := Nat.pow_le_pow_left hp 6
  rw [← pow_mul] at hp6
  change (globalS B * (n + 1)) ^ 6 ≤ X ^ 12 at hp6
  have hcoef : 2 * X ^ 12 + 1 ≤ X ^ 14 := by
    have h12 : 1 ≤ X ^ 12 := Nat.one_le_pow _ _ hx
    have hsq : 3 ≤ X ^ 2 := by nlinarith
    rw [show (14 : ℕ) = 12 + 2 by norm_num, pow_add]
    nlinarith only [h12, hsq]
  exact (by unfold globalJ; omega : globalJ n B ≤ 2 * X ^ 12 + 1).trans hcoef

theorem chainBound_scale {B X : ℕ} (hX : 32 ≤ X) (hs : globalS B ≤ X)
    (hl : Nat.log 2 B + 2 ≤ X) : chainBound B ≤ X ^ 3 := by
  have hsl := Nat.mul_le_mul hs hl
  have hx3 : 8 * X ^ 2 + 1 ≤ X ^ 3 := by
    have hsq : 1 ≤ X ^ 2 := by nlinarith
    nlinarith
  have hh : chainBound B ≤ 8 * X ^ 2 + 1 := by unfold chainBound; nlinarith only [hsl]
  exact hh.trans hx3

theorem globalListBound_scale {n B X : ℕ} (hX : 32 ≤ X)
    (hg : globalG B + 1 ≤ X) (hj : globalJ n B ≤ X ^ 14) :
    globalListBound n B ≤ X ^ 16 := by
  have hgg : 2 * globalG B + 3 ≤ X ^ 2 := by nlinarith
  have hmul := Nat.mul_le_mul hj hgg
  simpa only [globalListBound, ← pow_add] using hmul

theorem auxiliaryCalls_scale {n B X : ℕ} (hX : 32 ≤ X) (hn : n + 1 ≤ X)
    (hg : globalG B + 1 ≤ X) (hs : globalS B ≤ X) : auxiliaryCalls n B ≤ X ^ 32 := by
  have hx : 1 ≤ X := by omega
  have hj := globalJ_scale hX hn hs
  have hl := globalListBound_scale hX hg hj
  have hns := Nat.mul_le_mul (by omega : n ≤ X) hs
  have ht : 16 * n * globalS B + 2 ≤ X ^ 3 := by
    have hsq : 1 ≤ X ^ 2 := by nlinarith
    nlinarith
  have h1 : (16 * n * globalS B + 2) * globalJ n B ≤ X ^ 17 := by
    simpa only [← pow_add] using Nat.mul_le_mul ht hj
  have h2j : 2 * globalJ n B ≤ X ^ 15 := by
    have hp := Nat.mul_le_mul (by omega : 2 ≤ X) hj
    simpa only [← pow_succ'] using hp
  have h2 : globalJ n B * ((globalG B + 1) * (globalS B * (2 * globalJ n B))) ≤ X ^ 31 := by
    have hp := Nat.mul_le_mul hj (Nat.mul_le_mul hg (Nat.mul_le_mul hs h2j))
    have he : X ^ 14 * (X * (X * X ^ 15)) = X ^ 31 := by ring
    exact he ▸ hp
  have h3 : globalListBound n B * globalJ n B ≤ X ^ 30 := by
    simpa only [← pow_add] using Nat.mul_le_mul hl hj
  have hp17 : X ^ 17 ≤ X ^ 31 := Nat.pow_le_pow_right hx (by norm_num)
  have hp30 : X ^ 30 ≤ X ^ 31 := Nat.pow_le_pow_right hx (by norm_num)
  have hxmul : 3 * X ^ 31 ≤ X ^ 32 := by
    conv_rhs => rw [pow_succ']
    exact Nat.mul_le_mul_right (X ^ 31) (by omega : 3 ≤ X)
  unfold auxiliaryCalls
  omega

theorem callBase_scale {n B X : ℕ} (hX : 32 ≤ X) (hn : n + 1 ≤ X)
    (hg : globalG B + 1 ≤ X) (hs : globalS B ≤ X) (hl : Nat.log 2 B + 2 ≤ X) :
    callBase n B ≤ X ^ 37 := by
  have hx : 1 ≤ X := by omega
  have ha := auxiliaryCalls_scale hX hn hg hs
  have hk := chainBound_scale hX hs hl
  have hp : 1 ≤ X ^ 32 := Nat.one_le_pow _ _ hx
  have ha1 : auxiliaryCalls n B + 1 ≤ X ^ 33 := by
    rw [pow_succ]
    nlinarith only [hX, ha, hp]
  have hh := Nat.mul_le_mul hk ha1
  rw [← pow_add] at hh
  change chainBound B * (auxiliaryCalls n B + 1) ≤ X ^ 36 at hh
  have hp36 : 1 ≤ X ^ 36 := Nat.one_le_pow _ _ hx
  have hh1 : X ^ 36 + 1 ≤ X ^ 37 := by
    rw [pow_succ]
    nlinarith only [hX, hp36]
  unfold callBase
  omega



end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_BitDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace RandomTree
open scoped Classical

theorem prefix_sum {α : Type} (t : RandomTree α) (f : α → ℚ) (T : ℕ)
    (hT : t.bitDepth ≤ T) :
    ∑ bits : Fin T → Bool, f (t.readPrefix bits) = (2 : ℚ) ^ T * t.expect f := by
  induction T generalizing t with
  | zero =>
    cases t with
    | leaf a => simp [expect]
    | coin l r => simp [bitDepth] at hT
  | succ T ih =>
    cases t with
    | leaf a => simp [expect]
    | coin l r =>
      have hl : l.bitDepth ≤ T := by simp only [bitDepth] at hT; omega
      have hr : r.bitDepth ≤ T := by simp only [bitDepth] at hT; omega
      have he := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (T + 1) => Bool))
        (fun bits => f ((coin l r).readPrefix bits))
      rw [← he, Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, readPrefix_coin_cons]
      rw [Fintype.sum_bool]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih l hl, ih r hr]
      simp only [expect, pow_succ]
      ring

end RandomTree
end MeanPayoff

namespace MeanPayoff

theorem rootInvocationBound_nat (G : Game) :
    rootInvocationBound G ≤ 2 ^ (24000 * (Nat.clog 2 ((input G).length + 2)) ^ 2) := by
  let h := Nat.clog 2 ((input G).length + 2)
  let X := inputScale G
  have hh : 1 ≤ h := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mpr
    simp only [pow_zero]
    omega
  have hn := input_n_le G
  have hr := rootRank_bound G
  have hclog : Nat.clog 2 (G.n + 1) ≤ h :=
    Nat.clog_mono_right (b := 2) (by omega)
  have hrank : parameterRank (rootBudgets G).parameter + 1 ≤ 25 * h := by omega
  have hc := callBase_scale (inputScale_large G) (inputScale_n G) (inputScale_g G)
    (inputScale_s G) (inputScale_log G)
  have hx : X ≤ 2 ^ (24 + h) := by
    have hp := Nat.le_pow_clog (by norm_num : 1 < 2) ((input G).length + 2)
    have hm := Nat.mul_le_mul_left (2 ^ 24) hp
    simpa only [X, inputScale, pow_add] using hm
  have hx37 := Nat.pow_le_pow_left hx 37
  have hcall : callBase G.n (topWidth G).toNat ≤ 2 ^ ((24 + h) * 37) := by
    exact hc.trans (by simpa only [← pow_mul] using hx37)
  have hp := Nat.pow_le_pow_left hcall (parameterRank (rootBudgets G).parameter + 1)
  have he : (24 + h) * 37 * (parameterRank (rootBudgets G).parameter + 1) ≤ 24000 * h ^ 2 := by
    have h24 : 24 + h ≤ 25 * h := by omega
    have hm := Nat.mul_le_mul (Nat.mul_le_mul_right 37 h24) hrank
    nlinarith only [hm]
  unfold rootInvocationBound callBound
  exact hp.trans (by rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) he)


namespace RandomTree

theorem Path.all {α : Type} {t : RandomTree α} {a : α} {d : ℕ}
    (h : Path t a d) {P : α → Prop} (hp : t.All P) : P a := by
  induction h with
  | leaf a => exact hp
  | left h ih => exact ih hp.1
  | right h ih => exact ih hp.2

theorem Path.depth_le {α : Type} {t : RandomTree α} {a : α} {d : ℕ}
    (h : Path t a d) : d ≤ t.bitDepth := by
  induction h with
  | leaf a => exact le_rfl
  | left h ih => dsimp [bitDepth]; omega
  | right h ih => dsimp [bitDepth]; omega

end RandomTree

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Decoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace BinaryInput

theorem rawCode_lower (G : Game) : rawCode (lower G) = input G := by
  simp [rawCode, lower, input, List.map_ofFn, Function.comp_def, encodeEdge]

end BinaryInput
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Online
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace RandomTree

theorem consume_path {α : Type} (t : RandomTree α) (bits : ℕ → Bool) (pos : ℕ) :
    pos ≤ (t.consume bits pos).2 ∧
      Path t (t.consume bits pos).1 ((t.consume bits pos).2 - pos) := by
  induction t generalizing pos with
  | leaf a => exact ⟨le_rfl, by simp only [consume, Nat.sub_self]; exact .leaf a⟩
  | coin l r il ir =>
    simp only [consume]
    split
    · obtain ⟨hp, hh⟩ := ir (pos + 1)
      exact ⟨by omega, by convert Path.right (l := l) hh using 1 ; omega⟩
    · obtain ⟨hp, hh⟩ := il (pos + 1)
      exact ⟨by omega, by convert Path.left (r := r) hh using 1 ; omega⟩

theorem consume_read {α : Type} (t : RandomTree α) (bits : ℕ → Bool) (pos : ℕ) :
    (t.consume bits pos).1 = t.read (fun k => bits (pos + k)) := by
  induction t generalizing pos with
  | leaf a => rfl
  | coin l r il ir =>
    simp only [consume, read, Nat.add_zero]
    split
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ir (pos + 1)
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using il (pos + 1)

end RandomTree

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_SignedBits
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff
namespace SignedBits
open BinaryStack.Addition (value low carry full_adder)

theorem value_bound (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    cases b <;> simp only [value, Bool.toNat_false, Bool.toNat_true, List.length_cons, pow_succ] <;> omega

theorem val_negative (w : Word) : w.val < 0 ↔ w.sign = true := by
  cases w with
  | mk s xs =>
    have h : (value xs : ℤ) < 2 ^ xs.length := by exact_mod_cast value_bound xs
    cases s <;> simp [Word.val] ; omega

end SignedBits
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Instructions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.RegisterBits

theorem advance_front {K : ℕ} (P : Program K) (bits : ℕ → Bool) (c : Config P) (n : ℕ) :
    advance P bits c (n + 1) = advance P (fun j => bits (j + 1)) (step P c (bits 0)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step P (advance P bits c (n + 1)) (bits (n + 1)) = _
    rw [ih]; rfl

end MeanPayoff.RegisterBits
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Stack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace Counted
@[simp] theorem map_bind {α β γ : Type} (t : Counted α) (f : α → Counted β) (g : β → γ) :
    (t.bind f).map g = t.bind (fun a => (f a).map g) := by
  ext; simp [map, bind, RandomTree.map_bind]
@[simp] theorem bind_assoc {α β γ : Type} (t : Counted α) (f : α → Counted β) (g : β → Counted γ) :
    (t.bind f).bind g = t.bind (fun a => (f a).bind g) := by
  ext; simp [bind, RandomTree.map_bind, Nat.add_assoc]
@[simp] theorem charge_bind {α β : Type} (t : Counted α) (c : ℕ) (f : α → Counted β) :
    (t.charge c).bind f = (t.bind f).charge c := by
  ext; simp [charge, bind, RandomTree.map_bind, Nat.add_assoc]
end Counted
namespace SourceControl

theorem resume_denote {G : Game} {B : ℕ} {A C R : Result G B}
    (f : Frame G B A C) (v : A.Value) (k : Kont G B C R) :
    (resume f v k).bind State.denote = (f.denote v).bind k.denote := by
  cases f <;> simp only [resume, Frame.denote, Counted.pure_bind, Counted.bind_map,
    State.denote, Kont.denote, Counted.bind_assoc]

  case orientLoop P hR I hB =>
    unfold CountedAlgorithm.orientationTail
    try dsimp only
    split_ifs <;> simp only [Counted.pure_bind, Counted.bind_map, State.denote,
      Kont.denote, Frame.denote, Counted.bind_assoc, Job.denote]
  case tightenFirst P hR I hB =>
    split_ifs <;> simp only [Counted.pure_bind, Counted.bind_map, State.denote,
      Kont.denote, Frame.denote, Counted.bind_assoc, Job.denote]
  case tightenSecond P hR I hB =>
    split_ifs <;> simp only [Counted.pure_bind, Counted.bind_map, State.denote,
      Kont.denote, Frame.denote, Job.denote]
  case solveOriented P hR I hB =>
    unfold CountedAlgorithm.finishChoice
    try dsimp only
    cases v.chooseY <;> simp only [Bool.false_eq_true, ↓reduceIte, Job.denote, Counted.bind_assoc, wholeLower, Counted.bind_map]
  case solveReweighted P hR I hB side =>
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, Counted.pure_bind, State.denote, Kont.denote, Frame.denote, Job.denote,
      Counted.pure_bind, Counted.bind_map]

theorem solve_notSmall {G : Game} {B : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (I : SolveBox G.n B) : CountedAlgorithm.solve G P I =
      CountedAlgorithm.solveWidth G P hR (wholeLower P) I := by
  rw [CountedAlgorithm.solve, dite_eq_right (not_lt_of_ge hR)]

theorem step_denote {G : Game} {B : ℕ} {R : Result G B} (s : State G B R) :
    (step s).bind State.denote = s.denote := by
  cases s with
  | ret k v =>
    cases k with
    | done => simp only [step, State.denote, Counted.pure_bind]
    | push f k => exact resume_denote f v k
  | call j k =>
    cases j with
    | solve P I =>
      simp only [step, State.denote, Job.denote, Counted.charge_bind]
      rw [CountedAlgorithm.solve]
      split_ifs with hR hB
      · simp only [Counted.charge_bind, Counted.pure_bind, State.denote]
      · rw [CountedAlgorithm.solveWidth]
        simp only [dite_eq_left hB, Counted.charge_bind, Counted.pure_bind, State.denote]
      · rw [CountedAlgorithm.solveWidth]
        simp only [dite_eq_right hB, Counted.charge_bind, Counted.pure_bind,
          State.denote, Job.denote, Kont.denote, Frame.denote, Counted.bind_assoc]
        congr 2
        funext T
        simp only [solve_notSmall P (le_of_not_gt hR)]
    | ask P I =>
      simp only [step, State.denote, Job.denote, Counted.pure_bind,
        Kont.denote, Frame.denote, Counted.pure_bind, SolveBox.repeatedCounted,
        Counted.bind_map]
    | trials P I J =>
      cases J <;> simp only [step, State.denote, Job.denote, Counted.pure_bind,
        Kont.denote, Frame.denote, Counted.bind_assoc, Counted.trials, Counted.bind_map]
    | update P hR I hB q =>
      simp only [step, State.denote, Job.denote, Counted.pure_bind,
        Kont.denote, Frame.denote, Counted.bind_assoc, CountedAlgorithm.centerUpdate,
        wholeLower, Counted.bind_map]
    | centers P hR I hB t q =>
      cases t <;> simp only [step, State.denote, Job.denote, Counted.pure_bind,
        Kont.denote, Frame.denote, Counted.bind_assoc, CountedAlgorithm.centerSteps,
        Counted.bind_map]
    | orient P hR I =>
      simp only [step, State.denote, Job.denote]
      rw [CountedAlgorithm.orient]
      split_ifs <;> simp only [Counted.pure_bind, State.denote, Job.denote,
        Kont.denote, Frame.denote, Counted.bind_assoc]
    | orientTrials P hR I J =>
      cases J <;> simp only [step, State.denote, Job.denote, Counted.pure_bind,
        Kont.denote, Frame.denote, Counted.bind_assoc, Counted.trials, Counted.bind_map]
    | orientPlus P hR I =>
      simp only [step, State.denote, Job.denote, Counted.pure_bind,
        Kont.denote, Frame.denote, Counted.pure_bind, CountedAlgorithm.orientPlus,
        Counted.bind_map]
    | tighten P hR I hB =>
      simp only [step, State.denote, Job.denote, Counted.pure_bind,
        Kont.denote, Frame.denote]
      rw [CountedAlgorithm.tighten, Counted.bind_assoc]
    | reweight P hR I side Hs =>
      cases Hs <;> simp only [step, State.denote, Job.denote, Counted.pure_bind,
        Kont.denote, Frame.denote, Counted.bind_assoc, Counted.traverse, Counted.bind_map]

end SourceControl

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_StackSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.SourceControl

theorem orientCredit_mono {n B v w : ℕ} (h : v ≤ w) :
    orientCredit n B v ≤ orientCredit n B w := by
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.clog_mono_right 2 h) 1)

theorem orientPlusCredit_mono {n B v w : ℕ} (h : v ≤ w) :
    orientPlusCredit n B v ≤ orientPlusCredit n B w := by
  unfold orientPlusCredit orientTrialsCredit
  gcongr
  exact orientCredit_mono h

theorem orientBase_credit (G : Game) {B : ℕ} (P : Budgets G.n) (I : SolveBox G.n B) :
    (Result.orientation (B := B) P).credit (orientBase G P I) = exceptionCredit G.n B := by
  simp only [orientBase]
  split_ifs <;> simp [Result.credit]

 theorem resume_credit {G : Game} {B : ℕ} {A C R : Result G B}
    (f : Frame G B A C) (v : A.Value) (k : Kont G B C R) :
    (resume f v k).tree.All (fun p => p.1.credit+1 ≤ A.credit v+f.credit+k.credit) := by
  cases f with
  | orientLoop P hR I hB =>
    simp only [resume]
    split_ifs
    · simp only [Counted.pure, RandomTree.All, State.credit, Result.credit,
        List.length_singleton, one_mul, Frame.credit]
      omega
    · simp only [Counted.pure, RandomTree.All, State.credit, Result.credit,
        List.length_singleton, one_mul, Frame.credit]
      omega
    · apply (RandomTree.all_map _ _ _).mpr
      apply (RandomTree.all_map _ _ _).mpr
      apply RandomTree.all_of_forall
      intro j
      simp only [State.credit, Job.credit, Kont.credit, Frame.credit,
        SolveBox.wideCentered, SolveBox.centered, Result.credit]
      omega
  | tightenFirst P hR I hB =>
    simp only [resume]
    split_ifs with h
    · have hd := quotient_drop (I.delta_positive hB) (volume_floor_drop I v h)
      have hm := Nat.mul_le_mul_right (tightenUnit G.n B) hd
      simp only [Counted.pure, RandomTree.All, State.credit, Job.credit,
        Kont.credit, Frame.credit, Result.credit, tightenCredit]
      have he : (I.withFloor v).delta = I.delta := rfl
      rw [he]
      omega
    · simp only [Counted.pure, RandomTree.All, State.credit, Job.credit,
        Kont.credit, Frame.credit, Result.credit]
      omega
  | tightenSecond P hR I hB =>
    simp only [resume]
    split_ifs with h
    · have hd := quotient_drop (I.delta_positive hB) (volume_ceiling_drop I v h)
      have hm := Nat.mul_le_mul_right (tightenUnit G.n B) hd
      simp only [Counted.pure, RandomTree.All, State.credit, Job.credit,
        Kont.credit, Frame.credit, Result.credit, tightenCredit]
      have he : (I.withCeiling v).delta = I.delta := rfl
      rw [he]
      omega
    · simp [Counted.pure, RandomTree.All, State.credit, Frame.credit, Result.credit]
  | solveTight P hR I hB =>
    simp only [resume, Counted.pure, RandomTree.All, State.credit, Job.credit,
      Kont.credit, Frame.credit, Result.credit, v.width_eq]
    omega
  | solveReweighted P hR I hB side =>
    cases side <;> simp [resume, Counted.pure, RandomTree.All, State.credit,
      Job.credit, Kont.credit, Frame.credit, Result.credit]
  | _ =>
    simp [resume, Counted.pure, RandomTree.All, State.credit, Job.credit,
      Kont.credit, Frame.credit, Result.credit, combineOrientations,
      reweightCredit, List.map_cons, List.length_append,
      Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

 theorem step_credit {G : Game} {B : ℕ} {R : Result G B} (s : State G B R)
    (h : ¬s.halted) :
    (step s).tree.All (fun p => p.1.credit+1 ≤ s.credit+controlAllowance G.n B*p.2) := by
  cases s with
  | ret k v =>
    cases k with
    | done => exact (h trivial).elim
    | push f k =>
      apply RandomTree.all_mono _ (resume_credit f v k)
      intro p hp
      simp only [State.credit, Kont.credit] at hp ⊢
      omega
  | call j k =>
    cases j with
    | solve P I =>
      simp only [step, Counted.charge]
      apply (RandomTree.all_map _ _ _).mpr
      split_ifs with hR hB
      · simp [Counted.pure, RandomTree.All, State.credit, Job.credit, Result.credit,
          controlAllowance]
      · simp [Counted.pure, RandomTree.All, State.credit, Job.credit, Result.credit,
          controlAllowance]
      · have hb : 128*globalS B < I.width := by omega
        have ht := Nat.mul_le_mul_right (tightenUnit G.n B)
          (Nat.add_le_add_right (I.tightening_passes hb) 1)
        have ho : orientPlusCredit G.n B I.width ≤ orientPlusCredit G.n B (B+1) :=
          orientPlusCredit_mono (I.bounded.trans (Nat.le_succ B))
        simp only [Counted.pure, RandomTree.All, State.credit, Job.credit, Kont.credit,
          Frame.credit, Result.credit, Nat.add_zero, Nat.mul_one]
        unfold tightenCredit controlAllowance
        omega
    | orient P hR I =>
      simp only [step]
      split_ifs with hB
      · simp only [Counted.pure, RandomTree.All, State.credit, Job.credit,
          orientBase_credit, Nat.mul_zero, Nat.add_zero]
        unfold orientCredit orientUnit
        have hm := Nat.le_mul_of_pos_left (centersCredit G.n B (globalS B)+2*exceptionCredit G.n B+3)
          (by omega : 0 < Nat.clog 2 I.width+1)
        omega
      · have hb : 128*globalS B < I.width := by omega
        have hs := globalS_large B
        have hr := (I.radius_bounds hb).2.2.2
        have hc := clog_double_decrease (by omega : 1 < I.width) (by omega : 2*(2*I.E) ≤ I.width)
        have hm := Nat.mul_le_mul_right (orientUnit G.n B) hc
        simp only [Counted.pure, RandomTree.All, State.credit, Job.credit,
          Kont.credit, Frame.credit, Nat.mul_zero, Nat.add_zero]
        unfold orientCredit
        calc
          _ = (Nat.clog 2 (2*I.E)+1)*orientUnit G.n B+orientUnit G.n B+k.credit := by
            unfold orientUnit
            omega
          _ ≤ Nat.clog 2 I.width*orientUnit G.n B+orientUnit G.n B+k.credit := by omega
          _ = _ := by rw [Nat.add_mul, one_mul]
    | trials P I t =>
      cases t <;> simp [step, Counted.pure, RandomTree.All, State.credit, Job.credit,
        Kont.credit, Frame.credit, Result.credit, trialCredit] ; omega
    | centers P hR I hB t q =>
      cases t <;> simp [step, Counted.pure, RandomTree.All, State.credit, Job.credit,
        Kont.credit, Frame.credit, Result.credit, centersCredit, Nat.add_mul] ; omega
    | orientTrials P hR I t =>
      cases t <;> simp [step, Counted.pure, RandomTree.All, State.credit, Job.credit,
        Kont.credit, Frame.credit, Result.credit, orientTrialsCredit, Nat.add_mul] ; omega
    | reweight P hR I side Hs =>
      cases Hs <;> simp [step, Counted.pure, RandomTree.All, State.credit, Job.credit,
        Kont.credit, Frame.credit, Result.credit, reweightCredit, exceptionCredit, Nat.add_mul] ; omega
    | _ =>
      simp [step, Counted.pure, RandomTree.All, State.credit, Job.credit,
        Kont.credit, Frame.credit, Result.credit, askCredit, updateCredit,
        orientPlusCredit, tightenCredit, tightenUnit, Nat.add_mul] ; omega

end MeanPayoff.SourceControl
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_ArithmeticBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff
namespace RandomTree

theorem maximum_le_iff {α : Type} (t : RandomTree α) (f : α → ℕ) (N : ℕ) :
    t.maximum f ≤ N ↔ t.All (fun a => f a ≤ N) := by
  induction t with
  | leaf a => rfl
  | coin l r hl hr => simp only [maximum, max_le_iff, All, hl, hr]

theorem all_le_maximum {α : Type} (t : RandomTree α) (f : α → ℕ) :
    t.All (fun a => f a ≤ t.maximum f) := (maximum_le_iff t f _).mp le_rfl

theorem maximum_add {α : Type} (t : RandomTree α) (f : α → ℕ) (c : ℕ) :
    t.maximum (fun a => c+f a) = c+t.maximum f := by
  induction t with
  | leaf a => rfl
  | coin l r hl hr => simp only [maximum, hl, hr, ← Nat.add_max_add_left]

theorem not_all_false {α : Type} (t : RandomTree α) : ¬t.All (fun _ => False) := by
  induction t with
  | leaf a => exact id
  | coin l r hl hr => exact fun h => hl h.1

end RandomTree
namespace Counted

theorem maximum_le_iff {α : Type} (t : Counted α) (N : ℕ) :
    t.maximum ≤ N ↔ t.Bounded N := RandomTree.maximum_le_iff _ _ _

theorem maximum_bind {α β : Type} (t : Counted α) (f : α → Counted β) :
    t.tree.All (fun p => p.2+(f p.1).maximum ≤ (t.bind f).maximum) := by
  have h := RandomTree.all_le_maximum (t.bind f).tree Prod.snd
  simp only [bind, RandomTree.all_bind, RandomTree.all_map] at h
  apply RandomTree.all_mono _ h
  intro p hp
  have hm := (RandomTree.maximum_le_iff (f p.1).tree (fun q => p.2+q.2) _).mpr hp
  simpa only [RandomTree.maximum_add, maximum, bind] using hm

end Counted
namespace SourceControl

theorem step_rank {G : Game} {B : ℕ} {R : Result G B} (s : State G B R)
    (h : ¬s.halted) : (step s).tree.All (fun p => p.1.rank < s.rank) := by
  have hc := step_credit s h
  have hm := Counted.maximum_bind (step s) State.denote
  rw [step_denote] at hm
  apply RandomTree.all_mono _ (RandomTree.all_and _ hc hm)
  intro p hp
  have hmul := Nat.mul_le_mul_left (controlAllowance G.n B) hp.2
  rw [Nat.mul_add] at hmul
  simp only [State.rank]
  omega

theorem run_halted {G : Game} {B : ℕ} {R : Result G B} (n : ℕ) (s : State G B R)
    (h : s.halted) : run n s = Counted.pure s := by
  cases s with
  | call j k => exact h.elim
  | ret k v =>
    cases k with
    | push f k => exact h.elim
    | done =>
      induction n with
      | zero => rfl
      | succ n ih => simpa only [run, step, Counted.pure_bind] using ih

theorem run_halts {G : Game} {B : ℕ} {R : Result G B} (n : ℕ) (s : State G B R)
    (hn : s.rank ≤ n) : (run n s).tree.All (fun p => p.1.halted) := by
  induction n generalizing s with
  | zero =>
    change s.halted
    by_contra h
    have hd := step_rank s h
    exact RandomTree.not_all_false (step s).tree
      (RandomTree.all_mono _ hd (fun p hp => by omega))
  | succ n ih =>
    by_cases h : s.halted
    · rw [run_halted _ _ h]
      exact h
    · simp only [run, Counted.bind, RandomTree.all_bind, RandomTree.all_map]
      apply RandomTree.all_mono _ (step_rank s h)
      intro p hp
      exact ih p.1 (by omega)

theorem run_denote {G : Game} {B : ℕ} {R : Result G B} (n : ℕ) (s : State G B R) :
    (run n s).bind State.denote = s.denote := by
  induction n generalizing s with
  | zero => exact Counted.pure_bind _ _
  | succ n ih => simp only [run, Counted.bind_assoc, ih, step_denote]

end SourceControl
end MeanPayoff
namespace MeanPayoff.SourceControl

theorem affine_power {a X d k c : ℕ} (hX : 1 ≤ X) (ha : a ≤ X^d)
    (hk : k+c ≤ X) : k*a+c ≤ X^(d+1) := by
  have hp : 1 ≤ X^d := Nat.one_le_pow _ _ hX
  have hm := Nat.mul_le_mul_left k ha
  have hh := Nat.mul_le_mul_right (X^d) hk
  rw [pow_succ]
  nlinarith only [hp, hm, hh]

theorem controlAllowance_scale {n B X : ℕ} (hX : 32 ≤ X) (hn : n+1 ≤ X)
    (hg : globalG B+1 ≤ X) (hs : globalS B ≤ X) :
    controlAllowance n B ≤ X^39 := by
  have hx : 1 ≤ X := by omega
  have hj := globalJ_scale hX hn hs
  have ha : askCredit n B ≤ X^15 := by
    simpa only [askCredit, trialCredit, Nat.add_assoc] using
      (affine_power hx hj (by omega : 3+3 ≤ X))
  have he : exceptionCredit n B ≤ X^16 := by
    simpa only [one_mul, exceptionCredit] using (affine_power hx ha (by omega : 1+3 ≤ X))
  have hu : updateCredit n B ≤ X^16 := by
    exact affine_power hx ha (by omega : 2+3 ≤ X)
  have hu3 : updateCredit n B+3 ≤ X^17 := by
    simpa only [one_mul] using (affine_power hx hu (by omega : 1+3 ≤ X))
  have hcent0 := Nat.mul_le_mul hs hu3
  have hcent0' : globalS B*(updateCredit n B+3) ≤ X^18 := by
    simpa only [← pow_succ'] using hcent0
  have hcent : centersCredit n B (globalS B) ≤ X^19 := by
    simpa only [centersCredit, one_mul] using (affine_power hx hcent0' (by omega : 1+1 ≤ X))
  have he19 : exceptionCredit n B ≤ X^19 := he.trans (Nat.pow_le_pow_right hx (by norm_num))
  have hunit0 : orientUnit n B ≤ 3*X^19+3 := by unfold orientUnit; omega
  have hunit : orientUnit n B ≤ X^20 := hunit0.trans (affine_power hx le_rfl (by omega : 3+3 ≤ X))
  have hoc : orientCredit n B (B+1) ≤ X^21 := by
    have h := Nat.mul_le_mul (by unfold globalG at hg; omega : Nat.clog 2 (B+1)+1 ≤ X) hunit
    simpa only [orientCredit, ← pow_succ'] using h
  have hoc3 : orientCredit n B (B+1)+3 ≤ X^22 := by
    simpa only [one_mul] using (affine_power hx hoc (by omega : 1+3 ≤ X))
  have hp0 : globalJ n B*(orientCredit n B (B+1)+3) ≤ X^36 := by
    simpa only [← pow_add] using Nat.mul_le_mul hj hoc3
  have hp : orientPlusCredit n B (B+1) ≤ X^37 := by
    simpa only [orientPlusCredit, orientTrialsCredit, Nat.add_assoc, one_mul] using
      (affine_power hx hp0 (by omega : 1+3 ≤ X))
  have htu : tightenUnit n B ≤ X^16 := affine_power hx ha (by omega : 2+5 ≤ X)
  have hns := Nat.mul_le_mul (by omega : n ≤ X) hs
  have hfact : 8*n*globalS B+1 ≤ X^3 := by
    have hsq : 8*n*globalS B+1 ≤ 8*X^2+1 := by nlinarith only [hns]
    exact hsq.trans (affine_power hx le_rfl (by omega : 8+1 ≤ X))
  have ht : (8*n*globalS B+1)*tightenUnit n B ≤ X^19 := by
    simpa only [← pow_add] using Nat.mul_le_mul hfact htu
  have ht37 := ht.trans (Nat.pow_le_pow_right hx (by norm_num : 19 ≤ 37))
  have hall : controlAllowance n B ≤ 2*X^37+7 := by unfold controlAllowance; omega
  exact (hall.trans (affine_power hx le_rfl (by omega : 2+7 ≤ X))).trans
    (Nat.pow_le_pow_right hx (by norm_num : 38 ≤ 39))

theorem rootControlBound_nat (G : Game) :
    rootControlBound G ≤ 2^(25000*(Nat.clog 2 ((input G).length+2))^2) := by
  let h := Nat.clog 2 ((input G).length+2)
  have hh : 1 ≤ h := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mpr
    simp only [pow_zero]
    omega
  have hk := controlAllowance_scale (inputScale_large G) (inputScale_n G)
    (inputScale_g G) (inputScale_s G)
  have hx : inputScale G ≤ 2^(24+h) := by
    have hp := Nat.le_pow_clog (by norm_num : 1 < 2) ((input G).length+2)
    have hm := Nat.mul_le_mul_left (2^24) hp
    simpa only [inputScale, pow_add] using hm
  have hk' : controlAllowance G.n (topWidth G).toNat ≤ 2^((24+h)*39) :=
    hk.trans (by simpa only [← pow_mul] using Nat.pow_le_pow_left hx 39)
  have hi := rootInvocationBound_nat G
  have ht := Nat.mul_le_mul hk' hi
  rw [← pow_add] at ht
  apply ht.trans
  apply Nat.pow_le_pow_right (by norm_num)
  change (24+h)*39+24000*h^2 ≤ 25000*h^2
  nlinarith only [hh]

end MeanPayoff.SourceControl
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_TreeDevices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.RegisterBits
open BinaryData.Take (advance_add)

theorem step_coinFree {K : ℕ} (P : Program K) (h : CoinFree P) (c : Config P) (b : Bool) :
    step P c b = step P c false := by
  cases hc : c.control with
  | none => simp [step,hc]
  | some q => simp only [step,hc]; rw [h q _ b]

theorem advance_coinFree {K : ℕ} (P : Program K) (h : CoinFree P) (c : Config P)
    (bits : ℕ → Bool) (n : ℕ) : advance P bits c n = advance P (fun _ => false) c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [advance,ih,step_coinFree P h]

end MeanPayoff.RegisterBits

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_OperatorDevices
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice
open BinaryData

namespace Order

theorem low_val (ab : SignedBits.Word × SignedBits.Word) : (low ab).val = min ab.1.val ab.2.val := by
  unfold low
  rw [Compare.testPair_eq]
  by_cases h : ab.1.val < ab.2.val
  · simp [h,min_eq_left (le_of_lt h)]
  · simp [h,min_eq_right (le_of_not_gt h)]

theorem high_val (ab : SignedBits.Word × SignedBits.Word) : (high ab).val = max ab.1.val ab.2.val := by
  unfold high
  rw [Compare.testPair_eq]
  by_cases h : ab.1.val < ab.2.val
  · simp [h,max_eq_right (le_of_lt h)]
  · simp [h,max_eq_left (le_of_not_gt h)]

end Order
end MeanPayoff.TreeDevice

namespace MeanPayoff.TreeDevice.EdgeScan
open BinaryData

theorem high_bounds (a : SignedBits.Word) (xs : List SignedBits.Word) :
    ∀ w ∈ a::xs, w.val ≤ (Fold.fold Order.high a xs).val := by
  induction xs generalizing a with
  | nil => intro w hw; simpa [Fold.fold] using List.mem_singleton.mp hw ▸ le_refl a.val
  | cons b bs ih =>
    intro w hw
    change w.val ≤ (Fold.fold Order.high (Order.high (a,b)) bs).val
    have hh := ih (Order.high (a,b)) _ (List.mem_cons_self ..)
    rcases List.mem_cons.mp hw with rfl | hw
    · exact (show w.val ≤ (Order.high (w,b)).val by rw [Order.high_val]; exact le_max_left _ _).trans hh
    rcases List.mem_cons.mp hw with rfl | hw
    · exact (show w.val ≤ (Order.high (a,w)).val by rw [Order.high_val]; exact le_max_right _ _).trans hh
    · exact ih _ _ (List.mem_cons_of_mem _ hw)

theorem low_bounds (a : SignedBits.Word) (xs : List SignedBits.Word) :
    ∀ w ∈ a::xs, (Fold.fold Order.low a xs).val ≤ w.val := by
  induction xs generalizing a with
  | nil => intro w hw; simpa [Fold.fold] using List.mem_singleton.mp hw ▸ le_refl a.val
  | cons b bs ih =>
    intro w hw
    change (Fold.fold Order.low (Order.low (a,b)) bs).val ≤ w.val
    have hh := ih (Order.low (a,b)) _ (List.mem_cons_self ..)
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hh.trans (by rw [Order.low_val]; exact min_le_left _ _)
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hh.trans (by rw [Order.low_val]; exact min_le_right _ _)
    · exact ih _ _ (List.mem_cons_of_mem _ hw)

theorem maxScan_exact (G : Game) (p : Vec (Fin G.n)) (v : Fin G.n) (z : Pair × List Pair)
    (hz : Represents G p v z) :
    (maxScan z).val = (outgoing G v).sup' (outgoing_nonempty G v)
      (fun e => transformed G e+p (G.head e)) := by
  apply le_antisymm
  · have hm := fold_mem Order.high high_mem (Add.sumPair z.1) (z.2.map Add.sumPair)
    change maxScan z ∈ (z.1::z.2).map Add.sumPair at hm
    obtain ⟨ab,hab,he⟩ := List.mem_map.mp hm
    obtain ⟨e,he',hev⟩ := hz.1 ab hab
    rw [← he,Add.sumPair_val,hev]
    exact Finset.le_sup' (fun e => transformed G e+p (G.head e)) he'
  · apply (Finset.sup'_le_iff _ _).2
    intro e he
    obtain ⟨ab,hab,hval⟩ := hz.2 e he
    have hb := high_bounds (Add.sumPair z.1) (z.2.map Add.sumPair) (Add.sumPair ab)
      (show Add.sumPair ab ∈ (z.1::z.2).map Add.sumPair from List.mem_map.mpr ⟨ab,hab,rfl⟩)
    simpa only [Add.sumPair_val,hval,maxScan] using hb

theorem minScan_exact (G : Game) (p : Vec (Fin G.n)) (v : Fin G.n) (z : Pair × List Pair)
    (hz : Represents G p v z) :
    (minScan z).val = (outgoing G v).inf' (outgoing_nonempty G v)
      (fun e => transformed G e+p (G.head e)) := by
  apply le_antisymm
  · apply (Finset.le_inf'_iff _ _).2
    intro e he
    obtain ⟨ab,hab,hval⟩ := hz.2 e he
    have hb := low_bounds (Add.sumPair z.1) (z.2.map Add.sumPair) (Add.sumPair ab)
      (show Add.sumPair ab ∈ (z.1::z.2).map Add.sumPair from List.mem_map.mpr ⟨ab,hab,rfl⟩)
    simpa only [Add.sumPair_val,hval,minScan] using hb
  · have hm := fold_mem Order.low low_mem (Add.sumPair z.1) (z.2.map Add.sumPair)
    change minScan z ∈ (z.1::z.2).map Add.sumPair at hm
    obtain ⟨ab,hab,he⟩ := List.mem_map.mp hm
    obtain ⟨e,he',hev⟩ := hz.1 ab hab
    rw [← he,Add.sumPair_val,hev]
    exact Finset.inf'_le (fun e => transformed G e+p (G.head e)) he'

theorem operator_exact (G : Game) (p : Vec (Fin G.n)) (v : Fin G.n) (z : Pair × List Pair)
    (hz : Represents G p v z) :
    (if G.maxOwner v then (maxScan z).val else (minScan z).val) = operator G p v := by
  simp only [operator,maxScan_exact G p v z hz,minScan_exact G p v z hz]

end MeanPayoff.TreeDevice.EdgeScan
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Sorting
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.Halve
open BinaryData

theorem halve_val (w : SignedBits.Word) : (halve w).val = w.val / 2 := by
  have hv := SignedBits.val_uncons w.sign w.digits
  change w.val = (SignedBits.head w.sign w.digits).toNat +
    2*(SignedBits.Word.mk w.sign w.digits.tail).val at hv
  have hb : (SignedBits.head w.sign w.digits).toNat ≤ 1 := by
    cases (SignedBits.head w.sign w.digits) <;> decide
  change (SignedBits.Word.mk w.sign w.digits.tail).val = _
  omega

end MeanPayoff.TreeDevice.Halve

namespace MeanPayoff.TreeDevice.Sort
open BinaryData

theorem bubble_val (w : W) (xs : List W) :
    (bubble w xs).map SignedBits.Word.val = bubbleInt w.val (xs.map SignedBits.Word.val) := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih => simp only [bubble,List.map_cons,bubbleInt,Order.low_val,ih,Order.high_val]

end MeanPayoff.TreeDevice.Sort
namespace MeanPayoff.TreeDevice.Sort
open BinaryData

theorem bubbleInt_perm (w : ℤ) (xs : List ℤ) : (bubbleInt w xs).Perm (w::xs) := by
  induction xs generalizing w with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    by_cases h : w ≤ x
    · simpa only [bubbleInt,min_eq_left h,max_eq_right h] using (ih x).cons w
    · simpa only [bubbleInt,min_eq_right (le_of_not_ge h),max_eq_left (le_of_not_ge h)] using
        ((ih w).cons x).trans (List.Perm.swap _ _ _)

theorem bubbleInt_sorted (w : ℤ) (xs : List ℤ) (hs : xs.Pairwise (· ≤ ·)) :
    (bubbleInt w xs).Pairwise (· ≤ ·) := by
  induction xs generalizing w with
  | nil => simp [bubbleInt]
  | cons x xs ih =>
    rw [List.pairwise_cons] at hs
    rw [bubbleInt,List.pairwise_cons]
    refine ⟨?_,ih _ hs.2⟩
    intro y hy
    have hm := (bubbleInt_perm (max w x) xs).mem_iff.mp hy
    rcases List.mem_cons.mp hm with rfl | hy
    · exact (min_le_left w x).trans (le_max_left w x)
    · exact (min_le_right w x).trans (hs.1 y hy)

theorem insert_sorted (w : W) (xs : List W) (hs : (xs.map SignedBits.Word.val).Pairwise (· ≤ ·)) :
    ((insert (w,xs)).map SignedBits.Word.val).Pairwise (· ≤ ·) := by
  rw [insert_eq,bubble_val]
  exact bubbleInt_sorted _ _ hs

theorem fold_sort_sorted (xs acc : List W) (hs : (acc.map SignedBits.Word.val).Pairwise (· ≤ ·)) :
    ((xs.foldl (fun a w => insert (w,a)) acc).map SignedBits.Word.val).Pairwise (· ≤ ·) := by
  induction xs generalizing acc with
  | nil => exact hs
  | cons w xs ih => exact ih _ (insert_sorted _ _ hs)

theorem sort_sorted (xs : List W) : ((sort xs).map SignedBits.Word.val).Pairwise (· ≤ ·) :=
  fold_sort_sorted xs [] (by simp)

theorem sort_values (xs : List W) :
    (sort xs).map SignedBits.Word.val = (xs.map SignedBits.Word.val).mergeSort (· ≤ ·) := by
  exact List.Perm.eq_of_pairwise' (sort_sorted xs) (List.pairwise_mergeSort' (· ≤ ·) _)
    (((sort_perm xs).map _).trans (List.mergeSort_perm _ _).symm)

end MeanPayoff.TreeDevice.Sort
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_ArithmeticDevices
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Median
open BinaryData

theorem halfStep_measure (s : State) :
    2*(halfStep s).2.length+(halfStep s).1.toNat = 2*s.2.length+s.1.toNat+1 := by
  rcases s with ⟨b,c⟩
  cases b <;> simp [halfStep] ; omega

theorem count_measure {α : Type} (xs : List α) (s : State) :
    let t := xs.foldl (fun s _ => halfStep s) s
    2*t.2.length+t.1.toNat = 2*s.2.length+s.1.toNat+xs.length := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons,List.length_cons]
    rw [ih,halfStep_measure]
    omega

theorem count_length {α : Type} (xs : List α) : (count xs).length = xs.length/2 := by
  have h := count_measure xs (false,[])
  have hb : (xs.foldl (fun s _ => halfStep s) (false,[])).1.toNat ≤ 1 := by
    cases (xs.foldl (fun s _ => halfStep s) (false,[])).1 <;> decide
  dsimp only at h
  simp only [List.length_nil,Bool.toNat_false] at h
  unfold count
  omega

end MeanPayoff.TreeDevice.Median
namespace MeanPayoff.TreeDevice.Median
open BinaryData

theorem val_headD (xs : List SignedBits.Word) (w : SignedBits.Word) :
    (xs.headD w).val = (xs.map SignedBits.Word.val).headD w.val := by
  cases xs <;> rfl

theorem value_exact (xs : List SignedBits.Word) :
    (median xs).val = medianInt (xs.map SignedBits.Word.val) := by
  rw [median,count_length,val_headD,List.map_drop,Sort.sort_values,zeroWord_val]
  by_cases h : xs.length=0
  · have hx : xs=[] := List.length_eq_zero_iff.mp h
    subst xs
    simp [medianInt]
  · have hp : 0 < (xs.map SignedBits.Word.val).length := by simp; omega
    have hi : xs.length/2 < ((xs.map SignedBits.Word.val).mergeSort (· ≤ ·)).length := by
      simp only [List.length_mergeSort,List.length_map]
      exact Nat.div_lt_self (by omega) (by omega)
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi,Option.getD_some]
    have hpos : 0 < xs.length := by omega
    simp only [medianInt,List.length_map,dite_eq_left hpos]

end MeanPayoff.TreeDevice.Median
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_BatchDevices
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.Graph
open BinaryData

theorem lookup_exact {n : ℕ} (p : Fin n → W) (i : Fin n) :
    lookup (codePot p,List.replicate i.val ()) = p i := by
  unfold lookup codePot
  rw [List.length_replicate,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn]
  simp [i.isLt]

theorem edgePair_exact (G : Game) (p : Fin G.n → W) (w : Fin G.m → W) (e : Fin G.m) :
    edgePair (codePot p,codeEdge G w e) = (w e,p (G.head e)) := by
  simp only [edgePair,codeEdge,lookup_exact]

theorem batch_represents (G : Game) (p : Fin G.n → W) (w : Fin G.m → W)
    (hw : ∀ e, (w e).val = transformed G e) (v : Fin G.n)
    (e : Fin G.m) (es : List (Fin G.m))
    (hes : ∀ f, f∈e::es ↔ f∈outgoing G v) :
    EdgeScan.Represents G (fun i => (p i).val) v
      (batch (codePot p,(codeEdge G w e,es.map (codeEdge G w)))) := by
  have eqs : (batch (codePot p,(codeEdge G w e,es.map (codeEdge G w)))).1::
      (batch (codePot p,(codeEdge G w e,es.map (codeEdge G w)))).2 =
      (e::es).map (fun f => (w f,p (G.head f))) := by
    simp only [batch,edgePair_exact,List.map_map,List.map_cons,Function.comp_def]
  constructor
  · intro ab hab
    rw [eqs] at hab
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hab
    exact ⟨f,(hes f).mp hf,by rw [hw]⟩
  · intro f hf
    refine ⟨(w f,p (G.head f)),?_,?_⟩
    · rw [eqs]
      exact List.mem_map.mpr ⟨f,(hes f).mpr hf,rfl⟩
    · rw [hw]

theorem vertex_exact (G : Game) (p : Fin G.n → W) (w : Fin G.m → W)
    (hw : ∀ e, (w e).val = transformed G e) (v : Fin G.n)
    (e : Fin G.m) (es : List (Fin G.m)) (hes : ∀ f, f∈e::es ↔ f∈outgoing G v) :
    (vertex (codePot p,(G.maxOwner v,(codeEdge G w e,es.map (codeEdge G w))))).val =
      operator G (fun i => (p i).val) v := by
  have hh := EdgeScan.operator_exact G (fun i => (p i).val) v _ (batch_represents G p w hw v e es hes)
  simpa only [vertex,apply_ite] using hh

end MeanPayoff.TreeDevice.Graph

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_OperatorCosts
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.Graph
open BinaryData

theorem codeVertex_exact (G : Game) (p : Fin G.n → W) (w : Fin G.m → W)
    (hw : ∀ e, (w e).val = transformed G e) (v : Fin G.n) :
    (vertex (codePot p,codeVertex G w v)).val = operator G (fun i => (p i).val) v := by
  apply vertex_exact G p w hw v _ _
  intro f
  rw [show firstEdge G v :: (outList G v).tail = outList G v from List.cons_head_tail (outList_ne_nil G v)]
  exact mem_outList G v f

end MeanPayoff.TreeDevice.Graph

namespace MeanPayoff.BinaryStack.Addition

theorem value_append (xs ys : List Bool) : value (xs++ys) = value xs+2^xs.length*value ys := by
  induction xs with
  | nil => simp [value]
  | cons b bs ih => simp only [List.cons_append,value,ih,List.length_cons,pow_succ]; ring

end MeanPayoff.BinaryStack.Addition
namespace MeanPayoff.TreeDevice.Multiply
open BinaryData

theorem step_val (s : State) (b : Bool) : (step (s,b)).2.val = 2*s.2.val + b.toNat*s.1.val := by
  cases b <;> simp [step,Add.sumPair_val]

theorem fold_val (s : State) (bs : List Bool) :
    (Fold.fold step s bs).2.val = 2^bs.length*s.2.val + (BinaryStack.Addition.value bs.reverse : ℤ)*s.1.val := by
  induction bs generalizing s with
  | nil => simp [Fold.fold,BinaryStack.Addition.value]
  | cons b bs ih =>
    change (Fold.fold step (step (s,b)) bs).2.val = _
    rw [ih,step_val,step_first,List.reverse_cons,BinaryStack.Addition.value_append]
    simp only [List.length_reverse,BinaryStack.Addition.value,Nat.cast_add,Nat.cast_mul,
      Nat.cast_pow,Nat.cast_ofNat,List.length_cons,pow_succ]
    ring

theorem exact (w : W) (bs : List Bool) : (multiply (w,bs)).val = w.val*BinaryStack.Addition.value bs := by
  rw [multiply,fold_val,List.reverse_reverse]
  simp [Median.zeroWord,SignedBits.Word.val,BinaryStack.Addition.value,mul_comm]

end MeanPayoff.TreeDevice.Multiply
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_WordDecoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.Prefix
open BinaryData

theorem length_prefix (n : ℕ) (c : Count) (xs : List Bool) :
    Fold.fold step (false,(c,[])) (List.replicate n true++false::xs) =
      (true,(List.replicate n ()++c,xs.reverse)) := by
  induction n generalizing c with
  | zero =>
    change Fold.fold step (true,(c,[])) xs = _
    rw [read_from_done]
    simp
  | succ n ih =>
    simp only [List.replicate_succ,List.cons_append,Fold.fold,List.foldl_cons]
    change Fold.fold step (false,(()::c,[])) (List.replicate n true++false::xs) = _
    rw [ih]
    congr 2
    apply List.ext_getElem <;> simp [Nat.add_assoc]

theorem exact (n : ℕ) (xs : List Bool) :
    read (List.replicate n true++false::xs) = (List.replicate n (),xs) := by
  simp [read,length_prefix]

end MeanPayoff.TreeDevice.Prefix

namespace MeanPayoff.TreeDevice.Split
open BinaryData

theorem fold_exact (xs acc : List Bool) (ks : Median.Count) (hk : ks.length ≤ xs.length) :
    Fold.fold step (acc,xs) ks = ((xs.take ks.length).reverse++acc,xs.drop ks.length) := by
  induction ks generalizing xs acc with
  | nil => simp [Fold.fold]
  | cons u ks ih =>
    cases xs with
    | nil => simp at hk
    | cons b bs =>
      change Fold.fold step (b::acc,bs) ks = _
      rw [ih bs (b::acc) (by simpa using hk)]
      simp [List.take_succ_cons,List.reverse_cons,List.append_assoc]

theorem exact (xs : List Bool) (ks : Median.Count) (hk : ks.length ≤ xs.length) :
    split (xs,ks) = (xs.take ks.length,xs.drop ks.length) := by
  simp [split,fold_exact xs [] ks hk]

end MeanPayoff.TreeDevice.Split

namespace MeanPayoff.TreeDevice.IntegerRead
open BinaryData

theorem nat_encode (n : ℕ) (suffix : List Bool) :
    readNat (encodeNat n++suffix) = (decrement (n+1).bits,suffix) := by
  unfold readNat
  rw [show encodeNat n++suffix = List.replicate (n+1).bits.length true++false::((n+1).bits++suffix) by simp [encodeNat,List.append_assoc]]
  rw [Prefix.exact]
  dsimp only
  rw [Split.exact _ _ (by simp)]
  simp

end MeanPayoff.TreeDevice.IntegerRead
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Counters
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Address
open BinaryData

theorem dec_val (w : W) : (dec w).val = w.val-1 := by
  rw [dec,Add.sumPair_val]
  simp [IntegerRead.minusOne,SignedBits.Word.val,sub_eq_add_neg,BinaryStack.Addition.value]
theorem test_eq (w : W) : test w = decide (0<w.val) := by
  rw [test,Compare.testPair_eq]
  rfl

theorem fold_stopped (w : W) (hw : w.val ≤ 0) (c : Count) (xs : List Bool) :
    Fold.fold step (w,c) xs = (w,c) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Fold.fold step (step ((w,c),x)) xs = _
    simpa only [step,test_eq,decide_eq_true_eq,not_lt_of_ge hw,↓reduceIte] using ih

theorem fold_count (n : ℕ) (w : W) (hw : w.val=n) (c : Count) (xs : List Bool)
    (hn : n ≤ xs.length) :
    (Fold.fold step (w,c) xs).2 = List.replicate n ()++c := by
  induction n generalizing w c xs with
  | zero => simp [fold_stopped w (by omega) c xs]
  | succ n ih =>
    cases xs with
    | nil => simp at hn
    | cons x xs =>
      have hp : test w = true := by simp [test_eq,hw]
      change (Fold.fold step (step ((w,c),x)) xs).2 = _
      simp only [step,hp,↓reduceIte]
      rw [ih (dec w) (by rw [dec_val,hw]; omega) (()::c) xs (by simpa using hn)]
      apply List.ext_getElem <;> simp [Nat.add_comm,Nat.add_left_comm]

theorem exact (n : ℕ) (w : W) (hw : w.val=n) (xs : List Bool) (hn : n≤xs.length) :
    read (w,xs) = List.replicate n () := by
  simp only [read,fold_count n w hw [] xs hn,List.append_nil]

end MeanPayoff.TreeDevice.Address
namespace MeanPayoff.TreeDevice.Header
open BinaryData

theorem numbers_exact (n m : ℕ) (suffix : List Bool) :
    numbers (encodeNat n++encodeNat m++suffix) =
      (IntegerRead.decrement (n+1).bits,(IntegerRead.decrement (m+1).bits,suffix)) := by
  simp [numbers,List.append_assoc,IntegerRead.nat_encode]

theorem word_val (n : ℕ) : (IntegerRead.decrement (n+1).bits).val = n := by
  rw [IntegerRead.decrement_val,BinaryStack.Addition.value_bits]
  simp

theorem exact (n m : ℕ) (owners suffix : List Bool) (ho : owners.length=n)
    (hm : m ≤ (encodeNat n++encodeNat m++owners++suffix).length) :
    read (encodeNat n++encodeNat m++owners++suffix) =
      (List.replicate n (),(List.replicate m (),(owners,suffix))) := by
  let xs := encodeNat n++encodeNat m++owners++suffix
  have hn : n≤xs.length := by simp only [xs,List.length_append]; omega
  have hn' := Address.exact n (IntegerRead.decrement (n+1).bits) (word_val n) xs hn
  have hm' := Address.exact m (IntegerRead.decrement (m+1).bits) (word_val m) xs hm
  have hnum : numbers xs = (IntegerRead.decrement (n+1).bits,(IntegerRead.decrement (m+1).bits,owners++suffix)) := by
    simpa only [xs,List.append_assoc] using numbers_exact n m (owners++suffix)
  change finish (xs,numbers xs)=_
  rw [hnum]
  change (Address.read (IntegerRead.decrement (n+1).bits,xs),
    Address.read (IntegerRead.decrement (m+1).bits,xs),
    Split.split (owners++suffix,Address.read (IntegerRead.decrement (n+1).bits,xs))) = _
  rw [hn',hm',Split.exact _ _ (by simp; omega)]
  simp [← ho]

end MeanPayoff.TreeDevice.Header
namespace MeanPayoff.TreeDevice.EdgeRead
open BinaryData

theorem words_exact (a b : ℕ) (w : ℤ) (suffix : List Bool) :
    words (BinaryInput.encodeEdge (a,b,w)++suffix) =
      (IntegerRead.decrement (a+2).bits,(IntegerRead.decrement (b+2).bits,(encodedWord w,suffix))) := by
  simp [words,BinaryInput.encodeEdge,List.append_assoc,IntegerRead.nat_encode,
    IntegerRead.readInt,encodeInt,IntegerRead.signed,encodedWord,Nat.add_assoc]

theorem exact (a b : ℕ) (w : ℤ) (bound suffix : List Bool) (ha : a≤bound.length) (hb : b≤bound.length) :
    read (bound,BinaryInput.encodeEdge (a,b,w)++suffix) =
      ((List.replicate a (),(List.replicate b (),encodedWord w)),suffix) := by
  have ha' : (Address.dec (IntegerRead.decrement (a+2).bits)).val=a := by
    rw [Address.dec_val,IntegerRead.decrement_val,BinaryStack.Addition.value_bits]; push_cast; omega
  have hb' : (Address.dec (IntegerRead.decrement (b+2).bits)).val=b := by
    rw [Address.dec_val,IntegerRead.decrement_val,BinaryStack.Addition.value_bits]; push_cast; omega
  simp only [read,words_exact,finish,edge,source,target]
  rw [Address.exact a _ ha' _ ha,Address.exact b _ hb' _ hb]

end MeanPayoff.TreeDevice.EdgeRead
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_ParserCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.EdgesRead
open BinaryData

theorem fold_exact (es : List BinaryInput.Edge) (env suffix : List Bool) (acc : List Edge)
    (hd : ∀ e∈es, e.1≤env.length ∧ e.2.1≤env.length) :
    Fold.fold (StreamFold.step EdgeRead.read) (env,(acc,code es++suffix)) (List.replicate es.length ()) =
      (env,((es.map lower).reverse++acc,suffix)) := by
  induction es generalizing acc with
  | nil => simp [code,Fold.fold]
  | cons e es ih =>
    have he := hd e (by simp)
    have hread := EdgeRead.exact e.1 e.2.1 e.2.2 env (code es++suffix) he.1 he.2
    have hc : code (e::es)++suffix=BinaryInput.encodeEdge e++(code es++suffix) := by simp [code,List.append_assoc]
    rw [hc]
    simp only [List.length_cons,List.replicate_succ,Fold.fold,List.foldl_cons]
    change Fold.fold (StreamFold.step EdgeRead.read)
      (StreamFold.step EdgeRead.read ((env,(acc,BinaryInput.encodeEdge e++(code es++suffix))),()))
      (List.replicate es.length ()) = _
    simp only [StreamFold.step,hread]
    change Fold.fold (StreamFold.step EdgeRead.read) (env,(lower e::acc,code es++suffix)) _ = _
    rw [ih (lower e::acc) (by intro x hx; exact hd x (by simp [hx]))]
    simp [List.reverse_cons,List.append_assoc]

theorem exact (es : List BinaryInput.Edge) (env suffix : List Bool)
    (hd : ∀ e∈es, e.1≤env.length ∧ e.2.1≤env.length) :
    read (env,(code es++suffix,List.replicate es.length ())) = (es.map lower,suffix) := by
  simp only [read,fold_exact es env suffix [] hd,List.append_nil,List.reverse_reverse]

end MeanPayoff.TreeDevice.EdgesRead
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_ArenaParsing
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.ArenaRead
open BinaryData

theorem code_length (es : List BinaryInput.Edge) : es.length≤(EdgesRead.code es).length := by
  induction es with
  | nil => simp [EdgesRead.code]
  | cons e es ih =>
    have he : 1≤(BinaryInput.encodeEdge e).length := by
      simp only [BinaryInput.encodeEdge,List.length_append,encodeNat_length,encodeInt_length]
      omega
    simp only [EdgesRead.code,List.map_cons,List.flatten_cons,List.length_append,List.length_cons] at *
    omega

theorem raw_exact (n : ℕ) (owners : List Bool) (es : List BinaryInput.Edge) (ho : owners.length=n)
    (hd : ∀ e∈es, e.1≤(encodeNat n++encodeNat es.length++owners++EdgesRead.code es).length ∧
      e.2.1≤(encodeNat n++encodeNat es.length++owners++EdgesRead.code es).length) :
    read (encodeNat n++encodeNat es.length++owners++EdgesRead.code es) =
      (List.replicate n (),(owners,es.map EdgesRead.lower)) := by
  let xs := encodeNat n++encodeNat es.length++owners++EdgesRead.code es
  have hm : es.length≤xs.length := by
    have h := code_length es
    simp only [xs,List.length_append]
    omega
  have hh := Header.exact n es.length owners (EdgesRead.code es) ho hm
  have he := EdgesRead.exact es xs [] hd
  simp only [List.append_nil] at he
  change finish (xs,Header.read xs)=_
  rw [hh]
  change (List.replicate n (),(owners,(EdgesRead.read (xs,(EdgesRead.code es,List.replicate es.length ()))).1))=_
  rw [he]

theorem game_exact (G : Game) :
    read (input G) = (List.replicate G.n (),(List.ofFn G.maxOwner,(BinaryInput.lower G).edges.map EdgesRead.lower)) := by
  let es := (BinaryInput.lower G).edges
  have hel : es.length=G.m := by simp [es,BinaryInput.lower]
  have hi : encodeNat G.n++encodeNat es.length++List.ofFn G.maxOwner++EdgesRead.code es = input G := by
    simpa [es,BinaryInput.rawCode,BinaryInput.lower,EdgesRead.code] using BinaryInput.rawCode_lower G
  rw [← hi]
  apply raw_exact _ _ _ (by simp)
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  rw [hi]
  exact ⟨(Nat.le_of_lt (G.tail i).isLt).trans (input_n_le G),(Nat.le_of_lt (G.head i).isLt).trans (input_n_le G)⟩

end MeanPayoff.TreeDevice.ArenaRead
namespace MeanPayoff.TreeDevice.Scale
open BinaryData

theorem fold_val (s : State) (xs : Count) : (Fold.fold step s xs).2.val=s.2.val+xs.length*s.1.val := by
  induction xs generalizing s with
  | nil => simp [Fold.fold]
  | cons b bs ih =>
    change (Fold.fold step (step (s,b)) bs).2.val=_
    rw [ih,step_val,step_first,List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

theorem exact (w : W) (xs : Count) : (scale (w,xs)).val=(xs.length+1 : ℤ)*w.val := by
  rw [scale,fold_val]
  ring

theorem transform_val (w : W) (xs : Count) :
    (transform (w,xs)).val=(xs.length+1 : ℤ)*w.val+1 := by
  rw [transform,Add.sumPair_val,exact]
  simp [oneWord,SignedBits.Word.val,BinaryStack.Addition.value]

end MeanPayoff.TreeDevice.Scale
namespace MeanPayoff.TreeDevice.CountTest
open BinaryData

theorem equal_eq (z : Count × Count) : equal z=decide (z.1.length=z.2.length) := by
  unfold equal
  have hh (a b : Count) : (a.drop b.length).isEmpty = decide (a.length≤b.length) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.isEmpty_iff, List.drop_eq_nil_iff, decide_eq_true_eq]
  rw [hh,hh]
  split <;> rename_i h
  · apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq] at *
    omega
  · symm
    exact decide_eq_false (by simp only [decide_eq_true_eq] at h; omega)

end MeanPayoff.TreeDevice.CountTest

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Normalize
open BinaryData

theorem word_val (G : Game) (e : Fin G.m) : (word G e).val=transformed G e := by
  simp only [word,Scale.transform_val,List.length_replicate,EdgeRead.encodedWord_val,transformed]

theorem edge_exact (G : Game) (e : Fin G.m) :
    edge (List.replicate G.n (),EdgesRead.lower ((G.tail e).val,(G.head e).val,G.weight e))=encodedEdge G e := rfl

theorem exact (G : Game) : read (input G) =
    (List.replicate G.n (),(List.ofFn G.maxOwner,List.ofFn (encodedEdge G))) := by
  rw [read,ArenaRead.game_exact]
  simp only [arena,BinaryInput.lower,List.map_ofFn,Function.comp_def,edge_exact]

end MeanPayoff.TreeDevice.Normalize
namespace MeanPayoff.TreeDevice.Adjacency
open BinaryData

theorem test_exact (G : Game) (v : Fin G.n) (e : Fin G.m) :
    test (List.replicate v.val (),Normalize.encodedEdge G e)=decide (G.tail e=v) := by
  rw [test,CountTest.equal_eq]
  simp only [Normalize.encodedEdge,List.length_replicate]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h; exact Fin.ext h.symm
  · intro h; exact congrArg Fin.val h.symm

theorem select_exact (G : Game) (v : Fin G.n) :
    select (List.replicate v.val (),List.ofFn (Normalize.encodedEdge G)) =
      (Graph.outList G v).map (Graph.codeEdge G (Normalize.word G)) := by
  simp only [select,List.ofFn_eq_map,List.filter_map,List.map_map,Function.comp_def,test_exact]
  rfl

theorem vertex_exact (G : Game) (v : Fin G.n) :
    vertex (List.ofFn (Normalize.encodedEdge G)) (List.replicate v.val (),G.maxOwner v) =
      Graph.codeVertex G (Normalize.word G) v := by
  rw [vertex,select_exact]
  have h := Graph.outList_ne_nil G v
  rw [show Graph.outList G v=Graph.firstEdge G v::(Graph.outList G v).tail from (List.cons_head_tail h).symm]
  rfl

end MeanPayoff.TreeDevice.Adjacency
namespace MeanPayoff.TreeDevice.Rows
open BinaryData

theorem count_eq (xs : List Bool) : count xs = List.replicate xs.length () := by simp [count]

theorem fold_exact (edges : Edges) (owners : List Bool) (acc : List Graph.Vertex) :
    Fold.fold (StreamFold.step row) (edges,(acc,owners)) (List.replicate owners.length ()) =
      (edges,((descending edges owners).reverse++acc,[])) := by
  induction owners generalizing acc with
  | nil => simp [Fold.fold,descending]
  | cons b bs ih =>
    simp only [List.length_cons,List.replicate_succ,Fold.fold,List.foldl_cons]
    change Fold.fold (StreamFold.step row) (StreamFold.step row ((edges,(acc,b::bs)),())) (List.replicate bs.length ())= _
    simp only [StreamFold.step,row,List.tail_cons,List.headD_cons,count_eq]
    rw [ih]
    simp [descending,List.reverse_cons,List.append_assoc]

theorem descending_ofFn (edges : Edges) {n : ℕ} (f : Fin n → Bool) :
    (descending edges (List.ofFn f).reverse).reverse=
      List.ofFn (fun i => Adjacency.vertex edges (List.replicate i.val (),f i)) := by
  induction n with
  | zero => simp [descending]
  | succ n ih =>
    rw [List.ofFn_succ_last,List.reverse_append]
    simp only [List.singleton_append,descending,List.length_reverse,List.length_ofFn,List.reverse_cons,List.reverse_nil,List.nil_append]
    rw [ih,List.ofFn_succ_last]
    rfl

theorem build_exact (G : Game) :
    build (List.replicate G.n (),(List.ofFn G.maxOwner,List.ofFn (Normalize.encodedEdge G))) =
      Graph.codeVertices G (Normalize.word G) := by
  have hf := fold_exact (List.ofFn (Normalize.encodedEdge G)) (List.ofFn G.maxOwner).reverse []
  simp only [List.length_reverse,List.length_ofFn] at hf
  change (Fold.fold (StreamFold.step row) (List.ofFn (Normalize.encodedEdge G),([], (List.ofFn G.maxOwner).reverse)) (List.replicate G.n ())).2.1 = _
  rw [hf]
  simp only [List.append_nil,descending_ofFn,Graph.codeVertices]
  apply congrArg List.ofFn
  funext v
  exact Adjacency.vertex_exact G v

end MeanPayoff.TreeDevice.Rows
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_EncodedPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData
open Code

namespace Word
@[simp] theorem min_val (x y : W) : (min (x,y)).val=Min.min x.val y.val := Order.low_val _
@[simp] theorem max_val (x y : W) : (max (x,y)).val=Max.max x.val y.val := Order.high_val _
@[simp] theorem half_val (x : W) : (half x).val=x.val/2 := Halve.halve_val _
@[simp] theorem average_val (x y : W) : (average (x,y)).val=(x.val+y.val)/2 := by simp [average]
@[simp] theorem unsignedMul_val (x y : W) (hy : y.sign=false) : (unsignedMul (x,y)).val=x.val*y.val := by
  change (Multiply.multiply (x,y.digits)).val=x.val*y.val
  rw [Multiply.exact]
  simp [SignedBits.Word.val,hy]
@[simp] theorem mul_val (x y : W) : (mul (x,y)).val=x.val*y.val := by
  change (if y.sign then neg (unsignedMul (x,neg y)) else unsignedMul (x,y)).val=x.val*y.val
  by_cases h : y.sign=true
  · rw [ite_eq_left h]
    have hn : (neg y).sign=false := by
      have hy : y.val<0 := (SignedBits.val_negative y).mpr h
      have hp : ¬(neg y).val<0 := by rw [neg_val]; omega
      have := mt (SignedBits.val_negative (neg y)).mpr hp
      cases hs : (neg y).sign <;> simp_all
    simp only [neg_val,unsignedMul_val _ _ hn]
    ring
  · rw [ite_eq_right h]
    have hy : y.sign=false := Bool.eq_false_iff.mpr h
    exact unsignedMul_val x y hy
end Word
end MeanPayoff.TreeDevice.Certified
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_EncodedArithmetic
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.RawControl.instEncodingPack _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingParsed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace Word

theorem addFold_val (a : W) (xs : List W) :
    (addFold (a,xs)).val=a.val+(xs.map SignedBits.Word.val).sum := by
  change (Fold.fold add.eval a xs).val=_
  induction xs generalizing a with
  | nil => simp [Fold.fold]
  | cons x xs ih =>
    change (Fold.fold add.eval (add (a,x)) xs).val=_
    have h := ih (add (a,x))
    simp only [List.map_cons,List.sum_cons] at *
    rw [add_val] at h
    omega
@[simp] theorem sum_val (xs : List W) : (sum xs).val=(xs.map SignedBits.Word.val).sum := by
  change (addFold (Median.zeroWord,xs)).val=_
  rw [addFold_val]
  change 0+_=_
  omega

theorem shiftRight_val (w : W) (c : Count) : (shiftRight (w,c)).val=w.val/(2^c.length) := by
  change (Fold.fold shiftStep.eval w c).val=_
  induction c generalizing w with
  | nil => simp [Fold.fold]
  | cons u cs ih =>
    change (Fold.fold shiftStep.eval (half w) cs).val=_
    rw [ih,half_val,Int.ediv_ediv]
    simp only [List.length_cons,pow_succ]
    norm_num
    rw [mul_comm]
end Word

namespace Counter
@[simp] theorem word_val (xs : Count) : (word xs).val=xs.length := by
  simp [word,Code.const,List.sum_replicate]
end Counter
end MeanPayoff.TreeDevice.Certified
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace Array

theorem zip_ofFn {α β γ : Type} (f : α × β → γ) (b : β) {n : ℕ}
    (as : Fin n → α) (bs : Fin n → β) :
    Zip.zip f b (List.ofFn as) (List.ofFn bs)=List.ofFn (fun i => f (as i,bs i)) := by
  induction n with
  | zero => simp [List.ofFn_zero,Zip.zip]
  | succ n ih => simp [List.ofFn_succ,Zip.zip,ih]

theorem zip_rep {n : ℕ} (f : Code (W × W) W) (g : ℤ → ℤ → ℤ)
    (hf : ∀ w v, (f (w,v)).val=g w.val v.val)
    {x y : Fin n → ℤ} {xs ys : List W} (hx : VectorRep x xs) (hy : VectorRep y ys) :
    VectorRep (fun i => g (x i) (y i)) (zip zero zero f (xs,ys)) := by
  obtain ⟨ws,rfl,hw⟩ := hx
  obtain ⟨vs,rfl,hv⟩ := hy
  refine ⟨fun i => f (ws i,vs i),?_,?_⟩
  · exact zip_ofFn f.eval zero ws vs
  · intro i
    rw [hf,hw,hv]
end Array

namespace RawBudget

@[simp] theorem times_val (r : ℤ) (w : W) : (times r w).val=w.val*r := by simp [times]

theorem shrink_fst (r : ℤ) (p : W × W) : ((shrink r p).1).val=p.1.val*r := by simp [shrink]
theorem shrink_snd (r : ℤ) (p : W × W) : ((shrink r p).2).val=p.2.val*5 := by simp [shrink]

theorem reduceK_rep {n : ℕ} {P : Budgets n} {p : Data} (h : Rep P p) :
    Rep P.reduceK (reduceK p) := by
  rcases h with ⟨hkn,hkd,hmn,hmd,hk,hm,hcoords⟩
  refine ⟨?_,?_,hmn,hmd,?_,hm,hcoords⟩
  · change 0<((shrink 4 p.1).1).val
    rw [shrink_fst]
    omega
  · change 0<((shrink 4 p.1).2).val
    rw [shrink_snd]
    omega
  · change (4/5:ℚ)*P.k=(((shrink 4 p.1).1).val:ℚ)/(((shrink 4 p.1).2).val:ℚ)
    rw [hk,shrink_fst,shrink_snd]
    push_cast
    ring

theorem reduceM_rep {n : ℕ} {P : Budgets n} {p : Data} (h : Rep P p) :
    Rep P.reduceM (reduceM p) := by
  rcases h with ⟨hkn,hkd,hmn,hmd,hk,hm,hcoords⟩
  refine ⟨hkn,hkd,?_,?_,hk,?_,hcoords⟩
  · change 0<((shrink 4 p.2.1).1).val
    rw [shrink_fst]
    omega
  · change 0<((shrink 4 p.2.1).2).val
    rw [shrink_snd]
    omega
  · change (4/5:ℚ)*P.m=(((shrink 4 p.2.1).1).val:ℚ)/(((shrink 4 p.2.1).2).val:ℚ)
    rw [hm,shrink_fst,shrink_snd]
    push_cast
    ring

theorem reweightK_rep {n : ℕ} {P : Budgets n} {p : Data} {H : Finset (Fin n)} {hs : List Bool}
    (h : Rep P p) (hH : MaskRep H hs) : Rep (P.reweightK H) (reweightK (p,hs)) := by
  rcases h with ⟨hkn,hkd,hmn,hmd,hk,hm,a,b,ha,hb,hap,hbp,hea,heb⟩
  refine ⟨?_,?_,hmn,hmd,?_,hm,?_⟩
  · change 0<((shrink 3 p.1).1).val
    rw [shrink_fst]
    omega
  · change 0<((shrink 3 p.1).2).val
    rw [shrink_snd]
    omega
  · change (3/5:ℚ)*P.k=(((shrink 3 p.1).1).val:ℚ)/(((shrink 3 p.1).2).val:ℚ)
    rw [hk,shrink_fst,shrink_snd]
    push_cast
    ring
  · let a' : Fin n → W := fun i => if i∈H then Word.double (a i) else a i
    refine ⟨a',b,?_,hb,?_,hbp,?_,heb⟩
    · change Zip.zip _ _ p.2.2.1 hs=List.ofFn a'
      rw [ha,hH,Array.zip_ofFn]
      congr 1
      funext i
      simp [a',Code.branch,Code.comp,Code.fst,Code.snd]
    · intro i
      dsimp [a']
      split_ifs
      · rw [Word.double_val]
        have := hap i
        omega
      · exact hap i
    · intro i
      change halve P.alpha H i=1/((a' i).val:ℚ)
      unfold halve a'
      split_ifs <;> simp [hea,Word.double_val] ; ring

theorem reweightM_rep {n : ℕ} {P : Budgets n} {p : Data} {H : Finset (Fin n)} {hs : List Bool}
    (h : Rep P p) (hH : MaskRep H hs) : Rep (P.reweightM H) (reweightM (p,hs)) := by
  rcases h with ⟨hkn,hkd,hmn,hmd,hk,hm,a,b,ha,hb,hap,hbp,hea,heb⟩
  refine ⟨hkn,hkd,?_,?_,hk,?_,?_⟩
  · change 0<((shrink 3 p.2.1).1).val
    rw [shrink_fst]
    omega
  · change 0<((shrink 3 p.2.1).2).val
    rw [shrink_snd]
    omega
  · change (3/5:ℚ)*P.m=(((shrink 3 p.2.1).1).val:ℚ)/(((shrink 3 p.2.1).2).val:ℚ)
    rw [hm,shrink_fst,shrink_snd]
    push_cast
    ring
  · let b' : Fin n → W := fun i => if i∈H then Word.double (b i) else b i
    refine ⟨a,b',ha,?_,hap,?_,hea,?_⟩
    · change Zip.zip _ _ p.2.2.2 hs=List.ofFn b'
      rw [hb,hH,Array.zip_ofFn]
      congr 1
      funext i
      simp [b',Code.branch,Code.comp,Code.fst,Code.snd]
    · intro i
      dsimp [b']
      split_ifs
      · rw [Word.double_val]
        have := hbp i
        omega
      · exact hbp i
    · intro i
      change halve P.beta H i=1/((b' i).val:ℚ)
      unfold halve b'
      split_ifs <;> simp [heb,Word.double_val] ; ring

theorem density_cast {n : ℕ} {P : Budgets n} {a b : Fin n → W}
    (ha : ∀ i, P.alpha i=1/((a i).val:ℚ)) (hb : ∀ i, P.beta i=1/((b i).val:ℚ)) (i : Fin n) :
    P.density i=((a i).val:ℚ)*((b i).val:ℚ) := by
  simp [Budgets.density,ha,hb,one_div,mul_inv_rev,mul_comm]

theorem total_eq {n : ℕ} {P : Budgets n} {p : Data} (h : Rep P p) :
    ((total p).val:ℚ)=P.totalDensity := by
  obtain ⟨a,b,ha,hb,_,_,hea,heb⟩ := h.coords
  change ((Word.sum (Array.mul (p.2.2.1,p.2.2.2))).val:ℚ)=_
  rw [ha,hb]
  change ((Word.sum (Zip.zip _ _ (List.ofFn a) (List.ofFn b))).val:ℚ)=_
  rw [Array.zip_ofFn,Word.sum_val]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def,Word.mul_val]
  push_cast
  unfold Budgets.totalDensity mass
  apply Finset.sum_congr rfl
  intro i _
  exact (density_cast hea heb i).symm

theorem masked_eq {n : ℕ} {P : Budgets n} {p : Data} {H : Finset (Fin n)} {hs : List Bool}
    (h : Rep P p) (hH : MaskRep H hs) :
    ((Word.sum (Array.mask (density p,hs))).val:ℚ)=mass P.density H := by
  obtain ⟨a,b,ha,hb,_,_,hea,heb⟩ := h.coords
  change ((Word.sum (Zip.zip _ _ (Zip.zip _ _ p.2.2.1 p.2.2.2) hs)).val:ℚ)=_
  rw [ha,hb,hH,Array.zip_ofFn,Array.zip_ofFn,Word.sum_val]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def]
  rw [Int.cast_sum]
  unfold mass
  calc
    _ = ∑ i : Fin n, if i∈H then P.density i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      change ((if decide (i∈H) then Word.mul (a i,b i) else Word.constant 0 (Word.mul (a i,b i),decide (i∈H))).val:ℚ)=_
      by_cases hi : i∈H
      · simp only [hi,decide_true,↓reduceIte,Word.mul_val,Int.cast_mul]
        exact (density_cast hea heb i).symm
      · simp [hi]
    _ = _ := by simp []

theorem small_eq {n : ℕ} {P : Budgets n} {p : Data} (h : Rep P p) :
    small p=decide (P.parameter<1) := by
  change Word.lt (parameterNumerator p,parameterDenominator p)=_
  rw [Word.lt_eval]
  apply decide_eq_decide.mpr
  have hk : (((kn p).val:ℤ):ℚ)=(p.1.1.val:ℚ) := rfl
  have ht := total_eq h
  have hd : (0:ℚ)<p.1.2.val*p.2.1.2.val := by
    exact mul_pos (by exact_mod_cast h.kd_pos) (by exact_mod_cast h.md_pos)
  have he : P.parameter=
      ((parameterNumerator p).val:ℚ)/((parameterDenominator p).val:ℚ) := by
    change P.k*P.m*P.totalDensity=_
    simp only [parameterNumerator,parameterDenominator,comp_eval,pair_eval,Word.mul_val,Int.cast_mul]
    rw [← ht,h.k_eq,h.m_eq]
    change _=(p.1.1.val:ℚ)*p.2.1.1.val*(total p).val/((p.1.2.val:ℚ)*p.2.1.2.val)
    ring
  rw [he,div_lt_one (by
    change (0:ℚ)<((Word.mul (p.1.2,p.2.1.2)).val:ℚ)
    rw [Word.mul_val,Int.cast_mul]
    exact hd)]
  exact_mod_cast (Iff.rfl : (parameterNumerator p).val<(parameterDenominator p).val ↔ _)

theorem measureLarge_eq {n : ℕ} {P : Budgets n} {p : Data} {H : Finset (Fin n)} {hs : List Bool}
    (hn : 0<n) (h : Rep P p) (hH : MaskRep H hs) :
    measureLarge (p,hs)=decide ((1/2:ℚ)<P.measure H) := by
  change Word.lt (total p,Word.double (Word.sum (Array.mask (density p,hs))))=_
  rw [Word.lt_eval,Word.double_val]
  apply decide_eq_decide.mpr
  have ht := total_eq h
  have hm := masked_eq h hH
  have hp := P.totalDensity_pos hn
  have he : (1/2:ℚ)<P.measure H ↔ P.totalDensity<2*mass P.density H := by
    unfold Budgets.measure
    rw [lt_div_iff₀ hp]
    constructor <;> intro hh <;> linarith
  rw [he,← ht,← hm]
  exact_mod_cast (Iff.rfl : (total p).val<2*(Word.sum (Array.mask (density p,hs))).val ↔ _)
end RawBudget
end MeanPayoff.TreeDevice.Certified
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_FiniteIteration
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.RawControl.instEncodingPack _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingParsed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Array

theorem scale_rep {n : ℕ} {v : Fin n → ℤ} {xs : List W} (h : VectorRep v xs) (w : W) :
    VectorRep (fun i => w.val*v i) (scale (w,xs)) := by
  obtain ⟨ws,rfl,hw⟩ := h
  refine ⟨fun i => Word.mul (w,ws i),by simp [scale,Function.comp_def],?_⟩
  intro i
  simp [hw]

theorem translate_rep {n : ℕ} {v : Fin n → ℤ} {xs : List W} (h : VectorRep v xs) (w : W) :
    VectorRep (fun i => w.val+v i) (translate (w,xs)) := by
  obtain ⟨ws,rfl,hw⟩ := h
  refine ⟨fun i => Word.add (w,ws i),by simp [translate,Function.comp_def],?_⟩
  intro i
  simp [hw]

theorem choose_rep {n : ℕ} {H : Finset (Fin n)} {hs : List Bool}
    {a b : Fin n → ℤ} {as bs : List W} (hH : MaskRep H hs) (ha : VectorRep a as) (hb : VectorRep b bs) :
    VectorRep (fun i => if i∈H then a i else b i) (choose (hs,as,bs)) := by
  obtain ⟨ws,rfl,hw⟩ := ha
  obtain ⟨vs,rfl,hv⟩ := hb
  rw [hH]
  refine ⟨fun i => if i∈H then ws i else vs i,?_,?_⟩
  · change Zip.zip _ _ (List.ofFn _) (Zip.zip _ _ (List.ofFn ws) (List.ofFn vs))=_
    rw [zip_ofFn,zip_ofFn]
    congr 1
    funext i
    simp [comp,fst,snd]
  · intro i
    dsimp only
    split_ifs <;> simp_all

theorem complement_rep {n : ℕ} {H : Finset (Fin n)} {hs : List Bool} (h : MaskRep H hs) :
    MaskRep Hᶜ (complement hs) := by
  rw [h]
  simp [MaskRep,complement,Code.not,List.map_ofFn,Function.comp_def]

theorem anyLE_eq {n : ℕ} (w : W) {v : Fin n → ℤ} {xs : List W} (h : VectorRep v xs) :
    anyLE (w,xs)=decide (∃ i, w.val≤v i) := by
  obtain ⟨ws,rfl,hw⟩ := h
  simp [anyLE,Code.any,Code.filter,Code.empty,Word.le_eval,hw,← decide_not]

end Array

namespace RawBudget
theorem smallMask_eq {n : ℕ} {P : Budgets n} {p : Data} (h : Rep P p) :
    MaskRep (Finset.univ.filter (fun i => P.m < P.beta i)) (smallMask p) := by
  obtain ⟨a,b,ha,hb,hap,hbp,hea,heb⟩ := h.coords
  change Zip.zip _ _ (List.map _ p.2.2.2) (List.map _ p.2.2.2)=_
  rw [hb,List.map_ofFn,List.map_ofFn,Array.zip_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply,Word.mul_val,Word.lt_eval,Finset.mem_filter,Finset.mem_univ,true_and]
  apply decide_eq_decide.mpr
  have hd : (0:ℚ)<p.2.1.2.val := by exact_mod_cast h.md_pos
  have hp : (0:ℚ)<(b i).val := by exact_mod_cast hbp i
  rw [h.m_eq,heb,div_lt_div_iff₀ hd hp]
  simp only [one_mul]
  change p.2.1.1.val*(b i).val<p.2.1.2.val ↔ _
  exact_mod_cast (Iff.rfl : p.2.1.1.val*(b i).val<p.2.1.2.val ↔ _)
end RawBudget
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace RawBox

theorem floor_rep {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    (v : BoxVector I) {vs : List W} (hv : VectorRep v.val vs) :
    Rep (I.withFloor v) (withFloor (b,vs)) := ⟨h.width,hv,h.upper⟩
theorem ceiling_rep {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    (v : BoxVector I) {vs : List W} (hv : VectorRep v.val vs) :
    Rep (I.withCeiling v) (withCeiling (b,vs)) := ⟨h.width,h.lower,hv⟩

theorem clip_rep {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    {v : Fin n → ℤ} {vs : List W} (hv : VectorRep v vs) :
    VectorRep (MeanPayoff.clip I.a I.b v) (clip (b,vs)) := by
  exact Array.zip_rep Word.min Min.min (fun _ _ => Word.min_val _ _) h.upper
    (Array.zip_rep Word.max Max.max (fun _ _ => Word.max_val _ _) h.lower hv)

theorem midpoint_rep {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b) :
    VectorRep I.midpoint.val (midpoint b) := by
  exact Array.zip_rep Word.average (fun a b => (a+b)/2) (fun _ _ => Word.average_val _ _) h.lower h.upper

theorem average_rep {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    {v w : Fin n → ℤ} {vs ws : List W} (hv : VectorRep v vs) (hw : VectorRep w ws) :
    VectorRep (I.averageClipped v w).val (averageClipped (b,vs,ws)) := by
  exact clip_rep h (Array.zip_rep Word.average (fun a b => (a+b)/2)
    (fun _ _ => Word.average_val _ _) hv hw)

theorem centered_rep {n B : ℕ} (v : Fin n → ℤ) {vs : List W} (hv : VectorRep v vs)
    {A : ℕ} (hA : 0<A) (hB : 2*A≤B) (a : W) (ha : a.val=A) :
    Rep (SolveBox.centered v A hA hB) (centered (a,vs)) := by
  refine ⟨?_,?_,?_⟩
  · simp [centered,Word.double_val,ha,SolveBox.centered]
  · convert Array.translate_rep hv (Word.neg a) using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
    funext i
    simp [SolveBox.centered,Word.neg_val,ha]
    ring
  · convert Array.translate_rep hv a using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
    funext i
    simp [SolveBox.centered,ha,add_comm]

theorem capLow_rep {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    {C : ℕ} (hC : 0<C) (hCI : C≤I.width) (c : W) (hc : c.val=C) :
    Rep (I.capLow C hC hCI) (capLow (b,c)) := by
  refine ⟨hc,h.lower,?_⟩
  convert Array.zip_rep Word.min Min.min (fun _ _ => Word.min_val _ _) h.upper
    (Array.translate_rep h.lower c) using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  funext i
  simp [SolveBox.capLow,hc,add_comm]

theorem capHigh_rep {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    {C : ℕ} (hC : 0<C) (hCI : C≤I.width) (c : W) (hc : c.val=C) :
    Rep (I.capHigh C hC hCI) (capHigh (b,c)) := by
  refine ⟨hc,?_,h.upper⟩
  convert Array.zip_rep Word.max Max.max (fun _ _ => Word.max_val _ _) h.lower
    (Array.translate_rep h.upper (Word.neg c)) using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  funext i
  simp [SolveBox.capHigh,Word.neg_val,hc,sub_eq_neg_add]

theorem smallVector_rep {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    {P : Budgets n} {p : RawBudget.Data} (hp : RawBudget.Rep P p) :
    VectorRep (I.smallVector P).val (smallVector (p,b)) := by
  convert Array.choose_rep (RawBudget.smallMask_eq hp) h.upper h.lower using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  funext i
  simp [SolveBox.smallVector,smallRankAnswer]

theorem dividedWidth_eq {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b) (c : Count) :
    (dividedWidth (b,c)).val=(I.width:ℤ)/(2^c.length) := by
  simp [dividedWidth,Word.shiftRight_val,width,h.width]

theorem dividedWidth_nat {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    (c : Count) (d : ℕ) (hc : 2^c.length=d) :
    (dividedWidth (b,c)).val=(I.width/d:ℕ) := by
  rw [dividedWidth_eq h]
  norm_cast
  rw [hc]

theorem movedFloor_eq {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    {v : Fin n → ℤ} {vs : List W} (hv : VectorRep v vs) (d : W) :
    movedFloor (b,vs,d)=decide (∃ i, d.val≤v i-I.a i) := by
  exact Array.anyLE_eq d (Array.zip_rep Word.sub (·-·) (fun _ _ => Word.sub_val _ _) hv h.lower)
theorem movedCeiling_eq {n B : ℕ} {I : SolveBox n B} {b : Data} (h : Rep I b)
    {v : Fin n → ℤ} {vs : List W} (hv : VectorRep v vs) (d : W) :
    movedCeiling (b,vs,d)=decide (∃ i, d.val≤I.b i-v i) := by
  exact Array.anyLE_eq d (Array.zip_rep Word.sub (·-·) (fun _ _ => Word.sub_val _ _) h.upper hv)
end RawBox
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff

theorem box_iterate_fixed {n : ℕ} (F : Vec (Fin n) → Vec (Fin n)) (hF : Monotone F)
    (a b : Vec (Fin n)) (hab : a≤b) (p : Vec (Fin n)) (_hp : InBox a b p)
    (hi : p≤boxStep F a b p) (t : ℕ) (ht : volume b p≤t) :
    boxStep F a b ((boxStep F a b)^[t] p)=(boxStep F a b)^[t] p := by
  by_cases heq : boxStep F a b p=p
  · have hit : ∀ k, (boxStep F a b)^[k] p=p := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply',ih,heq]
    rw [hit,heq]
  · have hq := boxStep_in_box F hab p
    have hnext := boxStep_mono hF a b hi
    have hv := volume_decreases hi hq.2 (Ne.symm heq)
    cases t with
    | zero => omega
    | succ t =>
      rw [Function.iterate_succ_apply]
      exact box_iterate_fixed F hF a b hab (boxStep F a b p) hq hnext t (by omega)
termination_by volume b p

theorem SolveBox.volume_bound {n B : ℕ} (I : SolveBox n B) : volume I.b I.a≤n*I.width := by
  unfold volume
  calc
    ∑ i : Fin n, (I.b i-I.a i).toNat ≤ ∑ _i : Fin n, I.width := by
      apply Finset.sum_le_sum
      intro i _
      exact Int.toNat_le.mpr (by exact_mod_cast I.width_bound i)
    _ = n*I.width := by simp

theorem SolveBox.iterate_exact (G : Game) {B : ℕ} (I : SolveBox G.n B)
    (t : ℕ) (ht : G.n*I.width≤t) :
    (boxStep (operator G) I.a I.b)^[t] I.a = (I.exactVector G).val := by
  have hf := box_iterate_fixed (operator G) (operator_laws G).mono I.a I.b I.ordered I.a
    ⟨le_rfl,I.ordered⟩ (boxStep_in_box (operator G) I.ordered I.a).1 t (I.volume_bound.trans ht)
  have hs := (fixed_iff_comparisons (operator G) I.ordered).mp hf
  exact le_antisymm (box_comparison G hs.1 (basic_spec G I.a I.b I.ordered).2.1)
    (box_comparison G (basic_spec G I.a I.b I.ordered).1 hs.2)
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_RawSolutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace RawBasic

theorem next_rep (G : Game) {B : ℕ} {I : SolveBox G.n B} {b : RawBox.Data}
    (hb : RawBox.Rep I b) (w : Fin G.m→W) (hw : ∀ e, (w e).val=transformed G e)
    {v : Fin G.n→ℤ} {xs : List W} (hx : VectorRep v xs) :
    VectorRep (boxStep (operator G) I.a I.b v) (next ((Graph.codeVertices G w,b),xs)) := by
  apply RawBox.clip_rep hb
  obtain ⟨ws,rfl,hws⟩ := hx
  refine ⟨fun i => Graph.vertex (Graph.codePot ws,Graph.codeVertex G w i),?_,?_⟩
  · exact List.map_ofFn
  · intro i
    rw [Graph.codeVertex_exact G ws w hw]
    congr 2
    exact funext hws

theorem loop_rep (G : Game) {B : ℕ} {I : SolveBox G.n B} {b : RawBox.Data}
    (hb : RawBox.Rep I b) (w : Fin G.m→W) (hw : ∀ e, (w e).val=transformed G e)
    {v : Fin G.n→ℤ} {xs : List W} (hx : VectorRep v xs) (cs : Count) :
    VectorRep ((boxStep (operator G) I.a I.b)^[cs.length] v)
      (loop (((Graph.codeVertices G w,b),xs),cs)).2 := by
  change VectorRep _ (Fold.fold advance.eval ((Graph.codeVertices G w,b),xs) cs).2
  induction cs generalizing v xs with
  | nil => exact hx
  | cons u cs ih =>
    change VectorRep _ (Fold.fold advance.eval ((Graph.codeVertices G w,b),next ((Graph.codeVertices G w,b),xs)) cs).2
    rw [List.length_cons,Function.iterate_succ_apply]
    exact ih (next_rep G hb w hw hx)

theorem solve_rep (G : Game) {B : ℕ} {I : SolveBox G.n B} {b : RawBox.Data}
    (hb : RawBox.Rep I b) (w : Fin G.m→W) (hw : ∀ e, (w e).val=transformed G e)
    (cs : Count) (hc : G.n*I.width ≤ cs.length) :
    VectorRep (I.exactVector G).val (solve ((Graph.codeVertices G w,b),cs)) := by
  have hh := loop_rep G hb w hw hb.lower cs
  rw [I.iterate_exact G cs.length hc] at hh
  exact hh
end RawBasic
end MeanPayoff.TreeDevice.Certified
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Driver
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.RawControl.instEncodingPack _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingParsed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace Code
variable {α β : Type} [Encoding α] [Encoding β]
theorem select_eval (tag : Code α Count) (cases : List (Code α β)) (fallback : Code α β) (x : α) :
    select tag cases fallback x=(cases.getD (tag x).length fallback) x := by
  induction cases generalizing tag with
  | nil => simp [select,List.getD]
  | cons c cs ih =>
    simp only [select,branch_eval,comp_eval,empty_eval,ih]
    cases h : tag x with
    | nil => simp []
    | cons u us => simp [tail_eval,List.getD]
end Code

end MeanPayoff.TreeDevice.Certified

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_InputCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace NaturalLog

theorem recurrence (n : ℕ) (h : 0<n) : Nat.clog 2 (n+1)=Nat.clog 2 (n/2+1)+1 := by
  rw [Nat.clog_of_one_lt (by decide : 1<2) (by omega : 1<n+1)]
  congr 2
  omega

theorem fold_stopped (w : W) (hw : w.val ≤ 0) (c xs : Count) :
    Fold.fold step.eval (w,c) xs = (w,c) := by
  induction xs with
  | nil => rfl
  | cons u us ih =>
    change Fold.fold step.eval (step ((w,c),u)) us = _
    rw [step_eval]
    dsimp only
    rw [ite_eq_right (by omega)]
    exact ih

theorem fold_length (w : W) (hw : 0 ≤ w.val) (c xs : Count) (hf : w.digits.length ≤ xs.length) :
    (Fold.fold step.eval (w,c) xs).2.length = c.length+Nat.clog 2 (w.val.toNat+1) := by
  induction xs generalizing w c with
  | nil =>
    have hd : w.digits=[] := List.length_eq_zero_iff.mp (by simpa using hf)
    have hs : w.sign=false := Bool.eq_false_iff.mpr (fun h => (not_lt_of_ge hw) ((SignedBits.val_negative w).mpr h))
    have hz : w.val=0 := by simp [SignedBits.Word.val,hd,hs,BinaryStack.Addition.value]
    simp [Fold.fold,hz]
  | cons u us ih =>
    by_cases hp : 0<w.val
    · have hd : w.digits ≠ [] := by
        intro hd
        have hb : w.val ≤ 0 := by
          cases hs : w.sign <;> simp [SignedBits.Word.val,hd,hs,BinaryStack.Addition.value]
        omega
      have hw' : 0 ≤ (Word.half w).val := by rw [Word.half_val]; omega
      have hf' : (Word.half w).digits.length ≤ us.length := by
        rw [Word.half_length]
        have : 0<w.digits.length := by simpa only [List.length_pos_iff] using hd
        simp only [List.length_cons] at hf
        omega
      change (Fold.fold step.eval (step ((w,c),u)) us).2.length = _
      rw [step_eval,ite_eq_left hp,ih (Word.half w) hw' (()::c) hf',List.length_cons]
      have hn : 0<w.val.toNat := by omega
      have he : (Word.half w).val.toNat=w.val.toNat/2 := by rw [Word.half_val]; omega
      rw [he,recurrence _ hn]
      omega
    · have hz : w.val=0 := by omega
      rw [fold_stopped w (by omega)]
      simp [hz]

theorem length_exact (w : W) (hw : 0 ≤ w.val) : (length w).length=Nat.clog 2 (w.val.toNat+1) := by
  change (Fold.fold step.eval (w,[]) (Word.digitCount w)).2.length=_
  simpa only [List.length_nil,Nat.zero_add] using fold_length w hw [] (Word.digitCount w) (by rw [Word.digitCount_length])

theorem ceil_exact (w : W) (hw : 0 < w.val) : (ceil w).length=Nat.clog 2 w.val.toNat := by
  change (length (Word.sub (w,Word.constant 1 w))).length=_
  rw [length_exact _ (by simp; omega)]
  congr 1
  simp only [Word.sub_val,Word.constant_val]
  omega
end NaturalLog
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Word

theorem powerFold_val (w : W) (cs : Count) : (powerFold (w,cs)).val=2^cs.length*w.val := by
  change (Fold.fold powerStep.eval w cs).val=_
  induction cs generalizing w with
  | nil => simp [Fold.fold]
  | cons u us ih =>
    change (Fold.fold powerStep.eval (double w) us).val=_
    rw [ih,Word.double_val,List.length_cons,pow_succ]
    ring
@[simp] theorem power_val (cs : Count) : (power cs).val=2^cs.length := by
  change (powerFold (Word.constant 1 cs,cs)).val=_
  rw [powerFold_val,Word.constant_val,mul_one]
end Word
namespace Counter

 theorem bounded_exact (w : W) (n : ℕ) (hw : w.val=n) (cap : Count) (hc : n ≤ cap.length) :
    bounded (w,cap)=List.replicate n () :=
  Address.exact n w hw _ (by simpa only [List.length_map] using hc)
 theorem power_exact (e cap : Count) (hc : 2^e.length ≤ cap.length) :
    power (e,cap)=List.replicate (2^e.length) () := by
  exact bounded_exact (Word.power e) _ (by simp) cap hc

theorem pow_clog_le (n : ℕ) (hn : 0<n) : 2^Nat.clog 2 n ≤ 2*n := by
  by_cases h : n≤1
  · have he : n=1 := by omega
    subst n
    norm_num
  · have hl : 0<Nat.clog 2 n := Nat.clog_pos (by decide) (by omega)
    have hh := Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<n by omega)
    have he : Nat.clog 2 n=(Nat.clog 2 n).pred+1 := (Nat.succ_pred_eq_of_pos hl).symm
    rw [he,pow_succ]
    omega
end Counter
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace InputCode
@[simp] theorem parse_game (G : Game) : parse ⟨input G⟩=game G := by
  change Parsed.mk (Normalize.read (input G))=_
  rw [Normalize.exact]
  rfl
@[simp] theorem rows_game (G : Game) : rows (game G)=Graph.codeVertices G (Normalize.word G) := Rows.build_exact _

@[simp] theorem absolute_val (w : W) : (absolute w).val=|w.val| := by simp [absolute,abs_eq_max_neg]

 theorem fold_upper (a : W) (xs : List W) (M : ℤ) (ha : a.val ≤ M) (hx : ∀ x∈xs, x.val ≤ M) :
    (maximumFold (a,xs)).val ≤ M := by
  change (Fold.fold Word.max.eval a xs).val ≤ M
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    change (Fold.fold Word.max.eval (Word.max (a,x)) xs).val ≤ M
    exact ih _ (by simp only [Word.max_val]; exact max_le ha (hx _ (by simp))) (by intro y hy; exact hx y (by simp [hy]))
 theorem fold_lower (a : W) (xs : List W) : a.val ≤ (maximumFold (a,xs)).val := by
  change a.val ≤ (Fold.fold Word.max.eval a xs).val
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih =>
    exact le_trans (show a.val ≤ (Word.max (a,x)).val by rw [Word.max_val]; exact le_max_left _ _) (ih (Word.max (a,x)))
 theorem fold_mem (a : W) (xs : List W) (x : W) (hx : x∈xs) : x.val ≤ (maximumFold (a,xs)).val := by
  change x.val ≤ (Fold.fold Word.max.eval a xs).val
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (show x.val ≤ (Word.max (a,x)).val by rw [Word.max_val]; exact le_max_right _ _) (fold_lower (Word.max (a,x)) ys)
    · exact ih (Word.max (a,y)) hx

 theorem bound_val (G : Game) : (bound (game G)).val=weightBound G := by
  let xs := (List.ofFn (Normalize.encodedEdge G)).map (fun e => absolute e.2.2)
  change (maximumFold (Word.constant 1 xs,xs)).val=weightBound G
  apply le_antisymm
  · apply fold_upper
    · rw [Word.constant_val]
      exact le_max_left _ _
    · intro x hx
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp he
      subst e
      simp only [Normalize.encodedEdge,absolute_val,Normalize.word_val]
      exact transformed_le_bound G i
  · have h1 : 1 ≤ (maximumFold (Word.constant 1 xs,xs)).val := by simpa only [Word.constant_val] using fold_lower (Word.constant 1 xs) xs
    apply max_le h1
    have hsup : Finset.univ.sup (fun e : Fin G.m => (transformed G e).natAbs) ≤ (maximumFold (Word.constant 1 xs,xs)).val.toNat := by
      apply Finset.sup_le
      intro i _
      have hmem : absolute (Normalize.word G i) ∈ xs := by
        apply List.mem_map.mpr
        exact ⟨Normalize.encodedEdge G i,List.mem_ofFn.mpr ⟨i,rfl⟩,rfl⟩
      have hh := fold_mem (Word.constant 1 xs) xs _ hmem
      rw [absolute_val,Normalize.word_val] at hh
      exact_mod_cast (show ((transformed G i).natAbs : ℤ) ≤ ((maximumFold (Word.constant 1 xs,xs)).val.toNat : ℤ) by
        rw [Int.natCast_natAbs,Int.toNat_of_nonneg (by omega)]; exact hh)
    have hh := Int.ofNat_le.mpr hsup
    rwa [Int.toNat_of_nonneg (by omega)] at hh
@[simp] theorem width_val (G : Game) : (width (game G)).val=topWidth G := by
  simp only [width,comp_eval,pair_eval,RawBudget.times_val,Word.mul_val,Counter.word_val,n_game,List.length_replicate,bound_val]
  unfold topWidth
  ring
end InputCode
end MeanPayoff.TreeDevice.Certified
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Allocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Allocation

 theorem fold_length (a cs : Count) : (Fold.fold double.eval a cs).length=2^cs.length*a.length := by
  induction cs generalizing a with
  | nil => simp [Fold.fold]
  | cons u us ih =>
    change (Fold.fold double.eval (double (a,u)) us).length=_
    rw [ih]
    simp only [double,comp_eval,pair_eval,fst_eval,Counter.add_length,List.length_cons,pow_succ]
    ring
 theorem exact (cs : Count) : Fold.fold double.eval [()] cs=List.replicate (2^cs.length) () := by
  have h := fold_length [()] cs
  simpa using (List.eq_replicate_of_mem (a:=()) (by intro a ha; exact Subsingleton.elim _ _)).trans (by rw [h]; simp)

end Allocation
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Realizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.Box5
open RegisterBits BinaryData TreeDevice
open BinaryData.Take (config_ext)
 theorem injective : Function.Injective place := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 5 => x.val) h)
 theorem installs (a b c : List Bool) :
    install place (core [] [] []) ![a,b,c]=core a b c := by
  funext i; fin_cases i
  · exact install_at place injective _ _ 0
  · exact install_at place injective _ _ 1
  · exact install_at place injective _ _ 2
  · exact install_off place _ _ _ (by intro j; fin_cases j <;> decide)
  · exact install_off place _ _ _ (by intro j; fin_cases j <;> decide)
 theorem quiet : CoinFree program := by intro q top b; rfl
 theorem runs (bs out : List Bool) (bits : ℕ→Bool) :
    advance program bits ⟨some program.start,core bs [] [],out⟩
      (2*bs.length+2+feedCost bs+1)=⟨none,core [] (encode (listData bs)) [],out⟩ := by
  have h := rename_advance Box.program place injective (core [] [] [])
    (Box.cfg .reverse bs [] [] out) bits (2*bs.length+2+feedCost bs+1)
  rw [Box.boxes] at h
  change advance (rename Box.program place) bits
    ⟨some (Box.enc .reverse),core bs [] [],out⟩ _=_
  simp only [renamed,Box.cfg,Box.stopped,installs,List.append_nil] at h
  convert h using 1; rfl
end MeanPayoff.Box5

end

section
namespace MeanPayoff.Emit
open RegisterBits BinaryData TreeDevice
open BinaryData.Take (advance_add config_ext)
 theorem quiet : CoinFree program := by intro q top b; rfl
 theorem nil_run (xs out : List Bool) (bits : ℕ→Bool) :
    advance program bits (cfg 0 (false::xs) out) 2=⟨none,core xs [] [],out⟩ := by
  apply config_ext <;> (try rfl)
  · funext i; fin_cases i <;> rfl
  · change out++[]=out
    exact List.append_nil out
 theorem one (b : Bool) (xs out : List Bool) (bits : ℕ→Bool) :
    advance program bits (cfg 0 (consCode b++xs) out) (if b then 4 else 2)=cfg 0 xs (out++[b]) := by
  cases b <;> apply config_ext <;> (try rfl)
  all_goals first
  | (funext i; fin_cases i <;> rfl)
  | simp [advance,RegisterBits.step,cfg,program,core,consCode,BinaryStack.applyOp]
 theorem runs (bs xs out : List Bool) (bits : ℕ→Bool) :
    advance program bits (cfg 0 (encode (listData bs)++xs) out) (cost bs)=
      ⟨none,core xs [] [],out++bs⟩ := by
  induction bs generalizing out bits with
  | nil => simpa only [cost,List.map_nil,List.sum_nil,Nat.zero_add,List.append_nil,encode_list_nil,List.singleton_append] using nil_run xs out bits
  | cons b bs ih =>
    have hc : cost (b::bs)=(if b then 4 else 2)+cost bs := by simp only [cost,List.map_cons,List.sum_cons]; omega
    rw [hc,encode_list_cons,List.append_assoc,advance_add,one,ih]
    simp only [List.append_assoc,List.singleton_append]
end MeanPayoff.Emit

end

section
namespace MeanPayoff.RegisterBits.Sequence5
open BinaryData.Take (advance_add)
variable (P Q : Program 5)
 theorem quiet (hP : CoinFree P) (hQ : CoinFree Q) : CoinFree (program P Q) :=
  Flow.compile_coinFree _ (by intro p; fin_cases p; exact hP; exact hQ) (by intros; rfl)
 theorem finish_output (F : Flow.Program 5) (p : Fin F.nodes)
    (s t : Fin 5→List Bool) (out result : List Bool) (bits : ℕ→Bool) (N : ℕ)
    (h : advance (F.block p) bits ⟨some (F.block p).start,s,out⟩ N=⟨none,t,result⟩)
    (hn : ∀ top b, F.next p top b=none) :
    ∃ n≤N+1, advance (Flow.compile F) bits (Flow.state F p s out) n=⟨none,t,result⟩ := by
  obtain ⟨n,hn',hh⟩ := Flow.macro_runs F p s out bits N (by rw [h])
  rw [h] at hh
  refine ⟨n+1,by omega,?_⟩
  simp only [advance,hh,Flow.step_boundary,hn]
 theorem runs (s t u : Fin 5→List Bool) (out result : List Bool) (N M : ℕ)
    (hP : ∀ bits, advance P bits ⟨some P.start,s,out⟩ N=⟨none,t,out⟩)
    (hQ : ∀ bits, advance Q bits ⟨some Q.start,t,out⟩ M=⟨none,u,result⟩)
    (bits : ℕ→Bool) : advance (program P Q) bits ⟨some (program P Q).start,s,out⟩ (N+M+2)=⟨none,u,result⟩ := by
  obtain ⟨a,ha,ea⟩ := Flow.hop (flow P Q) (0 : Fin 2) (1 : Fin 2) s t out bits N (hP bits) (by intros; rfl)
  obtain ⟨b,hb,eb⟩ := finish_output (flow P Q) (1 : Fin 2) t u out result (fun j => bits (a+j)) M (hQ _) (by intros; rfl)
  apply advance_pad _ _ _ bits (n:=a+b) (by omega) ?_ rfl
  change advance _ bits (Flow.state (flow P Q) (0 : Fin 2) s out) (a+b)=_
  rw [advance_add,ea,eb]
  rfl
end MeanPayoff.RegisterBits.Sequence5

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Orientation
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.RawControl.instEncodingPack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace Counter

theorem enum_ofFn (c : Count) : enum c=List.ofFn (fun i : Fin c.length => List.replicate i.val ()) := by
  rw [enum_eq,List.ofFn_eq_map]
  rw [←List.map_coe_finRange_eq_range]
  rw [List.map_map]
  rfl
end Counter

theorem VectorRep.length {n : ℕ} {v : Fin n→ℤ} {xs : List W} (h : VectorRep v xs) : xs.length=n := by
  obtain ⟨ws,rfl,_⟩ := h
  exact List.length_ofFn

theorem VectorRep.nth {n : ℕ} {v : Fin n→ℤ} {xs : List W} (h : VectorRep v xs) (i : Fin n) :
    (Code.nth Array.zero (xs,List.replicate i.val ())).val=v i := by
  obtain ⟨ws,rfl,hws⟩ := h
  change (Graph.lookup (Graph.codePot ws,List.replicate i.val ())).val=_
  rw [Graph.lookup_exact,hws]

namespace RawMedian

theorem column_values {n : ℕ} {vs : List (Fin n→ℤ)} {xss : List (List W)}
    (h : VectorsRep vs xss) (i : Fin n) :
    (xss.map (fun xs => entry (List.replicate i.val (),xs))).map SignedBits.Word.val=
      vs.map (fun v => v i) := by
  induction h with
  | nil => rfl
  | cons h hrest ih =>
    simp only [List.map_cons]
    rw [show (entry (List.replicate i.val (),_)).val=_ from h.nth i,ih]

theorem coordinates_rep {n : ℕ} {vs : List (Fin n→ℤ)} {xss : List (List W)}
    (h : VectorsRep vs xss) (c : Count) (hc : c.length=n) :
    VectorRep (MeanPayoff.median vs) (coordinates (c,xss)) := by
  subst n
  refine ⟨fun i => column (xss,List.replicate i.val ()),?_,?_⟩
  · change List.map _ (Counter.enum c)=_
    rw [Counter.enum_ofFn,List.map_ofFn]
    rfl
  · intro i
    change (Median.median (xss.map (fun xs => entry (List.replicate i.val (),xs)))).val=_
    rw [Median.value_exact,column_values h i]
    rfl

theorem boxed_rep {n B : ℕ} {I : SolveBox n B} {b : RawBox.Data} (hb : RawBox.Rep I b)
    (vs : List (BoxVector I)) {xss : List (List W)}
    (h : VectorsRep (vs.map Subtype.val) xss) :
    VectorRep (I.medianBox vs).val (boxed (b,xss)) := by
  have hl := h.length_eq
  simp only [List.length_map] at hl
  by_cases he : xss=[]
  · have hv : vs=[] := List.length_eq_zero_iff.mp (by rw [hl,he]; rfl)
    subst xss
    subst vs
    simpa [boxed,SolveBox.medianBox,SolveBox.bottom,RawBox.lower] using hb.lower
  · have hp : 0<vs.length := by have := List.length_pos_iff.mpr he; omega
    simp only [boxed,Code.branch_eval,Code.comp_eval,Code.snd_eval,Code.fst_eval,Code.empty_eval]
    rw [show xss.isEmpty=false by cases xss <;> simp_all]
    simp only [Bool.false_eq_true,ite_false, if_false,SolveBox.medianBox,dite_eq_left hp,Code.pair_eval]
    apply coordinates_rep h
    simpa only [Code.comp_eval,Code.fst_eval,Code.count,Code.map_eval,List.length_map,RawBox.lower,
      Code.snd_eval] using hb.lower.length

end RawMedian
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp

namespace Array

theorem scalarTest_rep {n : ℕ} {v : Fin n→ℤ} {xs : List W} (h : VectorRep v xs)
    (w : W) (f : Code (W×W) Bool) (p : ℤ→ℤ→Prop) [DecidableRel p]
    (hf : ∀ a b, f (a,b)=decide (p a.val b.val)) :
    MaskRep (Finset.univ.filter (fun i => p w.val (v i))) (envMap f (w,xs)) := by
  obtain ⟨ws,rfl,hws⟩ := h
  unfold MaskRep
  simp only [Code.envMap_eval,List.map_ofFn]
  congr 1
  funext i
  simp [hf,hws]

end Array

namespace RawOrientation

theorem positives_rep {n B : ℕ} {I : SolveBox n B} {b : RawBox.Data} (hb : RawBox.Rep I b)
    (q : BoxVector I) {qs : List W} (hq : VectorRep q.val qs) (s : W) (hs : s.val=globalS B) :
    MaskRep (PositiveDisplacement I q) (positives (b,s,qs)) := by
  have hd := Array.zip_rep Word.sub (·-·) (fun _ _ => Word.sub_val _ _) hq (RawBox.midpoint_rep hb)
  have hv := Array.scale_rep hd s
  have h := Array.scalarTest_rep hv (Word.double b.1) Word.lt (·<·) Word.lt_eval
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [PositiveDisplacement,Word.double_val,hb.width,hs]

theorem negatives_rep {n B : ℕ} {I : SolveBox n B} {b : RawBox.Data} (hb : RawBox.Rep I b)
    (q : BoxVector I) {qs : List W} (hq : VectorRep q.val qs) (s : W) (hs : s.val=globalS B) :
    MaskRep (NegativeDisplacement I q) (negatives (b,s,qs)) := by
  have hd := Array.zip_rep Word.sub (·-·) (fun _ _ => Word.sub_val _ _) hq (RawBox.midpoint_rep hb)
  have hv := Array.scale_rep hd s
  have h := Array.scalarTest_rep hv (Word.neg (Word.double b.1)) (swap ≫ₚ Word.lt)
    (fun a b => b<a) (by intro a b; exact Word.lt_eval b a)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [NegativeDisplacement,Word.neg_val,Word.double_val,hb.width,hs]
  congr 1

theorem baseMask_rep {n B : ℕ} {I : SolveBox n B} {b : RawBox.Data} (hb : RawBox.Rep I b)
    (q : BoxVector I) {qs : List W} (hq : VectorRep q.val qs) :
    MaskRep (Finset.univ.filter (fun i => (I.width:ℤ)≤2*(q.val i-I.a i))) (baseMask (b,qs)) := by
  have hd := Array.zip_rep Word.sub (·-·) (fun _ _ => Word.sub_val _ _) hq hb.lower
  have hd' : VectorRep (fun i => 2*(q.val i-I.a i)) (map Word.double (Array.sub (qs,b.2.1))) := by
    obtain ⟨ws,he,hw⟩ := hd
    refine ⟨fun i => Word.double (ws i),?_,?_⟩
    · change List.map _ (Array.sub (qs,b.2.1))=_
      change Array.sub (qs,b.2.1)=_ at he
      rw [he,List.map_ofFn]
      rfl
    · intro i
      rw [Word.double_val,hw]
  convert Array.scalarTest_rep hd' b.1 Word.le (·≤·) Word.le_eval using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  rw [hb.width]

theorem base_rep (G : Game) {B : ℕ} {I : SolveBox G.n B} {b : RawBox.Data}
    (hb : RawBox.Rep I b) {P : Budgets G.n} {p : RawBudget.Data} (hp : RawBudget.Rep P p)
    {qs : List W} (hq : VectorRep (I.exactVector G).val qs) :
    Rep (orientBase G P I) (base (p,b,qs)) := by
  let H : Finset (Fin G.n) := Finset.univ.filter (fun i => (I.width:ℤ)≤2*((I.exactVector G).val i-I.a i))
  have hm : MaskRep H (baseMask (b,qs)) := baseMask_rep hb _ hq
  have ht := RawBudget.measureLarge_eq G.positive hp hm
  by_cases hh : (1/2:ℚ)<P.measure H
  · have hsrc : orientBase G P I=⟨true,[⟨Hᶜ,by rw [P.measure_compl G.positive]; linarith⟩]⟩ := by
      simp only [orientBase]
      dsimp only [H] at hh ⊢
      rw [dite_eq_left hh]
    rw [hsrc]
    change Rep _ (if RawBudget.measureLarge (p,baseMask (b,qs)) then _ else _)
    simp only [ht,decide_eq_true hh,ite_true, if_true]
    exact ⟨rfl,List.Forall₂.cons (Array.complement_rep hm) List.Forall₂.nil⟩
  · have hsrc : orientBase G P I=⟨false,[⟨H,le_of_not_gt hh⟩]⟩ := by
      simp only [orientBase]
      dsimp only [H] at hh ⊢
      rw [dite_eq_right hh]
    rw [hsrc]
    change Rep _ (if RawBudget.measureLarge (p,baseMask (b,qs)) then _ else _)
    rw [ht,ite_eq_right (by simpa using hh)]
    exact ⟨rfl,List.Forall₂.cons hm List.Forall₂.nil⟩

theorem extend_rep {n : ℕ} {P : Budgets n} {O : Orientation P} {o : Data} (ho : Rep O o)
    (H N : SmallSet P) {hs ns : List Bool} (hH : MaskRep H.val hs) (hN : MaskRep N.val ns) :
    Rep ⟨O.chooseY,O.exceptions++[H,N]⟩ (extend (o,hs,ns)) := by
  refine ⟨ho.1,?_⟩
  change List.Forall₂ _ _ (Code.append (o.2,[hs,ns]))
  rw [Code.append_eval]
  exact List.rel_append ho.2 (List.Forall₂.cons hH (List.Forall₂.cons hN List.Forall₂.nil))

theorem choices_length {n : ℕ} {P : Budgets n} {os : List (Orientation P)} {rs : List Data}
    (h : ManyRep os rs) : (rs.filter Prod.fst).length=(os.filter Orientation.chooseY).length := by
  induction h with
  | nil => rfl
  | cons h hr ih =>
    simp only [List.filter_cons]
    rw [h.1]
    split <;> simp_all only [List.length_cons]

theorem exceptions_rep {n : ℕ} {P : Budgets n} {os : List (Orientation P)} {rs : List Data}
    (h : ManyRep os rs) :
    List.Forall₂ (fun H hs => MaskRep H.val hs) (os.map Orientation.exceptions).flatten (rs.map Prod.snd).flatten := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h hr ih =>
    simp only [List.map_cons,List.flatten_cons]
    exact List.rel_append h.2 ih

theorem combine_rep {n : ℕ} {P : Budgets n} {os : List (Orientation P)} {rs : List Data}
    (h : ManyRep os rs) : Rep (combineOrientations os) (combine rs) := by
  refine ⟨?_,?_⟩
  swap
  · simpa only [combine,Code.pair_eval,Code.comp_eval,Code.map_eval,Code.flatten_eval,combineOrientations,Code.snd]
      using exceptions_rep h
  change Word.lt (Counter.word (count rs),Word.double (Counter.word (count (filter fst rs))))=_
  simp only [Word.lt_eval,Counter.word_val,Word.double_val,Code.count_eval,List.length_map,
    Code.filter_eval]
  change decide ((rs.length:ℤ)<2*((rs.filter Prod.fst).length:ℤ))=_
  rw [choices_length h,←h.length_eq]
  change decide ((os.length:ℤ)<2*((os.filter Orientation.chooseY).length:ℤ))=decide _
  congr 1
  norm_cast

end RawOrientation
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Control
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Array

theorem foldMin_rep {n B : ℕ} {I : SolveBox n B} (v : BoxVector I) {xs : List W}
    (hv : VectorRep v.val xs) {vs : List (BoxVector I)} {xss : List (List W)}
    (hs : VectorsRep (vs.map Subtype.val) xss) :
    VectorRep (vs.foldl I.minVector v).val (foldMin (xs,xss)) := by
  induction vs generalizing v xs xss with
  | nil => cases hs; exact hv
  | cons w ws ih =>
    cases hs with
    | cons hw hws =>
      exact ih (I.minVector v w) (Array.zip_rep Word.min Min.min (fun _ _ => Word.min_val _ _) hv hw) hws

theorem foldMax_rep {n B : ℕ} {I : SolveBox n B} (v : BoxVector I) {xs : List W}
    (hv : VectorRep v.val xs) {vs : List (BoxVector I)} {xss : List (List W)}
    (hs : VectorsRep (vs.map Subtype.val) xss) :
    VectorRep (vs.foldl I.maxVector v).val (foldMax (xs,xss)) := by
  induction vs generalizing v xs xss with
  | nil => cases hs; exact hv
  | cons w ws ih =>
    cases hs with
    | cons hw hws =>
      exact ih (I.maxVector v w) (Array.zip_rep Word.max Max.max (fun _ _ => Word.max_val _ _) hv hw) hws
end Array
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_ControlCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code

theorem VecsRep.map {n B : ℕ} {I : SolveBox n B} {vs : List (BoxVector I)} {rs : List (List W)}
    (h : VecsRep I vs rs) : VectorsRep (vs.map Subtype.val) rs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h hr ih => exact List.Forall₂.cons h ih

theorem VecsRep.getD {n B : ℕ} {I : SolveBox n B} {vs : List (BoxVector I)} {rs : List (List W)}
    (h : VecsRep I vs rs) (i : ℕ) (d : BoxVector I) {ds : List W} (hd : VectorRep d.val ds) :
    VectorRep (vs.getD i d).val (rs.getD i ds) := by
  induction h generalizing i with
  | nil => simpa using hd
  | cons h hr ih => cases i with
    | zero => exact h
    | succ i => exact ih i

end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp

variable {G : Game} {B : ℕ} {x : Input}

theorem smallWidth_eq (he : EnvRep G B x.1) {I : SolveBox G.n B} (b : Code Input RawBox.Data)
    (hb : RawBox.Rep I (b x)) : smallWidth b x=decide (I.width≤128*globalS B) := by
  change Word.le ((b x).1,RawBudget.times 128 (Counter.word x.1.2.2.1))=_
  rw [Word.le_eval,RawBudget.times_val,Counter.word_val,hb.width,he.samples]
  rw [mul_comm (globalS B : ℤ) 128]
  change decide ((I.width:ℤ)≤((128*globalS B:ℕ):ℤ))=_
  exact decide_eq_decide.mpr Int.ofNat_le

theorem basic_rep (he : EnvRep G B x.1) {I : SolveBox G.n B} (b : Code Input RawBox.Data)
    (hb : RawBox.Rep I (b x)) (hsmall : I.width≤128*globalS B) :
    VectorRep (I.exactVector G).val (basic b x) := by
  obtain ⟨ws,hw,heval⟩ := he.graph
  change VectorRep _ (RawBasic.solve ((x.1.1,b x),x.1.2.2.2.2))
  rw [hw]
  exact RawBasic.solve_rep G hb ws heval _ ((Nat.mul_le_mul_left G.n hsmall).trans he.basic)

theorem narrow_rep (he : EnvRep G B x.1) {I : SolveBox G.n B} (b : Code Input RawBox.Data)
    (hb : RawBox.Rep I (b x)) {v : Fin G.n→ℤ} (q : Code Input (List W)) (hq : VectorRep v (q x))
    (hB : 128*globalS B<I.width) : RawBox.Rep (I.narrowCentered hB v) (narrow b q x) := by
  apply RawBox.centered_rep v hq
  apply RawBox.dividedWidth_nat hb _ (32*globalS B)
  change 2^(Counter.add (x.1.2.1,List.replicate 5 ())).length=32*globalS B
  simp [Counter.add,Code.append_eval,List.length_append,he.exponent,pow_add,globalS,Nat.mul_comm]

theorem wide_rep {I : SolveBox G.n B} (b : Code Input RawBox.Data)
    (hb : RawBox.Rep I (b x)) {v : Fin G.n→ℤ} (q : Code Input (List W)) (hq : VectorRep v (q x))
    (hB : 128*globalS B<I.width) : RawBox.Rep (I.wideCentered hB v) (wide b q x) := by
  apply RawBox.centered_rep v hq
  exact RawBox.dividedWidth_nat hb _ 8 (by norm_num)

theorem delta_eq (he : EnvRep G B x.1) {I : SolveBox G.n B} (b : Code Input RawBox.Data)
    (hb : RawBox.Rep I (b x)) : (delta b x).val=I.delta := by
  apply RawBox.dividedWidth_nat hb _ (4*globalS B)
  change 2^(Counter.add (x.1.2.1,List.replicate 2 ())).length=4*globalS B
  simp [Counter.add,Code.append_eval,List.length_append,he.exponent,pow_add,globalS,Nat.mul_comm]

theorem capWidth_eq (he : EnvRep G B x.1) {I : SolveBox G.n B} (b : Code Input RawBox.Data)
    (hb : RawBox.Rep I (b x)) : (capWidth b x).val=I.C := by
  change (Word.sub ((b x).1,delta b x)).val=_
  rw [Word.sub_val,hb.width,delta_eq he b hb]
  exact (Int.ofNat_sub (Nat.div_le_self I.width (4*globalS B))).symm

theorem centerAt_rep {I : SolveBox G.n B} {rs : List (BoxVector I)}
    (hb : RawBox.Rep I (caller x).b) (hv : VecsRep I rs (current x).vs) (i : Code Input Count) :
    VectorRep (rs.getD (i x).length I.midpoint).val (centerAt i x) := by
  change VectorRep _ (Code.getD [] (((current x).vs,i x),RawBox.midpoint (caller x).b))
  rw [Code.getD_eval]
  exact hv.getD _ _ (RawBox.midpoint_rep hb)

theorem lastPositive_rep (he : EnvRep G B x.1) {I : SolveBox G.n B} {rs : List (BoxVector I)}
    (hb : RawBox.Rep I (caller x).b) (hv : VecsRep I rs (current x).vs) :
    MaskRep (PositiveDisplacement I (rs.getD (globalS B) I.midpoint)) (lastPositive x) := by
  have hv' := centerAt_rep hb hv (env ≫ₚ samples)
  change VectorRep (rs.getD x.1.2.2.1.length I.midpoint).val _ at hv'
  rw [he.samples] at hv'
  apply RawOrientation.positives_rep hb _ hv' _
  change (Counter.word x.1.2.2.1).val=_
  rw [Counter.word_val,he.samples]

theorem lastNegative_rep (he : EnvRep G B x.1) {I : SolveBox G.n B} {rs : List (BoxVector I)}
    (hb : RawBox.Rep I (caller x).b) (hv : VecsRep I rs (current x).vs) :
    MaskRep (NegativeDisplacement I (rs.getD (globalS B) I.midpoint)) (lastNegative x) := by
  have hv' := centerAt_rep hb hv (env ≫ₚ samples)
  change VectorRep (rs.getD x.1.2.2.1.length I.midpoint).val _ at hv'
  rw [he.samples] at hv'
  apply RawOrientation.negatives_rep hb _ hv' _
  change (Counter.word x.1.2.2.1).val=_
  rw [Counter.word_val,he.samples]

end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp

theorem dispatch_call {G : Game} {B : ℕ} {A : SourceControl.Result G B} (j : SourceControl.Job G B A)
    (e : Env) (r : Count) (c : Cell) (ks : List Cell) (ht : c.1.length=j.tag.val) :
    dispatch (e,r,(c,ks))=jobCode j (e,r,(c,ks)) := by
  cases j <;> simp [dispatch,Code.select_eval,state,ht,SourceControl.Job.tag,jobCode,List.getD]

theorem sampled_call_rep {G : Game} {B : ℕ} {A R : SourceControl.Result G B}
    (j : SourceControl.Job G B A) (k : SourceControl.Kont G B A R)
    (e : Env) (he : EnvRep G B e) (r : Count) (c : Cell) (ks : List Cell)
    (ht : c.1.length=j.tag.val) (hj : JobPackRep j c.2) (hk : KontRep k ks) :
    StateRep (SourceControl.sampledStep r.length (.call j k)) (dispatch (e,r,(c,ks))) := by
  rw [dispatch_call j e r c ks ht]
  cases j with
  | solve P I =>
    obtain ⟨hp,hb⟩ := hj
    have hs := RawBudget.small_eq hp
    have hw := smallWidth_eq (x:=(e,r,(c,ks))) he (current ≫ₚ b) hb
    simp only [SourceControl.sampledStep,jobCode,solveCase,Code.branch_eval,Code.comp_eval,p_eval]
    change StateRep (if hR : P.parameter<1 then _ else _) (if RawBudget.small c.2.p then _ else _)
    by_cases hR : P.parameter<1
    · rw [dite_eq_left hR,hs,ite_eq_left (by simp [hR])]
      exact StateRep.ret (by rfl) (RawBox.smallVector_rep hb hp) hk
    · rw [dite_eq_right hR,hs,ite_eq_right (by simp [hR])]
      by_cases hB : I.width≤128*globalS B
      · rw [dite_eq_left hB,hw,ite_eq_left (by simp [hB])]
        exact StateRep.ret (by rfl) (basic_rep he (current ≫ₚ b) hb hB) hk
      · rw [dite_eq_right hB,hw,ite_eq_right (by simp [hB])]
        exact StateRep.call (by rfl) ⟨hp,hb⟩ (KontRep.push (by rfl) ⟨hp,hb⟩ hk)
  | ask P I =>
    obtain ⟨hp,hb⟩ := hj
    exact StateRep.call (by rfl) ⟨hp,hb,he.trials⟩ (KontRep.push (by rfl) hb hk)
  | trials P I J =>
    obtain ⟨hp,hb,htime⟩ := hj
    cases J with
    | zero =>
      have hz : c.2.t=[] := List.length_eq_zero_iff.mp htime
      simp only [SourceControl.sampledStep,jobCode,trialsCase,Code.branch_eval,Code.comp_eval,t_eval,Code.empty_eval]
      change StateRep _ (if c.2.t.isEmpty then _ else _)
      simp only [hz,List.isEmpty_nil,ite_true, if_true]
      exact StateRep.ret (by rfl) List.Forall₂.nil hk
    | succ J =>
      have hz : c.2.t.isEmpty=false := by cases h : c.2.t <;> simp_all
      simp only [SourceControl.sampledStep,jobCode,trialsCase,Code.branch_eval,Code.comp_eval,t_eval,Code.empty_eval]
      change StateRep _ (if c.2.t.isEmpty then _ else _)
      rw [hz,ite_eq_right Bool.noConfusion]
      exact StateRep.call (by rfl) ⟨hp,hb⟩ (KontRep.push (by rfl) ⟨hp,hb,by change c.2.t.tail.length = _; simp [List.length_tail,htime]⟩ hk)
  | update P hR I hB v =>
    obtain ⟨hp,hb,hv⟩ := hj
    exact StateRep.call (by rfl) ⟨RawBudget.reduceK_rep hp,narrow_rep he (current ≫ₚ b) hb (current ≫ₚ q) hv hB⟩
      (KontRep.push (by rfl) ⟨hp,hb,hv⟩ hk)
  | centers P hR I hB t v =>
    obtain ⟨hp,hb,htime,hv⟩ := hj
    cases t with
    | zero =>
      have hz : c.2.t=[] := List.length_eq_zero_iff.mp htime
      simp only [SourceControl.sampledStep,jobCode,centersCase,Code.branch_eval,Code.comp_eval,t_eval,Code.empty_eval]
      change StateRep _ (if c.2.t.isEmpty then _ else _)
      simp only [hz,List.isEmpty_nil,ite_true, if_true]
      exact StateRep.ret (by rfl) (List.Forall₂.cons hv List.Forall₂.nil) hk
    | succ t =>
      have hz : c.2.t.isEmpty=false := by cases h : c.2.t <;> simp_all
      simp only [SourceControl.sampledStep,jobCode,centersCase,Code.branch_eval,Code.comp_eval,t_eval,Code.empty_eval]
      change StateRep _ (if c.2.t.isEmpty then _ else _)
      rw [hz,ite_eq_right Bool.noConfusion]
      exact StateRep.call (by rfl) ⟨hp,hb,hv⟩ (KontRep.push (by rfl) ⟨hp,hb,by change c.2.t.tail.length = _; simp [List.length_tail,htime],hv⟩ hk)
  | orient P hR I =>
    obtain ⟨hp,hb⟩ := hj
    have hw := smallWidth_eq (x:=(e,r,(c,ks))) he (current ≫ₚ b) hb
    simp only [SourceControl.sampledStep,jobCode,orientCase,Code.branch_eval]
    rw [hw]
    by_cases hB : I.width≤128*globalS B
    · rw [dite_eq_left hB,ite_eq_left (by simp [hB])]
      exact StateRep.ret (by rfl) (RawOrientation.base_rep G hb hp (basic_rep he (current ≫ₚ b) hb hB)) hk
    · rw [dite_eq_right hB,ite_eq_right (by simp [hB])]
      exact StateRep.call (by rfl) ⟨hp,hb,he.samples,RawBox.midpoint_rep hb⟩ (KontRep.push (by rfl) ⟨hp,hb⟩ hk)
  | orientTrials P hR I J =>
    obtain ⟨hp,hb,htime⟩ := hj
    cases J with
    | zero =>
      have hz : c.2.t=[] := List.length_eq_zero_iff.mp htime
      simp only [SourceControl.sampledStep,jobCode,orientTrialsCase,Code.branch_eval,Code.comp_eval,t_eval,Code.empty_eval]
      change StateRep _ (if c.2.t.isEmpty then _ else _)
      simp only [hz,List.isEmpty_nil,ite_true, if_true]
      exact StateRep.ret (by rfl) List.Forall₂.nil hk
    | succ J =>
      have hz : c.2.t.isEmpty=false := by cases h : c.2.t <;> simp_all
      simp only [SourceControl.sampledStep,jobCode,orientTrialsCase,Code.branch_eval,Code.comp_eval,t_eval,Code.empty_eval]
      change StateRep _ (if c.2.t.isEmpty then _ else _)
      rw [hz,ite_eq_right Bool.noConfusion]
      exact StateRep.call (by rfl) ⟨hp,hb⟩ (KontRep.push (by rfl) ⟨hp,hb,by change c.2.t.tail.length = _; simp [List.length_tail,htime]⟩ hk)
  | orientPlus P hR I =>
    obtain ⟨hp,hb⟩ := hj
    exact StateRep.call (by rfl) ⟨hp,hb,he.trials⟩ (KontRep.push (by rfl) trivial hk)
  | tighten P hR I hB =>
    obtain ⟨hp,hb⟩ := hj
    exact StateRep.call (by rfl) ⟨RawBudget.reduceK_rep hp,hb⟩ (KontRep.push (by rfl) ⟨hp,hb⟩ hk)
  | reweight P hR I side Hs =>
    obtain ⟨hp,hb,hside,hs⟩ := hj
    cases Hs with
    | nil =>
      have ho := List.forall₂_nil_left_iff.mp hs
      simp only [SourceControl.sampledStep,jobCode,reweightCase,Code.branch_eval,Code.comp_eval,o_eval,Code.snd_eval,Code.empty_eval]
      change StateRep _ (if c.2.o.2.isEmpty then _ else _)
      simp only [ho,List.isEmpty_nil,ite_true, if_true]
      exact StateRep.ret (by rfl) List.Forall₂.nil hk
    | cons H Hs =>
      obtain ⟨rh,rt,hmask,htail,ho⟩ := List.forall₂_cons_left_iff.mp hs
      simp only [SourceControl.sampledStep,jobCode,reweightCase,Code.branch_eval,Code.comp_eval,o_eval,Code.snd_eval,Code.empty_eval]
      change StateRep _ (if c.2.o.2.isEmpty then _ else _)
      simp only [ho,List.isEmpty_cons]
      refine StateRep.call (by rfl) ⟨?_,hb⟩ (KontRep.push (by rfl) ⟨hp,hb,hside,?_⟩ hk)
      · change RawBudget.Rep (if side then P.reweightM H.val else P.reweightK H.val)
          (if c.2.o.1 then RawBudget.reweightM (c.2.p,c.2.o.2.headD []) else RawBudget.reweightK (c.2.p,c.2.o.2.headD []))
        rw [hside,ho]
        cases side
        · exact RawBudget.reweightK_rep hp hmask
        · exact RawBudget.reweightM_rep hp hmask
      · change List.Forall₂ _ Hs c.2.o.2.tail
        rw [ho]
        exact htail

end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp

theorem dispatch_return {G : Game} {B : ℕ} {A C : SourceControl.Result G B} (f : SourceControl.Frame G B A C)
    (e : Env) (r : Count) (c d : Cell) (ks : List Cell) (ht : c.1.length=10) (hf : d.1.length=f.tag.val) :
    dispatch (e,r,(c,d::ks))=frameCode f (e,r,(c,d::ks)) := by
  cases f <;> simp [dispatch,Code.select_eval,state,ht,resume,stack,hf,SourceControl.Frame.tag,frameCode,List.getD,Code.empty_eval]

theorem sampled_resume_rep {G : Game} {B : ℕ} {A C R : SourceControl.Result G B}
    (f : SourceControl.Frame G B A C) (v : A.Value) (k : SourceControl.Kont G B C R)
    (e : Env) (he : EnvRep G B e) (r : Count) (c d : Cell) (ks : List Cell)
    (hf : FramePackRep f d.2) (hv : ValueRep A v c.2) (hk : KontRep k ks) :
    StateRep (SourceControl.sampledResume f v k r.length) (frameCode f (e,r,(c,d::ks))) := by
  cases f with
  | trialsHead P I J =>
    obtain ⟨hp,hb,hj⟩ := hf
    exact StateRep.call (by rfl) ⟨hp,hb,hj⟩ (KontRep.push (by rfl) hv hk)
  | vectorCons a => exact StateRep.ret (by rfl) (List.Forall₂.cons hf hv) hk
  | median I => exact StateRep.ret (by rfl) (RawMedian.boxed_rep hf v hv.map) hk
  | centerFirst P hR I hB q =>
    obtain ⟨hp,hb,hq⟩ := hf
    exact StateRep.call (by rfl) ⟨RawBudget.reduceM_rep hp,narrow_rep he (caller ≫ₚ b) hb (caller ≫ₚ RawControl.q) hq hB⟩
      (KontRep.push (by rfl) ⟨hb,hv⟩ hk)
  | centerSecond I hB q r' =>
    obtain ⟨hb,hr⟩ := hf
    exact StateRep.ret (by rfl) (RawBox.average_rep hb hr hv) hk
  | centersHead P hR I hB t q =>
    obtain ⟨hp,hb,ht,hq⟩ := hf
    exact StateRep.call (by rfl) ⟨hp,hb,ht,hv⟩ (KontRep.push (by rfl) hq hk)
  | orientLoop P hR I hB =>
    obtain ⟨hp,hb⟩ := hf
    have hpos := lastPositive_rep (x:=(e,r,(c,d::ks))) he hb hv
    have hneg := lastNegative_rep (x:=(e,r,(c,d::ks))) he hb hv
    have hpTest := RawBudget.measureLarge_eq G.positive hp hpos
    have hnTest := RawBudget.measureLarge_eq G.positive hp hneg
    simp only [SourceControl.sampledResume,frameCode,orientLoopCase,Code.branch_eval,Code.comp_eval,Code.pair_eval,p_eval]
    change StateRep (if hh : (1/2:ℚ)<P.measure _ then _ else _)
      (if RawBudget.measureLarge (d.2.p,lastPositive (e,r,(c,d::ks))) then _ else _)
    by_cases hH : (1/2:ℚ)<P.measure (PositiveDisplacement I (v.getD (globalS B) I.midpoint))
    · rw [dite_eq_left hH,hpTest,decide_eq_true hH,ite_eq_left rfl]
      exact StateRep.ret (by rfl) ⟨rfl,List.Forall₂.cons (Array.complement_rep hpos) List.Forall₂.nil⟩ hk
    · rw [dite_eq_right hH,hpTest,decide_eq_false hH,ite_eq_right (by decide)]
      change StateRep _ (if RawBudget.measureLarge (d.2.p,lastNegative (e,r,(c,d::ks))) then _ else _)
      by_cases hN : (1/2:ℚ)<P.measure (NegativeDisplacement I (v.getD (globalS B) I.midpoint))
      · rw [dite_eq_left hN,hnTest,decide_eq_true hN,ite_eq_left rfl]
        exact StateRep.ret (by rfl) ⟨rfl,List.Forall₂.cons (Array.complement_rep hneg) List.Forall₂.nil⟩ hk
      · rw [dite_eq_right hN,hnTest,decide_eq_false hN,ite_eq_right (by decide)]
        exact StateRep.call (by rfl)
          ⟨hp,wide_rep (caller ≫ₚ b) hb (centerAt random) (centerAt_rep (x:=(e,r,(c,d::ks))) hb hv random) hB⟩
          (KontRep.push (by rfl) ⟨rfl,hpos,hneg⟩ hk)
  | orientTail H N =>
    obtain ⟨_,hH,hN⟩ := hf
    exact StateRep.ret (by rfl) (RawOrientation.extend_rep hv H N hH hN) hk
  | orientHead P hR I J =>
    obtain ⟨hp,hb,hj⟩ := hf
    exact StateRep.call (by rfl) ⟨hp,hb,hj⟩ (KontRep.push (by rfl) hv hk)
  | orientCons O => exact StateRep.ret (by rfl) (List.Forall₂.cons hf hv) hk
  | combine P => exact StateRep.ret (by rfl) (RawOrientation.combine_rep hv) hk
  | tightenFirst P hR I hB =>
    obtain ⟨hp,hb⟩ := hf
    have hd := delta_eq (x:=(e,r,(c,d::ks))) he (caller ≫ₚ b) hb
    have hm := RawBox.movedFloor_eq hb hv (delta (caller ≫ₚ b) (e,r,(c,d::ks)))
    rw [hd] at hm
    simp only [SourceControl.sampledResume,frameCode,tightenFirstCase,Code.branch_eval]
    change StateRep (if h : ∃ i, (I.delta:ℤ)≤v.val i-I.a i then _ else _)
      (if RawBox.movedFloor (d.2.b,c.2.q,delta (caller ≫ₚ b) (e,r,(c,d::ks))) then _ else _)
    rw [hm]
    by_cases h : ∃ i, (I.delta:ℤ)≤v.val i-I.a i
    · simp only [dite_eq_left h,decide_eq_true h,ite_true, if_true]
      exact StateRep.call (by rfl) ⟨hp,RawBox.floor_rep hb v hv⟩ (KontRep.push (by rfl) trivial hk)
    · simp only [dite_eq_right h,decide_eq_false h]
      exact StateRep.call (by rfl) ⟨RawBudget.reduceM_rep hp,hb⟩ (KontRep.push (by rfl) ⟨hp,hb⟩ hk)
  | tightenSecond P hR I hB =>
    obtain ⟨hp,hb⟩ := hf
    have hd := delta_eq (x:=(e,r,(c,d::ks))) he (caller ≫ₚ b) hb
    have hm := RawBox.movedCeiling_eq hb hv (delta (caller ≫ₚ b) (e,r,(c,d::ks)))
    rw [hd] at hm
    simp only [SourceControl.sampledResume,frameCode,tightenSecondCase,Code.branch_eval]
    change StateRep (if h : ∃ i, (I.delta:ℤ)≤I.b i-v.val i then _ else _)
      (if RawBox.movedCeiling (d.2.b,c.2.q,delta (caller ≫ₚ b) (e,r,(c,d::ks))) then _ else _)
    rw [hm]
    by_cases h : ∃ i, (I.delta:ℤ)≤I.b i-v.val i
    · simp only [dite_eq_left h,decide_eq_true h,ite_true, if_true]
      exact StateRep.call (by rfl) ⟨hp,RawBox.ceiling_rep hb v hv⟩ (KontRep.push (by rfl) trivial hk)
    · simp only [dite_eq_right h,decide_eq_false h]
      exact StateRep.ret (by rfl) hb hk
  | floor I q => exact StateRep.ret (by rfl) hv hk
  | ceiling I q => exact StateRep.ret (by rfl) hv hk
  | solveTight P hR I hB =>
    obtain ⟨hp,_⟩ := hf
    exact StateRep.call (by rfl) ⟨hp,hv⟩ (KontRep.push (by rfl) ⟨hp,hv⟩ (KontRep.push (by rfl) trivial hk))
  | solveOriented P hR I hB =>
    obtain ⟨hp,hb⟩ := hf
    exact StateRep.call (by rfl) ⟨hp,hb,hv.1,hv.2⟩ (KontRep.push (by rfl) ⟨hp,hb,hv.1⟩ hk)
  | reweightHead P hR I side Hs =>
    exact StateRep.call (by rfl) hf (KontRep.push (by rfl) hv hk)
  | solveReweighted P hR I hB side =>
    obtain ⟨hp,hb,hs⟩ := hf
    have hc := capWidth_eq (x:=(e,r,(c,d::ks))) he (caller ≫ₚ b) hb
    simp only [SourceControl.sampledResume,frameCode,solveReweightedCase,Code.branch_eval]
    change StateRep (if side then _ else _) (if d.2.o.1 then _ else _)
    rw [hs]
    cases side with
    | false =>
      exact StateRep.call (by rfl) ⟨hp,RawBox.capLow_rep hb _ _ _ hc⟩ (KontRep.push (by rfl) hv hk)
    | true =>
      exact StateRep.call (by rfl) ⟨hp,RawBox.capHigh_rep hb _ _ _ hc⟩ (KontRep.push (by rfl) hv hk)
  | capHigh I hB rs =>
    exact StateRep.ret (by rfl) (Array.foldMin_rep (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le v) hv hf.map) hk
  | capLow I hB rs =>
    exact StateRep.ret (by rfl) (Array.foldMax_rep (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le v) hv hf.map) hk
  | includeInner T => exact StateRep.ret (by rfl) hv hk

end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code

theorem sampled_dispatch_rep {G : Game} {B : ℕ} {R : SourceControl.Result G B}
    {s : SourceControl.State G B R} {z : State} (h : StateRep s z)
    (e : Env) (he : EnvRep G B e) (r : Count) :
    StateRep (SourceControl.sampledStep r.length s) (dispatch (e,r,z)) := by
  cases h with
  | call ht hj hk => exact sampled_call_rep _ _ e he r _ _ ht hj hk
  | ret ht hv hk =>
    cases hk with
    | done =>
      simpa [dispatch,Code.select_eval,state,ht,resume,stack,Code.empty_eval,SourceControl.sampledStep,List.getD]
        using StateRep.ret ht hv KontRep.done
    | push hf hfr hk =>
      rw [dispatch_return _ e r _ _ _ ht hf]
      exact sampled_resume_rep _ _ _ e he r _ _ _ hfr hv hk

end MeanPayoff.TreeDevice.Certified.RawControl

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Loop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.SourceControl

theorem sampledResume_all {G : Game} {B : ℕ} {A C R : Result G B} (f : Frame G B A C)
    (v : A.Value) (k : Kont G B C R) (Q : State G B R→Prop) :
    (resume f v k).tree.All (fun p => Q p.1) ↔
      (RandomTree.uniformBelow (sampleExponent B)).All (fun j => Q (sampledResume f v k j)) := by
  cases f
  all_goals simp only [resume,sampledResume]
  all_goals try split_ifs
  all_goals simp [Counted.pure,Counted.map,Counted.lift,RandomTree.all_map,RandomTree.All]

theorem sampledResume_expect {G : Game} {B : ℕ} {A C R : Result G B} (f : Frame G B A C)
    (v : A.Value) (k : Kont G B C R) (Q : State G B R→ℚ) :
    (resume f v k).tree.expect (fun p => Q p.1) =
      (RandomTree.uniformBelow (sampleExponent B)).expect (fun j => Q (sampledResume f v k j)) := by
  cases f
  all_goals simp only [resume,sampledResume]
  all_goals try split_ifs
  all_goals simp [Counted.pure,Counted.map,Counted.lift,RandomTree.expect_map,Function.comp_def]

theorem sampledStep_all {G : Game} {B : ℕ} {R : Result G B} (s : State G B R) (Q : State G B R→Prop) :
    (step s).tree.All (fun p => Q p.1) ↔
      (RandomTree.uniformBelow (sampleExponent B)).All (fun j => Q (sampledStep j s)) := by
  cases s with
  | ret k v =>
    cases k with
    | done => simp [step,sampledStep,Counted.pure,RandomTree.All]
    | push f k => exact sampledResume_all f v k Q
  | call j k =>
    cases j
    all_goals simp only [step,sampledStep]
    all_goals try split_ifs
    all_goals try simp [Counted.charge,Counted.pure,RandomTree.all_map,RandomTree.All]
    all_goals split <;> simp_all [RandomTree.All]

theorem sampledStep_expect {G : Game} {B : ℕ} {R : Result G B} (s : State G B R) (Q : State G B R→ℚ) :
    (step s).tree.expect (fun p => Q p.1) =
      (RandomTree.uniformBelow (sampleExponent B)).expect (fun j => Q (sampledStep j s)) := by
  cases s with
  | ret k v =>
    cases k with
    | done => simp [step,sampledStep,Counted.pure]
    | push f k => exact sampledResume_expect f v k Q
  | call j k =>
    cases j
    all_goals simp only [step,sampledStep]
    all_goals try split_ifs
    all_goals try simp [Counted.charge,Counted.pure,RandomTree.expect_map]
    all_goals split <;> simp_all

end MeanPayoff.SourceControl

end

section
namespace MeanPayoff.SourceControl

theorem sampledRun_all {G : Game} {B : ℕ} {R : Result G B} (n : ℕ) (s : State G B R) (Q : State G B R→Prop) :
    (sampledRun n s).All Q ↔ (run n s).tree.All (fun p => Q p.1) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [sampledRun,RandomTree.all_bind,run,Counted.bind,RandomTree.all_bind,RandomTree.all_map]
    simp_rw [ih]
    exact (sampledStep_all s (fun t => (run n t).tree.All (fun p => Q p.1))).symm

theorem sampledRun_expect {G : Game} {B : ℕ} {R : Result G B} (n : ℕ) (s : State G B R) (Q : State G B R→ℚ) :
    (sampledRun n s).expect Q = (run n s).tree.expect (fun p => Q p.1) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [sampledRun,RandomTree.expect_bind,run,Counted.bind,RandomTree.expect_bind,RandomTree.expect_map]
    simp_rw [ih]
    exact (sampledStep_expect s (fun t => (run n t).tree.expect (fun p => Q p.1))).symm
end MeanPayoff.SourceControl
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code

theorem loop_rep {G : Game} {B : ℕ} {R : SourceControl.Result G B}
    (s : SourceControl.State G B R) (z : State) (h : StateRep s z)
    (e : Env) (he : EnvRep G B e) (cs : List Count) :
    StateRep (cs.foldl (fun s c => SourceControl.sampledStep c.length s) s) (loop ((e,z),cs)).2 := by
  change StateRep _ (Fold.fold advance.eval (e,z) cs).2
  induction cs generalizing s z with
  | nil => exact h
  | cons c cs ih =>
    exact ih _ _ (sampled_dispatch_rep h e he c)

theorem samples_fold_expect {G : Game} {B : ℕ} {R : SourceControl.Result G B}
    (n : ℕ) (s : SourceControl.State G B R) (Q : SourceControl.State G B R→ℚ) :
    (drawSamples (sampleExponent B) n).expect (fun cs => Q (cs.foldl (fun s c => SourceControl.sampledStep c.length s) s)) =
      (SourceControl.sampledRun n s).expect Q := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [drawSamples,RandomTree.expect_bind,RandomTree.expect_map,Function.comp_def,List.foldl_cons,List.length_replicate,
      SourceControl.sampledRun]
    simp_rw [ih]

theorem samples_fold_all {G : Game} {B : ℕ} {R : SourceControl.Result G B}
    (n : ℕ) (s : SourceControl.State G B R) (Q : SourceControl.State G B R→Prop) :
    (drawSamples (sampleExponent B) n).All (fun cs => Q (cs.foldl (fun s c => SourceControl.sampledStep c.length s) s)) ↔
      (SourceControl.sampledRun n s).All Q := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [drawSamples,RandomTree.all_bind,RandomTree.all_map,List.foldl_cons,List.length_replicate,
      SourceControl.sampledRun]
    simp_rw [ih]
end MeanPayoff.TreeDevice.Certified.RawControl

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Allocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace RootCode
open InputCode

theorem g_length (G : Game) : (g (game G)).length=globalG (topWidth G).toNat+1 := by
  change (NaturalLog.length (width (game G))).length+1+1=_
  rw [NaturalLog.length_exact _ (by rw [width_val]; exact (topWidth_positive G).le),width_val]
  unfold globalG
  omega
 theorem argument_length (G : Game) : (argument (game G)).length=2^17*(globalG (topWidth G).toNat+1) := by
  simp only [argument,comp_eval,pair_eval,const_eval,Counter.mul_length,List.length_replicate,g_length]
 theorem exponent_length (G : Game) : (exponent (game G)).length=sampleExponent (topWidth G).toNat := by
  change (NaturalLog.ceil (Counter.word (argument (game G)))).length=_
  rw [NaturalLog.ceil_exact _ (by rw [Counter.word_val]; exact_mod_cast (show 0<(argument (game G)).length by rw [argument_length]; positivity)),Counter.word_val,Int.toNat_natCast,argument_length]
  rfl
 theorem samples_length (G : Game) : (samples (game G)).length=globalS (topWidth G).toNat := by
  change (Counter.power (exponent (game G),cap (game G))).length=_
  rw [Counter.power_exact]
  · rw [List.length_replicate,exponent_length]
    rfl
  · change 2^(exponent (game G)).length ≤ (Counter.add (argument (game G),argument (game G))).length
    rw [Counter.add_length,exponent_length,argument_length]
    have h := Counter.pow_clog_le (2^17*(globalG (topWidth G).toNat+1)) (by positivity)
    change 2^Nat.clog 2 (2^17*(globalG (topWidth G).toNat+1)) ≤ _
    simpa only [two_mul] using h
 theorem trials_length (G : Game) : (trials (game G)).length=globalJ G.n (topWidth G).toNat := by
  simp only [trials,trialBase,comp_eval,pair_eval,Counter.inc_length,Counter.add_length,Counter.fixedPower_length,Counter.mul_length,n_game,List.length_replicate,samples_length]
  unfold globalJ
  omega
 theorem basic_length (G : Game) : (basic (game G)).length=G.n*(128*globalS (topWidth G).toNat) := by
  simp only [basic,comp_eval,pair_eval,Counter.mul_length,const_eval,List.length_replicate,n_game,samples_length]
 theorem env_rep (G : Game) : RawControl.EnvRep G (topWidth G).toNat (env (game G)) := by
  refine ⟨⟨Normalize.word G,rows_game G,Normalize.word_val G⟩,exponent_length G,samples_length G,trials_length G,?_⟩
  exact (basic_length G).ge
end RootCode
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace RootCode
open InputCode

 theorem budgets_rep (G : Game) : RawBudget.Rep (rootBudgets G) (budgets (game G)) := by
  have hn : (Counter.word (n (game G))).val=G.n := by simp
  have hx : ones (game G)=List.ofFn (fun _ : Fin G.n => EdgeRead.encodedWord 1) := by
    change (List.replicate G.n ()).map (fun _ => EdgeRead.encodedWord 1)=_
    simp [List.ofFn_const]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · change 0<(Counter.word (n (game G))).val
    rw [hn]; exact_mod_cast G.positive
  · change 0<(Word.constant 1 (game G)).val
    simp
  · change 0<(Counter.word (n (game G))).val
    rw [hn]; exact_mod_cast G.positive
  · change 0<(Word.constant 1 (game G)).val
    simp
  · change (G.n : ℚ)=(Counter.word (n (game G))).val/(Word.constant 1 (game G)).val
    simp
  · change (G.n : ℚ)=(Counter.word (n (game G))).val/(Word.constant 1 (game G)).val
    simp
  · refine ⟨fun _ => EdgeRead.encodedWord 1,fun _ => EdgeRead.encodedWord 1,hx,hx,?_,?_,?_,?_⟩ <;>
      intro i <;> simp [EdgeRead.encodedWord_val,rootBudgets]
 theorem box_rep (G : Game) : RawBox.Rep (rootBox G) (box (game G)) := by
  refine ⟨?_,?_,?_⟩
  · change (width (game G)).val=((topWidth G).toNat : ℤ)
    rw [width_val,Int.toNat_of_nonneg (topWidth_positive G).le]
  · refine ⟨fun _ => EdgeRead.encodedWord 0,?_,?_⟩
    · change (List.replicate G.n ()).map (fun _ => EdgeRead.encodedWord 0)=_
      simp [List.ofFn_const]
    · intro i; exact EdgeRead.encodedWord_val 0
  · refine ⟨fun _ => width (game G),?_,?_⟩
    · change (List.replicate G.n ()).map (fun _ => width (game G))=_
      simp [List.ofFn_const]
    · intro i; exact width_val G
 theorem state_rep (G : Game) : RawControl.StateRep
    (SourceControl.State.call (SourceControl.Job.solve (rootBudgets G) (rootBox G)) .done) (state (game G)) := by
  exact .call rfl ⟨budgets_rep G,box_rep G⟩ .done
end RootCode
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Preparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Preparation
 theorem logarithm_length (d : Digits) : (logarithm d).length=Nat.clog 2 (d.bits.length+2) := by
  change (NaturalLog.ceil (Counter.word (Counter.inc (Counter.inc (inputLength d))))).length=_
  rw [NaturalLog.ceil_exact _ (by rw [Counter.word_val]; simp only [Counter.inc_length]; positivity),Counter.word_val,Int.toNat_natCast]
  change Nat.clog 2 ((d.bits.map (fun _ => ())).length+1+1)=_
  simp only [List.length_map,Nat.add_assoc]
 theorem exponent_length (d : Digits) : (exponent d).length=25000*(Nat.clog 2 (d.bits.length+2))^2 := by
  simp only [exponent,comp_eval,pair_eval,Counter.mul_length,const_eval,List.length_replicate,Counter.fixedPower_length,logarithm_length]
 theorem bits_length (d : Digits) : (value d).1.length=(root d).1.1.length*2^(exponent d).length := by
  change (Counter.mul ((root d).1.1,Fold.fold Allocation.double.eval [()] (exponent d))).length=_
  rw [Counter.mul_length,Allocation.exact,List.length_replicate]
 theorem aux (d : Digits) : (value d).2=((root d).1,List.replicate (2^(exponent d).length) (), (root d).2) := by
  change ((root d).1,Fold.fold Allocation.double.eval [()] (exponent d),(root d).2)=_
  rw [Allocation.exact]
end Preparation
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Traces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.RegisterBits
open RandomTree BinaryData.Take

namespace Traces
variable {K : ℕ} {P : Program K} {c d : Config P} {t : RandomTree (Config P)}
 theorem leaf (c : Config P) : Traces P c (.leaf c) := by intro bits pos; simp [consume,advance]
 theorem wait (n : ℕ) (h : ∀ bits, advance P bits c n=d) (ht : Traces P d t) :
    Traces P c (RandomTree.wait n t) := by
  intro bits pos
  simp only [consume_wait]
  have hp := (consume_path t bits (pos+n)).1
  rw [show (t.consume bits (pos+n)).2-pos=n+((t.consume bits (pos+n)).2-(pos+n)) by omega,
    advance_add,h]
  simpa only [Nat.add_assoc] using ht bits (pos+n)
 theorem coin {l r : RandomTree (Config P)}
    (hl : Traces P (step P c false) l) (hr : Traces P (step P c true) r) :
    Traces P c (.coin l r) := by
  intro bits pos
  simp only [consume]
  split
  next hb =>
    have hp := (consume_path r bits (pos+1)).1
    rw [show (r.consume bits (pos+1)).2-pos=((r.consume bits (pos+1)).2-(pos+1))+1 by omega,
      advance_front]
    simp only [Nat.add_zero,hb]
    convert hr bits (pos+1) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext j
    congr 1
    omega
  next hb =>
    have hp := (consume_path l bits (pos+1)).1
    have he : bits pos=false := Bool.eq_false_iff.mpr hb
    rw [show (l.consume bits (pos+1)).2-pos=((l.consume bits (pos+1)).2-(pos+1))+1 by omega,
      advance_front]
    simp only [Nat.add_zero,he]
    convert hl bits (pos+1) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext j
    congr 1
    omega
 theorem padded (ht : Traces P c t) (hh : t.All (fun s => s.control=none))
    {N : ℕ} (hN : t.bitDepth≤N) (bits : ℕ→Bool) : advance P bits c N=t.read bits := by
  have hp := (consume_path t bits 0).2
  have hr : (t.consume bits 0).2≤N := by simpa only [Nat.sub_zero] using hp.depth_le.trans hN
  have hs := ht bits 0
  simp only [Nat.zero_add,Nat.sub_zero] at hs
  have hn := hp.all hh
  have ha := advance_pad P c (t.consume bits 0).1 bits hr hs hn
  simpa only [consume_read,Nat.zero_add] using ha
end Traces
 theorem read_tree {K : ℕ} (P : Program K) (n : ℕ) (c : Config P) (bits : ℕ→Bool) :
    (tree P n c).read bits=advance P bits c n := by
  induction n generalizing c bits with
  | zero => rfl
  | succ n ih =>
    rw [advance_front]
    simp only [tree,RandomTree.read]
    split <;> simp_all only
 theorem depth_tree {K : ℕ} (P : Program K) (n : ℕ) (c : Config P) : (tree P n c).bitDepth=n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [tree,bitDepth,ih,Nat.max_self]
 theorem Traces.expect {K : ℕ} {P : Program K} {c : Config P} {t : RandomTree (Config P)}
    (ht : Traces P c t) (hh : t.All (fun s => s.control=none)) {N : ℕ} (hN : t.bitDepth≤N)
    (f : Config P→ℚ) : (tree P N c).expect f=t.expect f := by
  have h1 := prefix_sum (tree P N c) f N (by rw [depth_tree])
  have h2 := prefix_sum t f N hN
  have he : ∀ bits : Fin N→Bool, (tree P N c).readPrefix bits=t.readPrefix bits := by
    intro bits
    exact (read_tree P N c (padBits bits)).trans (ht.padded hh hN _)
  simp_rw [he] at h1
  rw [h2] at h1
  exact mul_left_cancel₀ (by positivity : (2:ℚ)^N≠0) h1.symm

 theorem Flow.quiet_runs {K : ℕ} (F : Flow.Program K) (p : Fin F.nodes)
    (hq : CoinFree (F.block p)) (s t : Fin K→List Bool) (out out' : List Bool) (N : ℕ)
    (h : ∀ bits, advance (F.block p) bits ⟨some (F.block p).start,s,out⟩ N=⟨none,t,out'⟩) :
    ∃ d≤N, ∀ bits, advance (Flow.compile F) bits (Flow.state F p s out) d=Flow.edge F p t out' := by
  let c : Config (F.block p) := ⟨some (F.block p).start,s,out⟩
  obtain ⟨d,hd,hh,hn,he⟩ := first_termination (F.block p) c (fun _ => false) N (by rw [h])
  refine ⟨d,hd,?_⟩
  intro bits
  have hn' : ∀ j<d, (advance (F.block p) bits c j).control≠none := by
    intro j hj
    rw [advance_coinFree _ hq]
    exact hn j hj
  change advance _ bits (Flow.embed F p c) d=_
  rw [Flow.advance_inner F p c bits d hn',advance_coinFree _ hq,he,h]
  rfl
end MeanPayoff.RegisterBits

end

section
namespace MeanPayoff.RandomTree
 theorem map_congr_all {α β : Type} (t : RandomTree α) (f g : α→β)
    (h : t.All (fun a => f a=g a)) : t.map f=t.map g := by
  induction t with
  | leaf a => exact congrArg leaf h
  | coin l r il ir => exact congrArg₂ coin (il h.1) (ir h.2)
 theorem expect_congr_all {α : Type} (t : RandomTree α) (f g : α→ℚ)
    (h : t.All (fun a => f a=g a)) : t.expect f=t.expect g := by
  apply le_antisymm
  · exact expect_mono_all t f g (all_mono t h (by intro a ha; exact ha.le))
  · exact expect_mono_all t g f (all_mono t h (by intro a ha; exact ha.ge))
end MeanPayoff.RandomTree
namespace MeanPayoff.FairBits
open RandomTree

 theorem length (n : ℕ) : (draw n).All (fun bs => bs.length=n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    constructor <;> rw [all_map] <;> exact all_mono _ ih (by intro bs hb; simp [hb])
 theorem acc_eq (n : ℕ) (bs : List Bool) : acc n bs=(draw n).map (fun xs => xs.reverse++bs) := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih => simp only [acc,draw,map_coin',map_map,ih,List.reverse_cons,List.append_assoc,List.singleton_append]
 theorem append (a b : ℕ) : draw (a+b)=(draw a).bind (fun xs => (draw b).map (xs++·)) := by
  induction a with
  | zero => simp [draw,RandomTree.map]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega]
    simp only [draw,ih,RandomTree.map_bind,RandomTree.bind,RandomTree.bind_map,map_map,List.cons_append]
 theorem prepend_value (b : Bool) (bs : List Bool) : BinaryStack.Addition.value (b::bs).reverse=
    BinaryStack.Addition.value bs.reverse + if b then 2^bs.length else 0 := by
  rw [List.reverse_cons,BinaryStack.Addition.value_append,List.length_reverse]
  cases b <;> simp [BinaryStack.Addition.value]
 theorem number (n : ℕ) : (draw n).map (fun bs => BinaryStack.Addition.value bs.reverse)=uniformBelow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [draw,map_coin',map_map,uniformBelow]
    apply congrArg₂ coin
    · simpa only [prepend_value,Bool.false_eq_true,↓reduceIte,Nat.add_zero] using ih
    · rw [←ih,map_map]
      apply map_congr_all
      exact all_mono _ (length n) (by
        intro bs hb
        rw [prepend_value,hb]; rfl)
end MeanPayoff.FairBits

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Chunks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified.Chunks
open BinaryData
open BinaryStack.Addition (value)
open SignedBits (value_bound)
 theorem sample_exact (s : State) (hc : 2 ^ (s.1.1.length) ≤ s.1.2.length) (hl : s.1.1.length ≤ s.2.2.bits.length) :
    sample s=List.replicate (value (s.2.2.bits.take s.1.1.length).reverse) () := by
  change Counter.bounded (IntegerRead.positive (Split.split (s.2.2.bits,s.1.1)).1.reverse,s.1.2)=_
  rw [Split.exact _ _ hl]
  apply Counter.bounded_exact
  · simp only [IntegerRead.positive,SignedBits.Word.val,Bool.false_eq_true,↓reduceIte,sub_zero]
  · have h := value_bound (s.2.2.bits.take s.1.1.length).reverse
    rw [List.length_reverse,List.length_take,min_eq_left hl] at h
    omega
 theorem fold_decode (s : State) (cs : Count) (hc : 2 ^ (s.1.1.length) ≤ s.1.2.length)
    (hl : s.1.1.length*cs.length ≤ s.2.2.bits.length) :
    (Fold.fold step.eval s cs).2.1.reverse=s.2.1.reverse++decode s.1.1.length cs.length s.2.2.bits := by
  induction cs generalizing s with
  | nil => simp [Fold.fold,decode]
  | cons u us ih =>
    have he : s.1.1.length ≤ s.2.2.bits.length := by simp only [List.length_cons] at hl; nlinarith
    have hd : (next s).1.1.length*us.length ≤ (next s).2.2.bits.length := by
      rw [next_params,next_bits,List.length_drop]
      simp only [List.length_cons] at hl
      have hh : s.1.1.length*us.length+s.1.1.length ≤ s.2.2.bits.length := by nlinarith
      omega
    change (Fold.fold step.eval (next s) us).2.1.reverse=_
    rw [ih (next s) (by rw [next_params]; exact hc) hd,next_params,next_acc,next_bits,List.reverse_cons,List.append_assoc]
    simp only [List.length_cons,decode,List.singleton_append,sample_exact s hc he]
 theorem run_exact (p : Count×Count) (bs : Digits) (cs : Count)
    (hc : 2 ^ (p.1.length) ≤ p.2.length) (hl : p.1.length*cs.length ≤ bs.bits.length) :
    run (p,bs,cs)=decode p.1.length cs.length bs.bits := by
  change (Fold.fold step.eval (p,[],bs) cs).2.1.reverse=_
  rw [fold_decode (p,[],bs) cs hc hl]
  rfl
 theorem decode_append (e n : ℕ) (xs ys : List Bool) (hx : xs.length=e) :
    decode e (n+1) (xs++ys)=List.replicate (value xs.reverse) ()::decode e n ys := by
  subst e
  simp only [decode,List.take_left,List.drop_left]
end MeanPayoff.TreeDevice.Certified.Chunks

end

section
namespace MeanPayoff.RandomTree
 theorem bind_congr_all {α β : Type} (t : RandomTree α) (f g : α→RandomTree β)
    (h : t.All (fun a => f a=g a)) : t.bind f=t.bind g := by
  induction t with
  | leaf a => exact h
  | coin l r il ir => exact congrArg₂ coin (il h.1) (ir h.2)
end MeanPayoff.RandomTree
namespace MeanPayoff.TreeDevice.Certified.Chunks
open RandomTree BinaryStack.Addition
 theorem decode_law (e n : ℕ) :
    (FairBits.draw (e*n)).map (decode e n)=RawControl.drawSamples e n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show e*(n+1)=e+e*n by ring, FairBits.append]
    simp only [RandomTree.map_bind,RandomTree.map_map,RawControl.drawSamples]
    rw [←FairBits.number e,RandomTree.bind_map]
    apply bind_congr_all
    apply all_mono _ (FairBits.length e)
    intro xs hx
    simp_rw [decode_append e n xs _ hx]
    rw [←RandomTree.map_map,ih]
end MeanPayoff.TreeDevice.Certified.Chunks

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace PostCode
 theorem classify_eval (w : W) (xs : List W) :
    classify (w,xs)=xs.map (fun x => decide (w.val/2<x.val)) := by
  simp only [classify,comp_eval,pair_eval,fst_eval,snd_eval,envMap_eval]
  apply List.map_congr_left
  intro x hx
  change Compare.testPair (Halve.halve w,x)=_
  rw [Compare.testPair_eq,Halve.halve_val]
 theorem returned_eval (w : W) (a : RawControl.Acc) : returned (w,a)=(w,a.2.1.2.q) := rfl
 theorem digits_eval (bs : List Bool) : digits bs=⟨bs⟩ := rfl
 theorem samples_eval (z : Input) : samples z=Chunks.run (z.2.1,⟨z.1.bits.reverse⟩,z.2.2.1) := rfl
 theorem execute_eval (z : Input) : execute z=(z.2.2.2.1,RawControl.loop (z.2.2.2.2,samples z)) := rfl
end PostCode
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_RandomTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.RegisterBits.Flow
open BinaryData.Take
 theorem quiet_hop_all {K : ℕ} (F : Program K) (p : Fin F.nodes)
    (hq : CoinFree (F.block p)) (s t : Fin K→List Bool) (out out' : List Bool) (N : ℕ)
    (h : ∀ bits, advance (F.block p) bits ⟨some (F.block p).start,s,out⟩ N=⟨none,t,out'⟩)
    (d : Config (compile F)) (he : ∀ b, RegisterBits.step (compile F) (edge F p t out') b=d) :
    ∃ n≤N+1, ∀ bits, advance (compile F) bits (state F p s out) n=d := by
  obtain ⟨n,hn,hh⟩ := quiet_runs F p hq s t out out' N h
  exact ⟨n+1,by omega,fun bits => by rw [advance,hh,he]⟩
 theorem skip_edge (F : Program 5) (p : Fin F.nodes) (hp : F.block p=TreeDevice.skip)
    (s : Fin 5→List Bool) (out : List Bool) (b : Bool) :
    RegisterBits.step (compile F) (state F p s out) b=edge F p s out := by
  have h := step_inner F p ⟨some (F.block p).start,s,out⟩ (by simp) b
  change RegisterBits.step _ (state F p s out) b=_ at h
  rw [h]
  have ht : ∀ q top b, (F.block p).transition q top b=none := by
    rw [hp]; intros; rfl
  simp only [RegisterBits.step,ht]
  rfl
end MeanPayoff.RegisterBits.Flow
namespace MeanPayoff.RandomTable
open RegisterBits BinaryData TreeDevice
open BinaryData.Take (advance_add config_ext)
variable (pre post : RegisterBits.Program 5)
 theorem skip_step (p : Fin 12) (h0 : p≠0) (h9 : p≠9) (h11 : p≠11)
    (xs ys out : List Bool) (b : Bool) :
    RegisterBits.step (program pre post) (cfg pre post p xs ys out) b=edge pre post p xs ys out := by
  exact Flow.skip_edge (flow pre post) p (by simp [flow,h0,h9,h11]) _ _ _
 theorem boundary (p : Fin 12) (xs ys out : List Bool) (b : Bool) :
    RegisterBits.step (program pre post) (edge pre post p xs ys out) b =
    match (flow pre post).next p ((core xs ys []) ((flow pre post).read p)).head? b with
    | none => ⟨none,core xs ys [],out⟩
    | some a => Flow.state (flow pre post) a.next
        (Function.update (core xs ys []) ((flow pre post).read p)
          (BinaryStack.applyOp a.work ((core xs ys []) ((flow pre post).read p)))) (out++a.emit.toList) :=
  by
    convert Flow.step_boundary (flow pre post) p (core xs ys []) out b using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
    cases (flow pre post).next p ((core xs ys []) ((flow pre post).read p)).head? b <;> rfl
 theorem wait_two (p q : Fin 12) (h0 : p≠0) (h9 : p≠9) (h11 : p≠11)
    (xs ys xs' ys' out : List Bool)
    (h : ∀ b, RegisterBits.step (program pre post) (edge pre post p xs ys out) b=cfg pre post q xs' ys' out)
    (bits : ℕ→Bool) : advance (program pre post) bits (cfg pre post p xs ys out) 2=cfg pre post q xs' ys' out := by
  simp only [advance,skip_step pre post p h0 h9 h11,h]
 theorem loop_one (ns xs ys out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 3 (true::false::ns++xs) ys out) 5 =
      edge pre post 5 (ns++xs) ys out := by
  have h3 : ∀ b, RegisterBits.step (program pre post) (edge pre post 3 (true::false::ns++xs) ys out) b=
      cfg pre post 4 (false::ns++xs) ys out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  have h4 : ∀ b, RegisterBits.step (program pre post) (edge pre post 4 (false::ns++xs) ys out) b=
      cfg pre post 5 (ns++xs) ys out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  change advance _ bits _ (2+(2+1)) = _
  rw [advance_add,wait_two pre post 3 4 (by decide) (by decide) (by decide) _ _ _ _ _ h3,
    advance_add,wait_two pre post 4 5 (by decide) (by decide) (by decide) _ _ _ _ _ h4]
  exact skip_step pre post 5 (by decide) (by decide) (by decide) _ _ _ _
 theorem toss_false (xs ys out : List Bool) :
    RegisterBits.step (program pre post) (edge pre post 5 xs ys out) false=cfg pre post 8 xs (false::ys) out := by
  rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
 theorem toss_true (xs ys out : List Bool) :
    RegisterBits.step (program pre post) (edge pre post 5 xs ys out) true=cfg pre post 6 xs (false::ys) out := by
  rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
 theorem cons_false (xs ys out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 8 xs (false::ys) out) 2=cfg pre post 3 xs (consCode false++ys) out := by
  apply wait_two pre post 8 3 (by decide) (by decide) (by decide)
  intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
 theorem cons_true (xs ys out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 6 xs (false::ys) out) 6=cfg pre post 3 xs (consCode true++ys) out := by
  have h6 : ∀ b, RegisterBits.step (program pre post) (edge pre post 6 xs (false::ys) out) b=
      cfg pre post 7 xs (false::false::ys) out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  have h7 : ∀ b, RegisterBits.step (program pre post) (edge pre post 7 xs (false::false::ys) out) b=
      cfg pre post 8 xs (true::false::false::ys) out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  change advance _ bits _ (2+(2+2)) = _
  rw [advance_add,wait_two pre post 6 7 (by decide) (by decide) (by decide) _ _ _ _ _ h6,
    advance_add,wait_two pre post 7 8 (by decide) (by decide) (by decide) _ _ _ _ _ h7]
  apply wait_two pre post 8 3 (by decide) (by decide) (by decide)
  intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
end MeanPayoff.RandomTable

end

section
namespace MeanPayoff.RandomTable
open RegisterBits BinaryData TreeDevice RandomTree
open BinaryData.Take (advance_add config_ext)
variable (pre post : RegisterBits.Program 5)
 theorem loop_zero (xs ys out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 3 (false::xs) ys out) 2=cfg pre post 9 xs ys out := by
  apply wait_two pre post 3 9 (by decide) (by decide) (by decide)
  intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
 theorem pair_up (xs out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 10 xs [] out) 2=cfg pre post 11 (true::xs) [] out := by
  apply wait_two pre post 10 11 (by decide) (by decide) (by decide)
  intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
 theorem moves (x : Data) (xs out : List Bool) :
    ∃ n≤6*treeSize x+4, ∀ bits, advance (program pre post) bits
      (cfg pre post 9 xs (encode x) out) n=cfg pre post 10 (encode x++xs) [] out := by
  apply Flow.quiet_hop_all (flow pre post) (9 : Fin 12) (by intro q top bit; rfl)
    (core xs (encode x) []) (core (encode x++xs) [] []) out out (6*treeSize x+3)
  · intro bits
    change advance (moveCode 1 0) bits ⟨some (moveCode 1 0).start,core xs (encode x) [],out⟩ _ = _
    convert move10 x [] xs [] out bits using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [List.append_nil] ; try rfl)
  · intro b
    change RegisterBits.step _ (edge pre post 9 (encode x++xs) [] out) b=_
    rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
 theorem finishes (hq : CoinFree post) (x : Data) (out result : List Bool) (N : ℕ)
    (h : ∀ bits, advance post bits ⟨some post.start,store x [],out⟩ N=⟨none,core [] [] [],result⟩) :
    ∃ n≤N+1, ∀ bits, advance (program pre post) bits (cfg pre post 11 (encode x) [] out) n=
      ⟨none,core [] [] [],result⟩ := by
  have he : ∀ b, RegisterBits.step (Flow.compile (flow pre post))
      (Flow.edge (flow pre post) (11 : Fin 12) (core [] [] []) result) b=
      ⟨none,core [] [] [],result⟩ := by intro b; exact boundary pre post 11 [] [] result b
  obtain ⟨n,hn,hh⟩ := Flow.quiet_hop_all (flow pre post) (11 : Fin 12) hq
    (store x []) (core [] [] []) out result N h _ he
  refine ⟨n,hn,fun bits => ?_⟩
  simpa only [program,cfg,store,List.append_nil,core] using hh bits
 theorem list_size (bs : List Bool) : treeSize (listData bs)≤4*bs.length+1 := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    change (encode (listData (b::bs))).length≤_
    rw [encode_list_cons,List.length_append,List.length_cons]
    have h := consCode_length_le b
    change (encode (listData bs)).length≤_ at ih
    omega
 theorem sample_trace (hq : CoinFree post) (x : Data) (result : List Bool→List Bool) (U N : ℕ)
    (hp : ∀ bs, bs.length=U → ∀ bits,
      advance post bits ⟨some post.start,store (.pair (listData bs) x) [],[]⟩ N=
        ⟨none,core [] [] [],result bs⟩) (n : ℕ) (bs : List Bool) (hn : n+bs.length=U) :
    ∃ t : RandomTree (Config (program pre post)),
      Traces (program pre post) (cfg pre post 3
        (encode (listTree (fun _ : Unit => Data.nil) (List.replicate n ()))++encode x) (encode (listData bs)) []) t ∧
      t.All (fun c => c.control=none) ∧ t.bitDepth≤12*n+24*U+N+15 ∧
      ∀ f : Config (program pre post)→ℚ, t.expect f=(FairBits.acc n bs).expect
        (fun cs => f ⟨none,core [] [] [],result cs⟩) := by
  induction n generalizing bs with
  | zero =>
    obtain ⟨a,ha,ea⟩ := moves pre post (listData bs) (encode x) []
    obtain ⟨b,hb,eb⟩ := finishes pre post hq (.pair (listData bs) x) [] (result bs) N (hp bs (by omega))
    let d : Config (program pre post) := ⟨none,core [] [] [],result bs⟩
    let t : RandomTree (Config (program pre post)) := wait (2+a+2+b) (.leaf d)
    refine ⟨t,?_,?_,?_,?_⟩
    · apply Traces.wait _ ?_ (Traces.leaf d)
      intro bits
      change advance _ bits (cfg pre post 3 (false::encode x) (encode (listData bs)) []) (2+a+2+b)=d
      rw [advance_add,advance_add,advance_add,loop_zero,ea,pair_up]
      exact eb _
    · simp [t,All,d]
    · simp only [t,depth_wait,bitDepth,Nat.add_zero]
      have hs := list_size bs
      omega
    · intro f; simp only [t,expect_wait,expect,FairBits.acc]; rfl
  | succ n ih =>
    obtain ⟨l,hl,hal,hdl,hel⟩ := ih (false::bs) (by simp only [List.length_cons]; omega)
    obtain ⟨r,hr,har,hdr,her⟩ := ih (true::bs) (by simp only [List.length_cons]; omega)
    let t := wait 5 (RandomTree.coin (wait 2 l) (wait 6 r))
    refine ⟨t,?_,?_,?_,?_⟩
    · refine Traces.wait (d:=edge pre post 5
          (encode (listTree (fun _ : Unit => Data.nil) (List.replicate n ()))++encode x)
          (encode (listData bs)) []) 5 ?_ ?_
      · intro bits
        exact loop_one pre post (encode (listTree (fun _ : Unit => Data.nil) (List.replicate n ()))) (encode x) (encode (listData bs)) [] bits
      · apply Traces.coin
        · rw [toss_false]
          apply Traces.wait 2 (cons_false pre post _ _ [])
          simpa only [encode_list_cons] using hl
        · rw [toss_true]
          apply Traces.wait 6 (cons_true pre post _ _ [])
          simpa only [encode_list_cons] using hr
    · simp only [t,all_wait,All]; exact ⟨hal,har⟩
    · simp only [t,depth_wait,bitDepth]
      omega
    · intro f
      simp only [t,expect_wait,expect,FairBits.acc,hel,her]
 theorem begin_steps (xs ys out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 1 (true::xs) ys out) 4=
      cfg pre post 3 xs (false::ys) out := by
  have h1 : ∀ b, RegisterBits.step (program pre post) (edge pre post 1 (true::xs) ys out) b=
      cfg pre post 2 xs ys out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  have h2 : ∀ b, RegisterBits.step (program pre post) (edge pre post 2 xs ys out) b=
      cfg pre post 3 xs (false::ys) out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  change advance _ bits _ (2+2)=_
  rw [advance_add,wait_two pre post 1 2 (by decide) (by decide) (by decide) _ _ _ _ _ h1]
  exact wait_two pre post 2 3 (by decide) (by decide) (by decide) _ _ _ _ _ h2 _
 theorem complete_trace (hpre : CoinFree pre) (hpost : CoinFree post)
    (input : List Bool) (x : Data) (result : List Bool→List Bool) (U A B : ℕ)
    (hp : ∀ bits, advance pre bits ⟨some pre.start,core input [] [],[]⟩ A=
      ⟨none,store (.pair (listTree (fun _ : Unit => Data.nil) (List.replicate U ())) x) [],[]⟩)
    (hq : ∀ bs, bs.length=U → ∀ bits,
      advance post bits ⟨some post.start,store (.pair (listData bs) x) [],[]⟩ B=
        ⟨none,core [] [] [],result bs⟩) :
    ∃ t : RandomTree (Config (program pre post)),
      Traces (program pre post) (cfg pre post 0 input [] []) t ∧
      t.All (fun c => c.control=none) ∧ t.bitDepth≤A+36*U+B+20 ∧
      ∀ f : Config (program pre post)→ℚ, t.expect f=(FairBits.acc U []).expect
        (fun cs => f ⟨none,core [] [] [],result cs⟩) := by
  let z := Data.pair (listTree (fun _ : Unit => Data.nil) (List.replicate U ())) x
  have he : ∀ b, RegisterBits.step (Flow.compile (flow pre post))
      (Flow.edge (flow pre post) (0 : Fin 12) (store z []) []) b=
      cfg pre post 1 (encode z) [] [] := by
    intro b
    change RegisterBits.step _ (edge pre post 0 (encode z++[]) [] []) b=_
    rw [List.append_nil,boundary]
    apply config_ext <;> (try rfl)
    funext i; fin_cases i <;> rfl
  obtain ⟨a,ha,ea⟩ := Flow.quiet_hop_all (flow pre post) (0 : Fin 12) hpre
    (core input [] []) (store z []) [] [] A hp _ he
  change ∀ bits, advance (program pre post) bits (cfg pre post 0 input [] []) a=
    cfg pre post 1 (encode z) [] [] at ea
  obtain ⟨t,ht,hal,hd,he⟩ := sample_trace pre post hpost x result U B hq U [] (by simp)
  refine ⟨wait (a+4) t,?_,by simpa only [all_wait] using hal,?_,?_⟩
  · apply Traces.wait _ ?_ ht
    intro bits
    rw [advance_add,ea]
    exact begin_steps pre post _ [] [] _
  · simp only [depth_wait]
    omega
  · intro f; rw [expect_wait,he]
end MeanPayoff.RandomTable

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Realizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.Realizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified
 theorem pre_quiet : CoinFree pre :=
  Sequence5.quiet _ _ Box5.quiet (Sequence5.quiet _ _ (by intro q top b; rfl) Preparation.device.quiet)
 theorem pre_runs (d : Digits) (bits : ℕ→Bool) :
    advance pre bits ⟨some pre.start,core d.bits [] [],[]⟩ (preCost d)=
      ⟨none,store (encode (Preparation.value d)) [],[]⟩ := by
  have hd : (encode d : Data)=listData d.bits := Halve.listTree_boolData _
  apply Sequence5.runs Box5.program preTail (core d.bits [] []) (core [] (BinaryData.encode (encode d)) [])
    (store (encode (Preparation.value d)) []) [] [] _ _ ?_ ?_ bits
  · intro cs; rw [hd]; exact Box5.runs d.bits [] cs
  · intro cs
    apply Sequence5.runs (moveCode 1 0) Preparation.device.program _ (store (encode d) []) _ [] [] _ _ ?_ ?_ cs
    · intro ds
      convert move10 (encode d) [] [] [] [] ds using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [store,core,List.append_nil])
    · exact Preparation.device.correct d [] []
 theorem post_quiet : CoinFree post := Sequence5.quiet _ _ PostCode.run.device.quiet Emit.quiet
 theorem post_runs (z : PostCode.Input) (bits : ℕ→Bool) :
    advance post bits ⟨some post.start,store (encode z) [],[]⟩ (postCost z)=
      ⟨none,core [] [] [],(PostCode.run z).bits⟩ := by
  apply Sequence5.runs PostCode.run.device.program Emit.program _ (store (encode (PostCode.run z)) []) _ [] _ _ _
    (PostCode.run.device.correct z [] []) ?_ bits
  intro cs
  have hd : (encode (PostCode.run z) : Data)=listData (PostCode.run z).bits := Halve.listTree_boolData _
  convert Emit.runs (PostCode.run z).bits [] [] cs using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [List.nil_append,hd] ; try rfl)
end MeanPayoff.Realizer

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open SourceControl RandomTree
 theorem halted_value {G : Game} {B : ℕ} {R : Result G B}
    (s : SourceControl.State G B R) (z : State) (h : StateRep s z) (hh : s.halted)
    (F : Pack→ℚ) (f : R.Value→ℚ) (hf : ∀ v p, ValueRep R v p → F p=f v) :
    F z.1.2=s.denote.erase.expect f := by
  cases s with
  | call j k => exact hh.elim
  | ret k v =>
    cases k with
    | push frame k => exact hh.elim
    | done =>
      cases h with
      | ret tag value stack =>
        change F _=f v
        exact hf v _ value
 theorem loop_expect {G : Game} {B : ℕ} {R : Result G B}
    (n : ℕ) (s : SourceControl.State G B R) (z : State) (h : StateRep s z)
    (e : Env) (he : EnvRep G B e) (hn : s.rank≤n)
    (F : Pack→ℚ) (f : R.Value→ℚ) (hf : ∀ v p, ValueRep R v p → F p=f v) :
    (drawSamples (sampleExponent B) n).expect (fun cs => F (loop ((e,z),cs)).2.1.2)=
      s.denote.erase.expect f := by
  have hh := (samples_fold_all n s (fun s => s.halted)).mpr
    ((sampledRun_all n s _).mpr (run_halts n s hn))
  calc
    _ = (drawSamples (sampleExponent B) n).expect
        (fun cs => (cs.foldl (fun s c => sampledStep c.length s) s).denote.erase.expect f) := by
      apply expect_congr_all
      exact all_mono _ hh (fun cs hc => halted_value _ _ (loop_rep s z h e he cs) hc F f hf)
    _ = (SourceControl.sampledRun n s).expect (fun s => s.denote.erase.expect f) := samples_fold_expect n s (fun s => s.denote.erase.expect f)
    _ = (SourceControl.run n s).tree.expect (fun p => p.1.denote.erase.expect f) := sampledRun_expect n s _
    _ = ((SourceControl.run n s).bind SourceControl.State.denote).erase.expect f := by
      simp only [Counted.erase,Counted.bind,expect_map,expect_bind,Function.comp_def]
    _ = s.denote.erase.expect f := by rw [run_denote]
end MeanPayoff.TreeDevice.Certified.RawControl
namespace MeanPayoff.SourceControl
 theorem root_rank (G : Game) :
    (State.call (Job.solve (rootBudgets G) (rootBox G)) .done).rank ≤ rootControlBound G := by
  simp only [State.rank, State.credit, Job.credit, Kont.credit, Nat.zero_add,
    State.denote, Job.denote, Kont.denote, Counted.bind_pure]
  exact Nat.mul_le_mul_left _ ((Counted.maximum_le_iff _ _).mpr
    (CountedAlgorithm.bounded_solve G _ _))
end MeanPayoff.SourceControl
namespace MeanPayoff.Realizer
open TreeDevice TreeDevice.Certified BinaryData RandomTree
 theorem classify_rep (G : Game) (w : W) (hw : w.val=topWidth G)
    (v : BoxVector (rootBox G)) (p : RawControl.Pack) (hp : RawControl.ValueRep (.vector (rootBox G)) v p) :
    PostCode.classify (w,p.q)=List.ofFn (fun i => decide (topWidth G/2<v.val i)) := by
  obtain ⟨ws,hws,hval⟩ := hp
  rw [PostCode.classify_eval,hws,List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_def,hw,hval]
 theorem root_loop_law (G : Game) (N : ℕ) (hN : SourceControl.rootControlBound G≤N)
    (f : List Bool→ℚ) :
    (RawControl.drawSamples (sampleExponent (topWidth G).toNat) N).expect
      (fun cs => f (PostCode.classify (InputCode.width (InputCode.game G),
        (RawControl.loop ((RootCode.env (InputCode.game G),RootCode.state (InputCode.game G)),cs)).2.1.2.q))) =
    (gameSolve G).expect (fun out => f (List.ofFn out)) := by
  have h := RawControl.loop_expect N _ _ (RootCode.state_rep G) _ (RootCode.env_rep G)
    ((SourceControl.root_rank G).trans hN)
    (fun p => f (PostCode.classify (InputCode.width (InputCode.game G),p.q)))
    (fun v => f (List.ofFn (fun i => decide (topWidth G/2<v.val i))))
    (fun v p hp => congrArg f (classify_rep G _ (InputCode.width_val G) v p hp))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [SourceControl.State.denote,SourceControl.Job.denote,SourceControl.Kont.denote,
    Counted.bind_pure,CountedAlgorithm.erase_solve,gameSolve,expect_map,Function.comp_def]
end MeanPayoff.Realizer

end

section
namespace MeanPayoff.Realizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified
 theorem input_size (d : Digits) (bs : List Bool) :
    treeSize (encode ((⟨bs⟩ : Digits),aux d))≤4*bs.length+treeSize (encode (aux d))+2 := by
  change treeSize (.pair (listTree boolData bs) (encode (aux d)))≤_
  rw [Halve.listTree_boolData,treeSize_pair]
  have h := RandomTable.list_size bs
  omega
 theorem post_budget (K e : ℕ) (h : ∀ z, postCost z≤K*(treeSize (encode z)+1)^e)
    (d : Digits) (bs : List Bool) (hl : bs.length=amount d) :
    postCost (⟨bs⟩,aux d)≤postBudget K e d := by
  apply (h _).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have hi := input_size d bs
  rw [hl] at hi
  omega
 theorem trace (K e : ℕ) (h : ∀ z, postCost z≤K*(treeSize (encode z)+1)^e) (d : Digits) :
    ∃ t : RandomTree (Config program), Traces program (RegisterBits.initial program d.bits) t ∧
      t.All (fun c => c.control=none) ∧ t.bitDepth≤limit K e d ∧
      ∀ f : Config program→ℚ, t.expect f=(FairBits.acc (amount d) []).expect
        (fun bs => f ⟨none,core [] [] [],answer d bs⟩) := by
  have hu : (Preparation.value d).1=List.replicate (amount d) () :=
    List.eq_replicate_of_mem (fun _ _ => Subsingleton.elim _ _)
  have hp : ∀ bits, advance pre bits ⟨some pre.start,core d.bits [] [],[]⟩ (preCost d)=
      ⟨none,store (.pair (listTree (fun _ : Unit => Data.nil) (List.replicate (amount d) ())) (encode (aux d))) [],[]⟩ := by
    intro bits
    have hv : encode (Preparation.value d)=Data.pair
        (listTree (fun _ : Unit => Data.nil) (List.replicate (amount d) ())) (encode (aux d)) := by
      change Data.pair (encode (Preparation.value d).1) (encode (aux d))=_
      rw [hu]
      rfl
    simpa only [hv] using pre_runs d bits
  have hq : ∀ bs, bs.length=amount d → ∀ bits,
      advance post bits ⟨some post.start,store (.pair (listData bs) (encode (aux d))) [],[]⟩ (postBudget K e d)=
      ⟨none,core [] [] [],answer d bs⟩ := by
    intro bs hl bits
    have hr := post_runs (⟨bs⟩,aux d) bits
    apply advance_pad _ _ _ bits (post_budget K e h d bs hl) ?_ rfl
    have hv : encode ((⟨bs⟩ : Digits),aux d)=Data.pair (listData bs) (encode (aux d)) := by
      change Data.pair (listTree boolData bs) _=_
      rw [Halve.listTree_boolData]
    simpa only [hv,answer] using hr
  obtain ⟨t,ht,hh,hd,he⟩ := RandomTable.complete_trace pre post pre_quiet post_quiet d.bits
    (encode (aux d)) (answer d) (amount d) (preCost d) (postBudget K e d) hp hq
  refine ⟨t,?_,hh,hd,he⟩
  have hi : RegisterBits.initial program d.bits=RandomTable.cfg pre post 0 d.bits [] [] := by
    apply BinaryData.Take.config_ext <;> (try rfl)
    funext i; fin_cases i <;> rfl
  rw [hi]
  exact ht
end MeanPayoff.Realizer

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Complexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.Realizer
open TreeDevice TreeDevice.Certified BinaryData RandomTree
 theorem iterations_bound (G : Game) : SourceControl.rootControlBound G ≤ iterations ⟨input G⟩ := by
  rw [iterations,Preparation.exponent_length]
  exact SourceControl.rootControlBound_nat G
 theorem root_game (G : Game) : Preparation.root ⟨input G⟩=
    ((RootCode.exponent (InputCode.game G),RootCode.samples (InputCode.game G)),
      (InputCode.width (InputCode.game G),(RootCode.env (InputCode.game G),RootCode.state (InputCode.game G)))) := by
  simp only [Preparation.root,Code.comp_eval,InputCode.parse_game,Code.pair_eval]
 theorem aux_game (G : Game) : aux ⟨input G⟩=
    ((RootCode.exponent (InputCode.game G),RootCode.samples (InputCode.game G)),
      List.replicate (iterations ⟨input G⟩) (),
      (InputCode.width (InputCode.game G),(RootCode.env (InputCode.game G),RootCode.state (InputCode.game G)))) := by
  rw [aux,Preparation.aux,root_game]
  rfl
 theorem amount_game (G : Game) : amount ⟨input G⟩=sampleExponent (topWidth G).toNat*iterations ⟨input G⟩ := by
  rw [amount,Preparation.bits_length,root_game]
  rw [RootCode.exponent_length]
  rfl
 theorem answer_eval (d : Digits) (bs : List Bool) : answer d bs=
    PostCode.classify ((aux d).2.2.1,
      (RawControl.loop ((aux d).2.2.2,PostCode.samples (⟨bs⟩,aux d))).2.1.2.q) := by
  simp only [answer,PostCode.run,Code.comp_eval,PostCode.execute_eval,PostCode.returned_eval,PostCode.digits_eval]
 theorem answer_game (G : Game) (bs : List Bool) (hl : bs.length=amount ⟨input G⟩) :
    answer ⟨input G⟩ bs.reverse=
      PostCode.classify (InputCode.width (InputCode.game G),
        (RawControl.loop ((RootCode.env (InputCode.game G),RootCode.state (InputCode.game G)),
          Chunks.decode (sampleExponent (topWidth G).toNat) (iterations ⟨input G⟩) bs)).2.1.2.q) := by
  rw [answer_eval,PostCode.samples_eval,aux_game]
  simp only [List.reverse_reverse]
  rw [Chunks.run_exact]
  · rw [RootCode.exponent_length,List.length_replicate]
  · rw [RootCode.exponent_length,RootCode.samples_length]
    rfl
  · rw [RootCode.exponent_length,List.length_replicate,hl,amount_game]
 theorem answer_expect (G : Game) (f : List Bool→ℚ) :
    (FairBits.acc (amount ⟨input G⟩) []).expect (fun bs => f (answer ⟨input G⟩ bs))=
      (gameSolve G).expect (fun out => f (List.ofFn out)) := by
  rw [FairBits.acc_eq,expect_map]
  simp only [Function.comp_def,List.append_nil]
  have hh := expect_congr_all (FairBits.draw (amount ⟨input G⟩))
    (fun bs => f (answer ⟨input G⟩ bs.reverse))
    (fun bs => f (PostCode.classify (InputCode.width (InputCode.game G),
      (RawControl.loop ((RootCode.env (InputCode.game G),RootCode.state (InputCode.game G)),
        Chunks.decode (sampleExponent (topWidth G).toNat) (iterations ⟨input G⟩) bs)).2.1.2.q)))
    (all_mono _ (FairBits.length _) (fun bs hb => congrArg f (answer_game G bs hb)))
  rw [hh,amount_game]
  have he := expect_map (FairBits.draw (sampleExponent (topWidth G).toNat*iterations ⟨input G⟩))
    (Chunks.decode (sampleExponent (topWidth G).toNat) (iterations ⟨input G⟩))
    (fun cs => f (PostCode.classify (InputCode.width (InputCode.game G),
      (RawControl.loop ((RootCode.env (InputCode.game G),RootCode.state (InputCode.game G)),cs)).2.1.2.q)))
  rw [Chunks.decode_law] at he
  exact he.symm.trans (root_loop_law G _ (iterations_bound G) f)
end MeanPayoff.Realizer

end

section
namespace MeanPayoff.Realizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified RandomTree
 theorem tree_answer (K e : ℕ) (h : ∀ z, postCost z≤K*(treeSize (encode z)+1)^e)
    (d : Digits) (f : List Bool→ℚ) :
    (tree program (limit K e d) (RegisterBits.initial program d.bits)).expect (fun c => f c.output)=
      (FairBits.acc (amount d) []).expect (fun bs => f (answer d bs)) := by
  obtain ⟨t,ht,hh,hd,he⟩ := trace K e h d
  refine (ht.expect hh hd (fun c : Config program => f c.output)).trans ?_
  simpa only using he (fun c : Config program => f c.output)
 theorem tree_law_oai (K e : ℕ) (h : ∀ z, postCost z≤K*(treeSize (encode z)+1)^e)
    (G : Game) (f : List Bool→ℚ) :
    (tree program (limit K e ⟨input G⟩) (RegisterBits.initial program (input G))).expect (fun c => f c.output)=
      (gameSolve G).expect (fun out => f (List.ofFn out)) := by
  exact (tree_answer K e h ⟨input G⟩ f).trans (answer_expect G f)

end MeanPayoff.Realizer

end

end OAI
end

theorem solution : type_of% @OAI.MeanPayoff.Realizer.tree_law_oai := @OAI.MeanPayoff.Realizer.tree_law_oai
