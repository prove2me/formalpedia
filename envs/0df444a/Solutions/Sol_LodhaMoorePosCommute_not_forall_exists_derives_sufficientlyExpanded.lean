-- Prove2me | solution 1 for LodhaMoorePosCommute.not_forall_exists_derives_sufficientlyExpanded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T19:33:24.996876+00:00
-- url     : https://prove2.me/submissions/9db594ff-f388-4f2d-beb0-821d7d91fa76

import Mathlib
import Definitions.Def_LodhaMoorePosCommute
import Definitions.Def_LodhaMooreWords

/-!
# Lemma 5.6 of Lodha–Moore fails when the commutation rule moves only positive letters

Lodha–Moore (arXiv:1308.4250v3) p. 9 list the substitution `y_u y_v ⇔ y_v y_u` (incompatible `u`,
`v`) without exponents, while the proof of Lemma 5.6 moves `y_{s10}⁻¹` past other letters. Here
`LodhaMoorePosCommute.Step` is `LodhaMoore.Step` with the commutation rule restricted to positive exponents (which
contains the printed exponent-1 rule), every other rule unchanged (including the expansion of
`y_s⁻¹`). The standard form `W0 = y_00⁻¹ y_01⁻¹ y_1⁻¹ y_ε` derives no sufficiently expanded
standard form.

Proof:
* semantics: `x_s`, `y_s` act on infinite binary sequences; a word acts on the right (`act`);
  every step preserves `act`;
* invariant (`Frozen`): the `y`-letters carry labels `(r, w, c)` from four expansion trees
  (roots `y_00⁻¹`, `y_01⁻¹`, `y_1⁻¹`, `y_ε`) in order (`Forest`), with exponent `c = ±1` and chart
  `η ↦ ψ_r (w η)` (`Good`); no two consecutive labels are positive and consecutive labels have
  different regions, so commutation, cancellation and merging of `y`-letters never apply;
* no frozen standard form is sufficiently expanded (the twist by `y` in the chart of `y_ε`'s
  descendants makes a required support a non-cone).
-/

open LodhaMoore

namespace LM56

/-- The start word `y_00⁻¹ y_01⁻¹ y_1⁻¹ y_ε`. -/
def W0 : Word := [(.y [false, false], -1), (.y [false, true], -1), (.y [true], -1), (.y [], 1)]

/-! ## 2. Semantics -/

abbrev Str := Stream' Bool

/-- The cone of sequences extending `u`. -/
def cone (u : Seq) : Set Str := Set.range (fun η : Str => u ++ₛ η)

/-- `x⁻¹`: `0η ↦ 00η`, `10η ↦ 01η`, `11η ↦ 1η`. -/
def xInvFun (ξ : Str) : Str :=
  match ξ 0, ξ 1 with
  | false, _ => [false, false] ++ₛ ξ.drop 1
  | true, false => [false, true] ++ₛ ξ.drop 2
  | true, true => [true] ++ₛ ξ.drop 2

namespace PartS1
open LodhaMoore LM56
/-- Every stream is its first two digits followed by the rest. -/
theorem decomp2 (ξ : Str) : ξ = [ξ 0, ξ 1] ++ₛ ξ.drop 2 := by
  apply Stream'.ext
  intro n
  rcases n with _ | _ | n <;> rfl

/-- Two streams with the same finite prefix agree at a digit if the tails agree at the
corresponding digit. -/
theorem append_get_eq (l : List Bool) (s t : Str) (n : ℕ)
    (h : ∀ j, l.length + j = n → s j = t j) : (l ++ₛ s) n = (l ++ₛ t) n := by
  rcases lt_or_ge n l.length with hn | hn
  · exact (Stream'.get_append_left n l s hn).trans (Stream'.get_append_left n l t hn).symm
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact (Stream'.get_append_right j l s).trans
      ((h j rfl).trans (Stream'.get_append_right j l t).symm)

/-! ## `x` and `x⁻¹` -/

theorem xFun_00 (η : Str) : xFun ([false, false] ++ₛ η) = [false] ++ₛ η := rfl
end PartS1

alias xFun_00 := PartS1.xFun_00

namespace PartS1
open LodhaMoore LM56
theorem xFun_01 (η : Str) : xFun ([false, true] ++ₛ η) = [true, false] ++ₛ η := rfl
end PartS1

alias xFun_01 := PartS1.xFun_01

namespace PartS1
open LodhaMoore LM56
theorem xFun_1 (η : Str) : xFun ([true] ++ₛ η) = [true, true] ++ₛ η := rfl

theorem xInvFun_0 (η : Str) : xInvFun ([false] ++ₛ η) = [false, false] ++ₛ η := rfl
theorem xInvFun_10 (η : Str) : xInvFun ([true, false] ++ₛ η) = [false, true] ++ₛ η := rfl
theorem xInvFun_11 (η : Str) : xInvFun ([true, true] ++ₛ η) = [true] ++ₛ η := rfl

theorem xInvFun_xFun (ξ : Str) : xInvFun (xFun ξ) = ξ := by
  rw [decomp2 ξ]
  generalize ξ 0 = a
  generalize ξ 1 = b
  generalize ξ.drop 2 = η
  cases a <;> cases b
  · rw [PartS1.xFun_00, PartS1.xInvFun_0]
  · rw [PartS1.xFun_01, PartS1.xInvFun_10]
  · exact (congrArg xInvFun (PartS1.xFun_1 ([false] ++ₛ η))).trans
      (PartS1.xInvFun_11 ([false] ++ₛ η))
  · exact (congrArg xInvFun (PartS1.xFun_1 ([true] ++ₛ η))).trans
      (PartS1.xInvFun_11 ([true] ++ₛ η))

end PartS1

alias xInvFun_xFun := PartS1.xInvFun_xFun

namespace PartS1
open LodhaMoore LM56
theorem xFun_xInvFun (ξ : Str) : xFun (xInvFun ξ) = ξ := by
  rw [decomp2 ξ]
  generalize ξ 0 = a
  generalize ξ 1 = b
  generalize ξ.drop 2 = η
  cases a <;> cases b
  · exact (congrArg xFun (PartS1.xInvFun_0 ([false] ++ₛ η))).trans
      (PartS1.xFun_00 ([false] ++ₛ η))
  · exact (congrArg xFun (PartS1.xInvFun_0 ([true] ++ₛ η))).trans
      (PartS1.xFun_00 ([true] ++ₛ η))
  · rw [PartS1.xInvFun_10, PartS1.xFun_01]
  · rw [PartS1.xInvFun_11, PartS1.xFun_1]

/-! ## The recursion of `y` and `y⁻¹` -/

end PartS1

alias xFun_xInvFun := PartS1.xFun_xInvFun

alias xFun_1 := PartS1.xFun_1

namespace PartS1
open LodhaMoore LM56
/-- Each step of the recursion outputs at least one digit. -/
theorem one_le_length_yStep (σ : Bool) (ξ : Str) : 1 ≤ (yStep σ ξ).1.length := by
  cases σ <;> simp only [yStep] <;> split <;> simp

/-- The first `k` steps output at least `k` digits. -/
theorem le_length_yOut (k : ℕ) (σ : Bool) (ξ : Str) : k ≤ (yOut k σ ξ).length := by
  induction k generalizing σ ξ with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have h1 := one_le_length_yStep σ ξ
    have h2 := ih (yStep σ ξ).2.1 (yStep σ ξ).2.2
    show k + 1 ≤ ((yStep σ ξ).1 ++ yOut k (yStep σ ξ).2.1 (yStep σ ξ).2.2).length
    rw [List.length_append]
    omega

/-- `yOut k` is a prefix of `yOut (k + 1)`. -/
theorem yOut_prefix_succ (k : ℕ) (σ : Bool) (ξ : Str) : yOut k σ ξ <+: yOut (k + 1) σ ξ := by
  induction k generalizing σ ξ with
  | zero => exact List.nil_prefix
  | succ k ih =>
    show (yStep σ ξ).1 ++ yOut k (yStep σ ξ).2.1 (yStep σ ξ).2.2 <+:
      (yStep σ ξ).1 ++ yOut (k + 1) (yStep σ ξ).2.1 (yStep σ ξ).2.2
    exact (List.prefix_append_right_inj _).2 (ih _ _)

theorem yOut_prefix_of_le {k m : ℕ} (h : k ≤ m) (σ : Bool) (ξ : Str) :
    yOut k σ ξ <+: yOut m σ ξ := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (yOut_prefix_succ _ _ _)

/-- Digit `n` of `yFun` is digit `n` of the output of any number of steps that reaches it. -/
theorem yFun_eq_getD {σ : Bool} {ξ : Str} {n m : ℕ} (h : n < (yOut m σ ξ).length) :
    yFun σ ξ n = (yOut m σ ξ).getD n false := by
  show (yOut (n + 1) σ ξ).getD n false = _
  have h1 : n < (yOut (n + 1) σ ξ).length :=
    lt_of_lt_of_le (Nat.lt_succ_self n) (le_length_yOut _ _ _)
  rcases le_total (n + 1) m with hm | hm
  · obtain ⟨t, ht⟩ := yOut_prefix_of_le hm σ ξ
    rw [← ht, List.getD_append _ _ _ _ h1]
  · obtain ⟨t, ht⟩ := yOut_prefix_of_le hm σ ξ
    rw [← ht, List.getD_append _ _ _ _ h]

/-- One step of the recursion. -/
theorem yFun_step (σ : Bool) (ξ : Str) :
    yFun σ ξ = (yStep σ ξ).1 ++ₛ yFun (yStep σ ξ).2.1 (yStep σ ξ).2.2 := by
  apply Stream'.ext
  intro n
  have ho := one_le_length_yStep σ ξ
  have hrec : ∀ k, yOut (k + 1) σ ξ =
      (yStep σ ξ).1 ++ yOut k (yStep σ ξ).2.1 (yStep σ ξ).2.2 := fun _ => rfl
  rcases lt_or_ge n (yStep σ ξ).1.length with hn | hn
  · rw [Stream'.get_append_left _ _ _ hn]
    show (yOut (n + 1) σ ξ).getD n false = _
    rw [hrec, List.getD_append _ _ _ _ hn, List.getD_eq_getElem _ _ hn]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Stream'.get_append_right]
    show (yOut ((yStep σ ξ).1.length + j + 1) σ ξ).getD ((yStep σ ξ).1.length + j) false = _
    rw [hrec, List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    have hlen := le_length_yOut ((yStep σ ξ).1.length + j) (yStep σ ξ).2.1 (yStep σ ξ).2.2
    exact (yFun_eq_getD (by omega)).symm

theorem yFun_true_00 (η : Str) : yFun true ([false, false] ++ₛ η) = [false] ++ₛ yFun true η := by
  rw [yFun_step]; rfl
end PartS1

alias yFun_true_00 := PartS1.yFun_true_00

namespace PartS1
open LodhaMoore LM56
theorem yFun_true_01 (η : Str) :
    yFun true ([false, true] ++ₛ η) = [true, false] ++ₛ yFun false η := by
  rw [yFun_step]; rfl
end PartS1

alias yFun_true_01 := PartS1.yFun_true_01

namespace PartS1
open LodhaMoore LM56
theorem yFun_true_1 (η : Str) : yFun true ([true] ++ₛ η) = [true, true] ++ₛ yFun true η := by
  rw [yFun_step]; rfl
end PartS1

alias yFun_true_1 := PartS1.yFun_true_1

namespace PartS1
open LodhaMoore LM56
theorem yFun_false_0 (η : Str) :
    yFun false ([false] ++ₛ η) = [false, false] ++ₛ yFun false η := by
  rw [yFun_step]; rfl
end PartS1

alias yFun_false_0 := PartS1.yFun_false_0

namespace PartS1
open LodhaMoore LM56
theorem yFun_false_10 (η : Str) :
    yFun false ([true, false] ++ₛ η) = [false, true] ++ₛ yFun true η := by
  rw [yFun_step]; rfl
end PartS1

alias yFun_false_10 := PartS1.yFun_false_10

namespace PartS1
open LodhaMoore LM56
theorem yFun_false_11 (η : Str) :
    yFun false ([true, true] ++ₛ η) = [true] ++ₛ yFun false η := by
  rw [yFun_step]; rfl

/-! ## The inverse laws of `y` -/

/-- `yFun (!σ)` inverts `yFun σ`, digit by digit. -/
theorem yFun_not_yFun_get (n : ℕ) : ∀ (σ : Bool) (ξ : Str), yFun (!σ) (yFun σ ξ) n = ξ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro σ ξ
  rw [decomp2 ξ]
  generalize ξ 0 = a
  generalize ξ 1 = b
  generalize ξ.drop 2 = η
  cases σ <;> cases a <;> cases b
  -- `y⁻¹`
  · show yFun true (yFun false ([false] ++ₛ ([false] ++ₛ η))) n = ([false] ++ₛ ([false] ++ₛ η)) n
    rw [PartS1.yFun_false_0, PartS1.yFun_true_00]
    exact append_get_eq _ _ _ n fun j hj => ih j (by simp at hj; omega) false _
  · show yFun true (yFun false ([false] ++ₛ ([true] ++ₛ η))) n = ([false] ++ₛ ([true] ++ₛ η)) n
    rw [PartS1.yFun_false_0, PartS1.yFun_true_00]
    exact append_get_eq _ _ _ n fun j hj => ih j (by simp at hj; omega) false _
  · show yFun true (yFun false ([true, false] ++ₛ η)) n = ([true, false] ++ₛ η) n
    rw [PartS1.yFun_false_10, PartS1.yFun_true_01]
    exact append_get_eq _ _ _ n fun j hj => ih j (by simp at hj; omega) true _
  · show yFun true (yFun false ([true, true] ++ₛ η)) n = ([true, true] ++ₛ η) n
    rw [PartS1.yFun_false_11, PartS1.yFun_true_1]
    exact append_get_eq _ _ _ n fun j hj => ih j (by simp at hj; omega) false _
  -- `y`
  · show yFun false (yFun true ([false, false] ++ₛ η)) n = ([false, false] ++ₛ η) n
    rw [PartS1.yFun_true_00, PartS1.yFun_false_0]
    exact append_get_eq _ _ _ n fun j hj => ih j (by simp at hj; omega) true _
  · show yFun false (yFun true ([false, true] ++ₛ η)) n = ([false, true] ++ₛ η) n
    rw [PartS1.yFun_true_01, PartS1.yFun_false_10]
    exact append_get_eq _ _ _ n fun j hj => ih j (by simp at hj; omega) false _
  · show yFun false (yFun true ([true] ++ₛ ([false] ++ₛ η))) n = ([true] ++ₛ ([false] ++ₛ η)) n
    rw [PartS1.yFun_true_1, PartS1.yFun_false_11]
    exact append_get_eq _ _ _ n fun j hj => ih j (by simp at hj; omega) true _
  · show yFun false (yFun true ([true] ++ₛ ([true] ++ₛ η))) n = ([true] ++ₛ ([true] ++ₛ η)) n
    rw [PartS1.yFun_true_1, PartS1.yFun_false_11]
    exact append_get_eq _ _ _ n fun j hj => ih j (by simp at hj; omega) true _

theorem yFun_false_true (ξ : Str) : yFun false (yFun true ξ) = ξ :=
  Stream'.ext fun n => yFun_not_yFun_get n true ξ

end PartS1

alias yFun_false_true := PartS1.yFun_false_true

namespace PartS1
open LodhaMoore LM56
theorem yFun_true_false (ξ : Str) : yFun true (yFun false ξ) = ξ :=
  Stream'.ext fun n => yFun_not_yFun_get n false ξ

/-! ## Localization -/

end PartS1

alias yFun_true_false := PartS1.yFun_true_false

alias yFun_false_11 := PartS1.yFun_false_11

namespace PartS1
open LodhaMoore LM56
theorem localize_append (s : Seq) (f : Str → Str) (η : Str) :
    localize s f (s ++ₛ η) = s ++ₛ f η := by
  unfold localize
  rw [if_pos (by rw [Stream'.take_append_of_le_length _ _ _ le_rfl, List.take_length]),
    Stream'.drop_append_stream]

end PartS1

alias localize_append := PartS1.localize_append

namespace PartS1
open LodhaMoore LM56
theorem localize_of_not_mem (s : Seq) (f : Str → Str) (ξ : Str) (h : ξ ∉ cone s) :
    localize s f ξ = ξ := by
  unfold localize
  rw [if_neg]
  intro h'
  apply h
  have := Stream'.append_take_drop s.length ξ
  rw [h'] at this
  exact ⟨_, this⟩

end PartS1

alias localize_of_not_mem := PartS1.localize_of_not_mem

namespace PartS1
open LodhaMoore LM56
theorem localize_symm (s : Seq) (p : Equiv.Perm Str) (ξ : Str) :
    localize s p.symm (localize s p ξ) = ξ := by
  by_cases h : ξ ∈ cone s
  · obtain ⟨η, rfl⟩ := h
    rw [PartS1.localize_append, PartS1.localize_append, Equiv.symm_apply_apply]
  · rw [PartS1.localize_of_not_mem s _ ξ h, PartS1.localize_of_not_mem s _ ξ h]
end PartS1

alias localize_symm := PartS1.localize_symm

/-- `f` localized at `s`, as a permutation. -/
def locP (s : Seq) (p : Equiv.Perm Str) : Equiv.Perm Str where
  toFun := localize s p
  invFun := localize s p.symm
  left_inv := localize_symm s p
  right_inv := fun ξ => by simpa using localize_symm s p.symm ξ

/-- `x` as a permutation. -/
def xP : Equiv.Perm Str := ⟨xFun, xInvFun, xInvFun_xFun, xFun_xInvFun⟩

/-- `y` as a permutation. -/
def yP : Equiv.Perm Str := ⟨yFun true, yFun false, yFun_false_true, yFun_true_false⟩

/-- The permutation of a generator. -/
def genP : Gen → Equiv.Perm Str
  | .x s => locP s xP
  | .y s => locP s yP

/-- The right action of a word: `act (l :: w) = act w * l`, i.e. `ξ.(l w) = (ξ.l).w`. -/
def act : Word → Equiv.Perm Str
  | [] => 1
  | (g, n) :: w => act w * genP g ^ n

namespace PartS2
open LodhaMoore LM56
theorem genP_y_apply (s : Seq) (ξ : Str) : genP (.y s) ξ = localize s (yFun true) ξ := rfl
theorem genP_y_inv_apply (s : Seq) (ξ : Str) :
    (genP (.y s))⁻¹ ξ = localize s (yFun false) ξ := rfl
theorem genP_x_apply (s : Seq) (ξ : Str) : genP (.x s) ξ = localize s xFun ξ := rfl
theorem genP_x_inv_apply (s : Seq) (ξ : Str) : (genP (.x s))⁻¹ ξ = localize s xInvFun ξ := rfl

/-- Two sequences with a common infinite extension are compatible. -/
theorem compat_of_append_eq : ∀ {u v : Seq} {η ζ : Str}, u ++ₛ η = v ++ₛ ζ → u <+: v ∨ v <+: u
  | [], _, _, _, _ => Or.inl List.nil_prefix
  | _ :: _, [], _, _, _ => Or.inr List.nil_prefix
  | a :: u, b :: v, η, ζ, h => by
    rw [Stream'.cons_append_stream, Stream'.cons_append_stream] at h
    obtain ⟨rfl, h'⟩ := Stream'.cons_injective2 h
    rcases compat_of_append_eq h' with h | h
    · exact Or.inl (List.cons_prefix_cons.2 ⟨rfl, h⟩)
    · exact Or.inr (List.cons_prefix_cons.2 ⟨rfl, h⟩)

theorem not_mem_cone_of_incompat {u v : Seq} (h1 : ¬ u <+: v) (h2 : ¬ v <+: u) (η : Str) :
    u ++ₛ η ∉ cone v := by
  rintro ⟨ζ, hζ⟩
  rcases compat_of_append_eq hζ with h | h
  · exact h2 h
  · exact h1 h

theorem not_mem_cone_append {u v : Seq} (s : Seq) (h1 : ¬ u <+: v) (h2 : ¬ v <+: u) (η : Str) :
    s ++ₛ (u ++ₛ η) ∉ cone (s ++ v) := by
  rw [← Stream'.append_append_stream]
  exact not_mem_cone_of_incompat (by rwa [List.prefix_append_right_inj])
    (by rwa [List.prefix_append_right_inj]) η

theorem not_mem_cone_of_incompatible {u v : Seq} (h : Incompatible u v) {ξ : Str}
    (hu : ξ ∈ cone u) : ξ ∉ cone v := by
  obtain ⟨η, rfl⟩ := hu
  exact not_mem_cone_of_incompat h.1 h.2 η

theorem mem_cone_of_mem_cone_append {s v : Seq} {ξ : Str} (h : ξ ∈ cone (s ++ v)) :
    ξ ∈ cone s := by
  obtain ⟨ζ, rfl⟩ := h
  exact ⟨v ++ₛ ζ, (Stream'.append_append_stream s v ζ).symm⟩

theorem not_mem_cone_append_of_not_mem {s v : Seq} {ξ : Str} (h : ξ ∉ cone s) :
    ξ ∉ cone (s ++ v) := fun h' => h (mem_cone_of_mem_cone_append h')

theorem y_app (s : Seq) (η : Str) : genP (.y s) (s ++ₛ η) = s ++ₛ yFun true η :=
  localize_append s (yFun true) η
theorem yinv_app (s : Seq) (η : Str) : (genP (.y s))⁻¹ (s ++ₛ η) = s ++ₛ yFun false η :=
  localize_append s (yFun false) η
theorem x_app (s : Seq) (η : Str) : genP (.x s) (s ++ₛ η) = s ++ₛ xFun η :=
  localize_append s xFun η
theorem xinv_app (s : Seq) (η : Str) : (genP (.x s))⁻¹ (s ++ₛ η) = s ++ₛ xInvFun η :=
  localize_append s xInvFun η

theorem y_fix {s : Seq} {ξ : Str} (h : ξ ∉ cone s) : genP (.y s) ξ = ξ :=
  localize_of_not_mem s _ ξ h
theorem yinv_fix {s : Seq} {ξ : Str} (h : ξ ∉ cone s) : (genP (.y s))⁻¹ ξ = ξ :=
  localize_of_not_mem s _ ξ h
theorem x_fix {s : Seq} {ξ : Str} (h : ξ ∉ cone s) : genP (.x s) ξ = ξ :=
  localize_of_not_mem s _ ξ h
theorem xinv_fix {s : Seq} {ξ : Str} (h : ξ ∉ cone s) : (genP (.x s))⁻¹ ξ = ξ :=
  localize_of_not_mem s _ ξ h

theorem y_app' (s u : Seq) (η : Str) :
    genP (.y (s ++ u)) (s ++ₛ (u ++ₛ η)) = s ++ₛ (u ++ₛ yFun true η) := by
  rw [← Stream'.append_append_stream, y_app, Stream'.append_append_stream]
theorem yinv_app' (s u : Seq) (η : Str) :
    (genP (.y (s ++ u)))⁻¹ (s ++ₛ (u ++ₛ η)) = s ++ₛ (u ++ₛ yFun false η) := by
  rw [← Stream'.append_append_stream, yinv_app, Stream'.append_append_stream]

theorem xInvFun_0 (η : Str) : xInvFun ([false] ++ₛ η) = [false, false] ++ₛ η := by
  rw [← xFun_00, xInvFun_xFun]
theorem xInvFun_10 (η : Str) : xInvFun ([true, false] ++ₛ η) = [false, true] ++ₛ η := by
  rw [← xFun_01, xInvFun_xFun]
theorem xInvFun_11 (η : Str) : xInvFun ([true, true] ++ₛ η) = [true] ++ₛ η := by
  rw [← xFun_1, xInvFun_xFun]

/-- The cones `[00]`, `[01]`, `[1]` cover everything. -/
theorem tri_x (ζ : Str) : (∃ η, ζ = [false, false] ++ₛ η) ∨ (∃ η, ζ = [false, true] ++ₛ η) ∨
    ∃ η, ζ = [true] ++ₛ η := by
  have h2 : ζ = [ζ 0, ζ 1] ++ₛ ζ.drop 2 := by
    conv_lhs => rw [← Stream'.append_take_drop 2 ζ]
    rfl
  have h1 : ζ = [ζ 0] ++ₛ ζ.drop 1 := by
    conv_lhs => rw [← Stream'.append_take_drop 1 ζ]
    rfl
  generalize ζ 0 = a at h1 h2
  generalize ζ 1 = b at h2
  cases a
  · cases b
    · exact Or.inl ⟨_, h2⟩
    · exact Or.inr (Or.inl ⟨_, h2⟩)
  · exact Or.inr (Or.inr ⟨_, h1⟩)

/-- The cones `[0]`, `[10]`, `[11]` cover everything. -/
theorem tri_xinv (ζ : Str) : (∃ η, ζ = [false] ++ₛ η) ∨ (∃ η, ζ = [true, false] ++ₛ η) ∨
    ∃ η, ζ = [true, true] ++ₛ η := by
  have h2 : ζ = [ζ 0, ζ 1] ++ₛ ζ.drop 2 := by
    conv_lhs => rw [← Stream'.append_take_drop 2 ζ]
    rfl
  have h1 : ζ = [ζ 0] ++ₛ ζ.drop 1 := by
    conv_lhs => rw [← Stream'.append_take_drop 1 ζ]
    rfl
  generalize ζ 0 = a at h1 h2
  generalize ζ 1 = b at h2
  cases a
  · exact Or.inl ⟨_, h1⟩
  · cases b
    · exact Or.inr (Or.inl ⟨_, h2⟩)
    · exact Or.inr (Or.inr ⟨_, h2⟩)

/-! ## `act_append` -/

theorem act_append (u v : Word) : act (u ++ v) = act v * act u := by
  induction u with
  | nil => simp [act]
  | cons p u ih =>
    obtain ⟨g, n⟩ := p
    simp only [List.cons_append, act, ih, mul_assoc]

/-! ## The `x`-moves and the `y`-powers -/

end PartS2

alias act_append := PartS2.act_append

namespace PartS2
open LodhaMoore LM56
/-- `x_s` moves `t` to `t' = t.x_s` by prefix replacement. -/
theorem genP_x_of_xFin {s t t' : Seq} (h : xFin s t = some t') (η : Str) :
    genP (.x s) (t ++ₛ η) = t' ++ₛ η := by
  unfold xFin at h
  split_ifs at h with h1 h2
  · obtain ⟨d, rfl⟩ := h1
    rw [List.drop_left] at h
    rcases d with _ | ⟨_ | _, d⟩
    · simp at h
    · rcases d with _ | ⟨_ | _, r⟩
      · simp at h
      · simp at h
        subst h
        rw [Stream'.append_append_stream, Stream'.append_append_stream]
        show genP (.x s) (s ++ₛ ([false, false] ++ₛ (r ++ₛ η))) = s ++ₛ ([false] ++ₛ (r ++ₛ η))
        rw [x_app, xFun_00]
      · simp at h
        subst h
        rw [Stream'.append_append_stream, Stream'.append_append_stream]
        show genP (.x s) (s ++ₛ ([false, true] ++ₛ (r ++ₛ η))) =
          s ++ₛ ([true, false] ++ₛ (r ++ₛ η))
        rw [x_app, xFun_01]
    · simp at h
      subst h
      rw [Stream'.append_append_stream, Stream'.append_append_stream]
      show genP (.x s) (s ++ₛ ([true] ++ₛ (d ++ₛ η))) = s ++ₛ ([true, true] ++ₛ (d ++ₛ η))
      rw [x_app, xFun_1]
  · simp at h
    subst h
    exact x_fix (not_mem_cone_of_incompat h2 h1 η)

end PartS2

alias genP_x_of_xFin := PartS2.genP_x_of_xFin

namespace PartS2
open LodhaMoore LM56
/-- `x_s⁻¹` moves `t` to `t' = t.x_s⁻¹` by prefix replacement. -/
theorem genP_x_inv_of_xFinInv {s t t' : Seq} (h : xFinInv s t = some t') (η : Str) :
    (genP (.x s))⁻¹ (t ++ₛ η) = t' ++ₛ η := by
  unfold xFinInv at h
  split_ifs at h with h1 h2
  · obtain ⟨d, rfl⟩ := h1
    rw [List.drop_left] at h
    rw [Equiv.Perm.inv_eq_iff_eq]
    rcases d with _ | ⟨_ | _, d⟩
    · simp at h
    · simp at h
      subst h
      rw [Stream'.append_append_stream, Stream'.append_append_stream]
      show s ++ₛ ([false] ++ₛ (d ++ₛ η)) = genP (.x s) (s ++ₛ ([false, false] ++ₛ (d ++ₛ η)))
      rw [x_app, xFun_00]
    · rcases d with _ | ⟨_ | _, r⟩
      · simp at h
      · simp at h
        subst h
        rw [Stream'.append_append_stream, Stream'.append_append_stream]
        show s ++ₛ ([true, false] ++ₛ (r ++ₛ η)) =
          genP (.x s) (s ++ₛ ([false, true] ++ₛ (r ++ₛ η)))
        rw [x_app, xFun_01]
      · simp at h
        subst h
        rw [Stream'.append_append_stream, Stream'.append_append_stream]
        show s ++ₛ ([true, true] ++ₛ (r ++ₛ η)) = genP (.x s) (s ++ₛ ([true] ++ₛ (r ++ₛ η)))
        rw [x_app, xFun_1]
  · simp at h
    subst h
    exact xinv_fix (not_mem_cone_of_incompat h2 h1 η)

end PartS2

alias genP_x_inv_of_xFinInv := PartS2.genP_x_inv_of_xFinInv

namespace PartS2
open LodhaMoore LM56
/-- `y_s^n` fixes the sequences outside `[s]`. -/
theorem genP_y_zpow_of_not_mem (s : Seq) (n : ℤ) (ξ : Str) (h : ξ ∉ cone s) :
    (genP (.y s) ^ n) ξ = ξ :=
  Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (y_fix h) n

end PartS2

alias genP_y_zpow_of_not_mem := PartS2.genP_y_zpow_of_not_mem

namespace PartS2
open LodhaMoore LM56
/-- `y_s^n` maps `[s]` to itself. -/
theorem genP_y_zpow_mem_iff (s : Seq) (n : ℤ) (ξ : Str) :
    (genP (.y s) ^ n) ξ ∈ cone s ↔ ξ ∈ cone s := by
  constructor
  · intro h
    by_contra hξ
    rw [LM56.PartS2.genP_y_zpow_of_not_mem s n ξ hξ] at h
    exact hξ h
  · intro h
    by_contra h'
    have h'' := LM56.PartS2.genP_y_zpow_of_not_mem s (-n) _ h'
    rw [zpow_neg, Equiv.Perm.inv_eq_iff_eq] at h''
    rw [← (genP (.y s) ^ n).injective h''] at h'
    exact h' h

/-! ## `psi .D` -/

end PartS2

alias genP_y_zpow_mem_iff := PartS2.genP_y_zpow_mem_iff

/-- The roots: `y_00⁻¹`, `y_01⁻¹`, `y_1⁻¹`, `y_ε`. -/
inductive Root | A | B | C | D
  deriving DecidableEq

/-- The chart of a root: `η ↦ 00η`, `01η`, `1η`, and for `D` the inverse of the value of
`y_00⁻¹ y_01⁻¹ y_1⁻¹`. -/
def psi : Root → Str → Str
  | .A, η => [false, false] ++ₛ η
  | .B, η => [false, true] ++ₛ η
  | .C, η => [true] ++ₛ η
  | .D, η => (act (W0.take 3)).symm η

namespace PartS2
open LodhaMoore LM56
theorem psi_D_apply (ξ : Str) :
    psi .D ξ = genP (.y [false, false]) (genP (.y [false, true]) (genP (.y [true]) ξ)) := by
  show (act (W0.take 3)).symm ξ = _
  rw [show W0.take 3 = [(.y [false, false], -1), (.y [false, true], -1), (.y [true], -1)] from rfl,
    ← Equiv.Perm.inv_def]
  simp only [act, one_mul, zpow_neg_one, mul_inv_rev, inv_inv, Equiv.Perm.mul_apply]

theorem psi_D_00 (ρ : Str) :
    psi .D ([false, false] ++ₛ ρ) = [false, false] ++ₛ yFun true ρ := by
  rw [psi_D_apply, y_fix (not_mem_cone_of_incompat (by decide) (by decide) ρ),
    y_fix (not_mem_cone_of_incompat (by decide) (by decide) ρ), y_app]

end PartS2

alias psi_D_00 := PartS2.psi_D_00

namespace PartS2
open LodhaMoore LM56
theorem psi_D_01 (ρ : Str) :
    psi .D ([false, true] ++ₛ ρ) = [false, true] ++ₛ yFun true ρ := by
  rw [psi_D_apply, y_fix (not_mem_cone_of_incompat (by decide) (by decide) ρ), y_app,
    y_fix (not_mem_cone_of_incompat (by decide) (by decide) _)]

end PartS2

alias psi_D_01 := PartS2.psi_D_01

namespace PartS2
open LodhaMoore LM56
theorem psi_D_1 (ρ : Str) : psi .D ([true] ++ₛ ρ) = [true] ++ₛ yFun true ρ := by
  rw [psi_D_apply, y_app, y_fix (not_mem_cone_of_incompat (by decide) (by decide) _),
    y_fix (not_mem_cone_of_incompat (by decide) (by decide) _)]

/-! ## Steps preserve the action -/

/-- Conjugating `y_t` by a permutation that replaces the prefix `t` by `t'` gives `y_{t'}`. -/
theorem semiconj_y {g : Equiv.Perm Str} {t t' : Seq} (hg : ∀ η, g (t ++ₛ η) = t' ++ₛ η) :
    SemiconjBy g (genP (.y t)) (genP (.y t')) := by
  show g * genP (.y t) = genP (.y t') * g
  refine Equiv.ext fun ξ => ?_
  simp only [Equiv.Perm.mul_apply]
  by_cases h : ξ ∈ cone t
  · obtain ⟨η, rfl⟩ := h
    rw [y_app, hg, hg, y_app]
  · rw [y_fix h]
    symm
    apply y_fix
    rintro ⟨η, hη⟩
    exact h ⟨η, g.injective (by rw [hg]; exact hη)⟩

/-- Letters with incompatible subscripts commute. -/
theorem commute_y {u v : Seq} (h : Incompatible u v) (i j : ℤ) :
    Commute (genP (.y u) ^ i) (genP (.y v) ^ j) := by
  show _ * _ = _ * _
  refine Equiv.ext fun ξ => ?_
  simp only [Equiv.Perm.mul_apply]
  have h' : Incompatible v u := ⟨h.2, h.1⟩
  by_cases hu : ξ ∈ cone u
  · have hAu := (LM56.PartS2.genP_y_zpow_mem_iff u i ξ).2 hu
    rw [LM56.PartS2.genP_y_zpow_of_not_mem v j ξ (not_mem_cone_of_incompatible h hu),
      LM56.PartS2.genP_y_zpow_of_not_mem v j _ (not_mem_cone_of_incompatible h hAu)]
  · rw [LM56.PartS2.genP_y_zpow_of_not_mem u i ξ hu]
    by_cases hv : ξ ∈ cone v
    · have hBv := (LM56.PartS2.genP_y_zpow_mem_iff v j ξ).2 hv
      rw [LM56.PartS2.genP_y_zpow_of_not_mem u i _ (not_mem_cone_of_incompatible h' hBv)]
    · rw [LM56.PartS2.genP_y_zpow_of_not_mem v j ξ hv,
        LM56.PartS2.genP_y_zpow_of_not_mem u i ξ hu]

theorem moveX_block {s t t' : Seq} (h : xFin s t = some t') (i : ℤ) :
    act [(.y t, i), (.x s, 1)] = act [(.x s, 1), (.y t', i)] := by
  simp only [act, one_mul, zpow_one]
  exact (semiconj_y (LM56.PartS2.genP_x_of_xFin h)).zpow_right i

theorem moveXInv_block {s t t' : Seq} (h : xFinInv s t = some t') (i : ℤ) :
    act [(.y t, i), (.x s, -1)] = act [(.x s, -1), (.y t', i)] := by
  simp only [act, one_mul, zpow_neg_one]
  exact (semiconj_y (LM56.PartS2.genP_x_inv_of_xFinInv h)).zpow_right i

theorem expand_block (s : Seq) :
    act [(.y s, 1)] = act [(.x s, 1), (.y (s ++ [false]), 1), (.y (s ++ [true, false]), -1),
      (.y (s ++ [true, true]), 1)] := by
  simp only [act, one_mul, zpow_one, zpow_neg_one]
  refine Equiv.ext fun ξ => ?_
  simp only [Equiv.Perm.mul_apply]
  by_cases hξ : ξ ∈ cone s
  · obtain ⟨ζ, rfl⟩ := hξ
    rcases tri_x ζ with ⟨η, rfl⟩ | ⟨η, rfl⟩ | ⟨η, rfl⟩
    · rw [y_app s, yFun_true_00, x_app s, xFun_00, y_app' s [false],
        yinv_fix (not_mem_cone_append (u := [false]) (v := [true, false]) s (by decide)
          (by decide) _),
        y_fix (not_mem_cone_append (u := [false]) (v := [true, true]) s (by decide)
          (by decide) _)]
    · rw [y_app s, yFun_true_01, x_app s, xFun_01,
        y_fix (not_mem_cone_append (u := [true, false]) (v := [false]) s (by decide)
          (by decide) _),
        yinv_app' s [true, false],
        y_fix (not_mem_cone_append (u := [true, false]) (v := [true, true]) s (by decide)
          (by decide) _)]
    · rw [y_app s, yFun_true_1, x_app s, xFun_1,
        y_fix (not_mem_cone_append (u := [true, true]) (v := [false]) s (by decide)
          (by decide) _),
        yinv_fix (not_mem_cone_append (u := [true, true]) (v := [true, false]) s (by decide)
          (by decide) _),
        y_app' s [true, true]]
  · rw [y_fix hξ, x_fix hξ, y_fix (not_mem_cone_append_of_not_mem hξ),
      yinv_fix (not_mem_cone_append_of_not_mem hξ), y_fix (not_mem_cone_append_of_not_mem hξ)]

theorem expandInv_block (s : Seq) :
    act [(.y s, -1)] = act [(.x s, -1), (.y (s ++ [false, false]), -1),
      (.y (s ++ [false, true]), 1), (.y (s ++ [true]), -1)] := by
  simp only [act, one_mul, zpow_one, zpow_neg_one]
  refine Equiv.ext fun ξ => ?_
  simp only [Equiv.Perm.mul_apply]
  by_cases hξ : ξ ∈ cone s
  · obtain ⟨ζ, rfl⟩ := hξ
    rcases tri_xinv ζ with ⟨η, rfl⟩ | ⟨η, rfl⟩ | ⟨η, rfl⟩
    · rw [yinv_app s, yFun_false_0, xinv_app s, xInvFun_0, yinv_app' s [false, false],
        y_fix (not_mem_cone_append (u := [false, false]) (v := [false, true]) s (by decide)
          (by decide) _),
        yinv_fix (not_mem_cone_append (u := [false, false]) (v := [true]) s (by decide)
          (by decide) _)]
    · rw [yinv_app s, yFun_false_10, xinv_app s, xInvFun_10,
        yinv_fix (not_mem_cone_append (u := [false, true]) (v := [false, false]) s (by decide)
          (by decide) _),
        y_app' s [false, true],
        yinv_fix (not_mem_cone_append (u := [false, true]) (v := [true]) s (by decide)
          (by decide) _)]
    · rw [yinv_app s, yFun_false_11, xinv_app s, xInvFun_11,
        yinv_fix (not_mem_cone_append (u := [true]) (v := [false, false]) s (by decide)
          (by decide) _),
        y_fix (not_mem_cone_append (u := [true]) (v := [false, true]) s (by decide)
          (by decide) _),
        yinv_app' s [true]]
  · rw [yinv_fix hξ, xinv_fix hξ, yinv_fix (not_mem_cone_append_of_not_mem hξ),
      y_fix (not_mem_cone_append_of_not_mem hξ), yinv_fix (not_mem_cone_append_of_not_mem hξ)]

theorem commute_block {u v : Seq} (h : Incompatible u v) (i j : ℤ) :
    act [(.y u, i), (.y v, j)] = act [(.y v, j), (.y u, i)] := by
  simp only [act, one_mul]
  exact ((commute_y h i j).symm).eq

theorem split_block (g : Gen) (i j : ℤ) : act [(g, i + j)] = act [(g, i), (g, j)] := by
  simp only [act, one_mul]
  rw [add_comm, zpow_add]

theorem cancel_block (s : Seq) (i : ℤ) : act [(.y s, i), (.y s, -i)] = 1 := by
  simp only [act, one_mul, zpow_neg, inv_mul_cancel]

/-- Every substitution preserves the value. -/
theorem act_posStep {V V' : Word} (h : LodhaMoorePosCommute.Step V V') : act V = act V' := by
  cases h with
  | moveX pre post s t t' i h => simp only [LM56.PartS2.act_append, moveX_block h i]
  | moveXInv pre post s t t' i h => simp only [LM56.PartS2.act_append, moveXInv_block h i]
  | expand pre post s => simp only [LM56.PartS2.act_append, expand_block s]
  | expandInv pre post s => simp only [LM56.PartS2.act_append, expandInv_block s]
  | commute pre post u v i j hi hj h =>
    simp only [LM56.PartS2.act_append, commute_block h i j]
  | split pre post g i j hi hj hij => simp only [LM56.PartS2.act_append, split_block g i j]
  | merge pre post g i j hi hj hij => simp only [LM56.PartS2.act_append, split_block g i j]
  | cancel pre post s i hi => simp only [LM56.PartS2.act_append, cancel_block s i, one_mul]
end PartS2

alias act_posStep := PartS2.act_posStep

alias psi_D_1 := PartS2.psi_D_1

/-- A label `(r, w, c)`: root, leaf, sign (`true` for exponent `1`). -/
abbrev Label := Root × Seq × Bool

/-- The region of a label: the image of `[w]` under the root chart. -/
def region (l : Label) : Set Str := psi l.1 '' cone l.2.1

/-- The leaves of the four expansion trees, in order: expanding a leaf of sign `c` replaces it in
place by its three children (signs `c, -c, c`). -/
inductive Forest : List Label → Prop
  | init : Forest [(.A, [], false), (.B, [], false), (.C, [], false), (.D, [], true)]
  | expandPos (L₁ L₂ : List Label) (r : Root) (w : Seq) :
      Forest (L₁ ++ [(r, w, true)] ++ L₂) →
      Forest (L₁ ++ [(r, w ++ [false, false], true), (r, w ++ [false, true], false),
        (r, w ++ [true], true)] ++ L₂)
  | expandNeg (L₁ L₂ : List Label) (r : Root) (w : Seq) :
      Forest (L₁ ++ [(r, w, false)] ++ L₂) →
      Forest (L₁ ++ [(r, w ++ [false], false), (r, w ++ [true, false], true),
        (r, w ++ [true, true], false)] ++ L₂)

namespace PartL
open LodhaMoore LM56
/-- Replacing the entry `a` of a chain by `a₁, a₂, a₃` keeps it a chain, when `a₁` inherits the
left relations of `a` and `a₃` its right relations. -/
theorem isChain_expand {α : Type*} {R : α → α → Prop} {L₁ L₂ : List α} {a a₁ a₂ a₃ : α}
    (h : List.IsChain R (L₁ ++ [a] ++ L₂))
    (hl : ∀ x, R x a → R x a₁) (hr : ∀ y, R a y → R a₃ y) (h12 : R a₁ a₂) (h23 : R a₂ a₃) :
    List.IsChain R (L₁ ++ [a₁, a₂, a₃] ++ L₂) := by
  rw [List.isChain_append, List.isChain_append] at h
  obtain ⟨⟨h1, -, h1a⟩, h2, ha2⟩ := h
  refine List.isChain_append.2 ⟨List.isChain_append.2 ⟨h1, ?_, ?_⟩, h2, ?_⟩
  · simp [List.isChain_cons_cons, h12, h23]
  · intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact hl x (h1a x hx a (by simp))
  · intro x hx y hy
    have hx' : a₃ = x := by simpa using hx
    subst hx'
    exact hr y (ha2 a (by simp) y hy)

/-! ### Signs -/

/-- Two consecutive labels are not both positive. -/
def SignRel (a b : Label) : Prop := ¬ (a.2.2 = true ∧ b.2.2 = true)

theorem isChain_sign {L : List Label} (hL : Forest L) : List.IsChain SignRel L := by
  induction hL with
  | init => simp [List.isChain_cons_cons, SignRel]
  | expandPos L₁ L₂ r w _ ih =>
    exact isChain_expand ih (fun _ hx => hx) (fun _ hy => hy) (by simp [SignRel])
      (by simp [SignRel])
  | expandNeg L₁ L₂ r w _ ih =>
    exact isChain_expand ih (fun _ _ => by simp [SignRel]) (fun _ _ => by simp [SignRel])
      (by simp [SignRel]) (by simp [SignRel])

/-- No two consecutive labels are positive. -/
theorem Forest.not_pos_pos {L : List Label} (hL : Forest L) (i : ℕ) (hi : i + 1 < L.length) :
    ¬ (L[i].2.2 = true ∧ L[i + 1].2.2 = true) :=
  (isChain_sign hL).getElem i hi

/-! ### Incompatibility -/

end PartL

alias Forest.not_pos_pos := PartL.Forest.not_pos_pos

namespace PartL
open LodhaMoore LM56
theorem incompatible_append_right {u v : Seq} (x : Seq) (h : Incompatible u v) :
    Incompatible u (v ++ x) := by
  refine ⟨fun h' => ?_, fun h' => h.2 ((List.prefix_append v x).trans h')⟩
  rcases List.prefix_or_prefix_of_prefix h' (List.prefix_append v x) with h'' | h''
  · exact h.1 h''
  · exact h.2 h''

theorem incompatible_append_left {u v : Seq} (x : Seq) (h : Incompatible u v) :
    Incompatible (u ++ x) v :=
  let h' := incompatible_append_right x ⟨h.2, h.1⟩
  ⟨h'.2, h'.1⟩

theorem incompatible_append_same (w : Seq) {x y : Seq} (h : Incompatible x y) :
    Incompatible (w ++ x) (w ++ y) := by
  simpa [Incompatible] using h

/-- Two sequences with a common extension are comparable. -/
theorem prefix_or_prefix_of_append_stream_eq :
    ∀ {u v : Seq} {η η' : Str}, u ++ₛ η = v ++ₛ η' → u <+: v ∨ v <+: u
  | [], _, _, _, _ => Or.inl (List.nil_prefix)
  | _ :: _, [], _, _, _ => Or.inr (List.nil_prefix)
  | b :: u, b' :: v, η, η', h => by
    rw [Stream'.cons_append_stream, Stream'.cons_append_stream] at h
    have hb : b = b' := by simpa using congrArg Stream'.head h
    have ht : u ++ₛ η = v ++ₛ η' := by simpa using congrArg Stream'.tail h
    subst hb
    rcases prefix_or_prefix_of_append_stream_eq ht with h' | h'
    · exact Or.inl (List.cons_prefix_cons.2 ⟨rfl, h'⟩)
    · exact Or.inr (List.cons_prefix_cons.2 ⟨rfl, h'⟩)

theorem not_incompatible_of_append_stream_eq {u v : Seq} {η η' : Str}
    (h : u ++ₛ η = v ++ₛ η') : ¬ Incompatible u v := by
  rintro ⟨h1, h2⟩
  rcases prefix_or_prefix_of_append_stream_eq h with h' | h'
  · exact h1 h'
  · exact h2 h'

/-! ### Regions -/

theorem append_stream_inj (u : Seq) {η η' : Str} (h : u ++ₛ η = u ++ₛ η') : η = η' := by
  rw [← Stream'.drop_append_stream u η, h, Stream'.drop_append_stream]

theorem psi_injective (r : Root) : Function.Injective (psi r) := by
  cases r with
  | D => exact (act (W0.take 3)).symm.injective
  | A => exact fun _ _ h => append_stream_inj [false, false] h
  | B => exact fun _ _ h => append_stream_inj [false, true] h
  | C => exact fun _ _ h => append_stream_inj [true] h

theorem append_stream_mem_cone (u : Seq) (η : Str) : u ++ₛ η ∈ cone u := ⟨η, rfl⟩

/-- Consecutive labels are related: same root and incompatible leaves, or roots `A|B`, `B|C`,
or `C|D` with the `D` leaf empty or starting with `00`. -/
def RegRel (a b : Label) : Prop :=
  (a.1 = b.1 ∧ Incompatible a.2.1 b.2.1) ∨
  (a.1 = .A ∧ b.1 = .B) ∨ (a.1 = .B ∧ b.1 = .C) ∨
  (a.1 = .C ∧ b.1 = .D ∧ (b.2.1 = [] ∨ [false, false] <+: b.2.1))

/-- The empty leaf of `D` is positive. -/
def DOk (a : Label) : Prop := a.1 = .D → a.2.1 = [] → a.2.2 = true

theorem regRel_region_ne {a b : Label} (h : RegRel a b) : region a ≠ region b := by
  obtain ⟨r, u, c⟩ := a
  obtain ⟨r', v, c'⟩ := b
  intro hab
  simp only [RegRel] at h
  rcases h with ⟨hr, hi⟩ | ⟨hr, hr'⟩ | ⟨hr, hr'⟩ | ⟨hr, hr', hv⟩
  · -- same root, incompatible leaves
    subst hr
    have hm : psi r (u ++ₛ Stream'.const false) ∈ region (r, v, c') := by
      rw [← hab]; exact ⟨_, append_stream_mem_cone u _, rfl⟩
    obtain ⟨ξ, ⟨η', rfl⟩, hξ⟩ := hm
    exact not_incompatible_of_append_stream_eq (psi_injective r hξ).symm hi
  · subst hr hr'
    have hm : psi .A (u ++ₛ Stream'.const false) ∈ region (.B, v, c') := by
      rw [← hab]; exact ⟨_, append_stream_mem_cone u _, rfl⟩
    obtain ⟨ξ, -, hξ⟩ := hm
    have := prefix_or_prefix_of_append_stream_eq hξ
    revert this; decide
  · subst hr hr'
    have hm : psi .B (u ++ₛ Stream'.const false) ∈ region (.C, v, c') := by
      rw [← hab]; exact ⟨_, append_stream_mem_cone u _, rfl⟩
    obtain ⟨ξ, -, hξ⟩ := hm
    have := prefix_or_prefix_of_append_stream_eq hξ
    revert this; decide
  · subst hr hr'
    -- an element `ψ_D (00 ρ) = 00 (ρ.y)` of the `D` region
    obtain ⟨ρ, hρ⟩ : ∃ ρ : Str, [false, false] ++ₛ ρ ∈ cone v := by
      rcases hv with rfl | ⟨v', rfl⟩
      · exact ⟨Stream'.const false, [false, false] ++ₛ Stream'.const false, rfl⟩
      · exact ⟨v' ++ₛ Stream'.const false, Stream'.const false,
          Stream'.append_append_stream _ _ _⟩
    have hm : psi .D ([false, false] ++ₛ ρ) ∈ region (.C, u, c) := by
      rw [hab]; exact ⟨_, hρ, rfl⟩
    obtain ⟨ξ, -, hξ⟩ := hm
    rw [psi_D_00] at hξ
    have := prefix_or_prefix_of_append_stream_eq hξ
    revert this; decide

theorem regInv {L : List Label} (hL : Forest L) :
    List.IsChain RegRel L ∧ ∀ a ∈ L, DOk a := by
  induction hL with
  | init =>
    refine ⟨?_, ?_⟩
    · simp [List.isChain_cons_cons, RegRel]
    · simp [DOk]
  | expandPos L₁ L₂ r w _ ih =>
    refine ⟨isChain_expand ih.1 ?_ ?_ ?_ ?_, ?_⟩
    · rintro ⟨x, xw, xc⟩ hx
      simp only [RegRel] at hx ⊢
      rcases hx with ⟨hr, hi⟩ | h | h | ⟨hr, hr', hv⟩
      · exact Or.inl ⟨hr, incompatible_append_right _ hi⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · refine Or.inr (Or.inr (Or.inr ⟨hr, hr', Or.inr ?_⟩))
        rcases hv with rfl | hv
        · simp
        · exact hv.trans (List.prefix_append _ _)
    · rintro ⟨y, yw, yc⟩ hy
      simp only [RegRel] at hy ⊢
      rcases hy with ⟨hr, hi⟩ | h | h | h
      · exact Or.inl ⟨hr, incompatible_append_left _ hi⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl ⟨rfl, incompatible_append_same w (by unfold Incompatible; decide)⟩
    · exact Or.inl ⟨rfl, incompatible_append_same w (by unfold Incompatible; decide)⟩
    · intro a ha
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with (ha | ha | ha | ha) | ha
      · exact ih.2 a (by simp [ha])
      · subst ha; intro _ h; simp at h
      · subst ha; intro _ h; simp at h
      · subst ha; intro _ h; simp at h
      · exact ih.2 a (by simp [ha])
  | expandNeg L₁ L₂ r w _ ih =>
    have hD : DOk (r, w, false) := ih.2 _ (by simp)
    refine ⟨isChain_expand ih.1 ?_ ?_ ?_ ?_, ?_⟩
    · rintro ⟨x, xw, xc⟩ hx
      simp only [RegRel] at hx ⊢
      rcases hx with ⟨hr, hi⟩ | h | h | ⟨hr, hr', hv⟩
      · exact Or.inl ⟨hr, incompatible_append_right _ hi⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · refine Or.inr (Or.inr (Or.inr ⟨hr, hr', Or.inr ?_⟩))
        rcases hv with rfl | hv
        · exact absurd (hD hr' rfl) (by simp)
        · exact hv.trans (List.prefix_append _ _)
    · rintro ⟨y, yw, yc⟩ hy
      simp only [RegRel] at hy ⊢
      rcases hy with ⟨hr, hi⟩ | h | h | h
      · exact Or.inl ⟨hr, incompatible_append_left _ hi⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl ⟨rfl, incompatible_append_same w (by unfold Incompatible; decide)⟩
    · exact Or.inl ⟨rfl, incompatible_append_same w (by unfold Incompatible; decide)⟩
    · intro a ha
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with (ha | ha | ha | ha) | ha
      · exact ih.2 a (by simp [ha])
      · subst ha; intro _ h; simp at h
      · subst ha; intro _ h; simp at h
      · subst ha; intro _ h; simp at h
      · exact ih.2 a (by simp [ha])

/-- Consecutive labels have different regions. -/
theorem Forest.region_ne {L : List Label} (hL : Forest L) (i : ℕ) (hi : i + 1 < L.length) :
    region L[i] ≠ region L[i + 1] :=
  regRel_region_ne ((regInv hL).1.getElem i hi)
end PartL

alias Forest.region_ne := PartL.Forest.region_ne

/-- `Good f V L`: reading `V` from the left with `f` the value of the prefix read so far, the
`y`-letters of `V` carry the labels `L` in order; the label `(r, w, c)` on `y_t^e` means
`e = 1` if `c` and `e = -1` otherwise, and `f (ψ_r (w η)) = t η` for all `η`. -/
def Good : Equiv.Perm Str → Word → List Label → Prop
  | _, [], L => L = []
  | f, (.x s, n) :: V, L => Good (genP (.x s) ^ n * f) V L
  | _, (.y _, _) :: _, [] => False
  | f, (.y t, e) :: V, (r, w, c) :: L =>
      e = (if c then 1 else -1) ∧ (∀ η, f (psi r (w ++ₛ η)) = t ++ₛ η) ∧
        Good (genP (.y t) ^ e * f) V L

namespace PartG
open LodhaMoore LM56
theorem good_nil' (f : Equiv.Perm Str) (L : List Label) : Good f [] L ↔ L = [] := by
  simp [Good]

theorem good_x' (f : Equiv.Perm Str) (s : Seq) (n : ℤ) (V : Word) (L : List Label) :
    Good f ((.x s, n) :: V) L ↔ Good (genP (.x s) ^ n * f) V L := by
  simp [Good]

theorem good_y' (f : Equiv.Perm Str) (t : Seq) (e : ℤ) (V : Word) (L : List Label) :
    Good f ((.y t, e) :: V) L ↔ ∃ r w c L', L = (r, w, c) :: L' ∧ e = (if c then 1 else -1) ∧
      (∀ η, f (psi r (w ++ₛ η)) = t ++ₛ η) ∧ Good (genP (.y t) ^ e * f) V L' := by
  rcases L with _ | ⟨⟨r, w, c⟩, L'⟩
  · simp [Good]
  · simp only [Good]
    constructor
    · rintro ⟨he, hc, h⟩
      exact ⟨r, w, c, L', rfl, he, hc, h⟩
    · rintro ⟨r', w', c', L'', h, he, hc, hg⟩
      simp only [List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
      exact ⟨he, hc, hg⟩

theorem good_append (f : Equiv.Perm Str) (U V : Word) (L : List Label) :
    Good f (U ++ V) L ↔ ∃ L₁ L₂, L = L₁ ++ L₂ ∧ Good f U L₁ ∧ Good (act U * f) V L₂ := by
  induction U generalizing f L with
  | nil => simp [good_nil', act]
  | cons a U ih =>
    obtain ⟨g, n⟩ := a
    cases g with
    | x s =>
      simp only [List.cons_append, good_x', ih, act, mul_assoc]
    | y t =>
      simp only [List.cons_append, good_y', ih, act, mul_assoc]
      constructor
      · rintro ⟨r, w, c, L', rfl, he, hc, L₁, L₂, rfl, h1, h2⟩
        exact ⟨(r, w, c) :: L₁, L₂, rfl, ⟨r, w, c, L₁, rfl, he, hc, h1⟩, h2⟩
      · rintro ⟨L₁, L₂, rfl, ⟨r, w, c, L₁', rfl, he, hc, h1⟩, h2⟩
        exact ⟨r, w, c, L₁' ++ L₂, rfl, he, hc, L₁', L₂, rfl, h1, h2⟩

/-! ## Cones -/

end PartG

alias good_append := PartG.good_append

/-- The invariant. -/
def Frozen (V : Word) : Prop := ∃ L, Forest L ∧ Good 1 V L

namespace PartG
open LodhaMoore LM56
theorem mem_cone_iff (u : Seq) (ξ : Str) : ξ ∈ cone u ↔ ∃ η, u ++ₛ η = ξ := Iff.rfl

theorem append_mem_cone (u : Seq) (η : Str) : u ++ₛ η ∈ cone u := ⟨η, rfl⟩

theorem append_mem_cone_append_iff (s v : Seq) (ξ : Str) :
    s ++ₛ ξ ∈ cone (s ++ v) ↔ ξ ∈ cone v := by
  simp only [mem_cone_iff, Stream'.append_append_stream, Stream'.append_right_inj]

theorem cons_not_mem_cone_cons {a b : Bool} (h : a ≠ b) (l l' : Seq) (η : Str) :
    (a :: l) ++ₛ η ∉ cone (b :: l') := by
  rintro ⟨η', h'⟩
  have := congrArg Stream'.head h'
  simp [Stream'.cons_append_stream] at this
  exact h this.symm

theorem not_mem_cone_of_ne {a b : Bool} (h : a ≠ b) (s l l' : Seq) (η : Str) :
    (s ++ a :: l) ++ₛ η ∉ cone (s ++ b :: l') := by
  rw [Stream'.append_append_stream, append_mem_cone_append_iff]
  exact cons_not_mem_cone_cons h l l' η

/-! ## The start word -/

theorem act_W0_take3 :
    act (W0.take 3) = genP (.y [true]) ^ (-1 : ℤ) *
      (genP (.y [false, true]) ^ (-1 : ℤ) * (genP (.y [false, false]) ^ (-1 : ℤ) * 1)) := by
  simp [act, W0, mul_assoc]

theorem frozen_W0 : Frozen W0 := by
  refine ⟨[(.A, [], false), (.B, [], false), (.C, [], false), (.D, [], true)], Forest.init, ?_⟩
  simp only [W0, Good]
  refine ⟨by simp, fun η => rfl, by simp, fun η => ?_, by simp, fun η => ?_, by simp, fun η => ?_,
    trivial⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, psi]
    exact genP_y_zpow_of_not_mem _ _ _
      (not_mem_cone_of_ne (s := [false]) (a := true) (b := false) (by decide) [] [] η)
  · simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, psi, Stream'.nil_append_stream]
    rw [genP_y_zpow_of_not_mem [false, false] (-1) ([true] ++ₛ η)
      (not_mem_cone_of_ne (s := []) (a := true) (b := false) (by decide) [] [false] η)]
    exact genP_y_zpow_of_not_mem _ _ _
      (not_mem_cone_of_ne (s := []) (a := true) (b := false) (by decide) [] [true] η)
  · show (genP (.y [true]) ^ (-1 : ℤ) *
      (genP (.y [false, true]) ^ (-1 : ℤ) * (genP (.y [false, false]) ^ (-1 : ℤ) * 1)))
        ((act (W0.take 3)).symm η) = η
    rw [← act_W0_take3]
    exact Equiv.apply_symm_apply _ _

/-! ## Membership in cones of concrete shape -/

end PartG

alias frozen_W0 := PartG.frozen_W0

namespace PartG
open LodhaMoore LM56
theorem mem_cone_nil (ξ : Str) : ξ ∈ cone [] := ⟨ξ, rfl⟩

theorem cons_append_mem_cone_cons_iff (a b : Bool) (l l' : Seq) (η : Str) :
    (a :: l) ++ₛ η ∈ cone (b :: l') ↔ a = b ∧ l ++ₛ η ∈ cone l' := by
  simp only [mem_cone_iff, Stream'.cons_append_stream]
  constructor
  · rintro ⟨η', h'⟩
    have h1 := congrArg Stream'.head h'
    have h2 := congrArg Stream'.tail h'
    simp only [Stream'.head_cons, Stream'.tail_cons] at h1 h2
    exact ⟨h1.symm, η', h2⟩
  · rintro ⟨rfl, η', h'⟩
    exact ⟨η', by rw [h']⟩

/-! ## The values of `x_s` and `x_s⁻¹` on the three subcones of `[s]` -/

theorem genP_x_apply (s : Seq) (ξ : Str) : genP (.x s) ξ = localize s xFun ξ := rfl

theorem gx_00 (s : Seq) (η : Str) :
    genP (.x s) (s ++ₛ ([false, false] ++ₛ η)) = s ++ₛ ([false] ++ₛ η) := by
  rw [genP_x_apply, localize_append, xFun_00]

theorem gx_01 (s : Seq) (η : Str) :
    genP (.x s) (s ++ₛ ([false, true] ++ₛ η)) = s ++ₛ ([true, false] ++ₛ η) := by
  rw [genP_x_apply, localize_append, xFun_01]

theorem gx_1 (s : Seq) (η : Str) :
    genP (.x s) (s ++ₛ ([true] ++ₛ η)) = s ++ₛ ([true, true] ++ₛ η) := by
  rw [genP_x_apply, localize_append, xFun_1]

theorem gxinv_0 (s : Seq) (η : Str) :
    (genP (.x s))⁻¹ (s ++ₛ ([false] ++ₛ η)) = s ++ₛ ([false, false] ++ₛ η) := by
  rw [Equiv.Perm.inv_eq_iff_eq, gx_00]

theorem gxinv_10 (s : Seq) (η : Str) :
    (genP (.x s))⁻¹ (s ++ₛ ([true, false] ++ₛ η)) = s ++ₛ ([false, true] ++ₛ η) := by
  rw [Equiv.Perm.inv_eq_iff_eq, gx_01]

theorem gxinv_11 (s : Seq) (η : Str) :
    (genP (.x s))⁻¹ (s ++ₛ ([true, true] ++ₛ η)) = s ++ₛ ([true] ++ₛ η) := by
  rw [Equiv.Perm.inv_eq_iff_eq, gx_1]

/-! ## Regions of consecutive labels -/

/-- The region of a label is the preimage of its subscript's cone under the prefix value. -/
theorem region_eq_preimage {f : Equiv.Perm Str} {l : Label} {t : Seq}
    (h : ∀ η, f (psi l.1 (l.2.1 ++ₛ η)) = t ++ₛ η) : region l = f ⁻¹' cone t := by
  ext x
  simp only [region, Set.mem_image, Set.mem_preimage, cone, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨η, rfl⟩, rfl⟩
    exact ⟨η, (h η).symm⟩
  · rintro ⟨η, hη⟩
    refine ⟨l.2.1 ++ₛ η, ⟨η, rfl⟩, f.injective ?_⟩
    rw [h, hη]

/-- Two consecutive letters with the same subscript `t` have equal regions. -/
theorem region_eq_of_same {f : Equiv.Perm Str} {l₁ l₂ : Label} {t : Seq} {i : ℤ}
    (h₁ : ∀ η, f (psi l₁.1 (l₁.2.1 ++ₛ η)) = t ++ₛ η)
    (h₂ : ∀ η, (genP (.y t) ^ i * f) (psi l₂.1 (l₂.2.1 ++ₛ η)) = t ++ₛ η) :
    region l₁ = region l₂ := by
  rw [region_eq_preimage h₁, region_eq_preimage h₂]
  ext x
  simp only [Set.mem_preimage, Equiv.Perm.mul_apply, genP_y_zpow_mem_iff]

/-- Facts about two consecutive labels of a forest. -/
theorem forest_pair {La Lc : List Label} {l₁ l₂ : Label} (hF : Forest (La ++ [l₁, l₂] ++ Lc)) :
    region l₁ ≠ region l₂ ∧ ¬ (l₁.2.2 = true ∧ l₂.2.2 = true) := by
  have hlen : La.length + 1 < (La ++ [l₁, l₂] ++ Lc).length := by simp
  have e1 : (La ++ [l₁, l₂] ++ Lc)[La.length] = l₁ := by
    simp [List.getElem_append_right]
  have e2 : (La ++ [l₁, l₂] ++ Lc)[La.length + 1] = l₂ := by
    simp [List.getElem_append_right]
  have h1 := hF.region_ne La.length hlen
  have h2 := hF.not_pos_pos La.length hlen
  simp only [e1, e2] at h1 h2
  exact ⟨h1, h2⟩

/-! ## Replacing a block -/

/-- If a block `B` can be replaced by `B'` of the same value, keeping `Good` and the forest, then
`pre ++ B' ++ post` is frozen whenever `pre ++ B ++ post` is. -/
theorem frozen_replace {pre B B' post : Word} (hV : Frozen (pre ++ B ++ post))
    (hact : act B = act B')
    (hB : ∀ f La Lb Lc, Forest (La ++ Lb ++ Lc) → Good f B Lb →
      ∃ Lb', Forest (La ++ Lb' ++ Lc) ∧ Good f B' Lb') :
    Frozen (pre ++ B' ++ post) := by
  obtain ⟨L, hF, hG⟩ := hV
  obtain ⟨L₁, Lc, rfl, h1, hpost⟩ := (LM56.PartG.good_append _ _ _ _).1 hG
  obtain ⟨La, Lb, rfl, hpre, hblk⟩ := (LM56.PartG.good_append _ _ _ _).1 h1
  obtain ⟨Lb', hF', hblk'⟩ := hB _ La Lb Lc hF hblk
  refine ⟨La ++ Lb' ++ Lc, hF', (LM56.PartG.good_append _ _ _ _).2
    ⟨La ++ Lb', Lc, rfl, (LM56.PartG.good_append _ _ _ _).2 ⟨La, Lb', rfl, hpre, hblk'⟩, ?_⟩⟩
  rwa [act_append, ← hact, ← act_append]

/-! ## The blocks -/

theorem block_moveX {s t t' : Seq} {i : ℤ} (h : xFin s t = some t') (f : Equiv.Perm Str)
    (Lb : List Label) (hG : Good f [(.y t, i), (.x s, 1)] Lb) :
    Good f [(.x s, 1), (.y t', i)] Lb := by
  simp only [good_y', good_x', good_nil'] at hG
  obtain ⟨r, w, c, L', rfl, he, hc, rfl⟩ := hG
  simp only [Good]
  refine ⟨he, fun η => ?_, trivial⟩
  rw [Equiv.Perm.mul_apply, hc, zpow_one, genP_x_of_xFin h]

theorem block_moveXInv {s t t' : Seq} {i : ℤ} (h : xFinInv s t = some t') (f : Equiv.Perm Str)
    (Lb : List Label) (hG : Good f [(.y t, i), (.x s, -1)] Lb) :
    Good f [(.x s, -1), (.y t', i)] Lb := by
  simp only [good_y', good_x', good_nil'] at hG
  obtain ⟨r, w, c, L', rfl, he, hc, rfl⟩ := hG
  simp only [Good]
  refine ⟨he, fun η => ?_, trivial⟩
  rw [Equiv.Perm.mul_apply, hc, zpow_neg_one, genP_x_inv_of_xFinInv h]

theorem block_expand (s : Seq) (f : Equiv.Perm Str) (La Lb Lc : List Label)
    (hF : Forest (La ++ Lb ++ Lc)) (hG : Good f [(.y s, 1)] Lb) :
    ∃ Lb', Forest (La ++ Lb' ++ Lc) ∧
      Good f [(.x s, 1), (.y (s ++ [false]), 1), (.y (s ++ [true, false]), -1),
        (.y (s ++ [true, true]), 1)] Lb' := by
  simp only [good_y', good_nil'] at hG
  obtain ⟨r, w, c, L', rfl, he, hc, rfl⟩ := hG
  cases c
  · simp at he
  refine ⟨[(r, w ++ [false, false], true), (r, w ++ [false, true], false), (r, w ++ [true], true)],
    Forest.expandPos La Lc r w hF, ?_⟩
  simp only [Good]
  refine ⟨rfl, fun η => ?_, rfl, fun η => ?_, rfl, fun η => ?_, trivial⟩
  · simp only [Equiv.Perm.mul_apply, Stream'.append_append_stream, hc, zpow_one (genP (.x s)),
      gx_00]
  · simp (disch := simp only [append_mem_cone_append_iff, cons_append_mem_cone_cons_iff,
        Bool.true_eq_false, Bool.false_eq_true, false_and, and_false, true_and, not_false_eq_true])
      only [Equiv.Perm.mul_apply, Stream'.append_append_stream, hc, zpow_one (genP (.x s)),
      gx_01, genP_y_zpow_of_not_mem]
  · simp (disch := simp only [append_mem_cone_append_iff, cons_append_mem_cone_cons_iff,
        Bool.true_eq_false, Bool.false_eq_true, false_and, and_false, true_and, not_false_eq_true])
      only [Equiv.Perm.mul_apply, Stream'.append_append_stream, hc, zpow_one (genP (.x s)),
      gx_1, genP_y_zpow_of_not_mem]

theorem block_expandInv (s : Seq) (f : Equiv.Perm Str) (La Lb Lc : List Label)
    (hF : Forest (La ++ Lb ++ Lc)) (hG : Good f [(.y s, -1)] Lb) :
    ∃ Lb', Forest (La ++ Lb' ++ Lc) ∧
      Good f [(.x s, -1), (.y (s ++ [false, false]), -1), (.y (s ++ [false, true]), 1),
        (.y (s ++ [true]), -1)] Lb' := by
  simp only [good_y', good_nil'] at hG
  obtain ⟨r, w, c, L', rfl, he, hc, rfl⟩ := hG
  cases c
  swap
  · simp at he
  refine ⟨[(r, w ++ [false], false), (r, w ++ [true, false], true), (r, w ++ [true, true], false)],
    Forest.expandNeg La Lc r w hF, ?_⟩
  simp only [Good]
  refine ⟨rfl, fun η => ?_, rfl, fun η => ?_, rfl, fun η => ?_, trivial⟩
  · simp only [Equiv.Perm.mul_apply, Stream'.append_append_stream, hc, zpow_neg_one (genP (.x s)),
      gxinv_0]
  · simp (disch := simp only [append_mem_cone_append_iff, cons_append_mem_cone_cons_iff,
        Bool.true_eq_false, Bool.false_eq_true, false_and, and_false, true_and, not_false_eq_true])
      only [Equiv.Perm.mul_apply, Stream'.append_append_stream, hc, zpow_neg_one (genP (.x s)),
      gxinv_10, genP_y_zpow_of_not_mem]
  · simp (disch := simp only [append_mem_cone_append_iff, cons_append_mem_cone_cons_iff,
        Bool.true_eq_false, Bool.false_eq_true, false_and, and_false, true_and, not_false_eq_true])
      only [Equiv.Perm.mul_apply, Stream'.append_append_stream, hc, zpow_neg_one (genP (.x s)),
      gxinv_11, genP_y_zpow_of_not_mem]

/-- A pair of `y`-letters in a frozen word: its two labels are consecutive labels of the forest. -/
theorem good_pair {f : Equiv.Perm Str} {u v : Seq} {i j : ℤ} {Lb : List Label}
    (hG : Good f [(.y u, i), (.y v, j)] Lb) :
    ∃ l₁ l₂, Lb = [l₁, l₂] ∧ i = (if l₁.2.2 then 1 else -1) ∧ j = (if l₂.2.2 then 1 else -1) ∧
      (∀ η, f (psi l₁.1 (l₁.2.1 ++ₛ η)) = u ++ₛ η) ∧
      (∀ η, (genP (.y u) ^ i * f) (psi l₂.1 (l₂.2.1 ++ₛ η)) = v ++ₛ η) := by
  simp only [good_y', good_nil'] at hG
  obtain ⟨r, w, c, L', rfl, he, hc, r', w', c', L'', rfl, he', hc', rfl⟩ := hG
  exact ⟨(r, w, c), (r', w', c'), rfl, he, he', hc, hc'⟩

theorem block_commute {u v : Seq} {i j : ℤ} (hi : 0 < i) (hj : 0 < j) (f : Equiv.Perm Str)
    (La Lb Lc : List Label) (hF : Forest (La ++ Lb ++ Lc)) (hG : Good f [(.y u, i), (.y v, j)] Lb) :
    False := by
  obtain ⟨l₁, l₂, rfl, he, he', -, -⟩ := good_pair hG
  refine (forest_pair hF).2 ⟨?_, ?_⟩
  · cases h : l₁.2.2
    · rw [h] at he; simp at he; omega
    · rfl
  · cases h : l₂.2.2
    · rw [h] at he'; simp at he'; omega
    · rfl

theorem block_same {t : Seq} {i j : ℤ} (f : Equiv.Perm Str)
    (La Lb Lc : List Label) (hF : Forest (La ++ Lb ++ Lc)) (hG : Good f [(.y t, i), (.y t, j)] Lb) :
    False := by
  obtain ⟨l₁, l₂, rfl, -, -, hc, hc'⟩ := good_pair hG
  exact (forest_pair hF).1 (region_eq_of_same hc hc')

theorem block_split_y {t : Seq} {i j : ℤ} (hij : 0 < i * j)
    (f : Equiv.Perm Str) (Lb : List Label) (hG : Good f [(.y t, i + j)] Lb) : False := by
  simp only [good_y', good_nil'] at hG
  obtain ⟨r, w, c, L', rfl, he, -, rfl⟩ := hG
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos hij with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    cases c <;> simp at he <;> omega

theorem block_x_one {s : Seq} {n : ℤ} (f : Equiv.Perm Str) (Lb : List Label)
    (hG : Good f [(.x s, n)] Lb) : Lb = [] := by
  simpa only [good_x', good_nil'] using hG

theorem block_x_two (s : Seq) (i j : ℤ) (f : Equiv.Perm Str) : Good f [(.x s, i), (.x s, j)] [] := by
  simp [Good]

theorem block_x_one' (s : Seq) (n : ℤ) (f : Equiv.Perm Str) : Good f [(.x s, n)] [] := by
  simp [Good]

theorem block_x_two' {s : Seq} {i j : ℤ} (f : Equiv.Perm Str) (Lb : List Label)
    (hG : Good f [(.x s, i), (.x s, j)] Lb) : Lb = [] := by
  simpa only [good_x', good_nil'] using hG

/-! ## The invariant is preserved -/

/-- `act_posStep` on a block alone. -/
theorem act_block {B B' : Word} (h : LodhaMoorePosCommute.Step ([] ++ B ++ []) ([] ++ B' ++ [])) : act B = act B' := by
  simpa only [List.nil_append, List.append_nil] using act_posStep h

theorem frozen_posStep {V V' : Word} (hV : Frozen V) (h : LodhaMoorePosCommute.Step V V') : Frozen V' := by
  cases h with
  | moveX pre post s t t' i h =>
    exact frozen_replace hV (act_block (.moveX [] [] s t t' i h))
      fun f La Lb Lc hF hG => ⟨Lb, hF, block_moveX h f Lb hG⟩
  | moveXInv pre post s t t' i h =>
    exact frozen_replace hV (act_block (.moveXInv [] [] s t t' i h))
      fun f La Lb Lc hF hG => ⟨Lb, hF, block_moveXInv h f Lb hG⟩
  | expand pre post s =>
    exact frozen_replace hV (act_block (.expand [] [] s))
      fun f La Lb Lc hF hG => block_expand s f La Lb Lc hF hG
  | expandInv pre post s =>
    exact frozen_replace hV (act_block (.expandInv [] [] s))
      fun f La Lb Lc hF hG => block_expandInv s f La Lb Lc hF hG
  | commute pre post u v i j hi hj h =>
    exact frozen_replace hV (act_block (.commute [] [] u v i j hi hj h))
      fun f La Lb Lc hF hG => (block_commute hi hj f La Lb Lc hF hG).elim
  | split pre post g i j hi hj hij =>
    refine frozen_replace hV (act_block (.split [] [] g i j hi hj hij)) ?_
    intro f La Lb Lc hF hG
    cases g with
    | x s =>
      obtain rfl := block_x_one f Lb hG
      exact ⟨[], hF, block_x_two s i j f⟩
    | y t => exact (block_split_y hij f Lb hG).elim
  | merge pre post g i j hi hj hij =>
    refine frozen_replace hV (act_block (.merge [] [] g i j hi hj hij)) ?_
    intro f La Lb Lc hF hG
    cases g with
    | x s =>
      obtain rfl := block_x_two' f Lb hG
      exact ⟨[], hF, block_x_one' s (i + j) f⟩
    | y t => exact (block_same f La Lb Lc hF hG).elim
  | cancel pre post s i hi =>
    have := frozen_replace (B' := []) hV (act_block (.cancel [] [] s i hi))
      fun f La Lb Lc hF hG => (block_same f La Lb Lc hF hG).elim
    simpa only [List.append_nil] using this
end PartG

alias frozen_posStep := PartG.frozen_posStep

namespace PartF
open LodhaMoore LM56
theorem mem_cone_iff {ξ : Str} {p : Seq} :
    ξ ∈ cone p ↔ ∀ i (h : i < p.length), ξ.get i = p[i] := by
  constructor
  · rintro ⟨η, rfl⟩ i h
    exact Stream'.get_append_left i p η h
  · intro h
    refine ⟨ξ.drop p.length, ?_⟩
    funext n
    show (p ++ₛ ξ.drop p.length).get n = ξ.get n
    by_cases hn : n < p.length
    · rw [Stream'.get_append_left n p _ hn, h n hn]
    · obtain ⟨m, rfl⟩ : ∃ m, n = p.length + m := ⟨n - p.length, by omega⟩
      rw [Stream'.get_append_right, Stream'.get_drop]

theorem append_mem_cone (p : Seq) (η : Str) : p ++ₛ η ∈ cone p := ⟨η, rfl⟩

theorem cone_nil : cone [] = Set.univ := by
  ext ξ
  simp [mem_cone_iff]

theorem cone_mono {p q : Seq} (h : p <+: q) : cone q ⊆ cone p := by
  obtain ⟨r, rfl⟩ := h
  rintro _ ⟨η, rfl⟩
  exact ⟨r ++ₛ η, (Stream'.append_append_stream p r η).symm⟩

theorem append_mem_cone_append {ρ : Str} {p : Seq} (w : Seq) (h : ρ ∈ cone p) :
    w ++ₛ ρ ∈ cone (w ++ p) := by
  obtain ⟨η, rfl⟩ := h
  exact ⟨η, (Stream'.append_append_stream w p η)⟩

theorem prefix_of_mem_cone {ξ : Str} {p q : Seq} (hp : ξ ∈ cone p) (hq : ξ ∈ cone q)
    (hl : p.length ≤ q.length) : p <+: q := by
  rw [mem_cone_iff] at hp hq
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    rw [List.getElem_take, ← hp i h1, hq i (by omega)]

theorem compat_of_mem_cone {ξ : Str} {p q : Seq} (hp : ξ ∈ cone p) (hq : ξ ∈ cone q) :
    p <+: q ∨ q <+: p := by
  rcases le_total p.length q.length with h | h
  · exact Or.inl (prefix_of_mem_cone hp hq h)
  · exact Or.inr (prefix_of_mem_cone hq hp h)

theorem not_incompatible_of_mem_cone {ξ : Str} {p q : Seq} (hp : ξ ∈ cone p)
    (hq : ξ ∈ cone q) : ¬ Incompatible p q := by
  rintro ⟨h1, h2⟩
  rcases compat_of_mem_cone hp hq with h | h
  · exact h1 h
  · exact h2 h

/-- `q η ∈ [p]` for `|p| ≤ |q|` iff `p` is a prefix of `q`. -/
theorem append_mem_cone_iff {p q : Seq} (η : Str) (hl : p.length ≤ q.length) :
    q ++ₛ η ∈ cone p ↔ p <+: q :=
  ⟨fun h => prefix_of_mem_cone h (append_mem_cone q η) hl,
    fun h => cone_mono h (append_mem_cone q η)⟩

theorem append_left_cancel {p : Seq} {α β : Str} (h : p ++ₛ α = p ++ₛ β) : α = β := by
  funext n
  have := congrArg (fun s : Str => s.get (p.length + n)) h
  simp only [Stream'.get_append_right] at this
  exact this

theorem image_append_cone (p w : Seq) : (fun η => p ++ₛ η) '' cone w = cone (p ++ w) := by
  ext ξ
  constructor
  · rintro ⟨_, ⟨η, rfl⟩, rfl⟩
    exact ⟨η, Stream'.append_append_stream p w η⟩
  · rintro ⟨η, rfl⟩
    exact ⟨w ++ₛ η, ⟨η, rfl⟩, (Stream'.append_append_stream p w η).symm⟩

theorem eq_nil_of_cone_eq_univ {p : Seq} (h : cone p = Set.univ) : p = [] := by
  cases p with
  | nil => rfl
  | cons a p =>
    have hm : ([!a] ++ₛ Stream'.const false) ∈ cone (a :: p) := h ▸ Set.mem_univ _
    rw [mem_cone_iff] at hm
    have := hm 0 (by simp)
    rw [Stream'.get_append_left 0 [!a] _ (by simp)] at this
    cases a <;> simp at this

/-- The non-cone lemma (NC): a set containing `q a α` and `q (¬a) β` but not some `q γ` is not a
cone. -/
theorem ne_cone {S : Set Str} {q : Seq} {a : Bool} {α β γ : Str}
    (h1 : q ++ₛ Stream'.cons a α ∈ S) (h2 : q ++ₛ Stream'.cons (!a) β ∈ S) (h3 : q ++ₛ γ ∉ S)
    (p : Seq) : S ≠ cone p := by
  rintro rfl
  rw [mem_cone_iff] at h1 h2
  apply h3
  rw [mem_cone_iff]
  by_cases hl : q.length < p.length
  · exfalso
    have e1 := h1 (q.length + 0) (by omega)
    have e2 := h2 (q.length + 0) (by omega)
    rw [Stream'.get_append_right, Stream'.get_zero_cons] at e1 e2
    rw [← e1] at e2
    cases a <;> simp at e2
  · intro i hi
    rw [Stream'.get_append_left i q _ (by omega), ← h1 i hi, Stream'.get_append_left i q _ (by omega)]

/-! ## 2. `W0` is a standard form -/

theorem isStandardForm_W0 : IsStandardForm W0 := by
  refine ⟨?_, ⟨[], W0, rfl, ?_, ?_⟩, ?_⟩
  · simp [IsWord, W0]
  · simp [IsXWord, IsWord]
  · refine ⟨by simp [IsWord, W0], ?_⟩
    simp [W0]
  · intro i j hi hj s t m n h1 h2 hp
    simp only [W0, List.length_cons, List.length_nil] at hi hj
    interval_cases i <;> interval_cases j <;>
      first
      | omega
      | (simp only [W0, List.getElem_cons_zero, List.getElem_cons_succ, Prod.mk.injEq,
            Gen.y.injEq] at h1 h2
         obtain ⟨rfl, -⟩ := h1
         obtain ⟨rfl, -⟩ := h2
         exact absurd hp (by decide))

/-! ## 3. The advance lemma (ADV) -/

end PartF

alias isStandardForm_W0 := PartF.isStandardForm_W0

namespace PartF
open LodhaMoore LM56
/-- `(w η).y^σ = o (η.y^c)` for some output `o`. -/
def ADV (σ : Bool) (w : Seq) (c : Bool) : Prop :=
  ∃ o : Seq, ∀ η, yFun σ (w ++ₛ η) = o ++ₛ yFun c η

theorem adv_nil (σ : Bool) : ADV σ [] σ := ⟨[], fun η => by simp⟩

theorem adv_pos {σ : Bool} {w : Seq} (h : ADV σ w true) :
    ADV σ (w ++ [false, false]) true ∧ ADV σ (w ++ [false, true]) false ∧
      ADV σ (w ++ [true]) true := by
  obtain ⟨o, ho⟩ := h
  refine ⟨⟨o ++ [false], fun η => ?_⟩, ⟨o ++ [true, false], fun η => ?_⟩,
    ⟨o ++ [true, true], fun η => ?_⟩⟩
  · rw [Stream'.append_append_stream, ho, yFun_true_00, Stream'.append_append_stream]
  · rw [Stream'.append_append_stream, ho, yFun_true_01, Stream'.append_append_stream]
  · rw [Stream'.append_append_stream, ho, yFun_true_1, Stream'.append_append_stream]

theorem adv_neg {σ : Bool} {w : Seq} (h : ADV σ w false) :
    ADV σ (w ++ [false]) false ∧ ADV σ (w ++ [true, false]) true ∧
      ADV σ (w ++ [true, true]) false := by
  obtain ⟨o, ho⟩ := h
  refine ⟨⟨o ++ [false, false], fun η => ?_⟩, ⟨o ++ [false, true], fun η => ?_⟩,
    ⟨o ++ [true], fun η => ?_⟩⟩
  · rw [Stream'.append_append_stream, ho, yFun_false_0, Stream'.append_append_stream]
  · rw [Stream'.append_append_stream, ho, yFun_false_10, Stream'.append_append_stream]
  · rw [Stream'.append_append_stream, ho, yFun_false_11, Stream'.append_append_stream]

/-! ## 4. The forest invariant -/

/-- The block order of the roots. -/
def rank : Root → ℕ
  | .A => 0
  | .B => 1
  | .C => 2
  | .D => 3

/-- The shape of a `D`-leaf: the root (positive), or a leaf of the `00`, `01` or `1` subtree, with
the advance lemma for the `00` subtree. -/
def DShape (w : Seq) (c : Bool) : Prop :=
  (w = [] ∧ c = true) ∨ (∃ w', w = [false, false] ++ w' ∧ ADV true w' c) ∨
    (∃ w', w = [false, true] ++ w') ∨ (∃ w', w = [true] ++ w')

theorem dShape_pos {w : Seq} (h : DShape w true) :
    DShape (w ++ [false, false]) true ∧ DShape (w ++ [false, true]) false ∧
      DShape (w ++ [true]) true := by
  rcases h with ⟨rfl, -⟩ | ⟨w', rfl, hw⟩ | ⟨w', rfl⟩ | ⟨w', rfl⟩
  · exact ⟨Or.inr (Or.inl ⟨[], rfl, adv_nil true⟩), Or.inr (Or.inr (Or.inl ⟨[], rfl⟩)),
      Or.inr (Or.inr (Or.inr ⟨[], rfl⟩))⟩
  · obtain ⟨h1, h2, h3⟩ := adv_pos hw
    exact ⟨Or.inr (Or.inl ⟨_, List.append_assoc _ _ _, h1⟩),
      Or.inr (Or.inl ⟨_, List.append_assoc _ _ _, h2⟩),
      Or.inr (Or.inl ⟨_, List.append_assoc _ _ _, h3⟩)⟩
  · exact ⟨Or.inr (Or.inr (Or.inl ⟨_, List.append_assoc _ _ _⟩)),
      Or.inr (Or.inr (Or.inl ⟨_, List.append_assoc _ _ _⟩)),
      Or.inr (Or.inr (Or.inl ⟨_, List.append_assoc _ _ _⟩))⟩
  · exact ⟨Or.inr (Or.inr (Or.inr ⟨_, List.append_assoc _ _ _⟩)),
      Or.inr (Or.inr (Or.inr ⟨_, List.append_assoc _ _ _⟩)),
      Or.inr (Or.inr (Or.inr ⟨_, List.append_assoc _ _ _⟩))⟩

theorem dShape_neg {w : Seq} (h : DShape w false) :
    DShape (w ++ [false]) false ∧ DShape (w ++ [true, false]) true ∧
      DShape (w ++ [true, true]) false := by
  rcases h with ⟨-, h⟩ | ⟨w', rfl, hw⟩ | ⟨w', rfl⟩ | ⟨w', rfl⟩
  · exact absurd h (by decide)
  · obtain ⟨h1, h2, h3⟩ := adv_neg hw
    exact ⟨Or.inr (Or.inl ⟨_, List.append_assoc _ _ _, h1⟩),
      Or.inr (Or.inl ⟨_, List.append_assoc _ _ _, h2⟩),
      Or.inr (Or.inl ⟨_, List.append_assoc _ _ _, h3⟩)⟩
  · exact ⟨Or.inr (Or.inr (Or.inl ⟨_, List.append_assoc _ _ _⟩)),
      Or.inr (Or.inr (Or.inl ⟨_, List.append_assoc _ _ _⟩)),
      Or.inr (Or.inr (Or.inl ⟨_, List.append_assoc _ _ _⟩))⟩
  · exact ⟨Or.inr (Or.inr (Or.inr ⟨_, List.append_assoc _ _ _⟩)),
      Or.inr (Or.inr (Or.inr ⟨_, List.append_assoc _ _ _⟩)),
      Or.inr (Or.inr (Or.inr ⟨_, List.append_assoc _ _ _⟩))⟩

/-- The facts about `Forest` used here: D-leaf shapes, each tree's leaves cover every sequence,
and the roots come in the order `A, B, C, D`. -/
structure Inv (L : List Label) : Prop where
  shape : ∀ l ∈ L, l.1 = .D → DShape l.2.1 l.2.2
  cover : ∀ (r : Root) (η : Str), ∃ l ∈ L, l.1 = r ∧ η ∈ cone l.2.1
  order : L.Pairwise (fun a b => rank a.1 ≤ rank b.1)

theorem eq_append_two (ρ : Str) : ∃ a b ρ', ρ = [a, b] ++ₛ ρ' :=
  ⟨_, _, _, (Stream'.append_take_drop 2 ρ).symm⟩

theorem cone_cases_pos (ρ : Str) :
    ρ ∈ cone [false, false] ∨ ρ ∈ cone [false, true] ∨ ρ ∈ cone [true] := by
  obtain ⟨a, b, ρ', rfl⟩ := eq_append_two ρ
  cases a <;> cases b
  · exact Or.inl ⟨ρ', rfl⟩
  · exact Or.inr (Or.inl ⟨ρ', rfl⟩)
  · exact Or.inr (Or.inr ⟨[false] ++ₛ ρ', rfl⟩)
  · exact Or.inr (Or.inr ⟨[true] ++ₛ ρ', rfl⟩)

theorem cone_cases_neg (ρ : Str) :
    ρ ∈ cone [false] ∨ ρ ∈ cone [true, false] ∨ ρ ∈ cone [true, true] := by
  obtain ⟨a, b, ρ', rfl⟩ := eq_append_two ρ
  cases a <;> cases b
  · exact Or.inl ⟨[false] ++ₛ ρ', rfl⟩
  · exact Or.inl ⟨[true] ++ₛ ρ', rfl⟩
  · exact Or.inr (Or.inl ⟨ρ', rfl⟩)
  · exact Or.inr (Or.inr ⟨ρ', rfl⟩)

theorem pairwise_replace {L₁ L₂ M : List Label} {a : Label}
    (h : (L₁ ++ [a] ++ L₂).Pairwise (fun a b => rank a.1 ≤ rank b.1))
    (hM : ∀ b ∈ M, b.1 = a.1) :
    (L₁ ++ M ++ L₂).Pairwise (fun a b => rank a.1 ≤ rank b.1) := by
  rw [List.pairwise_append, List.pairwise_append] at h ⊢
  obtain ⟨⟨h1, -, h3⟩, h4, h5⟩ := h
  refine ⟨⟨h1, ?_, ?_⟩, h4, ?_⟩
  · exact List.pairwise_of_forall_mem_list (fun x hx y hy => by rw [hM x hx, hM y hy])
  · intro x hx y hy
    rw [hM y hy]
    exact h3 x hx a (List.mem_singleton_self a)
  · intro x hx y hy
    rcases List.mem_append.1 hx with hx | hx
    · exact h5 x (List.mem_append_left _ hx) y hy
    · rw [hM x hx]
      exact h5 a (List.mem_append_right _ (List.mem_singleton_self a)) y hy

theorem inv_of_forest {L : List Label} (hF : Forest L) : Inv L := by
  induction hF with
  | init =>
    refine ⟨?_, ?_, ?_⟩
    · intro l hl hD
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl <;> simp_all [DShape]
    · intro r η
      cases r
      · exact ⟨(.A, [], false), by simp, rfl, by simp [cone_nil]⟩
      · exact ⟨(.B, [], false), by simp, rfl, by simp [cone_nil]⟩
      · exact ⟨(.C, [], false), by simp, rfl, by simp [cone_nil]⟩
      · exact ⟨(.D, [], true), by simp, rfl, by simp [cone_nil]⟩
    · decide
  | expandPos L₁ L₂ r w _ ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro l hl hD
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with (hl | rfl | rfl | rfl) | hl
      · exact ih.shape l (by simp [hl]) hD
      · exact (dShape_pos (ih.shape (r, w, true) (by simp) hD)).1
      · exact (dShape_pos (ih.shape (r, w, true) (by simp) hD)).2.1
      · exact (dShape_pos (ih.shape (r, w, true) (by simp) hD)).2.2
      · exact ih.shape l (by simp [hl]) hD
    · intro r' η
      obtain ⟨l, hl, hr, hη⟩ := ih.cover r' η
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with (hl | rfl) | hl
      · exact ⟨l, by simp [hl], hr, hη⟩
      · obtain ⟨ρ, rfl⟩ := hη
        rcases cone_cases_pos ρ with h | h | h
        · exact ⟨(r, w ++ [false, false], true), by simp, hr, append_mem_cone_append w h⟩
        · exact ⟨(r, w ++ [false, true], false), by simp, hr, append_mem_cone_append w h⟩
        · exact ⟨(r, w ++ [true], true), by simp, hr, append_mem_cone_append w h⟩
      · exact ⟨l, by simp [hl], hr, hη⟩
    · exact pairwise_replace ih.order (by simp)
  | expandNeg L₁ L₂ r w _ ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro l hl hD
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with (hl | rfl | rfl | rfl) | hl
      · exact ih.shape l (by simp [hl]) hD
      · exact (dShape_neg (ih.shape (r, w, false) (by simp) hD)).1
      · exact (dShape_neg (ih.shape (r, w, false) (by simp) hD)).2.1
      · exact (dShape_neg (ih.shape (r, w, false) (by simp) hD)).2.2
      · exact ih.shape l (by simp [hl]) hD
    · intro r' η
      obtain ⟨l, hl, hr, hη⟩ := ih.cover r' η
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with (hl | rfl) | hl
      · exact ⟨l, by simp [hl], hr, hη⟩
      · obtain ⟨ρ, rfl⟩ := hη
        rcases cone_cases_neg ρ with h | h | h
        · exact ⟨(r, w ++ [false], false), by simp, hr, append_mem_cone_append w h⟩
        · exact ⟨(r, w ++ [true, false], true), by simp, hr, append_mem_cone_append w h⟩
        · exact ⟨(r, w ++ [true, true], false), by simp, hr, append_mem_cone_append w h⟩
      · exact ⟨l, by simp [hl], hr, hη⟩
    · exact pairwise_replace ih.order (by simp)

/-! ## 5. Regions of labels -/

theorem psi_D_eq : psi .D = ⇑(act (W0.take 3)).symm := rfl

theorem psi_D_injective : Function.Injective (psi .D) := by
  rw [psi_D_eq]; exact Equiv.injective _

theorem psi_D_surjective : Function.Surjective (psi .D) := by
  rw [psi_D_eq]; exact Equiv.surjective _

theorem region_D_nil (c : Bool) : region (.D, [], c) = Set.univ := by
  show psi .D '' cone [] = Set.univ
  rw [cone_nil, Set.image_univ, psi_D_surjective.range_eq]

theorem psi_D_00_append {w : Seq} (v : Seq) (η : Str) :
    psi .D (([false, false] ++ w ++ v) ++ₛ η) = [false, false] ++ₛ yFun true (w ++ₛ (v ++ₛ η)) := by
  rw [Stream'.append_append_stream, Stream'.append_append_stream, psi_D_00]

theorem yFun_inv (c : Bool) (ζ : Str) : yFun c (yFun (!c) ζ) = ζ := by
  cases c
  · exact yFun_false_true ζ
  · exact yFun_true_false ζ

/-- Every region is everything, or lies in `[00]`, `[01]` or `[1]`. -/
theorem region_cls1 {L : List Label} (hI : Inv L) {l : Label} (hl : l ∈ L) :
    region l = Set.univ ∨ region l ⊆ cone [false, false] ∨ region l ⊆ cone [false, true] ∨
      region l ⊆ cone [true] := by
  obtain ⟨r, w, c⟩ := l
  cases r with
  | A => exact Or.inr (Or.inl (by rintro _ ⟨x, -, rfl⟩; exact append_mem_cone _ _))
  | B => exact Or.inr (Or.inr (Or.inl (by rintro _ ⟨x, -, rfl⟩; exact append_mem_cone _ _)))
  | C => exact Or.inr (Or.inr (Or.inr (by rintro _ ⟨x, -, rfl⟩; exact append_mem_cone _ _)))
  | D =>
    rcases hI.shape _ hl rfl with ⟨h, -⟩ | ⟨w', h, -⟩ | ⟨w', h⟩ | ⟨w', h⟩ <;>
      simp only at h <;> subst h
    · exact Or.inl (region_D_nil c)
    · refine Or.inr (Or.inl ?_)
      rintro _ ⟨_, ⟨η, rfl⟩, rfl⟩
      show psi .D (([false, false] ++ w') ++ₛ η) ∈ _
      rw [Stream'.append_append_stream, psi_D_00]
      exact append_mem_cone _ _
    · refine Or.inr (Or.inr (Or.inl ?_))
      rintro _ ⟨_, ⟨η, rfl⟩, rfl⟩
      show psi .D (([false, true] ++ w') ++ₛ η) ∈ _
      rw [Stream'.append_append_stream, psi_D_01]
      exact append_mem_cone _ _
    · refine Or.inr (Or.inr (Or.inr ?_))
      rintro _ ⟨_, ⟨η, rfl⟩, rfl⟩
      show psi .D (([true] ++ w') ++ₛ η) ∈ _
      rw [Stream'.append_append_stream, psi_D_1]
      exact append_mem_cone _ _

/-- Every region is a cone, or lies in `[01]` or `[1]`. -/
theorem region_cls2 {L : List Label} (hI : Inv L) {l : Label} (hl : l ∈ L) :
    (∃ p, region l = cone p) ∨ region l ⊆ cone [false, true] ∨ region l ⊆ cone [true] := by
  obtain ⟨r, w, c⟩ := l
  cases r with
  | A => exact Or.inl ⟨_, image_append_cone [false, false] w⟩
  | B => exact Or.inr (Or.inl (by rintro _ ⟨x, -, rfl⟩; exact append_mem_cone _ _))
  | C => exact Or.inr (Or.inr (by rintro _ ⟨x, -, rfl⟩; exact append_mem_cone _ _))
  | D =>
    rcases hI.shape _ hl rfl with ⟨h, -⟩ | ⟨w', h, hadv⟩ | ⟨w', h⟩ | ⟨w', h⟩ <;>
      simp only at h <;> subst h
    · exact Or.inl ⟨[], (region_D_nil c).trans cone_nil.symm⟩
    · obtain ⟨o, ho⟩ := hadv
      refine Or.inl ⟨[false, false] ++ o, ?_⟩
      ext ξ
      constructor
      · rintro ⟨_, ⟨η, rfl⟩, rfl⟩
        show psi .D (([false, false] ++ w') ++ₛ η) ∈ _
        rw [Stream'.append_append_stream, psi_D_00, ho, ← Stream'.append_append_stream]
        exact append_mem_cone _ _
      · rintro ⟨ζ, rfl⟩
        refine ⟨([false, false] ++ w') ++ₛ yFun (!c) ζ, ⟨_, rfl⟩, ?_⟩
        show psi .D (([false, false] ++ w') ++ₛ yFun (!c) ζ) = _
        rw [Stream'.append_append_stream, psi_D_00, ho, yFun_inv,
          ← Stream'.append_append_stream]
    · refine Or.inr (Or.inl ?_)
      rintro _ ⟨_, ⟨η, rfl⟩, rfl⟩
      show psi .D (([false, true] ++ w') ++ₛ η) ∈ _
      rw [Stream'.append_append_stream, psi_D_01]
      exact append_mem_cone _ _
    · refine Or.inr (Or.inr ?_)
      rintro _ ⟨_, ⟨η, rfl⟩, rfl⟩
      show psi .D (([true] ++ w') ++ₛ η) ∈ _
      rw [Stream'.append_append_stream, psi_D_1]
      exact append_mem_cone _ _

theorem region_D_00_sub {w : Seq} {c : Bool} :
    region (.D, [false, false] ++ w, c) ⊆ cone [false, false] := by
  rintro _ ⟨_, ⟨η, rfl⟩, rfl⟩
  show psi .D (([false, false] ++ w) ++ₛ η) ∈ _
  rw [Stream'.append_append_stream, psi_D_00]
  exact append_mem_cone _ _

theorem cover_root {L : List Label} (hI : Inv L) (r : Root) (ρ : Str) :
    ∃ k, ∃ hk : k < L.length, L[k].1 = r ∧ psi r ρ ∈ region L[k] := by
  obtain ⟨l, hl, hr, hρ⟩ := hI.cover r ρ
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hl
  exact ⟨k, hk, hr, ρ, hρ, by rw [hr]⟩

/-- The A-regions cover `[00]`. -/
theorem a_cover {L : List Label} (hI : Inv L) {ξ : Str} (hξ : ξ ∈ cone [false, false]) :
    ∃ k, ∃ hk : k < L.length, L[k].1 = .A ∧ ξ ∈ region L[k] := by
  obtain ⟨ρ, rfl⟩ := hξ
  exact cover_root hI .A ρ

/-- The A-, B- and C-regions cover everything. -/
theorem abc_cover {L : List Label} (hI : Inv L) (ξ : Str) :
    ∃ k, ∃ hk : k < L.length, L[k].1 ≠ .D ∧ ξ ∈ region L[k] := by
  rcases cone_cases_pos ξ with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · obtain ⟨k, hk, h1, h2⟩ := cover_root hI .A ρ
    exact ⟨k, hk, by rw [h1]; decide, h2⟩
  · obtain ⟨k, hk, h1, h2⟩ := cover_root hI .B ρ
    exact ⟨k, hk, by rw [h1]; decide, h2⟩
  · obtain ⟨k, hk, h1, h2⟩ := cover_root hI .C ρ
    exact ⟨k, hk, by rw [h1]; decide, h2⟩

/-- A-labels come before D-labels. -/
theorem lt_of_A_D {L : List Label} (hI : Inv L) {i j : ℕ} (hi : i < L.length) (hj : j < L.length)
    (hA : L[i].1 = .A) (hD : L[j].1 = .D) : i < j := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact h
  · rw [hA] at hD; exact absurd hD (by decide)
  · have := List.pairwise_iff_getElem.1 hI.order j i hj hi h
    rw [hA, hD] at this
    simp [rank] at this

/-! ## 6. Reading `Good` along a standard form -/

/-- The subscript of a generator. -/
def gsub : Gen → Seq
  | .x s => s
  | .y s => s

theorem good_xword_append : ∀ {Ξ : Word}, (∀ p ∈ Ξ, ∃ s, p.1 = .x s) →
    ∀ (f : Equiv.Perm Str) (Υ : Word) (L : List Label),
      Good f (Ξ ++ Υ) L ↔ Good (act Ξ * f) Υ L
  | [], _, f, Υ, L => by simp [act]
  | (g0, n) :: Ξ, hX, f, Υ, L => by
    obtain ⟨s, hs⟩ := hX (g0, n) List.mem_cons_self
    simp only at hs
    subst hs
    rw [List.cons_append]
    show Good (genP (.x s) ^ n * f) (Ξ ++ Υ) L ↔ _
    rw [good_xword_append (fun p hp => hX p (List.mem_cons_of_mem _ hp))]
    simp only [act, mul_assoc]

theorem good_yword : ∀ {g : Equiv.Perm Str} {Υ : Word} {L : List Label},
    (∀ p ∈ Υ, ∃ s, p.1 = .y s) → Good g Υ L →
    L.length = Υ.length ∧ ∀ k (hk : k < L.length), ∃ t,
      Υ[k]? = some (.y t, if L[k].2.2 then 1 else -1) ∧
      ∀ η, (act (Υ.take k) * g) (psi L[k].1 (L[k].2.1 ++ₛ η)) = t ++ₛ η
  | g, [], L, _, h => by
    have : L = [] := h
    subst this
    simp
  | g, (g0, e) :: Υ, L, hY, h => by
    obtain ⟨s, hs⟩ := hY (g0, e) List.mem_cons_self
    simp only at hs
    subst hs
    match L, h with
    | [], h => exact h.elim
    | (r, w, c) :: L', h =>
      obtain ⟨he, hc, h'⟩ := h
      obtain ⟨hlen, hk⟩ := good_yword (fun p hp => hY p (List.mem_cons_of_mem _ hp)) h'
      refine ⟨by simp [hlen], ?_⟩
      intro k hk'
      cases k with
      | zero =>
        refine ⟨s, by simp [he], fun η => ?_⟩
        simpa [act] using hc η
      | succ k =>
        obtain ⟨t, ht1, ht2⟩ := hk k (by simpa using hk')
        refine ⟨t, by simpa using ht1, fun η => ?_⟩
        rw [List.take_succ_cons, act, mul_assoc]
        exact ht2 η

/-- `y_s^m` preserves `[u]` when `s` is not a proper prefix of `u`. -/
theorem genP_y_zpow_mem_cone_iff {s u : Seq} (h : ¬ s <+: u ∨ s = u) (m : ℤ) (ξ : Str) :
    (genP (.y s) ^ m) ξ ∈ cone u ↔ ξ ∈ cone u := by
  rcases h with h | rfl
  · by_cases hξ : ξ ∈ cone s
    · have h2 := (genP_y_zpow_mem_iff s m ξ).2 hξ
      have key : ∀ ζ ∈ cone s, ζ ∈ cone u ↔ u <+: s := fun ζ hζ =>
        ⟨fun hu => (compat_of_mem_cone hu hζ).resolve_right h, fun hus => cone_mono hus hζ⟩
      rw [key _ h2, key _ hξ]
    · rw [genP_y_zpow_of_not_mem s m ξ hξ]
  · exact genP_y_zpow_mem_iff s m ξ

theorem act_mem_cone_iff {u : Seq} : ∀ {P : Word},
    (∀ p ∈ P, ∃ s, p.1 = .y s ∧ (¬ s <+: u ∨ s = u)) → ∀ ξ, act P ξ ∈ cone u ↔ ξ ∈ cone u
  | [], _, ξ => by simp [act]
  | (g0, m) :: P, hP, ξ => by
    obtain ⟨s, hs, hsu⟩ := hP (g0, m) List.mem_cons_self
    simp only at hs
    subst hs
    rw [act, Equiv.Perm.mul_apply, act_mem_cone_iff (fun p hp => hP p (List.mem_cons_of_mem _ hp)),
      genP_y_zpow_mem_cone_iff hsu]

/-- From the chart and the support fact: the image of `[w u]` is `g⁻¹[t u]`. -/
theorem image_eq_preimage {f g : Equiv.Perm Str} {r : Root} {w t : Seq}
    (hchart : ∀ η, f (psi r (w ++ₛ η)) = t ++ₛ η) (u : Seq)
    (hfg : ∀ ξ, f ξ ∈ cone (t ++ u) ↔ g ξ ∈ cone (t ++ u)) :
    psi r '' cone (w ++ u) = g ⁻¹' cone (t ++ u) := by
  ext ξ
  rw [Set.mem_preimage, ← hfg]
  constructor
  · rintro ⟨_, ⟨η, rfl⟩, rfl⟩
    refine ⟨η, ?_⟩
    show (t ++ u) ++ₛ η = f (psi r ((w ++ u) ++ₛ η))
    rw [Stream'.append_append_stream, Stream'.append_append_stream, hchart]
  · rintro ⟨η, hη⟩
    refine ⟨(w ++ u) ++ₛ η, ⟨η, rfl⟩, f.injective ?_⟩
    rw [Stream'.append_append_stream, hchart, ← Stream'.append_append_stream]
    exact hη

/-! ## 7. The non-cone lemma for a twisted set -/

theorem cons_inj {a b : Bool} {α β : Str} (h : Stream'.cons a α = Stream'.cons b β) :
    a = b ∧ α = β :=
  ⟨by simpa using congrArg Stream'.head h, by simpa using congrArg Stream'.tail h⟩

/-- `{q (([¬c] η).y^c)}` is not a cone: (NC) of RESULT.md, after the prefix `q`. -/
theorem twist_ne_cone (q : Seq) (c : Bool) (S : Set Str)
    (hS : ∀ ξ, ξ ∈ S ↔ ∃ η, ξ = q ++ₛ yFun c (Stream'.cons (!c) η)) (p : Seq) : S ≠ cone p := by
  let z := Stream'.const false
  cases c
  · -- `[1].y⁻¹ = [01] ∪ [1]`
    refine ne_cone (q := q) (a := false) (α := Stream'.cons true (yFun true z)) (β := yFun false z)
      (γ := Stream'.cons false (Stream'.cons false z)) ?_ ?_ ?_ p
    · exact (hS _).2 ⟨Stream'.cons false z, congrArg (q ++ₛ ·) (yFun_false_10 z).symm⟩
    · exact (hS _).2 ⟨Stream'.cons true z, congrArg (q ++ₛ ·) (yFun_false_11 z).symm⟩
    · rw [hS]
      rintro ⟨η, hη⟩
      have h := append_left_cancel hη
      obtain ⟨b, η', rfl⟩ : ∃ b η', η = Stream'.cons b η' := ⟨_, _, (Stream'.eta η).symm⟩
      cases b
      · have h2 := yFun_false_10 η'
        simp only [Stream'.cons_append_stream, Stream'.nil_append_stream] at h2
        rw [Bool.not_false, h2] at h
        exact absurd (cons_inj (cons_inj h).2).1 (by decide)
      · have h2 := yFun_false_11 η'
        simp only [Stream'.cons_append_stream, Stream'.nil_append_stream] at h2
        rw [Bool.not_false, h2] at h
        exact absurd (cons_inj h).1 (by decide)
  · -- `[0].y = [0] ∪ [10]`
    refine ne_cone (q := q) (a := false) (α := yFun true z) (β := Stream'.cons false (yFun false z))
      (γ := Stream'.cons true (Stream'.cons true z)) ?_ ?_ ?_ p
    · exact (hS _).2 ⟨Stream'.cons false z, congrArg (q ++ₛ ·) (yFun_true_00 z).symm⟩
    · exact (hS _).2 ⟨Stream'.cons true z, congrArg (q ++ₛ ·) (yFun_true_01 z).symm⟩
    · rw [hS]
      rintro ⟨η, hη⟩
      have h := append_left_cancel hη
      obtain ⟨b, η', rfl⟩ : ∃ b η', η = Stream'.cons b η' := ⟨_, _, (Stream'.eta η).symm⟩
      cases b
      · have h2 := yFun_true_00 η'
        simp only [Stream'.cons_append_stream, Stream'.nil_append_stream] at h2
        rw [Bool.not_true, h2] at h
        exact absurd (cons_inj h).1 (by decide)
      · have h2 := yFun_true_01 η'
        simp only [Stream'.cons_append_stream, Stream'.nil_append_stream] at h2
        rw [Bool.not_true, h2] at h
        exact absurd (cons_inj (cons_inj h).2).1 (by decide)

theorem not_mem_cone_of_mem_cone {ξ : Str} {p q : Seq} (hp : ξ ∈ cone p) (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) : ξ ∉ cone q := fun hq =>
  (compat_of_mem_cone hp hq).elim hpq hqp

/-! ## 8. The two phases -/

/-- What the main proof extracts from a frozen standard form `Ξ Υ`: `g` is the value of `Ξ`,
`t k` the subscript of the `k`-th `y`-letter, `Occ`, `Pos`, `Neg` the occurrence predicates. -/
structure Setting (g : Equiv.Perm Str) (L : List Label) (t : ℕ → Seq)
    (Occ Pos Neg : Seq → Prop) : Prop where
  inv : Inv L
  reg0 : ∀ k (hk : k < L.length), region L[k] = g ⁻¹' cone (t k)
  reg1 : ∀ k (hk : k < L.length) (z : Bool),
    psi L[k].1 '' cone (L[k].2.1 ++ [z]) = g ⁻¹' cone (t k ++ [z])
  ord : ∀ i j, i < j → j < L.length → ¬ t i <+: t j
  occ : ∀ s, Occ s ↔ ∃ k, k < L.length ∧ t k = s
  pos : ∀ k (hk : k < L.length), L[k].2.2 = true → Pos (t k)
  neg : ∀ k (hk : k < L.length), L[k].2.2 = false → Neg (t k)
  se : ∀ s, Occ s → ¬ (∃ u, s <+: u ∧ ∀ t', ¬ Incompatible t' u → Occ t' → t' <+: s) →
    (Pos s → Occ (s ++ [false])) ∧ (Neg s → Occ (s ++ [true]))

theorem Setting.inj {g L t Occ Pos Neg} (H : Setting g L t Occ Pos Neg) {i j : ℕ}
    (hi : i < L.length) (hj : j < L.length) (h : t i = t j) : i = j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd (by rw [h]) (H.ord i j hij hj)
  · rfl
  · exact absurd (by rw [h]) (H.ord j i hij hi)

/-- Phase 1: the root of `D` is a leaf. -/
theorem phase1 {g L t Occ Pos Neg} (H : Setting g L t Occ Pos Neg) {kD : ℕ}
    (hkD : kD < L.length) (hL : L[kD] = (.D, [], true)) : False := by
  have htD : t kD = [] := by
    have h0 := H.reg0 kD hkD
    rw [hL, region_D_nil] at h0
    apply eq_nil_of_cone_eq_univ
    ext ξ
    simp only [Set.mem_univ, iff_true]
    have : g.symm ξ ∈ g ⁻¹' cone (t kD) := h0 ▸ Set.mem_univ _
    simpa using this
  have hne : ¬ ∃ u, [] <+: u ∧ ∀ t', ¬ Incompatible t' u → Occ t' → t' <+: [] := by
    rintro ⟨u, -, hu⟩
    obtain ⟨k, hk, hkD', hmem⟩ := abc_cover H.inv (g.symm (u ++ₛ Stream'.const false))
    rw [H.reg0 k hk] at hmem
    simp only [Set.mem_preimage, Equiv.apply_symm_apply] at hmem
    have h1 := hu (t k) (not_incompatible_of_mem_cone hmem (append_mem_cone _ _))
      ((H.occ _).2 ⟨k, hk, rfl⟩)
    have h2 : t k = t kD := by rw [htD]; exact List.prefix_nil.1 h1
    have := H.inj hk hkD h2
    subst this
    rw [hL] at hkD'
    exact hkD' rfl
  have hocc : Occ [] := (H.occ _).2 ⟨kD, hkD, htD⟩
  have hpos : Pos [] := htD ▸ H.pos kD hkD (by rw [hL])
  obtain ⟨k', hk', htk'⟩ := (H.occ _).1 ((H.se [] hocc hne).1 hpos)
  have h1 := H.reg1 kD hkD false
  rw [hL, htD] at h1
  have h2 := H.reg0 k' hk'
  rw [htk', ← h1] at h2
  simp only [List.nil_append] at h2
  -- `ψ_D([0]) = [0]` meets `[00]` and `[01]` and misses `[1]`
  have m00 : [false, false] ++ₛ yFun true (Stream'.const false) ∈ region L[k'] := by
    rw [h2]
    exact ⟨[false, false] ++ₛ Stream'.const false, ⟨[false] ++ₛ Stream'.const false, rfl⟩,
      psi_D_00 _⟩
  have m01 : [false, true] ++ₛ yFun true (Stream'.const false) ∈ region L[k'] := by
    rw [h2]
    exact ⟨[false, true] ++ₛ Stream'.const false, ⟨[true] ++ₛ Stream'.const false, rfl⟩,
      psi_D_01 _⟩
  rcases region_cls1 H.inv (List.getElem_mem hk') with h | h | h | h
  · have : psi .D ([true] ++ₛ Stream'.const false) ∈ region L[k'] := h ▸ Set.mem_univ _
    rw [h2] at this
    obtain ⟨x, hx, hxe⟩ := this
    rw [psi_D_injective hxe] at hx
    exact not_mem_cone_of_mem_cone (append_mem_cone _ _) (by decide) (by decide) hx
  · exact not_mem_cone_of_mem_cone (append_mem_cone _ _) (by decide) (by decide) (h m01)
  · exact not_mem_cone_of_mem_cone (append_mem_cone _ _) (by decide) (by decide) (h m00)
  · exact not_mem_cone_of_mem_cone (append_mem_cone _ _) (by decide) (by decide) (h m00)

/-- Phase 2: some D-leaf lies in the `00` subtree. -/
theorem phase2 {g L t Occ Pos Neg} (H : Setting g L t Occ Pos Neg) {kD : ℕ}
    (hkD : kD < L.length) {w : Seq} {c : Bool} (hL : L[kD] = (.D, [false, false] ++ w, c))
    (hadv : ADV true w c) : False := by
  have h0 := H.reg0 kD hkD
  rw [hL] at h0
  -- the subscript of `d` is not exposed: the A-letters cover its support
  have hne : ¬ ∃ u, t kD <+: u ∧ ∀ t', ¬ Incompatible t' u → Occ t' → t' <+: t kD := by
    rintro ⟨u, hu1, hu⟩
    have hgξ : g (g.symm (u ++ₛ Stream'.const false)) ∈ cone u := by
      rw [Equiv.apply_symm_apply]; exact append_mem_cone _ _
    have hξD : g.symm (u ++ₛ Stream'.const false) ∈ region (.D, [false, false] ++ w, c) := by
      rw [h0]; exact cone_mono hu1 hgξ
    obtain ⟨ka, hka, hkaA, hmem⟩ := a_cover H.inv (region_D_00_sub hξD)
    rw [H.reg0 ka hka] at hmem
    have h1 := hu (t ka) (not_incompatible_of_mem_cone hmem hgξ) ((H.occ _).2 ⟨ka, hka, rfl⟩)
    exact H.ord ka kD (lt_of_A_D H.inv hka hkD hkaA (by rw [hL])) hkD h1
  have hocc : Occ (t kD) := (H.occ _).2 ⟨kD, hkD, rfl⟩
  have hreq : Occ (t kD ++ [!c]) := by
    obtain ⟨hP, hN⟩ := H.se _ hocc hne
    cases c
    · exact hN (H.neg kD hkD (by rw [hL]))
    · exact hP (H.pos kD hkD (by rw [hL]))
  obtain ⟨k', hk', htk'⟩ := (H.occ _).1 hreq
  have h1 := H.reg1 kD hkD (!c)
  rw [hL] at h1
  have h2 := H.reg0 k' hk'
  rw [htk', ← h1] at h2
  -- the required letter's support is `χ_d([¬c]) = 00 o ([¬c].y^c)`
  obtain ⟨o, ho⟩ := hadv
  have hS : ∀ ξ, ξ ∈ region L[k'] ↔
      ∃ η, ξ = ([false, false] ++ o) ++ₛ yFun c (Stream'.cons (!c) η) := by
    intro ξ
    rw [h2]
    constructor
    · rintro ⟨_, ⟨η, rfl⟩, rfl⟩
      refine ⟨η, ?_⟩
      show psi .D (([false, false] ++ w ++ [!c]) ++ₛ η) = _
      rw [psi_D_00_append, ho, Stream'.append_append_stream]
      rfl
    · rintro ⟨η, rfl⟩
      refine ⟨([false, false] ++ w ++ [!c]) ++ₛ η, ⟨η, rfl⟩, ?_⟩
      rw [psi_D_00_append, ho, Stream'.append_append_stream]
      rfl
  have hmem : ([false, false] ++ o) ++ₛ yFun c (Stream'.cons (!c) (Stream'.const false)) ∈
      region L[k'] := (hS _).2 ⟨_, rfl⟩
  have hmem00 : ([false, false] ++ o) ++ₛ yFun c (Stream'.cons (!c) (Stream'.const false)) ∈
      cone [false, false] := cone_mono (List.prefix_append _ _) (append_mem_cone _ _)
  rcases region_cls2 H.inv (List.getElem_mem hk') with ⟨p, hp⟩ | h | h
  · exact twist_ne_cone _ c _ hS p hp
  · exact not_mem_cone_of_mem_cone hmem00 (by decide) (by decide) (h hmem)
  · exact not_mem_cone_of_mem_cone hmem00 (by decide) (by decide) (h hmem)

theorem setting_false {g L t Occ Pos Neg} (H : Setting g L t Occ Pos Neg) : False := by
  obtain ⟨l, hl, hlD, hlη⟩ := H.inv.cover .D ([false, false] ++ₛ Stream'.const false)
  obtain ⟨kD, hkD, rfl⟩ := List.mem_iff_getElem.1 hl
  have hshape := H.inv.shape _ hl hlD
  rcases hL : L[kD] with ⟨r, w, c⟩
  rw [hL] at hshape hlη hlD
  simp only at hlD hlη hshape
  subst hlD
  rcases hshape with ⟨rfl, rfl⟩ | ⟨w', rfl, hadv⟩ | ⟨w', rfl⟩ | ⟨w', rfl⟩
  · exact phase1 H hkD hL
  · exact phase2 H hkD hL hadv
  · exact not_mem_cone_of_mem_cone (append_mem_cone _ _) (by decide) (by decide)
      (cone_mono (List.prefix_append _ _) hlη)
  · exact not_mem_cone_of_mem_cone (append_mem_cone _ _) (by decide) (by decide)
      (cone_mono (List.prefix_append _ _) hlη)

/-! ## 9. The theorem -/

theorem not_sufficientlyExpanded_of_frozen {V : Word} (hV : Frozen V) (hS : IsStandardForm V) :
    ¬ SufficientlyExpanded V := by
  intro hSE
  obtain ⟨L, hF, hG⟩ := hV
  obtain ⟨-, ⟨Ξ, Υ, rfl, hX, hY⟩, hSF⟩ := hS
  have hG' : Good (act Ξ) Υ L := by
    have := (good_xword_append hX.2 1 Υ L).1 hG
    rwa [mul_one] at this
  obtain ⟨hlen, hst⟩ := good_yword hY.2 hG'
  -- the subscript of the `k`-th `y`-letter
  let t : ℕ → Seq := fun k => gsub ((Υ[k]?).getD (.x [], 0)).1
  have hΥ : ∀ k (hk : k < L.length), Υ[k]? = some (.y (t k), if L[k].2.2 then 1 else -1) := by
    intro k hk
    obtain ⟨t0, h1, -⟩ := hst k hk
    simp only [t, h1]
    rfl
  have hchart : ∀ k (hk : k < L.length) η,
      (act (Υ.take k) * act Ξ) (psi L[k].1 (L[k].2.1 ++ₛ η)) = t k ++ₛ η := by
    intro k hk η
    obtain ⟨t0, h1, h2⟩ := hst k hk
    have : t k = t0 := by simp only [t, h1]; rfl
    rw [this]
    exact h2 η
  -- the standard-form order: an earlier subscript is never a prefix of a later one
  have hord : ∀ i j, i < j → j < L.length → ¬ t i <+: t j := by
    intro i j hij hj hp
    have hi : i < L.length := by omega
    have ei : (Ξ ++ Υ)[Ξ.length + i]? =
        some (.y (t i), if L[i].2.2 then 1 else -1) := by
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact hΥ i hi
    have ej : (Ξ ++ Υ)[Ξ.length + j]? =
        some (.y (t j), if L[j].2.2 then 1 else -1) := by
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact hΥ j hj
    rw [List.getElem?_eq_some_iff] at ei ej
    obtain ⟨hi', ei⟩ := ei
    obtain ⟨hj', ej⟩ := ej
    have := hSF _ _ hi' hj' _ _ _ _ ei ej hp
    omega
  -- the support fact (g)
  have hsupp : ∀ k (hk : k < L.length) (u : Seq), (u = t k ∨ ∃ z, u = t k ++ [z]) →
      ∀ ξ, (act (Υ.take k) * act Ξ) ξ ∈ cone u ↔ act Ξ ξ ∈ cone u := by
    intro k hk u hu ξ
    rw [Equiv.Perm.mul_apply]
    apply act_mem_cone_iff
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
    have hik : i < k := by simp at hi; omega
    have hiL : i < L.length := by omega
    have ei := hΥ i hiL
    rw [List.getElem?_eq_some_iff] at ei
    obtain ⟨hi', ei⟩ := ei
    refine ⟨t i, by rw [List.getElem_take, ei], ?_⟩
    have hno := hord i k hik hk
    rcases hu with rfl | ⟨z, rfl⟩
    · exact Or.inl hno
    · by_cases h : t i <+: t k ++ [z]
      · rcases List.prefix_concat_iff.1 h with h | h
        · exact Or.inr h
        · exact absurd h hno
      · exact Or.inl h
  refine setting_false (g := act Ξ) (L := L) (t := t) (Occ := YOccurs (Ξ ++ Υ))
    (Pos := YOccursPos (Ξ ++ Υ)) (Neg := YOccursNeg (Ξ ++ Υ)) ⟨inv_of_forest hF, ?_, ?_, hord,
      ?_, ?_, ?_, hSE⟩
  · intro k hk
    have := image_eq_preimage (hchart k hk) [] (by simpa using hsupp k hk (t k) (Or.inl rfl))
    simp only [List.append_nil] at this
    exact this
  · intro k hk z
    exact image_eq_preimage (hchart k hk) [z] (hsupp k hk _ (Or.inr ⟨z, rfl⟩))
  · intro s
    constructor
    · rintro ⟨n, hn⟩
      rcases List.mem_append.1 hn with h | h
      · obtain ⟨s', hs'⟩ := hX.2 _ h
        simp at hs'
      · obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.1 h
        have hkL : k < L.length := hlen ▸ hk
        have := hΥ k hkL
        rw [List.getElem?_eq_getElem hk, hke] at this
        simp only [Option.some.injEq, Prod.mk.injEq, Gen.y.injEq] at this
        exact ⟨k, hkL, this.1.symm⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨_, List.mem_append_right _ (List.mem_of_getElem? (hΥ k hk))⟩
  · intro k hk hc
    have := hΥ k hk
    rw [hc] at this
    exact ⟨1, one_pos, List.mem_append_right _ (List.mem_of_getElem? this)⟩
  · intro k hk hc
    have := hΥ k hk
    rw [hc] at this
    exact ⟨-1, by norm_num, List.mem_append_right _ (List.mem_of_getElem? this)⟩
end PartF

alias not_sufficientlyExpanded_of_frozen := PartF.not_sufficientlyExpanded_of_frozen

theorem frozen_of_derives {V : Word} (h : Relation.ReflTransGen LodhaMoorePosCommute.Step W0 V) : Frozen V := by
  induction h with
  | refl => exact frozen_W0
  | tail _ hst ih => exact frozen_posStep ih hst

theorem lemma56_fails :
    ¬ ∀ W, IsStandardForm W → ∃ W', Relation.ReflTransGen LodhaMoorePosCommute.Step W W' ∧ IsStandardForm W' ∧
      SufficientlyExpanded W' := by
  intro h
  obtain ⟨W', hd, hs, hse⟩ := h W0 isStandardForm_W0
  exact not_sufficientlyExpanded_of_frozen (frozen_of_derives hd) hs hse

end LM56

open LodhaMoore in
theorem solution :
    ¬ ∀ W : LodhaMoore.Word, LodhaMoore.IsStandardForm W →
      ∃ W', Relation.ReflTransGen LodhaMoorePosCommute.Step W W' ∧ LodhaMoore.IsStandardForm W' ∧
        LodhaMoore.SufficientlyExpanded W' :=
  LM56.lemma56_fails
