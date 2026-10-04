-- Prove2me | solution 1 for LodhaMoore.exists_mem_F_finAct_of_lexLt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:57:40.437966+00:00
-- url     : https://prove2.me/submissions/87914823-f7b7-4ebd-948b-a6967898b34a

import Mathlib
import Definitions.Def_LodhaMoore
import Theorems.Thm_LodhaMoore_bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R
section
/-! # Lodha–Moore §3 (group S3b): Propositions 3.4 and 3.5, and finite presentability. -/

namespace LodhaMoore.Dev.S3b

open LodhaMoore

/-- `group`, after expanding squares (which `group` does not combine). -/

abbrev Str := Stream' Bool

/-! ## Streams and cylinders -/

theorem take_length_append (s : Seq) (η : Str) : (s ++ₛ η).take s.length = s := by
  have := Stream'.append_take (x := s) (a := η) (n := 0)
  simpa [Stream'.take_zero] using this.symm

/-- The cylinder of `s`. -/
def Cyl (s : Seq) (ξ : Str) : Prop := ∃ η, ξ = s ++ₛ η

theorem cyl_append_self (s : Seq) (η : Str) : Cyl s (s ++ₛ η) := ⟨η, rfl⟩

theorem prefix_of_cyl_cyl {s t : Seq} {ξ : Str} (hs : Cyl s ξ) (ht : Cyl t ξ) :
    s <+: t ∨ t <+: s := by
  obtain ⟨η, rfl⟩ := hs
  obtain ⟨ζ, hζ⟩ := ht
  have h1 : (s ++ₛ η).take s.length = s := take_length_append s η
  have h2 : (s ++ₛ η).take t.length = t := by rw [hζ]; exact take_length_append t ζ
  rcases le_total s.length t.length with h | h
  · left; rw [← h1, ← h2]; exact Stream'.take_prefix_take_left _ _ _ h
  · right; rw [← h1, ← h2]; exact Stream'.take_prefix_take_left _ _ _ h

theorem not_cyl_of_incompatible {s t : Seq} (h : Incompatible s t) {ξ : Str} (hs : Cyl s ξ) :
    ¬ Cyl t ξ := fun ht => by
  rcases prefix_of_cyl_cyl hs ht with h' | h'
  · exact h.1 h'
  · exact h.2 h'

theorem cyl_of_prefix {s t : Seq} (h : s <+: t) {ξ : Str} (ht : Cyl t ξ) : Cyl s ξ := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨η, rfl⟩ := ht
  exact ⟨w ++ₛ η, by rw [Stream'.append_append_stream]⟩

theorem localize_append_self (s : Seq) (f : Str → Str) (η : Str) :
    localize s f (s ++ₛ η) = s ++ₛ f η := by
  unfold localize
  rw [if_pos (take_length_append s η), Stream'.drop_append_stream]

theorem localize_of_not_cyl {s : Seq} {ξ : Str} (h : ¬ Cyl s ξ) (f : Str → Str) :
    localize s f ξ = ξ := by
  unfold localize
  rw [if_neg]
  intro h'
  apply h
  refine ⟨ξ.drop s.length, ?_⟩
  conv_lhs => rw [← Stream'.append_take_drop s.length ξ]
  rw [h']

/-! ## `FinAct` -/

theorem finAct_one (s : Seq) : FinAct 1 s s := fun _ => rfl

theorem finAct_mul {g h : SeqGroup} {s t w : Seq} (hg : FinAct g s t) (hh : FinAct h t w) :
    FinAct (g * h) s w := by
  intro ξ
  rw [MulOpposite.unop_mul, Equiv.Perm.mul_apply, hg, hh]

theorem finAct_inv {g : SeqGroup} {s t : Seq} (hg : FinAct g s t) : FinAct g⁻¹ t s := by
  intro ξ
  rw [MulOpposite.unop_inv, Equiv.Perm.inv_eq_iff_eq, hg]

theorem finAct_append {g : SeqGroup} {s t : Seq} (hg : FinAct g s t) (z : Seq) :
    FinAct g (s ++ z) (t ++ z) := by
  intro ξ
  rw [Stream'.append_append_stream, Stream'.append_append_stream, hg]

/-- `g` moves only sequences extending `q`. -/
def Supp (g : SeqGroup) (q : Seq) : Prop := ∀ ξ, ¬ Cyl q ξ → MulOpposite.unop g ξ = ξ

theorem supp_one (q : Seq) : Supp 1 q := fun _ _ => rfl

theorem supp_mul {g h : SeqGroup} {q : Seq} (hg : Supp g q) (hh : Supp h q) : Supp (g * h) q := by
  intro ξ hξ
  rw [MulOpposite.unop_mul, Equiv.Perm.mul_apply, hg ξ hξ, hh ξ hξ]

theorem supp_inv {g : SeqGroup} {q : Seq} (hg : Supp g q) : Supp g⁻¹ q := by
  intro ξ hξ
  rw [MulOpposite.unop_inv, Equiv.Perm.inv_eq_iff_eq, hg ξ hξ]

theorem supp_mono {g : SeqGroup} {q q' : Seq} (hg : Supp g q) (h : q' <+: q) : Supp g q' :=
  fun ξ hξ => hg ξ (fun h' => hξ (cyl_of_prefix h h'))

theorem finAct_of_supp {g : SeqGroup} {q v : Seq} (hg : Supp g q) (h : Incompatible q v) :
    FinAct g v v := fun ξ => hg _ (not_cyl_of_incompatible ⟨h.2, h.1⟩ (cyl_append_self v ξ))

/-! ## The generators as functions -/

theorem bij_x (s : Seq) : Function.Bijective (xSeq s) :=
  (bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R.1 s).1

theorem unop_xs (s : Seq) (ξ : Str) : MulOpposite.unop (xs s) ξ = xSeq s ξ := by
  unfold xs toSeqGroup
  rw [dif_pos (bij_x s)]
  rfl

theorem supp_xs (s : Seq) : Supp (xs s) s := fun ξ hξ => by
  rw [unop_xs]; exact localize_of_not_cyl hξ _

theorem finAct_xs_of {q d d' : Seq} (h : ∀ ξ, xFun (d ++ₛ ξ) = d' ++ₛ ξ) :
    FinAct (xs q) (q ++ d) (q ++ d') := by
  intro ξ
  rw [unop_xs, Stream'.append_append_stream, xSeq, localize_append_self, h,
    Stream'.append_append_stream]

theorem finAct_x00 (q z : Seq) : FinAct (xs q) (q ++ false :: false :: z) (q ++ false :: z) :=
  finAct_xs_of fun _ => rfl

theorem finAct_x01 (q z : Seq) :
    FinAct (xs q) (q ++ false :: true :: z) (q ++ true :: false :: z) :=
  finAct_xs_of fun _ => rfl

theorem finAct_x1 (q z : Seq) : FinAct (xs q) (q ++ true :: z) (q ++ true :: true :: z) :=
  finAct_xs_of fun _ => rfl

theorem incompat_cons {a b : Bool} (h : a ≠ b) (u v : Seq) : Incompatible (a :: u) (b :: v) := by
  refine ⟨fun h' => h ?_, fun h' => h ?_⟩
  · exact (List.cons_prefix_cons.mp h').1
  · exact (List.cons_prefix_cons.mp h').1.symm

theorem incompat_append (p : Seq) {u v : Seq} (h : Incompatible u v) :
    Incompatible (p ++ u) (p ++ v) :=
  ⟨fun h' => h.1 ((List.prefix_append_right_inj p).mp h'),
    fun h' => h.2 ((List.prefix_append_right_inj p).mp h')⟩

/-! ## Localized copies of `F` -/

/-- The group generated by the `x_{q w}`. -/
def Loc (q : Seq) : Subgroup SeqGroup := Subgroup.closure {g | ∃ w, g = xs (q ++ w)}

/-- The group generated by `x_q`, `x_{q0}`, `x_{q1}`. -/
def Loc3 (q : Seq) : Subgroup SeqGroup :=
  Subgroup.closure {xs q, xs (q ++ [false]), xs (q ++ [true])}

theorem loc3_le_loc (q : Seq) : Loc3 q ≤ Loc q := by
  rw [Loc3, Subgroup.closure_le]
  rintro g (rfl | rfl | rfl)
  · exact Subgroup.subset_closure ⟨[], by simp⟩
  · exact Subgroup.subset_closure ⟨[false], rfl⟩
  · exact Subgroup.subset_closure ⟨[true], rfl⟩

theorem loc_le_F (q : Seq) : Loc q ≤ F := by
  rw [Loc, Subgroup.closure_le]
  rintro g ⟨w, rfl⟩
  exact Subgroup.subset_closure ⟨_, rfl⟩

theorem supp_of_mem_loc {q : Seq} {g : SeqGroup} (hg : g ∈ Loc q) : Supp g q := by
  induction hg using Subgroup.closure_induction with
  | mem g hg => obtain ⟨w, rfl⟩ := hg; exact supp_mono (supp_xs _) (List.prefix_append _ _)
  | one => exact supp_one q
  | mul g h _ _ ihg ihh => exact supp_mul ihg ihh
  | inv g _ ih => exact supp_inv ih

/-! ## Lemma S: one sequence can be shortened to one of four representatives -/

/-- The four representatives `⟨⟩, 0, 1, 10`. -/
def IsBase (w : Seq) : Prop := w = [] ∨ w = [false] ∨ w = [true] ∨ w = [true, false]

theorem isBase_length {w : Seq} (h : IsBase w) : w.length ≤ 2 := by
  rcases h with rfl | rfl | rfl | rfl <;> simp

theorem lemmaS (q : Seq) :
    (w : Seq) → ∃ g ∈ Loc3 q, ∃ w0, IsBase w0 ∧ FinAct g (q ++ w0) (q ++ w)
  | [] => ⟨1, one_mem _, [], Or.inl rfl, finAct_one _⟩
  | [d] => ⟨1, one_mem _, [d], by cases d <;> simp [IsBase], finAct_one _⟩
  | false :: false :: z => by
      obtain ⟨g, hg, w0, hw0, h⟩ := lemmaS q (false :: z)
      exact ⟨g * (xs q)⁻¹, mul_mem hg (inv_mem (Subgroup.subset_closure (by simp))), w0, hw0,
        finAct_mul h (finAct_inv (finAct_x00 q z))⟩
  | true :: true :: z => by
      obtain ⟨g, hg, w0, hw0, h⟩ := lemmaS q (true :: z)
      exact ⟨g * xs q, mul_mem hg (Subgroup.subset_closure (by simp)), w0, hw0,
        finAct_mul h (finAct_x1 q z)⟩
  | [false, true] => ⟨(xs q)⁻¹, inv_mem (Subgroup.subset_closure (by simp)), [true, false],
      by simp [IsBase], finAct_inv (finAct_x01 q [])⟩
  | [true, false] => ⟨1, one_mem _, [true, false], by simp [IsBase], finAct_one _⟩
  | false :: true :: true :: z => by
      obtain ⟨g, hg, w0, hw0, h⟩ := lemmaS q (false :: true :: z)
      have h1 : FinAct (xs (q ++ [false])) (q ++ false :: true :: z)
          (q ++ false :: true :: true :: z) := by
        simpa using finAct_x1 (q ++ [false]) z
      exact ⟨g * xs (q ++ [false]), mul_mem hg (Subgroup.subset_closure (by simp)), w0, hw0,
        finAct_mul h h1⟩
  | false :: true :: false :: z => by
      obtain ⟨g, hg, w0, hw0, h⟩ := lemmaS q (true :: false :: z)
      have h1 : FinAct (xs (q ++ [true]))⁻¹ (q ++ true :: false :: z)
          (q ++ true :: false :: false :: z) := by
        simpa using finAct_inv (finAct_x00 (q ++ [true]) z)
      have h2 : FinAct (xs q)⁻¹ (q ++ true :: false :: false :: z)
          (q ++ false :: true :: false :: z) := finAct_inv (finAct_x01 q (false :: z))
      exact ⟨g * (xs (q ++ [true]))⁻¹ * (xs q)⁻¹,
        mul_mem (mul_mem hg (inv_mem (Subgroup.subset_closure (by simp))))
          (inv_mem (Subgroup.subset_closure (by simp))), w0, hw0,
        finAct_mul (finAct_mul h h1) h2⟩
  | true :: false :: false :: z => by
      obtain ⟨g, hg, w0, hw0, h⟩ := lemmaS q (true :: false :: z)
      have h1 : FinAct (xs (q ++ [true]))⁻¹ (q ++ true :: false :: z)
          (q ++ true :: false :: false :: z) := by
        simpa using finAct_inv (finAct_x00 (q ++ [true]) z)
      exact ⟨g * (xs (q ++ [true]))⁻¹, mul_mem hg (inv_mem (Subgroup.subset_closure (by simp))),
        w0, hw0, finAct_mul h h1⟩
  | true :: false :: true :: z => by
      obtain ⟨g, hg, w0, hw0, h⟩ := lemmaS q (false :: true :: z)
      have h1 : FinAct (xs (q ++ [false])) (q ++ false :: true :: z)
          (q ++ false :: true :: true :: z) := by
        simpa using finAct_x1 (q ++ [false]) z
      have h2 : FinAct (xs q) (q ++ false :: true :: true :: z)
          (q ++ true :: false :: true :: z) := finAct_x01 q (true :: z)
      exact ⟨g * xs (q ++ [false]) * xs q,
        mul_mem (mul_mem hg (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp)),
        w0, hw0, finAct_mul (finAct_mul h h1) h2⟩
termination_by w => w.length

/-! ## Proposition 3.4 -/


/-! ## Proposition 3.5 -/

theorem lexLt_split (p u v : Seq) : LexLt (p ++ false :: u) (p ++ true :: v) := by
  refine Or.inr ⟨incompat_append p (incompat_cons Bool.false_ne_true u v), p.length, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro j hj
    rw [List.getElem?_append_left hj, List.getElem?_append_left hj]

theorem exists_split_of_lexLt {u v : Seq} (h : Incompatible u v) (hlt : LexLt u v) :
    ∃ p u' v', u = p ++ false :: u' ∧ v = p ++ true :: v' := by
  rcases hlt with ⟨h1, -⟩ | ⟨-, i, hu, hv, hj⟩
  · exact absurd h1 h.2
  have hiu : i < u.length := by
    by_contra hc; rw [List.getElem?_eq_none (not_lt.mp hc)] at hu; cases hu
  have hiv : i < v.length := by
    by_contra hc; rw [List.getElem?_eq_none (not_lt.mp hc)] at hv; cases hv
  have hu' : u[i] = false := by rw [List.getElem?_eq_getElem hiu] at hu; exact Option.some.inj hu
  have hv' : v[i] = true := by rw [List.getElem?_eq_getElem hiv] at hv; exact Option.some.inj hv
  have htake : u.take i = v.take i := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take, List.getElem?_take]
    split_ifs with hji
    · exact hj j hji
    · rfl
  refine ⟨u.take i, u.drop (i + 1), v.drop (i + 1), ?_, ?_⟩
  · conv_lhs => rw [← List.take_append_drop i u]
    rw [← List.cons_getElem_drop_succ (h := hiu), hu']
  · conv_lhs => rw [← List.take_append_drop i v]
    rw [htake, ← List.cons_getElem_drop_succ (h := hiv), hv']

/-- The conclusion of Proposition 3.5 for a pair. -/
def Good (u v : Seq) : Prop :=
  ∃ g ∈ F, ∃ s t : Seq, LexLt s t ∧ s.length ≤ 3 ∧ t.length ≤ 3 ∧ FinAct g s u ∧ FinAct g t v

theorem good_trans {u v u' v' : Seq} (h : Good u v) {k : SeqGroup} (hk : k ∈ F)
    (hu : FinAct k u u') (hv : FinAct k v v') : Good u' v' := by
  obtain ⟨g, hg, s, t, hst, hs, ht, hgs, hgt⟩ := h
  exact ⟨g * k, mul_mem hg hk, s, t, hst, hs, ht, finAct_mul hgs hu, finAct_mul hgt hv⟩

theorem good_T (U V : Seq) : Good (false :: U) (true :: V) := by
  obtain ⟨g1, hg1, U0, hU0, h1⟩ := lemmaS [false] U
  obtain ⟨g2, hg2, V0, hV0, h2⟩ := lemmaS [true] V
  have base : Good (false :: U0) (true :: V0) :=
    ⟨1, one_mem _, false :: U0, true :: V0, lexLt_split [] U0 V0,
      by simp; have := isBase_length hU0; omega, by simp; have := isBase_length hV0; omega,
      finAct_one _, finAct_one _⟩
  have s1 := supp_of_mem_loc (loc3_le_loc _ hg1)
  have s2 := supp_of_mem_loc (loc3_le_loc _ hg2)
  refine good_trans base (k := g1 * g2)
    (mul_mem (loc_le_F _ (loc3_le_loc _ hg1)) (loc_le_F _ (loc3_le_loc _ hg2))) ?_ ?_
  · exact finAct_mul h1 (finAct_of_supp s2 (incompat_cons (by decide) [] U))
  · exact finAct_mul (finAct_of_supp s1 (incompat_cons Bool.false_ne_true [] V0)) h2

theorem xs_mem_F (s : Seq) : xs s ∈ F := Subgroup.subset_closure ⟨s, rfl⟩

theorem good_P0 (U V : Seq) : Good (false :: false :: U) (false :: true :: V) :=
  good_trans (good_T U (false :: V)) (inv_mem (xs_mem_F []))
    (finAct_inv (finAct_x00 [] U)) (finAct_inv (finAct_x01 [] V))

theorem good_P1 (U V : Seq) : Good (true :: false :: U) (true :: true :: V) :=
  good_trans (good_T (true :: U) V) (xs_mem_F []) (finAct_x01 [] U) (finAct_x1 [] V)

theorem good_P10 (U V : Seq) :
    Good (true :: false :: false :: U) (true :: false :: true :: V) :=
  good_trans (good_P1 U (false :: V)) (inv_mem (xs_mem_F [true]))
    (by simpa using finAct_inv (finAct_x00 [true] U))
    (by simpa using finAct_inv (finAct_x01 [true] V))

theorem good_split (p U V : Seq) : Good (p ++ false :: U) (p ++ true :: V) := by
  obtain ⟨g, hg, p0, hp0, h⟩ := lemmaS [] p
  simp only [List.nil_append] at h
  have hgF : g ∈ F := loc_le_F _ (loc3_le_loc _ hg)
  have key : Good (p0 ++ false :: U) (p0 ++ true :: V) := by
    rcases hp0 with rfl | rfl | rfl | rfl
    · exact good_T U V
    · exact good_P0 U V
    · exact good_P1 U V
    · exact good_P10 U V
  exact good_trans key hgF (finAct_append h _) (finAct_append h _)

theorem good_of_lexLt {u v : Seq} (huv : Incompatible u v) (hlt : LexLt u v) : Good u v := by
  obtain ⟨p, u', v', rfl, rfl⟩ := exists_split_of_lexLt huv hlt
  exact good_split p u' v'


/-! ## `Forall₂` of `FinAct` -/

/-! ## Binary trees and tree pairs -/

namespace BT

end BT

open BT

/-! ## Every tree pair supported below `q` is realized in `Loc q` -/

/-! ## Stabilizers of `0`, `1`, `10` -/

/-! ## The abstract Tietze argument -/

/-! ## A homomorphism from `F` out of the finite presentation of `F` -/

/-! ## Facts about the action used in the presentation -/

/-! ## Representatives and conjugators -/

/-! ## The relations, in any group receiving `F` -/

section Generic

variable {Q : Type*} [Group Q] (κ : ↥F →* Q) (Yof : Seq → Q)

variable (P : Seq → Prop)

end Generic

/-! ## Words in `x`, `x₁` -/

/-! ## `G` is finitely presented -/

inductive TG
  | x | x1 | y | y0 | y1 | y10
  deriving DecidableEq

instance : Fintype TG := ⟨{.x, .x1, .y, .y0, .y1, .y10}, fun t => by cases t <;> simp⟩

/-! ## `G₀` is finitely presented -/

inductive TG0
  | x | x1 | y10
  deriving DecidableEq

instance : Fintype TG0 := ⟨{.x, .x1, .y10}, fun t => by cases t <;> simp⟩

/-! ## Nonconstant incompatible pairs: two `F`-orbits -/

/-! ## The nine relations of p. 7 -/

end LodhaMoore.Dev.S3b

namespace LodhaMoore

open LodhaMoore.Dev.S3b

end LodhaMoore
end

section
open LodhaMoore
open LodhaMoore.Dev.S3b
theorem solution (u v : Seq) (huv : Incompatible u v) (hlt : LexLt u v) :
    ∃ g ∈ F, ∃ s t : Seq, LexLt s t ∧ s.length ≤ 3 ∧ t.length ≤ 3 ∧ FinAct g s u ∧
      FinAct g t v :=
  good_of_lexLt huv hlt
end
