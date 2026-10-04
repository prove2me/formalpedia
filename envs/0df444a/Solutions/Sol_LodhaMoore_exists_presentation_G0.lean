-- Prove2me | solution 1 for LodhaMoore.exists_presentation_G0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T12:15:10.317558+00:00
-- url     : https://prove2.me/submissions/26b6cfb4-4324-4b39-a262-b75531579a6d

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_CannonFloydParry_Presentations
import Theorems.Thm_LodhaMoore_bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R
import Theorems.Thm_LodhaMoore_exists_presentation_F_and_mulEquiv_F2
import Theorems.Thm_CannonFloydParry_Y_conj_eq_Y_succ
import Theorems.Thm_LodhaMoore_exists_mulEquiv_G0_G0Seq_and_semiconj_Phi
import Theorems.Thm_LodhaMoore_presentation_G_G0Seq_and_isFinitelyPresented

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

theorem append_stream_inj {t t' : Seq} (h : ∀ ξ : Str, t ++ₛ ξ = t' ++ₛ ξ) : t = t' := by
  have key : ∀ {a b : Seq}, (∀ ξ : Str, a ++ₛ ξ = b ++ₛ ξ) → a.length ≤ b.length → a = b := by
    intro a b hab hle
    rcases Nat.lt_or_ge a.length b.length with hlt | hge
    · exfalso
      have h0 := congrArg (fun ξ => Stream'.get ξ a.length) (hab (Stream'.const false))
      have h1 := congrArg (fun ξ => Stream'.get ξ a.length) (hab (Stream'.const true))
      simp only [Stream'.get_append_length, Stream'.get_const] at h0 h1
      rw [Stream'.get_append_left _ _ _ hlt] at h0 h1
      rw [← h0] at h1
      exact Bool.false_ne_true h1.symm
    · have hl : a.length = b.length := le_antisymm hle hge
      exact Stream'.append_left_injective _ _ _ _ (hab (Stream'.const false)) hl
  rcases le_total t.length t'.length with hle | hle
  · exact key h hle
  · exact (key (fun ξ => (h ξ).symm) hle).symm

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

theorem finAct_unique {g : SeqGroup} {s t t' : Seq} (h : FinAct g s t) (h' : FinAct g s t') :
    t = t' := append_stream_inj fun ξ => by rw [← h ξ, h' ξ]

/-- `g` moves only sequences extending `q`. -/
def Supp (g : SeqGroup) (q : Seq) : Prop := ∀ ξ, ¬ Cyl q ξ → MulOpposite.unop g ξ = ξ

theorem supp_one (q : Seq) : Supp 1 q := fun _ _ => rfl

theorem supp_cyl {g : SeqGroup} {q : Seq} (hg : Supp g q) {ξ : Str} (hξ : Cyl q ξ) :
    Cyl q (MulOpposite.unop g ξ) := by
  by_contra h
  have := hg _ h
  rw [(MulOpposite.unop g).injective this] at h
  exact h hξ

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

theorem commute_of_supp {g h : SeqGroup} {p q : Seq} (hg : Supp g p) (hh : Supp h q)
    (hpq : Incompatible p q) : Commute g h := by
  apply MulOpposite.unop_injective
  refine Equiv.ext fun ξ => ?_
  simp only [MulOpposite.unop_mul, Equiv.Perm.mul_apply]
  by_cases hp : Cyl p ξ
  · have hq : ¬ Cyl q ξ := not_cyl_of_incompatible hpq hp
    have hq' : ¬ Cyl q (MulOpposite.unop g ξ) := not_cyl_of_incompatible hpq (supp_cyl hg hp)
    rw [hh ξ hq, hh _ hq']
  · by_cases hq : Cyl q ξ
    · have hp' : ¬ Cyl p (MulOpposite.unop h ξ) :=
        not_cyl_of_incompatible ⟨hpq.2, hpq.1⟩ (supp_cyl hh hq)
      rw [hg ξ hp, hg _ hp']
    · rw [hg ξ hp, hh ξ hq, hg ξ hp]

/-! ## The generators as functions -/

theorem bij_x (s : Seq) : Function.Bijective (xSeq s) :=
  (bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R.1 s).1

theorem bij_y (s : Seq) : Function.Bijective (ySeq s) :=
  (bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R.1 s).2

theorem unop_xs (s : Seq) (ξ : Str) : MulOpposite.unop (xs s) ξ = xSeq s ξ := by
  unfold xs toSeqGroup
  rw [dif_pos (bij_x s)]
  rfl

theorem unop_ys (s : Seq) (ξ : Str) : MulOpposite.unop (ys s) ξ = ySeq s ξ := by
  unfold ys toSeqGroup
  rw [dif_pos (bij_y s)]
  rfl

theorem supp_xs (s : Seq) : Supp (xs s) s := fun ξ hξ => by
  rw [unop_xs]; exact localize_of_not_cyl hξ _

theorem supp_ys (s : Seq) : Supp (ys s) s := fun ξ hξ => by
  rw [unop_ys]; exact localize_of_not_cyl hξ _

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

/-- The relation (1) `x_s² = x_{s0} x_s x_{s1}`. -/
theorem rel_one (s : Seq) : xs s * xs s = xs (s ++ [false]) * xs s * xs (s ++ [true]) := by
  have h := bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R.2 _ ⟨Rel.one s, rfl⟩
  simp only [Rel.lhs, Rel.rhs, map_mul, map_inv, FreeGroup.lift_apply_of, Gen.val] at h
  exact mul_inv_eq_one.mp h

/-- Conjugation: if `s.g = t` then `g` intertwines the localizations at `s` and `t`. -/
theorem unop_localize_comm {g : SeqGroup} {s t : Seq} (h : FinAct g s t) (f : Str → Str)
    (ξ : Str) : MulOpposite.unop g (localize s f ξ) = localize t f (MulOpposite.unop g ξ) := by
  by_cases hc : Cyl s ξ
  · obtain ⟨η, rfl⟩ := hc
    rw [localize_append_self, h, h, localize_append_self]
  · rw [localize_of_not_cyl hc, localize_of_not_cyl]
    rintro ⟨η, hη⟩
    rw [← h η] at hη
    exact hc ⟨η, (MulOpposite.unop g).injective hη⟩

/-- Proposition 3.4: `x_s g = g x_{s.g}`. -/
theorem xs_mul_eq {g : SeqGroup} {s t : Seq} (h : FinAct g s t) : xs s * g = g * xs t := by
  apply MulOpposite.unop_injective
  refine Equiv.ext fun ξ => ?_
  simp only [MulOpposite.unop_mul, Equiv.Perm.mul_apply, unop_xs]
  exact unop_localize_comm h xFun ξ

theorem ys_mul_eq {g : SeqGroup} {s t : Seq} (h : FinAct g s t) : ys s * g = g * ys t := by
  apply MulOpposite.unop_injective
  refine Equiv.ext fun ξ => ?_
  simp only [MulOpposite.unop_mul, Equiv.Perm.mul_apply, unop_ys]
  exact unop_localize_comm h (yFun true) ξ


theorem ys_conj {g : SeqGroup} {u s : Seq} (h : FinAct g u s) : g⁻¹ * ys u * g = ys s := by
  rw [mul_assoc, ys_mul_eq h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem xs_conj {g : SeqGroup} {u s : Seq} (h : FinAct g u s) : g⁻¹ * xs u * g = xs s := by
  rw [mul_assoc, xs_mul_eq h, ← mul_assoc, inv_mul_cancel, one_mul]

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

theorem loc_mono {q : Seq} (w : Seq) : Loc (q ++ w) ≤ Loc q := by
  rw [Loc, Subgroup.closure_le]
  rintro g ⟨w', rfl⟩
  exact Subgroup.subset_closure ⟨w ++ w', by simp⟩

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

theorem xs_mem_closure2 (q w : Seq) :
    xs (q ++ w) ∈ Subgroup.closure ({xs q, xs (q ++ [true])} : Set SeqGroup) := by
  set K := Subgroup.closure ({xs q, xs (q ++ [true])} : Set SeqGroup)
  have hq : xs q ∈ K := Subgroup.subset_closure (by simp)
  have hq1 : xs (q ++ [true]) ∈ K := Subgroup.subset_closure (by simp)
  have hq11 : xs (q ++ [true, true]) ∈ K := by
    have e := xs_mul_eq (finAct_x1 q [])
    have : xs (q ++ [true, true]) = (xs q)⁻¹ * xs (q ++ [true]) * xs q := by
      rw [mul_assoc, e, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]; exact mul_mem (mul_mem (inv_mem hq) hq1) hq
  have hq0 : xs (q ++ [false]) ∈ K := by
    have e := rel_one q
    have : xs (q ++ [false]) = xs q * xs q * (xs (q ++ [true]))⁻¹ * (xs q)⁻¹ := by
      rw [e]; group
    rw [this]; exact mul_mem (mul_mem (mul_mem hq hq) (inv_mem hq1)) (inv_mem hq)
  have hq10 : xs (q ++ [true, false]) ∈ K := by
    have e := rel_one (q ++ [true])
    simp only [List.append_assoc, List.cons_append, List.nil_append] at e
    have : xs (q ++ [true, false]) =
        xs (q ++ [true]) * xs (q ++ [true]) * (xs (q ++ [true, true]))⁻¹ * (xs (q ++ [true]))⁻¹ := by
      rw [e]; group
    rw [this]; exact mul_mem (mul_mem (mul_mem hq1 hq1) (inv_mem hq11)) (inv_mem hq1)
  have hL : Loc3 q ≤ K := by
    rw [Loc3, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · exact hq
    · exact hq0
    · exact hq1
  obtain ⟨g, hg, w0, hw0, h⟩ := lemmaS q w
  have e := xs_mul_eq h
  have : xs (q ++ w) = g⁻¹ * xs (q ++ w0) * g := by rw [mul_assoc, e]; group
  rw [this]
  refine mul_mem (mul_mem (inv_mem (hL hg)) ?_) (hL hg)
  rcases hw0 with rfl | rfl | rfl | rfl
  · simpa using hq
  · exact hq0
  · exact hq1
  · exact hq10

theorem closure_eq_F : Subgroup.closure ({xs [], xs [true]} : Set SeqGroup) = F := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g (rfl | rfl) <;> exact Subgroup.subset_closure ⟨_, rfl⟩
  · rw [F, Subgroup.closure_le]
    rintro g ⟨s, rfl⟩
    simpa using xs_mem_closure2 [] s

theorem lift_map_eq {α β G : Type*} [Group G] (f : α → G) (k : β → α) (w : FreeGroup β) :
    FreeGroup.lift f (FreeGroup.map k w) = FreeGroup.lift (f ∘ k) w := by
  have : (FreeGroup.lift f).comp (FreeGroup.map k) = FreeGroup.lift (f ∘ k) := by
    ext b; simp
  exact congrArg (fun φ : FreeGroup β →* G => φ w) this


/-! ## Proposition 3.5 -/

theorem lexLt_split (p u v : Seq) : LexLt (p ++ false :: u) (p ++ true :: v) := by
  refine Or.inr ⟨incompat_append p (incompat_cons Bool.false_ne_true u v), p.length, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro j hj
    rw [List.getElem?_append_left hj, List.getElem?_append_left hj]

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


/-! ## `Forall₂` of `FinAct` -/

open List in
theorem f2_append {R : Seq → Seq → Prop} {a b c d : List Seq} (h1 : Forall₂ R a b)
    (h2 : Forall₂ R c d) : Forall₂ R (a ++ c) (b ++ d) := List.rel_append h1 h2

theorem f2_comp {g h : SeqGroup} : ∀ {L1 L2 L3 : List Seq}, List.Forall₂ (FinAct g) L1 L2 →
    List.Forall₂ (FinAct h) L2 L3 → List.Forall₂ (FinAct (g * h)) L1 L3
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 => .cons (finAct_mul h1 h2) (f2_comp t1 t2)

theorem f2_inv {g : SeqGroup} : ∀ {L1 L2 : List Seq}, List.Forall₂ (FinAct g) L1 L2 →
    List.Forall₂ (FinAct g⁻¹) L2 L1
  | _, _, .nil => .nil
  | _, _, .cons h1 t1 => .cons (finAct_inv h1) (f2_inv t1)

theorem f2_refl {g : SeqGroup} : ∀ {L : List Seq}, (∀ ℓ ∈ L, FinAct g ℓ ℓ) →
    List.Forall₂ (FinAct g) L L
  | [], _ => .nil
  | a :: L, h => .cons (h a (by simp)) (f2_refl fun ℓ hℓ => h ℓ (by simp [hℓ]))

theorem f2_exists {R : Seq → Seq → Prop} : ∀ {L L' : List Seq}, List.Forall₂ R L L' →
    ∀ ℓ ∈ L, ∃ m, R ℓ m
  | _, _, .nil, ℓ, h => by simp at h
  | _, _, .cons (a := a) (b := b) h1 t1, ℓ, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨b, h1⟩
      · exact f2_exists t1 ℓ h

theorem f2_exists_mem {R : Seq → Seq → Prop} : ∀ {L L' : List Seq}, List.Forall₂ R L L' →
    ∀ ℓ ∈ L, ∃ m ∈ L', R ℓ m
  | _, _, .nil, ℓ, h => by simp at h
  | _, _, .cons (a := a) (b := b) h1 t1, ℓ, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨b, by simp, h1⟩
      · obtain ⟨m, hm, hr⟩ := f2_exists_mem t1 ℓ h
        exact ⟨m, by simp [hm], hr⟩

theorem incompat_of_prefix {p p' ℓ : Seq} (h : Incompatible p p') (hℓ : p' <+: ℓ) :
    Incompatible p ℓ := by
  refine ⟨fun h' => ?_, fun h' => h.2 (hℓ.trans h')⟩
  rcases List.prefix_or_prefix_of_prefix h' hℓ with h'' | h''
  · exact h.1 h''
  · exact h.2 h''

/-! ## Binary trees and tree pairs -/

inductive BT
  | leaf
  | node (l r : BT)

namespace BT

def leaves : BT → Seq → List Seq
  | leaf, q => [q]
  | node l r, q => l.leaves (q ++ [false]) ++ r.leaves (q ++ [true])

def size : BT → ℕ
  | leaf => 0
  | node l r => l.size + r.size + 1

theorem length_leaves : ∀ (T : BT) (q : Seq), (T.leaves q).length = T.size + 1
  | leaf, _ => rfl
  | node l r, q => by
      simp only [leaves, size, List.length_append, length_leaves l, length_leaves r]; omega

theorem leaves_ne_nil (T : BT) (q : Seq) : T.leaves q ≠ [] := by
  intro h; have := length_leaves T q; rw [h] at this; simp at this

theorem prefix_of_mem_leaves : ∀ (T : BT) (q : Seq), ∀ ℓ ∈ T.leaves q, q <+: ℓ
  | leaf, q, ℓ, h => by simp only [leaves, List.mem_singleton] at h; subst h; exact List.prefix_refl _
  | node l r, q, ℓ, h => by
      simp only [leaves, List.mem_append] at h
      rcases h with h | h
      · exact (List.prefix_append q [false]).trans (prefix_of_mem_leaves l _ ℓ h)
      · exact (List.prefix_append q [true]).trans (prefix_of_mem_leaves r _ ℓ h)

theorem cover : ∀ (T : BT) (q : Seq) (ξ : Str), Cyl q ξ → ∃ ℓ ∈ T.leaves q, Cyl ℓ ξ
  | leaf, q, ξ, h => ⟨q, by simp [leaves], h⟩
  | node l r, q, ξ, h => by
      obtain ⟨η, rfl⟩ := h
      have hη : η = Stream'.cons (η 0) η.tail := (Stream'.eta η).symm
      have e : q ++ₛ η = (q ++ [η 0]) ++ₛ η.tail := by
        rw [Stream'.append_append_stream]; conv_lhs => rw [hη]
        rfl
      rcases hb : η 0 with _ | _
      · obtain ⟨ℓ, hℓ, hc⟩ := cover l (q ++ [false]) (q ++ₛ η) ⟨η.tail, by rw [e, hb]⟩
        exact ⟨ℓ, by simp [leaves, hℓ], hc⟩
      · obtain ⟨ℓ, hℓ, hc⟩ := cover r (q ++ [true]) (q ++ₛ η) ⟨η.tail, by rw [e, hb]⟩
        exact ⟨ℓ, by simp [leaves, hℓ], hc⟩

theorem leaves_shift {h : SeqGroup} : ∀ (T : BT) {ℓ m : Seq}, FinAct h ℓ m →
    List.Forall₂ (FinAct h) (T.leaves ℓ) (T.leaves m)
  | leaf, _, _, hlm => .cons hlm .nil
  | node l r, _, _, hlm =>
      f2_append (leaves_shift l (finAct_append hlm _)) (leaves_shift r (finAct_append hlm _))

/-- Grafting a list of trees at the leaves, in order. -/
def graft : BT → List BT → BT
  | leaf, Ss => Ss.headD leaf
  | node l r, Ss => node (l.graft (Ss.take (l.size + 1))) (r.graft (Ss.drop (l.size + 1)))

theorem leaves_graft : ∀ (T : BT) (Ss : List BT) (q : Seq), Ss.length = T.size + 1 →
    (T.graft Ss).leaves q = (List.zipWith (fun ℓ S => S.leaves ℓ) (T.leaves q) Ss).flatten
  | leaf, Ss, q, h => by
      match Ss, h with
      | [S], _ => simp [graft, leaves]
  | node l r, Ss, q, h => by
      have hl : (Ss.take (l.size + 1)).length = l.size + 1 := by
        simp [List.length_take]; simp [size] at h; omega
      have hr : (Ss.drop (l.size + 1)).length = r.size + 1 := by
        simp [List.length_drop]; simp [size] at h; omega
      simp only [graft, leaves]
      rw [leaves_graft l _ _ hl, leaves_graft r _ _ hr, ← List.flatten_append,
        ← List.zipWith_append (by rw [length_leaves, hl]), List.take_append_drop]

theorem f2_flatten {h : SeqGroup} : ∀ {Dl Rl : List Seq} (Ss : List BT),
    List.Forall₂ (FinAct h) Dl Rl →
    List.Forall₂ (FinAct h) (List.zipWith (fun ℓ S => S.leaves ℓ) Dl Ss).flatten
      (List.zipWith (fun ℓ S => S.leaves ℓ) Rl Ss).flatten
  | _, _, [], _ => by simp
  | _, _, _ :: _, .nil => by simp
  | _, _, S :: Ss, .cons h1 t1 => by
      simp only [List.zipWith_cons_cons, List.flatten_cons]
      exact f2_append (leaves_shift S h1) (f2_flatten Ss t1)

theorem graft_replicate : ∀ T : BT, T.graft (List.replicate (T.size + 1) leaf) = T
  | leaf => rfl
  | node l r => by
      simp only [graft, size, List.take_replicate, List.drop_replicate]
      congr 1
      · rw [show min (l.size + 1) (l.size + r.size + 1 + 1) = l.size + 1 by omega, graft_replicate]
      · rw [show l.size + r.size + 1 + 1 - (l.size + 1) = r.size + 1 by omega, graft_replicate]

theorem exists_common : ∀ A B : BT, ∃ SA SB : List BT, SA.length = A.size + 1 ∧
    SB.length = B.size + 1 ∧ A.graft SA = B.graft SB
  | leaf, B => ⟨[B], List.replicate (B.size + 1) leaf, rfl, by simp,
      by simp [graft, graft_replicate]⟩
  | node a b, leaf => ⟨List.replicate ((node a b).size + 1) leaf, [node a b], by simp, rfl,
      by rw [graft_replicate]; rfl⟩
  | node a b, node c d => by
      obtain ⟨SA1, SB1, h1, h1', e1⟩ := exists_common a c
      obtain ⟨SA2, SB2, h2, h2', e2⟩ := exists_common b d
      refine ⟨SA1 ++ SA2, SB1 ++ SB2, by simp [size, h1, h2]; omega,
        by simp [size, h1', h2']; omega, ?_⟩
      simp only [graft]
      rw [← h1, ← h1', List.take_left, List.drop_left, List.take_left, List.drop_left, e1, e2]

end BT

open BT

/-- `(D, R)` is a tree pair for `h`: `h` maps the leaves of `D` to those of `R`, in order. -/
def TP (h : SeqGroup) (D R : BT) : Prop := List.Forall₂ (FinAct h) (D.leaves []) (R.leaves [])

theorem TP.size_eq {h : SeqGroup} {D R : BT} (H : TP h D R) : D.size = R.size := by
  have := H.length_eq; rw [length_leaves, length_leaves] at this; omega

theorem TP.refine {h : SeqGroup} {D R : BT} (H : TP h D R) (Ss : List BT)
    (hS : Ss.length = D.size + 1) : TP h (D.graft Ss) (R.graft Ss) := by
  unfold TP
  rw [leaves_graft D Ss [] hS, leaves_graft R Ss [] (by rw [hS, H.size_eq])]
  exact f2_flatten Ss H

/-- A tree with a path to `r` whose last node carries `T`. -/
def pathTree : Seq → BT → BT
  | [], T => T
  | false :: r, T => node (pathTree r T) leaf
  | true :: r, T => node leaf (pathTree r T)

theorem f2_pathTree {h : SeqGroup} : ∀ (r q : Seq) (T1 T2 : BT), Supp h (q ++ r) →
    List.Forall₂ (FinAct h) (T1.leaves (q ++ r)) (T2.leaves (q ++ r)) →
    List.Forall₂ (FinAct h) ((pathTree r T1).leaves q) ((pathTree r T2).leaves q)
  | [], q, T1, T2, _, H => by simpa [pathTree] using H
  | false :: r, q, T1, T2, hs, H => by
      simp only [pathTree, leaves]
      refine f2_append (f2_pathTree r (q ++ [false]) T1 T2 (by simpa using hs) (by simpa using H))
        (.cons (finAct_of_supp hs ?_) .nil)
      exact incompat_append q (incompat_cons (by decide) r [])
  | true :: r, q, T1, T2, hs, H => by
      simp only [pathTree, leaves]
      refine f2_append (.cons (finAct_of_supp hs ?_) .nil)
        (f2_pathTree r (q ++ [true]) T1 T2 (by simpa using hs) (by simpa using H))
      exact incompat_append q (incompat_cons (by decide) r [])

theorem tp_xs (r : Seq) : TP (xs r) (pathTree r (node (node leaf leaf) leaf))
    (pathTree r (node leaf (node leaf leaf))) := by
  unfold TP
  refine f2_pathTree r [] _ _ (by simpa using supp_xs r) ?_
  simp only [List.nil_append, leaves, List.append_assoc, List.cons_append, List.nil_append]
  refine .cons ?_ (.cons ?_ (.cons ?_ .nil))
  · simpa using finAct_x00 r []
  · simpa using finAct_x01 r []
  · simpa using finAct_x1 r []

theorem TP.inv {h : SeqGroup} {D R : BT} (H : TP h D R) : TP h⁻¹ R D := f2_inv H

theorem TP.mul {g h : SeqGroup} {D1 R1 D2 R2 : BT} (H1 : TP g D1 R1) (H2 : TP h D2 R2) :
    ∃ D R, TP (g * h) D R := by
  obtain ⟨SA, SB, hA, hB, e⟩ := exists_common R1 D2
  have H1' := H1.refine SA (by rw [hA, H1.size_eq])
  have H2' := H2.refine SB hB
  refine ⟨D1.graft SA, R2.graft SB, ?_⟩
  unfold TP at H1' H2' ⊢
  rw [e] at H1'
  exact f2_comp H1' H2'

theorem exists_TP {h : SeqGroup} (hh : h ∈ F) : ∃ D R, TP h D R := by
  induction hh using Subgroup.closure_induction'' with
  | mem x hx => obtain ⟨r, rfl⟩ := hx; exact ⟨_, _, tp_xs r⟩
  | inv_mem x hx => obtain ⟨r, rfl⟩ := hx; exact ⟨_, _, (tp_xs r).inv⟩
  | one => exact ⟨leaf, leaf, .cons (finAct_one _) .nil⟩
  | mul g h _ _ ihg ihh =>
      obtain ⟨D1, R1, H1⟩ := ihg
      obtain ⟨D2, R2, H2⟩ := ihh
      exact H1.mul H2

/-- Two elements agreeing on the leaves of a tree are equal. -/
theorem eq_of_agree {h k : SeqGroup} (T : BT)
    (hag : ∀ ℓ ∈ T.leaves [], ∃ m, FinAct h ℓ m ∧ FinAct k ℓ m) : h = k := by
  apply MulOpposite.unop_injective
  refine Equiv.ext fun ξ => ?_
  obtain ⟨ℓ, hℓ, η, rfl⟩ := cover T [] ξ ⟨ξ, rfl⟩
  obtain ⟨m, h1, h2⟩ := hag ℓ hℓ
  rw [h1, h2]

/-! ## Every tree pair supported below `q` is realized in `Loc q` -/

def vine : ℕ → BT
  | 0 => leaf
  | n + 1 => node leaf (vine n)

theorem xs_mem_loc (q : Seq) : xs q ∈ Loc q := Subgroup.subset_closure ⟨[], by simp⟩

theorem f2_fix_of_supp {k : SeqGroup} {p p' : Seq} (hk : Supp k p) (hpp : Incompatible p p')
    (L : List Seq) (hL : ∀ ℓ ∈ L, p' <+: ℓ) : List.Forall₂ (FinAct k) L L :=
  f2_refl fun ℓ hℓ => finAct_of_supp hk (incompat_of_prefix hpp (hL ℓ hℓ))

theorem rotate : ∀ (m n : ℕ) (q : Seq), ∃ k ∈ Loc q,
    List.Forall₂ (FinAct k) ((node (vine m) (vine n)).leaves q) ((vine (m + n + 1)).leaves q)
  | 0, n, q => ⟨1, one_mem _, by
      rw [show 0 + n + 1 = n + 1 by omega]
      exact f2_refl fun ℓ _ => finAct_one ℓ⟩
  | m + 1, n, q => by
      obtain ⟨k, hk, hF⟩ := rotate m n (q ++ [true])
      refine ⟨xs q * k, mul_mem (xs_mem_loc q) (loc_mono _ hk), ?_⟩
      have step1 : List.Forall₂ (FinAct (xs q)) ((node (vine (m + 1)) (vine n)).leaves q)
          ((node leaf (node (vine m) (vine n))).leaves q) := by
        simp only [vine, leaves, List.append_assoc, List.cons_append,
          List.nil_append]
        refine .cons ?_ (f2_append ?_ ?_)
        · simpa using finAct_x00 q []
        · exact leaves_shift _ (by simpa using finAct_x01 q [])
        · exact leaves_shift _ (by simpa using finAct_x1 q [])
      have step2 : List.Forall₂ (FinAct k) ((node leaf (node (vine m) (vine n))).leaves q)
          ((vine (m + 1 + n + 1)).leaves q) := by
        rw [show m + 1 + n + 1 = (m + n + 1) + 1 by omega]
        simp only [vine, leaves]
        refine f2_append (.cons (finAct_of_supp (supp_of_mem_loc hk) ?_) .nil) hF
        exact incompat_append q (incompat_cons (by decide) [] [])
      exact f2_comp step1 step2

theorem toVine : ∀ (T : BT) (q : Seq), ∃ k ∈ Loc q,
    List.Forall₂ (FinAct k) (T.leaves q) ((vine T.size).leaves q)
  | leaf, q => ⟨1, one_mem _, f2_refl fun ℓ _ => finAct_one ℓ⟩
  | node a b, q => by
      obtain ⟨ka, hka, ha⟩ := toVine a (q ++ [false])
      obtain ⟨kb, hkb, hb⟩ := toVine b (q ++ [true])
      obtain ⟨r, hr, hrot⟩ := rotate a.size b.size q
      refine ⟨ka * kb * r, mul_mem (mul_mem (loc_mono _ hka) (loc_mono _ hkb)) hr, ?_⟩
      have hinc : Incompatible (q ++ [false]) (q ++ [true]) :=
        incompat_append q (incompat_cons (by decide) [] [])
      have e1 : List.Forall₂ (FinAct (ka * kb)) ((node a b).leaves q)
          ((node (vine a.size) (vine b.size)).leaves q) := by
        simp only [leaves]
        refine f2_append (f2_comp ha ?_) (f2_comp ?_ hb)
        · exact f2_fix_of_supp (supp_of_mem_loc hkb) ⟨hinc.2, hinc.1⟩ _
            (prefix_of_mem_leaves _ _)
        · exact f2_fix_of_supp (supp_of_mem_loc hka) hinc _ (prefix_of_mem_leaves _ _)
      simpa [size] using f2_comp e1 hrot

theorem tp_in_loc (D R : BT) (q : Seq) (h : D.size = R.size) : ∃ k ∈ Loc q,
    List.Forall₂ (FinAct k) (D.leaves q) (R.leaves q) := by
  obtain ⟨kD, hkD, hD⟩ := toVine D q
  obtain ⟨kR, hkR, hR⟩ := toVine R q
  refine ⟨kD * kR⁻¹, mul_mem hkD (inv_mem hkR), f2_comp hD ?_⟩
  rw [h]; exact f2_inv hR

/-! ## Stabilizers of `0`, `1`, `10` -/

theorem fixed_pair {h : SeqGroup} {p ℓ m : Seq} (hfix : FinAct h p p) (hlm : FinAct h ℓ m)
    (hp : p <+: ℓ ∨ p <+: m) : ℓ = m := by
  rcases hp with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · exact finAct_unique (finAct_append hfix w) hlm
  · have h2 := finAct_append hfix w
    apply append_stream_inj; intro ξ
    apply (MulOpposite.unop h).injective
    rw [hlm ξ, h2 ξ]

theorem f2_and {g h : SeqGroup} : ∀ {L L' : List Seq}, List.Forall₂ (FinAct g) L L' →
    List.Forall₂ (FinAct h) L L' → List.Forall₂ (fun a b => FinAct g a b ∧ FinAct h a b) L L'
  | _, _, .nil, .nil => .nil
  | _, _, .cons h1 t1, .cons h2 t2 => .cons ⟨h1, h2⟩ (f2_and t1 t2)

theorem pos_mem {p1 p2 p3 : Seq} (h12 : Incompatible p1 p2) (h23 : Incompatible p2 p3)
    {A B C : List Seq} (hA : ∀ ℓ ∈ A, p1 <+: ℓ) (hB : ∀ ℓ ∈ B, p2 <+: ℓ)
    (hC : ∀ ℓ ∈ C, p3 <+: ℓ) (i : ℕ) (hi : i < (A ++ B ++ C).length) :
    (p2 <+: (A ++ B ++ C)[i]) ↔ (A.length ≤ i ∧ i < A.length + B.length) := by
  have hAB : (A ++ B).length = A.length + B.length := List.length_append
  by_cases h1 : i < A.length
  · rw [List.getElem_append_left (by rw [hAB]; omega), List.getElem_append_left h1]
    have := hA _ (List.getElem_mem h1)
    constructor
    · intro hp; exact absurd hp (incompat_of_prefix ⟨h12.2, h12.1⟩ this).1
    · intro h; omega
  · by_cases h2 : i < A.length + B.length
    · rw [List.getElem_append_left (by rw [hAB]; omega), List.getElem_append_right (by omega)]
      exact ⟨fun _ => ⟨by omega, h2⟩, fun _ => hB _ (List.getElem_mem _)⟩
    · rw [List.getElem_append_right (by rw [hAB]; omega)]
      have hi2 : i - (A ++ B).length < C.length := by
        simp only [List.length_append] at hi ⊢; omega
      have := hC _ (List.getElem_mem hi2)
      constructor
      · intro hp; exact absurd hp (incompat_of_prefix h23 this).1
      · intro h; omega

theorem block3 {h : SeqGroup} {p1 p2 p3 : Seq} (h12 : Incompatible p1 p2)
    (h23 : Incompatible p2 p3) (hfix : FinAct h p2 p2) {A B C A' B' C' : List Seq}
    (hA : ∀ ℓ ∈ A, p1 <+: ℓ) (hB : ∀ ℓ ∈ B, p2 <+: ℓ) (hC : ∀ ℓ ∈ C, p3 <+: ℓ)
    (hA' : ∀ ℓ ∈ A', p1 <+: ℓ) (hB' : ∀ ℓ ∈ B', p2 <+: ℓ) (hC' : ∀ ℓ ∈ C', p3 <+: ℓ)
    (hBne : B ≠ []) (hB'ne : B' ≠ [])
    (hF : List.Forall₂ (FinAct h) (A ++ B ++ C) (A' ++ B' ++ C')) :
    List.Forall₂ (FinAct h) A A' ∧ List.Forall₂ (FinAct h) C C' := by
  have hlen := hF.length_eq
  have key : ∀ i (hi : i < (A ++ B ++ C).length) (hi' : i < (A' ++ B' ++ C').length),
      (A.length ≤ i ∧ i < A.length + B.length) ↔
        (A'.length ≤ i ∧ i < A'.length + B'.length) := by
    intro i hi hi'
    rw [← pos_mem h12 h23 hA hB hC i hi, ← pos_mem h12 h23 hA' hB' hC' i hi']
    have hpair : FinAct h (A ++ B ++ C)[i] (A' ++ B' ++ C')[i] := by
      have := (List.forall₂_iff_get.mp hF).2 i hi hi'
      simpa using this
    constructor
    · intro hp; rw [← fixed_pair hfix hpair (Or.inl hp)]; exact hp
    · intro hp; rw [fixed_pair hfix hpair (Or.inr hp)]; exact hp
  have hb : 0 < B.length := List.length_pos_iff.mpr hBne
  have hb' : 0 < B'.length := List.length_pos_iff.mpr hB'ne
  simp only [List.length_append] at hlen
  have e1 : A.length = A'.length := by
    have k1 := key A'.length (by simp; omega) (by simp; omega)
    have k2 := key A.length (by simp; omega) (by simp; omega)
    omega
  have e2 : A.length + B.length = A'.length + B'.length := by
    have k1 := key (A.length + B.length - 1) (by simp; omega) (by simp; omega)
    have k2 := key (A'.length + B'.length - 1) (by simp; omega) (by simp; omega)
    omega
  constructor
  · have := List.forall₂_take A.length hF
    rwa [List.append_assoc, List.take_left' rfl, List.append_assoc, List.take_left' e1.symm]
      at this
  · have := List.forall₂_drop (A.length + B.length) hF
    rwa [List.drop_left' (by simp), List.drop_left' (by simp; omega)] at this

theorem refine_dom {h : SeqGroup} {D R : BT} (H : TP h D R) (S : BT) :
    ∃ SB R', TP h (S.graft SB) R' := by
  obtain ⟨SA, SB, hA, -, e⟩ := exists_common D S
  exact ⟨SB, R.graft SA, e ▸ H.refine SA hA⟩

theorem refine_cod {h : SeqGroup} {D R : BT} (H : TP h D R) (S : BT) :
    ∃ SA SB, TP h (D.graft SA) (S.graft SB) := by
  obtain ⟨SA, SB, hA, -, e⟩ := exists_common R S
  exact ⟨SA, SB, e ▸ H.refine SA (by rw [hA, H.size_eq])⟩

theorem graft_node3 (X Y Z : BT) (SB : List BT) :
    ∃ X' Y' Z', (node X (node Y Z)).graft SB = node X' (node Y' Z') := ⟨_, _, _, rfl⟩

theorem exists_TP3 {h : SeqGroup} (hh : h ∈ F) :
    ∃ X Y Z X' Y' Z', TP h (node X (node Y Z)) (node X' (node Y' Z')) := by
  obtain ⟨D, R, H⟩ := exists_TP hh
  obtain ⟨SB, R', H1⟩ := refine_dom H (node leaf (node leaf leaf))
  obtain ⟨X, Y, Z, e⟩ := graft_node3 leaf leaf leaf SB
  rw [e] at H1
  obtain ⟨SA, SB', H2⟩ := refine_cod H1 (node leaf (node leaf leaf))
  obtain ⟨X', Y', Z', e'⟩ := graft_node3 leaf leaf leaf SB'
  obtain ⟨X1, Y1, Z1, e1⟩ := graft_node3 X Y Z SA
  rw [e', e1] at H2
  exact ⟨_, _, _, _, _, _, H2⟩

theorem leaves_node3_nil (X Y Z : BT) :
    (node X (node Y Z)).leaves [] =
      X.leaves [false] ++ Y.leaves [true, false] ++ Z.leaves [true, true] := by
  simp [leaves]

theorem stab10 {h : SeqGroup} (hh : h ∈ F) (hfix : FinAct h [true, false] [true, false]) :
    ∃ k0 ∈ Loc [false], ∃ k11 ∈ Loc [true, true], h = k0 * k11 := by
  obtain ⟨X, Y, Z, X', Y', Z', H⟩ := exists_TP3 hh
  have hF : List.Forall₂ (FinAct h) (X.leaves [false] ++ Y.leaves [true, false] ++
      Z.leaves [true, true]) (X'.leaves [false] ++ Y'.leaves [true, false] ++
        Z'.leaves [true, true]) := by
    simpa only [TP, leaves_node3_nil] using H
  have i0_10 : Incompatible [false] [true, false] := incompat_cons (by decide) [] [false]
  have i10_11 : Incompatible [true, false] [true, true] :=
    incompat_append [true] (incompat_cons (by decide) [] [])
  have i0_11 : Incompatible [false] [true, true] := incompat_cons (by decide) [] [true]
  obtain ⟨hA, hC⟩ := block3 i0_10 i10_11 hfix
    (prefix_of_mem_leaves _ _) (prefix_of_mem_leaves _ _) (prefix_of_mem_leaves _ _)
    (prefix_of_mem_leaves _ _) (prefix_of_mem_leaves _ _) (prefix_of_mem_leaves _ _)
    (leaves_ne_nil _ _) (leaves_ne_nil _ _) hF
  have hszA : X.size = X'.size := by
    have := hA.length_eq; rw [length_leaves, length_leaves] at this; omega
  have hszC : Z.size = Z'.size := by
    have := hC.length_eq; rw [length_leaves, length_leaves] at this; omega
  obtain ⟨k0, hk0, hk0F⟩ := tp_in_loc X X' [false] hszA
  obtain ⟨k11, hk11, hk11F⟩ := tp_in_loc Z Z' [true, true] hszC
  have s0 := supp_of_mem_loc hk0
  have s11 := supp_of_mem_loc hk11
  refine ⟨k0, hk0, k11, hk11, eq_of_agree (node X (node Y Z)) ?_⟩
  intro ℓ hℓ
  rw [leaves_node3_nil, List.mem_append, List.mem_append] at hℓ
  rcases hℓ with (hℓ | hℓ) | hℓ
  · obtain ⟨m, hm, h1, h2⟩ := f2_exists_mem (f2_and hA hk0F) ℓ hℓ
    exact ⟨m, h1, finAct_mul h2 (finAct_of_supp s11
      (incompat_of_prefix ⟨i0_11.2, i0_11.1⟩ (prefix_of_mem_leaves _ _ m hm)))⟩
  · obtain ⟨w, rfl⟩ := prefix_of_mem_leaves _ _ ℓ hℓ
    refine ⟨_, finAct_append hfix w, finAct_mul (finAct_of_supp s0 ?_) (finAct_of_supp s11 ?_)⟩
    · exact incompat_of_prefix i0_10 (List.prefix_append _ _)
    · exact incompat_of_prefix ⟨i10_11.2, i10_11.1⟩ (List.prefix_append _ _)
  · obtain ⟨m, h1, h2⟩ := f2_exists (f2_and hC hk11F) ℓ hℓ
    refine ⟨m, h1, finAct_mul (finAct_of_supp s0 ?_) h2⟩
    exact incompat_of_prefix i0_11 (prefix_of_mem_leaves _ _ ℓ hℓ)

/-! ## The abstract Tietze argument -/

theorem tietze_ev {α T : Type} {rels : Set (FreeGroup α)} {val : α → SeqGroup}
    {H : Subgroup SeqGroup}
    (phi : PresentedGroup rels →* SeqGroup) (hphi : ∀ g, phi (PresentedGroup.of g) = val g)
    (hinj : Function.Injective phi) (hrange : phi.range = H)
    (ι : T → α) (R' : Set (FreeGroup T))
    (hR'val : ∀ r ∈ R', FreeGroup.lift (val ∘ ι) r = 1)
    (θ : α → PresentedGroup R')
    (hθι : ∀ τ, θ (ι τ) = PresentedGroup.of τ)
    (hθrel : ∀ r ∈ rels, FreeGroup.lift θ r = 1)
    (hθval : ∀ a, PresentedGroup.toGroup hR'val (θ a) = val a) :
    Function.Injective (PresentedGroup.toGroup hR'val) ∧
      (PresentedGroup.toGroup hR'val).range = H := by
  let ψ : PresentedGroup rels →* PresentedGroup R' := PresentedGroup.toGroup hθrel
  have hcomp : phi.comp (FreeGroup.lift fun τ => (PresentedGroup.of (ι τ) :
      PresentedGroup rels)) = FreeGroup.lift (val ∘ ι) := by
    ext τ; simp [hphi]
  have hφrel : ∀ r ∈ R', FreeGroup.lift (fun τ => (PresentedGroup.of (ι τ) :
      PresentedGroup rels)) r = 1 := by
    intro r hr
    apply hinj
    rw [map_one, ← MonoidHom.comp_apply, hcomp, hR'val r hr]
  let φ : PresentedGroup R' →* PresentedGroup rels := PresentedGroup.toGroup hφrel
  have h1 : ψ.comp φ = MonoidHom.id _ := by
    apply PresentedGroup.ext; intro τ
    simp [φ, ψ, PresentedGroup.toGroup.of, hθι]
  have hev : phi.comp φ = PresentedGroup.toGroup hR'val := by
    apply PresentedGroup.ext; intro τ
    simp [φ, PresentedGroup.toGroup.of, hphi]
  have h2 : φ.comp ψ = MonoidHom.id _ := by
    apply PresentedGroup.ext; intro a
    apply hinj
    have : phi (φ (θ a)) = val a := by
      rw [← MonoidHom.comp_apply phi φ, hev, hθval]
    simpa [ψ, PresentedGroup.toGroup.of, hphi] using this
  rw [← hev]
  refine ⟨hinj.comp (fun u v huv => ?_), ?_⟩
  · have := congrArg ψ huv
    rwa [← MonoidHom.comp_apply ψ φ, ← MonoidHom.comp_apply ψ φ, h1] at this
  · rw [← hrange, MonoidHom.range_comp]
    have : φ.range = ⊤ := by
      rw [MonoidHom.range_eq_top]
      intro y; exact ⟨ψ y, by rw [← MonoidHom.comp_apply φ ψ, h2]; rfl⟩
    rw [this, ← MonoidHom.range_eq_map]

/-! ## A homomorphism from `F` out of the finite presentation of `F` -/

/-- `A ↦ x0`, `B ↦ x1`. -/
def abMap {Q : Type*} (x0 x1 : Q) : CannonFloydParry.FormalAB → Q
  | .A => x0
  | .B => x1

theorem exists_kappa {Q : Type*} [Group Q] (x0 x1 : Q)
    (hrel : ∀ r ∈ CannonFloydParry.relsF1, FreeGroup.lift (abMap x0 x1) r = 1) :
    ∃ κ : ↥F →* Q, κ ⟨xs [], xs_mem_F []⟩ = x0 ∧ κ ⟨xs [true], xs_mem_F [true]⟩ = x1 := by
  obtain ⟨-, e, he⟩ := exists_presentation_F_and_mulEquiv_F2
  have hβ : ∀ r ∈ CannonFloydParry.relsF2, FreeGroup.lift CannonFloydParry.Y r = 1 := by
    rintro r ⟨k, n, hkn, rfl⟩
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [CannonFloydParry.Y_conj_eq_Y_succ k n hkn, mul_inv_cancel]
  let β : CannonFloydParry.F2 →* CannonFloydParry.F1 := PresentedGroup.toGroup hβ
  let γ : CannonFloydParry.F1 →* Q := PresentedGroup.toGroup hrel
  refine ⟨γ.comp (β.comp e.symm.toMonoidHom), ?_, ?_⟩
  · have : (⟨xs [], xs_mem_F []⟩ : ↥F) = e (PresentedGroup.of 0) := by
      apply Subtype.ext; rw [he 0]; rfl
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, MulEquiv.symm_apply_apply]
    simp [β, γ, PresentedGroup.toGroup.of, CannonFloydParry.Y, abMap]
  · have : (⟨xs [true], xs_mem_F [true]⟩ : ↥F) = e (PresentedGroup.of 1) := by
      apply Subtype.ext; rw [he 1]; rfl
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, MulEquiv.symm_apply_apply]
    simp [β, γ, PresentedGroup.toGroup.of, CannonFloydParry.Y, abMap]

theorem commute_of_fix_supp {f g : SeqGroup} {p : Seq} (hf : FinAct f p p) (hg : Supp g p) :
    Commute f g := by
  apply MulOpposite.unop_injective
  refine Equiv.ext fun ξ => ?_
  simp only [MulOpposite.unop_mul, Equiv.Perm.mul_apply]
  by_cases hp : Cyl p ξ
  · obtain ⟨η, rfl⟩ := hp
    obtain ⟨η', hη'⟩ := supp_cyl hg (cyl_append_self p η)
    rw [hf, hη', hf]
  · have hp' : ¬ Cyl p (MulOpposite.unop f ξ) := by
      rintro ⟨η, hη⟩
      rw [← hf η] at hη
      exact hp ⟨η, (MulOpposite.unop f).injective hη⟩
    rw [hg ξ hp, hg _ hp']

/-! ## Facts about the action used in the presentation -/

theorem finAct_of_xFin {s t t' : Seq} (h : xFin s t = some t') : FinAct (xs s) t t' := by
  unfold xFin at h
  split_ifs at h with h1 h2
  · obtain ⟨d, rfl⟩ := h1
    rw [List.drop_left] at h
    match d, h with
    | false :: false :: r, h => cases h; exact finAct_x00 s r
    | false :: true :: r, h => cases h; exact finAct_x01 s r
    | true :: r, h => cases h; exact finAct_x1 s r
  · cases h; exact finAct_of_supp (supp_xs s) ⟨h1, h2⟩

theorem F_fix_const (b : Bool) {h : SeqGroup} (hh : h ∈ F) :
    MulOpposite.unop h (Stream'.const b) = Stream'.const b := by
  induction hh using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨s, rfl⟩ := hg
      rw [unop_xs, xSeq]
      by_cases hc : Cyl s (Stream'.const b)
      · obtain ⟨η, hη⟩ := hc
        have hη' : η = Stream'.const b := by
          have := congrArg (Stream'.drop s.length) hη
          rw [Stream'.drop_append_stream, Stream'.drop_const] at this
          exact this.symm
        subst hη'
        rw [hη, localize_append_self]
        congr 1
        cases b <;> funext n <;> cases n <;> rfl
      · exact localize_of_not_cyl hc _
  | one => rfl
  | mul g h _ _ ihg ihh => rw [MulOpposite.unop_mul, Equiv.Perm.mul_apply, ihg, ihh]
  | inv g _ ih => rw [MulOpposite.unop_inv, Equiv.Perm.inv_eq_iff_eq, ih]

theorem append_const_of_finAct {g : SeqGroup} (hg : g ∈ F) {u u' : Seq} (h : FinAct g u u')
    (b : Bool) (hu : u ++ₛ Stream'.const b = Stream'.const b) :
    u' ++ₛ Stream'.const b = Stream'.const b := by
  rw [← h, hu, F_fix_const b hg]

theorem nil_of_finAct_nil {g : SeqGroup} (hg : g ∈ F) {u : Seq} (h : FinAct g [] u) : u = [] := by
  have h0 := append_const_of_finAct hg h false rfl
  have h1 := append_const_of_finAct hg h true rfl
  rcases u with _ | ⟨a, u⟩
  · rfl
  · have e0 := congrFun h0 0
    have e1 := congrFun h1 0
    change a = false at e0
    change a = true at e1
    rw [e0] at e1; cases e1

theorem rep_unique {g : SeqGroup} (hg : g ∈ F) {u u' : Seq} (hu : IsBase u) (hu' : IsBase u')
    (h : FinAct g u u') : u = u' := by
  have hgi : g⁻¹ ∈ F := inv_mem hg
  have hi := finAct_inv h
  have e0 : [false] ++ₛ Stream'.const false = Stream'.const false := by
    funext n; cases n <;> rfl
  have e1 : [true] ++ₛ Stream'.const true = Stream'.const true := by
    funext n; cases n <;> rfl
  have f0 : ∀ {k : SeqGroup}, k ∈ F → ∀ {v : Seq}, FinAct k [false] v →
      v ++ₛ Stream'.const false = Stream'.const false :=
    fun hk _ hv => append_const_of_finAct hk hv false e0
  have f1 : ∀ {k : SeqGroup}, k ∈ F → ∀ {v : Seq}, FinAct k [true] v →
      v ++ₛ Stream'.const true = Stream'.const true :=
    fun hk _ hv => append_const_of_finAct hk hv true e1
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hu' with rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | exact (nil_of_finAct_nil hg h).symm
    | exact (nil_of_finAct_nil hgi hi)
    | exact absurd (congrFun (f0 hg h) 0) (by decide)
    | exact absurd (congrFun (f1 hg h) 0) (by decide)
    | exact absurd (congrFun (f1 hg h) 1) (by decide)
    | exact absurd (congrFun (f0 hgi hi) 0) (by decide)
    | exact absurd (congrFun (f1 hgi hi) 1) (by decide)

theorem incompat_split : ∀ {s t : Seq}, Incompatible s t →
    (∃ p s' t', s = p ++ false :: s' ∧ t = p ++ true :: t') ∨
      (∃ p s' t', s = p ++ true :: s' ∧ t = p ++ false :: t')
  | [], _, h => absurd List.nil_prefix h.1
  | _ :: _, [], h => absurd List.nil_prefix h.2
  | a :: s, b :: t, h => by
      by_cases hab : a = b
      · subst hab
        have h' : Incompatible s t :=
          ⟨fun h' => h.1 (List.cons_prefix_cons.mpr ⟨rfl, h'⟩),
            fun h' => h.2 (List.cons_prefix_cons.mpr ⟨rfl, h'⟩)⟩
        rcases incompat_split h' with ⟨p, s', t', rfl, rfl⟩ | ⟨p, s', t', rfl, rfl⟩
        · exact Or.inl ⟨a :: p, s', t', rfl, rfl⟩
        · exact Or.inr ⟨a :: p, s', t', rfl, rfl⟩
      · cases a <;> cases b <;> simp at hab
        · exact Or.inl ⟨[], s, t, rfl, rfl⟩
        · exact Or.inr ⟨[], s, t, rfl, rfl⟩

theorem incompat_of_finAct {g : SeqGroup} {a b a' b' : Seq} (h : FinAct g a b)
    (h' : FinAct g a' b') (hb : Incompatible b b') : Incompatible a a' := by
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · obtain ⟨w, rfl⟩ := ha
    have := finAct_unique h' (finAct_append h w)
    exact hb.1 ⟨w, this.symm⟩
  · obtain ⟨w, rfl⟩ := ha
    have := finAct_unique h (finAct_append h' w)
    exact hb.2 ⟨w, this.symm⟩

/-! ## Representatives and conjugators -/

theorem lemmaS0 (s : Seq) : ∃ g : ↥F, ∃ u, IsBase u ∧ FinAct (g : SeqGroup) u s := by
  obtain ⟨g, hg, u, hu, h⟩ := lemmaS [] s
  exact ⟨⟨g, loc_le_F _ (loc3_le_loc _ hg)⟩, u, hu, by simpa using h⟩

noncomputable def conjOf (s : Seq) : ↥F := (lemmaS0 s).choose

noncomputable def repOf (s : Seq) : Seq := (lemmaS0 s).choose_spec.choose

theorem repOf_base (s : Seq) : IsBase (repOf s) := (lemmaS0 s).choose_spec.choose_spec.1

theorem finAct_conjOf (s : Seq) : FinAct (conjOf s : SeqGroup) (repOf s) s :=
  (lemmaS0 s).choose_spec.choose_spec.2

/-! ## The relations, in any group receiving `F` -/

section Generic

variable {Q : Type*} [Group Q] (κ : ↥F →* Q) (Yof : Seq → Q)

/-- The image of `y_s`. -/
noncomputable def θy (s : Seq) : Q := (κ (conjOf s))⁻¹ * Yof (repOf s) * κ (conjOf s)

/-- The image of `x_s`. -/
noncomputable def θx (s : Seq) : Q := κ ⟨xs s, xs_mem_F s⟩

theorem θy_conj (s0 s : Seq) (g : ↥F) (h : FinAct (g : SeqGroup) s0 s)
    (hK : ∀ k : ↥F, FinAct (k : SeqGroup) (repOf s) (repOf s) →
      Commute (κ k) (Yof (repOf s))) :
    θy κ Yof s = (κ g)⁻¹ * θy κ Yof s0 * κ g := by
  set c0 := conjOf s0
  set c := conjOf s
  have h0 := finAct_conjOf s0
  have h1 := finAct_conjOf s
  have hk : FinAct ((c0 * g * c⁻¹ : ↥F) : SeqGroup) (repOf s0) (repOf s) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact finAct_mul (finAct_mul h0 h) (finAct_inv h1)
  have hu : repOf s0 = repOf s :=
    rep_unique (c0 * g * c⁻¹).2 (repOf_base s0) (repOf_base s) hk
  rw [hu] at hk
  have hc := (hK _ hk).eq
  unfold θy
  rw [hu]
  set Y := Yof (repOf s)
  simp only [map_mul, map_inv] at hc
  set B := κ c0 * κ g * (κ c)⁻¹
  have hB : B⁻¹ * Y * B = Y := by
    rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
  have e : κ c0 * κ g = B * κ c := by simp [B]
  calc (κ c)⁻¹ * Y * κ c = (κ c)⁻¹ * (B⁻¹ * Y * B) * κ c := by rw [hB]
    _ = (B * κ c)⁻¹ * Y * (B * κ c) := by group
    _ = (κ c0 * κ g)⁻¹ * Y * (κ c0 * κ g) := by rw [e]
    _ = (κ g)⁻¹ * ((κ c0)⁻¹ * Y * κ c0) * κ g := by group

variable (P : Seq → Prop)

theorem θx_conj (s0 s : Seq) (g : ↥F) (h : FinAct (g : SeqGroup) s0 s) :
    θx κ s = (κ g)⁻¹ * θx κ s0 * κ g := by
  unfold θx
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (xs_conj h).symm

/-- The images of all generators. -/
noncomputable def θgen : Gen → Q
  | .x s => θx κ s
  | .y s => θy κ Yof s

/-- `P` holds for the index of every `y`-generator. -/
def GenP (P : Seq → Prop) : Gen → Prop
  | .x _ => True
  | .y s => P s

theorem θx_mul_eq {a b c d : Seq} (h : xs a * xs b = xs c * xs d) :
    θx κ a * θx κ b = θx κ c * θx κ d := by
  unfold θx
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h

theorem rels_hold
    (hP : ∀ (g : ↥F) s0 s, FinAct (g : SeqGroup) s0 s → (P s0 ↔ P s))
    (hK : ∀ s, P s → ∀ k : ↥F, FinAct (k : SeqGroup) (repOf s) (repOf s) →
      Commute (κ k) (Yof (repOf s)))
    (hShort : ∀ s t, s.length ≤ 3 → t.length ≤ 3 → Incompatible s t → P s → P t →
      Commute (θy κ Yof s) (θy κ Yof t))
    (hFive : ∀ u, IsBase u → P u → P (u ++ [false]) → P (u ++ [true, false]) →
      P (u ++ [true, true]) →
      θy κ Yof u = θx κ u * θy κ Yof (u ++ [false]) * (θy κ Yof (u ++ [true, false]))⁻¹ *
        θy κ Yof (u ++ [true, true]))
    (r : Rel) (hr : ∀ g ∈ r.gens, GenP P g) :
    FreeGroup.lift (θgen κ Yof) (r.lhs * r.rhs⁻¹) = 1 := by
  rw [map_mul, map_inv, mul_inv_eq_one]
  cases r with
  | one s =>
      simp only [Rel.lhs, Rel.rhs, map_mul, FreeGroup.lift_apply_of, θgen]
      have h := rel_one s
      unfold θx
      rw [← map_mul, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h
  | two s t t' h =>
      simp only [Rel.lhs, Rel.rhs, map_mul, FreeGroup.lift_apply_of, θgen]
      exact θx_mul_eq κ (xs_mul_eq (finAct_of_xFin h))
  | three s t t' h =>
      simp only [Rel.lhs, Rel.rhs, map_mul, FreeGroup.lift_apply_of, θgen]
      have ht' : P t' := hr (.y t') (by simp [Rel.gens])
      rw [θy_conj κ Yof t t' ⟨xs s, xs_mem_F s⟩ (finAct_of_xFin h) (hK t' ht')]
      unfold θx
      group
  | four s t h =>
      simp only [Rel.lhs, Rel.rhs, map_mul, FreeGroup.lift_apply_of, θgen]
      have hs : P s := hr (.y s) (by simp [Rel.gens])
      have ht : P t := hr (.y t) (by simp [Rel.gens])
      suffices key : ∀ s t, Incompatible s t → Good s t → P s → P t →
          Commute (θy κ Yof s) (θy κ Yof t) by
        rcases incompat_split h with ⟨p, s', t', rfl, rfl⟩ | ⟨p, s', t', rfl, rfl⟩
        · exact (key _ _ h (good_split p s' t') hs ht).eq
        · exact (key _ _ ⟨h.2, h.1⟩ (good_split p t' s') ht hs).eq.symm
      intro s t h hgood hs ht
      obtain ⟨g, hg, s0, t0, -, hs0, ht0, h1, h2⟩ := hgood
      have hinc : Incompatible s0 t0 := incompat_of_finAct h1 h2 h
      have hs0P : P s0 := (hP ⟨g, hg⟩ s0 s h1).2 hs
      have ht0P : P t0 := (hP ⟨g, hg⟩ t0 t h2).2 ht
      rw [θy_conj κ Yof s0 s ⟨g, hg⟩ h1 (hK s hs), θy_conj κ Yof t0 t ⟨g, hg⟩ h2 (hK t ht)]
      have hc := (hShort s0 t0 hs0 ht0 hinc hs0P ht0P).eq
      have : (κ ⟨g, hg⟩)⁻¹ * θy κ Yof s0 * κ ⟨g, hg⟩ * ((κ ⟨g, hg⟩)⁻¹ * θy κ Yof t0 * κ ⟨g, hg⟩)
          = (κ ⟨g, hg⟩)⁻¹ * (θy κ Yof s0 * θy κ Yof t0) * κ ⟨g, hg⟩ := by group
      rw [Commute, SemiconjBy, this, hc]
      group
  | five s =>
      simp only [Rel.lhs, Rel.rhs, map_mul, map_inv, FreeGroup.lift_apply_of, θgen]
      have hs : P s := hr (.y s) (by simp [Rel.gens])
      have hs0 : P (s ++ [false]) := hr (.y _) (by simp [Rel.gens])
      have hs10 : P (s ++ [true, false]) := hr (.y _) (by simp [Rel.gens])
      have hs11 : P (s ++ [true, true]) := hr (.y _) (by simp [Rel.gens])
      set c := conjOf s
      set u := repOf s
      have hc : FinAct (c : SeqGroup) u s := finAct_conjOf s
      have hu : P u := (hP c u s hc).2 hs
      have hu0 := (hP c _ _ (finAct_append hc [false])).2 hs0
      have hu10 := (hP c _ _ (finAct_append hc [true, false])).2 hs10
      have hu11 := (hP c _ _ (finAct_append hc [true, true])).2 hs11
      rw [θy_conj κ Yof u s c hc (hK s hs),
        θy_conj κ Yof (u ++ [false]) (s ++ [false]) c (finAct_append hc _) (hK _ hs0),
        θy_conj κ Yof (u ++ [true, false]) (s ++ [true, false]) c (finAct_append hc _)
          (hK _ hs10),
        θy_conj κ Yof (u ++ [true, true]) (s ++ [true, true]) c (finAct_append hc _) (hK _ hs11),
        θx_conj κ u s c hc, hFive u (repOf_base s) hu hu0 hu10 hu11]
      group

end Generic

/-! ## Words in `x`, `x₁` -/

/-- `x` and `x₁`, indexed by `Bool`. -/
noncomputable def xx1 : Bool → SeqGroup := fun d => if d then xs [true] else xs []

theorem exists_word {g : SeqGroup} (hg : g ∈ F) :
    ∃ w : FreeGroup Bool, FreeGroup.lift xx1 w = g := by
  rw [← closure_eq_F] at hg
  have hr : Set.range xx1 = {xs [], xs [true]} := by
    ext g; constructor
    · rintro ⟨d, rfl⟩; cases d <;> simp [xx1]
    · rintro (rfl | rfl)
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
  rw [← hr, ← FreeGroup.range_lift_eq_closure] at hg
  exact hg

open Classical in
/-- A word in `x`, `x₁` for an element of `F`. -/
noncomputable def wordOf (g : SeqGroup) : FreeGroup Bool :=
  if h : g ∈ F then (exists_word h).choose else 1

theorem lift_wordOf {g : SeqGroup} (hg : g ∈ F) : FreeGroup.lift xx1 (wordOf g) = g := by
  unfold wordOf; rw [dif_pos hg]; exact (exists_word hg).choose_spec

/-- Words in `x`, `x₁` as elements of `F`. -/
noncomputable def liftF : FreeGroup Bool →* ↥F :=
  FreeGroup.lift fun d => if d then ⟨xs [true], xs_mem_F _⟩ else ⟨xs [], xs_mem_F _⟩

theorem coe_liftF (w : FreeGroup Bool) : (liftF w : SeqGroup) = FreeGroup.lift xx1 w := by
  have : F.subtype.comp liftF = FreeGroup.lift xx1 := by
    ext d; cases d <;> simp [liftF, xx1]
  exact congrArg (fun φ : FreeGroup Bool →* SeqGroup => φ w) this

theorem toGroup_mk {T G : Type*} [Group G] {R' : Set (FreeGroup T)} {f : T → G}
    (h : ∀ r ∈ R', FreeGroup.lift f r = 1) (w : FreeGroup T) :
    PresentedGroup.toGroup h (PresentedGroup.mk R' w) = FreeGroup.lift f w := by
  have : (PresentedGroup.toGroup h).comp (PresentedGroup.mk R') = FreeGroup.lift f := by
    ext t
    show PresentedGroup.toGroup h (PresentedGroup.of t) = _
    rw [PresentedGroup.toGroup.of, FreeGroup.lift_apply_of]
  exact congrArg (fun φ : FreeGroup T →* G => φ w) this

theorem commute_of_mem_closure {Q : Type*} [Group Q] (κ : ↥F →* Q) (Y : Q) (C : Set SeqGroup)
    (hC : C ⊆ F) (hc : ∀ c (h : c ∈ C), Commute (κ ⟨c, hC h⟩) Y) (k : ↥F)
    (hk : (k : SeqGroup) ∈ Subgroup.closure C) : Commute (κ k) Y := by
  let S : Subgroup SeqGroup := ((Subgroup.centralizer {Y}).comap κ).map F.subtype
  have hle : Subgroup.closure C ≤ S := by
    rw [Subgroup.closure_le]
    intro c h
    refine ⟨⟨c, hC h⟩, ?_, rfl⟩
    show κ ⟨c, hC h⟩ ∈ Subgroup.centralizer {Y}
    rw [Subgroup.mem_centralizer_iff]
    rintro y rfl
    exact (hc c h).eq.symm
  obtain ⟨k', hk', e⟩ := hle hk
  have : k' = k := Subtype.ext e
  subst this
  have hk'' : κ k' ∈ Subgroup.centralizer {Y} := hk'
  rw [Subgroup.mem_centralizer_iff] at hk''
  exact (hk'' Y rfl).symm

theorem loc_le_closure2 (q : Seq) : Loc q ≤ Subgroup.closure {xs q, xs (q ++ [true])} := by
  rw [Loc, Subgroup.closure_le]
  rintro g ⟨w, rfl⟩
  exact xs_mem_closure2 q w

theorem rel_five (s : Seq) :
    ys s = xs s * ys (s ++ [false]) * (ys (s ++ [true, false]))⁻¹ * ys (s ++ [true, true]) := by
  have h := bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R.2 _ ⟨Rel.five s, rfl⟩
  simp only [Rel.lhs, Rel.rhs, map_mul, map_inv, FreeGroup.lift_apply_of, Gen.val] at h
  exact mul_inv_eq_one.mp h

theorem θy_rep {Q : Type*} [Group Q] (κ : ↥F →* Q) (Yof : Seq → Q) {u : Seq} (hu : IsBase u)
    (hK : ∀ k : ↥F, FinAct (k : SeqGroup) u u → Commute (κ k) (Yof u)) :
    θy κ Yof u = Yof u := by
  have hr : repOf u = u := rep_unique (conjOf u).2 (repOf_base u) hu (finAct_conjOf u)
  have h := finAct_conjOf u
  rw [hr] at h
  unfold θy
  rw [hr, mul_assoc, ← (hK _ h).eq, ← mul_assoc, inv_mul_cancel, one_mul]

/-! ## `G` is finitely presented -/

inductive TG
  | x | x1 | y | y0 | y1 | y10
  deriving DecidableEq

instance : Fintype TG := ⟨{.x, .x1, .y, .y0, .y1, .y10}, fun t => by cases t <;> simp⟩

/-! ## `G₀` is finitely presented -/

theorem isConst_of_append_const {s : Seq} {b : Bool}
    (h : s ++ₛ Stream'.const b = Stream'.const b) : IsConst s := by
  have key : ∀ i (hi : i < s.length), s[i]? = some b := by
    intro i hi
    rw [List.getElem?_eq_getElem hi]
    congr 1
    have := congrArg (fun ξ => Stream'.get ξ i) h
    simp only [Stream'.get_const] at this
    rw [Stream'.get_append_left _ _ _ hi] at this
    exact this
  intro i hi j hj
  rw [key i hi, key j hj]

theorem append_const_of_isConst {s : Seq} (hs : IsConst s) (hne : s ≠ []) :
    ∃ b, s ++ₛ Stream'.const b = Stream'.const b := by
  have h0 : 0 < s.length := List.length_pos_iff.mpr hne
  refine ⟨s[0], ?_⟩
  apply Stream'.ext
  intro n
  rw [Stream'.get_const]
  by_cases hn : n < s.length
  · rw [Stream'.get_append_left _ _ _ hn]
    have := hs n hn 0 h0
    rw [List.getElem?_eq_getElem hn, List.getElem?_eq_getElem h0] at this
    exact Option.some.inj this
  · obtain ⟨k, rfl⟩ : ∃ k, n = s.length + k := ⟨n - s.length, by omega⟩
    rw [Stream'.get_append_right, Stream'.get_const]

theorem isConst_of_finAct {g : SeqGroup} (hg : g ∈ F) {s0 s : Seq} (h : FinAct g s0 s)
    (hc : IsConst s0) : IsConst s := by
  by_cases hne : s0 = []
  · subst hne
    rw [nil_of_finAct_nil hg h]
    intro i hi; simp at hi
  · obtain ⟨b, hb⟩ := append_const_of_isConst hc hne
    exact isConst_of_append_const (append_const_of_finAct hg h b hb)

theorem nonconst10 : ¬ IsConst [true, false] := fun h => by
  have := h 0 (by simp) 1 (by simp); simp at this

theorem isConst_short {s : Seq} (h : s = [] ∨ s = [false] ∨ s = [true]) : IsConst s := by
  rcases h with rfl | rfl | rfl <;> intro i hi j hj <;> simp at hi hj <;> subst hi hj <;> rfl

theorem repOf_nonconst {s : Seq} (hs : ¬ IsConst s) : repOf s = [true, false] := by
  rcases repOf_base s with h | h | h | h
  · exact absurd (isConst_of_finAct (conjOf s).2 (finAct_conjOf s) (isConst_short (by simp [h])))
      hs
  · exact absurd (isConst_of_finAct (conjOf s).2 (finAct_conjOf s) (isConst_short (by simp [h])))
      hs
  · exact absurd (isConst_of_finAct (conjOf s).2 (finAct_conjOf s) (isConst_short (by simp [h])))
      hs
  · exact h

inductive TG0
  | x | x1 | y10
  deriving DecidableEq

instance : Fintype TG0 := ⟨{.x, .x1, .y10}, fun t => by cases t <;> simp⟩

/-- The values of the generators of `S₀`. -/
noncomputable def val0 (g : GenS0) : SeqGroup := g.1.val

theorem nc_100 : ¬ IsConst [true, false, false] := fun h => by
  have := h 0 (by simp) 1 (by simp); simp at this
theorem nc_1010 : ¬ IsConst [true, false, true, false] := fun h => by
  have := h 0 (by simp) 1 (by simp); simp at this
theorem nc_1011 : ¬ IsConst [true, false, true, true] := fun h => by
  have := h 0 (by simp) 1 (by simp); simp at this

/-! ## Nonconstant incompatible pairs: two `F`-orbits -/

/-- `(u, v)` is the image under `F` of `(01, 10)` or of `(001, 10)`. -/
def Good2 (u v : Seq) : Prop :=
  ∃ g ∈ F, (FinAct g [false, true] u ∧ FinAct g [true, false] v) ∨
    (FinAct g [false, false, true] u ∧ FinAct g [true, false] v)

theorem good2_trans {u v u' v' : Seq} (h : Good2 u v) {k : SeqGroup} (hk : k ∈ F)
    (hu : FinAct k u u') (hv : FinAct k v v') : Good2 u' v' := by
  obtain ⟨g, hg, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ := h
  · exact ⟨g * k, mul_mem hg hk, Or.inl ⟨finAct_mul h1 hu, finAct_mul h2 hv⟩⟩
  · exact ⟨g * k, mul_mem hg hk, Or.inr ⟨finAct_mul h1 hu, finAct_mul h2 hv⟩⟩

theorem nonconst_of_finAct {g : SeqGroup} (hg : g ∈ F) {s0 s : Seq} (h : FinAct g s0 s)
    (hs : ¬ IsConst s) : ¬ IsConst s0 := fun hc => hs (isConst_of_finAct hg h hc)

theorem isConst_00 : IsConst [false, false] := by
  intro i hi j hj; simp at hi hj; interval_cases i <;> interval_cases j <;> rfl

theorem isConst_11 : IsConst [true, true] := by
  intro i hi j hj; simp at hi hj; interval_cases i <;> interval_cases j <;> rfl

theorem good2_T (U V : Seq) (hU : ¬ IsConst (false :: U)) (hV : ¬ IsConst (true :: V)) :
    Good2 (false :: U) (true :: V) := by
  obtain ⟨g1, hg1, U0, hU0, h1⟩ := lemmaS [false] U
  obtain ⟨g2, hg2, V0, hV0, h2⟩ := lemmaS [true] V
  have hg1F := loc_le_F _ (loc3_le_loc _ hg1)
  have hg2F := loc_le_F _ (loc3_le_loc _ hg2)
  have hU0' : ¬ IsConst (false :: U0) := nonconst_of_finAct hg1F h1 hU
  have hV0' : ¬ IsConst (true :: V0) := nonconst_of_finAct hg2F h2 hV
  have i0_10 : Incompatible [false] [true, false] := incompat_cons (by decide) [] [false]
  have i0_110 : Incompatible [false] [true, true, false] := incompat_cons (by decide) [] _
  have base : Good2 (false :: U0) (true :: V0) := by
    rcases hU0 with rfl | rfl | rfl | rfl
    · exact absurd (isConst_short (by simp)) hU0'
    · exact absurd isConst_00 hU0'
    · rcases hV0 with rfl | rfl | rfl | rfl
      · exact absurd (isConst_short (by simp)) hV0'
      · exact ⟨1, one_mem _, Or.inl ⟨finAct_one _, finAct_one _⟩⟩
      · exact absurd isConst_11 hV0'
      · exact ⟨xs [], xs_mem_F _, Or.inr ⟨by simpa using finAct_x00 [] [true],
          by simpa using finAct_x1 [] [false]⟩⟩
    · rcases hV0 with rfl | rfl | rfl | rfl
      · exact absurd (isConst_short (by simp)) hV0'
      · exact ⟨xs [false], xs_mem_F _, Or.inr ⟨by simpa using finAct_x01 [false] [],
          finAct_of_supp (supp_xs _) i0_10⟩⟩
      · exact absurd isConst_11 hV0'
      · refine ⟨(xs [false])⁻¹ * xs [] * xs [false],
          mul_mem (mul_mem (inv_mem (xs_mem_F _)) (xs_mem_F _)) (xs_mem_F _), Or.inr ⟨?_, ?_⟩⟩
        · have e1 : FinAct (xs [false])⁻¹ [false, false, true] [false, false, false, true] := by
            simpa using finAct_inv (finAct_x00 [false] [true])
          have e2 : FinAct (xs []) [false, false, false, true] [false, false, true] := by
            simpa using finAct_x00 [] [false, true]
          have e3 : FinAct (xs [false]) [false, false, true] [false, true, false] := by
            simpa using finAct_x01 [false] []
          exact finAct_mul (finAct_mul e1 e2) e3
        · have e1 : FinAct (xs [false])⁻¹ [true, false] [true, false] :=
            finAct_of_supp (supp_inv (supp_xs _)) i0_10
          have e2 : FinAct (xs []) [true, false] [true, true, false] := by
            simpa using finAct_x1 [] [false]
          have e3 : FinAct (xs [false]) [true, true, false] [true, true, false] :=
            finAct_of_supp (supp_xs _) i0_110
          exact finAct_mul (finAct_mul e1 e2) e3
  refine good2_trans base (k := g1 * g2) (mul_mem hg1F hg2F) ?_ ?_
  · exact finAct_mul h1 (finAct_of_supp (supp_of_mem_loc (loc3_le_loc _ hg2))
      (incompat_cons (by decide) [] U))
  · exact finAct_mul (finAct_of_supp (supp_of_mem_loc (loc3_le_loc _ hg1))
      (incompat_cons Bool.false_ne_true [] V0)) h2

theorem good2_P0 (U V : Seq) (hs : ¬ IsConst (false :: false :: U))
    (ht : ¬ IsConst (false :: true :: V)) : Good2 (false :: false :: U) (false :: true :: V) :=
  good2_trans (good2_T U (false :: V)
      (nonconst_of_finAct (inv_mem (xs_mem_F [])) (finAct_inv (finAct_x00 [] U)) hs)
      (nonconst_of_finAct (inv_mem (xs_mem_F [])) (finAct_inv (finAct_x01 [] V)) ht))
    (inv_mem (xs_mem_F [])) (finAct_inv (finAct_x00 [] U)) (finAct_inv (finAct_x01 [] V))

theorem good2_P1 (U V : Seq) (hs : ¬ IsConst (true :: false :: U))
    (ht : ¬ IsConst (true :: true :: V)) : Good2 (true :: false :: U) (true :: true :: V) :=
  good2_trans (good2_T (true :: U) V
      (nonconst_of_finAct (xs_mem_F []) (finAct_x01 [] U) hs)
      (nonconst_of_finAct (xs_mem_F []) (finAct_x1 [] V) ht))
    (xs_mem_F []) (finAct_x01 [] U) (finAct_x1 [] V)

theorem good2_P10 (U V : Seq) (hs : ¬ IsConst (true :: false :: false :: U))
    (ht : ¬ IsConst (true :: false :: true :: V)) :
    Good2 (true :: false :: false :: U) (true :: false :: true :: V) := by
  have h1 : FinAct (xs [true])⁻¹ (true :: false :: U) (true :: false :: false :: U) := by
    simpa using finAct_inv (finAct_x00 [true] U)
  have h2 : FinAct (xs [true])⁻¹ (true :: true :: false :: V) (true :: false :: true :: V) := by
    simpa using finAct_inv (finAct_x01 [true] V)
  exact good2_trans (good2_P1 U (false :: V)
      (nonconst_of_finAct (inv_mem (xs_mem_F _)) h1 hs)
      (nonconst_of_finAct (inv_mem (xs_mem_F _)) h2 ht))
    (inv_mem (xs_mem_F _)) h1 h2

theorem good2_split (p U V : Seq) (hs : ¬ IsConst (p ++ false :: U))
    (ht : ¬ IsConst (p ++ true :: V)) : Good2 (p ++ false :: U) (p ++ true :: V) := by
  obtain ⟨g, hg, p0, hp0, h⟩ := lemmaS [] p
  simp only [List.nil_append] at h
  have hgF : g ∈ F := loc_le_F _ (loc3_le_loc _ hg)
  have hs0 := nonconst_of_finAct hgF (finAct_append h (false :: U)) hs
  have ht0 := nonconst_of_finAct hgF (finAct_append h (true :: V)) ht
  have key : Good2 (p0 ++ false :: U) (p0 ++ true :: V) := by
    rcases hp0 with rfl | rfl | rfl | rfl
    · exact good2_T U V hs0 ht0
    · exact good2_P0 U V hs0 ht0
    · exact good2_P1 U V hs0 ht0
    · exact good2_P10 U V hs0 ht0
  exact good2_trans key hgF (finAct_append h _) (finAct_append h _)

/-! ## The nine relations of p. 7 -/

def ι9 : ABC → GenS0
  | .a => ⟨.x [], trivial⟩
  | .b => ⟨.x [true], trivial⟩
  | .c => ⟨.y [true, false], nonconst10⟩

theorem sx0 : xs [false] = xs [] * xs [] * (xs [true])⁻¹ * (xs [])⁻¹ := by
  have e := rel_one []
  simp only [List.nil_append] at e
  rw [e]; group

theorem sx11 : xs [true, true] = (xs [])⁻¹ * xs [true] * xs [] := by
  have h : (xs [])⁻¹ * xs [true] * xs [] = xs [true, true] := by
    simpa using xs_conj (finAct_x1 [] [])
  exact h.symm

theorem sx111 : xs [true, true, true] = (xs [])⁻¹ * (xs [])⁻¹ * xs [true] * xs [] * xs [] := by
  have e : (xs [])⁻¹ * xs [true, true] * xs [] = xs [true, true, true] := by
    simpa using xs_conj (finAct_x1 [] [true])
  rw [← e, sx11]; group

theorem sx10 : xs [true, false] =
    xs [true] * xs [true] * (xs [])⁻¹ * (xs [true])⁻¹ * xs [] * (xs [true])⁻¹ := by
  have e := rel_one [true]
  simp only [List.cons_append, List.nil_append] at e
  have : xs [true, false] = xs [true] * xs [true] * (xs [true, true])⁻¹ * (xs [true])⁻¹ := by
    rw [e]; group
  rw [this, sx11]; group

theorem sx01 : xs [false, true] = xs [] * xs [true, false] * (xs [])⁻¹ := by
  have e : (xs [])⁻¹ * xs [false, true] * xs [] = xs [true, false] := by
    simpa using xs_conj (finAct_x01 [] [])
  rw [← e]; group

theorem sy01 : ys [false, true] = xs [] * ys [true, false] * (xs [])⁻¹ := by
  have e : (xs [])⁻¹ * ys [false, true] * xs [] = ys [true, false] := by
    simpa using ys_conj (finAct_x01 [] [])
  rw [← e]; group

theorem sy001 : ys [false, false, true] = xs [] * xs [] * ys [true, false] * (xs [])⁻¹ *
    (xs [])⁻¹ := by
  have e : (xs [])⁻¹ * ys [false, false, true] * xs [] = ys [false, true] := by
    simpa using ys_conj (finAct_x00 [] [true])
  have h : ys [false, false, true] = xs [] * ys [false, true] * (xs [])⁻¹ := by
    rw [← e]; group
  rw [h, sy01]; group

theorem fa100 : FinAct (xs [true])⁻¹ [true, false] [true, false, false] := by
  simpa using finAct_inv (finAct_x00 [true] [])

theorem fa1010 : FinAct ((xs [true])⁻¹ * xs [] * (xs [true])⁻¹) [true, false]
    [true, false, true, false] := by
  have e2 : FinAct (xs []) [true, false, false] [true, true, false, false] := by
    simpa using finAct_x1 [] [false, false]
  have e3 : FinAct (xs [true])⁻¹ [true, true, false, false] [true, false, true, false] := by
    simpa using finAct_inv (finAct_x01 [true] [false])
  exact finAct_mul (finAct_mul fa100 e2) e3

theorem fa1011 : FinAct (xs [] * (xs [true])⁻¹ * xs [] * (xs [true])⁻¹) [true, false]
    [true, false, true, true] := by
  have e1 : FinAct (xs []) [true, false] [true, true, false] := by
    simpa using finAct_x1 [] [false]
  have e2 : FinAct (xs [true])⁻¹ [true, true, false] [true, false, true] := by
    simpa using finAct_inv (finAct_x01 [true] [])
  have e3 : FinAct (xs []) [true, false, true] [true, true, false, true] := by
    simpa using finAct_x1 [] [false, true]
  have e4 : FinAct (xs [true])⁻¹ [true, true, false, true] [true, false, true, true] := by
    simpa using finAct_inv (finAct_x01 [true] [true])
  exact finAct_mul (finAct_mul (finAct_mul e1 e2) e3) e4

theorem fa01 : FinAct (xs [])⁻¹ [true, false] [false, true] := by
  simpa using finAct_inv (finAct_x01 [] [])

theorem fa001 : FinAct ((xs [])⁻¹ * (xs [])⁻¹) [true, false] [false, false, true] :=
  finAct_mul fa01 (by simpa using finAct_inv (finAct_x00 [] [true]))

theorem comm_x1x_x11 : Commute (xs [true] * (xs [])⁻¹) ((xs [])⁻¹ * xs [true] * xs []) := by
  have hfix : FinAct (xs [] * (xs [true])⁻¹) [true, true] [true, true] :=
    finAct_mul (finAct_x1 [] [true]) (by simpa using finAct_inv (finAct_x1 [true] []))
  have c := (commute_of_fix_supp hfix (supp_xs [true, true])).inv_left
  rw [← sx11]; simpa using c

theorem comm_x1x_x111 :
    Commute (xs [true] * (xs [])⁻¹) ((xs [])⁻¹ * (xs [])⁻¹ * xs [true] * xs [] * xs []) := by
  have hfix : FinAct (xs [] * (xs [true])⁻¹) [true, true] [true, true] :=
    finAct_mul (finAct_x1 [] [true]) (by simpa using finAct_inv (finAct_x1 [true] []))
  have c := (commute_of_fix_supp hfix (supp_mono (supp_xs [true, true, true])
    ⟨[true], rfl⟩)).inv_left
  rw [← sx111]; simpa using c

theorem nine_val : ∀ r ∈ nineRels, FreeGroup.lift (val0 ∘ ι9) r = 1 := by
  have va : (val0 ∘ ι9) ABC.a = xs [] := rfl
  have vb : (val0 ∘ ι9) ABC.b = xs [true] := rfl
  have vc : (val0 ∘ ι9) ABC.c = ys [true, false] := rfl
  have i10_0 : Incompatible [true, false] [false] := incompat_cons (by decide) _ _
  intro r hr
  simp only [nineRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, va, vb, vc, pow_two] <;>
    rw [mul_inv_eq_one]
  · have := comm_x1x_x11.eq
    calc _ = xs [true] * (xs [])⁻¹ * ((xs [])⁻¹ * xs [true] * xs []) := by group
      _ = _ := by rw [this] ; group
  · have := comm_x1x_x111.eq
    calc _ = xs [true] * (xs [])⁻¹ * ((xs [])⁻¹ * (xs [])⁻¹ * xs [true] * xs [] * xs []) := by
          group
      _ = _ := by rw [this] ; group
  · have c := commute_of_supp (supp_ys [true, false]) (supp_xs [false]) i10_0
    rw [sx0] at c
    calc _ = ys [true, false] * (xs [] * xs [] * (xs [true])⁻¹ * (xs [])⁻¹) := by group
      _ = _ := by rw [c.eq]
  · have c := commute_of_supp (supp_ys [true, false]) (supp_xs [false, true])
      (incompat_cons (by decide) _ _)
    rw [sx01, sx10] at c
    calc _ = ys [true, false] * (xs [] * (xs [true] * xs [true] * (xs [])⁻¹ * (xs [true])⁻¹ *
          xs [] * (xs [true])⁻¹) * (xs [])⁻¹) := by group
      _ = _ := by rw [c.eq] ; group
  · have c := commute_of_supp (supp_ys [true, false]) (supp_xs [true, true])
      (incompat_append [true] (incompat_cons (by decide) _ _))
    rw [sx11] at c
    calc _ = ys [true, false] * ((xs [])⁻¹ * xs [true] * xs []) := by group
      _ = _ := by rw [c.eq]
  · have c := commute_of_supp (supp_ys [true, false]) (supp_xs [true, true, true])
      (incompat_append [true] (incompat_cons (by decide) _ _))
    rw [sx111] at c
    calc _ = ys [true, false] * ((xs [])⁻¹ * (xs [])⁻¹ * xs [true] * xs [] * xs []) := by group
      _ = _ := by rw [c.eq] ; group
  · have c := commute_of_supp (supp_ys [true, false]) (supp_ys [false, true])
      (incompat_cons (by decide) _ _)
    rw [sy01] at c
    calc _ = ys [true, false] * (xs [] * ys [true, false] * (xs [])⁻¹) := by group
      _ = _ := by rw [c.eq]
  · have c := commute_of_supp (supp_ys [true, false]) (supp_ys [false, false, true])
      (incompat_cons (by decide) _ _)
    rw [sy001] at c
    calc _ = ys [true, false] * (xs [] * xs [] * ys [true, false] * (xs [])⁻¹ * (xs [])⁻¹) := by
          group
      _ = _ := by rw [c.eq] ; group
  · have e := rel_five [true, false]
    simp only [List.cons_append, List.nil_append] at e
    rw [← ys_conj fa100, ← ys_conj fa1010, ← ys_conj fa1011, sx10] at e
    exact e.trans (by group)

theorem kappa_liftF {Q : Type*} [Group Q] (κ : ↥F →* Q) (w : FreeGroup Bool) :
    κ (liftF w) = FreeGroup.lift
      (fun d => if d then κ ⟨xs [true], xs_mem_F _⟩ else κ ⟨xs [], xs_mem_F _⟩) w := by
  have : κ.comp liftF = FreeGroup.lift
      (fun d => if d then κ ⟨xs [true], xs_mem_F _⟩ else κ ⟨xs [], xs_mem_F _⟩) := by
    ext d; cases d <;> simp [liftF]
  exact congrArg (fun φ : FreeGroup Bool →* Q => φ w) this

theorem mk_eq_liftF {g : SeqGroup} (hg : g ∈ F) (w : FreeGroup Bool)
    (hw : FreeGroup.lift xx1 w = g) : (⟨g, hg⟩ : ↥F) = liftF w :=
  Subtype.ext (by rw [coe_liftF, hw])

/-- The G₀ half of Theorem 3.3 (statement 27, imported as a statement: 27 does not rest on 19). -/
theorem R0S_presents_G0Seq : ∃ phi : PresentedGroup R0S →* SeqGroup,
    (∀ g, phi (PresentedGroup.of g) = g.1.val) ∧ Function.Injective phi ∧ phi.range = G0Seq :=
  presentation_G_G0Seq_and_isFinitelyPresented.2.1

theorem nine_presents : Function.Injective (PresentedGroup.toGroup nine_val) ∧
    (PresentedGroup.toGroup nine_val).range = G0Seq := by
  obtain ⟨psi, hpsi, hinj, hrange⟩ := R0S_presents_G0Seq
  set A : PresentedGroup nineRels := PresentedGroup.mk nineRels (FreeGroup.of ABC.a) with hA
  set B : PresentedGroup nineRels := PresentedGroup.mk nineRels (FreeGroup.of ABC.b) with hB
  set C : PresentedGroup nineRels := PresentedGroup.mk nineRels (FreeGroup.of ABC.c) with hC
  -- the nine relations in the presented group
  have m1 : _ ∈ nineRels := Or.inl rfl
  have m2 : _ ∈ nineRels := Or.inr (Or.inl rfl)
  have m3 : _ ∈ nineRels := Or.inr (Or.inr (Or.inl rfl))
  have m4 : _ ∈ nineRels := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have m5 : _ ∈ nineRels := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have m6 : _ ∈ nineRels := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have m7 : _ ∈ nineRels := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have m8 : _ ∈ nineRels :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have m9 : _ ∈ nineRels :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  have e1 := PresentedGroup.one_of_mem m1
  have e2 := PresentedGroup.one_of_mem m2
  have e3 := PresentedGroup.one_of_mem m3
  have e4 := PresentedGroup.one_of_mem m4
  have e5 := PresentedGroup.one_of_mem m5
  have e6 := PresentedGroup.one_of_mem m6
  have e7 := PresentedGroup.one_of_mem m7
  have e8 := PresentedGroup.one_of_mem m8
  have e9 := PresentedGroup.one_of_mem m9
  simp only [map_mul, map_inv, map_pow, ← hA, ← hB, ← hC, mul_inv_eq_one]
    at e1 e2 e3 e4 e5 e6 e7 e8 e9
  clear m1 m2 m3 m4 m5 m6 m7 m8 m9
  -- `F` maps in
  have c1 : Commute (A * B⁻¹) (A⁻¹ * B * A) := by
    have : Commute (B * A⁻¹) (A⁻¹ * B * A) := by
      show B * A⁻¹ * (A⁻¹ * B * A) = A⁻¹ * B * A * (B * A⁻¹)
      calc _ = B * A⁻¹ ^ 2 * B * A := by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
        _ = A⁻¹ * B * A * B * A⁻¹ := e1
        _ = _ := by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
    simpa using this.inv_left
  have c2 : Commute (A * B⁻¹) (A⁻¹ ^ 2 * B * A ^ 2) := by
    have : Commute (B * A⁻¹) (A⁻¹ ^ 2 * B * A ^ 2) := by
      show B * A⁻¹ * (A⁻¹ ^ 2 * B * A ^ 2) = A⁻¹ ^ 2 * B * A ^ 2 * (B * A⁻¹)
      calc _ = B * A⁻¹ * A⁻¹ ^ 2 * B * A ^ 2 := by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
        _ = A⁻¹ ^ 2 * B * A ^ 2 * B * A⁻¹ := e2
        _ = _ := by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
    simpa using this.inv_left
  have hrelF1 : ∀ r ∈ CannonFloydParry.relsF1, FreeGroup.lift (abMap A B) r = 1 := by
    intro r hr
    simp only [CannonFloydParry.relsF1, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, abMap]
      rw [c1.eq]; (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
    · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, abMap]
      rw [c2.eq]; (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
  obtain ⟨κ, hκx, hκx1⟩ := exists_kappa A B hrelF1
  have hκw : ∀ (g : SeqGroup) (hg : g ∈ F) (w : FreeGroup Bool), FreeGroup.lift xx1 w = g →
      κ ⟨g, hg⟩ = FreeGroup.lift (fun d => if d then B else A) w := by
    intro g hg w hw
    rw [mk_eq_liftF hg w hw, kappa_liftF, hκx, hκx1]
  have kx0 : κ ⟨xs [false], xs_mem_F _⟩ = A * A * B⁻¹ * A⁻¹ := by
    rw [hκw _ _ (.of false * .of false * (.of true)⁻¹ * (.of false)⁻¹) (by simp [xx1, sx0])]
    simp
  have kx01 : κ ⟨xs [false, true], xs_mem_F _⟩ = A * (B * B * A⁻¹ * B⁻¹ * A * B⁻¹) * A⁻¹ := by
    rw [hκw _ _ (.of false * (.of true * .of true * (.of false)⁻¹ * (.of true)⁻¹ * .of false *
      (.of true)⁻¹) * (.of false)⁻¹) (by simp [xx1, sx01, sx10])]
    simp
  have kx11 : κ ⟨xs [true, true], xs_mem_F _⟩ = A⁻¹ * B * A := by
    rw [hκw _ _ ((.of false)⁻¹ * .of true * .of false) (by simp [xx1, sx11])]
    simp
  have kx111 : κ ⟨xs [true, true, true], xs_mem_F _⟩ = A⁻¹ * A⁻¹ * B * A * A := by
    rw [hκw _ _ ((.of false)⁻¹ * (.of false)⁻¹ * .of true * .of false * .of false)
      (by simp [xx1, sx111])]
    simp
  have kx10 : κ ⟨xs [true, false], xs_mem_F _⟩ = B * B * A⁻¹ * B⁻¹ * A * B⁻¹ := by
    rw [hκw _ _ (.of true * .of true * (.of false)⁻¹ * (.of true)⁻¹ * .of false * (.of true)⁻¹)
      (by simp [xx1, sx10])]
    simp
  -- the stabilizer of `10`
  have hK10 : ∀ k : ↥F, FinAct (k : SeqGroup) [true, false] [true, false] → Commute (κ k) C := by
    intro k hk
    obtain ⟨k0, hk0, k11, hk11, e⟩ := stab10 k.2 hk
    refine commute_of_mem_closure κ _
      {xs [false], xs [false, true], xs [true, true], xs [true, true, true]} ?_ ?_ k ?_
    · rintro c (rfl | rfl | rfl | rfl) <;> exact xs_mem_F _
    · rintro c (rfl | rfl | rfl | rfl)
      · rw [kx0]
        show A * A * B⁻¹ * A⁻¹ * C = C * (A * A * B⁻¹ * A⁻¹)
        calc _ = A ^ 2 * B⁻¹ * A⁻¹ * C := by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
          _ = C * A ^ 2 * B⁻¹ * A⁻¹ := e3.symm
          _ = _ := by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
      · rw [kx01]
        show A * (B * B * A⁻¹ * B⁻¹ * A * B⁻¹) * A⁻¹ * C = C * (A * (B * B * A⁻¹ * B⁻¹ * A *
          B⁻¹) * A⁻¹)
        calc _ = A * B ^ 2 * A⁻¹ * B⁻¹ * A * B⁻¹ * A⁻¹ * C := by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
          _ = C * (A * B ^ 2 * A⁻¹ * B⁻¹ * A * B⁻¹ * A⁻¹) := e4.symm
          _ = _ := by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
      · rw [kx11]
        show A⁻¹ * B * A * C = C * (A⁻¹ * B * A)
        calc _ = A⁻¹ * B * A * C := rfl
          _ = C * A⁻¹ * B * A := e5.symm
          _ = _ := by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
      · rw [kx111]
        show A⁻¹ * A⁻¹ * B * A * A * C = C * (A⁻¹ * A⁻¹ * B * A * A)
        calc _ = A⁻¹ ^ 2 * B * A ^ 2 * C := by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
          _ = C * A⁻¹ ^ 2 * B * A ^ 2 := e6.symm
          _ = _ := by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
    · rw [e]
      refine mul_mem ?_ ?_
      · refine Subgroup.closure_mono ?_ (loc_le_closure2 [false] hk0)
        rintro c (rfl | rfl) <;> simp
      · refine Subgroup.closure_mono ?_ (loc_le_closure2 [true, true] hk11)
        rintro c (rfl | rfl) <;> simp
  let Yof : Seq → PresentedGroup nineRels := fun _ => C
  have hK : ∀ s, ¬ IsConst s → ∀ k : ↥F, FinAct (k : SeqGroup) (repOf s) (repOf s) →
      Commute (κ k) (Yof (repOf s)) := by
    intro s hs k hk
    rw [repOf_nonconst hs] at hk
    exact hK10 k hk
  have hP : ∀ (g : ↥F) s0 s, FinAct (g : SeqGroup) s0 s → (¬ IsConst s0 ↔ ¬ IsConst s) :=
    fun g s0 s h => ⟨fun h0 hc => h0 (isConst_of_finAct (inv_mem g.2) (finAct_inv h) hc),
      fun h0 hc => h0 (isConst_of_finAct g.2 h hc)⟩
  have ty10 : θy κ Yof [true, false] = C := θy_rep κ Yof (Or.inr (Or.inr (Or.inr rfl))) hK10
  have tyconj : ∀ (g : SeqGroup) (hg : g ∈ F) (s : Seq), ¬ IsConst s →
      FinAct g [true, false] s → θy κ Yof s = (κ ⟨g, hg⟩)⁻¹ * C * κ ⟨g, hg⟩ := by
    intro g hg s hs h
    rw [θy_conj κ Yof [true, false] s ⟨g, hg⟩ h (hK s hs), ty10]
  have hxi : (⟨(xs [])⁻¹, inv_mem (xs_mem_F _)⟩ : ↥F) = (⟨xs [], xs_mem_F _⟩)⁻¹ := rfl
  have hx1i : (⟨(xs [true])⁻¹, inv_mem (xs_mem_F _)⟩ : ↥F) = (⟨xs [true], xs_mem_F _⟩)⁻¹ := rfl
  have nc01 : ¬ IsConst [false, true] := fun h => by
    have := h 0 (by simp) 1 (by simp); simp at this
  have nc001 : ¬ IsConst [false, false, true] := fun h => by
    have := h 1 (by simp) 2 (by simp); simp at this
  have ty01 : θy κ Yof [false, true] = A * C * A⁻¹ := by
    rw [tyconj _ (inv_mem (xs_mem_F _)) _ nc01 fa01, hxi, map_inv, hκx]; (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
  have ty001 : θy κ Yof [false, false, true] = A * A * C * A⁻¹ * A⁻¹ := by
    rw [tyconj _ (mul_mem (inv_mem (xs_mem_F _)) (inv_mem (xs_mem_F _))) _ nc001 fa001]
    rw [show (⟨(xs [])⁻¹ * (xs [])⁻¹, mul_mem (inv_mem (xs_mem_F _)) (inv_mem (xs_mem_F _))⟩ :
      ↥F) = (⟨xs [], xs_mem_F _⟩)⁻¹ * (⟨xs [], xs_mem_F _⟩)⁻¹ from rfl, map_mul, map_inv, hκx]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  have ty100 : θy κ Yof [true, false, false] = B * C * B⁻¹ := by
    rw [tyconj _ (inv_mem (xs_mem_F _)) _ nc_100 fa100, hx1i, map_inv, hκx1]; (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
  have ty1010 : θy κ Yof [true, false, true, false] =
      (B⁻¹ * A * B⁻¹)⁻¹ * C * (B⁻¹ * A * B⁻¹) := by
    rw [tyconj _ (mul_mem (mul_mem (inv_mem (xs_mem_F _)) (xs_mem_F _)) (inv_mem (xs_mem_F _)))
      _ nc_1010 fa1010]
    rw [show (⟨(xs [true])⁻¹ * xs [] * (xs [true])⁻¹, mul_mem (mul_mem (inv_mem (xs_mem_F _))
      (xs_mem_F _)) (inv_mem (xs_mem_F _))⟩ : ↥F) = (⟨xs [true], xs_mem_F _⟩)⁻¹ *
        ⟨xs [], xs_mem_F _⟩ * (⟨xs [true], xs_mem_F _⟩)⁻¹ from rfl, map_mul, map_mul, map_inv,
      hκx, hκx1]
  have ty1011 : θy κ Yof [true, false, true, true] =
      (A * B⁻¹ * A * B⁻¹)⁻¹ * C * (A * B⁻¹ * A * B⁻¹) := by
    rw [tyconj _ (mul_mem (mul_mem (mul_mem (xs_mem_F _) (inv_mem (xs_mem_F _))) (xs_mem_F _))
      (inv_mem (xs_mem_F _))) _ nc_1011 fa1011]
    rw [show (⟨xs [] * (xs [true])⁻¹ * xs [] * (xs [true])⁻¹, mul_mem (mul_mem (mul_mem
      (xs_mem_F _) (inv_mem (xs_mem_F _))) (xs_mem_F _)) (inv_mem (xs_mem_F _))⟩ : ↥F) =
        ⟨xs [], xs_mem_F _⟩ * (⟨xs [true], xs_mem_F _⟩)⁻¹ * ⟨xs [], xs_mem_F _⟩ *
          (⟨xs [true], xs_mem_F _⟩)⁻¹ from rfl, map_mul, map_mul, map_mul, map_inv, hκx, hκx1]
  -- relations (4): two orbits
  have hShort : ∀ s t, s.length ≤ 3 → t.length ≤ 3 → Incompatible s t → ¬ IsConst s →
      ¬ IsConst t → Commute (θy κ Yof s) (θy κ Yof t) := by
    have base1 : Commute (θy κ Yof [false, true]) (θy κ Yof [true, false]) := by
      rw [ty01, ty10]
      show A * C * A⁻¹ * C = C * (A * C * A⁻¹)
      calc _ = A * C * A⁻¹ * C := rfl
        _ = C * A * C * A⁻¹ := e7.symm
        _ = _ := by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
    have base2 : Commute (θy κ Yof [false, false, true]) (θy κ Yof [true, false]) := by
      rw [ty001, ty10]
      show A * A * C * A⁻¹ * A⁻¹ * C = C * (A * A * C * A⁻¹ * A⁻¹)
      calc _ = A ^ 2 * C * A⁻¹ ^ 2 * C := by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
        _ = C * A ^ 2 * C * A⁻¹ ^ 2 := e8.symm
        _ = _ := by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
    have key : ∀ s t, Good2 s t → ¬ IsConst s → ¬ IsConst t →
        Commute (θy κ Yof s) (θy κ Yof t) := by
      intro s t hst hs ht
      obtain ⟨g, hg, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ := hst
      · rw [θy_conj κ Yof _ s ⟨g, hg⟩ h1 (hK s hs), θy_conj κ Yof _ t ⟨g, hg⟩ h2 (hK t ht)]
        have := base1.eq
        show _ = _
        calc _ = (κ ⟨g, hg⟩)⁻¹ * (θy κ Yof [false, true] * θy κ Yof [true, false]) *
              κ ⟨g, hg⟩ := by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
          _ = _ := by rw [this]; (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
      · rw [θy_conj κ Yof _ s ⟨g, hg⟩ h1 (hK s hs), θy_conj κ Yof _ t ⟨g, hg⟩ h2 (hK t ht)]
        have := base2.eq
        show _ = _
        calc _ = (κ ⟨g, hg⟩)⁻¹ * (θy κ Yof [false, false, true] * θy κ Yof [true, false]) *
              κ ⟨g, hg⟩ := by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
          _ = _ := by rw [this]; (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group)
    intro s t _ _ h hs ht
    rcases incompat_split h with ⟨p, s', t', rfl, rfl⟩ | ⟨p, s', t', rfl, rfl⟩
    · exact key _ _ (good2_split p s' t' hs ht) hs ht
    · exact (key _ _ (good2_split p t' s' ht hs) ht hs).symm
  -- relation (5) at `10`
  have hFive : ∀ u, IsBase u → ¬ IsConst u → ¬ IsConst (u ++ [false]) →
      ¬ IsConst (u ++ [true, false]) → ¬ IsConst (u ++ [true, true]) →
      θy κ Yof u = θx κ u * θy κ Yof (u ++ [false]) * (θy κ Yof (u ++ [true, false]))⁻¹ *
        θy κ Yof (u ++ [true, true]) := by
    intro u hu hnc _ _ _
    have hu10 : u = [true, false] := by
      rcases hu with h | h | h | h
      · exact absurd (isConst_short (Or.inl h)) hnc
      · exact absurd (isConst_short (Or.inr (Or.inl h))) hnc
      · exact absurd (isConst_short (Or.inr (Or.inr h))) hnc
      · exact h
    subst hu10
    simp only [List.cons_append, List.nil_append]
    rw [ty10, ty100, ty1010, ty1011, θx, kx10]
    exact e9.trans (by (first | (simp only [pow_two]; done) | (simp only [pow_two]; group) | group))
  -- evaluation
  have hevκ : ∀ k : ↥F, PresentedGroup.toGroup nine_val (κ k) = k := by
    intro k
    rw [show k = liftF (wordOf k) from Subtype.ext (by rw [coe_liftF, lift_wordOf k.2]),
      kappa_liftF, hκx, hκx1, coe_liftF]
    have : (PresentedGroup.toGroup nine_val).comp (FreeGroup.lift fun d => if d then B else A) =
        FreeGroup.lift xx1 := by
      ext d; cases d <;> simp [xx1, hA, hB, toGroup_mk, ι9, val0, Gen.val]
    exact congrArg (fun φ : FreeGroup Bool →* SeqGroup => φ (wordOf k)) this
  have hevC : PresentedGroup.toGroup nine_val C = ys [true, false] := by
    rw [hC, toGroup_mk, FreeGroup.lift_apply_of]; rfl
  refine tietze_ev (val := val0) psi hpsi hinj hrange ι9 nineRels nine_val
    (fun g => θgen κ Yof g.1) ?_ ?_ ?_
  · intro τ
    cases τ
    · show θx κ [] = _; exact hκx
    · show θx κ [true] = _; exact hκx1
    · show θy κ Yof [true, false] = _; exact ty10
  · intro r hr
    obtain ⟨rel, hrel, e⟩ := hr
    have : FreeGroup.lift (fun g : GenS0 => θgen κ Yof g.1) r =
        FreeGroup.lift (θgen κ Yof) (FreeGroup.map Subtype.val r) := by
      rw [lift_map_eq]; rfl
    rw [this, ← e]
    refine rels_hold κ Yof (fun s => ¬ IsConst s) hP hK hShort hFive rel ?_
    intro g hg
    have := hrel g hg
    cases g with
    | x s => trivial
    | y s => exact this
  · rintro ⟨g, hg⟩
    cases g with
    | x s =>
        show PresentedGroup.toGroup nine_val (θx κ s) = xs s
        rw [θx, hevκ]
    | y s =>
        show PresentedGroup.toGroup nine_val (θy κ Yof s) = ys s
        have h := finAct_conjOf s
        rw [repOf_nonconst hg] at h
        simp only [θy, Yof, map_mul, map_inv, hevκ, hevC]
        exact ys_conj h

end LodhaMoore.Dev.S3b

namespace LodhaMoore

open LodhaMoore.Dev.S3b

end LodhaMoore
end

section
open LodhaMoore
open LodhaMoore.Dev.S3b
theorem solution :
    ∃ phi : PresentedGroup nineRels →* (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ,
      phi (PresentedGroup.of .a) = MulOpposite.op a ∧
      phi (PresentedGroup.of .b) = MulOpposite.op b ∧
      phi (PresentedGroup.of .c) = MulOpposite.op c ∧ Function.Injective phi ∧
        phi.range = G0.op := by
  obtain ⟨e, ea, eb, ec, -⟩ := exists_mulEquiv_G0_G0Seq_and_semiconj_Phi
  obtain ⟨hinj, hrange⟩ := nine_presents
  set ev := PresentedGroup.toGroup nine_val
  have hmem : ∀ x, ev x ∈ G0Seq := fun x => hrange ▸ ⟨x, rfl⟩
  let ev' : PresentedGroup nineRels →* ↥G0Seq := ev.codRestrict G0Seq hmem
  let ι : (↥G0)ᵐᵒᵖ →* (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ := G0.subtype.op
  refine ⟨ι.comp (e.symm.toMonoidHom.comp ev'), ?_, ?_, ?_, ?_, ?_⟩
  · have : ev' (PresentedGroup.of .a) = e (MulOpposite.op ⟨a, Subgroup.subset_closure (by simp)⟩) :=
      Subtype.ext (by rw [ea]; rfl)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, MulEquiv.symm_apply_apply]
    rfl
  · have : ev' (PresentedGroup.of .b) = e (MulOpposite.op ⟨b, Subgroup.subset_closure (by simp)⟩) :=
      Subtype.ext (by rw [eb]; rfl)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, MulEquiv.symm_apply_apply]
    rfl
  · have : ev' (PresentedGroup.of .c) = e (MulOpposite.op ⟨c, Subgroup.subset_closure (by simp)⟩) :=
      Subtype.ext (by rw [ec]; rfl)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, MulEquiv.symm_apply_apply]
    rfl
  · intro x y hxy
    apply hinj
    have h1 : e.symm (ev' x) = e.symm (ev' y) := by
      apply MulOpposite.unop_injective
      apply Subtype.ext
      exact congrArg MulOpposite.unop hxy
    have h2 := congrArg Subtype.val (e.symm.injective h1)
    exact h2
  · ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact (e.symm (ev' x)).unop.2
    · intro hz
      obtain ⟨x, hx⟩ : e (MulOpposite.op ⟨z.unop, hz⟩) ∈ ev'.range := by
        have hm : ((e (MulOpposite.op ⟨z.unop, hz⟩) : SeqGroup) ∈ ev.range) := by
          rw [hrange]; exact (e (MulOpposite.op ⟨z.unop, hz⟩)).2
        obtain ⟨x, hx⟩ := hm
        exact ⟨x, Subtype.ext hx⟩
      refine ⟨x, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx, MulEquiv.symm_apply_apply]
      rfl
end
