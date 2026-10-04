-- Prove2me | solution 1 for LodhaMoore.isFinitelyPresented_of_presentation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T12:28:03.3259+00:00
-- url     : https://prove2.me/submissions/8855aec2-3eee-4db3-8b76-84915377c33d

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_CannonFloydParry_Presentations
import Theorems.Thm_LodhaMoore_bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R
import Theorems.Thm_LodhaMoore_exists_presentation_F_and_mulEquiv_F2
import Theorems.Thm_CannonFloydParry_Y_conj_eq_Y_succ
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

theorem stab_nil {h : SeqGroup} (hfix : FinAct h [] []) : h = 1 := by
  apply MulOpposite.unop_injective
  refine Equiv.ext fun ξ => ?_
  have := hfix ξ
  simpa using this

theorem refine_dom {h : SeqGroup} {D R : BT} (H : TP h D R) (S : BT) :
    ∃ SB R', TP h (S.graft SB) R' := by
  obtain ⟨SA, SB, hA, -, e⟩ := exists_common D S
  exact ⟨SB, R.graft SA, e ▸ H.refine SA hA⟩

theorem refine_cod {h : SeqGroup} {D R : BT} (H : TP h D R) (S : BT) :
    ∃ SA SB, TP h (D.graft SA) (S.graft SB) := by
  obtain ⟨SA, SB, hA, -, e⟩ := exists_common R S
  exact ⟨SA, SB, e ▸ H.refine SA (by rw [hA, H.size_eq])⟩

theorem graft_node2 (SB : List BT) : ∃ X Y, (node leaf leaf).graft SB = node X Y := ⟨_, _, rfl⟩

theorem graft_node3 (X Y Z : BT) (SB : List BT) :
    ∃ X' Y' Z', (node X (node Y Z)).graft SB = node X' (node Y' Z') := ⟨_, _, _, rfl⟩

theorem exists_TP2 {h : SeqGroup} (hh : h ∈ F) : ∃ X Y R0 R1, TP h (node X Y) (node R0 R1) := by
  obtain ⟨D, R, H⟩ := exists_TP hh
  obtain ⟨SB, R', H1⟩ := refine_dom H (node leaf leaf)
  obtain ⟨X, Y, e⟩ := graft_node2 SB
  rw [e] at H1
  cases R' with
  | leaf => have := H1.size_eq; simp [size] at this
  | node R0 R1 => exact ⟨X, Y, R0, R1, H1⟩

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

theorem leaves_node_nil (X Y : BT) :
    (node X Y).leaves [] = X.leaves [false] ++ Y.leaves [true] := rfl

theorem leaves_node3_nil (X Y Z : BT) :
    (node X (node Y Z)).leaves [] =
      X.leaves [false] ++ Y.leaves [true, false] ++ Z.leaves [true, true] := by
  simp [leaves]

theorem stab0 {h : SeqGroup} (hh : h ∈ F) (hfix : FinAct h [false] [false]) :
    h ∈ Loc [true] := by
  obtain ⟨X, Y, R0, R1, H⟩ := exists_TP2 hh
  have hF : List.Forall₂ (FinAct h) ([] ++ X.leaves [false] ++ Y.leaves [true])
      ([] ++ R0.leaves [false] ++ R1.leaves [true]) := by
    simpa only [TP, leaves_node_nil, List.nil_append] using H
  obtain ⟨-, hC⟩ := block3 (p1 := [true]) (incompat_cons (by decide) [] [])
    (incompat_cons (by decide) [] []) hfix (by simp) (prefix_of_mem_leaves _ _)
    (prefix_of_mem_leaves _ _) (by simp) (prefix_of_mem_leaves _ _) (prefix_of_mem_leaves _ _)
    (leaves_ne_nil _ _) (leaves_ne_nil _ _) hF
  have hsz : Y.size = R1.size := by
    have := hC.length_eq; rw [length_leaves, length_leaves] at this; omega
  obtain ⟨k, hk, hkF⟩ := tp_in_loc Y R1 [true] hsz
  have : h = k := by
    apply eq_of_agree (node X Y)
    intro ℓ hℓ
    rw [leaves_node_nil, List.mem_append] at hℓ
    rcases hℓ with hℓ | hℓ
    · obtain ⟨w, rfl⟩ := prefix_of_mem_leaves _ _ ℓ hℓ
      exact ⟨_, finAct_append hfix w, finAct_of_supp (supp_of_mem_loc hk)
        (incompat_of_prefix (incompat_cons (by decide) [] []) (List.prefix_append _ _))⟩
    · exact f2_exists (f2_and hC hkF) ℓ hℓ
  rw [this]; exact hk

theorem stab1 {h : SeqGroup} (hh : h ∈ F) (hfix : FinAct h [true] [true]) :
    h ∈ Loc [false] := by
  obtain ⟨X, Y, R0, R1, H⟩ := exists_TP2 hh
  have hF : List.Forall₂ (FinAct h) (X.leaves [false] ++ Y.leaves [true] ++ [])
      (R0.leaves [false] ++ R1.leaves [true] ++ []) := by
    simpa only [TP, leaves_node_nil, List.append_nil] using H
  obtain ⟨hA, -⟩ := block3 (p3 := [false]) (incompat_cons (by decide) [] [])
    (incompat_cons (by decide) [] []) hfix (prefix_of_mem_leaves _ _)
    (prefix_of_mem_leaves _ _) (by simp) (prefix_of_mem_leaves _ _)
    (prefix_of_mem_leaves _ _) (by simp) (leaves_ne_nil _ _) (leaves_ne_nil _ _) hF
  have hsz : X.size = R0.size := by
    have := hA.length_eq; rw [length_leaves, length_leaves] at this; omega
  obtain ⟨k, hk, hkF⟩ := tp_in_loc X R0 [false] hsz
  have : h = k := by
    apply eq_of_agree (node X Y)
    intro ℓ hℓ
    rw [leaves_node_nil, List.mem_append] at hℓ
    rcases hℓ with hℓ | hℓ
    · exact f2_exists (f2_and hA hkF) ℓ hℓ
    · obtain ⟨w, rfl⟩ := prefix_of_mem_leaves _ _ ℓ hℓ
      exact ⟨_, finAct_append hfix w, finAct_of_supp (supp_of_mem_loc hk)
        (incompat_of_prefix (incompat_cons (by decide) [] []) (List.prefix_append _ _))⟩
  rw [this]; exact hk

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

theorem fp_of {α T : Type} [Finite T] {rels : Set (FreeGroup α)} {val : α → SeqGroup}
    {H : Subgroup SeqGroup}
    (phi : PresentedGroup rels →* SeqGroup) (hphi : ∀ g, phi (PresentedGroup.of g) = val g)
    (hinj : Function.Injective phi) (hrange : phi.range = H)
    (ι : T → α) (R' : Set (FreeGroup T)) (hR' : R'.Finite)
    (hR'val : ∀ r ∈ R', FreeGroup.lift (val ∘ ι) r = 1)
    (θ : α → PresentedGroup R')
    (hθι : ∀ τ, θ (ι τ) = PresentedGroup.of τ)
    (hθrel : ∀ r ∈ rels, FreeGroup.lift θ r = 1)
    (hθval : ∀ a, PresentedGroup.toGroup hR'val (θ a) = val a) :
    Group.IsFinitelyPresented H := by
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
  let e1 : PresentedGroup R' ≃* PresentedGroup rels := MonoidHom.toMulEquiv φ ψ h1 h2
  let e2 : PresentedGroup rels ≃* phi.range := MonoidHom.ofInjective hinj
  let e3 : phi.range ≃* H := MulEquiv.subgroupCongr hrange
  have : Finite R' := hR'.to_subtype
  exact Group.IsFinitelyPresented.equiv (e1.trans (e2.trans e3))

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

theorem relsF1_hold : ∀ r ∈ CannonFloydParry.relsF1,
    FreeGroup.lift (abMap (xs []) (xs [true])) r = 1 := by
  have e11 : (xs [])⁻¹ * xs [true] * xs [] = xs [true, true] := by
    simpa using xs_conj (finAct_x1 [] [])
  have e111 : (xs [])⁻¹ * xs [true, true] * xs [] = xs [true, true, true] := by
    simpa using xs_conj (finAct_x1 [] [true])
  have hfix : FinAct (xs [] * (xs [true])⁻¹) [true, true] [true, true] :=
    finAct_mul (finAct_x1 [] [true]) (by simpa using finAct_inv (finAct_x1 [true] []))
  have c1 : Commute (xs [] * (xs [true])⁻¹) (xs [true, true]) :=
    commute_of_fix_supp hfix (supp_xs _)
  have c2 : Commute (xs [] * (xs [true])⁻¹) (xs [true, true, true]) :=
    commute_of_fix_supp hfix (supp_mono (supp_xs _) ⟨[true], rfl⟩)
  intro r hr
  simp only [CannonFloydParry.relsF1, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, abMap]
    rw [e11, c1.eq]; group
  · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, abMap]
    have : (xs [])⁻¹ ^ 2 * xs [true] * xs [] ^ 2 = xs [true, true, true] := by
      rw [pow_two, pow_two, ← e111, ← e11]; group
    rw [this, c2.eq]; group

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

theorem kappa_eq_word {Q T : Type*} [Group Q] (κ : ↥F →* Q) (f : T → Q) (tx tx1 : T)
    (hx : κ ⟨xs [], xs_mem_F []⟩ = f tx) (hx1 : κ ⟨xs [true], xs_mem_F [true]⟩ = f tx1)
    (g : ↥F) :
    κ g = FreeGroup.lift f (FreeGroup.map (fun d => if d then tx1 else tx) (wordOf g)) := by
  have hg : g = liftF (wordOf g) := Subtype.ext (by rw [coe_liftF, lift_wordOf g.2])
  have : κ.comp liftF = (FreeGroup.lift f).comp (FreeGroup.map fun d => if d then tx1 else tx) := by
    ext d; cases d <;> simp [liftF, hx, hx1]
  conv_lhs => rw [hg]
  exact congrArg (fun φ : FreeGroup Bool →* Q => φ (wordOf g)) this

theorem lift_map_word {T : Type*} (f : T → SeqGroup) (tx tx1 : T) (hx : f tx = xs [])
    (hx1 : f tx1 = xs [true]) {g : SeqGroup} (hg : g ∈ F) :
    FreeGroup.lift f (FreeGroup.map (fun d => if d then tx1 else tx) (wordOf g)) = g := by
  rw [lift_map_eq]
  have : (f ∘ fun d : Bool => if d then tx1 else tx) = xx1 := by
    funext d; cases d <;> simp [xx1, hx, hx1]
  rw [this, lift_wordOf hg]

theorem mk_eq_lift_of {T : Type*} (R' : Set (FreeGroup T)) (w : FreeGroup T) :
    PresentedGroup.mk R' w = FreeGroup.lift PresentedGroup.of w := by
  have : PresentedGroup.mk R' = FreeGroup.lift PresentedGroup.of := by
    ext t; rfl
  rw [this]

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

/-- The commutator word. -/
def cw {T : Type*} (a b : FreeGroup T) : FreeGroup T := a * b * a⁻¹ * b⁻¹

theorem commute_of_cw {T : Type*} {R' : Set (FreeGroup T)} {a b : FreeGroup T}
    (h : cw a b ∈ R') : Commute (PresentedGroup.mk R' a) (PresentedGroup.mk R' b) := by
  have := PresentedGroup.one_of_mem h
  simp only [cw, map_mul, map_inv] at this
  have e : PresentedGroup.mk R' a * PresentedGroup.mk R' b =
      PresentedGroup.mk R' b * PresentedGroup.mk R' a := by
    calc _ = PresentedGroup.mk R' a * PresentedGroup.mk R' b * (PresentedGroup.mk R' a)⁻¹ *
          (PresentedGroup.mk R' b)⁻¹ * (PresentedGroup.mk R' b * PresentedGroup.mk R' a) := by
            group
      _ = _ := by rw [this, one_mul]
  exact e

theorem cw_eval {T : Type*} (f : T → SeqGroup) {a b : FreeGroup T}
    (h : Commute (FreeGroup.lift f a) (FreeGroup.lift f b)) : FreeGroup.lift f (cw a b) = 1 := by
  simp only [cw, map_mul, map_inv]
  rw [h.eq]; group

theorem finite_short :
    {p : Seq × Seq | p.1.length ≤ 3 ∧ p.2.length ≤ 3 ∧ Incompatible p.1 p.2}.Finite :=
  ((List.finite_length_le Bool 3).prod (List.finite_length_le Bool 3)).subset
    fun _ hp => ⟨hp.1, hp.2.1⟩

theorem finite_base : {u : Seq | IsBase u}.Finite :=
  (Set.toFinite ({[], [false], [true], [true, false]} : Set Seq)).subset
    fun u hu => by rcases hu with rfl | rfl | rfl | rfl <;> simp

/-! ## `G` is finitely presented -/

inductive TG
  | x | x1 | y | y0 | y1 | y10
  deriving DecidableEq

instance : Fintype TG := ⟨{.x, .x1, .y, .y0, .y1, .y10}, fun t => by cases t <;> simp⟩

def ιG : TG → Gen
  | .x => .x []
  | .x1 => .x [true]
  | .y => .y []
  | .y0 => .y [false]
  | .y1 => .y [true]
  | .y10 => .y [true, false]

def jG : Bool → TG := fun d => if d then .x1 else .x

def jABG : CannonFloydParry.FormalAB → TG
  | .A => .x
  | .B => .x1

open Classical in
noncomputable def YwG (u : Seq) : FreeGroup TG :=
  if u = [] then .of .y else if u = [false] then .of .y0 else if u = [true] then .of .y1
  else if u = [true, false] then .of .y10 else 1

noncomputable def wG (g : SeqGroup) : FreeGroup TG := FreeGroup.map jG (wordOf g)

noncomputable def ΘG (s : Seq) : FreeGroup TG :=
  (wG (conjOf s))⁻¹ * YwG (repOf s) * wG (conjOf s)

def KG : Set (Seq × Seq) :=
  {([false], [true]), ([false], [true, true]), ([true], [false]), ([true], [false, true]),
    ([true, false], [false]), ([true, false], [false, true]), ([true, false], [true, true]),
    ([true, false], [true, true, true])}

noncomputable def RG : Set (FreeGroup TG) :=
  FreeGroup.map jABG '' CannonFloydParry.relsF1 ∪
  (fun p : Seq × Seq => cw (YwG p.1) (wG (xs p.2))) '' KG ∪
  (fun p : Seq × Seq => cw (ΘG p.1) (ΘG p.2)) ''
    {p : Seq × Seq | p.1.length ≤ 3 ∧ p.2.length ≤ 3 ∧ Incompatible p.1 p.2} ∪
  (fun u => ΘG u * (wG (xs u) * ΘG (u ++ [false]) * (ΘG (u ++ [true, false]))⁻¹ *
    ΘG (u ++ [true, true]))⁻¹) '' {u | IsBase u}

theorem RG_finite : RG.Finite := by
  refine ((Set.Finite.union ?_ ?_).union ?_).union ?_
  · exact (by simp only [CannonFloydParry.relsF1]; exact Set.toFinite _ :
      CannonFloydParry.relsF1.Finite).image _
  · exact (by simp only [KG]; exact Set.toFinite _ : KG.Finite).image _
  · exact finite_short.image _
  · exact finite_base.image _

theorem evG_w {g : SeqGroup} (hg : g ∈ F) : FreeGroup.lift (Gen.val ∘ ιG) (wG g) = g :=
  lift_map_word _ TG.x TG.x1 rfl rfl hg

theorem evG_Yw {u : Seq} (hu : IsBase u) : FreeGroup.lift (Gen.val ∘ ιG) (YwG u) = ys u := by
  rcases hu with rfl | rfl | rfl | rfl <;> simp [YwG, ιG, Gen.val]

theorem evG_Θ (s : Seq) : FreeGroup.lift (Gen.val ∘ ιG) (ΘG s) = ys s := by
  simp only [ΘG, map_mul, map_inv, evG_w (conjOf s).2, evG_Yw (repOf_base s)]
  exact ys_conj (finAct_conjOf s)

theorem RG_val : ∀ r ∈ RG, FreeGroup.lift (Gen.val ∘ ιG) r = 1 := by
  rintro r (((⟨r, hr, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩) | ⟨u, hu, rfl⟩)
  · rw [lift_map_eq]
    have : ((Gen.val ∘ ιG) ∘ jABG) = abMap (xs []) (xs [true]) := by
      funext a; cases a <;> rfl
    rw [this]; exact relsF1_hold r hr
  · apply cw_eval
    have hb : IsBase p.1 := by
      simp only [KG, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [IsBase]
    rw [evG_Yw hb, evG_w (xs_mem_F _)]
    refine commute_of_supp (supp_ys _) (supp_xs _) ?_
    simp only [KG, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by decide⟩
  · apply cw_eval
    rw [evG_Θ, evG_Θ]
    exact commute_of_supp (supp_ys _) (supp_ys _) hp.2.2
  · simp only [map_mul, map_inv, evG_Θ, evG_w (xs_mem_F _)]
    rw [← rel_five, mul_inv_cancel]

theorem fp_G : (∃ phi : PresentedGroup R →* SeqGroup, (∀ g, phi (PresentedGroup.of g) = g.val) ∧
      Function.Injective phi ∧ phi.range = G) → Group.IsFinitelyPresented G := by
  rintro ⟨phi, hphi, hinj, hrange⟩
  set Q := PresentedGroup RG
  have hrelF1 : ∀ r ∈ CannonFloydParry.relsF1, FreeGroup.lift
      (abMap (PresentedGroup.of TG.x : Q) (PresentedGroup.of TG.x1)) r = 1 := by
    intro r hr
    have : abMap (PresentedGroup.of TG.x : Q) (PresentedGroup.of TG.x1) =
        PresentedGroup.of ∘ jABG := by
      funext a; cases a <;> rfl
    rw [this, ← lift_map_eq, ← mk_eq_lift_of RG]
    exact PresentedGroup.one_of_mem (Or.inl (Or.inl (Or.inl ⟨r, hr, rfl⟩)))
  obtain ⟨κ, hκx, hκx1⟩ := exists_kappa _ _ hrelF1
  let Yof : Seq → Q := fun u => PresentedGroup.mk RG (YwG u)
  have hκw : ∀ g : ↥F, κ g = PresentedGroup.mk RG (wG g) := by
    intro g
    rw [kappa_eq_word κ PresentedGroup.of TG.x TG.x1 hκx hκx1 g, mk_eq_lift_of]
    rfl
  have hθy : ∀ s, θy κ Yof s = PresentedGroup.mk RG (ΘG s) := by
    intro s; simp only [θy, ΘG, map_mul, map_inv, hκw, Yof]
  have hθx : ∀ s, θx κ s = PresentedGroup.mk RG (wG (xs s)) := fun s => hκw _
  -- the stabilizer relations
  have hKc : ∀ p ∈ KG, Commute (κ ⟨xs p.2, xs_mem_F _⟩) (Yof p.1) := by
    intro p hp
    rw [hκw]
    exact (commute_of_cw (R' := RG) (Or.inl (Or.inl (Or.inr ⟨p, hp, rfl⟩)))).symm
  have hK : ∀ s, True → ∀ k : ↥F, FinAct (k : SeqGroup) (repOf s) (repOf s) →
      Commute (κ k) (Yof (repOf s)) := by
    intro s _ k hk
    rcases repOf_base s with hu | hu | hu | hu <;> rw [hu] at hk ⊢
    · have : k = 1 := Subtype.ext (stab_nil hk)
      rw [this, map_one]; exact Commute.one_left _
    · refine commute_of_mem_closure κ _ {xs [true], xs [true, true]} ?_ ?_ k
        (loc_le_closure2 [true] (stab0 k.2 hk))
      · rintro c (rfl | rfl) <;> exact xs_mem_F _
      · rintro c (rfl | rfl)
        · exact hKc ([false], [true]) (by simp [KG])
        · exact hKc ([false], [true, true]) (by simp [KG])
    · refine commute_of_mem_closure κ _ {xs [false], xs [false, true]} ?_ ?_ k
        (loc_le_closure2 [false] (stab1 k.2 hk))
      · rintro c (rfl | rfl) <;> exact xs_mem_F _
      · rintro c (rfl | rfl)
        · exact hKc ([true], [false]) (by simp [KG])
        · exact hKc ([true], [false, true]) (by simp [KG])
    · obtain ⟨k0, hk0, k11, hk11, e⟩ := stab10 k.2 hk
      refine commute_of_mem_closure κ _
        {xs [false], xs [false, true], xs [true, true], xs [true, true, true]} ?_ ?_ k ?_
      · rintro c (rfl | rfl | rfl | rfl) <;> exact xs_mem_F _
      · rintro c (rfl | rfl | rfl | rfl)
        · exact hKc ([true, false], [false]) (by simp [KG])
        · exact hKc ([true, false], [false, true]) (by simp [KG])
        · exact hKc ([true, false], [true, true]) (by simp [KG])
        · exact hKc ([true, false], [true, true, true]) (by simp [KG])
      · rw [e]
        refine mul_mem ?_ ?_
        · refine Subgroup.closure_mono ?_ (loc_le_closure2 [false] hk0)
          rintro c (rfl | rfl) <;> simp
        · refine Subgroup.closure_mono ?_ (loc_le_closure2 [true, true] hk11)
          rintro c (rfl | rfl) <;> simp
  have hKb : ∀ u, IsBase u → ∀ k : ↥F, FinAct (k : SeqGroup) u u → Commute (κ k) (Yof u) := by
    intro u hu k hk
    have hr : repOf u = u := rep_unique (conjOf u).2 (repOf_base u) hu (finAct_conjOf u)
    have := hK u trivial k (by rw [hr]; exact hk)
    rwa [hr] at this
  have hShort : ∀ s t, s.length ≤ 3 → t.length ≤ 3 → Incompatible s t → True → True →
      Commute (θy κ Yof s) (θy κ Yof t) := by
    intro s t hs ht h _ _
    rw [hθy, hθy]
    exact commute_of_cw (Or.inl (Or.inr ⟨(s, t), ⟨hs, ht, h⟩, rfl⟩))
  have hFive : ∀ u, IsBase u → True → True → True → True →
      θy κ Yof u = θx κ u * θy κ Yof (u ++ [false]) * (θy κ Yof (u ++ [true, false]))⁻¹ *
        θy κ Yof (u ++ [true, true]) := by
    intro u hu _ _ _ _
    simp only [hθy, hθx, ← map_mul, ← map_inv]
    exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Or.inr ⟨u, hu, rfl⟩)
  refine fp_of phi hphi hinj hrange ιG RG RG_finite RG_val (θgen κ Yof) ?_ ?_ ?_
  · intro τ
    cases τ
    · show θx κ [] = _; exact hκx
    · show θx κ [true] = _; exact hκx1
    · show θy κ Yof [] = _; rw [θy_rep κ Yof (Or.inl rfl) (hKb _ (Or.inl rfl))]; rfl
    · show θy κ Yof [false] = _
      rw [θy_rep κ Yof (Or.inr (Or.inl rfl)) (hKb _ (Or.inr (Or.inl rfl)))]; rfl
    · show θy κ Yof [true] = _
      rw [θy_rep κ Yof (Or.inr (Or.inr (Or.inl rfl))) (hKb _ (Or.inr (Or.inr (Or.inl rfl))))]
      rfl
    · show θy κ Yof [true, false] = _
      rw [θy_rep κ Yof (Or.inr (Or.inr (Or.inr rfl))) (hKb _ (Or.inr (Or.inr (Or.inr rfl))))]
      rfl
  · rintro r ⟨rel, rfl⟩
    exact rels_hold κ Yof (fun _ => True) (fun _ _ _ _ => Iff.rfl) hK hShort hFive rel
      (fun g _ => by cases g <;> trivial)
  · intro a
    cases a with
    | x s => show PresentedGroup.toGroup RG_val (θx κ s) = xs s
             rw [hθx, toGroup_mk, evG_w (xs_mem_F _)]
    | y s => show PresentedGroup.toGroup RG_val (θy κ Yof s) = ys s
             rw [hθy, toGroup_mk, evG_Θ]

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

def ι0 : TG0 → GenS0
  | .x => ⟨.x [], trivial⟩
  | .x1 => ⟨.x [true], trivial⟩
  | .y10 => ⟨.y [true, false], nonconst10⟩

def j0 : Bool → TG0 := fun d => if d then .x1 else .x

def jAB0 : CannonFloydParry.FormalAB → TG0
  | .A => .x
  | .B => .x1

noncomputable def w0 (g : SeqGroup) : FreeGroup TG0 := FreeGroup.map j0 (wordOf g)

noncomputable def Θ0 (s : Seq) : FreeGroup TG0 :=
  (w0 (conjOf s))⁻¹ * FreeGroup.of TG0.y10 * w0 (conjOf s)

def K0 : Set Seq := {[false], [false, true], [true, true], [true, true, true]}

noncomputable def R0' : Set (FreeGroup TG0) :=
  FreeGroup.map jAB0 '' CannonFloydParry.relsF1 ∪
  (fun w => cw (FreeGroup.of TG0.y10) (w0 (xs w))) '' K0 ∪
  (fun p : Seq × Seq => cw (Θ0 p.1) (Θ0 p.2)) ''
    {p : Seq × Seq | p.1.length ≤ 3 ∧ p.2.length ≤ 3 ∧ Incompatible p.1 p.2 ∧
      ¬ IsConst p.1 ∧ ¬ IsConst p.2} ∪
  {Θ0 [true, false] * (w0 (xs [true, false]) * Θ0 [true, false, false] *
    (Θ0 [true, false, true, false])⁻¹ * Θ0 [true, false, true, true])⁻¹}

theorem R0'_finite : R0'.Finite := by
  refine ((Set.Finite.union ?_ ?_).union ?_).union ?_
  · exact (by simp only [CannonFloydParry.relsF1]; exact Set.toFinite _ :
      CannonFloydParry.relsF1.Finite).image _
  · exact (by simp only [K0]; exact Set.toFinite _ : K0.Finite).image _
  · exact (finite_short.subset fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩).image _
  · exact Set.finite_singleton _

/-- The values of the generators of `S₀`. -/
noncomputable def val0 (g : GenS0) : SeqGroup := g.1.val

theorem ev0_w {g : SeqGroup} (hg : g ∈ F) : FreeGroup.lift (val0 ∘ ι0) (w0 g) = g :=
  lift_map_word _ TG0.x TG0.x1 rfl rfl hg

theorem ev0_Θ {s : Seq} (hs : ¬ IsConst s) : FreeGroup.lift (val0 ∘ ι0) (Θ0 s) = ys s := by
  simp only [Θ0, map_mul, map_inv, ev0_w (conjOf s).2, FreeGroup.lift_apply_of]
  have h := finAct_conjOf s
  rw [repOf_nonconst hs] at h
  exact ys_conj h

theorem nc_100 : ¬ IsConst [true, false, false] := fun h => by
  have := h 0 (by simp) 1 (by simp); simp at this
theorem nc_1010 : ¬ IsConst [true, false, true, false] := fun h => by
  have := h 0 (by simp) 1 (by simp); simp at this
theorem nc_1011 : ¬ IsConst [true, false, true, true] := fun h => by
  have := h 0 (by simp) 1 (by simp); simp at this

theorem R0'_val : ∀ r ∈ R0', FreeGroup.lift (val0 ∘ ι0) r = 1 := by
  rintro r (((⟨r, hr, rfl⟩ | ⟨w, hw, rfl⟩) | ⟨p, hp, rfl⟩) | hr)
  · rw [lift_map_eq]
    have : ((val0 ∘ ι0) ∘ jAB0) = abMap (xs []) (xs [true]) := by
      funext a; cases a <;> rfl
    rw [this]; exact relsF1_hold r hr
  · apply cw_eval
    rw [ev0_w (xs_mem_F _), FreeGroup.lift_apply_of]
    refine commute_of_supp (supp_ys _) (supp_xs _) ?_
    simp only [K0, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  · apply cw_eval
    rw [ev0_Θ hp.2.2.2.1, ev0_Θ hp.2.2.2.2]
    exact commute_of_supp (supp_ys _) (supp_ys _) hp.2.2.1
  · rw [Set.mem_singleton_iff] at hr
    subst hr
    simp only [map_mul, map_inv, ev0_Θ nonconst10, ev0_Θ nc_100, ev0_Θ nc_1010, ev0_Θ nc_1011,
      ev0_w (xs_mem_F _)]
    have := rel_five [true, false]
    simp only [List.cons_append, List.nil_append] at this
    rw [← this, mul_inv_cancel]

theorem fp_G0 : (∃ phi : PresentedGroup R0S →* SeqGroup,
      (∀ g, phi (PresentedGroup.of g) = g.1.val) ∧ Function.Injective phi ∧
        phi.range = G0Seq) → Group.IsFinitelyPresented G0Seq := by
  rintro ⟨phi, hphi, hinj, hrange⟩
  set Q := PresentedGroup R0'
  have hrelF1 : ∀ r ∈ CannonFloydParry.relsF1, FreeGroup.lift
      (abMap (PresentedGroup.of TG0.x : Q) (PresentedGroup.of TG0.x1)) r = 1 := by
    intro r hr
    have : abMap (PresentedGroup.of TG0.x : Q) (PresentedGroup.of TG0.x1) =
        PresentedGroup.of ∘ jAB0 := by
      funext a; cases a <;> rfl
    rw [this, ← lift_map_eq, ← mk_eq_lift_of R0']
    exact PresentedGroup.one_of_mem (Or.inl (Or.inl (Or.inl ⟨r, hr, rfl⟩)))
  obtain ⟨κ, hκx, hκx1⟩ := exists_kappa _ _ hrelF1
  let Yof : Seq → Q := fun _ => PresentedGroup.of TG0.y10
  have hκw : ∀ g : ↥F, κ g = PresentedGroup.mk R0' (w0 g) := by
    intro g
    rw [kappa_eq_word κ PresentedGroup.of TG0.x TG0.x1 hκx hκx1 g, mk_eq_lift_of]
    rfl
  have hθy : ∀ s, θy κ Yof s = PresentedGroup.mk R0' (Θ0 s) := by
    intro s; simp only [θy, Θ0, map_mul, map_inv, hκw, Yof]; rfl
  have hθx : ∀ s, θx κ s = PresentedGroup.mk R0' (w0 (xs s)) := fun s => hκw _
  have hKc : ∀ w ∈ K0, Commute (κ ⟨xs w, xs_mem_F _⟩) (PresentedGroup.of TG0.y10 : Q) := by
    intro w hw
    rw [hκw]
    exact (commute_of_cw (R' := R0') (Or.inl (Or.inl (Or.inr ⟨w, hw, rfl⟩)))).symm
  have hK10 : ∀ k : ↥F, FinAct (k : SeqGroup) [true, false] [true, false] →
      Commute (κ k) (PresentedGroup.of TG0.y10 : Q) := by
    intro k hk
    obtain ⟨k0, hk0, k11, hk11, e⟩ := stab10 k.2 hk
    refine commute_of_mem_closure κ _
      {xs [false], xs [false, true], xs [true, true], xs [true, true, true]} ?_ ?_ k ?_
    · rintro c (rfl | rfl | rfl | rfl) <;> exact xs_mem_F _
    · rintro c (rfl | rfl | rfl | rfl)
      · exact hKc [false] (by simp [K0])
      · exact hKc [false, true] (by simp [K0])
      · exact hKc [true, true] (by simp [K0])
      · exact hKc [true, true, true] (by simp [K0])
    · rw [e]
      refine mul_mem ?_ ?_
      · refine Subgroup.closure_mono ?_ (loc_le_closure2 [false] hk0)
        rintro c (rfl | rfl) <;> simp
      · refine Subgroup.closure_mono ?_ (loc_le_closure2 [true, true] hk11)
        rintro c (rfl | rfl) <;> simp
  have hK : ∀ s, ¬ IsConst s → ∀ k : ↥F, FinAct (k : SeqGroup) (repOf s) (repOf s) →
      Commute (κ k) (Yof (repOf s)) := by
    intro s hs k hk
    rw [repOf_nonconst hs] at hk
    exact hK10 k hk
  have hP : ∀ (g : ↥F) s0 s, FinAct (g : SeqGroup) s0 s → (¬ IsConst s0 ↔ ¬ IsConst s) :=
    fun g s0 s h => ⟨fun h0 hc => h0 (isConst_of_finAct (inv_mem g.2) (finAct_inv h) hc),
      fun h0 hc => h0 (isConst_of_finAct g.2 h hc)⟩
  have hShort : ∀ s t, s.length ≤ 3 → t.length ≤ 3 → Incompatible s t → ¬ IsConst s →
      ¬ IsConst t → Commute (θy κ Yof s) (θy κ Yof t) := by
    intro s t hs ht h hs' ht'
    rw [hθy, hθy]
    exact commute_of_cw (Or.inl (Or.inr ⟨(s, t), ⟨hs, ht, h, hs', ht'⟩, rfl⟩))
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
    simp only [hθy, hθx, ← map_mul, ← map_inv]
    exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Or.inr rfl)
  refine fp_of (val := val0) phi hphi hinj hrange ι0 R0' R0'_finite R0'_val
    (fun g => θgen κ Yof g.1) ?_ ?_ ?_
  · intro τ
    cases τ
    · show θx κ [] = _; exact hκx
    · show θx κ [true] = _; exact hκx1
    · show θy κ Yof [true, false] = _
      rw [θy_rep κ Yof (Or.inr (Or.inr (Or.inr rfl))) hK10]
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
        show PresentedGroup.toGroup R0'_val (θx κ s) = xs s
        rw [hθx, toGroup_mk, ev0_w (xs_mem_F _)]
    | y s =>
        show PresentedGroup.toGroup R0'_val (θy κ Yof s) = ys s
        rw [hθy, toGroup_mk, ev0_Θ hg]

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
theorem solution :
    ((∃ phi : PresentedGroup R →* SeqGroup, (∀ g, phi (PresentedGroup.of g) = g.val) ∧
      Function.Injective phi ∧ phi.range = G) → Group.IsFinitelyPresented G) ∧
    ((∃ phi : PresentedGroup R0S →* SeqGroup, (∀ g, phi (PresentedGroup.of g) = g.1.val) ∧
      Function.Injective phi ∧ phi.range = G0Seq) → Group.IsFinitelyPresented G0Seq) :=
  ⟨fp_G, fp_G0⟩
end
