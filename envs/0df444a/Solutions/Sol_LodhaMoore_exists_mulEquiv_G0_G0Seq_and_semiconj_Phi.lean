-- Prove2me | solution 1 for LodhaMoore.exists_mulEquiv_G0_G0Seq_and_semiconj_Phi
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:29.222278+00:00
-- url     : https://prove2.me/submissions/965f848f-4220-4ba6-a5b4-d094f45cd525

import Mathlib
import Definitions.Def_LodhaMoore
import Theorems.Thm_LodhaMoore_phi_cons_and_eq_phi_of_cons_and_Phi_fibers
import Theorems.Thm_LodhaMoore_phi_y_and_Phi_a_b_c
import Theorems.Thm_LodhaMoore_bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R

section
/-! Development: `a`, `b`, `c` are the homeomorphisms the bundle names (`ofReal` returns the
extension of `aFun`, `bFun`, `cFun`), and their values on `ℝ`. -/

namespace LodhaMoore

end LodhaMoore
end

section
/-! # Lodha–Moore §3 (group S3a): Proposition 3.1, the identification `G₀ ≅ ⟨X ∪ Y₀⟩`, the
relations (1)–(5), the presentation of `F`, and the conjugacy classes of the `y_s`. -/

namespace LodhaMoore.Dev.S3a

open LodhaMoore

/-! ## Infinite binary sequences -/

abbrev Str := Stream' Bool

theorem cons_zero (d : Bool) (s : Str) : (Stream'.cons d s) 0 = d := rfl

theorem eq_cons (ξ : Str) : ξ = Stream'.cons (ξ 0) ξ.tail := (Stream'.eta ξ).symm

theorem exists_cons (ξ : Str) : ∃ d ζ, ξ = Stream'.cons d ζ := ⟨_, _, eq_cons ξ⟩

theorem cases_x (ξ : Str) :
    (∃ ζ, ξ = Stream'.cons false (Stream'.cons false ζ)) ∨
    (∃ ζ, ξ = Stream'.cons false (Stream'.cons true ζ)) ∨ (∃ ζ, ξ = Stream'.cons true ζ) := by
  obtain ⟨d, ζ, rfl⟩ := exists_cons ξ
  obtain ⟨e, η, rfl⟩ := exists_cons ζ
  cases d <;> cases e <;>
    first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr (Or.inl ⟨_, rfl⟩) | exact Or.inr (Or.inr ⟨_, rfl⟩)

theorem cases_xinv (ξ : Str) :
    (∃ ζ, ξ = Stream'.cons false ζ) ∨
    (∃ ζ, ξ = Stream'.cons true (Stream'.cons false ζ)) ∨
    (∃ ζ, ξ = Stream'.cons true (Stream'.cons true ζ)) := by
  obtain ⟨d, ζ, rfl⟩ := exists_cons ξ
  obtain ⟨e, η, rfl⟩ := exists_cons ζ
  cases d <;> cases e <;>
    first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr (Or.inl ⟨_, rfl⟩) | exact Or.inr (Or.inr ⟨_, rfl⟩)

theorem append_cons (d : Bool) (l : Seq) (s : Str) :
    (d :: l) ++ₛ s = Stream'.cons d (l ++ₛ s) := rfl

theorem take_length_append (s : Seq) (η : Str) : (s ++ₛ η).take s.length = s := by
  have := Stream'.append_take 0 s η
  simpa [Stream'.take_zero] using this.symm

/-! ## `localize` -/

theorem localize_nil (f : Str → Str) (ξ : Str) : localize [] f ξ = f ξ := by
  simp [localize, Stream'.take_zero]

theorem localize_cons_same (d : Bool) (t : Seq) (f : Str → Str) (ζ : Str) :
    localize (d :: t) f (Stream'.cons d ζ) = Stream'.cons d (localize t f ζ) := by
  unfold localize
  simp only [List.length_cons, Stream'.take_succ_cons, List.cons.injEq, true_and]
  split_ifs
  · rfl
  · rfl

theorem localize_append_self (s : Seq) (f : Str → Str) (η : Str) :
    localize s f (s ++ₛ η) = s ++ₛ f η := by
  induction s with
  | nil => simp [localize_nil]
  | cons d s ih => rw [append_cons, localize_cons_same, ih]; rfl

theorem localize_of_not {s : Seq} {ξ : Str} (h : ∀ η, ξ ≠ s ++ₛ η) (f : Str → Str) :
    localize s f ξ = ξ := by
  unfold localize
  rw [if_neg]
  intro h'
  apply h (ξ.drop s.length)
  conv_lhs => rw [← Stream'.append_take_drop s.length ξ]
  rw [h']

/-- The cylinder of `s`. -/
def Cyl (s : Seq) (ξ : Str) : Prop := ∃ η, ξ = s ++ₛ η

theorem localize_of_not_cyl {s : Seq} {ξ : Str} (h : ¬ Cyl s ξ) (f : Str → Str) :
    localize s f ξ = ξ :=
  localize_of_not (fun η hη => h ⟨η, hη⟩) f

theorem localize_comp (s : Seq) (f g : Str → Str) (ξ : Str) :
    localize s f (localize s g ξ) = localize s (f ∘ g) ξ := by
  by_cases h : Cyl s ξ
  · obtain ⟨η, rfl⟩ := h
    simp [localize_append_self]
  · rw [localize_of_not_cyl h, localize_of_not_cyl h, localize_of_not_cyl h]

theorem localize_inv {s : Seq} {f g : Str → Str} (h : ∀ ξ, g (f ξ) = ξ) (ξ : Str) :
    localize s g (localize s f ξ) = ξ := by
  rw [localize_comp]
  by_cases hc : Cyl s ξ
  · obtain ⟨η, rfl⟩ := hc
    rw [localize_append_self, Function.comp_apply, h]
  · rw [localize_of_not_cyl hc]

/-! ## `x` and `x⁻¹` -/

/-- `x⁻¹`: `0η ↦ 00η`, `10η ↦ 01η`, `11η ↦ 1η`. -/
def xInvFun (ξ : Str) : Str :=
  match ξ 0, ξ 1 with
  | false, _ => Stream'.cons false ξ
  | true, false => Stream'.cons false (Stream'.cons true (ξ.drop 2))
  | true, true => ξ.tail

theorem xFun_00 (ζ : Str) : xFun (Stream'.cons false (Stream'.cons false ζ)) =
    Stream'.cons false ζ := rfl
theorem xFun_01 (ζ : Str) : xFun (Stream'.cons false (Stream'.cons true ζ)) =
    Stream'.cons true (Stream'.cons false ζ) := rfl
theorem xFun_1 (ζ : Str) : xFun (Stream'.cons true ζ) = Stream'.cons true (Stream'.cons true ζ) :=
  rfl

theorem xInvFun_0 (ζ : Str) : xInvFun (Stream'.cons false ζ) =
    Stream'.cons false (Stream'.cons false ζ) := rfl
theorem xInvFun_10 (ζ : Str) : xInvFun (Stream'.cons true (Stream'.cons false ζ)) =
    Stream'.cons false (Stream'.cons true ζ) := rfl
theorem xInvFun_11 (ζ : Str) : xInvFun (Stream'.cons true (Stream'.cons true ζ)) =
    Stream'.cons true ζ := rfl

theorem xFun_xInvFun (ξ : Str) : xFun (xInvFun ξ) = ξ := by
  rcases cases_xinv ξ with ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩
  · rfl
  · rfl
  · rfl

/-! ## `y` and `y⁻¹` -/

theorem yStep_ne_nil (σ : Bool) (ξ : Str) : (yStep σ ξ).1 ≠ [] := by
  cases σ <;> simp only [yStep] <;> split <;> simp

theorem yOut_length (k : ℕ) (σ : Bool) (ξ : Str) : k ≤ (yOut k σ ξ).length := by
  induction k generalizing σ ξ with
  | zero => simp
  | succ k ih =>
    simp only [yOut, List.length_append]
    have := ih (yStep σ ξ).2.1 (yStep σ ξ).2.2
    have := List.length_pos_of_ne_nil (yStep_ne_nil σ ξ)
    omega

theorem yOut_prefix_succ (k : ℕ) (σ : Bool) (ξ : Str) : yOut k σ ξ <+: yOut (k + 1) σ ξ := by
  induction k generalizing σ ξ with
  | zero => simp [yOut]
  | succ k ih =>
    simp only [yOut] at ih ⊢
    exact (List.prefix_append_right_inj _).mpr (ih _ _)

theorem yOut_prefix {k m : ℕ} (h : k ≤ m) (σ : Bool) (ξ : Str) : yOut k σ ξ <+: yOut m σ ξ := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih => exact ih.trans (yOut_prefix_succ m σ ξ)

theorem getD_of_prefix {l₁ l₂ : Seq} (h : l₁ <+: l₂) {n : ℕ} (hn : n < l₁.length) :
    l₁.getD n false = l₂.getD n false := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hn]

theorem yFun_eq_getD {n m : ℕ} (h : n + 1 ≤ m) (σ : Bool) (ξ : Str) :
    yFun σ ξ n = (yOut m σ ξ).getD n false := by
  unfold yFun
  exact getD_of_prefix (yOut_prefix h σ ξ) (by have := yOut_length (n + 1) σ ξ; omega)

theorem yFun_rec (σ : Bool) (ξ : Str) :
    yFun σ ξ = (yStep σ ξ).1 ++ₛ yFun (yStep σ ξ).2.1 (yStep σ ξ).2.2 := by
  funext n
  have hne := List.length_pos_of_ne_nil (yStep_ne_nil σ ξ)
  change yFun σ ξ n = Stream'.get _ n
  rw [yFun_eq_getD (le_refl _), yOut]
  by_cases hn : n < (yStep σ ξ).1.length
  · rw [List.getD_append _ _ _ _ hn, Stream'.get_append_left n _ _ hn, List.getD_eq_getElem _ _ hn]
  · push Not at hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [List.getD_append_right _ _ _ _ hn, Stream'.get_append_right, Nat.add_sub_cancel_left]
    change _ = yFun (yStep σ ξ).2.1 (yStep σ ξ).2.2 j
    rw [yFun_eq_getD (m := (yStep σ ξ).1.length + j) (by omega)]

theorem yT_00 (ζ : Str) : yFun true (Stream'.cons false (Stream'.cons false ζ)) =
    Stream'.cons false (yFun true ζ) := by rw [yFun_rec]; rfl
theorem yT_01 (ζ : Str) : yFun true (Stream'.cons false (Stream'.cons true ζ)) =
    Stream'.cons true (Stream'.cons false (yFun false ζ)) := by rw [yFun_rec]; rfl
theorem yT_1 (ζ : Str) : yFun true (Stream'.cons true ζ) =
    Stream'.cons true (Stream'.cons true (yFun true ζ)) := by rw [yFun_rec]; rfl
theorem yF_0 (ζ : Str) : yFun false (Stream'.cons false ζ) =
    Stream'.cons false (Stream'.cons false (yFun false ζ)) := by rw [yFun_rec]; rfl
theorem yF_10 (ζ : Str) : yFun false (Stream'.cons true (Stream'.cons false ζ)) =
    Stream'.cons false (Stream'.cons true (yFun true ζ)) := by rw [yFun_rec]; rfl
theorem yF_11 (ζ : Str) : yFun false (Stream'.cons true (Stream'.cons true ζ)) =
    Stream'.cons true (yFun false ζ) := by rw [yFun_rec]; rfl

theorem yFun_inv_aux (n : ℕ) : ∀ (σ : Bool) (ξ : Str), yFun (!σ) (yFun σ ξ) n = ξ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro σ ξ
  cases σ
  · rcases cases_xinv ξ with ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩
    · rw [yF_0, Bool.not_false, yT_00]
      match n with
      | 0 => rfl
      | k + 1 => exact ih k (by omega) false ζ
    · rw [yF_10, Bool.not_false, yT_01]
      match n with
      | 0 => rfl
      | 1 => rfl
      | k + 2 => exact ih k (by omega) true ζ
    · rw [yF_11, Bool.not_false, yT_1]
      match n with
      | 0 => rfl
      | 1 => rfl
      | k + 2 => exact ih k (by omega) false ζ
  · rcases cases_x ξ with ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩
    · rw [yT_00, Bool.not_true, yF_0]
      match n with
      | 0 => rfl
      | 1 => rfl
      | k + 2 => exact ih k (by omega) true ζ
    · rw [yT_01, Bool.not_true, yF_10]
      match n with
      | 0 => rfl
      | 1 => rfl
      | k + 2 => exact ih k (by omega) false ζ
    · rw [yT_1, Bool.not_true, yF_11]
      match n with
      | 0 => rfl
      | k + 1 => exact ih k (by omega) true ζ

theorem yFun_inv (σ : Bool) (ξ : Str) : yFun (!σ) (yFun σ ξ) = ξ :=
  funext fun n => yFun_inv_aux n σ ξ

theorem yT_yF (ξ : Str) : yFun true (yFun false ξ) = ξ := yFun_inv false ξ

/-! ## The relations (1)–(5) as identities of functions -/

/-- `(xr r)`: the tail action of `x` on finite sequences, as in `xFin`. -/
def xr : List Bool → Option (List Bool)
  | false :: false :: r => some (false :: r)
  | false :: true :: r => some (true :: false :: r)
  | true :: r => some (true :: true :: r)
  | _ => none

theorem xFin_append (s r : Seq) : xFin s (s ++ r) = (xr r).map (s ++ ·) := by
  unfold xFin
  rw [if_pos (List.prefix_append _ _)]
  simp only [List.drop_left]
  rcases r with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;> rfl

/-! ## `SeqGroup` -/

theorem seq_ext {g h : SeqGroup} (H : ∀ ξ, MulOpposite.unop g ξ = MulOpposite.unop h ξ) :
    g = h :=
  MulOpposite.unop_injective (Equiv.ext H)

theorem unop_mul_apply (g h : SeqGroup) (ξ : Str) :
    MulOpposite.unop (g * h) ξ = MulOpposite.unop h (MulOpposite.unop g ξ) := rfl

theorem unop_one_apply (ξ : Str) : MulOpposite.unop (1 : SeqGroup) ξ = ξ := rfl

theorem unop_toSeqGroup {f : Str → Str} (hf : Function.Bijective f) (ξ : Str) :
    MulOpposite.unop (toSeqGroup f) ξ = f ξ := by
  simp [toSeqGroup, hf]

theorem unop_toSeqGroup_inv {f g : Str → Str} (hf : Function.Bijective f)
    (hfg : ∀ ξ, f (g ξ) = ξ) (ξ : Str) : MulOpposite.unop (toSeqGroup f)⁻¹ ξ = g ξ := by
  simp only [toSeqGroup, hf, dif_pos, MulOpposite.unop_inv, MulOpposite.unop_op,
    Equiv.Perm.inv_def]
  rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, hfg]

/-- Every `x_s` and `y_s` is a bijection. -/
def HB : Prop := ∀ s, Function.Bijective (xSeq s) ∧ Function.Bijective (ySeq s)

/-- Every relation of `R` holds. -/
def HR : Prop := ∀ r ∈ R, FreeGroup.lift Gen.val r = 1

section
variable (hb : HB)
include hb

theorem unop_xs (s : Seq) (ξ : Str) : MulOpposite.unop (xs s) ξ = xSeq s ξ :=
  unop_toSeqGroup (hb s).1 ξ

theorem unop_ys (s : Seq) (ξ : Str) : MulOpposite.unop (ys s) ξ = ySeq s ξ :=
  unop_toSeqGroup (hb s).2 ξ

theorem unop_xs_inv (s : Seq) (ξ : Str) :
    MulOpposite.unop (xs s)⁻¹ ξ = localize s xInvFun ξ :=
  unop_toSeqGroup_inv (hb s).1 (localize_inv xFun_xInvFun) ξ

theorem unop_ys_inv (s : Seq) (ξ : Str) :
    MulOpposite.unop (ys s)⁻¹ ξ = localize s (yFun false) ξ :=
  unop_toSeqGroup_inv (hb s).2 (localize_inv yT_yF) ξ

end

/-! ## `phi`: the recursion, and the nested intervals -/

theorem phi_cons0 (ξ : Str) : phi (Stream'.cons false ξ) = (1 + (phi ξ)⁻¹)⁻¹ :=
  phi_cons_and_eq_phi_of_cons_and_Phi_fibers.1 ξ
theorem phi_cons1 (ξ : Str) : phi (Stream'.cons true ξ) = 1 + phi ξ :=
  phi_cons_and_eq_phi_of_cons_and_Phi_fibers.2.1 ξ

theorem phi_cons (d : Bool) (ξ : Str) : phi (Stream'.cons d ξ) = cfStep d (phi ξ) := by
  cases d
  · simp [cfStep, phi_cons0]
  · simp [cfStep, phi_cons1]

/-- The composite of the digit maps of a finite word. -/
noncomputable def Mw (w : Seq) (t : ENNReal) : ENNReal := w.foldr cfStep t

theorem Mw_nil (t : ENNReal) : Mw [] t = t := rfl
theorem Mw_cons (d : Bool) (w : Seq) (t : ENNReal) : Mw (d :: w) t = cfStep d (Mw w t) := rfl
theorem Mw_append (w w' : Seq) (t : ENNReal) : Mw (w ++ w') t = Mw w (Mw w' t) := by
  simp [Mw, List.foldr_append]

theorem phi_append (w : Seq) (ζ : Str) : phi (w ++ₛ ζ) = Mw w (phi ζ) := by
  induction w with
  | nil => rfl
  | cons d w ih => rw [append_cons, phi_cons, ih]; rfl

/-- The matrix `[[p, q], [r, s]]` of a composite of digit maps. -/
structure Q4 where
  p : ℕ
  q : ℕ
  r : ℕ
  s : ℕ

def Q4.step (m : Q4) (d : Bool) : Q4 :=
  if d then ⟨m.p, m.p + m.q, m.r, m.r + m.s⟩ else ⟨m.p + m.q, m.q, m.r + m.s, m.s⟩

def mat (w : Seq) : Q4 := w.foldl Q4.step ⟨1, 0, 0, 1⟩

theorem mat_snoc (w : Seq) (d : Bool) : mat (w ++ [d]) = (mat w).step d := by
  simp [mat, List.foldl_append]

theorem mat_good (w : Seq) :
    1 ≤ (mat w).p ∧ 1 ≤ (mat w).s ∧ (mat w).p * (mat w).s = (mat w).q * (mat w).r + 1 := by
  induction w using List.reverseRecOn with
  | nil => simp [mat]
  | append_singleton w d ih =>
    rw [mat_snoc]
    obtain ⟨h1, h2, h3⟩ := ih
    cases d <;> simp only [Q4.step, Bool.false_eq_true, if_false, if_true] <;>
      refine ⟨by omega, by omega, ?_⟩
    · rw [Nat.add_mul, Nat.mul_add, h3]; omega
    · rw [Nat.mul_add, Nat.add_mul, h3]; omega

theorem c0_coe (x : NNReal) : cfStep false (x : ENNReal) = ((x / (1 + x) : NNReal) : ENNReal) := by
  by_cases hx : x = 0
  · subst hx; simp [cfStep]
  · simp only [cfStep, Bool.false_eq_true, if_false]
    rw [← ENNReal.coe_inv hx, ← ENNReal.coe_one, ← ENNReal.coe_add,
      ← ENNReal.coe_inv (by positivity)]
    congr 1
    field_simp
    ring

theorem c0_top : cfStep false (⊤ : ENNReal) = ((1 : NNReal) : ENNReal) := by simp [cfStep]

theorem c1_coe (x : NNReal) : cfStep true (x : ENNReal) = ((1 + x : NNReal) : ENNReal) := by
  simp [cfStep]

theorem c1_top : cfStep true (⊤ : ENNReal) = ⊤ := by simp [cfStep]

theorem Mw_formula (w : Seq) :
    (∀ x : NNReal, Mw w x = (((mat w).p * x + (mat w).q) / ((mat w).r * x + (mat w).s) : NNReal)) ∧
      Mw w ⊤ = ((mat w).p : ENNReal) / (mat w).r := by
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨fun x => ?_, ?_⟩
    · simp [mat, Mw_nil]
    · simp [mat, Mw_nil]
  | append_singleton w d ih =>
    obtain ⟨hf, ht⟩ := ih
    obtain ⟨hp, hs, -⟩ := mat_good w
    have hsx : ∀ x : NNReal, ((mat w).r : NNReal) * x + (mat w).s ≠ 0 := fun x => by
      have : (1 : NNReal) ≤ (mat w).s := by exact_mod_cast hs
      exact ne_of_gt (lt_of_lt_of_le one_pos (le_add_left this))
    rw [mat_snoc]
    cases d
    · simp only [Q4.step, Bool.false_eq_true, if_false]
      refine ⟨fun x => ?_, ?_⟩
      · rw [Mw_append, Mw_cons, Mw_nil, c0_coe, hf]
        congr 1
        by_cases hx : x = 0
        · subst hx; simp
        push_cast
        have h1 : (1 + x) ≠ 0 := by positivity
        have h2 := hsx (x / (1 + x))
        have h3 := hsx x
        field_simp
        ring
      · rw [Mw_append, Mw_cons, Mw_nil, c0_top, hf, ← ENNReal.coe_natCast, ← ENNReal.coe_natCast,
          ← ENNReal.coe_div (by push_cast; positivity)]
        congr 1
        push_cast
        ring_nf
    · simp only [Q4.step, if_true]
      refine ⟨fun x => ?_, ?_⟩
      · rw [Mw_append, Mw_cons, Mw_nil, c1_coe, hf]
        congr 1
        push_cast
        ring_nf
      · rw [Mw_append, Mw_cons, Mw_nil, c1_top, ht]

theorem Mw_bounds (w : Seq) (hr : 1 ≤ (mat w).r) (t : ENNReal) :
    Mw w t ≠ ⊤ ∧ ((mat w).q : ℝ) / (mat w).s ≤ (Mw w t).toReal ∧
      (Mw w t).toReal ≤ ((mat w).p : ℝ) / (mat w).r := by
  obtain ⟨hf, ht⟩ := Mw_formula w
  obtain ⟨hp, hs, hdet⟩ := mat_good w
  have hdetR : ((mat w).p : ℝ) * (mat w).s = (mat w).q * (mat w).r + 1 := by exact_mod_cast hdet
  have hrR : (1 : ℝ) ≤ (mat w).r := by exact_mod_cast hr
  have hsR : (1 : ℝ) ≤ (mat w).s := by exact_mod_cast hs
  induction t using ENNReal.recTopCoe with
  | top =>
    rw [ht, ← ENNReal.coe_natCast, ← ENNReal.coe_natCast,
      ← ENNReal.coe_div (by exact_mod_cast (show (mat w).r ≠ 0 by omega))]
    refine ⟨ENNReal.coe_ne_top, ?_, ?_⟩
    · rw [ENNReal.coe_toReal]; push_cast
      rw [div_le_div_iff₀ (by linarith only [hsR]) (by linarith only [hrR])]
      linarith only [hdetR]
    · rw [ENNReal.coe_toReal]; push_cast; exact le_rfl
  | coe x =>
    rw [hf x]
    have hx : (0 : ℝ) ≤ x := x.2
    have hden : (0 : ℝ) < (mat w).r * x + (mat w).s := by positivity
    have key : ((mat w).p : ℝ) * (mat w).s * x = (mat w).q * (mat w).r * x + x := by
      rw [hdetR]; ring
    refine ⟨ENNReal.coe_ne_top, ?_, ?_⟩
    · rw [ENNReal.coe_toReal]; push_cast
      rw [div_le_div_iff₀ (by linarith only [hsR]) hden]
      linarith only [key, hx]
    · rw [ENNReal.coe_toReal]; push_cast
      rw [div_le_div_iff₀ hden (by linarith only [hrR])]
      linarith only [hdetR]

theorem Mw_replicate_ge (m : ℕ) : ∀ (η : Str), (∀ n, η n = true) → ∀ t,
    (m : ENNReal) ≤ Mw (η.take m) t := by
  induction m with
  | zero => simp
  | succ m ih =>
    intro η hη t
    rw [Stream'.take_succ, Mw_cons]
    have h0 : Stream'.head η = true := hη 0
    rw [h0]
    simp only [cfStep, if_true]
    have := ih η.tail (fun n => hη (n + 1)) t
    push_cast
    rw [add_comm]
    exact add_le_add_right this 1

theorem mat_r_growth (η : Str) (k : ℕ) (hk : η k = false) (n : ℕ) :
    1 ≤ (mat (η.take (k + 1 + n))).r ∧
      n + 2 ≤ (mat (η.take (k + 1 + n))).r + (mat (η.take (k + 1 + n))).s := by
  induction n with
  | zero =>
    rw [Nat.add_zero, Stream'.take_succ', mat_snoc]
    have hs := (mat_good (η.take k)).2.1
    change 1 ≤ ((mat (η.take k)).step (η.get k)).r ∧ _
    have hk' : η.get k = false := hk
    rw [hk']
    simp only [Q4.step, Bool.false_eq_true, if_false]
    omega
  | succ n ih =>
    rw [show k + 1 + (n + 1) = (k + 1 + n) + 1 by ring, Stream'.take_succ', mat_snoc]
    have hs := (mat_good (η.take (k + 1 + n))).2.1
    change 1 ≤ ((mat _).step (η.get _)).r ∧ _ + 2 ≤ ((mat _).step (η.get _)).r + _
    cases η.get (k + 1 + n) <;> simp only [Q4.step, Bool.false_eq_true, if_false, if_true] <;>
      omega

theorem eq_zero_of_abs_le (d : ℝ) (h : ∀ n : ℕ, |d| ≤ 1 / ((n : ℝ) + 1)) : d = 0 := by
  by_contra hd
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr hd)
  linarith [h n]

/-- The nested intervals `Mw (η ↾ m) [0, ∞]` shrink to a point. -/
theorem shrink (η : Str) (A B : ENNReal)
    (h : ∀ m, ∃ t u, A = Mw (η.take m) t ∧ B = Mw (η.take m) u) : A = B := by
  by_cases hall : ∀ n, η n = true
  · have key : ∀ C : ENNReal, (∀ m, ∃ t, C = Mw (η.take m) t) → C = ⊤ := by
      intro C hC
      apply ENNReal.eq_top_of_forall_nnreal_le
      intro r
      obtain ⟨m, hm⟩ := exists_nat_ge (r : ℝ)
      obtain ⟨t, ht⟩ := hC m
      calc (r : ENNReal) ≤ (m : ENNReal) := by
            rw [← ENNReal.coe_natCast]; exact ENNReal.coe_le_coe.mpr (by exact_mod_cast hm)
        _ ≤ C := ht ▸ Mw_replicate_ge m η hall t
    rw [key A (fun m => by obtain ⟨t, u, ht, -⟩ := h m; exact ⟨t, ht⟩),
      key B (fun m => by obtain ⟨t, u, -, hu⟩ := h m; exact ⟨u, hu⟩)]
  · push Not at hall
    obtain ⟨k, hk⟩ := hall
    simp only [ne_eq, Bool.not_eq_true] at hk
    have hfin : ∀ C : ENNReal, (∃ t, C = Mw (η.take (k + 1)) t) → C ≠ ⊤ := by
      rintro C ⟨t, rfl⟩
      exact (Mw_bounds _ (mat_r_growth η k hk 0).1 t).1
    obtain ⟨t0, u0, hA0, hB0⟩ := h (k + 1)
    have hA : A ≠ ⊤ := hfin A ⟨t0, hA0⟩
    have hB : B ≠ ⊤ := hfin B ⟨u0, hB0⟩
    rw [← ENNReal.toReal_eq_toReal_iff' hA hB, ← sub_eq_zero]
    apply eq_zero_of_abs_le
    intro n
    obtain ⟨t, u, hAt, hBu⟩ := h (k + 1 + n)
    set w := η.take (k + 1 + n)
    obtain ⟨hr, hrs⟩ := mat_r_growth η k hk n
    obtain ⟨-, hs, hdet⟩ := mat_good w
    obtain ⟨-, hA1, hA2⟩ := Mw_bounds w hr t
    obtain ⟨-, hB1, hB2⟩ := Mw_bounds w hr u
    rw [← hAt] at hA1 hA2
    rw [← hBu] at hB1 hB2
    have hrR : (1 : ℝ) ≤ (mat w).r := by exact_mod_cast hr
    have hsR : (1 : ℝ) ≤ (mat w).s := by exact_mod_cast hs
    have hdetR : ((mat w).p : ℝ) * (mat w).s = (mat w).q * (mat w).r + 1 := by
      exact_mod_cast hdet
    have hrsR : (n : ℝ) + 2 ≤ (mat w).r + (mat w).s := by exact_mod_cast hrs
    have hwidth : ((mat w).p : ℝ) / (mat w).r - (mat w).q / (mat w).s =
        1 / ((mat w).r * (mat w).s) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), mul_comm ((mat w).r : ℝ) ((mat w).s),
        hdetR]
      ring
    have hprod : (n : ℝ) + 1 ≤ (mat w).r * (mat w).s := by
      have := mul_nonneg (sub_nonneg.mpr hrR) (sub_nonneg.mpr hsR)
      linarith only [this, hrsR]
    have hle : 1 / (((mat w).r : ℝ) * (mat w).s) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hprod
    rw [abs_le]
    constructor <;> linarith only [hA1, hA2, hB1, hB2, hwidth, hle]

/-! ## Proposition 3.1, first part: `phi(ξ.y) = 2 phi(ξ)` -/

/-! ## Proposition 3.1, second part: `Phi` carries `x`, `x₁`, `y₁₀` to `a`, `b`, `c` -/

/-- The complement of an infinite sequence. -/
def compl (ξ : Str) : Str := fun n => !ξ n

theorem compl_cons (d : Bool) (ξ : Str) :
    compl (Stream'.cons d ξ) = Stream'.cons (!d) (compl ξ) := by
  funext n; cases n <;> rfl

theorem phi_compl (ξ : Str) : phi (compl ξ) = (phi ξ)⁻¹ := by
  have key := phi_cons_and_eq_phi_of_cons_and_Phi_fibers.2.2.1 (fun ξ => (phi (compl ξ))⁻¹)
    (fun ξ => by
      simp only [compl_cons, Bool.not_false, phi_cons1, inv_inv])
    (fun ξ => by
      simp only [compl_cons, Bool.not_true, phi_cons0, inv_inv])
  have := congrFun key ξ
  rw [← this, inv_inv]

/-- `-v` on the projective line, `∞ ↦ ∞`. -/
noncomputable def negP1 (v : ENNReal) : OnePoint ℝ :=
  if v = ⊤ then OnePoint.infty else ((-v.toReal : ℝ) : OnePoint ℝ)

theorem toP1_top : toP1 ⊤ = OnePoint.infty := by simp [toP1]

theorem Phi_cons1 (η : Str) : Phi (Stream'.cons true η) = toP1 (phi η) := by
  unfold Phi; rw [if_pos (cons_zero true η)]; rfl

theorem Phi_cons0 (η : Str) : Phi (Stream'.cons false η) = negP1 (phi η)⁻¹ := by
  unfold Phi negP1
  simp only [cons_zero, Bool.false_eq_true, if_false]
  have : (fun n => !(Stream'.cons false η).tail n) = compl η := rfl
  rw [this, phi_compl]

/-! ## Generation and conjugacy, from the relations alone (in any group) -/

theorem xFin_nil (r : Seq) : xFin [] r = xr r := by
  have := xFin_append [] r
  simp only [List.nil_append] at this
  rw [this]
  cases xr r <;> rfl

theorem xFin_one (r : Seq) : xFin [true] (true :: r) = (xr r).map (true :: ·) :=
  xFin_append [true] r

/-- `s` is `1ⁿ`, or `s` is `1ⁿ0r` (and likewise with the digits swapped). -/
theorem decomp (d : Bool) : ∀ s : Seq,
    s = List.replicate s.length d ∨ ∃ n r, s = List.replicate n d ++ (!d) :: r
  | [] => Or.inl rfl
  | e :: s => by
    by_cases he : e = d
    · subst he
      rcases decomp e s with h | ⟨n, r, h⟩
      · left; rw [List.length_cons, List.replicate_succ, ← h]
      · right; exact ⟨n + 1, r, by rw [h, List.replicate_succ, List.cons_append]⟩
    · right
      refine ⟨0, s, ?_⟩
      have : e = !d := by cases e <;> cases d <;> simp_all
      rw [this]; rfl

theorem isConst_replicate (k : ℕ) (d : Bool) : IsConst (List.replicate k d) := by
  intro i hi j hj
  simp only [List.length_replicate] at hi hj
  simp [hi, hj]

theorem nonconst_decomp {s : Seq} (h : ¬ IsConst s) :
    ∃ n r, s = List.replicate (n + 1) true ++ false :: r ∨
      s = List.replicate (n + 1) false ++ true :: r := by
  rcases s with _ | ⟨d, s⟩
  · exact absurd (fun i hi => absurd hi (by simp)) h
  · rcases decomp d s with h' | ⟨n, r, h'⟩
    · exact absurd (by rw [h', ← List.replicate_succ]; exact isConst_replicate _ _) h
    · refine ⟨n, r, ?_⟩
      rw [h', ← List.cons_append, ← List.replicate_succ]
      cases d
      · right; rfl
      · left; rfl

section GroupGen

variable {Γ : Type*} [Group Γ]

theorem gen_rep (X : Seq → Γ) (h2 : ∀ s t t', xFin s t = some t' → X t * X s = X s * X t')
    (H : Subgroup Γ) (h0 : X [] ∈ H) (h1 : X [true] ∈ H) :
    ∀ n, X (List.replicate n true) ∈ H
  | 0 => h0
  | 1 => h1
  | n + 2 => by
    have key := h2 [] (List.replicate (n + 1) true) (List.replicate (n + 2) true)
      (by rw [xFin_nil]; rfl)
    have : X (List.replicate (n + 2) true) =
        (X [])⁻¹ * X (List.replicate (n + 1) true) * X [] := by
      rw [mul_assoc, key]; group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem h0) (gen_rep X h2 H h0 h1 (n + 1))) h0

theorem gen_x (X : Seq → Γ)
    (h1 : ∀ s, X s * X s = X (s ++ [false]) * X s * X (s ++ [true]))
    (h2 : ∀ s t t', xFin s t = some t' → X t * X s = X s * X t')
    (H : Subgroup Γ) (hH : ∀ n, X (List.replicate n true) ∈ H) : ∀ s, X s ∈ H := by
  have aux : ∀ r n, X (List.replicate n true ++ false :: r) ∈ H := by
    intro r
    induction r with
    | nil =>
      intro n
      have key := h1 (List.replicate n true)
      rw [← List.replicate_succ'] at key
      have : X (List.replicate n true ++ [false]) = X (List.replicate n true) *
          X (List.replicate n true) * (X (List.replicate (n + 1) true))⁻¹ *
            (X (List.replicate n true))⁻¹ := by
        rw [key]; group
      rw [this]
      exact H.mul_mem (H.mul_mem (H.mul_mem (hH n) (hH n)) (H.inv_mem (hH _)))
        (H.inv_mem (hH n))
    | cons d r ih =>
      intro n
      cases d
      · have key := h2 (List.replicate n true) (List.replicate n true ++ false :: false :: r)
          (List.replicate n true ++ false :: r) (by rw [xFin_append]; rfl)
        have : X (List.replicate n true ++ false :: false :: r) = X (List.replicate n true) *
            X (List.replicate n true ++ false :: r) * (X (List.replicate n true))⁻¹ := by
          rw [← key]; group
        rw [this]
        exact H.mul_mem (H.mul_mem (hH n) (ih n)) (H.inv_mem (hH n))
      · have key := h2 (List.replicate n true) (List.replicate n true ++ false :: true :: r)
          (List.replicate n true ++ true :: false :: r) (by rw [xFin_append]; rfl)
        have e : List.replicate n true ++ true :: false :: r =
            List.replicate (n + 1) true ++ false :: r := by
          rw [List.replicate_succ', List.append_assoc]; rfl
        rw [e] at key
        have : X (List.replicate n true ++ false :: true :: r) = X (List.replicate n true) *
            X (List.replicate (n + 1) true ++ false :: r) * (X (List.replicate n true))⁻¹ := by
          rw [← key]; group
        rw [this]
        exact H.mul_mem (H.mul_mem (hH n) (ih (n + 1))) (H.inv_mem (hH n))
  intro s
  rcases decomp true s with h | ⟨n, r, h⟩
  · rw [h]; exact hH _
  · rw [h]; exact aux r n

/-- `y_v` is a `K`-conjugate of `y_u`. -/
def CJ (Y : Seq → Γ) (K : Subgroup Γ) (u v : Seq) : Prop := ∃ g ∈ K, Y v = g⁻¹ * Y u * g

variable {Y : Seq → Γ} {K : Subgroup Γ}

theorem CJ.refl (u : Seq) : CJ Y K u u := ⟨1, K.one_mem, by group⟩

theorem CJ.symm {u v : Seq} (h : CJ Y K u v) : CJ Y K v u := by
  obtain ⟨g, hg, h⟩ := h
  exact ⟨g⁻¹, K.inv_mem hg, by rw [h]; group⟩

theorem CJ.trans {u v w : Seq} (h : CJ Y K u v) (h' : CJ Y K v w) : CJ Y K u w := by
  obtain ⟨g, hg, h⟩ := h
  obtain ⟨g', hg', h'⟩ := h'
  exact ⟨g * g', K.mul_mem hg hg', by rw [h', h]; group⟩

theorem CJ.move (X : Seq → Γ) (h3 : ∀ s t t', xFin s t = some t' → Y t * X s = X s * Y t')
    (hK : ∀ s, X s ∈ K) {s t t' : Seq} (h : xFin s t = some t') : CJ Y K t t' :=
  ⟨X s, hK s, by rw [mul_assoc, h3 s t t' h]; group⟩

section moves
variable (X : Seq → Γ) (h3 : ∀ s t t', xFin s t = some t' → Y t * X s = X s * Y t')
  (hK : ∀ s, X s ∈ K)
include h3 hK

theorem cj_10 (r : Seq) : CJ Y K [true, false] (true :: false :: r) := by
  induction r with
  | nil => exact CJ.refl _
  | cons d r ih =>
    cases d
    · refine ih.trans (CJ.move X h3 hK (s := [true]) ?_).symm
      rw [xFin_one]; rfl
    · refine (ih.trans (CJ.move X h3 hK (s := []) (t := true :: false :: r)
        (t' := true :: true :: false :: r) ?_)).trans
        (CJ.move X h3 hK (s := [true]) (t := true :: false :: true :: r)
          (t' := true :: true :: false :: r) ?_).symm
      · rw [xFin_nil]; rfl
      · rw [xFin_one]; rfl

theorem cj_1n0 (n : ℕ) (r : Seq) :
    CJ Y K [true, false] (List.replicate (n + 1) true ++ false :: r) := by
  induction n with
  | zero => exact cj_10 X h3 hK r
  | succ n ih =>
    refine ih.trans (CJ.move X h3 hK (s := []) ?_)
    rw [xFin_nil, List.replicate_succ, List.cons_append]; rfl

theorem cj_0n1 (n : ℕ) (r : Seq) :
    CJ Y K [true, false] (List.replicate (n + 1) false ++ true :: r) := by
  induction n with
  | zero =>
    refine (cj_10 X h3 hK r).trans (CJ.move X h3 hK (s := []) ?_).symm
    rw [xFin_nil]; rfl
  | succ n ih =>
    refine ih.trans (CJ.move X h3 hK (s := []) ?_).symm
    rw [xFin_nil, List.replicate_succ, List.replicate_succ, List.cons_append, List.cons_append]
    rfl

theorem cj_nonconst {s : Seq} (h : ¬ IsConst s) : CJ Y K [true, false] s := by
  obtain ⟨n, r, h | h⟩ := nonconst_decomp h <;> rw [h]
  · exact cj_1n0 X h3 hK n r
  · exact cj_0n1 X h3 hK n r

end moves

end GroupGen

/-! ## The relations in `SeqGroup`, from `HR` -/

section
variable (hr : HR)
include hr

theorem rel1_grp (s : Seq) : xs s * xs s = xs (s ++ [false]) * xs s * xs (s ++ [true]) := by
  have := hr _ ⟨Rel.one s, rfl⟩
  simp only [Rel.lhs, Rel.rhs, map_mul, map_inv, FreeGroup.lift_apply_of, Gen.val] at this
  exact mul_inv_eq_one.mp this

theorem rel2_grp {s t t' : Seq} (h : xFin s t = some t') : xs t * xs s = xs s * xs t' := by
  have := hr _ ⟨Rel.two s t t' h, rfl⟩
  simp only [Rel.lhs, Rel.rhs, map_mul, map_inv, FreeGroup.lift_apply_of, Gen.val] at this
  exact mul_inv_eq_one.mp this

theorem rel3_grp {s t t' : Seq} (h : xFin s t = some t') : ys t * xs s = xs s * ys t' := by
  have := hr _ ⟨Rel.three s t t' h, rfl⟩
  simp only [Rel.lhs, Rel.rhs, map_mul, map_inv, FreeGroup.lift_apply_of, Gen.val] at this
  exact mul_inv_eq_one.mp this

theorem xs_mem_of (H : Subgroup SeqGroup) (h0 : xs [] ∈ H) (h1 : xs [true] ∈ H) (s : Seq) :
    xs s ∈ H :=
  gen_x xs (rel1_grp hr) (fun _ _ _ h => rel2_grp hr h) H
    (gen_rep xs (fun _ _ _ h => rel2_grp hr h) H h0 h1) s

end

/-! ## Every element of `G` is locally determined -/

/-- Each initial segment of the output depends only on an initial segment of the input. -/
def LD (f : Str → Str) : Prop :=
  ∀ n, ∃ N, ∀ ξ ξ' : Str, ξ.take N = ξ'.take N → (f ξ).take n = (f ξ').take n

theorem take_mono {ξ ξ' : Str} {m n : ℕ} (h : ξ.take n = ξ'.take n) (hmn : m ≤ n) :
    ξ.take m = ξ'.take m := by
  have := congrArg (List.take m) h
  rwa [Stream'.take_take, Stream'.take_take, min_eq_right hmn] at this

theorem take_eq_cons {ξ ξ' : Str} {m : ℕ} (h : ξ.take m = ξ'.take m) (d : Bool) :
    (Stream'.cons d ξ).take (m + 1) = (Stream'.cons d ξ').take (m + 1) := by
  rw [Stream'.take_succ_cons, Stream'.take_succ_cons, h]

theorem take_cons_inj {d d' : Bool} {ξ ξ' : Str} {n : ℕ}
    (h : (Stream'.cons d ξ).take (n + 1) = (Stream'.cons d' ξ').take (n + 1)) :
    d = d' ∧ ξ.take n = ξ'.take n := by
  rw [Stream'.take_succ_cons, Stream'.take_succ_cons] at h
  exact List.cons.inj h

theorem take_append_congr (s : Seq) {X X' : Str} {n : ℕ} (h : X.take n = X'.take n) {m : ℕ}
    (hm : m ≤ s.length + n) : (s ++ₛ X).take m = (s ++ₛ X').take m := by
  refine take_mono ?_ hm
  rw [← Stream'.append_take, ← Stream'.append_take, h]

theorem cyl_iff_take (s : Seq) (ξ : Str) : Cyl s ξ ↔ ξ.take s.length = s := by
  constructor
  · rintro ⟨η, rfl⟩; exact take_length_append s η
  · intro h
    refine ⟨ξ.drop s.length, ?_⟩
    conv_lhs => rw [← Stream'.append_take_drop s.length ξ]
    rw [h]

theorem LD_id : LD id := fun n => ⟨n, fun _ _ h => h⟩

theorem LD_comp {f g : Str → Str} (hf : LD f) (hg : LD g) : LD (fun ξ => f (g ξ)) := by
  intro n
  obtain ⟨N1, h1⟩ := hf n
  obtain ⟨N2, h2⟩ := hg N1
  exact ⟨N2, fun ξ ξ' h => h1 _ _ (h2 _ _ h)⟩

theorem LD_localize {f : Str → Str} (hf : LD f) (s : Seq) : LD (localize s f) := by
  intro n
  obtain ⟨N, hN⟩ := hf n
  refine ⟨s.length + N + n, fun ξ ξ' h => ?_⟩
  have hs : ξ.take s.length = ξ'.take s.length := take_mono h (by omega)
  by_cases hc : Cyl s ξ
  · have hc' : Cyl s ξ' := by
      rw [cyl_iff_take] at hc ⊢; rw [← hs, hc]
    obtain ⟨η, rfl⟩ := hc
    obtain ⟨η', rfl⟩ := hc'
    have h' : (s ++ₛ η).take (s.length + N) = (s ++ₛ η').take (s.length + N) :=
      take_mono h (by omega)
    rw [← Stream'.append_take, ← Stream'.append_take] at h'
    have hη : η.take N = η'.take N := List.append_cancel_left h'
    rw [localize_append_self, localize_append_self]
    exact take_append_congr s (hN η η' hη) (by omega)
  · have hc' : ¬ Cyl s ξ' := by
      rw [cyl_iff_take] at hc ⊢; rwa [← hs]
    rw [localize_of_not_cyl hc, localize_of_not_cyl hc']
    exact take_mono h (by omega)

theorem LD_xFun : LD xFun := by
  intro n
  refine ⟨n + 2, fun ξ ξ' hξ => ?_⟩
  obtain ⟨a1, b1, ζ, rfl⟩ : ∃ a1 b1 ζ, ξ = Stream'.cons a1 (Stream'.cons b1 ζ) :=
    ⟨_, _, _, (eq_cons ξ).trans (congrArg _ (eq_cons _))⟩
  obtain ⟨a2, b2, ζ', rfl⟩ : ∃ a2 b2 ζ', ξ' = Stream'.cons a2 (Stream'.cons b2 ζ') :=
    ⟨_, _, _, (eq_cons ξ').trans (congrArg _ (eq_cons _))⟩
  obtain ⟨e1, h1⟩ := take_cons_inj hξ
  subst e1
  obtain ⟨e2, h2⟩ := take_cons_inj h1
  subst e2
  cases a1
  · cases b1
    · rw [xFun_00, xFun_00]; refine take_mono (take_eq_cons h2 false) ?_; omega
    · rw [xFun_01, xFun_01]
      refine take_mono (take_eq_cons (take_eq_cons h2 false) true) ?_; omega
  · rw [xFun_1, xFun_1]
    refine take_mono (take_eq_cons (take_eq_cons h1 true) true) ?_; omega

theorem LD_xInvFun : LD xInvFun := by
  intro n
  refine ⟨n + 2, fun ξ ξ' hξ => ?_⟩
  obtain ⟨a1, b1, ζ, rfl⟩ : ∃ a1 b1 ζ, ξ = Stream'.cons a1 (Stream'.cons b1 ζ) :=
    ⟨_, _, _, (eq_cons ξ).trans (congrArg _ (eq_cons _))⟩
  obtain ⟨a2, b2, ζ', rfl⟩ : ∃ a2 b2 ζ', ξ' = Stream'.cons a2 (Stream'.cons b2 ζ') :=
    ⟨_, _, _, (eq_cons ξ').trans (congrArg _ (eq_cons _))⟩
  obtain ⟨e1, h1⟩ := take_cons_inj hξ
  subst e1
  obtain ⟨e2, h2⟩ := take_cons_inj h1
  subst e2
  cases a1
  · rw [xInvFun_0, xInvFun_0]
    refine take_mono (take_eq_cons (take_eq_cons h1 false) false) ?_; omega
  · cases b1
    · rw [xInvFun_10, xInvFun_10]
      refine take_mono (take_eq_cons (take_eq_cons h2 true) false) ?_; omega
    · rw [xInvFun_11, xInvFun_11]; refine take_mono (take_eq_cons h2 true) ?_; omega

theorem yStep_congr (σ : Bool) {ξ ξ' : Str} (h0 : ξ 0 = ξ' 0) (h1 : ξ 1 = ξ' 1) :
    (yStep σ ξ).1 = (yStep σ ξ').1 ∧ (yStep σ ξ).2.1 = (yStep σ ξ').2.1 ∧
      ∃ m ≤ 2, (yStep σ ξ).2.2 = ξ.drop m ∧ (yStep σ ξ').2.2 = ξ'.drop m := by
  cases σ <;> simp only [yStep, h0, h1] <;> split <;> exact ⟨rfl, rfl, _, by norm_num, rfl, rfl⟩

theorem yOut_congr (k : ℕ) : ∀ (σ : Bool) (ξ ξ' : Str), ξ.take (2 * k) = ξ'.take (2 * k) →
    yOut k σ ξ = yOut k σ ξ' := by
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro σ ξ ξ' h
    have h0 : ξ 0 = ξ' 0 := by
      have := congrArg (fun l => l[0]?) h
      exact (by simpa [Stream'.getElem?_take (show 0 < 2 * (k + 1) by omega)] using this :
        ξ.get 0 = ξ'.get 0)
    have h1 : ξ 1 = ξ' 1 := by
      have := congrArg (fun l => l[1]?) h
      exact (by simpa [Stream'.getElem?_take (show 1 < 2 * (k + 1) by omega)] using this :
        ξ.get 1 = ξ'.get 1)
    obtain ⟨e1, e2, m, hm, e3, e4⟩ := yStep_congr σ h0 h1
    simp only [yOut]
    rw [e1, e2, e3, e4, ih _ _ _]
    rw [Stream'.take_drop, Stream'.take_drop, take_mono h (by omega)]

theorem LD_yFun (σ : Bool) : LD (yFun σ) := by
  intro n
  refine ⟨2 * n, fun ξ ξ' h => ?_⟩
  have hy := yOut_congr n σ ξ ξ' h
  apply List.ext_getElem (by simp)
  intro i hi _
  simp only [Stream'.length_take] at hi
  rw [Stream'.take_get, Stream'.take_get]
  change yFun σ ξ i = yFun σ ξ' i
  rw [yFun_eq_getD (m := n) (by omega), yFun_eq_getD (m := n) (by omega), hy]

/-- The locally determined elements (with locally determined inverse). -/
def LDG : Subgroup SeqGroup where
  carrier := {g | LD ⇑(MulOpposite.unop g) ∧ LD ⇑(MulOpposite.unop g⁻¹)}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨?_, ?_⟩
    · have := LD_comp hh1 hg1
      exact this
    · rw [mul_inv_rev]
      have := LD_comp hg2 hh2
      exact this
  one_mem' := ⟨LD_id, LD_id⟩
  inv_mem' := by
    rintro g ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    rw [inv_inv]; exact h1

/-- Milestone 13 (every `x_s`, `y_s` is a bijection, and the relations (1)–(5) hold), taken from its
statement: the isomorphism of milestone 12 and the steps below use it, as in the paper. `hB` and
`hR` above are milestone 13's own proof. -/
theorem hB' : HB := LodhaMoore.bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R.1

theorem hR' : HR := LodhaMoore.bijective_xSeq_ySeq_and_lift_val_eq_one_of_mem_R.2

theorem G_le_LDG : G ≤ LDG := by
  rw [G, Subgroup.closure_le]
  rintro g (⟨s, rfl⟩ | ⟨s, rfl⟩)
  · refine ⟨?_, ?_⟩
    · rw [show ⇑(MulOpposite.unop (xs s)) = xSeq s from funext (unop_xs hB' s)]
      exact LD_localize LD_xFun s
    · rw [show ⇑(MulOpposite.unop (xs s)⁻¹) = localize s xInvFun from funext (unop_xs_inv hB' s)]
      exact LD_localize LD_xInvFun s
  · refine ⟨?_, ?_⟩
    · rw [show ⇑(MulOpposite.unop (ys s)) = ySeq s from funext (unop_ys hB' s)]
      exact LD_localize (LD_yFun true) s
    · rw [show ⇑(MulOpposite.unop (ys s)⁻¹) = localize s (yFun false) from
        funext (unop_ys_inv hB' s)]
      exact LD_localize (LD_yFun false) s

/-- `0101…`, a sequence which is not eventually constant. -/
def alt : Str := fun i => decide (i % 2 = 0)

theorem not_eventuallyConst_append (p : Seq) : ¬ EventuallyConst (p ++ₛ alt) := by
  rintro ⟨M, d, hM⟩
  have h1 := hM (p.length + 2 * M) (by omega)
  have h2 := hM (p.length + (2 * M + 1)) (by omega)
  change (p ++ₛ alt).get _ = d at h1 h2
  rw [Stream'.get_append_right] at h1 h2
  simp only [alt, Stream'.get] at h1 h2
  rw [← h2] at h1
  simp [Nat.mul_mod_right, Nat.add_mod] at h1

theorem eq_id_of_LD {f : Str → Str} (hf : LD f)
    (hfix : ∀ ξ, ¬ EventuallyConst ξ → f ξ = ξ) (ξ : Str) : f ξ = ξ := by
  funext n
  obtain ⟨N, hN⟩ := hf (n + 1)
  set M := max N (n + 1)
  set ξ' := ξ.take M ++ₛ alt
  have hM : ξ'.take M = ξ.take M := by
    have := take_length_append (ξ.take M) alt
    rwa [Stream'.length_take] at this
  have e := hN ξ ξ' (take_mono hM.symm (le_max_left _ _))
  rw [hfix ξ' (not_eventuallyConst_append _), take_mono hM (le_max_right _ _)] at e
  have := congrArg (fun l => l[n]?) e
  simp only [Stream'.getElem?_take (show n < n + 1 by omega)] at this
  exact Option.some.inj this

/-! ## `Phi` is onto -/

/-- The greedy continued-fraction digit map: `v ↦ v - 1` if `v ≥ 1`, `v ↦ 1/(1/v - 1)` if not. -/
noncomputable def gstep (v : ENNReal) : ENNReal := if 1 ≤ v then v - 1 else (v⁻¹ - 1)⁻¹

noncomputable def gdig (v : ENNReal) : Bool := decide (1 ≤ v)

noncomputable def gstream (v : ENNReal) : Str := fun n => gdig (gstep^[n] v)

theorem cfStep_g (w : ENNReal) : cfStep (gdig w) (gstep w) = w := by
  unfold gdig gstep cfStep
  by_cases h : 1 ≤ w
  · simp only [h, decide_true, if_true]; exact add_tsub_cancel_of_le h
  · simp only [h, decide_false, if_false, Bool.false_eq_true]
    have h' : 1 ≤ w⁻¹ := ENNReal.one_le_inv.mpr (le_of_lt (not_le.mp h))
    rw [inv_inv, add_tsub_cancel_of_le h', inv_inv]

theorem g_nest (v : ENNReal) (m : ℕ) : v = Mw ((gstream v).take m) (gstep^[m] v) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Stream'.take_succ', Mw_append, Mw_cons, Mw_nil, Function.iterate_succ_apply']
    change v = Mw _ (cfStep (gdig (gstep^[m] v)) (gstep (gstep^[m] v)))
    rw [cfStep_g]; exact ih

theorem phi_gstream (v : ENNReal) : phi (gstream v) = v := by
  refine shrink (gstream v) _ _ fun m => ⟨phi ((gstream v).drop m), gstep^[m] v, ?_, g_nest v m⟩
  rw [← phi_append, Stream'.append_take_drop]

theorem Phi_surjective : Function.Surjective Phi := by
  intro z
  induction z using OnePoint.rec with
  | infty => exact ⟨Stream'.cons true (gstream ⊤), by rw [Phi_cons1, phi_gstream, toP1_top]⟩
  | coe t =>
    by_cases ht : 0 ≤ t
    · refine ⟨Stream'.cons true (gstream (ENNReal.ofReal t)), ?_⟩
      rw [Phi_cons1, phi_gstream]
      simp [toP1, ENNReal.toReal_ofReal ht]
    · refine ⟨Stream'.cons false (gstream (ENNReal.ofReal (-t))⁻¹), ?_⟩
      rw [Phi_cons0, phi_gstream, inv_inv]
      simp [negP1, ENNReal.toReal_ofReal (by linarith : 0 ≤ -t)]

/-! ## The identification `G₀ ≅ ⟨X ∪ Y₀⟩` induced by `Phi` -/

/-- `g` and `h` correspond under `Phi`. -/
def Sc (g : OnePoint ℝ ≃ₜ OnePoint ℝ) (h : SeqGroup) : Prop :=
  ∀ ξ, g (Phi ξ) = Phi (MulOpposite.unop h ξ)

theorem Sc_one : Sc 1 1 := fun _ => rfl

theorem Sc_mul {g g' : OnePoint ℝ ≃ₜ OnePoint ℝ} {h h' : SeqGroup} (H : Sc g h) (H' : Sc g' h') :
    Sc (g' * g) (h * h') := fun ξ => by
  rw [Homeomorph.mul_apply, H, H', unop_mul_apply]

theorem Sc_inv {g : OnePoint ℝ ≃ₜ OnePoint ℝ} {h : SeqGroup} (H : Sc g h) : Sc g⁻¹ h⁻¹ :=
  fun ξ => by
    rw [Homeomorph.inv_apply, Homeomorph.symm_apply_eq, H, ← unop_mul_apply, inv_mul_cancel,
      unop_one_apply]

theorem Sc_unique {g : OnePoint ℝ ≃ₜ OnePoint ℝ} {h h' : SeqGroup} (H : Sc g h) (H' : Sc g h')
    (hh : h ∈ G) (hh' : h' ∈ G) : h = h' := by
  have hk : h⁻¹ * h' ∈ LDG := G_le_LDG (G.mul_mem (G.inv_mem hh) hh')
  have fix : ∀ η, ¬ EventuallyConst η → MulOpposite.unop (h⁻¹ * h') η = η := by
    intro η hη
    rw [unop_mul_apply]
    apply phi_cons_and_eq_phi_of_cons_and_Phi_fibers.2.2.2.1 η hη
    have e1 : MulOpposite.unop h (MulOpposite.unop h⁻¹ η) = η := by
      rw [← unop_mul_apply, inv_mul_cancel, unop_one_apply]
    rw [← H', H, e1]
  have h1 : h⁻¹ * h' = 1 := seq_ext fun ξ => eq_id_of_LD hk.1 fix ξ
  exact inv_mul_eq_one.mp h1

/-- `⟨x, x₁, y₁₀⟩`. -/
def K3 : Subgroup SeqGroup := Subgroup.closure {xs [], xs [true], ys [true, false]}

theorem isConst_10 : ¬ IsConst [true, false] := fun h => by
  have := h 0 (by simp) 1 (by simp)
  simp at this

theorem K3_le_G0Seq : K3 ≤ G0Seq := by
  rw [K3, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact Subgroup.subset_closure (Or.inl ⟨[], rfl⟩)
  · exact Subgroup.subset_closure (Or.inl ⟨[true], rfl⟩)
  · exact Subgroup.subset_closure (Or.inr ⟨[true, false], isConst_10, rfl⟩)

theorem G0Seq_le_G : G0Seq ≤ G := by
  apply Subgroup.closure_mono
  rintro g (⟨s, rfl⟩ | ⟨s, -, rfl⟩)
  · exact Or.inl ⟨s, rfl⟩
  · exact Or.inr ⟨s, rfl⟩

theorem G0Seq_le_K3 : G0Seq ≤ K3 := by
  have hx : ∀ s, xs s ∈ K3 := xs_mem_of hR' K3 (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))
  rw [G0Seq, Subgroup.closure_le]
  rintro g (⟨s, rfl⟩ | ⟨s, hs, rfl⟩)
  · exact hx s
  · obtain ⟨g, hg, e⟩ := cj_nonconst (Y := ys) (K := K3) xs (fun _ _ _ h => rel3_grp hR' h) hx hs
    rw [SetLike.mem_coe, e]
    exact K3.mul_mem (K3.mul_mem (K3.inv_mem hg) (Subgroup.subset_closure (by simp))) hg

theorem exists_Sc
    (H11 : ∀ ξ, phi (yFun true ξ) = 2 * phi ξ ∧ a (Phi ξ) = Phi (xFun ξ) ∧
      b (Phi ξ) = Phi (xSeq [true] ξ) ∧ c (Phi ξ) = Phi (ySeq [true, false] ξ))
    {g : OnePoint ℝ ≃ₜ OnePoint ℝ} (hg : g ∈ G0) : ∃ h ∈ K3, Sc g h := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · refine ⟨xs [], Subgroup.subset_closure (by simp), fun ξ => ?_⟩
      rw [unop_xs hB', xSeq, localize_nil]; exact (H11 ξ).2.1
    · exact ⟨xs [true], Subgroup.subset_closure (by simp), fun ξ => by
        rw [unop_xs hB']; exact (H11 ξ).2.2.1⟩
    · exact ⟨ys [true, false], Subgroup.subset_closure (by simp), fun ξ => by
        rw [unop_ys hB']; exact (H11 ξ).2.2.2⟩
  | one => exact ⟨1, K3.one_mem, Sc_one⟩
  | mul x y _ _ hx hy =>
    obtain ⟨h, hK, hS⟩ := hx
    obtain ⟨h', hK', hS'⟩ := hy
    exact ⟨h' * h, K3.mul_mem hK' hK, Sc_mul hS' hS⟩
  | inv x _ hx =>
    obtain ⟨h, hK, hS⟩ := hx
    exact ⟨h⁻¹, K3.inv_mem hK, Sc_inv hS⟩

theorem exists_e
    (H11 : ∀ ξ, phi (yFun true ξ) = 2 * phi ξ ∧ a (Phi ξ) = Phi (xFun ξ) ∧
      b (Phi ξ) = Phi (xSeq [true] ξ) ∧ c (Phi ξ) = Phi (ySeq [true, false] ξ)) :
    ∃ e : (↥G0)ᵐᵒᵖ ≃* ↥G0Seq,
      (e (MulOpposite.op ⟨a, Subgroup.subset_closure (by simp)⟩) : SeqGroup) = xs [] ∧
      (e (MulOpposite.op ⟨b, Subgroup.subset_closure (by simp)⟩) : SeqGroup) = xs [true] ∧
      (e (MulOpposite.op ⟨c, Subgroup.subset_closure (by simp)⟩) : SeqGroup) = ys [true, false] ∧
      ∀ (g : ↥G0) (ξ : Stream' Bool),
        (g : OnePoint ℝ ≃ₜ OnePoint ℝ) (Phi ξ) =
          Phi (MulOpposite.unop (e (MulOpposite.op g) : SeqGroup) ξ) := by
  have hex : ∀ x : (↥G0)ᵐᵒᵖ, ∃ h ∈ K3, Sc (x.unop : OnePoint ℝ ≃ₜ OnePoint ℝ) h :=
    fun x => exists_Sc H11 x.unop.2
  let E : (↥G0)ᵐᵒᵖ → ↥G0Seq := fun x => ⟨(hex x).choose, K3_le_G0Seq (hex x).choose_spec.1⟩
  have hE : ∀ x, Sc (x.unop : OnePoint ℝ ≃ₜ OnePoint ℝ) (E x : SeqGroup) :=
    fun x => (hex x).choose_spec.2
  have hEG : ∀ x, (E x : SeqGroup) ∈ G := fun x => G0Seq_le_G (E x).2
  have hEeq : ∀ x h, Sc (x.unop : OnePoint ℝ ≃ₜ OnePoint ℝ) h → h ∈ G → (E x : SeqGroup) = h :=
    fun x h hS hG => Sc_unique (hE x) hS (hEG x) hG
  have hmul : ∀ x y, E (x * y) = E x * E y := by
    intro x y
    apply Subtype.ext
    apply hEeq
    · rw [MulOpposite.unop_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact Sc_mul (hE x) (hE y)
    · exact G.mul_mem (hEG x) (hEG y)
  let f : (↥G0)ᵐᵒᵖ →* ↥G0Seq := MonoidHom.mk' E hmul
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : Sc (x.unop : OnePoint ℝ ≃ₜ OnePoint ℝ) (E y : SeqGroup) := by
      have := hE x
      change E x = E y at hxy
      rwa [hxy] at this
    apply MulOpposite.unop_injective
    apply Subtype.ext
    ext z
    obtain ⟨ξ, rfl⟩ := Phi_surjective z
    rw [h1 ξ, hE y ξ]
  have hgen : ∀ (g : OnePoint ℝ ≃ₜ OnePoint ℝ) (hg : g ∈ G0) (h : SeqGroup), Sc g h → h ∈ G →
      (f (MulOpposite.op ⟨g, hg⟩) : SeqGroup) = h :=
    fun g hg h hS hG => hEeq (MulOpposite.op ⟨g, hg⟩) h hS hG
  have ha : (f (MulOpposite.op ⟨a, Subgroup.subset_closure (by simp)⟩) : SeqGroup) = xs [] :=
    hgen _ _ _ (fun ξ => by rw [unop_xs hB', xSeq, localize_nil]; exact (H11 ξ).2.1)
      (G0Seq_le_G (K3_le_G0Seq (Subgroup.subset_closure (by simp))))
  have hb : (f (MulOpposite.op ⟨b, Subgroup.subset_closure (by simp)⟩) : SeqGroup) = xs [true] :=
    hgen _ _ _ (fun ξ => by rw [unop_xs hB']; exact (H11 ξ).2.2.1)
      (G0Seq_le_G (K3_le_G0Seq (Subgroup.subset_closure (by simp))))
  have hc : (f (MulOpposite.op ⟨c, Subgroup.subset_closure (by simp)⟩) : SeqGroup) =
      ys [true, false] :=
    hgen _ _ _ (fun ξ => by rw [unop_ys hB']; exact (H11 ξ).2.2.2)
      (G0Seq_le_G (K3_le_G0Seq (Subgroup.subset_closure (by simp))))
  have hsurj : Function.Surjective f := by
    intro y
    have hK : K3 ≤ f.range.map G0Seq.subtype := by
      rw [K3, Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨_, ⟨_, rfl⟩, ha⟩
      · exact ⟨_, ⟨_, rfl⟩, hb⟩
      · exact ⟨_, ⟨_, rfl⟩, hc⟩
    obtain ⟨z, ⟨x, rfl⟩, hz⟩ := hK (G0Seq_le_K3 y.2)
    exact ⟨x, Subtype.ext hz⟩
  refine ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, ha, hb, hc, fun g ξ => ?_⟩
  exact hE (MulOpposite.op g) ξ

/-! ## Binary expansions: `F` on sequences and `F` on the unit interval -/

/-! ## The presentations of Cannon–Floyd–Parry: `F₂ → F₁` is injective -/

section CFP
open PresentedGroup

end CFP

/-! ## Statement 14: relations (1), (2) present `F`, and `F₂ ≅ F` -/

section PresF
open PresentedGroup

end PresF

/-! ## Statement 15: the `F`-conjugacy classes of the `y_s` -/

section Conj


end Conj

end LodhaMoore.Dev.S3a

namespace LodhaMoore

open LodhaMoore.Dev.S3a

end LodhaMoore
end

section
open LodhaMoore
open LodhaMoore.Dev.S3a
theorem solution :
    ∃ e : (↥G0)ᵐᵒᵖ ≃* ↥G0Seq,
      (e (MulOpposite.op ⟨a, Subgroup.subset_closure (by simp)⟩) : SeqGroup) = xs [] ∧
      (e (MulOpposite.op ⟨b, Subgroup.subset_closure (by simp)⟩) : SeqGroup) = xs [true] ∧
      (e (MulOpposite.op ⟨c, Subgroup.subset_closure (by simp)⟩) : SeqGroup) = ys [true, false] ∧
      ∀ (g : ↥G0) (ξ : Stream' Bool),
        (g : OnePoint ℝ ≃ₜ OnePoint ℝ) (Phi ξ) = Phi (MulOpposite.unop (e (MulOpposite.op g) : SeqGroup) ξ) :=
  exists_e phi_y_and_Phi_a_b_c
end
