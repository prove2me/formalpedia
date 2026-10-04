-- Prove2me | solution 1 for LodhaMoore.phi_y_and_Phi_a_b_c
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:28.947446+00:00
-- url     : https://prove2.me/submissions/c652a682-41ae-4866-ac57-f57cc21270a6

import Mathlib
import Definitions.Def_LodhaMoore
import Theorems.Thm_LodhaMoore_phi_cons_and_eq_phi_of_cons_and_Phi_fibers
section
/-! Development: `a`, `b`, `c` are the homeomorphisms the bundle names (`ofReal` returns the
extension of `aFun`, `bFun`, `cFun`), and their values on `ℝ`. -/

namespace LodhaMoore

theorem ofReal_coe {f : ℝ → ℝ} (e : ℝ ≃ₜ ℝ) (he : ∀ t, e t = f t) (t : ℝ) :
    ofReal f (t : OnePoint ℝ) = ((f t : ℝ) : OnePoint ℝ) := by
  have h : ∃ E : OnePoint ℝ ≃ₜ OnePoint ℝ, ∀ t : ℝ, E t = ((f t : ℝ) : OnePoint ℝ) :=
    ⟨e.onePointCongr, fun t => by rw [Homeomorph.onePointCongr_apply, OnePoint.map_some, he]⟩
  unfold ofReal
  rw [dif_pos h]
  exact h.choose_spec t

theorem aFun_strictMono : StrictMono aFun := fun x y h => by unfold aFun; linarith

theorem aFun_surjective : Function.Surjective aFun := fun u => ⟨u - 1, by unfold aFun; ring⟩

theorem bFun_strictMono : StrictMono bFun := by
  intro x y hxy
  unfold bFun
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 <;> try linarith
  all_goals first
    | (rw [lt_div_iff₀ (by linarith)]; nlinarith)
    | (rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith)
    | (have : 1 / y < 1 / x := one_div_lt_one_div_of_lt (by linarith) hxy; linarith)
    | (have : 1 / y < 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
       have : x / (1 - x) ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
       linarith)
    | (have : x / (1 - x) ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
       linarith)
    | (have : 1 / x ≥ 1 := by rw [ge_iff_le, le_div_iff₀ (by linarith)]; linarith
       linarith)

theorem bFun_surjective : Function.Surjective bFun := by
  intro u
  unfold bFun
  by_cases h0 : u ≤ 0
  · exact ⟨u, by simp [h0]⟩
  by_cases h1 : u ≤ 1
  · refine ⟨u / (1 + u), ?_⟩
    have hp : 0 < 1 + u := by linarith
    have hpos : ¬ u / (1 + u) ≤ 0 := not_le.mpr (div_pos (by linarith) hp)
    have hh : u / (1 + u) ≤ 1 / 2 := by rw [div_le_iff₀ hp]; linarith
    simp only [hpos, hh, if_false, if_true]
    field_simp
    ring
  by_cases h2 : u ≤ 2
  · refine ⟨1 / (3 - u), ?_⟩
    have hp : 0 < 3 - u := by linarith
    have hpos : ¬ 1 / (3 - u) ≤ 0 := not_le.mpr (div_pos one_pos hp)
    have hh : ¬ 1 / (3 - u) ≤ 1 / 2 := by
      rw [not_le, div_lt_div_iff₀ two_pos hp]; linarith
    have hh1 : 1 / (3 - u) ≤ 1 := by rw [div_le_iff₀ hp]; linarith
    simp only [hpos, hh, hh1, if_false, if_true]
    field_simp
    ring
  · refine ⟨u - 1, ?_⟩
    have a1 : ¬ u - 1 ≤ 0 := by linarith
    have a2 : ¬ u - 1 ≤ 1 / 2 := by linarith
    have a3 : ¬ u - 1 ≤ 1 := by linarith
    simp only [a1, a2, a3, if_false]
    ring

theorem cFun_strictMono : StrictMono cFun := by
  intro x y hxy
  unfold cFun
  split_ifs with h1 h2 h2 <;> try linarith
  · rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  · -- x ∈ [0,1], y ∉ [0,1], so y > 1
    have hy : 1 < y := by
      by_contra hc; exact h2 ⟨by linarith, by linarith⟩
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  · -- x ∉ [0,1], y ∈ [0,1], so x < 0
    have hx : x < 0 := by
      by_contra hc; exact h1 ⟨by linarith, by linarith⟩
    rw [lt_div_iff₀ (by linarith)]; nlinarith

theorem cFun_surjective : Function.Surjective cFun := by
  intro u
  unfold cFun
  by_cases h : 0 ≤ u ∧ u ≤ 1
  · refine ⟨u / (2 - u), ?_⟩
    have hp : 0 < 2 - u := by linarith
    have hh : 0 ≤ u / (2 - u) ∧ u / (2 - u) ≤ 1 :=
      ⟨div_nonneg h.1 hp.le, by rw [div_le_iff₀ hp]; linarith⟩
    rw [if_pos hh]
    field_simp
    ring
  · exact ⟨u, by rw [if_neg h]⟩

noncomputable def aHom : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective aFun aFun_strictMono aFun_surjective).toHomeomorph
noncomputable def bHom : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective bFun bFun_strictMono bFun_surjective).toHomeomorph
noncomputable def cHom : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective cFun cFun_strictMono cFun_surjective).toHomeomorph

theorem a_coe (t : ℝ) : a (t : OnePoint ℝ) = ((aFun t : ℝ) : OnePoint ℝ) := ofReal_coe aHom (fun _ => rfl) t
theorem b_coe (t : ℝ) : b (t : OnePoint ℝ) = ((bFun t : ℝ) : OnePoint ℝ) := ofReal_coe bHom (fun _ => rfl) t
theorem c_coe (t : ℝ) : c (t : OnePoint ℝ) = ((cFun t : ℝ) : OnePoint ℝ) := ofReal_coe cHom (fun _ => rfl) t

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

theorem localize_cons_diff {d e : Bool} (h : d ≠ e) (t : Seq) (f : Str → Str) (ζ : Str) :
    localize (d :: t) f (Stream'.cons e ζ) = Stream'.cons e ζ := by
  unfold localize
  simp only [List.length_cons, Stream'.take_succ_cons, List.cons.injEq]
  rw [if_neg (fun h' => h h'.1.symm)]

/-! ## `x` and `x⁻¹` -/

theorem xFun_00 (ζ : Str) : xFun (Stream'.cons false (Stream'.cons false ζ)) =
    Stream'.cons false ζ := rfl
theorem xFun_01 (ζ : Str) : xFun (Stream'.cons false (Stream'.cons true ζ)) =
    Stream'.cons true (Stream'.cons false ζ) := rfl
theorem xFun_1 (ζ : Str) : xFun (Stream'.cons true ζ) = Stream'.cons true (Stream'.cons true ζ) :=
  rfl

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

theorem localize_tf (t : Seq) (f : Str → Str) (ζ : Str) :
    localize (true :: t) f (Stream'.cons false ζ) = Stream'.cons false ζ :=
  localize_cons_diff (by decide) t f ζ
theorem localize_ft (t : Seq) (f : Str → Str) (ζ : Str) :
    localize (false :: t) f (Stream'.cons true ζ) = Stream'.cons true ζ :=
  localize_cons_diff (by decide) t f ζ

/-! ## The relations (1)–(5) as identities of functions -/

/-! ## `SeqGroup` -/

section

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

theorem mul2_coe (x : NNReal) : (2 : ENNReal) * (x : ENNReal) = ((2 * x : NNReal) : ENNReal) := by
  simp

theorem mul2_top : (2 : ENNReal) * ⊤ = ⊤ := ENNReal.mul_top two_ne_zero

theorem div2_coe (x : NNReal) : (x : ENNReal) / 2 = ((x / 2 : NNReal) : ENNReal) := by
  rw [ENNReal.coe_div two_ne_zero]; simp

theorem div2_top : (⊤ : ENNReal) / 2 = ⊤ := ENNReal.top_div_of_ne_top (by simp)

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

/-- `D true` doubles and `D false` halves. -/
noncomputable def D (σ : Bool) (v : ENNReal) : ENNReal := if σ then 2 * v else v / 2

theorem idT00 (v : ENNReal) : 2 * cfStep false (cfStep false v) = cfStep false (2 * v) := by
  induction v using ENNReal.recTopCoe with
  | top => rw [c0_top, mul2_top, c0_coe, mul2_coe, c0_top]; congr 1; norm_num
  | coe x =>
    rw [c0_coe, c0_coe, mul2_coe, mul2_coe, c0_coe]; congr 1
    field_simp; ring
theorem idT01 (v : ENNReal) :
    2 * cfStep false (cfStep true v) = cfStep true (cfStep false (v / 2)) := by
  induction v using ENNReal.recTopCoe with
  | top => rw [c1_top, c0_top, mul2_coe, div2_top, c0_top, c1_coe]; congr 1; norm_num
  | coe x =>
    rw [c1_coe, c0_coe, mul2_coe, div2_coe, c0_coe, c1_coe]; congr 1
    field_simp; ring
theorem idT1 (v : ENNReal) : 2 * cfStep true v = cfStep true (cfStep true (2 * v)) := by
  induction v using ENNReal.recTopCoe with
  | top => rw [c1_top, mul2_top, c1_top, c1_top]
  | coe x =>
    rw [c1_coe, mul2_coe, mul2_coe, c1_coe, c1_coe]; congr 1; ring
theorem idF0 (v : ENNReal) : cfStep false v / 2 = cfStep false (cfStep false (v / 2)) := by
  induction v using ENNReal.recTopCoe with
  | top => rw [c0_top, div2_coe, div2_top, c0_top, c0_coe]; congr 1; norm_num
  | coe x =>
    rw [c0_coe, div2_coe, div2_coe, c0_coe, c0_coe]; congr 1
    field_simp; ring
theorem idF10 (v : ENNReal) :
    cfStep true (cfStep false v) / 2 = cfStep false (cfStep true (2 * v)) := by
  induction v using ENNReal.recTopCoe with
  | top => rw [c0_top, c1_coe, div2_coe, mul2_top, c1_top, c0_top]; congr 1; norm_num
  | coe x =>
    rw [c0_coe, c1_coe, div2_coe, mul2_coe, c1_coe, c0_coe]; congr 1
    field_simp; ring
theorem idF11 (v : ENNReal) : cfStep true (cfStep true v) / 2 = cfStep true (v / 2) := by
  induction v using ENNReal.recTopCoe with
  | top => rw [c1_top, c1_top, div2_top, c1_top]
  | coe x =>
    rw [c1_coe, c1_coe, div2_coe, div2_coe, c1_coe]; congr 1
    field_simp; ring

def Nest (η : Str) (m : ℕ) (A B : ENNReal) : Prop :=
  ∃ t u, A = Mw (η.take m) t ∧ B = Mw (η.take m) u

theorem nest_zero (η : Str) (A B : ENNReal) : Nest η 0 A B := ⟨A, B, rfl, rfl⟩

theorem nest_mono {η : Str} {m m' : ℕ} (h : m ≤ m') {A B : ENNReal} (hn : Nest η m' A B) :
    Nest η m A B := by
  obtain ⟨t, u, rfl, rfl⟩ := hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨Mw ((η.drop m).take j) t, Mw ((η.drop m).take j) u, ?_, ?_⟩ <;>
    rw [Stream'.take_add, Mw_append]

theorem nest_prepend {η : Str} {k : ℕ} {A B : ENNReal} (hn : Nest η k A B) (w : Seq) :
    Nest (w ++ₛ η) (w.length + k) (Mw w A) (Mw w B) := by
  obtain ⟨t, u, rfl, rfl⟩ := hn
  refine ⟨t, u, ?_, ?_⟩ <;> rw [← Stream'.append_take, Mw_append]

theorem nest_step {σ σ' : Bool} {ξ ζ : Str} {out : Seq} (hy : yFun σ ξ = out ++ₛ yFun σ' ζ)
    (hout : out ≠ []) (hD : D σ (phi ξ) = Mw out (D σ' (phi ζ))) (k : ℕ)
    (ih : Nest (yFun σ' ζ) k (phi (yFun σ' ζ)) (D σ' (phi ζ))) :
    Nest (yFun σ ξ) (k + 1) (phi (yFun σ ξ)) (D σ (phi ξ)) := by
  rw [hy, phi_append, hD]
  have := List.length_pos_of_ne_nil hout
  exact nest_mono (by omega) (nest_prepend ih out)

theorem nest_y (m : ℕ) : ∀ (σ : Bool) (ξ : Str),
    Nest (yFun σ ξ) m (phi (yFun σ ξ)) (D σ (phi ξ)) := by
  induction m with
  | zero => intro σ ξ; exact nest_zero _ _ _
  | succ k ih =>
    intro σ ξ
    cases σ
    · rcases cases_xinv ξ with ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩
      · refine nest_step (out := [false, false]) (yF_0 ζ) (by simp) ?_ k (ih false ζ)
        simp only [D, phi_cons, Bool.false_eq_true, if_false, Mw_cons, Mw_nil]
        exact idF0 _
      · refine nest_step (out := [false, true]) (yF_10 ζ) (by simp) ?_ k (ih true ζ)
        simp only [D, phi_cons, Bool.false_eq_true, if_false, if_true, Mw_cons, Mw_nil]
        exact idF10 _
      · refine nest_step (out := [true]) (yF_11 ζ) (by simp) ?_ k (ih false ζ)
        simp only [D, phi_cons, Bool.false_eq_true, if_false, Mw_cons, Mw_nil]
        exact idF11 _
    · rcases cases_x ξ with ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩
      · refine nest_step (out := [false]) (yT_00 ζ) (by simp) ?_ k (ih true ζ)
        simp only [D, phi_cons, if_true, Mw_cons, Mw_nil]
        exact idT00 _
      · refine nest_step (out := [true, false]) (yT_01 ζ) (by simp) ?_ k (ih false ζ)
        simp only [D, phi_cons, Bool.false_eq_true, if_false, if_true, Mw_cons, Mw_nil]
        exact idT01 _
      · refine nest_step (out := [true, true]) (yT_1 ζ) (by simp) ?_ k (ih true ζ)
        simp only [D, phi_cons, if_true, Mw_cons, Mw_nil]
        exact idT1 _

theorem phi_yFun (σ : Bool) (ξ : Str) : phi (yFun σ ξ) = D σ (phi ξ) :=
  shrink (yFun σ ξ) _ _ (fun m => nest_y m σ ξ)

theorem phi_y (ξ : Str) : phi (yFun true ξ) = 2 * phi ξ := phi_yFun true ξ

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

theorem toP1_coe (x : NNReal) : toP1 (x : ENNReal) = ((x : ℝ) : OnePoint ℝ) := by simp [toP1]
theorem toP1_top : toP1 ⊤ = OnePoint.infty := by simp [toP1]
theorem negP1_coe (x : NNReal) : negP1 (x : ENNReal) = ((-(x : ℝ) : ℝ) : OnePoint ℝ) := by
  simp [negP1]
theorem negP1_top : negP1 ⊤ = OnePoint.infty := by simp [negP1]

theorem Phi_cons1 (η : Str) : Phi (Stream'.cons true η) = toP1 (phi η) := by
  unfold Phi; rw [if_pos (cons_zero true η)]; rfl

theorem Phi_cons0 (η : Str) : Phi (Stream'.cons false η) = negP1 (phi η)⁻¹ := by
  unfold Phi negP1
  simp only [cons_zero, Bool.false_eq_true, if_false]
  have : (fun n => !(Stream'.cons false η).tail n) = compl η := rfl
  rw [this, phi_compl]

theorem fix_infty (e : OnePoint ℝ ≃ₜ OnePoint ℝ) (f : ℝ → ℝ) (hf : Function.Surjective f)
    (he : ∀ t : ℝ, e (t : OnePoint ℝ) = ((f t : ℝ) : OnePoint ℝ)) : e OnePoint.infty = OnePoint.infty := by
  by_contra h
  obtain ⟨t, ht⟩ := OnePoint.ne_infty_iff_exists.mp h
  obtain ⟨u, rfl⟩ := hf t
  rw [← he u] at ht
  exact OnePoint.coe_ne_infty u (e.injective ht)

theorem a_infty : a OnePoint.infty = OnePoint.infty := fix_infty a aFun aFun_surjective a_coe
theorem b_infty : b OnePoint.infty = OnePoint.infty := fix_infty b bFun bFun_surjective b_coe
theorem c_infty : c OnePoint.infty = OnePoint.infty := fix_infty c cFun cFun_surjective c_coe

theorem inv_coe_one_add (x : NNReal) : (1 + (x : ENNReal))⁻¹ = (((1 + x)⁻¹ : NNReal) : ENNReal) := by
  rw [← ENNReal.coe_one, ← ENNReal.coe_add, ENNReal.coe_inv (by positivity)]

theorem inv_c0 (v : ENNReal) : (cfStep false v)⁻¹ = 1 + v⁻¹ := by simp [cfStep]
theorem inv_c1 (v : ENNReal) : (cfStep true v)⁻¹ = (1 + v)⁻¹ := by simp [cfStep]

theorem a_Phi (ξ : Str) : a (Phi ξ) = Phi (xFun ξ) := by
  rcases cases_x ξ with ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩
  · rw [xFun_00, Phi_cons0, Phi_cons0, phi_cons, inv_c0]
    induction (phi ζ)⁻¹ using ENNReal.recTopCoe with
    | top => simp [negP1_top, a_infty]
    | coe x =>
      rw [← ENNReal.coe_one, ← ENNReal.coe_add, negP1_coe, negP1_coe, a_coe]
      congr 1; simp only [aFun]; push_cast; ring
  · rw [xFun_01, Phi_cons0, Phi_cons1, phi_cons, phi_cons, inv_c1]
    induction phi ζ using ENNReal.recTopCoe with
    | top => simp [negP1, toP1, cfStep, a_coe, aFun]
    | coe x =>
      rw [inv_coe_one_add, negP1_coe, c0_coe, toP1_coe, a_coe]
      congr 1
      simp only [aFun]
      push_cast
      field_simp
      ring
  · rw [xFun_1, Phi_cons1, Phi_cons1, phi_cons]
    induction phi ζ using ENNReal.recTopCoe with
    | top => rw [c1_top, toP1_top, a_infty]
    | coe x =>
      rw [c1_coe, toP1_coe, toP1_coe, a_coe]
      congr 1; simp only [aFun]; push_cast; ring

theorem bFun_of_le_zero {t : ℝ} (h : t ≤ 0) : bFun t = t := by simp [bFun, h]
theorem bFun_of_le_half {t : ℝ} (h0 : 0 ≤ t) (h : t ≤ 1 / 2) : bFun t = t / (1 - t) := by
  unfold bFun
  by_cases ht : t ≤ 0
  · have : t = 0 := le_antisymm ht h0
    subst this; simp
  · rw [if_neg ht, if_pos h]
theorem bFun_of_le_one {t : ℝ} (h0 : 1 / 2 ≤ t) (h : t ≤ 1) : bFun t = 3 - 1 / t := by
  unfold bFun
  by_cases ht : t ≤ 1 / 2
  · have : t = 1 / 2 := le_antisymm ht h0
    subst this; norm_num
  · rw [if_neg (by linarith), if_neg ht, if_pos h]
theorem bFun_of_one_le {t : ℝ} (h : 1 ≤ t) : bFun t = t + 1 := by
  unfold bFun
  by_cases ht : t ≤ 1
  · have : t = 1 := le_antisymm ht h
    subst this; norm_num
  · rw [if_neg (by linarith), if_neg (by linarith), if_neg ht]

theorem cFun_of_le_zero {t : ℝ} (h : t ≤ 0) : cFun t = t := by
  unfold cFun
  split_ifs with h'
  · have : t = 0 := le_antisymm h h'.1
    subst this; simp
  · rfl
theorem cFun_of_one_le {t : ℝ} (h : 1 ≤ t) : cFun t = t := by
  unfold cFun
  split_ifs with h'
  · have : t = 1 := le_antisymm h'.2 h
    subst this; norm_num
  · rfl
theorem cFun_of_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : cFun t = 2 * t / (1 + t) := by
  simp [cFun, h0, h1]

theorem b_negP1 (w : ENNReal) : b (negP1 w) = negP1 w := by
  induction w using ENNReal.recTopCoe with
  | top => rw [negP1_top, b_infty]
  | coe x =>
    rw [negP1_coe, b_coe, bFun_of_le_zero (by simp)]

theorem c_negP1 (w : ENNReal) : c (negP1 w) = negP1 w := by
  induction w using ENNReal.recTopCoe with
  | top => rw [negP1_top, c_infty]
  | coe x =>
    rw [negP1_coe, c_coe, cFun_of_le_zero (by simp)]

theorem b_Phi (ξ : Str) : b (Phi ξ) = Phi (xSeq [true] ξ) := by
  obtain ⟨d, η, rfl⟩ := exists_cons ξ
  cases d
  · rw [xSeq, localize_tf, Phi_cons0, b_negP1]
  · rw [xSeq, localize_cons_same, localize_nil, Phi_cons1, Phi_cons1]
    rcases cases_x η with ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩
    · rw [xFun_00]
      simp only [phi_cons]
      induction phi ζ using ENNReal.recTopCoe with
      | top =>
        simp only [c0_top, c0_coe, toP1_coe, b_coe]
        congr 1
        push_cast
        rw [bFun_of_le_half (by norm_num) (by norm_num)]
        norm_num
      | coe x =>
        simp only [c0_coe, toP1_coe, b_coe]
        congr 1
        have hx : (0 : ℝ) ≤ x := x.2
        push_cast
        have key : (x : ℝ) / (1 + x) / (1 + x / (1 + x)) = x / (1 + 2 * x) := by
          field_simp; ring
        rw [key, bFun_of_le_half (by positivity) (by rw [div_le_iff₀ (by positivity)]; linarith)]
        have h1 : (0:ℝ) < 1 + 2 * (x : ℝ) := by linarith
        have h2 : (1 : ℝ) - (x : ℝ) / (1 + 2 * (x : ℝ)) = (1 + (x : ℝ)) / (1 + 2 * (x : ℝ)) := by
          field_simp; ring
        rw [h2, div_div_div_cancel_right₀ h1.ne']
    · rw [xFun_01]
      simp only [phi_cons]
      induction phi ζ using ENNReal.recTopCoe with
      | top =>
        simp only [c1_top, c0_top, c1_coe, toP1_coe, b_coe]
        congr 1
        push_cast
        rw [bFun_of_le_one (by norm_num) (by norm_num)]
        norm_num
      | coe x =>
        simp only [c1_coe, c0_coe, toP1_coe, b_coe]
        congr 1
        have hx : (0 : ℝ) ≤ x := x.2
        push_cast
        have key : (1 + (x : ℝ)) / (1 + (1 + x)) = (1 + x) / (2 + x) := by ring_nf
        rw [key, bFun_of_le_one (by rw [le_div_iff₀ (by positivity)]; linarith)
          (by rw [div_le_iff₀ (by positivity)]; linarith)]
        field_simp
        ring
    · rw [xFun_1]
      simp only [phi_cons]
      induction phi ζ using ENNReal.recTopCoe with
      | top => rw [c1_top, c1_top, toP1_top, b_infty]
      | coe x =>
        simp only [c1_coe, toP1_coe, b_coe]
        congr 1
        have hx : (0 : ℝ) ≤ x := x.2
        push_cast
        rw [bFun_of_one_le (by linarith)]
        ring

theorem c_Phi (ξ : Str) : c (Phi ξ) = Phi (ySeq [true, false] ξ) := by
  obtain ⟨d, η, rfl⟩ := exists_cons ξ
  cases d
  · rw [ySeq, localize_tf, Phi_cons0, c_negP1]
  · obtain ⟨e, ζ, rfl⟩ := exists_cons η
    cases e
    · rw [ySeq, localize_cons_same, localize_cons_same, localize_nil, Phi_cons1, Phi_cons1]
      simp only [phi_cons, phi_y]
      induction phi ζ using ENNReal.recTopCoe with
      | top =>
        simp only [mul2_top, c0_top, toP1_coe, c_coe]
        congr 1
        push_cast
        rw [cFun_of_one_le (by norm_num)]
      | coe x =>
        simp only [mul2_coe, c0_coe, toP1_coe, c_coe]
        congr 1
        have hx : (0 : ℝ) ≤ x := x.2
        push_cast
        rw [cFun_of_mem (by positivity) (by rw [div_le_iff₀ (by positivity)]; linarith)]
        field_simp
        ring
    · rw [ySeq, localize_cons_same, localize_ft, Phi_cons1]
      simp only [phi_cons]
      induction phi ζ using ENNReal.recTopCoe with
      | top => rw [c1_top, toP1_top, c_infty]
      | coe x =>
        simp only [c1_coe, toP1_coe, c_coe]
        congr 1
        have hx : (0 : ℝ) ≤ x := x.2
        push_cast
        rw [cFun_of_one_le (by linarith)]

/-! ## Generation and conjugacy, from the relations alone (in any group) -/

section GroupGen

variable {Γ : Type*} [Group Γ]

variable {Y : Seq → Γ} {K : Subgroup Γ}

section moves
variable (X : Seq → Γ) (h3 : ∀ s t t', xFin s t = some t' → Y t * X s = X s * Y t')
  (hK : ∀ s, X s ∈ K)
include h3 hK

end moves

end GroupGen

/-! ## The relations in `SeqGroup`, from `HR` -/

section

end

/-! ## Every element of `G` is locally determined -/

/-! ## `Phi` is onto -/

/-! ## The identification `G₀ ≅ ⟨X ∪ Y₀⟩` induced by `Phi` -/

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
theorem solution (ξ : Stream' Bool) :
    phi (yFun true ξ) = 2 * phi ξ ∧ a (Phi ξ) = Phi (xFun ξ) ∧ b (Phi ξ) = Phi (xSeq [true] ξ) ∧
      c (Phi ξ) = Phi (ySeq [true, false] ξ) :=
  ⟨phi_y ξ, a_Phi ξ, b_Phi ξ, c_Phi ξ⟩
end
