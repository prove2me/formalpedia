-- Prove2me | solution 1 for MediaMenus.Duopoly.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T16:26:57.726522+00:00
-- url     : https://prove2.me/submissions/f504917c-64ef-4f3f-896a-c0b8c2dd15b6

import Mathlib
import Definitions.Def_MediaMenus_Duopoly_Model

namespace MediaMenus.Duopoly

/-- `K = ρ v²/2`, the extra value of the second platform. -/
noncomputable def KK (P : Params) : ℝ := rho P * P.v ^ 2 / 2

/-- closed-form utility -/
noncomputable def uval (P : Params) (θ : Ty) (M : Profile) : Choice → ℝ
  | .abstain => 0
  | .single i k => P.v ^ 2 / 2 - cost P θ (M i k)
  | .multi k₀ k₁ => P.v ^ 2 / 2 + KK P - cost P θ (M 0 k₀) - cost P θ (M 1 k₁)

section basic
variable {P : Params} (hS : P.Standing)
include hS

lemma KK_pos : 0 < KK P := by
  obtain ⟨hv, -, -, -, -, -, hg, hg1⟩ := hS
  unfold KK rho
  have : 0 < (1 - P.γ) / (1 + P.γ) := div_pos (by linarith) (by linarith)
  positivity

lemma KK_lt : KK P < P.v ^ 2 / 2 := by
  obtain ⟨hv, -, -, -, -, -, hg, hg1⟩ := hS
  unfold KK rho
  have h1 : (1 - P.γ) / (1 + P.γ) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have : 0 < P.v ^ 2 := by positivity
  nlinarith

lemma multi_const : P.v ^ 2 / (1 + P.γ) = P.v ^ 2 / 2 + KK P := by
  obtain ⟨hv, -, -, -, -, -, hg, hg1⟩ := hS
  unfold KK rho
  have : (1 + P.γ) ≠ 0 := by linarith
  field_simp
  ring

lemma KK_eq' : KK P = (1 - P.γ) * P.v ^ 2 / (2 * (1 + P.γ)) := by
  obtain ⟨hv, -, -, -, -, -, hg, hg1⟩ := hS
  unfold KK rho
  have : (1 + P.γ) ≠ 0 := by linarith
  field_simp

lemma utility_single (θ : Ty) (M : Profile) (i k : Fin 2) :
    utility P θ M (.single i k) = P.v ^ 2 / 2 - cost P θ (M i k) := by
  obtain ⟨hv, -, -, -, -, -, hg, hg1⟩ := hS
  show sSup (singleUtil P θ (M i k) '' Set.Ici 0) = _
  apply IsGreatest.csSup_eq
  refine ⟨⟨P.v, Set.mem_Ici.mpr hv.le, ?_⟩, ?_⟩
  · simp only [singleUtil]; ring
  · rintro _ ⟨x, -, rfl⟩
    simp only [singleUtil]
    nlinarith [sq_nonneg (x - P.v)]

lemma utility_multi (θ : Ty) (M : Profile) (k₀ k₁ : Fin 2) :
    utility P θ M (.multi k₀ k₁) =
      P.v ^ 2 / 2 + KK P - cost P θ (M 0 k₀) - cost P θ (M 1 k₁) := by
  have hc := multi_const hS
  obtain ⟨hv, -, -, -, -, -, hg, hg1⟩ := hS
  show sSup ((fun x : ℝ × ℝ => multiUtil P θ (M 0 k₀) (M 1 k₁) x.1 x.2) ''
        (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))) = _
  rw [← hc]
  have hg0 : (1 + P.γ) ≠ 0 := by linarith
  set t := P.v / (1 + P.γ) with ht
  have ht0 : 0 ≤ t := div_nonneg hv.le (by linarith)
  have key : ∀ x₀ x₁ : ℝ, P.v ^ 2 / (1 + P.γ) -
      (P.v * x₀ - x₀ ^ 2 / 2 + (P.v * x₁ - x₁ ^ 2 / 2) - P.γ * x₀ * x₁) =
      ((1 - P.γ) * ((x₀ - t) ^ 2 + (x₁ - t) ^ 2) + P.γ * (x₀ + x₁ - 2 * t) ^ 2) / 2 := by
    intro x₀ x₁
    rw [ht]
    field_simp
    ring
  apply IsGreatest.csSup_eq
  refine ⟨⟨(t, t), ⟨Set.mem_Ici.mpr ht0, Set.mem_Ici.mpr ht0⟩, ?_⟩, ?_⟩
  · simp only [multiUtil]
    have := key t t
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      mul_zero, zero_div] at this
    have h2 : t + t - 2 * t = 0 := by ring
    rw [h2] at this
    simp at this
    linarith
  · rintro _ ⟨x, -, rfl⟩
    simp only [multiUtil]
    have := key x.1 x.2
    have h1 : 0 ≤ ((1 - P.γ) * ((x.1 - t) ^ 2 + (x.2 - t) ^ 2) + P.γ * (x.1 + x.2 - 2 * t) ^ 2) / 2 := by
      have : 0 ≤ 1 - P.γ := by linarith
      positivity
    linarith

lemma utility_eq (θ : Ty) (M : Profile) (c : Choice) : utility P θ M c = uval P θ M c := by
  cases c with
  | abstain => rfl
  | single i k => exact utility_single hS θ M i k
  | multi k₀ k₁ => exact utility_multi hS θ M k₀ k₁

end basic

/-! ## platform / choice helpers -/

lemma other_ne (i : Fin 2) : other i ≠ i := by fin_cases i <;> decide

lemma other_other (i : Fin 2) : other (other i) = i := by fin_cases i <;> rfl

lemma fin2_cases (i : Fin 2) (p : Fin 2) : p = i ∨ p = other i := by
  fin_cases i <;> fin_cases p <;> simp [other]

/-- multi-homing choice built from own slot `o` on platform `i` and rival slot `r`. -/
def mk (i o r : Fin 2) : Choice := if i = 0 then .multi o r else .multi r o

@[simp] lemma itemOn_mk_self (i o r : Fin 2) : (mk i o r).itemOn i = some o := by
  fin_cases i <;> simp [mk, Choice.itemOn]

@[simp] lemma itemOn_mk_other (i o r : Fin 2) : (mk i o r).itemOn (other i) = some r := by
  fin_cases i <;> simp [mk, Choice.itemOn, other]

lemma mk_isMulti (i o r : Fin 2) : (mk i o r).IsMulti := by
  unfold mk; split_ifs <;> trivial

lemma uval_mk (P : Params) (θ : Ty) (M : Profile) (i o r : Fin 2) :
    uval P θ M (mk i o r) =
      P.v ^ 2 / 2 + KK P - cost P θ (M i o) - cost P θ (M (other i) r) := by
  fin_cases i <;> simp [mk, uval, other] <;> ring

lemma adsSeen_mk (M : Profile) (i o r : Fin 2) :
    adsSeen M (mk i o r) = (M i o).2 + (M (other i) r).2 := by
  fin_cases i <;> simp [mk, adsSeen, other]; ring

lemma multi_eq_mk (i k₀ k₁ : Fin 2) :
    Choice.multi k₀ k₁ = mk i (if i = 0 then k₀ else k₁) (if i = 0 then k₁ else k₀) := by
  fin_cases i <;> simp [mk]

lemma isMulti_iff (c : Choice) (i : Fin 2) : c.IsMulti ↔ ∃ o r, c = mk i o r := by
  constructor
  · intro h
    cases c with
    | abstain => exact h.elim
    | single _ _ => exact h.elim
    | multi k₀ k₁ => exact ⟨_, _, multi_eq_mk i k₀ k₁⟩
  · rintro ⟨o, r, rfl⟩; exact mk_isMulti i o r

lemma itemOn_single_self (i k : Fin 2) : (Choice.single i k).itemOn i = some k := by
  simp [Choice.itemOn]

lemma itemOn_single_other (i k : Fin 2) : (Choice.single i k).itemOn (other i) = none := by
  simp [Choice.itemOn, Ne.symm (other_ne i)]

lemma platRev_some (P : Params) (M : Profile) (i : Fin 2) (c : Choice) (k : Fin 2)
    (h : c.itemOn i = some k) :
    platRev P M i c = (M i k).1 + (M i k).2 * (P.w - adsSeen M c) := by
  unfold platRev; rw [h]

lemma platRev_none (P : Params) (M : Profile) (i : Fin 2) (c : Choice)
    (h : c.itemOn i = none) : platRev P M i c = 0 := by
  unfold platRev; rw [h]

lemma expRev_split (P : Params) (M : Profile) (i : Fin 2) (c : Ty → Choice) (θ : Ty) :
    expRev P M i c = P.prob θ * platRev P M i (c θ) +
      P.prob (if θ = .L then .H else .L) * platRev P M i (c (if θ = .L then .H else .L)) := by
  cases θ <;> simp [expRev] ; ring

lemma prob_pos {P : Params} (hS : P.Standing) (θ : Ty) : 0 < P.prob θ := by
  obtain ⟨-, -, -, -, hr, hr1, -, -⟩ := hS
  cases θ <;> simp [Params.prob] <;> linarith

lemma update_self (M : Profile) (i : Fin 2) (M' : Menu) : Function.update M i M' i = M' := by
  simp

lemma update_other (M : Profile) (i : Fin 2) (M' : Menu) :
    Function.update M i M' (other i) = M (other i) := by
  simp [other_ne i]

/-! ## optimality via closed forms -/

section opt
variable {P : Params} (hS : P.Standing)
include hS

lemma opt_le {θ : Ty} {M : Profile} {c : Choice} (h : IsOptimal P θ M c) (c' : Choice) :
    uval P θ M c' ≤ uval P θ M c := by
  have := h c'; rwa [utility_eq hS, utility_eq hS] at this

lemma opt_of_bounds (θ : Ty) (M : Profile) (c : Choice) (m : Fin 2 → ℝ)
    (hm : ∀ p k, m p ≤ cost P θ (M p k)) (hA : 0 ≤ uval P θ M c)
    (hS1 : ∀ p, P.v ^ 2 / 2 - m p ≤ uval P θ M c)
    (hM : P.v ^ 2 / 2 + KK P - m 0 - m 1 ≤ uval P θ M c) : IsOptimal P θ M c := by
  intro c'
  rw [utility_eq hS, utility_eq hS]
  generalize uval P θ M c = u at *
  cases c' with
  | abstain => simpa [uval] using hA
  | single i k => simp only [uval]; linarith [hm i k, hS1 i]
  | multi k₀ k₁ => simp only [uval]; linarith [hm 0 k₀, hm 1 k₁]

omit hS in
lemma resp_of_multi {θ : Ty} {M : Profile} {c : Choice} (h : IsOptimal P θ M c)
    (hc : c.IsMulti) : IsResponse P θ M c := by
  refine ⟨h, fun _ => hc, fun _ => ?_⟩
  rintro rfl; exact hc

lemma resp_of_single {θ : Ty} {M : Profile} {i k : Fin 2} (h : IsOptimal P θ M (.single i k))
    (hlt : ∀ k₀ k₁, uval P θ M (.multi k₀ k₁) < uval P θ M (.single i k)) :
    IsResponse P θ M (.single i k) := by
  refine ⟨h, ?_, fun _ => by simp⟩
  rintro ⟨k₀, k₁, hk⟩
  have := opt_le hS hk (.single i k)
  linarith [hlt k₀ k₁]

/-- Lemma 6 E in closed form: the used slot minimizes cost. -/
lemma opt_min_cost {θ : Ty} {M : Profile} {c : Choice} (h : IsOptimal P θ M c) (i k : Fin 2)
    (hk : c.itemOn i = some k) (k' : Fin 2) : cost P θ (M i k) ≤ cost P θ (M i k') := by
  cases c with
  | abstain => simp [Choice.itemOn] at hk
  | single j l =>
    simp only [Choice.itemOn] at hk
    split_ifs at hk with hj
    · subst hj; cases hk
      have := opt_le hS h (.single j k')
      simp only [uval] at this; linarith
  | multi k₀ k₁ =>
    simp only [Choice.itemOn] at hk
    fin_cases i
    · simp at hk; subst hk
      have := opt_le hS h (.multi k' k₁)
      simp only [uval] at this; simp; linarith
    · simp at hk; subst hk
      have := opt_le hS h (.multi k₀ k')
      simp only [uval] at this; simp; linarith

/-- Lemma 6 C in closed form. -/
lemma opt_multi_cost {θ : Ty} {M : Profile} {i o r : Fin 2} (h : IsOptimal P θ M (mk i o r)) :
    cost P θ (M i o) ≤ KK P := by
  have := opt_le hS h (.single (other i) r)
  rw [uval_mk] at this; simp only [uval] at this; linarith

end opt

/-! ## responses -/

section resp
variable {P : Params} (hS : P.Standing)
include hS

lemma exists_response (θ : Ty) (M : Profile) (j : Fin 2 → Fin 2)
    (hj : ∀ p k, cost P θ (M p (j p)) ≤ cost P θ (M p k)) :
    ∃ c', IsResponse P θ M c' ∧ ∀ p k, c'.itemOn p = some k → k = j p := by
  have hK := KK_pos hS
  set u := P.v ^ 2 / 2 + KK P - cost P θ (M 0 (j 0)) - cost P θ (M 1 (j 1)) with hu
  set s0 := P.v ^ 2 / 2 - cost P θ (M 0 (j 0)) with hs0
  set s1 := P.v ^ 2 / 2 - cost P θ (M 1 (j 1)) with hs1
  have hm : ∀ p k, cost P θ (M p (j p)) ≤ cost P θ (M p k) := hj
  have hmulti : ∀ k₀ k₁, uval P θ M (.multi k₀ k₁) ≤ u := by
    intro k₀ k₁; simp only [uval]; linarith [hm 0 k₀, hm 1 k₁]
  have hsingle : ∀ p k, uval P θ M (.single p k) ≤ P.v ^ 2 / 2 - cost P θ (M p (j p)) := by
    intro p k; simp only [uval]; linarith [hm p k]
  have hsp : ∀ p, P.v ^ 2 / 2 - cost P θ (M p (j p)) ≤ max s0 s1 := by
    intro p; fin_cases p
    · exact le_max_left _ _
    · exact le_max_right _ _
  by_cases h1 : max s0 (max s1 0) ≤ u
  · refine ⟨.multi (j 0) (j 1), resp_of_multi (opt_of_bounds hS θ M _ (fun p => cost P θ (M p (j p)))
      hm ?_ ?_ ?_) trivial, ?_⟩
    · simp only [uval]; linarith [le_max_right s1 0, le_max_right s0 (max s1 0)]
    · intro p; simp only [uval]
      have := hsp p
      have : max s0 s1 ≤ max s0 (max s1 0) := max_le (le_max_left _ _)
        (le_trans (le_max_left _ _) (le_max_right _ _))
      linarith
    · simp only [uval]; linarith
    · intro p k hk
      fin_cases p <;> simp [Choice.itemOn] at hk <;> simp [hk]
  push Not at h1
  by_cases h2 : s1 ≤ s0 ∧ 0 ≤ s0
  · have hmax : max s0 (max s1 0) = s0 := by
      rw [max_eq_left (max_le h2.1 h2.2)]
    rw [hmax] at h1
    refine ⟨.single 0 (j 0), resp_of_single hS (opt_of_bounds hS θ M _
      (fun p => cost P θ (M p (j p))) hm ?_ ?_ ?_) ?_, ?_⟩
    · simp only [uval]; linarith
    · intro p; fin_cases p <;> simp only [uval] <;> simp <;> linarith
    · simp only [uval]; linarith
    · intro k₀ k₁; have := hmulti k₀ k₁; simp only [uval] at this ⊢; linarith
    · intro p k hk
      fin_cases p <;> simp [Choice.itemOn] at hk <;> simp [hk]
  by_cases h3 : 0 ≤ s1
  · have h4 : s0 ≤ s1 := by
      by_contra h; push Not at h; exact h2 ⟨h.le, le_trans h3 h.le⟩
    have hmax : max s0 (max s1 0) = s1 := by
      rw [max_eq_left h3, max_eq_right h4]
    rw [hmax] at h1
    refine ⟨.single 1 (j 1), resp_of_single hS (opt_of_bounds hS θ M _
      (fun p => cost P θ (M p (j p))) hm ?_ ?_ ?_) ?_, ?_⟩
    · simp only [uval]; linarith
    · intro p; fin_cases p <;> simp only [uval] <;> simp <;> linarith
    · simp only [uval]; linarith
    · intro k₀ k₁; have := hmulti k₀ k₁; simp only [uval] at this ⊢; linarith
    · intro p k hk
      fin_cases p <;> simp [Choice.itemOn] at hk <;> simp [hk]
  push Not at h3
  have h5 : s0 < 0 := by
    by_contra h; push Not at h; exact h2 ⟨by linarith, h⟩
  have hmax : max s0 (max s1 0) = 0 := by
    rw [max_eq_right h3.le, max_eq_right h5.le]
  rw [hmax] at h1
  have hall : ∀ c', c' ≠ .abstain → uval P θ M c' < 0 := by
    intro c' hc'
    cases c' with
    | abstain => exact absurd rfl hc'
    | single p k =>
      have := hsingle p k
      fin_cases p
      · simp at this ⊢; linarith
      · simp at this ⊢; linarith
    | multi k₀ k₁ => linarith [hmulti k₀ k₁]
  have hopt : IsOptimal P θ M .abstain := by
    intro c'
    rw [utility_eq hS, utility_eq hS]
    by_cases hc : c' = .abstain
    · rw [hc]
    · have := hall c' hc; show uval P θ M c' ≤ 0; linarith
  refine ⟨.abstain, ⟨hopt, ?_, ?_⟩, ?_⟩
  · rintro ⟨k₀, k₁, hk⟩
    have := opt_le hS hk .abstain
    have := hall (.multi k₀ k₁) (by simp)
    simp only [uval] at *; linarith
  · rintro ⟨c', hc', hk⟩
    have := opt_le hS hk .abstain
    have := hall c' hc'
    simp only [uval] at *; linarith
  · intro p k hk; simp [Choice.itemOn] at hk

/-- slot replacement -/
def replaceSlots (g : Fin 2 → Fin 2 → Fin 2) : Choice → Choice
  | .abstain => .abstain
  | .single p k => .single p (g p k)
  | .multi k₀ k₁ => .multi (g 0 k₀) (g 1 k₁)

omit hS in
lemma uval_congr (θ : Ty) (M M' : Profile) (c : Choice)
    (hsame : ∀ p k, c.itemOn p = some k → M' p k = M p k) :
    uval P θ M' c = uval P θ M c := by
  cases c with
  | abstain => rfl
  | single p k =>
    have := hsame p k (by simp [Choice.itemOn])
    simp only [uval, this]
  | multi k₀ k₁ =>
    have h0 := hsame 0 k₀ (by simp [Choice.itemOn])
    have h1 := hsame 1 k₁ (by simp [Choice.itemOn])
    simp only [uval, h0, h1]

omit hS in
lemma adsSeen_congr (M M' : Profile) (c : Choice)
    (hsame : ∀ p k, c.itemOn p = some k → M' p k = M p k) :
    adsSeen M' c = adsSeen M c := by
  cases c with
  | abstain => rfl
  | single p k =>
    have := hsame p k (by simp [Choice.itemOn])
    simp only [adsSeen, this]
  | multi k₀ k₁ =>
    have h0 := hsame 0 k₀ (by simp [Choice.itemOn])
    have h1 := hsame 1 k₁ (by simp [Choice.itemOn])
    simp only [adsSeen, h0, h1]

omit hS in
lemma platRev_congr (M M' : Profile) (i : Fin 2) (c : Choice)
    (hsame : ∀ p k, c.itemOn p = some k → M' p k = M p k) :
    platRev P M' i c = platRev P M i c := by
  rcases h : c.itemOn i with _ | k
  · rw [platRev_none _ _ _ _ h, platRev_none _ _ _ _ h]
  · rw [platRev_some _ _ _ _ _ h, platRev_some _ _ _ _ _ h, adsSeen_congr M M' c hsame,
      hsame i k h]

lemma resp_preserved {θ : Ty} {M M' : Profile} {c : Choice}
    (hdom : ∀ p k, ∃ k₂, cost P θ (M p k₂) ≤ cost P θ (M' p k))
    (hsame : ∀ p k, c.itemOn p = some k → M' p k = M p k)
    (hc : IsResponse P θ M c) : IsResponse P θ M' c := by
  choose g hg using hdom
  have hrep : ∀ c', uval P θ M' c' ≤ uval P θ M (replaceSlots g c') := by
    intro c'
    cases c' with
    | abstain => simp [replaceSlots, uval]
    | single p k => simp only [replaceSlots, uval]; linarith [hg p k]
    | multi k₀ k₁ => simp only [replaceSlots, uval]; linarith [hg 0 k₀, hg 1 k₁]
  have heq := uval_congr (P := P) θ M M' c hsame
  have hopt : IsOptimal P θ M' c := by
    intro c'
    rw [utility_eq hS, utility_eq hS, heq]
    exact le_trans (hrep c') (opt_le hS hc.1 _)
  refine ⟨hopt, ?_, ?_⟩
  · rintro ⟨k₀, k₁, hk⟩
    apply hc.2.1
    refine ⟨g 0 k₀, g 1 k₁, ?_⟩
    intro c''
    have h1 := opt_le hS hk c
    have h2 := hrep (.multi k₀ k₁)
    have h3 := opt_le hS hc.1 c''
    rw [utility_eq hS, utility_eq hS]
    simp only [replaceSlots] at h2
    linarith
  · rintro ⟨c', hc', hk⟩
    apply hc.2.2
    refine ⟨replaceSlots g c', ?_, ?_⟩
    · cases c' <;> simp_all [replaceSlots]
    · intro c''
      have h1 := opt_le hS hk c
      have h2 := hrep c'
      have h3 := opt_le hS hc.1 c''
      rw [utility_eq hS, utility_eq hS]
      linarith

end resp

/-! ## Lemma 8 -/

def Ty.oth : Ty → Ty
  | .L => .H
  | .H => .L

lemma Ty.oth_ne (θ : Ty) : θ.oth ≠ θ := by cases θ <;> decide

lemma Ty.oth_oth (θ : Ty) : θ.oth.oth = θ := by cases θ <;> rfl

lemma expRev_split' (P : Params) (M : Profile) (i : Fin 2) (c : Ty → Choice) (θ : Ty) :
    expRev P M i c = P.prob θ * platRev P M i (c θ) + P.prob θ.oth * platRev P M i (c θ.oth) := by
  cases θ <;> simp [expRev, Ty.oth] ; ring

lemma Ty.eq_or_oth (τ θ : Ty) : τ = θ ∨ τ = θ.oth := by
  cases τ <;> cases θ <;> simp [Ty.oth]

lemma cost_N (P : Params) (τ : Ty) (x : ℝ) : cost P τ ((x, 0) : Item) = x := by
  simp [cost]

lemma sum_fin2 (f : Fin 2 → ℝ) (q : Fin 2) : f 0 + f 1 = f q + f (other q) := by
  fin_cases q <;> simp [other]; ring

noncomputable def argminSlot (P : Params) (θ : Ty) (Mp : Menu) : Fin 2 :=
  if cost P θ (Mp 0) ≤ cost P θ (Mp 1) then 0 else 1

lemma argminSlot_le (P : Params) (θ : Ty) (Mp : Menu) (k : Fin 2) :
    cost P θ (Mp (argminSlot P θ Mp)) ≤ cost P θ (Mp k) := by
  unfold argminSlot
  split_ifs with h <;> fin_cases k <;> simp_all; linarith

section lemma8
variable {P : Params} (hS : P.Standing)
include hS

lemma opt_of_bounds' (θ : Ty) (M : Profile) (c : Choice) (q : Fin 2) (m : Fin 2 → ℝ)
    (hm : ∀ p k, m p ≤ cost P θ (M p k)) (hA : 0 ≤ uval P θ M c)
    (hS1 : ∀ p, P.v ^ 2 / 2 - m p ≤ uval P θ M c)
    (hM : P.v ^ 2 / 2 + KK P - m q - m (other q) ≤ uval P θ M c) : IsOptimal P θ M c :=
  opt_of_bounds hS θ M c m hm hA hS1 (by linarith [sum_fin2 m q])

/-- the rival-slot used by a type, or a cheapest one. -/
noncomputable def keepSlot (P : Params) (θ : Ty) (M : Profile) (c : Choice) (p : Fin 2) : Fin 2 :=
  match c.itemOn p with
  | some e => e
  | none => argminSlot P θ (M p)

omit hS in
lemma keepSlot_some (θ : Ty) (M : Profile) (c : Choice) (p e : Fin 2) (h : c.itemOn p = some e) :
    keepSlot P θ M c p = e := by
  unfold keepSlot; rw [h]

lemma keepSlot_le {θ : Ty} {M : Profile} {c : Choice} (hc : IsOptimal P θ M c) (p k : Fin 2) :
    cost P θ (M p (keepSlot P θ M c p)) ≤ cost P θ (M p k) := by
  unfold keepSlot
  rcases h : c.itemOn p with _ | e
  · exact argminSlot_le P θ (M p) k
  · exact opt_min_cost hS hc p e h k

/-- Response of a type to a platform `q` whose cheapest item `fN` costs exactly `K`. -/
lemma attract_resp (θ : Ty) (M2 : Profile) (q fN e : Fin 2)
    (hfN : cost P θ (M2 q fN) = KK P) (hq : ∀ k, KK P ≤ cost P θ (M2 q k))
    (he : ∀ k, cost P θ (M2 (other q) e) ≤ cost P θ (M2 (other q) k)) :
    ∃ c', IsResponse P θ M2 c' ∧ c'.itemOn q = some fN ∧
      (∀ k', c'.itemOn (other q) = some k' → k' = e) := by
  have hK := KK_pos hS
  have hKV := KK_lt hS
  set mp := cost P θ (M2 (other q) e)
  let m : Fin 2 → ℝ := fun x => if x = q then KK P else mp
  have hmq : m q = KK P := by simp [m]
  have hmo : m (other q) = mp := by simp [m, other_ne q]
  have hm : ∀ p k, m p ≤ cost P θ (M2 p k) := by
    intro p k
    rcases fin2_cases q p with rfl | rfl
    · rw [hmq]; exact hq k
    · rw [hmo]; exact he k
  by_cases h : mp ≤ KK P
  · refine ⟨mk q fN e, resp_of_multi (opt_of_bounds' hS θ M2 _ q m hm ?_ ?_ ?_) (mk_isMulti _ _ _),
      itemOn_mk_self _ _ _, fun k' hk' => ?_⟩
    · rw [uval_mk, hfN]; linarith
    · intro p; rw [uval_mk, hfN]
      rcases fin2_cases q p with rfl | rfl
      · rw [hmq]; linarith
      · rw [hmo]; linarith
    · rw [uval_mk, hfN, hmq, hmo]
    · rw [itemOn_mk_other] at hk'; exact (Option.some.inj hk').symm
  · push Not at h
    refine ⟨.single q fN, resp_of_single hS (opt_of_bounds' hS θ M2 _ q m hm ?_ ?_ ?_) ?_,
      itemOn_single_self _ _, fun k' hk' => ?_⟩
    · simp only [uval]; rw [hfN]; linarith
    · intro p; simp only [uval]; rw [hfN]
      rcases fin2_cases q p with rfl | rfl
      · rw [hmq]
      · rw [hmo]; linarith
    · simp only [uval]; rw [hfN, hmq, hmo]; linarith
    · intro k₀ k₁
      rw [multi_eq_mk q, uval_mk]; simp only [uval]; rw [hfN]
      linarith [hm q (if q = 0 then k₀ else k₁), hm (other q) (if q = 0 then k₁ else k₀), hmq, hmo]
    · rw [itemOn_single_other] at hk'; cases hk'

lemma dev_core {M : Profile} {c : Ty → Choice} (hE : IsEquilibrium P M c) (θ : Ty) (q : Fin 2)
    (hθq : (c θ).itemOn q = none) (M' : Menu) (hadm' : M'.Admissible) (fN : Fin 2)
    (hfN : M' fN = ((KK P, 0) : Item)) (hθc' : ∀ k, KK P ≤ cost P θ (M' k)) (c2 : Choice)
    (hc2 : IsResponse P θ.oth (Function.update M q M') c2)
    (hkeep2 : ∀ k k', (c θ.oth).itemOn (other q) = some k → c2.itemOn (other q) = some k' → k' = k)
    (hrev : platRev P M q (c θ.oth) ≤ platRev P (Function.update M q M') q c2) : False := by
  have hK := KK_pos hS
  obtain ⟨hadm, hresp, hdev⟩ := hE
  set M2 := Function.update M q M' with hM2
  have hM2q : M2 q = M' := by simp [M2]
  have hM2o : M2 (other q) = M (other q) := by simp [M2, other_ne q]
  set e := keepSlot P θ M (c θ) (other q)
  obtain ⟨cθ, hcθ, hcθq, hcθo⟩ := attract_resp hS θ M2 q fN e
    (by rw [hM2q, hfN]; simp [cost]) (by rw [hM2q]; exact hθc')
    (by rw [hM2o]; exact keepSlot_le hS (hresp θ).1 (other q))
  let c' : Ty → Choice := fun τ => if τ = θ then cθ else c2
  have hc'θ : c' θ = cθ := if_pos rfl
  have hc'o : c' θ.oth = c2 := if_neg (Ty.oth_ne θ)
  have hresp' : ∀ τ, IsResponse P τ M2 (c' τ) := by
    intro τ
    rcases Ty.eq_or_oth τ θ with h | h
    · rw [h, hc'θ]; exact hcθ
    · rw [h, hc'o]; exact hc2
  have hkeep' : ∀ τ k k', (c τ).itemOn (other q) = some k → (c' τ).itemOn (other q) = some k' →
      k' = k := by
    intro τ k k' h1 h2
    rcases Ty.eq_or_oth τ θ with h | h
    · rw [h] at h1 h2; rw [hc'θ] at h2
      rw [hcθo k' h2]; exact keepSlot_some θ M (c θ) (other q) k h1
    · rw [h] at h1 h2; rw [hc'o] at h2; exact hkeep2 k k' h1 h2
  have := hdev q M' hadm' c' hresp' hkeep'
  rw [expRev_split' P _ _ _ θ, expRev_split' P _ _ _ θ, hc'θ, hc'o] at this
  rw [platRev_some P M2 q cθ fN hcθq, hM2q, hfN, platRev_none P M q (c θ) hθq] at this
  have h1 := prob_pos hS θ
  have h2 := prob_pos hS θ.oth
  simp only [zero_mul, add_zero, mul_zero, zero_add] at this
  nlinarith

lemma dev1 {M : Profile} {c : Ty → Choice} (hE : IsEquilibrium P M c) (θ : Ty) (q : Fin 2)
    (hθq : (c θ).itemOn q = none) (hθc : ∀ k, KK P ≤ cost P θ (M q k))
    (hθ' : ∀ k', (c θ.oth).itemOn q = some k' → cost P θ.oth (M q k') ≤ KK P) : False := by
  have hK := KK_pos hS
  have hresp := hE.2.1
  rcases hq' : (c θ.oth).itemOn q with _ | k'
  · -- the other type does not use `q`: offer `N` in both slots
    let N : Item := (KK P, 0)
    let M' : Menu := fun _ => N
    set M2 := Function.update M q M' with hM2
    have hM2q : M2 q = M' := by simp [M2]
    have hM2o : M2 (other q) = M (other q) := by simp [M2, other_ne q]
    let j : Fin 2 → Fin 2 := fun x => if x = q then 0 else keepSlot P θ.oth M (c θ.oth) (other q)
    have hj : ∀ p k, cost P θ.oth (M2 p (j p)) ≤ cost P θ.oth (M2 p k) := by
      intro p k
      rcases fin2_cases q p with h | h <;> rw [h]
      · rw [hM2q]
      · rw [hM2o]; simp only [j, if_neg (other_ne q)]
        exact keepSlot_le hS (hresp θ.oth).1 (other q) k
    obtain ⟨c2, hc2, hc2j⟩ := exists_response hS θ.oth M2 j hj
    refine dev_core hS hE θ q hθq M' (fun _ => le_refl _) 0 rfl (fun k => by simp [M', N, cost])
      c2 hc2 ?_ ?_
    · intro k k'' h1 h2
      have := hc2j (other q) k'' h2
      simp only [j, if_neg (other_ne q)] at this
      rw [this]; exact keepSlot_some θ.oth M (c θ.oth) (other q) k h1
    · rw [platRev_none P M q _ hq']
      rcases h : c2.itemOn q with _ | k
      · rw [platRev_none P _ q _ h]
      · rw [platRev_some P _ q _ k h]; simp [M', N]; linarith
  · -- the other type uses `q` with slot `k'`, cheap: put `N` in the other slot
    have hk'c := hθ' k' hq'
    let N : Item := (KK P, 0)
    let M' : Menu := Function.update (M q) (other k') N
    set M2 := Function.update M q M' with hM2
    have hM2q : M2 q = M' := by simp [M2]
    have hM2o : M2 (other q) = M (other q) := by simp [M2, other_ne q]
    have hM'k' : M' k' = M q k' := by simp [M', Ne.symm (other_ne k')]
    have hM'N : M' (other k') = N := by simp [M']
    have hadm' : M'.Admissible := by
      intro k
      rcases fin2_cases k' k with h | h <;> rw [h]
      · rw [hM'k']; exact hE.1 q k'
      · rw [hM'N]
    have hθc' : ∀ k, KK P ≤ cost P θ (M' k) := by
      intro k
      rcases fin2_cases k' k with h | h <;> rw [h]
      · rw [hM'k']; exact hθc k'
      · rw [hM'N, cost_N]
    have hsame : ∀ p k, (c θ.oth).itemOn p = some k → M2 p k = M p k := by
      intro p k hk
      rcases fin2_cases q p with h | h <;> rw [h] at hk ⊢
      · rw [hq'] at hk; cases hk; rw [hM2q, hM'k']
      · rw [hM2o]
    have hdom : ∀ p k, ∃ k₂, cost P θ.oth (M p k₂) ≤ cost P θ.oth (M2 p k) := by
      intro p k
      rcases fin2_cases q p with h | h <;> rw [h]
      · rw [hM2q]
        rcases fin2_cases k' k with h' | h' <;> rw [h']
        · exact ⟨k', by rw [hM'k']⟩
        · exact ⟨k', by rw [hM'N, cost_N]; exact hk'c⟩
      · exact ⟨k, by rw [hM2o]⟩
    refine dev_core hS hE θ q hθq M' hadm' (other k') hM'N hθc' (c θ.oth)
      (resp_preserved hS hdom hsame (hresp θ.oth)) ?_ ?_
    · intro k k'' h1 h2; rw [h1] at h2; exact (Option.some.inj h2).symm
    · rw [platRev_congr M M2 q _ hsame]

lemma dev2 {M : Profile} {c : Ty → Choice} (hE : IsEquilibrium P M c) (θ : Ty) (p e e' : Fin 2)
    (hθ : c θ = .single p e) (hθ' : c θ.oth = .single (other p) e')
    (hgt : KK P < cost P θ (M p e)) (hge : cost P θ.oth (M (other p) e') ≤ cost P θ (M p e)) :
    False := by
  have hK := KK_pos hS
  obtain ⟨hadm, hresp, hdev⟩ := hE
  set q := other p with hq
  have hqp : other q = p := other_other p
  set cθ := cost P θ (M p e)
  let N : Item := (cθ, 0)
  let M' : Menu := Function.update (M q) (other e') N
  set M2 := Function.update M q M' with hM2
  have hM2q : M2 q = M' := by simp [M2]
  have hM2o : M2 p = M p := by rw [← hqp]; simp [M2, other_ne q]
  have hM'e' : M' e' = M q e' := by simp [M', Ne.symm (other_ne e')]
  have hM'N : M' (other e') = N := by simp [M']
  have hadm' : M'.Admissible := by
    intro k
    rcases fin2_cases e' k with h | h <;> rw [h]
    · rw [hM'e']; exact hadm q e'
    · rw [hM'N]
  have hoptθ := (hresp θ).1
  rw [hθ] at hoptθ
  -- θ's new response: single-home on `q` with `N`
  have hθq : ∀ k, cθ ≤ cost P θ (M q k) := by
    intro k
    have := opt_le hS hoptθ (.single q k)
    simp only [uval] at this; linarith
  have hθp : ∀ k, cθ ≤ cost P θ (M p k) := fun k =>
    opt_min_cost hS hoptθ p e (by simp [Choice.itemOn]) k
  have hθ0 : 0 ≤ P.v ^ 2 / 2 - cθ := by
    have := opt_le hS hoptθ .abstain
    simpa [uval] using this
  have hm : ∀ x k, (fun _ : Fin 2 => cθ) x ≤ cost P θ (M2 x k) := by
    intro x k
    rcases fin2_cases q x with h | h <;> rw [h]
    · rw [hM2q]
      rcases fin2_cases e' k with h' | h' <;> rw [h']
      · rw [hM'e']; exact hθq e'
      · rw [hM'N, cost_N]
    · rw [hqp, hM2o]; exact hθp k
  have huθ : uval P θ M2 (.single q (other e')) = P.v ^ 2 / 2 - cθ := by
    simp only [uval]; rw [hM2q, hM'N, cost_N]
  have hrθ : IsResponse P θ M2 (.single q (other e')) := by
    refine resp_of_single hS (opt_of_bounds hS θ M2 _ (fun _ => cθ) hm ?_ ?_ ?_) ?_
    · rw [huθ]; exact hθ0
    · intro x; rw [huθ]
    · rw [huθ]; linarith
    · intro k₀ k₁; rw [huθ]; simp only [uval]
      linarith [hm 0 k₀, hm 1 k₁]
  -- θ' keeps her choice
  have hsame : ∀ x k, (c θ.oth).itemOn x = some k → M2 x k = M x k := by
    intro x k hk
    rw [hθ'] at hk
    rcases fin2_cases q x with h | h <;> rw [h] at hk ⊢
    · simp [Choice.itemOn] at hk; subst hk; rw [hM2q, hM'e']
    · rw [hqp] at hk ⊢; rw [hM2o]
  have hdom : ∀ x k, ∃ k₂, cost P θ.oth (M x k₂) ≤ cost P θ.oth (M2 x k) := by
    intro x k
    rcases fin2_cases q x with h | h <;> rw [h]
    · rw [hM2q]
      rcases fin2_cases e' k with h' | h' <;> rw [h']
      · exact ⟨e', by rw [hM'e']⟩
      · exact ⟨e', by rw [hM'N, cost_N]; exact hge⟩
    · rw [hqp, hM2o]; exact ⟨k, le_refl _⟩
  have hrθ' := resp_preserved hS hdom hsame (hresp θ.oth)
  let c' : Ty → Choice := fun τ => if τ = θ then .single q (other e') else c θ.oth
  have hc'θ : c' θ = .single q (other e') := if_pos rfl
  have hc'o : c' θ.oth = c θ.oth := if_neg (Ty.oth_ne θ)
  have hresp' : ∀ τ, IsResponse P τ M2 (c' τ) := by
    intro τ
    rcases Ty.eq_or_oth τ θ with h | h
    · rw [h, hc'θ]; exact hrθ
    · rw [h, hc'o]; exact hrθ'
  have hkeep' : ∀ τ k k', (c τ).itemOn (other q) = some k → (c' τ).itemOn (other q) = some k' →
      k' = k := by
    intro τ k k' h1 h2
    rcases Ty.eq_or_oth τ θ with h | h
    · rw [h, hc'θ, itemOn_single_other] at h2; cases h2
    · rw [h] at h1 h2; rw [hc'o, h1] at h2; exact (Option.some.inj h2).symm
  have := hdev q M' hadm' c' hresp' hkeep'
  rw [expRev_split' P _ _ _ θ, expRev_split' P _ _ _ θ, hc'θ, hc'o] at this
  rw [platRev_some P M2 q _ (other e') (itemOn_single_self _ _), hM2q, hM'N,
    platRev_congr M M2 q _ hsame, hθ] at this
  have hθnone : (Choice.single p e).itemOn q = none := by
    rw [hq]; exact itemOn_single_other p e
  rw [platRev_none P M q _ hθnone] at this
  have h1 := prob_pos hS θ
  simp only [zero_mul, add_zero, mul_zero] at this
  nlinarith

lemma abstain_free {θ : Ty} {M : Profile} (hc : IsResponse P θ M .abstain) (q k : Fin 2) :
    P.v ^ 2 / 2 < cost P θ (M q k) := by
  by_contra h; push Not at h
  apply hc.2.2 ⟨.single q k, by simp, ?_⟩ rfl
  intro c'
  have := opt_le hS hc.1 c'
  rw [utility_eq hS, utility_eq hS]
  simp only [uval] at this ⊢; linarith

lemma single_free {θ : Ty} {M : Profile} {q k' : Fin 2} (hc : IsResponse P θ M (.single q k'))
    (k : Fin 2) : KK P < cost P θ (M (other q) k) := by
  by_contra h; push Not at h
  have hopt : IsOptimal P θ M (mk q k' k) := by
    intro c'
    rw [utility_eq hS, utility_eq hS, uval_mk]
    have h1 := opt_le hS hc.1 c'
    have h2 : uval P θ M (.single q k') = P.v ^ 2 / 2 - cost P θ (M q k') := rfl
    linarith
  have : (Choice.single q k').IsMulti := by
    apply hc.2.1
    unfold mk at hopt
    split_ifs at hopt
    · exact ⟨_, _, hopt⟩
    · exact ⟨_, _, hopt⟩
  exact this

theorem lemma8' {M : Profile} {c : Ty → Choice} (hE : IsEquilibrium P M c) :
    ∀ θ, (c θ).IsMulti := by
  intro θ
  by_contra hθ
  have hresp := hE.2.1
  have hKV := KK_lt hS
  obtain ⟨q, hθq, hθc⟩ : ∃ q, (c θ).itemOn q = none ∧ ∀ k, KK P ≤ cost P θ (M q k) := by
    rcases h : c θ with _ | ⟨p, e⟩ | ⟨k0, k1⟩
    · have hr := hresp θ; rw [h] at hr
      refine ⟨0, by simp [Choice.itemOn], fun k => ?_⟩
      have := abstain_free hS hr 0 k; linarith
    · have hr := hresp θ; rw [h] at hr
      exact ⟨other p, itemOn_single_other p e, fun k => (single_free hS hr k).le⟩
    · exact absurd (by rw [h]; trivial) hθ
  have hτo : θ.oth.oth = θ := Ty.oth_oth θ
  rcases hτq : (c θ.oth).itemOn q with _ | k'
  · exact dev1 hS hE θ q hθq hθc (by intro k' h; rw [hτq] at h; cases h)
  by_cases hk'c : cost P θ.oth (M q k') ≤ KK P
  · exact dev1 hS hE θ q hθq hθc (by intro k'' h; rw [hτq] at h; cases h; exact hk'c)
  push Not at hk'c
  have hτs : c θ.oth = .single q k' := by
    rcases h : c θ.oth with _ | ⟨q', e⟩ | ⟨k0, k1⟩
    · rw [h] at hτq; simp [Choice.itemOn] at hτq
    · rw [h] at hτq; simp [Choice.itemOn] at hτq; obtain ⟨rfl, rfl⟩ := hτq; rfl
    · exfalso
      have hopt := (hresp θ.oth).1
      rw [h, multi_eq_mk q] at hopt
      have := opt_multi_cost hS hopt
      rw [h] at hτq
      simp only [Choice.itemOn] at hτq
      have hk := Option.some.inj hτq
      rw [hk] at this; linarith
  have hrτ := hresp θ.oth
  rw [hτs] at hrτ
  have hτfree : ∀ k, KK P < cost P θ.oth (M (other q) k) := single_free hS hrτ
  rcases hθs : c θ with _ | ⟨p, e⟩ | ⟨k0, k1⟩
  · have hr := hresp θ; rw [hθs] at hr
    apply dev1 hS hE θ (other q) (by rw [hθs]; simp [Choice.itemOn])
      (fun k => by have := abstain_free hS hr (other q) k; linarith)
    intro k'' h; rw [hτs, itemOn_single_other] at h; cases h
  · have hp : p = other q := by
      rw [hθs] at hθq
      simp only [Choice.itemOn] at hθq
      split_ifs at hθq with hpq
      rcases fin2_cases q p with h | h
      · exact absurd h hpq
      · exact h
    subst hp
    by_cases hθc2 : cost P θ (M (other q) e) ≤ KK P
    · apply dev1 hS hE θ.oth (other q) (by rw [hτs]; exact itemOn_single_other q k')
        (fun k => (hτfree k).le)
      intro k'' h; rw [hτo, hθs] at h; simp [Choice.itemOn] at h; subst h; rw [hτo]; exact hθc2
    · push Not at hθc2
      by_cases hcmp : cost P θ.oth (M q k') ≤ cost P θ (M (other q) e)
      · exact dev2 hS hE θ (other q) e k' hθs (by rw [other_other]; exact hτs) hθc2
          (by rw [other_other]; exact hcmp)
      · push Not at hcmp
        exact dev2 hS hE θ.oth q k' e hτs (by rw [hτo]; exact hθs) hk'c (by rw [hτo]; exact hcmp.le)
  · exact hθ (by rw [hθs]; trivial)

end lemma8

/-! ## algebra of α and the equilibrium items -/

noncomputable def betaQ (P : Params) : ℝ := P.w - P.dH - (1 - P.r) * (P.dH - P.dL) / P.r

section alg
variable {P : Params} (hS : P.Standing)
include hS

lemma r_beta : P.r * betaQ P = P.r * (P.w - P.dH) - (1 - P.r) * (P.dH - P.dL) := by
  obtain ⟨-, -, -, -, hr, -, -, -⟩ := hS
  unfold betaQ; field_simp

omit hS in
lemma alpha_cases : (alphaQ P = betaQ P ∧ 0 ≤ betaQ P) ∨ (alphaQ P = 0 ∧ betaQ P ≤ 0) := by
  unfold alphaQ betaQ
  rcases le_total 0 (P.w - P.dH - (1 - P.r) * (P.dH - P.dL) / P.r) with h | h
  · left; exact ⟨max_eq_left h, h⟩
  · right; exact ⟨max_eq_right h, h⟩

omit hS in
lemma alpha_nonneg : 0 ≤ alphaQ P := le_max_right _ _

lemma beta_lt : betaQ P < P.w - P.dL := by
  obtain ⟨-, -, hd, -, hr, hr1, -, -⟩ := hS
  unfold betaQ
  have : 0 ≤ (1 - P.r) * (P.dH - P.dL) / P.r := div_nonneg (by nlinarith) hr.le
  linarith

lemma alpha_lt : alphaQ P < P.w - P.dL := by
  have := beta_lt hS
  obtain ⟨-, -, -, hw, -, -, -, -⟩ := hS
  unfold alphaQ; exact max_lt (by unfold betaQ at this; linarith) (by linarith)

/-- the screening bound -/
lemma screen_bound (x y sL sH : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hH : P.dH * y + sH ≤ KK P)
    (hL : P.dL * x + sL ≤ P.dL * y + sH) :
    (1 - P.r) * (sL + x * (P.w - (x + (P.w - P.dL) / 3))) +
      P.r * (sH + y * (P.w - (y + alphaQ P / 3))) ≤
    KK P + ((1 - P.r) * (P.w - P.dL) ^ 2 + P.r * alphaQ P ^ 2) / 9 := by
  have hrb := r_beta hS
  obtain ⟨-, -, hd, -, hr, hr1, -, -⟩ := hS
  have e1 : (1 - P.r) * (sL + x * (P.w - (x + (P.w - P.dL) / 3))) ≤
      (1 - P.r) * (KK P - P.dH * y + P.dL * y - P.dL * x + x * (P.w - (x + (P.w - P.dL) / 3))) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have e2 : P.r * (sH + y * (P.w - (y + alphaQ P / 3))) ≤
      P.r * (KK P - P.dH * y + y * (P.w - (y + alphaQ P / 3))) :=
    mul_le_mul_of_nonneg_left (by linarith) hr.le
  have e3 : (1 - P.r) * (x * (P.w - P.dL - x - (P.w - P.dL) / 3)) ≤ (1 - P.r) * ((P.w - P.dL) ^ 2 / 9) :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (x - (P.w - P.dL) / 3)]) (by linarith)
  have e4 : P.r * (y * (betaQ P - alphaQ P / 3 - y)) ≤ P.r * (alphaQ P ^ 2 / 9) := by
    apply mul_le_mul_of_nonneg_left _ hr.le
    rcases alpha_cases (P := P) with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha]; nlinarith [sq_nonneg (y - betaQ P / 3)]
    · rw [ha]; nlinarith
  have key : P.r * (y * (betaQ P - alphaQ P / 3 - y)) =
      P.r * (y * (P.w - P.dH - alphaQ P / 3 - y)) - (1 - P.r) * (P.dH - P.dL) * y := by
    have : P.r * (y * (betaQ P - alphaQ P / 3 - y)) = y * (P.r * betaQ P) - P.r * y * (alphaQ P / 3 + y) := by ring
    rw [this, hrb]; ring
  nlinarith

end alg

/-! ## existence -/

def eqSlot : Ty → Fin 2
  | .L => 0
  | .H => 1

lemma eqChoice_itemOn (θ : Ty) (i : Fin 2) : (eqChoice θ).itemOn i = some (eqSlot θ) := by
  cases θ <;> fin_cases i <;> rfl

section exist
variable {P : Params} (hS : P.Standing)
include hS

omit hS in
lemma cost_eqL_L : cost P .L (eqItem P .L) = KK P - (P.dH - P.dL) * (alphaQ P / 3) := by
  simp [cost, eqItem, Params.d, KK]; ring

omit hS in
lemma cost_eqH_L : cost P .L (eqItem P .H) = KK P - (P.dH - P.dL) * (alphaQ P / 3) := by
  simp [cost, eqItem, Params.d, KK]; ring

omit hS in
lemma cost_eqH_H : cost P .H (eqItem P .H) = KK P := by
  simp [cost, eqItem, Params.d, KK]

omit hS in
lemma cost_eqL_H : cost P .H (eqItem P .L) =
    KK P + (P.dH - P.dL) * ((P.w - P.dL) / 3 - alphaQ P / 3) := by
  simp [cost, eqItem, Params.d, KK]; ring

lemma eqMenu_cost_ge (θ : Ty) (k : Fin 2) :
    cost P θ (eqItem P θ) ≤ cost P θ (eqMenu P k) := by
  have ha := alpha_lt hS
  have ha0 := alpha_nonneg (P := P)
  obtain ⟨-, -, hd, -, -, -, -, -⟩ := hS
  cases θ <;> fin_cases k <;> simp [eqMenu]
  · rw [cost_eqL_L, cost_eqH_L]
  · rw [cost_eqL_H, cost_eqH_H]; nlinarith

omit hS in
lemma eqMenu_slot (θ : Ty) : eqMenu P (eqSlot θ) = eqItem P θ := by
  cases θ <;> rfl

lemma eqItem_cost_le (θ : Ty) : cost P θ (eqItem P θ) ≤ KK P := by
  have ha0 := alpha_nonneg (P := P)
  obtain ⟨-, -, hd, -, -, -, -, -⟩ := hS
  cases θ
  · rw [cost_eqL_L]; nlinarith
  · rw [cost_eqH_H]

theorem consumer_choices' : ∀ θ, IsResponse P θ (fun _ => eqMenu P) (eqChoice θ) := by
  intro θ
  have hK := KK_pos hS
  have hKV := KK_lt hS
  have hle := eqItem_cost_le hS θ
  have hm : ∀ p k, (fun _ : Fin 2 => cost P θ (eqItem P θ)) p ≤
      cost P θ ((fun _ => eqMenu P) p k) := fun p k => eqMenu_cost_ge hS θ k
  have hu : uval P θ (fun _ => eqMenu P) (eqChoice θ) =
      P.v ^ 2 / 2 + KK P - cost P θ (eqItem P θ) - cost P θ (eqItem P θ) := by
    cases θ <;> rfl
  refine resp_of_multi (opt_of_bounds hS θ _ _ _ hm ?_ ?_ ?_) (by cases θ <;> trivial)
  · rw [hu]; linarith
  · intro p; rw [hu]; linarith
  · rw [hu]

lemma eq_revenue (i : Fin 2) :
    expRev P (fun _ => eqMenu P) i eqChoice =
      rho P * P.v ^ 2 / 2 + ((1 - P.r) * (P.w - P.dL) ^ 2 + P.r * alphaQ P ^ 2) / 9 := by
  have hrb := r_beta hS
  have h1 : platRev P (fun _ => eqMenu P) i (eqChoice .L) =
      (eqItem P .L).1 + (eqItem P .L).2 * (P.w - ((eqItem P .L).2 + (eqItem P .L).2)) := by
    rw [platRev_some P _ i _ 0 (eqChoice_itemOn .L i)]; rfl
  have h2 : platRev P (fun _ => eqMenu P) i (eqChoice .H) =
      (eqItem P .H).1 + (eqItem P .H).2 * (P.w - ((eqItem P .H).2 + (eqItem P .H).2)) := by
    rw [platRev_some P _ i _ 1 (eqChoice_itemOn .H i)]; rfl
  unfold expRev; rw [h1, h2]
  simp only [eqItem, Params.prob]
  rcases alpha_cases (P := P) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha]
    have : P.r * (betaQ P / 3 * (P.w - (betaQ P / 3 + betaQ P / 3)) - P.dH * (betaQ P / 3))
        - (1 - P.r) * (P.dH - P.dL) * (betaQ P / 3) = P.r * betaQ P ^ 2 / 9 := by
      have : P.r * (betaQ P / 3 * (P.w - (betaQ P / 3 + betaQ P / 3)) - P.dH * (betaQ P / 3))
        - (1 - P.r) * (P.dH - P.dL) * (betaQ P / 3) =
          betaQ P / 3 * (P.r * (P.w - P.dH) - (1 - P.r) * (P.dH - P.dL)) - 2 * P.r * betaQ P ^ 2 / 9 := by ring
      rw [this, ← hrb]; ring
    linear_combination this
  · rw [ha]; ring

lemma multi_of_uses {θ : Ty} {M : Profile} {c : Choice} (hc : IsResponse P θ M c) {i k r : Fin 2}
    (hk : c.itemOn i = some k) (hr : cost P θ (M (other i) r) ≤ KK P) : c.IsMulti := by
  cases c with
  | abstain => simp [Choice.itemOn] at hk
  | multi k₀ k₁ => trivial
  | single j k' =>
    simp only [Choice.itemOn] at hk
    split_ifs at hk with hj
    cases hk; subst hj
    have hopt : IsOptimal P θ M (mk j k r) := by
      intro c'
      rw [utility_eq hS, utility_eq hS, uval_mk]
      have h1 := opt_le hS hc.1 c'
      have h2 : uval P θ M (.single j k) = P.v ^ 2 / 2 - cost P θ (M j k) := rfl
      linarith
    apply hc.2.1
    unfold mk at hopt
    split_ifs at hopt
    · exact ⟨_, _, hopt⟩
    · exact ⟨_, _, hopt⟩

lemma multi_of_cheap {θ : Ty} {M : Profile} {c : Choice} (hc : IsResponse P θ M c) {i k r : Fin 2}
    (hk : cost P θ (M i k) ≤ KK P) (hr : cost P θ (M (other i) r) ≤ KK P) : c.IsMulti := by
  have hK := KK_pos hS
  have hKV := KK_lt hS
  set k0 := argminSlot P θ (M i)
  set r0 := argminSlot P θ (M (other i))
  have hk0 := argminSlot_le P θ (M i)
  have hr0 := argminSlot_le P θ (M (other i))
  let m : Fin 2 → ℝ := fun x => if x = i then cost P θ (M i k0) else cost P θ (M (other i) r0)
  have hmi : m i = cost P θ (M i k0) := by simp [m]
  have hmo : m (other i) = cost P θ (M (other i) r0) := by simp [m, other_ne i]
  have hm : ∀ p k, m p ≤ cost P θ (M p k) := by
    intro p k
    rcases fin2_cases i p with h | h <;> rw [h]
    · rw [hmi]; exact hk0 k
    · rw [hmo]; exact hr0 k
  have h1 := hk0 k
  have h2 := hr0 r
  have hopt : IsOptimal P θ M (mk i k0 r0) := by
    refine opt_of_bounds' hS θ M _ i m hm ?_ ?_ ?_
    · rw [uval_mk]; linarith
    · intro p; rw [uval_mk]
      rcases fin2_cases i p with h | h <;> rw [h]
      · rw [hmi]; linarith
      · rw [hmo]; linarith
    · rw [uval_mk, hmi, hmo]
  apply hc.2.1
  unfold mk at hopt
  split_ifs at hopt
  · exact ⟨_, _, hopt⟩
  · exact ⟨_, _, hopt⟩

lemma dev_use (i : Fin 2) (M' : Menu) (θ : Ty) (c2 : Choice)
    (hc2 : IsResponse P θ (Function.update (fun _ => eqMenu P) i M') c2)
    (hkeep : ∀ k', c2.itemOn (other i) = some k' → k' = eqSlot θ) (k : Fin 2)
    (hk : c2.itemOn i = some k) : c2 = mk i k (eqSlot θ) ∧ cost P θ (M' k) ≤ KK P := by
  set M2 := Function.update (fun _ => eqMenu P) i M'
  have hM2i : M2 i = M' := by simp [M2]
  have hM2o : M2 (other i) = eqMenu P := by simp [M2, other_ne i]
  have hr : cost P θ (M2 (other i) (eqSlot θ)) ≤ KK P := by
    rw [hM2o, eqMenu_slot]; exact eqItem_cost_le hS θ
  have hm := multi_of_uses hS hc2 hk hr
  obtain ⟨o, r, hor⟩ := (isMulti_iff c2 i).1 hm
  rw [hor, itemOn_mk_self] at hk
  cases hk
  have hro : r = eqSlot θ := hkeep r (by rw [hor, itemOn_mk_other])
  subst hro
  refine ⟨hor, ?_⟩
  have := opt_multi_cost hS (hor ▸ hc2.1)
  rwa [hM2i] at this

lemma platRev_dev (i : Fin 2) (M' : Menu) (θ : Ty) (k : Fin 2) :
    platRev P (Function.update (fun _ => eqMenu P) i M') i (mk i k (eqSlot θ)) =
      (M' k).1 + (M' k).2 * (P.w - ((M' k).2 + (eqItem P θ).2)) := by
  rw [platRev_some P _ i _ k (itemOn_mk_self _ _ _), adsSeen_mk]
  simp [other_ne i, eqMenu_slot]

omit hS in
lemma cost_mono (M' : Menu) (hadm : M'.Admissible) (k : Fin 2) (hd : P.dL < P.dH) :
    cost P .L (M' k) ≤ cost P .H (M' k) := by
  simp only [cost, Params.d]; nlinarith [hadm k]

theorem platform_best_response' (i : Fin 2) :
    expRev P (fun _ => eqMenu P) i eqChoice =
      rho P * P.v ^ 2 / 2 + ((1 - P.r) * (P.w - P.dL) ^ 2 + P.r * alphaQ P ^ 2) / 9 ∧
    ∀ (M' : Menu), M'.Admissible → ∀ c' : Ty → Choice,
      (∀ θ, IsResponse P θ (Function.update (fun _ => eqMenu P) i M') (c' θ)) →
      (∀ θ k k', (eqChoice θ).itemOn (other i) = some k →
        (c' θ).itemOn (other i) = some k' → k' = k) →
      expRev P (Function.update (fun _ => eqMenu P) i M') i c' ≤
        rho P * P.v ^ 2 / 2 + ((1 - P.r) * (P.w - P.dL) ^ 2 + P.r * alphaQ P ^ 2) / 9 := by
  refine ⟨eq_revenue hS i, ?_⟩
  intro M' hadm c' hresp hkeep
  have hK := KK_pos hS
  have hd : P.dL < P.dH := hS.2.2.1
  have hr0 : 0 < P.r := hS.2.2.2.2.1
  have hr1 : P.r < 1 := hS.2.2.2.2.2.1
  have hkeep' : ∀ θ k', (c' θ).itemOn (other i) = some k' → k' = eqSlot θ :=
    fun θ k' h => hkeep θ (eqSlot θ) k' (eqChoice_itemOn θ (other i)) h
  set M2 := Function.update (fun _ => eqMenu P) i M'
  have hM2i : M2 i = M' := by simp [M2]
  have hM2o : M2 (other i) = eqMenu P := by simp [M2, other_ne i]
  have hKrho : rho P * P.v ^ 2 / 2 = KK P := rfl
  rw [hKrho]
  have hT : 0 ≤ ((1 - P.r) * (P.w - P.dL) ^ 2 + P.r * alphaQ P ^ 2) / 9 := by
    have : 0 ≤ 1 - P.r := by linarith
    positivity
  unfold expRev
  simp only [Params.prob]
  rcases hL : (c' .L).itemOn i with _ | kL <;> rcases hH : (c' .H).itemOn i with _ | kH
  · rw [platRev_none P _ i _ hL, platRev_none P _ i _ hH]; linarith
  · exfalso
    obtain ⟨-, hcH⟩ := dev_use hS i M' .H (c' .H) (hresp .H) (hkeep' .H) kH hH
    have h1 : cost P .L (M2 i kH) ≤ KK P := by
      rw [hM2i]; exact le_trans (cost_mono M' hadm kH hd) hcH
    have h2 : cost P .L (M2 (other i) 0) ≤ KK P := by
      rw [hM2o]; exact eqItem_cost_le hS .L
    have := multi_of_cheap hS (hresp .L) h1 h2
    obtain ⟨o, r, hor⟩ := (isMulti_iff _ i).1 this
    rw [hor, itemOn_mk_self] at hL; cases hL
  · obtain ⟨heL, hcL⟩ := dev_use hS i M' .L (c' .L) (hresp .L) (hkeep' .L) kL hL
    rw [platRev_none P _ i _ hH, heL, platRev_dev hS]
    have hb := screen_bound hS (M' kL).2 0 (M' kL).1 (KK P) (hadm kL) le_rfl (by simp)
      (by simp only [cost, Params.d] at hcL; linarith)
    simp only [eqItem] at hb ⊢
    nlinarith
  · obtain ⟨heL, hcL⟩ := dev_use hS i M' .L (c' .L) (hresp .L) (hkeep' .L) kL hL
    obtain ⟨heH, hcH⟩ := dev_use hS i M' .H (c' .H) (hresp .H) (hkeep' .H) kH hH
    have hIC : cost P .L (M2 i kL) ≤ cost P .L (M2 i kH) :=
      opt_min_cost hS (hresp .L).1 i kL hL kH
    rw [hM2i] at hIC
    rw [heL, heH, platRev_dev hS, platRev_dev hS]
    have hb := screen_bound hS (M' kL).2 (M' kH).2 (M' kL).1 (M' kH).1 (hadm kL) (hadm kH)
      (by simp only [cost, Params.d] at hcH; linarith)
      (by simp only [cost, Params.d] at hIC; linarith)
    simp only [eqItem]
    linarith

end exist

/-! ## uniqueness: the platform problem in equilibrium -/

noncomputable def Fq (P : Params) (A B x y : ℝ) : ℝ := (1 - P.r) * (x * (A - x)) + P.r * (y * (B - y))

lemma mk_of_slots (c : Choice) (hc : c.IsMulti) (k : Fin 2 → Fin 2)
    (hk : ∀ p, c.itemOn p = some (k p)) (i : Fin 2) : c = mk i (k i) (k (other i)) := by
  obtain ⟨o, r, hor⟩ := (isMulti_iff c i).1 hc
  have h1 := hk i; rw [hor, itemOn_mk_self] at h1
  have h2 := hk (other i); rw [hor, itemOn_mk_other] at h2
  rw [hor, Option.some.inj h1, Option.some.inj h2]

section uniq
variable {P : Params} (hS : P.Standing)
include hS

/-- The deviation used for the lower bound. -/
noncomputable def devMenu (P : Params) (x y : ℝ) : Menu :=
  ![(KK P - P.dL * x - (P.dH - P.dL) * y, x), (KK P - P.dH * y, y)]

lemma eq_lower {M : Profile} {c : Ty → Choice} (hE : IsEquilibrium P M c)
    (k : Ty → Fin 2 → Fin 2) (hk : ∀ θ p, (c θ).itemOn p = some (k θ p)) (i : Fin 2)
    (x y : ℝ) (hy : 0 ≤ y) (hxy : y ≤ x) :
    KK P + Fq P (P.w - P.dL - (M (other i) (k .L (other i))).2)
      (betaQ P - (M (other i) (k .H (other i))).2) x y ≤ expRev P M i c := by
  have hK := KK_pos hS
  have hKV := KK_lt hS
  have hrb := r_beta hS
  have hd : P.dL < P.dH := hS.2.2.1
  have hmL : ∀ θ, (c θ).IsMulti := lemma8' hS hE
  obtain ⟨hadm, hresp, hdev⟩ := hE
  have hM2i : Function.update M i (devMenu P x y) i = devMenu P x y := by simp
  have hM2o : Function.update M i (devMenu P x y) (other i) = M (other i) := by simp [other_ne i]
  have hadm' : (devMenu P x y).Admissible := by
    intro kk; fin_cases kk
    · show 0 ≤ x; linarith
    · show 0 ≤ y; exact hy
  -- rival costs
  have hcj : ∀ θ, cost P θ (M (other i) (k θ (other i))) ≤ KK P := by
    intro θ
    have h := mk_of_slots (c θ) (hmL θ) (k θ) (hk θ) (other i)
    have := opt_multi_cost hS (h ▸ (hresp θ).1)
    exact this
  have hcjmin : ∀ θ kk, cost P θ (M (other i) (k θ (other i))) ≤ cost P θ (M (other i) kk) :=
    fun θ kk => opt_min_cost hS (hresp θ).1 (other i) (k θ (other i)) (hk θ (other i)) kk
  -- costs of the deviation menu
  have c00 : cost P .L (devMenu P x y 0) = KK P - (P.dH - P.dL) * y := by
    simp [devMenu, cost, Params.d]; ring
  have c01 : cost P .L (devMenu P x y 1) = KK P - (P.dH - P.dL) * y := by
    simp [devMenu, cost, Params.d]; ring
  have c11 : cost P .H (devMenu P x y 1) = KK P := by
    simp [devMenu, cost, Params.d]
  have c10 : cost P .H (devMenu P x y 0) = KK P + (P.dH - P.dL) * (x - y) := by
    simp [devMenu, cost, Params.d]; ring
  have hown : ∀ θ kk, cost P θ (devMenu P x y (eqSlot θ)) ≤ cost P θ (devMenu P x y kk) := by
    intro θ kk
    cases θ <;> fin_cases kk <;> simp [eqSlot, c00, c01, c11, c10] <;> nlinarith
  have hownK : ∀ θ, cost P θ (devMenu P x y (eqSlot θ)) ≤ KK P := by
    intro θ; cases θ <;> simp [eqSlot, c00, c11] <;> nlinarith
  -- the response
  let c' : Ty → Choice := fun θ => mk i (eqSlot θ) (k θ (other i))
  have hresp' : ∀ θ, IsResponse P θ (Function.update M i (devMenu P x y)) (c' θ) := by
    intro θ
    let m : Fin 2 → ℝ := fun p => if p = i then cost P θ (devMenu P x y (eqSlot θ))
      else cost P θ (M (other i) (k θ (other i)))
    have hmi : m i = cost P θ (devMenu P x y (eqSlot θ)) := by simp [m]
    have hmo : m (other i) = cost P θ (M (other i) (k θ (other i))) := by simp [m, other_ne i]
    have hu : uval P θ (Function.update M i (devMenu P x y)) (c' θ) = P.v ^ 2 / 2 + KK P -
        cost P θ (devMenu P x y (eqSlot θ)) - cost P θ (M (other i) (k θ (other i))) := by
      simp only [c']; rw [uval_mk, hM2i, hM2o]
    have h1 := hcj θ
    have h2 := hownK θ
    refine resp_of_multi (opt_of_bounds' hS θ _ _ i m ?_ ?_ ?_ ?_) (mk_isMulti _ _ _)
    · intro p kk
      rcases fin2_cases i p with h | h <;> rw [h]
      · rw [hmi, hM2i]; exact hown θ kk
      · rw [hmo, hM2o]; exact hcjmin θ kk
    · rw [hu]; linarith
    · intro p; rw [hu]
      rcases fin2_cases i p with h | h <;> rw [h]
      · rw [hmi]; linarith
      · rw [hmo]; linarith
    · rw [hu, hmi, hmo]
  have hkeep' : ∀ θ kk kk', (c θ).itemOn (other i) = some kk → (c' θ).itemOn (other i) = some kk' →
      kk' = kk := by
    intro θ kk kk' h1 h2
    rw [hk θ (other i)] at h1
    have h3 : (c' θ).itemOn (other i) = some (k θ (other i)) := itemOn_mk_other _ _ _
    rw [h3] at h2
    rw [← Option.some.inj h1, ← Option.some.inj h2]
  have := hdev i (devMenu P x y) hadm' c' hresp' hkeep'
  refine le_trans (le_of_eq ?_) this
  unfold expRev
  simp only [Params.prob, c']
  rw [platRev_some P _ i _ _ (itemOn_mk_self _ _ _), platRev_some P _ i _ _ (itemOn_mk_self _ _ _),
    adsSeen_mk, adsSeen_mk, hM2i, hM2o]
  simp only [eqSlot, devMenu, Fq]
  simp
  linear_combination y * hrb

lemma eq_upper {M : Profile} {c : Ty → Choice} (hE : IsEquilibrium P M c)
    (k : Ty → Fin 2 → Fin 2) (hk : ∀ θ p, (c θ).itemOn p = some (k θ p)) (i : Fin 2) :
    0 ≤ (M i (k .H i)).2 ∧ (M i (k .H i)).2 ≤ (M i (k .L i)).2 ∧
    0 ≤ KK P - (P.dH * (M i (k .H i)).2 + (M i (k .H i)).1) ∧
    0 ≤ (P.dL * (M i (k .H i)).2 + (M i (k .H i)).1) - (P.dL * (M i (k .L i)).2 + (M i (k .L i)).1) ∧
    expRev P M i c = KK P + Fq P (P.w - P.dL - (M (other i) (k .L (other i))).2)
      (betaQ P - (M (other i) (k .H (other i))).2) (M i (k .L i)).2 (M i (k .H i)).2
      - (1 - P.r) * ((KK P - (P.dH * (M i (k .H i)).2 + (M i (k .H i)).1)) +
          ((P.dL * (M i (k .H i)).2 + (M i (k .H i)).1) - (P.dL * (M i (k .L i)).2 + (M i (k .L i)).1)))
      - P.r * (KK P - (P.dH * (M i (k .H i)).2 + (M i (k .H i)).1)) := by
  have hrb := r_beta hS
  have hd : P.dL < P.dH := hS.2.2.1
  have hmL : ∀ θ, (c θ).IsMulti := lemma8' hS hE
  obtain ⟨hadm, hresp, hdev⟩ := hE
  have hcL := mk_of_slots (c .L) (hmL .L) (k .L) (hk .L) i
  have hcH := mk_of_slots (c .H) (hmL .H) (k .H) (hk .H) i
  have hICL := opt_min_cost hS (hresp .L).1 i (k .L i) (hk .L i) (k .H i)
  have hICH := opt_min_cost hS (hresp .H).1 i (k .H i) (hk .H i) (k .L i)
  have hPH := opt_multi_cost hS (hcH ▸ (hresp .H).1)
  simp only [cost, Params.d] at hICL hICH hPH
  refine ⟨hadm i _, ?_, by linarith, by linarith, ?_⟩
  · have : (P.dH - P.dL) * (M i (k .H i)).2 ≤ (P.dH - P.dL) * (M i (k .L i)).2 := by linarith
    exact le_of_mul_le_mul_left this (by linarith)
  · unfold expRev
    rw [hcL, hcH, platRev_some P _ i _ _ (itemOn_mk_self _ _ _),
      platRev_some P _ i _ _ (itemOn_mk_self _ _ _), adsSeen_mk, adsSeen_mk]
    simp only [Params.prob, Fq]
    linear_combination (-(M i (k .H i)).2) * hrb

/-- first-order facts for maximizers of `Fq` on the cone `x ≥ y ≥ 0`. -/
lemma Fq_max_a (A B x y : ℝ) (hy : 0 ≤ y) (hxy : y ≤ x)
    (hmax : ∀ x' y', 0 ≤ y' → y' ≤ x' → Fq P A B x' y' ≤ Fq P A B x y) :
    x = y ∨ 2 * (x - y) ≤ A - B := by
  obtain ⟨-, -, -, -, hr, hr1, -, -⟩ := hS
  by_contra h
  push Not at h
  obtain ⟨hne, hlt⟩ := h
  have hpos : 0 < x - y := by
    rcases lt_or_eq_of_le hxy with h | h
    · linarith
    · exact absurd h.symm hne
  set t := min (x - y) ((2 * (x - y) - (A - B)) / 2) with ht
  have ht0 : 0 < t := lt_min hpos (by linarith)
  have ht1 : t ≤ x - y := min_le_left _ _
  have ht2 : t ≤ (2 * (x - y) - (A - B)) / 2 := min_le_right _ _
  have := hmax (x - P.r * t) (y + (1 - P.r) * t) (by nlinarith) (by nlinarith)
  have key : Fq P A B (x - P.r * t) (y + (1 - P.r) * t) - Fq P A B x y =
      P.r * (1 - P.r) * t * (2 * (x - y) - (A - B) - t) := by
    unfold Fq; ring
  have : 0 < P.r * (1 - P.r) * t * (2 * (x - y) - (A - B) - t) := by
    have h1 : 0 < P.r * (1 - P.r) := mul_pos hr (by linarith)
    have h2 : 0 < 2 * (x - y) - (A - B) - t := by linarith
    positivity
  linarith

lemma Fq_max_b (A B x y : ℝ) (hy : 0 ≤ y) (hxy : y ≤ x) (hBA : B ≤ A)
    (hmax : ∀ x' y', 0 ≤ y' → y' ≤ x' → Fq P A B x' y' ≤ Fq P A B x y) :
    x = max A 0 / 2 ∧ y = max B 0 / 2 := by
  obtain ⟨-, -, -, -, hr, hr1, -, -⟩ := hS
  have hx : 0 ≤ x := le_trans hy hxy
  have h1 := hmax (max A 0 / 2) (max B 0 / 2) (by positivity)
    (by have := max_le_max hBA (le_refl (0:ℝ)); linarith)
  have g : ∀ (C z : ℝ), 0 ≤ z → z * (C - z) + (z - max C 0 / 2) ^ 2 ≤
      max C 0 / 2 * (C - max C 0 / 2) := by
    intro C z hz
    rcases le_total 0 C with hC | hC
    · rw [max_eq_left hC]; nlinarith
    · rw [max_eq_right hC]; nlinarith
  have gA := g A x hx
  have gB := g B y hy
  unfold Fq at h1
  have hsq1 : (1 - P.r) * (x - max A 0 / 2) ^ 2 ≤ 0 := by nlinarith
  have hsq2 : P.r * (y - max B 0 / 2) ^ 2 ≤ 0 := by nlinarith
  have e1 : (x - max A 0 / 2) ^ 2 = 0 := by
    have : 0 < 1 - P.r := by linarith
    nlinarith [sq_nonneg (x - max A 0 / 2)]
  have e2 : (y - max B 0 / 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (y - max B 0 / 2)]
  constructor
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 e1; linarith
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 e2; linarith

lemma eq_platform {M : Profile} {c : Ty → Choice} (hE : IsEquilibrium P M c)
    (k : Ty → Fin 2 → Fin 2) (hk : ∀ θ p, (c θ).itemOn p = some (k θ p)) (i : Fin 2) :
    0 ≤ (M i (k .H i)).2 ∧ (M i (k .H i)).2 ≤ (M i (k .L i)).2 ∧
    (M i (k .H i)).1 = KK P - P.dH * (M i (k .H i)).2 ∧
    (M i (k .L i)).1 = P.dL * (M i (k .H i)).2 + (M i (k .H i)).1 - P.dL * (M i (k .L i)).2 ∧
    (∀ x' y', 0 ≤ y' → y' ≤ x' →
      Fq P (P.w - P.dL - (M (other i) (k .L (other i))).2) (betaQ P - (M (other i) (k .H (other i))).2) x' y' ≤
      Fq P (P.w - P.dL - (M (other i) (k .L (other i))).2) (betaQ P - (M (other i) (k .H (other i))).2)
        (M i (k .L i)).2 (M i (k .H i)).2) ∧
    expRev P M i c = KK P + Fq P (P.w - P.dL - (M (other i) (k .L (other i))).2)
      (betaQ P - (M (other i) (k .H (other i))).2) (M i (k .L i)).2 (M i (k .H i)).2 := by
  obtain ⟨hy, hxy, heH, heL, hR⟩ := eq_upper hS hE k hk i
  have hlow := eq_lower hS hE k hk i _ _ hy hxy
  have hr : 0 < P.r := hS.2.2.2.2.1
  have hr1 : P.r < 1 := hS.2.2.2.2.2.1
  have hslack : (1 - P.r) * ((KK P - (P.dH * (M i (k .H i)).2 + (M i (k .H i)).1)) +
          ((P.dL * (M i (k .H i)).2 + (M i (k .H i)).1) - (P.dL * (M i (k .L i)).2 + (M i (k .L i)).1)))
      + P.r * (KK P - (P.dH * (M i (k .H i)).2 + (M i (k .H i)).1)) ≤ 0 := by linarith
  have h1 : 0 ≤ (1 - P.r) * ((KK P - (P.dH * (M i (k .H i)).2 + (M i (k .H i)).1)) +
          ((P.dL * (M i (k .H i)).2 + (M i (k .H i)).1) - (P.dL * (M i (k .L i)).2 + (M i (k .L i)).1))) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ P.r * (KK P - (P.dH * (M i (k .H i)).2 + (M i (k .H i)).1)) := mul_nonneg hr.le heH
  have eH0 : KK P - (P.dH * (M i (k .H i)).2 + (M i (k .H i)).1) = 0 := by
    have : P.r * (KK P - (P.dH * (M i (k .H i)).2 + (M i (k .H i)).1)) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  have eL0 : (P.dL * (M i (k .H i)).2 + (M i (k .H i)).1) - (P.dL * (M i (k .L i)).2 + (M i (k .L i)).1) = 0 := by
    have : (1 - P.r) * ((KK P - (P.dH * (M i (k .H i)).2 + (M i (k .H i)).1)) +
          ((P.dL * (M i (k .H i)).2 + (M i (k .H i)).1) - (P.dL * (M i (k .L i)).2 + (M i (k .L i)).1))) = 0 := by
      linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  refine ⟨hy, hxy, by linarith, by linarith, ?_, ?_⟩
  · intro x' y' hy' hxy'
    have := eq_lower hS hE k hk i x' y' hy' hxy'
    rw [eH0, eL0] at hR
    linarith
  · rw [hR, eH0, eL0]; ring

lemma fixed_x (c0 x0 x1 : ℝ) (hc : 0 < c0) (h0 : 0 ≤ x0) (h1 : 0 ≤ x1)
    (e0 : x0 = max (c0 - x1) 0 / 2) (e1 : x1 = max (c0 - x0) 0 / 2) :
    x0 = c0 / 3 ∧ x1 = c0 / 3 := by
  have b0 : x0 ≤ c0 / 2 := by rw [e0]; have := max_le (by linarith : c0 - x1 ≤ c0) hc.le; linarith
  have b1 : x1 ≤ c0 / 2 := by rw [e1]; have := max_le (by linarith : c0 - x0 ≤ c0) hc.le; linarith
  rw [max_eq_left (by linarith)] at e0 e1
  constructor <;> linarith

omit hS in
lemma fixed_y (b y0 y1 : ℝ) (h0 : 0 ≤ y0) (h1 : 0 ≤ y1)
    (e0 : y0 = max (b - y1) 0 / 2) (e1 : y1 = max (b - y0) 0 / 2) :
    y0 = max b 0 / 3 ∧ y1 = max b 0 / 3 := by
  rcases le_total 0 b with hb | hb
  · rw [max_eq_left hb]
    have b0 : y0 ≤ b / 2 := by rw [e0]; have := max_le (by linarith : b - y1 ≤ b) hb; linarith
    have b1 : y1 ≤ b / 2 := by rw [e1]; have := max_le (by linarith : b - y0 ≤ b) hb; linarith
    rw [max_eq_left (by linarith)] at e0 e1
    constructor <;> linarith
  · rw [max_eq_right hb]
    rw [max_eq_right (by linarith)] at e0 e1
    constructor <;> linarith

lemma eq_unique {M : Profile} {c : Ty → Choice} (hE : IsEquilibrium P M c)
    (k : Ty → Fin 2 → Fin 2) (hk : ∀ θ p, (c θ).itemOn p = some (k θ p)) (i : Fin 2) :
    M i (k .L i) = eqItem P .L ∧ M i (k .H i) = eqItem P .H ∧
    expRev P M i c = rho P * P.v ^ 2 / 2 + ((1 - P.r) * (P.w - P.dL) ^ 2 + P.r * alphaQ P ^ 2) / 9 := by
  have hbl := beta_lt hS
  have hw : P.dL < P.w := hS.2.2.2.1
  obtain ⟨hy0, hxy0, hsH0, hsL0, hmax0, hR0⟩ := eq_platform hS hE k hk 0
  obtain ⟨hy1, hxy1, hsH1, hsL1, hmax1, hR1⟩ := eq_platform hS hE k hk 1
  have o0 : other 0 = 1 := rfl
  have o1 : other 1 = 0 := rfl
  rw [o0] at hmax0 hR0
  rw [o1] at hmax1 hR1
  set x0 := (M 0 (k .L 0)).2
  set x1 := (M 1 (k .L 1)).2
  set y0 := (M 0 (k .H 0)).2
  set y1 := (M 1 (k .H 1)).2
  set D := P.w - P.dL - betaQ P
  have hD : 0 < D := by simp only [D]; linarith
  have a0 := Fq_max_a hS _ _ _ _ hy0 hxy0 hmax0
  have a1 := Fq_max_a hS _ _ _ _ hy1 hxy1 hmax1
  have d0 : x0 - y0 ≤ D / 2 := by
    rcases a0 with h | h
    · rw [h]; linarith
    · linarith
  have d1 : x1 - y1 ≤ D / 2 := by
    rcases a1 with h | h
    · rw [h]; linarith
    · linarith
  obtain ⟨ex0, ey0⟩ := Fq_max_b hS _ _ _ _ hy0 hxy0 (by linarith) hmax0
  obtain ⟨ex1, ey1⟩ := Fq_max_b hS _ _ _ _ hy1 hxy1 (by linarith) hmax1
  obtain ⟨fx0, fx1⟩ := fixed_x hS (P.w - P.dL) x0 x1 (by linarith) (by linarith) (by linarith)
    ex0 ex1
  obtain ⟨fy0, fy1⟩ := fixed_y (betaQ P) y0 y1 hy0 hy1
    ey0 ey1
  have hα : max (betaQ P) 0 = alphaQ P := rfl
  rw [hα] at fy0 fy1
  have hrev : ∀ xa ya xb yb : ℝ, xa = (P.w - P.dL) / 3 → ya = alphaQ P / 3 →
      xb = (P.w - P.dL) / 3 → yb = alphaQ P / 3 →
      KK P + Fq P (P.w - P.dL - xb) (betaQ P - yb) xa ya =
      rho P * P.v ^ 2 / 2 + ((1 - P.r) * (P.w - P.dL) ^ 2 + P.r * alphaQ P ^ 2) / 9 := by
    intro xa ya xb yb hx hy hx' hy'
    rw [hx, hy, hx', hy']; unfold Fq KK
    rcases alpha_cases (P := P) with ⟨ha, -⟩ | ⟨ha, -⟩
    · rw [ha]; ring
    · rw [ha]; ring
  have hitems : ∀ (sL sH xa ya : ℝ), sH = KK P - P.dH * ya → sL = P.dL * ya + sH - P.dL * xa →
      xa = (P.w - P.dL) / 3 → ya = alphaQ P / 3 →
      ((sL, xa) : Item) = eqItem P .L ∧ ((sH, ya) : Item) = eqItem P .H := by
    intro sL sH xa ya h1 h2 h3 h4
    rw [h2, h1, h3, h4]
    constructor
    · simp only [eqItem, KK]; ext <;> simp; ring
    · simp only [eqItem, KK]
  fin_cases i
  · obtain ⟨hL, hH⟩ := hitems _ _ _ _ hsH0 hsL0 fx0 fy0
    refine ⟨?_, ?_, ?_⟩
    · exact (Prod.ext rfl rfl : M 0 (k .L 0) = ((M 0 (k .L 0)).1, x0)).trans hL
    · exact (Prod.ext rfl rfl : M 0 (k .H 0) = ((M 0 (k .H 0)).1, y0)).trans hH
    · show expRev P M 0 c = _
      rw [hR0]; exact hrev _ _ _ _ fx0 fy0 fx1 fy1
  · obtain ⟨hL, hH⟩ := hitems _ _ _ _ hsH1 hsL1 fx1 fy1
    refine ⟨?_, ?_, ?_⟩
    · exact (Prod.ext rfl rfl : M 1 (k .L 1) = ((M 1 (k .L 1)).1, x1)).trans hL
    · exact (Prod.ext rfl rfl : M 1 (k .H 1) = ((M 1 (k .H 1)).1, y1)).trans hH
    · show expRev P M 1 c = _
      rw [hR1]; exact hrev _ _ _ _ fx1 fy1 fx0 fy0

omit hS in
lemma fin2_two (a b x : Fin 2) (h : a ≠ b) : x = a ∨ x = b := by
  fin_cases a <;> fin_cases b <;> fin_cases x <;> simp_all

lemma slots_of_eq {M : Profile} {c : Ty → Choice} (hE : IsEquilibrium P M c) :
    ∃ k : Ty → Fin 2 → Fin 2, ∀ θ p, (c θ).itemOn p = some (k θ p) := by
  have hm := lemma8' hS hE
  have : ∀ θ p, ∃ kk, (c θ).itemOn p = some kk := by
    intro θ p
    have := hm θ
    rcases h : c θ with _ | ⟨_, _⟩ | ⟨k0, k1⟩
    · rw [h] at this; exact this.elim
    · rw [h] at this; exact this.elim
    · exact ⟨_, rfl⟩
  choose k hk using this
  exact ⟨k, hk⟩

theorem eq_exists : IsEquilibrium P (fun _ => eqMenu P) eqChoice := by
  have ha0 := alpha_nonneg (P := P)
  have hw : P.dL < P.w := hS.2.2.2.1
  refine ⟨?_, consumer_choices' hS, ?_⟩
  · intro i kk; fin_cases kk
    · show 0 ≤ (P.w - P.dL) / 3; linarith
    · show 0 ≤ alphaQ P / 3; linarith
  · intro i M' hadm c' hresp hkeep
    rw [(platform_best_response' hS i).1]
    exact (platform_best_response' hS i).2 M' hadm c' hresp hkeep

lemma eqItem_ne : eqItem P .L ≠ eqItem P .H := by
  intro h
  have h2 := congrArg Prod.snd h
  simp only [eqItem] at h2
  have := alpha_lt hS
  linarith

theorem proposition_3' :
    IsEquilibrium P (fun _ => eqMenu P) eqChoice ∧
    eqItem P .L ≠ eqItem P .H ∧
    (∀ (M : Profile) (c : Ty → Choice), IsEquilibrium P M c →
      (∀ i, Set.range (M i) = {eqItem P .L, eqItem P .H}) ∧
      ∀ θ, ∃ k₀ k₁, c θ = .multi k₀ k₁ ∧ M 0 k₀ = eqItem P θ ∧ M 1 k₁ = eqItem P θ) ∧
    (∀ (M : Profile) (c : Ty → Choice), IsEquilibrium P M c → ∀ i,
      expRev P M i c =
        rho P * P.v ^ 2 / 2 + ((1 - P.r) * (P.w - P.dL) ^ 2 + P.r * alphaQ P ^ 2) / 9) := by
  refine ⟨eq_exists hS, eqItem_ne hS, ?_, ?_⟩
  · intro M c hE
    obtain ⟨k, hk⟩ := slots_of_eq hS hE
    have hu := eq_unique hS hE k hk
    refine ⟨?_, ?_⟩
    · intro i
      obtain ⟨hL, hH, -⟩ := hu i
      have hne : k .L i ≠ k .H i := by
        intro h; apply eqItem_ne hS; rw [← hL, ← hH, h]
      ext z
      constructor
      · rintro ⟨kk, rfl⟩
        rcases fin2_two _ _ kk hne with h | h
        · rw [h, hL]; simp
        · rw [h, hH]; simp
      · intro hz
        rcases hz with hz | hz
        · exact ⟨k .L i, by rw [hL, hz]⟩
        · rw [Set.mem_singleton_iff] at hz; exact ⟨k .H i, by rw [hH, hz]⟩
    · intro θ
      refine ⟨k θ 0, k θ 1, ?_, ?_, ?_⟩
      · have := mk_of_slots (c θ) (lemma8' hS hE θ) (k θ) (hk θ) 0
        rw [this]; rfl
      · cases θ
        · exact (hu 0).1
        · exact (hu 0).2.1
      · cases θ
        · exact (hu 1).1
        · exact (hu 1).2.1
  · intro M c hE i
    obtain ⟨k, hk⟩ := slots_of_eq hS hE
    exact (eq_unique hS hE k hk i).2.2

end uniq

end MediaMenus.Duopoly

open MediaMenus.Duopoly

theorem solution (P : Params) (hS : P.Standing) :
    IsEquilibrium P (fun _ => eqMenu P) eqChoice ∧
    eqItem P .L ≠ eqItem P .H ∧
    (∀ (M : Profile) (c : Ty → Choice), IsEquilibrium P M c →
      (∀ i, Set.range (M i) = {eqItem P .L, eqItem P .H}) ∧
      ∀ θ, ∃ k₀ k₁, c θ = .multi k₀ k₁ ∧ M 0 k₀ = eqItem P θ ∧ M 1 k₁ = eqItem P θ) ∧
    (∀ (M : Profile) (c : Ty → Choice), IsEquilibrium P M c → ∀ i,
      expRev P M i c =
        rho P * P.v ^ 2 / 2 + ((1 - P.r) * (P.w - P.dL) ^ 2 + P.r * alphaQ P ^ 2) / 9) :=
  proposition_3' hS

