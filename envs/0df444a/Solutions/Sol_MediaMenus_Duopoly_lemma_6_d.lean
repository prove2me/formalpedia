-- Prove2me | solution 1 for MediaMenus.Duopoly.lemma_6_d
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T16:09:16.858142+00:00
-- url     : https://prove2.me/submissions/f169ec88-e591-4f8a-b493-287ef42a624a

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

end MediaMenus.Duopoly

open MediaMenus.Duopoly

theorem solution (P : Params) (hS : P.Standing) (M : Profile) (θ : Ty) (i k : Fin 2)
    (hopt : IsOptimal P θ M (.single i k)) :
    ∀ k' : Fin 2, (1 - P.γ) * P.v ^ 2 / (2 * (1 + P.γ)) ≤ cost P θ (M (other i) k') := by
  intro k'
  rw [← KK_eq' hS]
  have := opt_le hS hopt (mk i k k')
  rw [uval_mk] at this
  have h2 : uval P θ M (.single i k) = P.v ^ 2 / 2 - cost P θ (M i k) := rfl
  linarith
