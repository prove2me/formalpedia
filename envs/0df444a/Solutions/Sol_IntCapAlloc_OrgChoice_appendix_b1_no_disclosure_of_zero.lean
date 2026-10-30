-- Prove2me | solution 1 for IntCapAlloc.OrgChoice.appendix_b1_no_disclosure_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T16:35:24.014754+00:00
-- url     : https://prove2.me/submissions/f6abf5c9-6abe-4f76-8616-02c66434b49b

import Mathlib
import Definitions.Def_IntCapAlloc_OrgChoice_Model

open IntCapAlloc.OrgChoice

namespace ICA

def T (a b : Bool) : Fin 2 → Bool := fun i => if i = 0 then a else b
def M (a b : Option Bool) : Msg := fun i => if i = 0 then a else b

@[simp] lemma T_0 (a b : Bool) : T a b 0 = a := rfl
@[simp] lemma T_1 (a b : Bool) : T a b 1 = b := rfl
@[simp] lemma M_0 (a b : Option Bool) : M a b 0 = a := rfl
@[simp] lemma M_1 (a b : Option Bool) : M a b 1 = b := rfl

lemma T_eta (t : Fin 2 → Bool) : t = T (t 0) (t 1) := by
  funext i; fin_cases i <;> rfl

lemma M_eta (m : Msg) : m = M (m 0) (m 1) := by
  funext i; fin_cases i <;> rfl

@[simp] lemma T_inj (a b a' b' : Bool) : T a b = T a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h; exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] lemma M_inj (a b a' b' : Option Bool) : M a b = M a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h; exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩; rfl

def eqv : (Bool × Bool) ≃ Profile where
  toFun x := T x.1 x.2
  invFun t := (t 0, t 1)
  left_inv _ := rfl
  right_inv t := (T_eta t).symm

lemma sum4 (f : Profile → ℝ) : ∑ t, f t =
    f (T true true) + f (T true false) + f (T false true) + f (T false false) := by
  rw [← Equiv.sum_comp eqv f, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, add_assoc]
  rfl

def o (d a : Bool) : Option Bool := if d then some a else none
@[simp] lemma o_t (a : Bool) : o true a = some a := rfl
@[simp] lemma o_f (a : Bool) : o false a = none := rfl

@[simp] lemma msg_T (a b d1 d2 : Bool) : msg (T a b) (T d1 d2) = M (o d1 a) (o d2 b) := by
  funext i; fin_cases i <;> simp [msg, M, T, o]

@[simp] lemma nD_M (a b : Option Bool) :
    (nD (M a b) : ℝ) = (if a.isSome then 1 else 0) + (if b.isSome then 1 else 0) := by
  simp only [nD, Finset.card_filter, Fin.sum_univ_two]
  cases a <;> cases b <;> simp [M] <;> norm_num

@[simp] lemma prior_T (p : ℝ) (a b : Bool) :
    prior p (T a b) = (if a then p else 1 - p) * (if b then p else 1 - p) := by
  cases a <;> cases b <;> simp [prior, Fin.prod_univ_two]

@[simp] lemma th_t : th true = 1 := rfl
@[simp] lemma th_f : th false = 0 := rfl

@[simp] lemma impl_T (a b : Bool) : implemented (T a b) = max (th a) (th b) := rfl
@[simp] lemma max10 : max (1:ℝ) 0 = 1 := by norm_num
@[simp] lemma max01 : max (0:ℝ) 1 = 1 := by norm_num
@[simp] lemma max00 : max (0:ℝ) 0 = 0 := by norm_num
@[simp] lemma max11 : max (1:ℝ) 1 = 1 := by norm_num

lemma E2_eq (μ : Belief) (m : Msg) : E2 μ m =
    2 * μ m (T true true) + μ m (T true false) + μ m (T false true) := by
  simp only [E2, sum4]; simp [th]; ring

lemma E1_eq (μ : Belief) (m : Msg) : E1 μ m =
    μ m (T true true) + μ m (T true false) + μ m (T false true) := by
  simp only [E1, sum4]; simp [th]

lemma cons_iff (a b : Option Bool) (x y : Bool) :
    Consistent (M a b) (T x y) ↔ (∀ v, a = some v → x = v) ∧ (∀ v, b = some v → y = v) := by
  constructor
  · intro h; exact ⟨fun v hv => h 0 v hv, fun v hv => h 1 v hv⟩
  · rintro ⟨h0, h1⟩ i v hv; fin_cases i
    · exact h0 v hv
    · exact h1 v hv

/-- An admissible belief vanishes on inconsistent types. -/
lemma adm_zero {μ : Belief} (hμ : Admissible μ) (a b : Option Bool) (x y : Bool)
    (h : ¬ Consistent (M a b) (T x y)) : μ (M a b) (T x y) = 0 := by
  by_contra hne; exact h ((hμ _).2.2 _ hne)

lemma adm_sum {μ : Belief} (hμ : Admissible μ) (m : Msg) :
    μ m (T true true) + μ m (T true false) + μ m (T false true) + μ m (T false false) = 1 := by
  rw [← sum4]; exact (hμ m).2.1

lemma adm_nn {μ : Belief} (hμ : Admissible μ) (m : Msg) (t : Profile) : 0 ≤ μ m t := (hμ m).1 t


lemma exIcc_iff (E X R : ℝ) (hE : 0 ≤ E) (hX : 0 < X) (hR : 0 < R) :
    (∃ α ∈ Set.Icc (0 : ℝ) 1, E * α * X = R) ↔ R ≤ E * X := by
  constructor
  · rintro ⟨α, ⟨h0, h1⟩, h⟩
    rw [← h]
    have : E * α * X = (E * X) * α := by ring
    rw [this]
    have : 0 ≤ E * X := mul_nonneg hE hX.le
    nlinarith
  · intro h
    have hEX : 0 < E * X := lt_of_lt_of_le hR h
    have hE0 : E ≠ 0 := by rintro rfl; simp at hEX
    refine ⟨R / (E * X), ⟨div_nonneg hR.le hEX.le, (div_le_one hEX).mpr h⟩, ?_⟩
    field_simp

lemma E2_nn {μ : Belief} (hμ : Admissible μ) (m : Msg) : 0 ≤ E2 μ m := by
  rw [E2_eq]; have := adm_nn hμ m (T true true); have := adm_nn hμ m (T true false)
  have := adm_nn hμ m (T false true); linarith

lemma E1_nn {μ : Belief} (hμ : Admissible μ) (m : Msg) : 0 ≤ E1 μ m := by
  rw [E1_eq]; have := adm_nn hμ m (T true true); have := adm_nn hμ m (T true false)
  have := adm_nn hμ m (T false true); linarith

lemma nD_nn (m : Msg) : (0 : ℝ) ≤ nD m := Nat.cast_nonneg _

/-- Investors' choice in closed form. -/
noncomputable def K (X c e2 e1 n : ℝ) : ℕ :=
  if 2 + c * n ≤ e2 * X then 2 else if 1 + c * n ≤ e1 * X then 1 else 0

/-- The manager's payoff in closed form: `s` = θ₁+θ₂, `mx` = implemented θ. -/
noncomputable def Pay (X c q bet s mx e2 e1 n : ℝ) : ℝ :=
  if 2 + c * n ≤ e2 * X then q * s * (X - (2 + c * n) / e2) + 2 * bet
  else if 1 + c * n ≤ e1 * X then q * mx * (X - (1 + c * n) / e1) + bet else 0

lemma invest_eq {X c : ℝ} {μ : Belief} (hμ : Admissible μ) (hX : 0 < X) (hc : 0 ≤ c) (m : Msg) :
    invest X c μ m = K X c (E2 μ m) (E1 μ m) (nD m) := by
  have hn := nD_nn m
  unfold invest K
  rw [exIcc_iff _ _ _ (E2_nn hμ m) hX (by positivity),
    exIcc_iff _ _ _ (E1_nn hμ m) hX (by positivity)]

lemma Kpos {e X A : ℝ} (hX : 0 < X) (hA : 0 < A) (h : A ≤ e * X) : 0 < e := by
  by_contra hh; push Not at hh
  have : e * X ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hh hX.le
  linarith

lemma mgr_eq {X c q bet : ℝ} {μ : Belief} (hμ : Admissible μ) (hX : 0 < X) (hc : 0 ≤ c)
    (t : Profile) (m : Msg) :
    mgrPayoff X c q bet μ t m =
      Pay X c q bet (th (t 0) + th (t 1)) (implemented t) (E2 μ m) (E1 μ m) (nD m) := by
  have hn := nD_nn m
  have hi := invest_eq hμ hX hc m
  have hp2 : 0 < 2 + c * nD m := by positivity
  have hp1 : 0 < 1 + c * nD m := by positivity
  unfold Pay
  by_cases k2 : 2 + c * nD m ≤ E2 μ m * X
  · have hk : invest X c μ m = 2 := by rw [hi]; simp [K, k2]
    have he := Kpos hX hp2 k2
    simp only [mgrPayoff, share, hk, if_true, k2]
    field_simp
  by_cases k1 : 1 + c * nD m ≤ E1 μ m * X
  · have hk : invest X c μ m = 1 := by rw [hi]; simp [K, k2, k1]
    have he := Kpos hX hp1 k1
    simp only [mgrPayoff, share, hk, k2, k1, if_true, if_false, show (1:ℕ) ≠ 2 from by decide]
    field_simp
  · have hk : invest X c μ m = 0 := by rw [hi]; simp [K, k2, k1]
    simp [mgrPayoff, hk, k2, k1]

section PayLemmas
variable {X c q bet s mx e2 e1 n : ℝ}

lemma Pay2 (h : 2 + c * n ≤ e2 * X) :
    Pay X c q bet s mx e2 e1 n = q * s * (X - (2 + c * n) / e2) + 2 * bet := by
  simp [Pay, h]

lemma Pay1 (h : ¬ 2 + c * n ≤ e2 * X) (h1 : 1 + c * n ≤ e1 * X) :
    Pay X c q bet s mx e2 e1 n = q * mx * (X - (1 + c * n) / e1) + bet := by
  simp [Pay, h, h1]

lemma Pay0 (h : ¬ 2 + c * n ≤ e2 * X) (h1 : ¬ 1 + c * n ≤ e1 * X) :
    Pay X c q bet s mx e2 e1 n = 0 := by
  simp [Pay, h, h1]

lemma K2 (h : 2 + c * n ≤ e2 * X) : K X c e2 e1 n = 2 := by simp [K, h]
lemma K1 (h : ¬ 2 + c * n ≤ e2 * X) (h1 : 1 + c * n ≤ e1 * X) : K X c e2 e1 n = 1 := by
  simp [K, h, h1]
lemma K0 (h : ¬ 2 + c * n ≤ e2 * X) (h1 : ¬ 1 + c * n ≤ e1 * X) : K X c e2 e1 n = 0 := by
  simp [K, h, h1]

variable (hX : 0 < X) (hq : 0 < q) (hb : q * X < bet) (hc : 0 ≤ c) (hn : 0 ≤ n)
include hX hq hb hc hn

lemma frac_le_X {A e : ℝ} (hA : 0 < A) (h : A ≤ e * X) : A / e ≤ X ∧ 0 < e ∧ 0 ≤ A / e := by
  have he : 0 < e := by
    by_contra hh; push Not at hh
    have : e * X ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hh hX.le
    linarith
  refine ⟨?_, he, by positivity⟩
  rw [div_le_iff₀ he]; linarith

lemma Pay_ge2 (hs : 0 ≤ s) (h : 2 + c * n ≤ e2 * X) : 2 * bet ≤ Pay X c q bet s mx e2 e1 n := by
  rw [Pay2 h]
  obtain ⟨h1, -, -⟩ := frac_le_X hX hq hb hc hn (by positivity) h
  have : 0 ≤ q * s * (X - (2 + c * n) / e2) := by
    apply mul_nonneg (mul_nonneg hq.le hs); linarith
  linarith

lemma Pay_ge1 (hs : 0 ≤ s) (hm : 0 ≤ mx) (h : 1 + c * n ≤ e1 * X) :
    bet ≤ Pay X c q bet s mx e2 e1 n := by
  have hbet : 0 < bet := by nlinarith
  by_cases h2 : 2 + c * n ≤ e2 * X
  · have := Pay_ge2 hX hq hb hc hn (mx := mx) (e1 := e1) hs h2; linarith
  rw [Pay1 h2 h]
  obtain ⟨h1, -, -⟩ := frac_le_X hX hq hb hc hn (by positivity) h
  have : 0 ≤ q * mx * (X - (1 + c * n) / e1) := by
    apply mul_nonneg (mul_nonneg hq.le hm); linarith
  linarith

lemma Pay_nonneg (hs : 0 ≤ s) (hm : 0 ≤ mx) : 0 ≤ Pay X c q bet s mx e2 e1 n := by
  have hbet : 0 < bet := by nlinarith
  by_cases h1 : 1 + c * n ≤ e1 * X
  · have := Pay_ge1 hX hq hb hc hn (s := s) (e2 := e2) hs hm h1; linarith
  by_cases h2 : 2 + c * n ≤ e2 * X
  · have := Pay_ge2 hX hq hb hc hn (mx := mx) (e1 := e1) hs h2; linarith
  rw [Pay0 h2 h1]

lemma Pay_lt2 (hm : 0 ≤ mx) (hm1 : mx ≤ 1) (h : ¬ 2 + c * n ≤ e2 * X) :
    Pay X c q bet s mx e2 e1 n < 2 * bet := by
  have hbet : 0 < bet := by nlinarith
  by_cases h1 : 1 + c * n ≤ e1 * X
  · rw [Pay1 h h1]
    obtain ⟨_, he, hfr⟩ := frac_le_X hX hq hb hc hn (by positivity) h1
    have : q * mx * (X - (1 + c * n) / e1) ≤ q * X := by
      have : q * mx * (X - (1 + c * n) / e1) ≤ q * mx * X := by
        have : 0 ≤ q * mx := mul_nonneg hq.le hm
        nlinarith
      have : q * mx * X ≤ q * X := by
        have : 0 ≤ q * X := by positivity
        nlinarith
      linarith
    linarith
  · rw [Pay0 h h1]; linarith

lemma Pay_lt1 (hm : 0 ≤ mx) (hm1 : mx ≤ 1) (h : ¬ 2 + c * n ≤ e2 * X)
    (h1 : 1 + c * n ≤ e1 * X) : Pay X c q bet s mx e2 e1 n ≤ q * X + bet := by
  rw [Pay1 h h1]
  obtain ⟨_, he, hfr⟩ := frac_le_X hX hq hb hc hn (by positivity) h1
  have : q * mx * (X - (1 + c * n) / e1) ≤ q * mx * X := by
    have : 0 ≤ q * mx := mul_nonneg hq.le hm
    nlinarith
  have : q * mx * X ≤ q * X := by
    have : 0 ≤ q * X := by positivity
    nlinarith
  linarith

lemma div_anti {A A' e e' : ℝ} (hA' : 0 ≤ A') (hAA : A' ≤ A) (he : 0 < e) (hee : e ≤ e') :
    A' / e' ≤ A / e := by
  have he' : 0 < e' := lt_of_lt_of_le he hee
  rw [div_le_div_iff₀ he' he]
  nlinarith

omit hX hq hb hc hn in
lemma Pay_mono_aux : True := trivial

lemma Pay_mono {e2' e1' n' : ℝ} (hn' : 0 ≤ n') (hs : 0 ≤ s) (hm : 0 ≤ mx) (hm1 : mx ≤ 1)
    (h2 : e2 ≤ e2') (h1 : e1 ≤ e1') (hnn : n' ≤ n) :
    Pay X c q bet s mx e2 e1 n ≤ Pay X c q bet s mx e2' e1' n' := by
  have hcn : c * n' ≤ c * n := mul_le_mul_of_nonneg_left hnn hc
  by_cases k2 : 2 + c * n ≤ e2 * X
  · have k2' : 2 + c * n' ≤ e2' * X := by nlinarith
    rw [Pay2 k2, Pay2 k2']
    obtain ⟨_, he, _⟩ := frac_le_X hX hq hb hc hn (by positivity) k2
    have := div_anti hX hq hb hc hn (by positivity) (by linarith : 2 + c * n' ≤ 2 + c * n) he h2
    have : 0 ≤ q * s := mul_nonneg hq.le hs
    nlinarith
  by_cases k1 : 1 + c * n ≤ e1 * X
  · have k1' : 1 + c * n' ≤ e1' * X := by nlinarith
    by_cases k2' : 2 + c * n' ≤ e2' * X
    · have := Pay_lt1 hX hq hb hc hn (s := s) (e2 := e2) hm hm1 k2 k1
      have := Pay_ge2 hX hq hb hc hn' (mx := mx) (e1 := e1') hs k2'
      linarith
    rw [Pay1 k2 k1, Pay1 k2' k1']
    obtain ⟨_, he, _⟩ := frac_le_X hX hq hb hc hn (by positivity) k1
    have := div_anti hX hq hb hc hn (by positivity) (by linarith : 1 + c * n' ≤ 1 + c * n) he h1
    have : 0 ≤ q * mx := mul_nonneg hq.le hm
    nlinarith
  rw [Pay0 k2 k1]
  exact Pay_nonneg hX hq hb hc hn' hs hm

lemma Pay_strict {e2' e1' : ℝ} (hs : 0 < s) (hm : 0 < mx) (hm1 : mx ≤ 1)
    (hk : 2 + c * n ≤ e2 * X ∨ 1 + c * n ≤ e1 * X) (h2 : e2 < e2') (h1 : e1 < e1') :
    Pay X c q bet s mx e2 e1 n < Pay X c q bet s mx e2' e1' n := by
  by_cases k2 : 2 + c * n ≤ e2 * X
  · have k2' : 2 + c * n ≤ e2' * X := by nlinarith
    rw [Pay2 k2, Pay2 k2']
    obtain ⟨_, he, _⟩ := frac_le_X hX hq hb hc hn (by positivity) k2
    have he' : 0 < e2' := by linarith
    have : (2 + c * n) / e2' < (2 + c * n) / e2 := by
      apply div_lt_div_of_pos_left (by positivity) he h2
    have : 0 < q * s := mul_pos hq hs
    nlinarith
  have k1 : 1 + c * n ≤ e1 * X := hk.resolve_left k2
  have k1' : 1 + c * n ≤ e1' * X := by nlinarith
  by_cases k2' : 2 + c * n ≤ e2' * X
  · have := Pay_lt1 hX hq hb hc hn (s := s) (e2 := e2) hm.le hm1 k2 k1
    have := Pay_ge2 hX hq hb hc hn (mx := mx) (e1 := e1') hs.le k2'
    linarith
  rw [Pay1 k2 k1, Pay1 k2' k1']
  obtain ⟨_, he, _⟩ := frac_le_X hX hq hb hc hn (by positivity) k1
  have : (1 + c * n) / e1' < (1 + c * n) / e1 := by
    apply div_lt_div_of_pos_left (by positivity) he h1
  have : 0 < q * mx := mul_pos hq hm
  nlinarith

lemma Pay_pos_k (hs : 0 ≤ s) (hm : 0 ≤ mx) (h : 0 < Pay X c q bet s mx e2 e1 n) :
    2 + c * n ≤ e2 * X ∨ 1 + c * n ≤ e1 * X := by
  by_contra hh; push Not at hh
  rw [Pay0 (not_le.mpr hh.1) (not_le.mpr hh.2)] at h; exact lt_irrefl _ h

lemma Pay00_ge (hk : 2 + c * n ≤ e2 * X ∨ 1 + c * n ≤ e1 * X) :
    bet ≤ Pay X c q bet 0 0 e2 e1 n := by
  have hbet : 0 < bet := by nlinarith
  rcases hk with h | h
  · have := Pay_ge2 hX hq hb hc hn (s := 0) (mx := 0) (e1 := e1) le_rfl h; linarith
  · exact Pay_ge1 hX hq hb hc hn (s := 0) (e2 := e2) le_rfl le_rfl h

end PayLemmas

@[simp] lemma upd0 (a b x : Bool) : Function.update (T a b) 0 x = T x b := by
  funext i; fin_cases i <;> simp [Function.update, T]
@[simp] lemma upd1 (a b x : Bool) : Function.update (T a b) 1 x = T a x := by
  funext i; fin_cases i <;> simp [Function.update, T]

/-! Beliefs at specific messages. -/
section Bel
variable {μ : Belief} (hμ : Admissible μ)
include hμ

lemma bel_ss_tt : E2 μ (M (some true) (some true)) = 2 ∧ E1 μ (M (some true) (some true)) = 1 := by
  have z1 := adm_zero hμ (some true) (some true) true false (by simp [cons_iff])
  have z2 := adm_zero hμ (some true) (some true) false true (by simp [cons_iff])
  have z3 := adm_zero hμ (some true) (some true) false false (by simp [cons_iff])
  have hs := adm_sum hμ (M (some true) (some true))
  rw [E2_eq, E1_eq]; constructor <;> linarith

lemma bel_s_n : E1 μ (M (some true) none) = 1 ∧ 1 ≤ E2 μ (M (some true) none) ∧
    E2 μ (M (some true) none) ≤ 2 := by
  have z2 := adm_zero hμ (some true) none false true (by simp [cons_iff])
  have z3 := adm_zero hμ (some true) none false false (by simp [cons_iff])
  have hs := adm_sum hμ (M (some true) none)
  have n1 := adm_nn hμ (M (some true) none) (T true true)
  have n2 := adm_nn hμ (M (some true) none) (T true false)
  rw [E2_eq, E1_eq]; refine ⟨by linarith, by linarith, by linarith⟩

lemma bel_n_s : E1 μ (M none (some true)) = 1 ∧ 1 ≤ E2 μ (M none (some true)) ∧
    E2 μ (M none (some true)) ≤ 2 := by
  have z2 := adm_zero hμ none (some true) true false (by simp [cons_iff])
  have z3 := adm_zero hμ none (some true) false false (by simp [cons_iff])
  have hs := adm_sum hμ (M none (some true))
  have n1 := adm_nn hμ (M none (some true)) (T true true)
  have n2 := adm_nn hμ (M none (some true)) (T false true)
  rw [E2_eq, E1_eq]; refine ⟨by linarith, by linarith, by linarith⟩

lemma bel_f_n : E2 μ (M (some false) none) = μ (M (some false) none) (T false true) ∧
    E1 μ (M (some false) none) = μ (M (some false) none) (T false true) ∧
    μ (M (some false) none) (T false true) ≤ 1 := by
  have z1 := adm_zero hμ (some false) none true true (by simp [cons_iff])
  have z2 := adm_zero hμ (some false) none true false (by simp [cons_iff])
  have hs := adm_sum hμ (M (some false) none)
  have n1 := adm_nn hμ (M (some false) none) (T false false)
  rw [E2_eq, E1_eq]; refine ⟨by linarith, by linarith, by linarith⟩

lemma bel_n_f : E2 μ (M none (some false)) = μ (M none (some false)) (T true false) ∧
    E1 μ (M none (some false)) = μ (M none (some false)) (T true false) ∧
    μ (M none (some false)) (T true false) ≤ 1 := by
  have z1 := adm_zero hμ none (some false) true true (by simp [cons_iff])
  have z2 := adm_zero hμ none (some false) false true (by simp [cons_iff])
  have hs := adm_sum hμ (M none (some false))
  have n1 := adm_nn hμ (M none (some false)) (T false false)
  rw [E2_eq, E1_eq]; refine ⟨by linarith, by linarith, by linarith⟩

lemma bel_ff : E2 μ (M (some false) (some false)) = 0 ∧ E1 μ (M (some false) (some false)) = 0 := by
  have z1 := adm_zero hμ (some false) (some false) true true (by simp [cons_iff])
  have z2 := adm_zero hμ (some false) (some false) true false (by simp [cons_iff])
  have z3 := adm_zero hμ (some false) (some false) false true (by simp [cons_iff])
  rw [E2_eq, E1_eq]; constructor <;> linarith

lemma bel_ft : E2 μ (M (some false) (some true)) = 1 ∧ E1 μ (M (some false) (some true)) = 1 := by
  have z1 := adm_zero hμ (some false) (some true) true true (by simp [cons_iff])
  have z2 := adm_zero hμ (some false) (some true) true false (by simp [cons_iff])
  have z3 := adm_zero hμ (some false) (some true) false false (by simp [cons_iff])
  have hs := adm_sum hμ (M (some false) (some true))
  rw [E2_eq, E1_eq]; constructor <;> linarith

lemma bel_tf : E2 μ (M (some true) (some false)) = 1 ∧ E1 μ (M (some true) (some false)) = 1 := by
  have z1 := adm_zero hμ (some true) (some false) true true (by simp [cons_iff])
  have z2 := adm_zero hμ (some true) (some false) false true (by simp [cons_iff])
  have z3 := adm_zero hμ (some true) (some false) false false (by simp [cons_iff])
  have hs := adm_sum hμ (M (some true) (some false))
  rw [E2_eq, E1_eq]; constructor <;> linarith

lemma bel_nn_le : E1 μ (M none none) ≤ 1 ∧ E1 μ (M none none) ≤ E2 μ (M none none) := by
  have hs := adm_sum hμ (M none none)
  have n1 := adm_nn hμ (M none none) (T false false)
  have n2 := adm_nn hμ (M none none) (T true true)
  rw [E2_eq, E1_eq]; constructor <;> linarith

end Bel

lemma pathMass_eq (p : ℝ) (σ : Profile → Disc) (m : Msg) : pathMass p σ m =
    (if msg (T true true) (σ (T true true)) = m then prior p (T true true) else 0) +
    (if msg (T true false) (σ (T true false)) = m then prior p (T true false) else 0) +
    (if msg (T false true) (σ (T false true)) = m then prior p (T false true) else 0) +
    (if msg (T false false) (σ (T false false)) = m then prior p (T false false) else 0) := by
  unfold pathMass; rw [sum4]

section Game
variable {p X c q bet : ℝ}

lemma P11 {μ : Belief} (hμ : Admissible μ) (hX : 0 < X) (hc : 0 ≤ c) (m : Msg) :
    mgrPayoff X c q bet μ (T true true) m = Pay X c q bet 2 1 (E2 μ m) (E1 μ m) (nD m) := by
  rw [mgr_eq hμ hX hc]; norm_num
lemma P10 {μ : Belief} (hμ : Admissible μ) (hX : 0 < X) (hc : 0 ≤ c) (m : Msg) :
    mgrPayoff X c q bet μ (T true false) m = Pay X c q bet 1 1 (E2 μ m) (E1 μ m) (nD m) := by
  rw [mgr_eq hμ hX hc]; norm_num
lemma P01 {μ : Belief} (hμ : Admissible μ) (hX : 0 < X) (hc : 0 ≤ c) (m : Msg) :
    mgrPayoff X c q bet μ (T false true) m = Pay X c q bet 1 1 (E2 μ m) (E1 μ m) (nD m) := by
  rw [mgr_eq hμ hX hc]; norm_num
lemma P00 {μ : Belief} (hμ : Admissible μ) (hX : 0 < X) (hc : 0 ≤ c) (m : Msg) :
    mgrPayoff X c q bet μ (T false false) m = Pay X c q bet 0 0 (E2 μ m) (E1 μ m) (nD m) := by
  rw [mgr_eq hμ hX hc]; norm_num

lemma bayes {σ : Profile → Disc} {μ : Belief} (hB : BayesConsistent p σ μ) (t0 : Profile)
    (m : Msg) (h0 : msg t0 (σ t0) = m) (t' : Profile) :
    μ m t' = (if msg t' (σ t') = m then prior p t' else 0) / pathMass p σ m :=
  hB m ⟨t0, h0⟩ t'

variable (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 < X) (hc : 0 < c) (hq0 : 0 < q)
  (hbet : q * X < bet) (hf : 1 + c ≤ X)
include hp0 hp1 hX hc hq0 hbet hf

lemma B1_00a {σ : Profile → Disc} {μ : Belief} (hE : IsEquilibrium p X c q bet σ μ) :
    σ (T false false) 0 = false := by
  obtain ⟨hA, hB, hIC, hT⟩ := hE
  have hX0 : (0:ℝ) < X := by linarith
  have hc0 : (0:ℝ) ≤ c := hc.le
  obtain ⟨d1, d2, hd⟩ : ∃ d1 d2, σ (T false false) = T d1 d2 := ⟨_, _, T_eta _⟩
  rw [hd]; simp only [T_0]
  by_contra h0; simp only [Bool.not_eq_false] at h0; subst h0
  have tie := hT (T false false) 0 (by rw [hd]; rfl)
  rw [hd] at tie
  simp only [upd0, msg_T, P00 hA hX0 hc0, o_t, o_f] at tie
  cases d2
  · -- message (0, N)
    simp only [o_f, nD_M, Option.isSome_some, Option.isSome_none, if_true] at tie
    simp only [Bool.false_eq_true, if_false, add_zero, zero_add] at tie
    have hnn := Pay_nonneg hX0 hq0 hbet hc0 (by norm_num : (0:ℝ) ≤ 0) (s := 0) (mx := 0)
      (e2 := E2 μ (M none none)) (e1 := E1 μ (M none none)) le_rfl le_rfl
    have hk := Pay_pos_k hX0 hq0 hbet hc0 (by norm_num : (0:ℝ) ≤ 1) le_rfl le_rfl
      (e2 := E2 μ (M (some false) none)) (e1 := E1 μ (M (some false) none)) (by linarith)
    obtain ⟨b2, b1, _⟩ := bel_f_n hA
    rw [b2, b1] at hk
    set w := μ (M (some false) none) (T false true) with hw
    have hwpos : 0 < w := by
      rcases hk with h | h <;> (by_contra hh; push Not at hh; nlinarith)
    have hb := bayes hB (T false false) (M (some false) none) (by rw [hd]; simp) (T false true)
    rw [← hw] at hb
    by_cases h01 : msg (T false true) (σ (T false true)) = M (some false) none
    swap
    · rw [if_neg h01, zero_div] at hb; linarith
    rw [if_pos h01] at hb
    obtain ⟨u, v, huv⟩ : ∃ u v, σ (T true true) = T u v := ⟨_, _, T_eta _⟩
    obtain ⟨a1, a2, ha⟩ : ∃ a1 a2, σ (T true false) = T a1 a2 := ⟨_, _, T_eta _⟩
    have hpm : pathMass p σ (M (some false) none) = p * (1 - p) + (1 - p) * (1 - p) := by
      rw [pathMass_eq, if_pos h01, huv, ha, hd]
      cases u <;> cases v <;> cases a1 <;> cases a2 <;> simp <;> ring
    rw [hpm] at hb
    have hwp : w = p := by
      rw [hb]; simp
      have : p * (1 - p) + (1 - p) * (1 - p) = 1 - p := by ring
      rw [this, div_eq_iff (by linarith)]; ring
    obtain ⟨e1, e2, he⟩ : ∃ e1 e2, σ (T false true) = T e1 e2 := ⟨_, _, T_eta _⟩
    rw [he] at h01
    have dev := hIC (T false true) (T false true)
    rw [he, h01] at dev
    simp only [msg_T, o_t, o_f, P01 hA hX0 hc0, nD_M, Option.isSome_some, Option.isSome_none,
      if_true, Bool.false_eq_true, if_false, add_zero, zero_add] at dev
    obtain ⟨c1, c2, -⟩ := bel_n_s hA
    rw [c1, b2, b1, hwp] at dev
    have := Pay_strict hX0 hq0 hbet hc0 (by norm_num : (0:ℝ) ≤ 0 + 1) (s := 1) (mx := 1)
      (e2 := p) (e1 := p) (e2' := E2 μ (M none (some true))) (e1' := 1)
      one_pos one_pos le_rfl (by rw [← hwp]; simpa using hk) (by linarith) hp1
    simp at this dev
    linarith
  · -- message (0, 0)
    simp only [o_t, nD_M, Option.isSome_some, if_true] at tie
    obtain ⟨b2, b1⟩ := bel_ff hA
    rw [b2, b1] at tie
    have h0 : Pay X c q bet 0 0 0 0 (1 + 1) = 0 := Pay0 (by norm_num; linarith) (by norm_num; linarith)
    rw [h0] at tie
    have := Pay_nonneg hX0 hq0 hbet hc0 (by norm_num : (0:ℝ) ≤ 0 + 1) (s := 0) (mx := 0)
      (e2 := E2 μ (M none (some false))) (e1 := E1 μ (M none (some false))) le_rfl le_rfl
    simp at this tie
    linarith

lemma B1_00b {σ : Profile → Disc} {μ : Belief} (hE : IsEquilibrium p X c q bet σ μ) :
    σ (T false false) 1 = false := by
  have ha := B1_00a hp0 hp1 hX hc hq0 hbet hf hE
  obtain ⟨hA, hB, hIC, hT⟩ := hE
  have hX0 : (0:ℝ) < X := by linarith
  have hc0 : (0:ℝ) ≤ c := hc.le
  obtain ⟨d1, d2, hd⟩ : ∃ d1 d2, σ (T false false) = T d1 d2 := ⟨_, _, T_eta _⟩
  rw [hd] at ha ⊢; simp only [T_0] at ha; subst ha; simp only [T_1]
  by_contra h0; simp only [Bool.not_eq_false] at h0; subst h0
  have tie := hT (T false false) 1 (by rw [hd]; rfl)
  rw [hd] at tie
  simp only [upd1, msg_T, P00 hA hX0 hc0, o_t, o_f, nD_M, Option.isSome_some,
    Option.isSome_none, if_true, Bool.false_eq_true, if_false, add_zero, zero_add] at tie
  have hnn := Pay_nonneg hX0 hq0 hbet hc0 (by norm_num : (0:ℝ) ≤ 0) (s := 0) (mx := 0)
    (e2 := E2 μ (M none none)) (e1 := E1 μ (M none none)) le_rfl le_rfl
  have hk := Pay_pos_k hX0 hq0 hbet hc0 (by norm_num : (0:ℝ) ≤ 1) le_rfl le_rfl
    (e2 := E2 μ (M none (some false))) (e1 := E1 μ (M none (some false))) (by linarith)
  obtain ⟨b2, b1, _⟩ := bel_n_f hA
  rw [b2, b1] at hk
  set w := μ (M none (some false)) (T true false) with hw
  have hwpos : 0 < w := by
    rcases hk with h | h <;> (by_contra hh; push Not at hh; nlinarith)
  have hb := bayes hB (T false false) (M none (some false)) (by rw [hd]; simp) (T true false)
  rw [← hw] at hb
  by_cases h10 : msg (T true false) (σ (T true false)) = M none (some false)
  swap
  · rw [if_neg h10, zero_div] at hb; linarith
  rw [if_pos h10] at hb
  obtain ⟨u, v, huv⟩ : ∃ u v, σ (T true true) = T u v := ⟨_, _, T_eta _⟩
  obtain ⟨a1, a2, ha⟩ : ∃ a1 a2, σ (T false true) = T a1 a2 := ⟨_, _, T_eta _⟩
  have hpm : pathMass p σ (M none (some false)) = p * (1 - p) + (1 - p) * (1 - p) := by
    rw [pathMass_eq, if_pos h10, huv, ha, hd]
    cases u <;> cases v <;> cases a1 <;> cases a2 <;> simp <;> ring
  rw [hpm] at hb
  have hwp : w = p := by
    rw [hb]; simp
    have : p * (1 - p) + (1 - p) * (1 - p) = 1 - p := by ring
    rw [this, div_eq_iff (by linarith)]
  obtain ⟨e1, e2, he⟩ : ∃ e1 e2, σ (T true false) = T e1 e2 := ⟨_, _, T_eta _⟩
  rw [he] at h10
  have dev := hIC (T true false) (T true false)
  rw [he, h10] at dev
  simp only [msg_T, o_t, o_f, P10 hA hX0 hc0, nD_M, Option.isSome_some, Option.isSome_none,
    if_true, Bool.false_eq_true, if_false, add_zero, zero_add] at dev
  obtain ⟨c1, c2, -⟩ := bel_s_n hA
  rw [c1, b2, b1, hwp] at dev
  have := Pay_strict hX0 hq0 hbet hc0 (by norm_num : (0:ℝ) ≤ 1) (s := 1) (mx := 1)
    (e2 := p) (e1 := p) (e2' := E2 μ (M (some true) none)) (e1' := 1)
    one_pos one_pos le_rfl (by rw [← hwp]; simpa using hk) (by linarith) hp1
  linarith

lemma B1_00 {σ : Profile → Disc} {μ : Belief} (hE : IsEquilibrium p X c q bet σ μ) :
    σ (T false false) = T false false := by
  rw [T_eta (σ _), B1_00a hp0 hp1 hX hc hq0 hbet hf hE, B1_00b hp0 hp1 hX hc hq0 hbet hf hE]

lemma B1_01 {σ : Profile → Disc} {μ : Belief} (hE : IsEquilibrium p X c q bet σ μ) :
    σ (T false true) 0 = false := by
  have h00 := B1_00 hp0 hp1 hX hc hq0 hbet hf hE
  obtain ⟨hA, hB, hIC, hT⟩ := hE
  have hX0 : (0:ℝ) < X := by linarith
  have hc0 : (0:ℝ) ≤ c := hc.le
  have hbet0 : 0 < bet := by nlinarith
  obtain ⟨e1, e2, he⟩ : ∃ e1 e2, σ (T false true) = T e1 e2 := ⟨_, _, T_eta _⟩
  rw [he]; simp only [T_0]
  by_contra h0; simp only [Bool.not_eq_false] at h0; subst h0
  have tie := hT (T false true) 0 (by rw [he]; rfl)
  rw [he] at tie
  simp only [upd0, msg_T, P01 hA hX0 hc0, o_t, o_f, nD_M, Option.isSome_some,
    Option.isSome_none, if_true, Bool.false_eq_true, if_false, add_zero, zero_add] at tie
  cases e2
  · -- 01 sends (0, N)
    simp only [o_f, nD_M, Option.isSome_some, Option.isSome_none, if_true, Bool.false_eq_true,
      if_false, add_zero, zero_add] at tie
    obtain ⟨b2, b1, hw1⟩ := bel_f_n hA
    rw [b2, b1] at tie
    set w := μ (M (some false) none) (T false true) with hw
    have hw0 : 0 ≤ w := adm_nn hA _ _
    have ic00 := hIC (T false false) (T true false)
    rw [h00] at ic00
    simp only [msg_T, o_t, o_f, P00 hA hX0 hc0, nD_M, Option.isSome_some, Option.isSome_none,
      if_true, Bool.false_eq_true, if_false, add_zero, zero_add] at ic00
    rw [b2, b1] at ic00
    obtain ⟨u, v, huv⟩ : ∃ u v, σ (T true true) = T u v := ⟨_, _, T_eta _⟩
    obtain ⟨a1, a2, ha⟩ : ∃ a1 a2, σ (T true false) = T a1 a2 := ⟨_, _, T_eta _⟩
    by_cases h11 : u = false ∧ v = false
    · obtain ⟨rfl, rfl⟩ := h11
      have ic11 := hIC (T true true) (T true true)
      rw [huv] at ic11
      simp only [msg_T, o_t, o_f, P11 hA hX0 hc0, nD_M, Option.isSome_some, Option.isSome_none,
        if_true, Bool.false_eq_true, if_false, add_zero, zero_add] at ic11
      obtain ⟨s2, s1⟩ := bel_ss_tt hA
      rw [s2, s1, Pay2 (by norm_num; nlinarith)] at ic11
      have k2 : 2 + c * 0 ≤ E2 μ (M none none) * X := by
        by_contra hh
        have := Pay_lt2 hX0 hq0 hbet hc0 le_rfl (s := 2) (e1 := E1 μ (M none none))
          zero_le_one le_rfl hh
        have : 0 ≤ q * 2 * (X - (2 + c * (1 + 1)) / 2) := by
          apply mul_nonneg (by positivity); linarith
        linarith
      rw [Pay2 k2] at ic11 tie
      obtain ⟨-, he2, -⟩ := frac_le_X hX0 hq0 hbet hc0 le_rfl (by norm_num) k2
      have key : 2 / E2 μ (M none none) ≤ 1 + c := by
        have : q * 2 * (X - (2 + c * (1 + 1)) / 2) ≤ q * 2 * (X - (2 + c * 0) / E2 μ (M none none)) := by
          linarith
        have := le_of_mul_le_mul_left this (by positivity : (0:ℝ) < q * 2)
        simp at this; linarith
      by_cases km : 2 + c * 1 ≤ w * X
      · rw [Pay2 km] at tie
        obtain ⟨-, hwp, -⟩ := frac_le_X hX0 hq0 hbet hc0 zero_le_one (by positivity) km
        have : 2 + c ≤ (2 + c) / w := by
          rw [le_div_iff₀ hwp]; nlinarith
        have : q * 1 * (X - (2 + c * 0) / E2 μ (M none none)) < q * 1 * (X - (2 + c * 1) / w) := by
          linarith
        have := lt_of_mul_lt_mul_left this (by positivity : (0:ℝ) ≤ q * 1)
        simp at this; linarith
      · have := Pay_lt2 hX0 hq0 hbet hc0 zero_le_one (s := 1) (e1 := w) zero_le_one le_rfl km
        have : 0 ≤ q * 1 * (X - (2 + c * 0) / E2 μ (M none none)) := by
          obtain ⟨h, -, -⟩ := frac_le_X hX0 hq0 hbet hc0 le_rfl (by norm_num) k2
          apply mul_nonneg (by positivity); linarith
        linarith
    by_cases h10 : a1 = false ∧ a2 = false
    · obtain ⟨rfl, rfl⟩ := h10
      have ic10 := hIC (T true false) (T true false)
      rw [ha] at ic10
      simp only [msg_T, o_t, o_f, P10 hA hX0 hc0, nD_M, Option.isSome_some, Option.isSome_none,
        if_true, Bool.false_eq_true, if_false, add_zero, zero_add] at ic10
      obtain ⟨c1, c2, -⟩ := bel_s_n hA
      rw [c1] at ic10
      have := Pay_mono hX0 hq0 hbet hc0 (by norm_num : (0:ℝ) ≤ 1) (s := 1) (mx := 1)
        (e2 := w) (e1 := w) (e2' := E2 μ (M (some true) none)) (e1' := 1) (n' := 1)
        (by norm_num) (by norm_num) (by norm_num) le_rfl (by linarith) hw1 le_rfl
      linarith
    -- nobody else pools at (N, N)
    have hb0 := bayes hB (T false false) (M none none) (by rw [h00]; simp)
    have z1 : μ (M none none) (T true true) = 0 := by
      rw [hb0, huv]; cases u <;> cases v <;> simp_all
    have z2 : μ (M none none) (T true false) = 0 := by
      rw [hb0, ha]; cases a1 <;> cases a2 <;> simp_all
    have z3 : μ (M none none) (T false true) = 0 := by
      rw [hb0, he]; simp
    have e2z : E2 μ (M none none) = 0 := by rw [E2_eq]; linarith
    have e1z : E1 μ (M none none) = 0 := by rw [E1_eq]; linarith
    rw [e2z, e1z] at ic00 tie
    have h0 : Pay X c q bet 0 0 0 0 0 = 0 := Pay0 (by norm_num) (by norm_num)
    have h1 : Pay X c q bet 1 1 0 0 0 = 0 := Pay0 (by norm_num) (by norm_num)
    rw [h0] at ic00; rw [h1] at tie
    have hk := Pay_pos_k hX0 hq0 hbet hc0 (by norm_num : (0:ℝ) ≤ 1) zero_le_one zero_le_one tie
    have := Pay00_ge hX0 hq0 hbet hc0 (by norm_num : (0:ℝ) ≤ 1) hk
    linarith
  · -- 01 sends (0, 1)
    simp only [o_t, nD_M, Option.isSome_some, if_true] at tie
    obtain ⟨f2, f1⟩ := bel_ft hA
    obtain ⟨c1, c2, -⟩ := bel_n_s hA
    rw [f2, f1, c1] at tie
    have := Pay_mono hX0 hq0 hbet hc0 (by norm_num : (0:ℝ) ≤ 1 + 1) (s := 1) (mx := 1)
      (e2 := 1) (e1 := 1) (e2' := E2 μ (M none (some true))) (e1' := 1) (n' := 1)
      (by norm_num) (by norm_num) (by norm_num) le_rfl c2 le_rfl (by norm_num)
    linarith

lemma B1_10 {σ : Profile → Disc} {μ : Belief} (hE : IsEquilibrium p X c q bet σ μ) :
    σ (T true false) 1 = false := by
  have h00 := B1_00 hp0 hp1 hX hc hq0 hbet hf hE
  obtain ⟨hA, hB, hIC, hT⟩ := hE
  have hX0 : (0:ℝ) < X := by linarith
  have hc0 : (0:ℝ) ≤ c := hc.le
  have hbet0 : 0 < bet := by nlinarith
  obtain ⟨e1, e2, he⟩ : ∃ e1 e2, σ (T true false) = T e2 e1 := ⟨_, _, T_eta _⟩
  rw [he]; simp only [T_1]
  by_contra h0; simp only [Bool.not_eq_false] at h0; subst h0
  have tie := hT (T true false) 1 (by rw [he]; rfl)
  rw [he] at tie
  simp only [upd1, msg_T, P10 hA hX0 hc0, o_t, o_f, nD_M, Option.isSome_some,
    Option.isSome_none, if_true, Bool.false_eq_true, if_false, add_zero, zero_add] at tie
  cases e2
  · -- 01 sends (0, N)
    simp only [o_f, nD_M, Option.isSome_some, Option.isSome_none, if_true, Bool.false_eq_true,
      if_false, add_zero, zero_add] at tie
    obtain ⟨b2, b1, hw1⟩ := bel_n_f hA
    rw [b2, b1] at tie
    set w := μ (M none (some false)) (T true false) with hw
    have hw0 : 0 ≤ w := adm_nn hA _ _
    have ic00 := hIC (T false false) (T false true)
    rw [h00] at ic00
    simp only [msg_T, o_t, o_f, P00 hA hX0 hc0, nD_M, Option.isSome_some, Option.isSome_none,
      if_true, Bool.false_eq_true, if_false, add_zero, zero_add] at ic00
    rw [b2, b1] at ic00
    obtain ⟨u, v, huv⟩ : ∃ u v, σ (T true true) = T v u := ⟨_, _, T_eta _⟩
    obtain ⟨a1, a2, ha⟩ : ∃ a1 a2, σ (T false true) = T a2 a1 := ⟨_, _, T_eta _⟩
    by_cases h11 : u = false ∧ v = false
    · obtain ⟨rfl, rfl⟩ := h11
      have ic11 := hIC (T true true) (T true true)
      rw [huv] at ic11
      simp only [msg_T, o_t, o_f, P11 hA hX0 hc0, nD_M, Option.isSome_some, Option.isSome_none,
        if_true, Bool.false_eq_true, if_false, add_zero, zero_add] at ic11
      obtain ⟨s2, s1⟩ := bel_ss_tt hA
      rw [s2, s1, Pay2 (by norm_num; nlinarith)] at ic11
      have k2 : 2 + c * 0 ≤ E2 μ (M none none) * X := by
        by_contra hh
        have := Pay_lt2 hX0 hq0 hbet hc0 le_rfl (s := 2) (e1 := E1 μ (M none none))
          zero_le_one le_rfl hh
        have : 0 ≤ q * 2 * (X - (2 + c * (1 + 1)) / 2) := by
          apply mul_nonneg (by positivity); linarith
        linarith
      rw [Pay2 k2] at ic11 tie
      obtain ⟨-, he2, -⟩ := frac_le_X hX0 hq0 hbet hc0 le_rfl (by norm_num) k2
      have key : 2 / E2 μ (M none none) ≤ 1 + c := by
        have : q * 2 * (X - (2 + c * (1 + 1)) / 2) ≤ q * 2 * (X - (2 + c * 0) / E2 μ (M none none)) := by
          linarith
        have := le_of_mul_le_mul_left this (by positivity : (0:ℝ) < q * 2)
        simp at this; linarith
      by_cases km : 2 + c * 1 ≤ w * X
      · rw [Pay2 km] at tie
        obtain ⟨-, hwp, -⟩ := frac_le_X hX0 hq0 hbet hc0 zero_le_one (by positivity) km
        have : 2 + c ≤ (2 + c) / w := by
          rw [le_div_iff₀ hwp]; nlinarith
        have : q * 1 * (X - (2 + c * 0) / E2 μ (M none none)) < q * 1 * (X - (2 + c * 1) / w) := by
          linarith
        have := lt_of_mul_lt_mul_left this (by positivity : (0:ℝ) ≤ q * 1)
        simp at this; linarith
      · have := Pay_lt2 hX0 hq0 hbet hc0 zero_le_one (s := 1) (e1 := w) zero_le_one le_rfl km
        have : 0 ≤ q * 1 * (X - (2 + c * 0) / E2 μ (M none none)) := by
          obtain ⟨h, -, -⟩ := frac_le_X hX0 hq0 hbet hc0 le_rfl (by norm_num) k2
          apply mul_nonneg (by positivity); linarith
        linarith
    by_cases h10 : a1 = false ∧ a2 = false
    · obtain ⟨rfl, rfl⟩ := h10
      have ic10 := hIC (T false true) (T false true)
      rw [ha] at ic10
      simp only [msg_T, o_t, o_f, P01 hA hX0 hc0, nD_M, Option.isSome_some, Option.isSome_none,
        if_true, Bool.false_eq_true, if_false, add_zero, zero_add] at ic10
      obtain ⟨c1, c2, -⟩ := bel_n_s hA
      rw [c1] at ic10
      have := Pay_mono hX0 hq0 hbet hc0 (by norm_num : (0:ℝ) ≤ 1) (s := 1) (mx := 1)
        (e2 := w) (e1 := w) (e2' := E2 μ (M none (some true))) (e1' := 1) (n' := 1)
        (by norm_num) (by norm_num) (by norm_num) le_rfl (by linarith) hw1 le_rfl
      linarith
    -- nobody else pools at (N, N)
    have hb0 := bayes hB (T false false) (M none none) (by rw [h00]; simp)
    have z1 : μ (M none none) (T true true) = 0 := by
      rw [hb0, huv]; cases u <;> cases v <;> simp_all
    have z2 : μ (M none none) (T false true) = 0 := by
      rw [hb0, ha]; cases a1 <;> cases a2 <;> simp_all
    have z3 : μ (M none none) (T true false) = 0 := by
      rw [hb0, he]; simp
    have e2z : E2 μ (M none none) = 0 := by rw [E2_eq]; linarith
    have e1z : E1 μ (M none none) = 0 := by rw [E1_eq]; linarith
    rw [e2z, e1z] at ic00 tie
    have h0 : Pay X c q bet 0 0 0 0 0 = 0 := Pay0 (by norm_num) (by norm_num)
    have h1 : Pay X c q bet 1 1 0 0 0 = 0 := Pay0 (by norm_num) (by norm_num)
    rw [h0] at ic00; rw [h1] at tie
    have hk := Pay_pos_k hX0 hq0 hbet hc0 (by norm_num : (0:ℝ) ≤ 1) zero_le_one zero_le_one tie
    have := Pay00_ge hX0 hq0 hbet hc0 (by norm_num : (0:ℝ) ≤ 1) hk
    linarith
  · -- 01 sends (0, 1)
    simp only [o_t, nD_M, Option.isSome_some, if_true] at tie
    obtain ⟨f2, f1⟩ := bel_tf hA
    obtain ⟨c1, c2, -⟩ := bel_s_n hA
    rw [f2, f1, c1] at tie
    have := Pay_mono hX0 hq0 hbet hc0 (by norm_num : (0:ℝ) ≤ 1 + 1) (s := 1) (mx := 1)
      (e2 := 1) (e1 := 1) (e2' := E2 μ (M (some true) none)) (e1' := 1) (n' := 1)
      (by norm_num) (by norm_num) (by norm_num) le_rfl c2 le_rfl (by norm_num)
    linarith

theorem B1 {σ : Profile → Disc} {μ : Belief} (hE : IsEquilibrium p X c q bet σ μ) :
    ∀ t i, t i = false → σ t i = false := by
  intro t i hti
  obtain ⟨a, b, rfl⟩ : ∃ a b, t = T a b := ⟨_, _, T_eta t⟩
  have h00 := B1_00 hp0 hp1 hX hc hq0 hbet hf hE
  have h01 := B1_01 hp0 hp1 hX hc hq0 hbet hf hE
  have h10 := B1_10 hp0 hp1 hX hc hq0 hbet hf hE
  fin_cases i <;> simp at hti <;> subst hti
  · cases b
    · simp [h00]
    · exact h01
  · cases a
    · simp [h00]
    · exact h10

end Game

end ICA

open ICA in
theorem solution (p X c q bet : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 < X) (hc : 0 < c)
    (hq0 : 0 < q) (hq1 : q < 1) (hbet : q * X < bet) (hfocus : 1 + c ≤ X)
    (σ : Profile → Disc) (μ : Belief) (hEq : IsEquilibrium p X c q bet σ μ) :
    ∀ t i, t i = false → σ t i = false :=
  B1 hp0 hp1 hX hc hq0 hbet hfocus hEq
