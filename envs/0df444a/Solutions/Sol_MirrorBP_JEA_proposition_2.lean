-- Prove2me | solution 1 for MirrorBP.JEA.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T17:47:54.189324+00:00
-- url     : https://prove2.me/submissions/c88dd43b-2675-4677-9f6e-32e63a52ffb8

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP
import Definitions.Def_MirrorBP_JEA_SPP
import Theorems.Thm_MirrorBP_JEA_proposition_1
import Theorems.Thm_MirrorBP_JEA_proposition_3
import Theorems.Thm_MirrorBP_JEA_proposition_4

namespace MirrorBP.JEA.Prop2Aux

open Finset MirrorBP.JEA

variable {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]

/-- The policy `π` restarted at period `t0` after history `h0`. -/
def shiftPol {P D : Ty → Finset V} (π : Policy P D) (t0 : ℕ) (h0 : History V Ty) : Policy P D where
  act t h q τ d := π.act (t0 + t) (h0 ++ h) q τ d
  nonneg t h q τ d := π.nonneg _ _ _ _ _
  sum_one t h q τ := π.sum_one _ _ _ _
  feasible t h q τ d hd := π.feasible _ _ _ _ _ hd

theorem expPayoffFrom_shift {P D : Ty → Finset V} (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ)
    (π : Policy P D) (t0 : ℕ) (h0 : History V Ty) :
    ∀ n s h q, expPayoffFrom w phi π n (t0 + s) (h0 ++ h) q
      = expPayoffFrom w (fun t => phi (t0 + t)) (shiftPol π t0 h0) n s h q := by
  intro n
  induction n with
  | zero => intro s h q; simp [expPayoffFrom]
  | succ n ih =>
    intro s h q
    rw [expPayoffFrom, expPayoffFrom]
    apply sum_congr rfl
    intro τ _
    congr 1
    apply sum_congr rfl
    intro d _
    have := ih (s + 1) (h ++ [(q, τ, d)]) (step q d)
    rw [← List.append_assoc] at this
    rw [show t0 + s + 1 = t0 + (s + 1) by ring, this]
    rfl

theorem expPayoffFrom_congr {P D : Ty → Finset V} (w : V → Ty → V → ℝ) (phi phi' : ℕ → Ty → ℝ)
    (π : Policy P D) :
    ∀ n t h q, (∀ s, t ≤ s → s < t + n → phi s = phi' s) →
      expPayoffFrom w phi π n t h q = expPayoffFrom w phi' π n t h q := by
  intro n
  induction n with
  | zero => intro t h q _; simp [expPayoffFrom]
  | succ n ih =>
    intro t h q hphi
    rw [expPayoffFrom, expPayoffFrom, hphi t le_rfl (by omega)]
    apply sum_congr rfl
    intro τ _
    congr 1
    apply sum_congr rfl
    intro d _
    rw [ih (t + 1) _ _ (fun s h1 h2 => hphi s (by omega) (by omega))]

theorem step_mem {P D : Ty → Finset V} (K : ℕ) (τ : Ty) (q : V → ℕ) (d : Decision V)
    (hf : Feasible P D τ q d) (hq : q ∈ StateSpace V K) : step q d ∈ StateSpace V K := by
  rcases d with _ | ⟨j, k⟩
  · simpa [step] using hq
  · have hj : 0 < q j := hf.2.2
    simp only [StateSpace, Set.mem_setOf_eq] at hq ⊢
    simp only [step, Pi.add_apply, Pi.sub_apply]
    rw [sum_add_distrib, Finset.sum_tsub_distrib]
    · simp [Finset.sum_pi_single', hq]
      have : K = ∑ j, q j := hq.symm
      have : q j ≤ ∑ i, q i := Finset.single_le_sum (fun i _ => Nat.zero_le _) (mem_univ j)
      omega
    · intro i _
      by_cases hij : i = j
      · subst hij; simp; omega
      · simp [Pi.single_apply, hij]

/-- One period of averaging: comparing the integrands at all feasible decisions. -/
theorem avg_le {P D : Ty → Finset V} (phi : Ty → ℝ) (hφ : IsRate phi) (π : Policy P D) (t : ℕ)
    (h : History V Ty) (q : V → ℕ) (f g : Ty → Decision V → ℝ) (B : ℝ)
    (hfg : ∀ τ d, Feasible P D τ q d → f τ d ≤ g τ d + B) :
    ∑ τ, phi τ * ∑ d, π.act t h q τ d * f τ d ≤ (∑ τ, phi τ * ∑ d, π.act t h q τ d * g τ d) + B := by
  have hinner : ∀ τ, ∑ d, π.act t h q τ d * f τ d ≤ (∑ d, π.act t h q τ d * g τ d) + B := by
    intro τ
    calc ∑ d, π.act t h q τ d * f τ d ≤ ∑ d, π.act t h q τ d * (g τ d + B) := by
          apply sum_le_sum
          intro d _
          by_cases hf : Feasible P D τ q d
          · exact mul_le_mul_of_nonneg_left (hfg τ d hf) (π.nonneg _ _ _ _ _)
          · rw [π.feasible _ _ _ _ _ hf]; simp
      _ = (∑ d, π.act t h q τ d * g τ d) + B := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, π.sum_one, one_mul]
  calc ∑ τ, phi τ * ∑ d, π.act t h q τ d * f τ d
      ≤ ∑ τ, phi τ * ((∑ d, π.act t h q τ d * g τ d) + B) := by
        apply sum_le_sum
        intro τ _
        exact mul_le_mul_of_nonneg_left (hinner τ) (hφ.1 τ)
    _ = (∑ τ, phi τ * ∑ d, π.act t h q τ d * g τ d) + B := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, hφ.2, one_mul]

theorem avg_ge {P D : Ty → Finset V} (phi : Ty → ℝ) (hφ : IsRate phi) (π : Policy P D) (t : ℕ)
    (h : History V Ty) (q : V → ℕ) (f g : Ty → Decision V → ℝ) (B : ℝ)
    (hfg : ∀ τ d, Feasible P D τ q d → g τ d + B ≤ f τ d) :
    (∑ τ, phi τ * ∑ d, π.act t h q τ d * g τ d) + B ≤ ∑ τ, phi τ * ∑ d, π.act t h q τ d * f τ d := by
  have := avg_le phi hφ π t h q (fun τ d => - f τ d) (fun τ d => - g τ d) (-B)
    (fun τ d hf => by have := hfg τ d hf; linarith)
  simp only [mul_neg, sum_neg_distrib] at this
  linarith

/-- Splitting the horizon, upper bound form. -/
theorem split_le {P D : Ty → Finset V} (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ) (π : Policy P D)
    (K b : ℕ) (B : ℝ) :
    ∀ a t h q, q ∈ StateSpace V K → (∀ s, t ≤ s → s < t + a → IsRate (phi s)) →
      (∀ h' q', q' ∈ StateSpace V K → expPayoffFrom w phi π b (t + a) h' q' ≤ B) →
      expPayoffFrom w phi π (a + b) t h q ≤ expPayoffFrom w phi π a t h q + B := by
  intro a
  induction a with
  | zero =>
    intro t h q hq _ hB
    simpa [expPayoffFrom] using hB h q hq
  | succ a ih =>
    intro t h q hq hr hB
    rw [show a + 1 + b = (a + b) + 1 by ring, expPayoffFrom, expPayoffFrom]
    apply avg_le _ (hr t le_rfl (by omega))
    intro τ d hf
    have := ih (t + 1) (h ++ [(q, τ, d)]) (step q d) (step_mem K τ q d hf hq)
      (fun s h1 h2 => hr s (by omega) (by omega))
      (fun h' q' hq' => by rw [show t + 1 + a = t + (a + 1) by ring]; exact hB h' q' hq')
    linarith

/-- Splitting the horizon, lower bound form. -/
theorem split_ge {P D : Ty → Finset V} (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ) (π : Policy P D)
    (K b : ℕ) (B : ℝ) :
    ∀ a t h q, q ∈ StateSpace V K → (∀ s, t ≤ s → s < t + a → IsRate (phi s)) →
      (∀ h' q', q' ∈ StateSpace V K → B ≤ expPayoffFrom w phi π b (t + a) h' q') →
      expPayoffFrom w phi π a t h q + B ≤ expPayoffFrom w phi π (a + b) t h q := by
  intro a
  induction a with
  | zero =>
    intro t h q hq _ hB
    simpa [expPayoffFrom] using hB h q hq
  | succ a ih =>
    intro t h q hq hr hB
    rw [show a + 1 + b = (a + b) + 1 by ring, expPayoffFrom, expPayoffFrom]
    apply avg_ge _ (hr t le_rfl (by omega))
    intro τ d hf
    have := ih (t + 1) (h ++ [(q, τ, d)]) (step q d) (step_mem K τ q d hf hq)
      (fun s h1 h2 => hr s (by omega) (by omega))
      (fun h' q' hq' => by rw [show t + 1 + a = t + (a + 1) by ring]; exact hB h' q' hq')
    linarith


/-- `‖φ^{s+1} − φ^s‖₁`. -/
noncomputable def dvar (phi : ℕ → Ty → ℝ) (s : ℕ) : ℝ := ∑ τ, |phi (s + 1) τ - phi s τ|

/-- Total variation of the rates inside the window `[t0, t0 + R)`. -/
noncomputable def Svar (phi : ℕ → Ty → ℝ) (t0 R : ℕ) : ℝ := ∑ t ∈ range (R - 1), dvar phi (t0 + t)

theorem dvar_nonneg (phi : ℕ → Ty → ℝ) (s : ℕ) : 0 ≤ dvar phi s := by
  unfold dvar; positivity

theorem Svar_nonneg (phi : ℕ → Ty → ℝ) (t0 R : ℕ) : 0 ≤ Svar phi t0 R := by
  unfold Svar; exact sum_nonneg (fun t _ => dvar_nonneg phi _)

theorem Svar_split (phi : ℕ → Ty → ℝ) (t0 r R : ℕ) (hr : 1 ≤ r) (hrR : r ≤ R) :
    Svar phi t0 r + Svar phi (t0 + r) (R - r) ≤ Svar phi t0 R := by
  rcases hrR.eq_or_lt with h | h
  · subst h; simp [Svar]
  · have e : R - 1 = r + (R - r - 1) := by omega
    have h1 : Svar phi t0 R = (∑ t ∈ range r, dvar phi (t0 + t))
        + ∑ t ∈ range (R - r - 1), dvar phi (t0 + r + t) := by
      unfold Svar; rw [e, sum_range_add]; simp [add_assoc]
    have h2 : Svar phi t0 r ≤ ∑ t ∈ range r, dvar phi (t0 + t) := by
      unfold Svar
      apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
      intro i _ _; exact dvar_nonneg phi _
    have h3 : Svar phi (t0 + r) (R - r) = ∑ t ∈ range (R - r - 1), dvar phi (t0 + r + t) := rfl
    linarith


/-- The rates of the window `[t0, t0 + r)`, extended constantly after the window. -/
def winPhi (phi : ℕ → Ty → ℝ) (t0 r : ℕ) : ℕ → Ty → ℝ := fun t => phi (t0 + min t (r - 1))

theorem winPhi_eq (phi : ℕ → Ty → ℝ) (t0 r t : ℕ) (ht : t < r) :
    winPhi phi t0 r t = phi (t0 + t) := by
  unfold winPhi; congr 2; omega

theorem expPayoffFrom_win {P D : Ty → Finset V} (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ)
    (π : Policy P D) (t0 r : ℕ) (h : History V Ty) (q : V → ℕ) :
    expPayoffFrom w phi π r t0 h q = expPayoff w (winPhi phi t0 r) (shiftPol π t0 h) r q := by
  have := expPayoffFrom_shift w phi π t0 h r 0 [] q
  rw [Nat.add_zero, List.append_nil] at this
  rw [this]
  unfold expPayoff
  apply expPayoffFrom_congr
  intro s _ hs
  rw [winPhi_eq phi t0 r s (by omega)]

theorem sum_win (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ) (t0 r : ℕ) :
    ∑ t ∈ range r, Wspp P D w (winPhi phi t0 r t) = ∑ t ∈ range r, Wspp P D w (phi (t0 + t)) := by
  apply sum_congr rfl
  intro t ht
  rw [winPhi_eq phi t0 r t (by simpa using ht)]

theorem win_varies (phi : ℕ → Ty → ℝ) (t0 r : ℕ) (hr : 1 ≤ r) :
    VariesSlowly (winPhi phi t0 r) r (Svar phi t0 r / ((r : ℝ) - 1)) := by
  unfold VariesSlowly
  have e : ∑ t ∈ range (r - 1), ∑ τ, |winPhi phi t0 r (t + 1) τ - winPhi phi t0 r t τ|
      = Svar phi t0 r := by
    unfold Svar dvar
    apply sum_congr rfl
    intro t ht
    have ht' : t < r - 1 := by simpa using ht
    rw [winPhi_eq phi t0 r (t + 1) (by omega), winPhi_eq phi t0 r t (by omega)]
    rfl
  rw [e]
  rcases hr.eq_or_lt with h | h
  · subst h; simp [Svar]
  · have : (0 : ℝ) < (r : ℝ) - 1 := by
      have : (2 : ℝ) ≤ r := by exact_mod_cast h
      linarith
    rw [mul_div_cancel₀ _ this.ne']

theorem win_eta_bound (S : ℝ) (hS : 0 ≤ S) (r ΔT : ℕ) (hr : 1 ≤ r) (hΔ : r = 1 ∨ r + 2 ≤ ΔT)
    (hS1 : r = 1 → S = 0) :
    S / ((r : ℝ) - 1) * (r : ℝ) * (r : ℝ) ≤ (ΔT : ℝ) * S := by
  by_cases h1 : r = 1
  · rw [hS1 h1]; simp
  have h : r + 2 ≤ ΔT := by omega
  · have hr2 : 2 ≤ r := by omega
    have hrr : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    have hpos : (0 : ℝ) < (r : ℝ) - 1 := by linarith
    have hΔr : (r : ℝ) + 2 ≤ ΔT := by exact_mod_cast h
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hpos]
    have : (r : ℝ) * r ≤ ΔT * ((r : ℝ) - 1) := by nlinarith
    nlinarith

/-- Block bound for an arbitrary policy (Propositions 1 and 4 on the window). -/
theorem blk_up (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (phi : ℕ → Ty → ℝ) (T K t0 r ΔT : ℕ) (π : Policy P D) (hr1 : 1 ≤ r) (hrT : t0 + r ≤ T)
    (hrate : ∀ t < T, IsRate (phi t)) (hΔ : r = 1 ∨ r + 2 ≤ ΔT)
    (h : History V Ty) (q : V → ℕ) (hq : q ∈ StateSpace V K) :
    expPayoffFrom w phi π r t0 h q ≤ ∑ t ∈ range r, Wspp P D w (phi (t0 + t))
      + (Fintype.card V : ℝ) * ΔT * Svar phi t0 r + (Fintype.card V : ℝ) * K := by
  have hrate' : ∀ t, IsRate (winPhi phi t0 r t) := fun t => hrate _ (by omega)
  rw [expPayoffFrom_win]
  have p1 := (MirrorBP.JEA.proposition_1 P D w hm hP hD hw (winPhi phi t0 r) K hrate').1 r
    (by omega) (shiftPol π t0 h) q hq
  have heta : 0 ≤ Svar phi t0 r / ((r : ℝ) - 1) := by
    apply div_nonneg (Svar_nonneg _ _ _)
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    linarith
  have p4 := MirrorBP.JEA.proposition_4 P D w hm hP hD hw (winPhi phi t0 r) r _ heta (by omega)
    (fun t _ => hrate' t) (win_varies phi t0 r hr1)
  rw [sum_win] at p4
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hm0 : (0 : ℝ) ≤ Fintype.card V := by positivity
  have hb := win_eta_bound (Svar phi t0 r) (Svar_nonneg _ _ _) r ΔT hr1 hΔ
    (fun h1 => by subst h1; simp [Svar])
  -- combine
  set W := Wspp P D w (phibar (winPhi phi t0 r) r)
  set E := expPayoff w (winPhi phi t0 r) (shiftPol π t0 h) r q
  set Sw := ∑ t ∈ range r, Wspp P D w (phi (t0 + t))
  set η := Svar phi t0 r / ((r : ℝ) - 1)
  set m := (Fintype.card V : ℝ)
  have q1 : E ≤ r * W + m * K := by
    rw [div_le_iff₀ hrpos] at p1
    have : (m * K / r) * r = m * K := by field_simp
    nlinarith
  have q2 : r * W ≤ Sw + m * η * r * r := by
    have := mul_le_mul_of_nonneg_left p4 hrpos.le
    have e : (r : ℝ) * (1 / r * Sw) = Sw := by field_simp
    nlinarith
  have q3 : m * η * r * r ≤ m * (ΔT * Svar phi t0 r) := by
    have := mul_le_mul_of_nonneg_left hb hm0
    linarith
  linarith


theorem shiftPol_mbp (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (f : ℝ → ℝ) (K : ℕ)
    (sel : (V → ℕ) → Ty → V × V) (hmem : ∀ q τ, (sel q τ).1 ∈ P τ ∧ (sel q τ).2 ∈ D τ)
    (t0 : ℕ) (h : History V Ty) :
    shiftPol (mbpPolicy P D w f K sel hmem) t0 h = mbpPolicy P D w f K sel hmem := rfl

theorem alphaMin_win (P D : Ty → Finset V) (phi : ℕ → Ty → ℝ) (T t0 r : ℕ) (hr1 : 1 ≤ r)
    (hrT : t0 + r ≤ T) :
    alphaMin P D phi T ≤ alphaMin P D (winPhi phi t0 r) r := by
  unfold alphaMin
  have hT : (range T).Nonempty := ⟨0, by simp; omega⟩
  have hr : (range r).Nonempty := ⟨0, by simp; omega⟩
  rw [dif_pos hT, dif_pos hr, Finset.le_inf'_iff]
  intro t _
  unfold winPhi
  exact Finset.inf'_le _ (by simp; omega)

/-- Block bound for MBP (Proposition 3 on the window). -/
theorem blk_lo (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (phi : ℕ → Ty → ℝ) (T K t0 r : ℕ) (sel : (V → ℕ) → Ty → V × V)
    (hsel : IsArgmaxSel P D w (fMBP (Fintype.card V)) K sel) (C3 c3 : ℝ) (N3 : ℕ)
    (hp3 : ∀ phi' : ℕ → Ty → ℝ, (∀ t < r, IsRate (phi' t)) → (∀ t < r, 0 < alphaConn P D (phi' t)) →
      c3 * ((Fintype.card V : ℝ) + 1 / alphaMin P D phi' r) ^ N3 ≤ (K : ℝ) →
      ∀ q' ∈ StateSpace V K,
        (1 / (r : ℝ)) * ∑ t ∈ range r, Wspp P D w (phi' t)
          - expPayoff w phi' (mbpPolicy P D w (fMBP (Fintype.card V)) K sel hsel.mem) r q' / r
          ≤ C3 * (Fintype.card V : ℝ) * ((K : ℝ) / r) + C3 * (Fintype.card V : ℝ) ^ 2 / K)
    (hr1 : 1 ≤ r) (hrT : t0 + r ≤ T) (hrate : ∀ t < T, IsRate (phi t))
    (hα : ∀ t < T, 0 < alphaConn P D (phi t))
    (hK : max c3 0 * ((Fintype.card V : ℝ) + 1 / alphaMin P D phi T) ^ N3 ≤ (K : ℝ))
    (hKpos : (0 : ℝ) < K)
    (h : History V Ty) (q : V → ℕ) (hq : q ∈ StateSpace V K) :
    ∑ t ∈ range r, Wspp P D w (phi (t0 + t)) - max C3 0 * (Fintype.card V : ℝ) * K
        - max C3 0 * (Fintype.card V : ℝ) ^ 2 * r / K
      ≤ expPayoffFrom w phi (mbpPolicy P D w (fMBP (Fintype.card V)) K sel hsel.mem) r t0 h q := by
  rw [expPayoffFrom_win, shiftPol_mbp]
  have hαT : 0 < alphaMin P D phi T := by
    unfold alphaMin
    have hT : (range T).Nonempty := ⟨0, by simp; omega⟩
    rw [dif_pos hT, Finset.lt_inf'_iff]
    intro t ht
    exact hα t (by simpa using ht)
  have hαw := alphaMin_win P D phi T t0 r hr1 hrT
  have hKw : c3 * ((Fintype.card V : ℝ) + 1 / alphaMin P D (winPhi phi t0 r) r) ^ N3 ≤ (K : ℝ) := by
    have hb : (Fintype.card V : ℝ) + 1 / alphaMin P D (winPhi phi t0 r) r
        ≤ (Fintype.card V : ℝ) + 1 / alphaMin P D phi T := by
      have := one_div_le_one_div_of_le hαT hαw
      linarith
    have hb0 : 0 ≤ (Fintype.card V : ℝ) + 1 / alphaMin P D (winPhi phi t0 r) r := by
      have : 0 < alphaMin P D (winPhi phi t0 r) r := lt_of_lt_of_le hαT hαw
      positivity
    calc c3 * ((Fintype.card V : ℝ) + 1 / alphaMin P D (winPhi phi t0 r) r) ^ N3
        ≤ max c3 0 * ((Fintype.card V : ℝ) + 1 / alphaMin P D (winPhi phi t0 r) r) ^ N3 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hb0 _)
      _ ≤ max c3 0 * ((Fintype.card V : ℝ) + 1 / alphaMin P D phi T) ^ N3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb _) (le_max_right _ _)
      _ ≤ K := hK
  have p3 := hp3 (winPhi phi t0 r) (fun t _ => hrate _ (by omega))
    (fun t _ => hα _ (by omega)) hKw q hq
  rw [sum_win] at p3
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  set E := expPayoff w (winPhi phi t0 r) (mbpPolicy P D w (fMBP (Fintype.card V)) K sel hsel.mem) r q
  set Sw := ∑ t ∈ range r, Wspp P D w (phi (t0 + t))
  set m := (Fintype.card V : ℝ)
  have hm0 : 0 ≤ m := by positivity
  have q1 : Sw - E ≤ C3 * m * K + C3 * m ^ 2 * r / K := by
    have := mul_le_mul_of_nonneg_left p3 hrpos.le
    have e1 : (r : ℝ) * (1 / r * Sw - E / r) = Sw - E := by field_simp
    have e2 : (r : ℝ) * (C3 * m * (K / r) + C3 * m ^ 2 / K) = C3 * m * K + C3 * m ^ 2 * r / K := by
      field_simp
    linarith
  have q2 : C3 * m * K + C3 * m ^ 2 * r / K ≤ max C3 0 * m * K + max C3 0 * m ^ 2 * r / K := by
    have hC := le_max_left C3 0
    have a1 : C3 * m * K ≤ max C3 0 * m * K := by
      apply mul_le_mul_of_nonneg_right _ hKpos.le
      exact mul_le_mul_of_nonneg_right hC hm0
    have a2 : C3 * m ^ 2 * r / K ≤ max C3 0 * m ^ 2 * r / K := by
      apply div_le_div_of_nonneg_right _ hKpos.le
      apply mul_le_mul_of_nonneg_right _ hrpos.le
      exact mul_le_mul_of_nonneg_right hC (by positivity)
    linarith
  linarith


theorem sum_split (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ) (t0 L R : ℕ)
    (h : L ≤ R) :
    ∑ t ∈ range R, Wspp P D w (phi (t0 + t)) = (∑ t ∈ range L, Wspp P D w (phi (t0 + t)))
      + ∑ t ∈ range (R - L), Wspp P D w (phi (t0 + L + t)) := by
  conv_lhs => rw [show R = L + (R - L) by omega]
  rw [sum_range_add]
  simp [add_assoc]

theorem count_split (R L : ℕ) (hL : 1 ≤ L) (h : L < R) :
    (((R - L : ℕ) : ℝ) / L + 1) + 1 = (R : ℝ) / L + 1 := by
  rw [Nat.cast_sub h.le]
  have : (0 : ℝ) < L := by exact_mod_cast hL
  field_simp
  ring

/-- Upper bound over a whole window, by induction on blocks of length `L`. -/
theorem up_all (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (phi : ℕ → Ty → ℝ) (T K ΔT L : ℕ) (π : Policy P D) (hL1 : 1 ≤ L)
    (hLΔ : L = 1 ∨ L + 2 ≤ ΔT) (hrate : ∀ t < T, IsRate (phi t)) :
    ∀ R t0, t0 + R ≤ T → ∀ h q, q ∈ StateSpace V K →
      expPayoffFrom w phi π R t0 h q ≤ ∑ t ∈ range R, Wspp P D w (phi (t0 + t))
        + (Fintype.card V : ℝ) * ΔT * Svar phi t0 R
        + ((R : ℝ) / L + 1) * ((Fintype.card V : ℝ) * K) := by
  intro R
  induction R using Nat.strong_induction_on with
  | _ R ih =>
  intro t0 hR h q hq
  have hm0 : (0 : ℝ) ≤ Fintype.card V := by positivity
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hΔ0 : (0 : ℝ) ≤ ΔT := by positivity
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hmK := mul_nonneg hm0 hK0
  rcases Nat.eq_zero_or_pos R with h0 | hpos
  · subst h0
    have hS := Svar_nonneg phi t0 0
    simp only [expPayoffFrom, range_zero, sum_empty, Nat.cast_zero, zero_div, zero_add, one_mul]
    nlinarith [mul_nonneg (mul_nonneg hm0 hΔ0) hS]
  by_cases hRL : R ≤ L
  · have hb := blk_up P D w hm hP hD hw phi T K t0 R ΔT π hpos hR hrate (by omega) h q hq
    have : (Fintype.card V : ℝ) * K ≤ ((R : ℝ) / L + 1) * ((Fintype.card V : ℝ) * K) := by
      have : (0 : ℝ) ≤ (R : ℝ) / L := by positivity
      nlinarith
    linarith
  · push Not at hRL
    have hsp := split_le w phi π K (R - L)
      (∑ t ∈ range (R - L), Wspp P D w (phi (t0 + L + t))
        + (Fintype.card V : ℝ) * ΔT * Svar phi (t0 + L) (R - L)
        + (((R - L : ℕ) : ℝ) / L + 1) * ((Fintype.card V : ℝ) * K))
      L t0 h q hq (fun s _ hs => hrate s (by omega))
      (fun h' q' hq' => ih (R - L) (by omega) (t0 + L) (by omega) h' q' hq')
    rw [show L + (R - L) = R by omega] at hsp
    have hb := blk_up P D w hm hP hD hw phi T K t0 L ΔT π hL1 (by omega) hrate hLΔ h q hq
    rw [sum_split P D w phi t0 L R hRL.le]
    have hS := Svar_split phi t0 L R hL1 hRL.le
    have hS' := mul_le_mul_of_nonneg_left hS (mul_nonneg hm0 hΔ0)
    have hc := count_split R L hL1 hRL
    have : ((R : ℝ) / L + 1) * ((Fintype.card V : ℝ) * K)
        = (((R - L : ℕ) : ℝ) / L + 1) * ((Fintype.card V : ℝ) * K) + (Fintype.card V : ℝ) * K := by
      rw [← hc]; ring
    nlinarith

/-- Lower bound for MBP over a whole window, by induction on blocks of length `L`. -/
theorem lo_all (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (phi : ℕ → Ty → ℝ) (T K L : ℕ) (sel : (V → ℕ) → Ty → V × V)
    (hsel : IsArgmaxSel P D w (fMBP (Fintype.card V)) K sel) (C3 c3 : ℝ) (N3 : ℕ)
    (hp3 : ∀ r : ℕ, 0 < r → ∀ phi' : ℕ → Ty → ℝ, (∀ t < r, IsRate (phi' t)) →
      (∀ t < r, 0 < alphaConn P D (phi' t)) →
      c3 * ((Fintype.card V : ℝ) + 1 / alphaMin P D phi' r) ^ N3 ≤ (K : ℝ) →
      ∀ q' ∈ StateSpace V K,
        (1 / (r : ℝ)) * ∑ t ∈ range r, Wspp P D w (phi' t)
          - expPayoff w phi' (mbpPolicy P D w (fMBP (Fintype.card V)) K sel hsel.mem) r q' / r
          ≤ C3 * (Fintype.card V : ℝ) * ((K : ℝ) / r) + C3 * (Fintype.card V : ℝ) ^ 2 / K)
    (hL1 : 1 ≤ L) (hrate : ∀ t < T, IsRate (phi t))
    (hα : ∀ t < T, 0 < alphaConn P D (phi t))
    (hK : max c3 0 * ((Fintype.card V : ℝ) + 1 / alphaMin P D phi T) ^ N3 ≤ (K : ℝ))
    (hKpos : (0 : ℝ) < K) :
    ∀ R t0, t0 + R ≤ T → ∀ h q, q ∈ StateSpace V K →
      ∑ t ∈ range R, Wspp P D w (phi (t0 + t))
          - ((R : ℝ) / L + 1) * (max C3 0 * (Fintype.card V : ℝ) * K)
          - max C3 0 * (Fintype.card V : ℝ) ^ 2 * R / K
        ≤ expPayoffFrom w phi (mbpPolicy P D w (fMBP (Fintype.card V)) K sel hsel.mem) R t0 h q := by
  intro R
  induction R using Nat.strong_induction_on with
  | _ R ih =>
  intro t0 hR h q hq
  have hm0 : (0 : ℝ) ≤ Fintype.card V := by positivity
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hC0 : 0 ≤ max C3 0 := le_max_right _ _
  have hA : 0 ≤ max C3 0 * (Fintype.card V : ℝ) * K := by positivity
  rcases Nat.eq_zero_or_pos R with h0 | hpos
  · subst h0
    simp only [expPayoffFrom, range_zero, sum_empty, Nat.cast_zero, zero_div, zero_add, one_mul,
      mul_zero, zero_div]
    linarith
  by_cases hRL : R ≤ L
  · have hb := blk_lo P D w phi T K t0 R sel hsel C3 c3 N3 (hp3 R hpos) hpos hR hrate hα hK hKpos h q hq
    have : max C3 0 * (Fintype.card V : ℝ) * K
        ≤ ((R : ℝ) / L + 1) * (max C3 0 * (Fintype.card V : ℝ) * K) := by
      have : (0 : ℝ) ≤ (R : ℝ) / L := by positivity
      nlinarith
    linarith
  · push Not at hRL
    have hsp := split_ge w phi (mbpPolicy P D w (fMBP (Fintype.card V)) K sel hsel.mem) K (R - L)
      (∑ t ∈ range (R - L), Wspp P D w (phi (t0 + L + t))
          - (((R - L : ℕ) : ℝ) / L + 1) * (max C3 0 * (Fintype.card V : ℝ) * K)
          - max C3 0 * (Fintype.card V : ℝ) ^ 2 * ((R - L : ℕ) : ℝ) / K)
      L t0 h q hq (fun s _ hs => hrate s (by omega))
      (fun h' q' hq' => ih (R - L) (by omega) (t0 + L) (by omega) h' q' hq')
    rw [show L + (R - L) = R by omega] at hsp
    have hb := blk_lo P D w phi T K t0 L sel hsel C3 c3 N3 (hp3 L hL1) hL1 (by omega) hrate hα hK
      hKpos h q hq
    rw [sum_split P D w phi t0 L R hRL.le]
    have hc := count_split R L hL1 hRL
    have e1 : ((R : ℝ) / L + 1) * (max C3 0 * (Fintype.card V : ℝ) * K)
        = (((R - L : ℕ) : ℝ) / L + 1) * (max C3 0 * (Fintype.card V : ℝ) * K)
          + max C3 0 * (Fintype.card V : ℝ) * K := by
      rw [← hc]; ring
    have e2 : max C3 0 * (Fintype.card V : ℝ) ^ 2 * R / K
        = max C3 0 * (Fintype.card V : ℝ) ^ 2 * L / K
          + max C3 0 * (Fintype.card V : ℝ) ^ 2 * ((R - L : ℕ) : ℝ) / K := by
      rw [Nat.cast_sub hRL.le]; field_simp; ring
    linarith


theorem final_arith (X Y Sw S m K T L ΔT C' η : ℝ) (hT : 0 < T) (hL : 1 ≤ L) (hLT : L ≤ T)
    (hΔL : ΔT ≤ 3 * L) (hΔ : 0 < ΔT) (hm : 0 ≤ m) (hK : 0 < K) (hC : 0 ≤ C') (hη : 0 ≤ η)
    (hS : S ≤ (T - 1) * η)
    (hX : X ≤ Sw + m * ΔT * S + (T / L + 1) * (m * K))
    (hY : Sw - (T / L + 1) * (C' * m * K) - C' * m ^ 2 * T / K ≤ Y) :
    (X - Y) / T ≤ 6 * (1 + C') * m * (K / ΔT) + 6 * (1 + C') * m ^ 2 / K + ΔT * m * η := by
  rw [div_le_iff₀ hT]
  have hLpos : 0 < L := by linarith
  have h1 : T / L + 1 ≤ 6 * T / ΔT := by
    have a : T / L + 1 ≤ 2 * T / L := by
      rw [div_add_one hLpos.ne', div_le_div_iff_of_pos_right hLpos]; linarith
    have b : 2 * T / L ≤ 6 * T / ΔT := by
      rw [div_le_div_iff₀ hLpos hΔ]; nlinarith
    linarith
  have hmK : 0 ≤ (1 + C') * (m * K) := by positivity
  have t1 : (T / L + 1) * ((1 + C') * (m * K)) ≤ 6 * T / ΔT * ((1 + C') * (m * K)) :=
    mul_le_mul_of_nonneg_right h1 hmK
  have e1 : 6 * T / ΔT * ((1 + C') * (m * K)) = 6 * (1 + C') * m * (K / ΔT) * T := by
    field_simp
  have t2 : C' * m ^ 2 * T / K ≤ 6 * (1 + C') * m ^ 2 / K * T := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hK.le
    have : 0 ≤ m ^ 2 * T := by positivity
    nlinarith
  have t3 : m * ΔT * S ≤ ΔT * m * η * T := by
    have : S ≤ T * η := by nlinarith
    have := mul_le_mul_of_nonneg_left this (mul_nonneg hm hΔ.le)
    linarith
  have e2 : (T / L + 1) * (m * K) + (T / L + 1) * (C' * m * K)
      = (T / L + 1) * ((1 + C') * (m * K)) := by ring
  have : X - Y ≤ (T / L + 1) * ((1 + C') * (m * K)) + C' * m ^ 2 * T / K + m * ΔT * S := by
    linarith
  have e3 : (6 * (1 + C') * m * (K / ΔT) + 6 * (1 + C') * m ^ 2 / K + ΔT * m * η) * T
      = 6 * (1 + C') * m * (K / ΔT) * T + 6 * (1 + C') * m ^ 2 / K * T + ΔT * m * η * T := by ring
  linarith

end MirrorBP.JEA.Prop2Aux

open Finset MirrorBP.JEA

theorem solution :
    ∃ C : ℝ, ∃ c : ℝ, ∃ N : ℕ,
      ∀ (V Ty : Type) [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
        (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ) (T : ℕ) (eta : ℝ) (K : ℕ)
        (sel : (V → ℕ) → Ty → V × V) (ΔT : ℕ),
        1 < Fintype.card V → (∀ τ, (P τ).Nonempty) → (∀ τ, (D τ).Nonempty) →
        (∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1) →
        0 < T → (∀ t < T, IsRate (phi t)) → (∀ t < T, 0 < alphaConn P D (phi t)) →
        VariesSlowly phi T eta →
        c * ((Fintype.card V : ℝ) + 1 / alphaMin P D phi T) ^ N ≤ (K : ℝ) →
        0 < ΔT → ΔT < T →
        ∀ hsel : IsArgmaxSel P D w (fMBP (Fintype.card V)) K sel,
        ∀ π : Policy P D, ∀ q ∈ StateSpace V K, ∀ q' ∈ StateSpace V K,
          (expPayoff w phi π T q
              - expPayoff w phi (mbpPolicy P D w (fMBP (Fintype.card V)) K sel hsel.mem) T q') / T
            ≤ C * (Fintype.card V : ℝ) * ((K : ℝ) / ΔT) + C * (Fintype.card V : ℝ) ^ 2 / K
              + ΔT * (Fintype.card V : ℝ) * eta := by
  obtain ⟨C3, c3, N3, h3⟩ := MirrorBP.JEA.proposition_3
  refine ⟨6 * (1 + max C3 0), max c3 1, N3, ?_⟩
  intro V Ty _ _ _ _ P D w phi T eta K sel ΔT hm hP hD hw hT hrate hα hvar hK hΔ1 hΔT hsel π q hq
    q' hq'
  have hαpos : 0 < alphaMin P D phi T := by
    unfold alphaMin
    have hne : (range T).Nonempty := ⟨0, by simp [hT]⟩
    rw [dif_pos hne, Finset.lt_inf'_iff]
    intro t ht
    exact hα t (by simpa using ht)
  have hx1 : 1 ≤ (Fintype.card V : ℝ) + 1 / alphaMin P D phi T := by
    have : 0 < 1 / alphaMin P D phi T := by positivity
    have : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hm.le
    linarith
  have hxN := one_le_pow₀ (n := N3) hx1
  have hK1 : (1 : ℝ) ≤ K := by
    have : (1 : ℝ) * 1 ≤ max c3 1 * ((Fintype.card V : ℝ) + 1 / alphaMin P D phi T) ^ N3 :=
      mul_le_mul (le_max_right _ _) hxN zero_le_one (le_trans zero_le_one (le_max_right _ _))
    linarith
  have hK0 : max c3 0 * ((Fintype.card V : ℝ) + 1 / alphaMin P D phi T) ^ N3 ≤ K :=
    le_trans (mul_le_mul_of_nonneg_right (max_le_max le_rfl zero_le_one) (by positivity)) hK
  have hKpos : (0 : ℝ) < K := by linarith
  -- the block length
  obtain ⟨L, hLdef⟩ : ∃ L, L = if 4 ≤ ΔT then ΔT - 2 else 1 := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hLdef]; split_ifs <;> omega
  have hLΔ : L = 1 ∨ L + 2 ≤ ΔT := by rw [hLdef]; split_ifs <;> omega
  have hL3 : ΔT ≤ 3 * L := by rw [hLdef]; split_ifs <;> omega
  have hLT : L ≤ T := by rw [hLdef]; split_ifs <;> omega
  have up := Prop2Aux.up_all P D w hm hP hD hw phi T K ΔT L π hL1 hLΔ hrate T 0 (by simp) [] q hq
  have lo := Prop2Aux.lo_all P D w phi T K L sel hsel C3 c3 N3
    (fun r hr phi' h1 h2 h3' q'' hq'' => h3 V Ty P D w phi' r K sel hm hP hD hw hr h1 h2 h3' hsel
      q'' hq'') hL1 hrate hα hK0 hKpos T 0 (by simp) [] q' hq'
  have hS : Prop2Aux.Svar phi 0 T ≤ ((T : ℝ) - 1) * eta := by
    have : Prop2Aux.Svar phi 0 T
        = ∑ t ∈ range (T - 1), ∑ τ, |phi (t + 1) τ - phi t τ| := by
      simp [Prop2Aux.Svar, Prop2Aux.dvar]
    rw [this]; exact hvar
  have hT2 : (2 : ℝ) ≤ T := by
    have : 2 ≤ T := by omega
    exact_mod_cast this
  have hη : 0 ≤ eta := by
    have h0 := Prop2Aux.Svar_nonneg phi 0 T
    by_contra hneg
    push Not at hneg
    have : ((T : ℝ) - 1) * eta < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
    linarith
  simp only [zero_add] at up lo
  unfold expPayoff
  exact Prop2Aux.final_arith _ _ _ _ _ _ _ _ _ _ _ (by positivity) (by exact_mod_cast hL1)
    (by exact_mod_cast hLT) (by exact_mod_cast hL3) (by exact_mod_cast hΔ1) (by positivity) hKpos
    (le_max_right _ _) hη hS up lo
