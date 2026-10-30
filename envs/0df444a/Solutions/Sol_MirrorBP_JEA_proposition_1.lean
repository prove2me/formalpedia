-- Prove2me | solution 1 for MirrorBP.JEA.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T17:50:20.587491+00:00
-- url     : https://prove2.me/submissions/721d5f14-7e28-4274-aadc-f4896d373d70

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_SPP
import Theorems.Thm_MirrorBP_JEA_lemma_4
import Theorems.Thm_MirrorBP_JEA_lemma_6

namespace MirrorBP.JEA.Prop1Aux

open Finset MirrorBP.JEA

/-- The per-period payoff is at most one in absolute value, so the expected payoff over `n`
periods is at most `n` in absolute value. -/
theorem abs_expPayoffFrom_le {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (phi : ℕ → Ty → ℝ) (π : Policy P D) :
    ∀ n t h q, (∀ s, t ≤ s → s < t + n → IsRate (phi s)) →
      |expPayoffFrom w phi π n t h q| ≤ n := by
  intro n
  induction n with
  | zero => intro t h q _; simp [expPayoffFrom]
  | succ n ih =>
    intro t h q hr
    rw [expPayoffFrom]
    have hrt := hr t le_rfl (by omega)
    have key : ∀ τ, |∑ d, π.act t h q τ d *
        (pay w τ d + expPayoffFrom w phi π n (t + 1) (h ++ [(q, τ, d)]) (step q d))|
          ≤ ((n : ℝ) + 1) := by
      intro τ
      calc _ ≤ ∑ d, |π.act t h q τ d *
            (pay w τ d + expPayoffFrom w phi π n (t + 1) (h ++ [(q, τ, d)]) (step q d))| :=
              abs_sum_le_sum_abs _ _
        _ ≤ ∑ d, π.act t h q τ d * ((n : ℝ) + 1) := by
          apply sum_le_sum
          intro d _
          rw [abs_mul, abs_of_nonneg (π.nonneg _ _ _ _ _)]
          by_cases hf : Feasible P D τ q d
          · apply mul_le_mul_of_nonneg_left _ (π.nonneg _ _ _ _ _)
            have hp : |pay w τ d| ≤ 1 := by
              rcases d with _ | ⟨j, k⟩
              · simp [pay]
              · exact hw τ j hf.1 k hf.2.1
            have he := ih (t + 1) (h ++ [(q, τ, d)]) (step q d)
              (fun s hs1 hs2 => hr s (by omega) (by omega))
            calc _ ≤ |pay w τ d| + |expPayoffFrom w phi π n (t + 1) (h ++ [(q, τ, d)]) (step q d)| :=
                  abs_add_le _ _
              _ ≤ 1 + n := add_le_add hp he
              _ = n + 1 := by ring
          · rw [π.feasible _ _ _ _ _ hf]; simp
        _ = (n : ℝ) + 1 := by rw [← sum_mul, π.sum_one, one_mul]
    push_cast
    calc _ ≤ ∑ τ, |phi t τ * ∑ d, π.act t h q τ d *
          (pay w τ d + expPayoffFrom w phi π n (t + 1) (h ++ [(q, τ, d)]) (step q d))| :=
            abs_sum_le_sum_abs _ _
      _ ≤ ∑ τ, phi t τ * ((n : ℝ) + 1) := by
          apply sum_le_sum
          intro τ _
          rw [abs_mul, abs_of_nonneg (hrt.1 τ)]
          exact mul_le_mul_of_nonneg_left (key τ) (hrt.1 τ)
      _ = (n : ℝ) + 1 := by rw [← sum_mul, hrt.2, one_mul]



theorem phibar_rate {Ty : Type} [Fintype Ty] (phi : ℕ → Ty → ℝ) (T : ℕ) (hT : 0 < T)
    (hrate : ∀ t, IsRate (phi t)) : IsRate (phibar phi T) := by
  constructor
  · intro τ
    unfold phibar
    exact mul_nonneg (by positivity) (sum_nonneg fun t _ => (hrate t).1 τ)
  · unfold phibar
    rw [← mul_sum, sum_comm]
    simp only [(hrate _).2, sum_const, card_range, nsmul_eq_mul, mul_one]
    have : (0 : ℝ) < T := by exact_mod_cast hT
    field_simp

theorem sppObj_le {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1) (φ : Ty → ℝ) (hφ : IsRate φ)
    (x : V → Ty → V → ℝ) (hx : sppFeasX P D φ x) : sppObjX P D w φ x ≤ 1 := by
  unfold sppObjX
  calc ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, w j τ k * φ τ * x j τ k
      ≤ ∑ τ, φ τ * ∑ j ∈ P τ, ∑ k ∈ D τ, x j τ k := by
        apply sum_le_sum; intro τ _
        rw [mul_sum]
        apply sum_le_sum; intro j hj
        rw [mul_sum]
        apply sum_le_sum; intro k hk
        have h1 : w j τ k ≤ 1 := le_trans (le_abs_self _) (hw τ j hj k hk)
        have h2 : 0 ≤ φ τ * x j τ k := mul_nonneg (hφ.1 τ) (hx.2.2 τ j hj k hk)
        nlinarith
    _ ≤ ∑ τ, φ τ * 1 := by
        apply sum_le_sum; intro τ _
        exact mul_le_mul_of_nonneg_left (hx.2.1 τ) (hφ.1 τ)
    _ = 1 := by simp [hφ.2]

theorem Wspp_bounds {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1) (φ : Ty → ℝ) (hφ : IsRate φ) :
    0 ≤ Wspp P D w φ ∧ Wspp P D w φ ≤ 1 := by
  have hfeas0 : sppFeasX P D φ (fun _ _ _ => 0) := by
    refine ⟨fun i => by simp [netOut], fun τ => by simp, fun τ j _ k _ => le_rfl⟩
  have hne : (sppObjX P D w φ '' {x | sppFeasX P D φ x}).Nonempty :=
    ⟨_, ⟨_, hfeas0, rfl⟩⟩
  have hbdd : BddAbove (sppObjX P D w φ '' {x | sppFeasX P D φ x}) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact sppObj_le P D w hw φ hφ x hx
  constructor
  · have : sppObjX P D w φ (fun _ _ _ => 0) = 0 := by simp [sppObjX]
    unfold Wspp
    rw [← this]
    exact le_csSup hbdd ⟨_, hfeas0, rfl⟩
  · unfold Wspp
    apply csSup_le hne
    rintro _ ⟨x, hx, rfl⟩
    exact sppObj_le P D w hw φ hφ x hx

/-- The policy that drops every customer. -/
def dropPol {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) : Policy P D where
  act _ _ _ _ d := if d = none then 1 else 0
  nonneg _ _ _ _ d := by split_ifs <;> norm_num
  sum_one _ _ _ _ := by simp
  feasible _ _ q τ d hd := by
    rw [if_neg]
    rintro rfl
    exact hd trivial

end MirrorBP.JEA.Prop1Aux

open Finset MirrorBP.JEA Filter

theorem solution {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (phi : ℕ → Ty → ℝ) (K : ℕ) (hrate : ∀ t, IsRate (phi t)) :
    (∀ T : ℕ, 0 < T → ∀ π : Policy P D, ∀ q ∈ StateSpace V K,
        expPayoff w phi π T q / T ≤ Wspp P D w (phibar phi T) + (Fintype.card V : ℝ) * K / T) ∧
      Wstar P D w phi K ≤ Filter.limsup (fun T : ℕ => Wspp P D w (phibar phi T)) Filter.atTop := by
  have part1 : ∀ T : ℕ, 0 < T → ∀ π : Policy P D, ∀ q ∈ StateSpace V K,
      expPayoff w phi π T q / T ≤ Wspp P D w (phibar phi T) + (Fintype.card V : ℝ) * K / T := by
    intro T hT π q hq
    have h4 := MirrorBP.JEA.lemma_4 P D w hm hP hD hw phi T K hT (fun t _ => hrate t) π q hq
    have h6 := MirrorBP.JEA.lemma_6 P D w hm hP hD hw (phibar phi T)
      (Prop1Aux.phibar_rate phi T hT hrate).1 ((K : ℝ) / T) (by positivity)
    have : (Fintype.card V : ℝ) * (K / T) = (Fintype.card V : ℝ) * K / T := by ring
    linarith
  refine ⟨part1, ?_⟩
  -- the set defining W*_T
  have hV : 0 < Fintype.card V := by omega
  obtain ⟨j0⟩ : Nonempty V := Fintype.card_pos_iff.mp hV
  have hq0 : (Pi.single j0 K : V → ℕ) ∈ StateSpace V K := by
    simp [StateSpace, Finset.sum_pi_single']
  set m : ℝ := (Fintype.card V : ℝ)
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hbdd : ∀ T : ℕ, 0 < T → BddAbove
      {x | ∃ π : Policy P D, ∃ q ∈ StateSpace V K, x = expPayoff w phi π T q / T} := by
    intro T hT
    refine ⟨Wspp P D w (phibar phi T) + m * K / T, ?_⟩
    rintro _ ⟨π, q, hq, rfl⟩
    exact part1 T hT π q hq
  have hne : ∀ T : ℕ,
      {x | ∃ π : Policy P D, ∃ q ∈ StateSpace V K, x = expPayoff w phi π T q / T}.Nonempty :=
    fun T => ⟨_, Prop1Aux.dropPol P D, _, hq0, rfl⟩
  have hu_le : ∀ T : ℕ, 0 < T → WstarT P D w phi K T ≤ Wspp P D w (phibar phi T) + m * K / T := by
    intro T hT
    unfold WstarT
    apply csSup_le (hne T)
    rintro _ ⟨π, q, hq, rfl⟩
    exact part1 T hT π q hq
  have hu_ge : ∀ T : ℕ, 0 < T → -1 ≤ WstarT P D w phi K T := by
    intro T hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    have hab := Prop1Aux.abs_expPayoffFrom_le P D w hw phi (Prop1Aux.dropPol P D) T 0 [] (Pi.single j0 K)
      (fun s _ _ => hrate s)
    have h1 : -1 ≤ expPayoff w phi (Prop1Aux.dropPol P D) T (Pi.single j0 K) / T := by
      rw [le_div_iff₀ hTpos]
      have := (abs_le.mp hab).1
      unfold expPayoff
      linarith
    exact le_trans h1 (le_csSup (hbdd T hT) ⟨_, _, hq0, rfl⟩)
  have hv : ∀ T : ℕ, 0 < T → 0 ≤ Wspp P D w (phibar phi T) ∧ Wspp P D w (phibar phi T) ≤ 1 :=
    fun T hT => Prop1Aux.Wspp_bounds P D w hw _ (Prop1Aux.phibar_rate phi T hT hrate)
  have hε : ∀ T : ℕ, 0 < T → m * K / T ≤ m * K := by
    intro T hT
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    exact div_le_self (by positivity) this
  have ev : ∀ᶠ T : ℕ in atTop, 0 < T := eventually_atTop.2 ⟨1, fun T hT => hT⟩
  have hlimε : limsup (fun T : ℕ => m * K / T) atTop = 0 :=
    (tendsto_const_div_atTop_nhds_zero_nat (m * K)).limsup_eq
  unfold Wstar
  calc limsup (fun T : ℕ => WstarT P D w phi K T) atTop
      ≤ limsup (fun T : ℕ => Wspp P D w (phibar phi T) + m * K / T) atTop := by
        refine limsup_le_limsup (ev.mono hu_le) ?_ ?_
        · exact isCoboundedUnder_le_of_eventually_le _ (ev.mono hu_ge)
        · refine isBoundedUnder_of_eventually_le (a := 1 + m * K) (ev.mono fun T hT => ?_)
          have := (hv T hT).2
          have := hε T hT
          linarith
    _ ≤ limsup (fun T : ℕ => Wspp P D w (phibar phi T)) atTop
          + limsup (fun T : ℕ => m * K / T) atTop := by
        refine limsup_add_le ?_ ?_ ?_ ?_
        · exact isBoundedUnder_of_eventually_ge (a := 0) (ev.mono fun T hT => (hv T hT).1)
        · exact isBoundedUnder_of_eventually_le (a := 1) (ev.mono fun T hT => (hv T hT).2)
        · exact isCoboundedUnder_le_of_le _ (fun T => by positivity)
        · exact isBoundedUnder_of_eventually_le (a := m * K) (ev.mono hε)
    _ = limsup (fun T : ℕ => Wspp P D w (phibar phi T)) atTop := by rw [hlimε, add_zero]
