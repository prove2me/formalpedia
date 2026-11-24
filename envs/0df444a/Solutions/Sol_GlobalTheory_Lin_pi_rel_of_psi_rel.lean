-- Prove2me | solution 1 for GlobalTheory.Lin.pi_rel_of_psi_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:12:57.801448+00:00
-- url     : https://prove2.me/submissions/aa204d1e-f1d1-4a4d-88ed-7396795c76a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
import Theorems.Thm_GlobalTheory_Lin_PsiToPi_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin
open PsiToPi
namespace GlobalTheory.Lin
theorem _root_.solution : ∀ c₂ c₃ C cS : ℝ, 0 < c₂ → 0 < c₃ → 0 < C → 0 < cS → ∃ c₂' c₃' C' : ℝ, 0 < c₂' ∧ 0 < c₃' ∧ 0 < C' ∧ ∀ (B φ β : ℝ) (θ : ℤ) (P : ℕ → Prop), 3 ≤ B → 1 ≤ φ → φ ≤ B → (θ = 0 ∨ ((θ = 1 ∨ θ = -1) ∧ 7 / 8 ≤ β ∧ cS / B ^ 3 ≤ 1 - β)) → (∀ u : ℝ, B ^ c₂ ≤ u → |φ * (∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - (u - θ * (u ^ β / β))| ≤ C * (Real.exp (-c₃ * Real.log u / Real.log B) + Real.exp (-Real.sqrt (c₃ * Real.log u))) * (u - θ * (u ^ β / β))) → ∀ X : ℝ, B ^ c₂' ≤ X → |φ * (((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ P p)).card : ℝ) - Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X| ≤ C' * (Real.exp (-c₃' * Real.log X / Real.log B) + Real.exp (-Real.sqrt (c₃' * Real.log X))) * Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X := by
  intro c₂ c₃ C cS h2 h3 hC hS
  set c := min cS 1 with hc
  have hc0 : 0 < c := lt_min hS one_pos
  set d := min (c₃ / 2) (1 / 16) with hd
  have hd0 : 0 < d := lt_min (by positivity) (by norm_num)
  have hd1 : d ≤ c₃ / 2 := min_le_left _ _
  have hd2 : d ≤ 1 / 16 := min_le_right _ _
  refine ⟨16 * (c₂ + 4 + 64 / c), d, 3 * C + 4, by positivity, hd0, by positivity, ?_⟩
  intro B φ β θ P hB hφ hφB hθ h X hX
  have hB0 : 0 < B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hlB : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hB0]; linarith [Real.exp_one_lt_d9]
  have hX1 : 1 ≤ X := le_trans (Real.one_le_rpow hB1 (by positivity)) hX
  have hX0 : 0 < X := by linarith
  obtain ⟨s, hs0, rfl⟩ : ∃ s : ℝ, 0 < s ∧ X = s ^ 16 :=
    ⟨X ^ ((16 : ℕ) : ℝ)⁻¹, by positivity, (Real.rpow_inv_natCast_pow hX0.le (by norm_num)).symm⟩
  have hs : B ^ (c₂ + 4 + 64 / c) ≤ s := by
    apply le_of_pow_le_pow_left₀ (n := 16) (by norm_num) hs0.le
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB0.le, mul_comm]
    exact_mod_cast hX
  have hs1 : 1 ≤ s := le_trans (Real.one_le_rpow hB1 (by positivity)) hs
  have hs2 : B ^ c₂ ≤ s := le_trans (Real.rpow_le_rpow_of_exponent_le hB1 (by
    have : 0 < 64 / c := by positivity
    linarith)) hs
  have hs3 : 64 * B ≤ c / B ^ 3 * s := by
    have a1 : B ^ (4 + 64 / c) ≤ s := le_trans (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)) hs
    have a2 : 64 / c ≤ B ^ (64 / c) := by
      rw [Real.rpow_def_of_pos hB0]
      have := Real.add_one_le_exp (Real.log B * (64 / c))
      have : 0 < 64 / c := by positivity
      nlinarith
    rw [Real.rpow_add hB0, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at a1
    have a3 : B ^ 4 * (64 / c) ≤ s := le_trans (by gcongr) a1
    calc 64 * B = c / B ^ 3 * (B ^ 4 * (64 / c)) := by field_simp
      _ ≤ _ := by gcongr
  have hls : 0 ≤ Real.log s := Real.log_nonneg hs1
  set e := Real.exp (-d * Real.log (s ^ 16) / Real.log B) + Real.exp (-Real.sqrt (d * Real.log (s ^ 16))) with he
  have he0 : 0 < e := by positivity
  have herr : ∀ u ∈ Set.Icc (s ^ 8) (s ^ 16),
      Real.exp (-c₃ * Real.log u / Real.log B) + Real.exp (-Real.sqrt (c₃ * Real.log u)) ≤ e := by
    intro u hu
    have a1 : d * Real.log (s ^ 16) ≤ c₃ * Real.log u := by
      have := Real.log_le_log (by positivity) hu.1
      rw [Real.log_pow] at this ⊢
      push_cast at this ⊢
      nlinarith
    refine add_le_add (Real.exp_le_exp.2 ?_) (Real.exp_le_exp.2 (neg_le_neg (Real.sqrt_le_sqrt a1)))
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hse : 1 / s ≤ e := by
    have a1 : 1 / s ≤ Real.exp (-d * Real.log (s ^ 16) / Real.log B) := by
      rw [one_div, ← Real.exp_log hs0, ← Real.exp_neg, Real.exp_log hs0]
      apply Real.exp_le_exp.2
      rw [le_div_iff₀ (by linarith), Real.log_pow]
      push_cast
      nlinarith
    exact a1.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  have key : ∀ β' : ℝ, (θ = 0 ∨ θ = 1 ∨ θ = -1) → 7 / 8 ≤ β' → c / B ^ 3 ≤ 1 - β' →
      (∀ u, mainPsi θ β' u = u - θ * (u ^ β / β)) →
      |φ * cnt P (s ^ 16) - Formalism.HermitianLattices.GL2PrimeSums.Emain θ β' (s ^ 16)| ≤ (3 * C + 4) * e * Formalism.HermitianLattices.GL2PrimeSums.Emain θ β' (s ^ 16) := by
    intro β' t1 t2 t3 t4
    have hY : s ≤ s ^ 8 := le_self_pow₀ hs1 (by norm_num)
    obtain ⟨r1, r2⟩ := step P (ρ := C * e) t1 t2 (by positivity) t3 hB (by linarith) hφB (by positivity) hs3 (fun u hu => by
      have hh := h u (by linarith [hu.1])
      rw [← t4 u] at hh
      have h0 : 0 ≤ mainPsi θ β' u := (mul_nonneg_iff_of_pos_left (by positivity)).1 (le_trans (abs_nonneg _) hh)
      exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (herr u hu) hC.le) h0))
    refine r2.trans (mul_le_mul_of_nonneg_right ?_ r1)
    rw [show 4 / s = 4 * (1 / s) by ring]
    linarith
  rcases hθ with rfl | ⟨t1, t2, t3⟩
  · have := key (7 / 8) (Or.inl rfl) le_rfl (by
      rw [div_le_iff₀ (by positivity)]
      have a1 : (3 : ℝ) ^ 3 ≤ B ^ 3 := by gcongr
      have a2 : c ≤ 1 := min_le_right _ _
      linarith) (fun u => by simp [mainPsi])
    simpa [Formalism.HermitianLattices.GL2PrimeSums.Emain, cnt] using this
  · exact key β (Or.inr t1) t2 (le_trans (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) t3)
      (fun u => rfl)
end GlobalTheory.Lin
