-- Prove2me | solution 1 for MDPFinance.TerminalWealth.hara_utility_solution
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:44:34.139989+00:00
-- url     : https://prove2.me/submissions/d4666247-13a7-48e1-9707-6ae4e94e6ccf

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market
import Definitions.Def_MDPFinance_TerminalWealth_PowerAuxiliary

open MeasureTheory ProbabilityTheory MDPFinance.TerminalWealth

namespace HaraCex

noncomputable def UU (x : ℝ) : ℝ := (x + 1) ^ (1 / 2 : ℝ)

theorem UU_concave : StrictConcaveOn ℝ (Set.Ici (-1 : ℝ)) UU := by
  have base := Real.strictConcaveOn_rpow (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨convex_Ici _, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hx' : x + 1 ∈ Set.Ici (0 : ℝ) := by simp only [Set.mem_Ici] at hx ⊢; linarith
  have hy' : y + 1 ∈ Set.Ici (0 : ℝ) := by simp only [Set.mem_Ici] at hy ⊢; linarith
  have hxy' : x + 1 ≠ y + 1 := fun h => hxy (by linarith)
  have := base.2 hx' hy' hxy' ha hb hab
  simp only [smul_eq_mul] at this ⊢
  unfold UU
  have e : a * x + b * y + 1 = a * (x + 1) + b * (y + 1) := by
    have : a * x + b * y + (a + b) = a * (x + 1) + b * (y + 1) := by ring
    rw [hab] at this; exact this
  rw [e]
  exact this

theorem UU_mono : StrictMonoOn UU (Set.Ici (-1 : ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  exact Real.rpow_lt_rpow (by linarith) (by linarith) (by norm_num)

noncomputable def M0 : TerminalWealthMarket Unit 0 where
  measIP := Measure.dirac ()
  isProb := inferInstance
  N := 1
  i := fun _ => 1
  hi_pos := fun _ _ _ => by norm_num
  R := fun _ _ k => k.elim0
  hR_meas := fun _ _ _ => Measurable.of_discrete
  hR_indep := iIndepFun.of_subsingleton
  hNA := fun _ _ _ => by
    rintro ⟨a, _, hpos⟩
    simp at hpos
  domU := Set.Ici (-1)
  U := UU
  hU_mono := UU_mono
  hU_concave := UU_concave
  hU_cont := by
    unfold UU
    exact (Continuous.continuousOn (by fun_prop (disch := norm_num)))

theorem D_empty : M0.D 0 (-1) = ∅ := by
  ext a
  simp only [TerminalWealthMarket.D, Set.mem_empty_iff_false, iff_false]
  intro h
  change ∀ᵐ ω ∂(Measure.dirac ()), _ at h
  rw [ae_dirac_iff (by exact MeasurableSet.of_discrete)] at h
  simp [M0] at h
  norm_num at h

theorem V_bot (x : ℝ) : M0.V 0 x = ⊥ := by
  unfold TerminalWealthMarket.V
  apply iSup₂_eq_bot.mpr
  intro π hπ
  exfalso
  have := ((hπ 0 le_rfl (by show 0 < 1; norm_num)).1 (-1) (by show (-1 : ℝ) ∈ Set.Ici (-1); simp))
  rw [D_empty] at this
  exact this

end HaraCex

open HaraCex in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d) (hFM2 : M.FM2) (γ b : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hb : 0 ≤ b) (hdomU : M.domU = Set.Ici (-b))
    (hU : ∀ x, -b ≤ x → M.U x = (x + b) ^ γ)
    (En : ℕ → Set ℝ) (hEn : ∀ n, En n = {x | 0 ≤ x * M.S0 M.N / M.S0 n + b}),
    (∀ n ≤ M.N, ∀ x ∈ En n,
        M.V n x = (((∏ k ∈ Finset.Ico n M.N, M.vPower γ k) *
          (x * M.S0 M.N / M.S0 n + b) ^ γ : ℝ) : EReal)) ∧
      (∃ αstar : ℕ → (Fin d → ℝ), (∀ n < M.N, αstar n ∈ M.Afrac n ∧
          ∫ ω, (1 + ∑ k, αstar n k * M.R (n + 1) ω k) ^ γ ∂M.measIP = M.vPower γ n) ∧
        ∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x ∈ En n,
            fstar n x = fun k => αstar n k * (x + b * M.S0 n / M.S0 M.N)) ∧
          ∀ x ∈ En 0, M.Vpi fstar 0 x = M.V 0 x)) := by
  intro h
  have H := (h M0 (fun _ _ _ => by simp) (1 / 2) 1 (by norm_num) (by norm_num) zero_le_one rfl
    (fun x _ => rfl) _ (fun _ => rfl)).1 0 (Nat.zero_le _) 0 (by simp)
  rw [V_bot] at H
  exact EReal.bot_ne_coe _ H

#print axioms solution
