-- Prove2me | solution 1 for MDPFinance.TerminalWealth.zero_mean_invest_in_bond
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:43:49.166079+00:00
-- url     : https://prove2.me/submissions/a6b536b5-0d1d-47fa-8af7-ab83704e6a00

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market

open MeasureTheory ProbabilityTheory MDPFinance.TerminalWealth

namespace ZeroMeanCex

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
  domU := {1}
  U := fun _ => 0
  hU_mono := fun x hx y hy hxy => by
    rw [Set.mem_singleton_iff] at hx hy
    subst hx hy
    exact absurd hxy (lt_irrefl _)
  hU_concave := ⟨convex_singleton 1, fun x hx y hy hxy => by
    rw [Set.mem_singleton_iff] at hx hy
    subst hx hy
    exact absurd rfl hxy⟩
  hU_cont := continuousOn_const

theorem D_empty : M0.D 0 1 = ∅ := by
  ext a
  simp only [TerminalWealthMarket.D, Set.mem_empty_iff_false, iff_false]
  intro h
  change ∀ᵐ ω ∂(Measure.dirac ()), _ at h
  rw [ae_dirac_iff (by exact MeasurableSet.of_discrete)] at h
  simp [M0] at h

theorem V_bot : M0.V 0 1 = ⊥ := by
  unfold TerminalWealthMarket.V
  apply iSup₂_eq_bot.mpr
  intro π hπ
  exfalso
  have := ((hπ 0 le_rfl (by show 0 < 1; norm_num)).1 1 rfl)
  rw [D_empty] at this
  exact this

end ZeroMeanCex

open ZeroMeanCex in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d) (hFM2 : M.FM2)
    (hR_zero_mean : ∀ n, 1 ≤ n → n ≤ M.N → ∀ k, ∫ ω, M.R n ω k ∂M.measIP = 0),
    (∀ n ≤ M.N, ∀ x ∈ M.domU, M.V n x = (M.U (x * M.S0 M.N / M.S0 n) : EReal)) ∧
      (∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
        (∀ n < M.N, ∀ x, fstar n x = 0) ∧
        ∀ x ∈ M.domU, M.Vpi fstar 0 x = M.V 0 x)) := by
  intro h
  have H := (h M0 (fun _ _ _ => by simp) (fun _ _ _ k => k.elim0)).1 0 (Nat.zero_le _) 1 rfl
  rw [V_bot] at H
  exact EReal.bot_ne_coe _ H

#print axioms solution
