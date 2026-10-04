-- Prove2me | solution 1 for MDPFinance.FinancialMarkets.no_arbitrage_iff_local
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:27:05.226906+00:00
-- url     : https://prove2.me/submissions/393f7a54-fd0f-49bb-aa90-a2fd7a990036

import Mathlib
import Definitions.Def_MDPFinance_FinancialMarkets_DiscreteMarket
import Definitions.Def_MDPFinance_FinancialMarkets_Portfolio
import Definitions.Def_MDPFinance_FinancialMarkets_Arbitrage

open MeasureTheory ProbabilityTheory MDPFinance.FinancialMarkets

namespace NACex

noncomputable def M0 : DiscreteFinancialMarket Unit 1 where
  measIP := Measure.dirac ()
  isProb := inferInstance
  N := 0
  Fam := fun _ => ⊥
  hFam_mono := fun _ _ _ => le_rfl
  hFam_le := fun _ => bot_le
  hFam0_trivial := fun s hs => MeasurableSpace.measurableSet_bot_iff.mp hs
  i := fun _ => 1
  hi_pos := fun n h1 h2 => absurd (le_trans h1 h2) (by norm_num)
  Rtilde := fun _ _ _ => 1
  hRtilde_adapted := fun n h1 h2 => absurd (le_trans h1 h2) (by norm_num)
  hRtilde_pos := fun n h1 h2 => absurd (le_trans h1 h2) (by norm_num)

def φa : Portfolio M0 where
  φ0 := fun _ _ => 1
  φ := fun _ _ _ => -1
  hφ0_adapted := fun n hn => absurd hn (Nat.not_lt_zero n)
  hφ_adapted := fun n hn => absurd hn (Nat.not_lt_zero n)

theorem arb : IsArbitrageOpportunity φa := by
  refine ⟨fun n h1 h2 => absurd (le_trans h1 h2) (by show ¬ (1 ≤ 0 - 1); norm_num), ?_, ?_, ?_⟩
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    simp [Portfolio.X0, φa]
  · have : {ω : Unit | 0 ≤ φa.Xminus M0.N ω} = Set.univ := by
      ext ω
      simp [Portfolio.Xminus, φa, M0]
    rw [this]
    simp [M0]
  · have : {ω : Unit | 0 < φa.Xminus M0.N ω} = Set.univ := by
      ext ω
      simp [Portfolio.Xminus, φa, M0]
    rw [this]
    simp [M0]

end NACex

open NACex in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
    (M : DiscreteFinancialMarket Ω d),
    NoArbitrage M ↔
      ∀ n < M.N, ∀ φn : Ω → (Fin d → ℝ), (@Measurable Ω (Fin d → ℝ) (M.Fam n) _ φn) →
        (M.measIP {ω | 0 ≤ ∑ k, φn ω k * M.R (n + 1) ω k} = 1 →
          M.measIP {ω | ∑ k, φn ω k * M.R (n + 1) ω k = 0} = 1)) := by
  intro h
  have := (h M0).mpr (fun n hn => absurd hn (Nat.not_lt_zero n))
  exact this ⟨φa, arb⟩

#print axioms solution
