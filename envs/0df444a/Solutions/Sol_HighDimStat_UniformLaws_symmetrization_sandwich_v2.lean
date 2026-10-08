-- Prove2me | solution 1 for HighDimStat.UniformLaws.symmetrization_sandwich_v2
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:31:32.602984+00:00
-- url     : https://prove2.me/submissions/485a28ad-111d-4a63-8afd-2fb4dcdb7197

import Mathlib
import Definitions.Def_HighDimStat_UniformLaws_empProcessDeviation
import Definitions.Def_HighDimStat_UniformLaws_symmetrizedProcess

open MeasureTheory ProbabilityTheory

namespace Cex6fe9c8e5

theorem iIndepFun_fin0 {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Fin 0 → Ω → β) :
    iIndepFun g μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  have hS : S = ∅ := Subsingleton.elim _ _
  subst hS
  simp

theorem integ_unit (g : Unit → ℝ) : Integrable g (Measure.dirac ()) := by
  have hg : g = fun _ => g () := rfl
  rw [hg]
  exact integrable_const _

end Cex6fe9c8e5

open HighDimStat.UniformLaws in
theorem solution : ¬ (∀ {D ι Ω : Type} [MeasurableSpace D] [MeasurableSpace Ω]
    [Countable ι]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (f : ι → D → ℝ) (hf : ∀ j, Measurable (f j))
    (Xs : ℕ → Ω → D) (X0 : Ω → D) (eps : ℕ → Ω → ℝ) (n : ℕ)
    (hXmeas : ∀ i, Measurable (Xs i))
    (hXid : ∀ i, i < n → IdentDistrib (Xs i) X0 Prob Prob)
    (hXindep : iIndepFun (fun i : Fin n => Xs i) Prob)
    (heps_meas : ∀ i, Measurable (eps i))
    (heps_law : ∀ i, i < n →
      Prob {ω | eps i ω = 1} = 1 / 2 ∧ Prob {ω | eps i ω = -1} = 1 / 2)
    (hepsindep : iIndepFun (fun i : Fin n => eps i) Prob)
    (hXeps : IndepFun (fun ω (i : Fin n) => Xs i ω) (fun ω (i : Fin n) => eps i ω) Prob)
    (hfint : ∀ j, Integrable (fun ω => f j (X0 ω)) Prob)
    (hbdd : ∀ x, BddAbove (Set.range fun j => |f j x|))
    (hbddE : BddAbove (Set.range fun j => |∫ ω', f j (X0 ω') ∂Prob|))
    (Φ : ℝ → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦmono : Monotone Φ)
    (hInt1 : Integrable (fun ω => Φ (1 / 2 *
      symmetrizedProcess (fun j x => f j x - ∫ ω', f j (X0 ω') ∂Prob) Xs eps n ω)) Prob)
    (hInt2 : Integrable (fun ω => Φ (empProcessDeviation f Xs X0 Prob n ω)) Prob)
    (hInt3 : Integrable (fun ω => Φ (2 * symmetrizedProcess f Xs eps n ω)) Prob),
    ∫ ω, Φ (1 / 2 *
      symmetrizedProcess (fun j x => f j x - ∫ ω', f j (X0 ω') ∂Prob) Xs eps n ω) ∂Prob ≤
    ∫ ω, Φ (empProcessDeviation f Xs X0 Prob n ω) ∂Prob
    ∧
    ∫ ω, Φ (empProcessDeviation f Xs X0 Prob n ω) ∂Prob ≤
    ∫ ω, Φ (2 * symmetrizedProcess f Xs eps n ω) ∂Prob) := by
  intro h
  have key := (@h Unit Unit Unit _ _ _ (Measure.dirac ()) _ (fun _ _ => (1 : ℝ))
    (fun _ => measurable_const) (fun _ _ => ()) (fun _ => ()) (fun _ _ => (1 : ℝ)) 0
    (fun _ => measurable_const) (fun i hi => absurd hi (Nat.not_lt_zero i))
    (Cex6fe9c8e5.iIndepFun_fin0 _ _) (fun _ => measurable_const)
    (fun i hi => absurd hi (Nat.not_lt_zero i))
    (Cex6fe9c8e5.iIndepFun_fin0 _ _)
    (indepFun_const_left _ _)
    (fun _ => integrable_const _)
    (fun _ => ⟨1, by rintro _ ⟨_, rfl⟩; simp⟩)
    ⟨1, by rintro _ ⟨_, rfl⟩; simp⟩
    id (convexOn_id convex_univ) monotone_id
    (Cex6fe9c8e5.integ_unit _) (Cex6fe9c8e5.integ_unit _) (Cex6fe9c8e5.integ_unit _)).2
  simp [empProcessDeviation, symmetrizedProcess] at key
  all_goals norm_num at key
