-- Prove2me | solution 1 for LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_simpleIntegral_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:15:13.361617+00:00
-- url     : https://prove2.me/submissions/99579676-0033-46c2-9f12-4b88de281703

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityLimit

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section Increments
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
/-- A Brownian increment has moments of every order. -/
theorem LevyStochCalc.Brownian.Ito.memLp_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun ω => W.W b ω - W.W a ω) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have h := (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (μ := P)
    (f := fun ω => W.W b ω - W.W a ω) (p := p)
    (by fun_prop) hmeas.aemeasurable).1
  rw [W.increment_gaussian ha hab] at h
  exact h (memLp_id_gaussianReal' p hp)
/-- A bounded random variable times a Brownian increment has moments of every order. -/
theorem LevyStochCalc.Brownian.Ito.memLp_mul_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤)
    {Y : Ω → ℝ} (hYm : Measurable Y) {C : ℝ} (hC : ∀ ω, |Y ω| ≤ C) :
    MemLp (fun ω => Y ω * (W.W b ω - W.W a ω)) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  refine MemLp.mono ((memLp_increment W ha hab p hp).const_mul C)
    (hYm.mul hmeas).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have hC0 : 0 ≤ C := (abs_nonneg (Y ω)).trans (hC ω)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hC0]
  exact mul_le_mul_of_nonneg_right (hC ω) (abs_nonneg _)
end Increments
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {d : ℕ}
section SimpleIntegrands
open LevyStochCalc.Brownian.Ito
variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
/-- Clamping an interval to `(-∞, t]` either collapses it or leaves its left endpoint alone. -/
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.min_eq_or_lt_min {p q : ℝ} (h : p < q) (t : ℝ) :
    min p t = min q t ∨ (min p t = p ∧ p < min q t) := by
  rcases lt_or_ge t q with htq | hqt
  · rcases lt_or_ge p t with hpt | htp
    · exact Or.inr ⟨min_eq_left hpt.le, by rw [min_eq_right htq.le]; exact hpt⟩
    · exact Or.inl (by rw [min_eq_right htp, min_eq_right htq.le])
  · exact Or.inr ⟨min_eq_left (h.le.trans hqt), by rw [min_eq_left hqt]; exact h⟩
end SimpleIntegrands
section L2Limit
open LevyStochCalc.Brownian.Ito
/-- An elementary integral is square-integrable at every time. -/
lemma solution (V : LevyStochCalc.Brownian.BrownianMotion P) {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T) (t : ℝ) :
    MemLp (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral V G t ω) 2 P := by
  have hnn : ∀ a : Fin G.N, 0 ≤ G.partition a.castSucc := fun a => by
    have h := G.partition_strictMono.monotone (Fin.zero_le a.castSucc)
    rwa [G.partition_zero] at h
  have hlt : ∀ a : Fin G.N, G.partition a.castSucc < G.partition a.succ := fun a =>
    G.partition_strictMono Fin.castSucc_lt_succ
  have hrw : (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral V G t ω) = fun ω => ∑ a : Fin G.N,
      G.ξ a ω * (V.W (min (G.partition a.succ) t) ω
        - V.W (min (G.partition a.castSucc) t) ω) := rfl
  rw [hrw]
  refine memLp_finsetSum (f := fun (a : Fin G.N) ω => G.ξ a ω
    * (V.W (min (G.partition a.succ) t) ω - V.W (min (G.partition a.castSucc) t) ω))
    Finset.univ fun a _ => ?_
  rcases LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.min_eq_or_lt_min (hlt a) t with hc | ⟨hpe, hplt⟩
  · have hz : (fun ω => G.ξ a ω * (V.W (min (G.partition a.succ) t) ω
        - V.W (min (G.partition a.castSucc) t) ω)) = fun _ => (0 : ℝ) := by
      funext ω; rw [hc]; ring
    rw [hz]
    exact memLp_const 0
  · obtain ⟨M, hM⟩ := G.ξ_bounded a
    rw [hpe]
    exact LevyStochCalc.Brownian.Ito.memLp_mul_increment V (hnn a) hplt 2 (by simp) (G.ξ_measurable a) hM
