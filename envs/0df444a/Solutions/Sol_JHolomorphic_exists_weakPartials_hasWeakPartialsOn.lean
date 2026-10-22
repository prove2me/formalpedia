-- Prove2me | solution 1 for JHolomorphic.exists_weakPartials_hasWeakPartialsOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T14:24:23.208612+00:00
-- url     : https://prove2.me/submissions/93d52473-3fe9-4fdf-8ee6-20ccbacc65f8

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_local
import Theorems.Thm_JHolomorphic_exists_ball_weakPartials_hasWeakPartialsOn



namespace JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

theorem exists_weakPartials_hasWeakPartialsOn_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → E) (hu : IsWeakJHolomorphicOn p J O U u) :
    ∃ us ut uss ust uts utt : ℂ → E, HasWeakPartialsOn U u us ut ∧
      HasWeakPartialsOn U us uss ust ∧ HasWeakPartialsOn U ut uts utt ∧
      ∀ K ⊆ U, IsCompact K →
        MemLp us (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp ut (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp uss (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp ust (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp uts (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp utt (ENNReal.ofReal p) (volume.restrict K) := by
  obtain ⟨hcont, hmaps, us, ut, hw, hLp, heq⟩ := hu
  have hloc := exists_ball_weakPartials_hasWeakPartialsOn p hp J O hJ U hU u us ut hcont hmaps
    hw hLp heq
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hint : ∀ {g : ℂ → E} (K : Set ℂ), IsCompact K →
      MemLp g (ENNReal.ofReal p) (volume.restrict K) → IntegrableOn g K := by
    intro g K hK hg
    haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    exact hg.integrable hp1
  obtain ⟨uss, ust, h1, h1L⟩ := HasWeakPartialsOn.of_local hU hp1 (f := us)
    (fun K hKU hK => hint K hK (hLp K hKU hK).2.1) fun z hz => by
      obtain ⟨r, hr, hb, a, b, c, d, hs, -, ha, hb', -, -⟩ := hloc z hz
      exact ⟨ball z r, isOpen_ball, mem_ball_self hr, hb, a, b, hs, ha, hb'⟩
  obtain ⟨uts, utt, h2, h2L⟩ := HasWeakPartialsOn.of_local hU hp1 (f := ut)
    (fun K hKU hK => hint K hK (hLp K hKU hK).2.2) fun z hz => by
      obtain ⟨r, hr, hb, a, b, c, d, -, ht, -, -, hc, hd⟩ := hloc z hz
      exact ⟨ball z r, isOpen_ball, mem_ball_self hr, hb, c, d, ht, hc, hd⟩
  exact ⟨us, ut, uss, ust, uts, utt, hw, h1, h2, fun K hKU hK =>
    ⟨(hLp K hKU hK).2.1, (hLp K hKU hK).2.2, (h1L K hKU hK).1, (h1L K hKU hK).2,
      (h2L K hKU hK).1, (h2L K hKU hK).2⟩⟩

end JHolomorphic

open JHolomorphic

open MeasureTheory
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → E) (hu : IsWeakJHolomorphicOn p J O U u) :
    ∃ us ut uss ust uts utt : ℂ → E, HasWeakPartialsOn U u us ut ∧
      HasWeakPartialsOn U us uss ust ∧ HasWeakPartialsOn U ut uts utt ∧
      ∀ K ⊆ U, IsCompact K →
        MemLp us (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp ut (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp uss (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp ust (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp uts (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp utt (ENNReal.ofReal p) (volume.restrict K) :=
  exists_weakPartials_hasWeakPartialsOn_aux p hp J O hJ U hU u hu
