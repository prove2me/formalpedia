-- Prove2me | solution 1 for JHolomorphic.HasWeakPartialsOn.prodMk
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T13:56:00.73399+00:00
-- url     : https://prove2.me/submissions/c9e47dee-3927-43e2-93d2-1d7da8c3b292

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Theorems.Thm_JHolomorphic_fderiv_apply_isTestFunction
import Theorems.Thm_JHolomorphic_integrable_smul_of_integrableOn_compact



namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

/-- Weak partial derivatives of a pair are the pairs of weak partial derivatives. -/
theorem HasWeakPartialsOn.prodMk_aux {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set ℂ} {u us ut : ℂ → E} {v vs vt : ℂ → F}
    (h1 : HasWeakPartialsOn U u us ut) (h2 : HasWeakPartialsOn U v vs vt)
    (hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn u K ∧ IntegrableOn us K ∧ IntegrableOn ut K ∧
        IntegrableOn v K ∧ IntegrableOn vs K ∧ IntegrableOn vt K) :
    HasWeakPartialsOn U (fun z => (u z, v z)) (fun z => (us z, vs z)) (fun z => (ut z, vt z)) := by
  intro φ hφ hφc hφU
  obtain ⟨a1, a2⟩ := h1 φ hφ hφc hφU
  obtain ⟨b1, b2⟩ := h2 φ hφ hφc hφU
  obtain ⟨hd1, hc1, hU1⟩ := fderiv_apply_isTestFunction hφ hφc hφU 1
  obtain ⟨hdI, hcI, hUI⟩ := fderiv_apply_isTestFunction hφ hφc hφU Complex.I
  have iu := fun g (hg : ContDiff ℝ ∞ g) hgc hgU => integrable_smul_of_integrableOn_compact
    (f := u) (fun K hKU hK => (hint K hKU hK).1) hg.continuous.continuousOn hgc hgU
  have ius := fun g (hg : ContDiff ℝ ∞ g) hgc hgU => integrable_smul_of_integrableOn_compact
    (f := us) (fun K hKU hK => (hint K hKU hK).2.1) hg.continuous.continuousOn hgc hgU
  have iut := fun g (hg : ContDiff ℝ ∞ g) hgc hgU => integrable_smul_of_integrableOn_compact
    (f := ut) (fun K hKU hK => (hint K hKU hK).2.2.1) hg.continuous.continuousOn hgc hgU
  have iv := fun g (hg : ContDiff ℝ ∞ g) hgc hgU => integrable_smul_of_integrableOn_compact
    (f := v) (fun K hKU hK => (hint K hKU hK).2.2.2.1) hg.continuous.continuousOn hgc hgU
  have ivs := fun g (hg : ContDiff ℝ ∞ g) hgc hgU => integrable_smul_of_integrableOn_compact
    (f := vs) (fun K hKU hK => (hint K hKU hK).2.2.2.2.1) hg.continuous.continuousOn hgc hgU
  have ivt := fun g (hg : ContDiff ℝ ∞ g) hgc hgU => integrable_smul_of_integrableOn_compact
    (f := vt) (fun K hKU hK => (hint K hKU hK).2.2.2.2.2) hg.continuous.continuousOn hgc hgU
  simp only [Prod.smul_mk]
  refine ⟨?_, ?_⟩
  · rw [integral_pair (iu _ hd1 hc1 hU1) (iv _ hd1 hc1 hU1),
      integral_pair (ius _ hφ hφc hφU) (ivs _ hφ hφc hφU), a1, b1, Prod.neg_mk]
  · rw [integral_pair (iu _ hdI hcI hUI) (iv _ hdI hcI hUI),
      integral_pair (iut _ hφ hφc hφU) (ivt _ hφ hφc hφU), a2, b2, Prod.neg_mk]

end JHolomorphic

open JHolomorphic JHolomorphic.HasWeakPartialsOn

open MeasureTheory Filter Topology
open scoped ContDiff

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set ℂ} {u us ut : ℂ → E} {v vs vt : ℂ → F}
    (h1 : HasWeakPartialsOn U u us ut) (h2 : HasWeakPartialsOn U v vs vt)
    (hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn u K ∧ IntegrableOn us K ∧ IntegrableOn ut K ∧
        IntegrableOn v K ∧ IntegrableOn vs K ∧ IntegrableOn vt K) :
    HasWeakPartialsOn U (fun z => (u z, v z)) (fun z => (us z, vs z)) (fun z => (ut z, vt z)) :=
  HasWeakPartialsOn.prodMk_aux h1 h2 hint
