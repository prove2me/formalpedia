-- Prove2me | solution 1 for JHolomorphic.HasWeakPartialsOn.add
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T11:31:45.367968+00:00
-- url     : https://prove2.me/submissions/149a5821-972f-4b8b-a613-81008f759530

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_integrable_smul_of_integrableOn_compact
import Mathlib.Analysis.Calculus.FDeriv.Const



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

/-- Weak partials of a sum. -/
theorem HasWeakPartialsOn.add_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℂ} {u us ut v vs vt : ℂ → E}
    (h1 : HasWeakPartialsOn U u us ut) (h2 : HasWeakPartialsOn U v vs vt)
    (hint1 : ∀ K ⊆ U, IsCompact K → IntegrableOn u K ∧ IntegrableOn us K ∧ IntegrableOn ut K)
    (hint2 : ∀ K ⊆ U, IsCompact K → IntegrableOn v K ∧ IntegrableOn vs K ∧ IntegrableOn vt K) :
    HasWeakPartialsOn U (fun z => u z + v z) (fun z => us z + vs z) (fun z => ut z + vt z) := by
  intro φ hφ hc hsub
  obtain ⟨a1, b1⟩ := h1 φ hφ hc hsub
  obtain ⟨a2, b2⟩ := h2 φ hφ hc hsub
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_cast)
  have hd : Continuous (fderiv ℝ φ) := hφ1.continuous_fderiv one_ne_zero
  have hds : Continuous (fun z => fderiv ℝ φ z 1) := hd.clm_apply continuous_const
  have hdt : Continuous (fun z => fderiv ℝ φ z Complex.I) := hd.clm_apply continuous_const
  have hcs : HasCompactSupport (fun z => fderiv ℝ φ z 1) := hc.fderiv_apply (𝕜 := ℝ) 1
  have hct : HasCompactSupport (fun z => fderiv ℝ φ z Complex.I) :=
    hc.fderiv_apply (𝕜 := ℝ) Complex.I
  have hss : tsupport (fun z => fderiv ℝ φ z 1) ⊆ U :=
    (tsupport_fderiv_apply_subset (𝕜 := ℝ) 1).trans hsub
  have hst : tsupport (fun z => fderiv ℝ φ z Complex.I) ⊆ U :=
    (tsupport_fderiv_apply_subset (𝕜 := ℝ) Complex.I).trans hsub
  have I : ∀ (f : ℂ → E), (∀ K ⊆ U, IsCompact K → IntegrableOn f K) →
      Integrable (fun z => fderiv ℝ φ z 1 • f z) ∧
      Integrable (fun z => fderiv ℝ φ z Complex.I • f z) ∧ Integrable (fun z => φ z • f z) :=
    fun f hf =>
    ⟨integrable_smul_of_integrableOn_compact hf hds.continuousOn hcs hss,
     integrable_smul_of_integrableOn_compact hf hdt.continuousOn hct hst,
     integrable_smul_of_integrableOn_compact hf hφ.continuous.continuousOn hc hsub⟩
  have Iu := I u (fun K h1 h2 => (hint1 K h1 h2).1)
  have Ius := I us (fun K h1 h2 => (hint1 K h1 h2).2.1)
  have Iut := I ut (fun K h1 h2 => (hint1 K h1 h2).2.2)
  have Iv := I v (fun K h1 h2 => (hint2 K h1 h2).1)
  have Ivs := I vs (fun K h1 h2 => (hint2 K h1 h2).2.1)
  have Ivt := I vt (fun K h1 h2 => (hint2 K h1 h2).2.2)
  constructor
  · simp only [smul_add]
    rw [integral_add Iu.1 Iv.1, integral_add Ius.2.2 Ivs.2.2, a1, a2, neg_add]
  · simp only [smul_add]
    rw [integral_add Iu.2.1 Iv.2.1, integral_add Iut.2.2 Ivt.2.2, b1, b2, neg_add]

end JHolomorphic

open JHolomorphic JHolomorphic.HasWeakPartialsOn

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℂ} {u us ut v vs vt : ℂ → E}
    (h1 : HasWeakPartialsOn U u us ut) (h2 : HasWeakPartialsOn U v vs vt)
    (hint1 : ∀ K ⊆ U, IsCompact K → IntegrableOn u K ∧ IntegrableOn us K ∧ IntegrableOn ut K)
    (hint2 : ∀ K ⊆ U, IsCompact K → IntegrableOn v K ∧ IntegrableOn vs K ∧ IntegrableOn vt K) :
    HasWeakPartialsOn U (fun z => u z + v z) (fun z => us z + vs z) (fun z => ut z + vt z) :=
  HasWeakPartialsOn.add_aux h1 h2 hint1 hint2
