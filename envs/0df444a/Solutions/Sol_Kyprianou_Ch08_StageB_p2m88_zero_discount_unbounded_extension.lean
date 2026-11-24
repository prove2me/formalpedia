-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_zero_discount_unbounded_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:47:08.829988+00:00
-- url     : https://prove2.me/submissions/b59f996f-31f1-441e-9687-433a726a10be

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_source_occupation_sections_measurable
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal
/-- Zero-discount convergence. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W → ∀ x : ℝ, 0 ≤ x →
      ∀ A : Set ℝ, MeasurableSet A →
      (∀ n : ℕ, ((volume.restrict (Ici (0 : ℝ))).withDensity (fun y : ℝ => ENNReal.ofReal (killedHalflineDensity ψ 0 (W 0) x y))) (A ∩ Iic (n : ℝ)) =
        ∫⁻ t : ℝ≥0, P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
          shifted D.X x t ω ∈ A ∩ Iic (n : ℝ)} ∂positiveTimeLebesgue) →
      ((volume.restrict (Ici (0 : ℝ))).withDensity (fun y : ℝ => ENNReal.ofReal (killedHalflineDensity ψ 0 (W 0) x y))) A =
      ∫⁻ t : ℝ≥0, P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
        shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
  intro Ω mΩ P hP D ψ W hψ hW x hx A hA hbound
  let B : ℕ → Set ℝ := fun n => A ∩ Iic (n : ℝ)
  let m := (volume.restrict (Ici (0 : ℝ))).withDensity
    (fun y : ℝ => ENNReal.ofReal (killedHalflineDensity ψ 0 (W 0) x y))
  let E (S : Set ℝ) (t : ℝ≥0) : Set Ω :=
    {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧ shifted D.X x t ω ∈ S}
  let f (n : ℕ) (t : ℝ≥0) := P (E (B n) t)
  have hBmono : Monotone B := by
    intro i j hij y hy
    have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact ⟨hy.1, le_trans (Set.mem_Iic.mp hy.2) hcast⟩
  have hBunion : (⋃ n, B n) = A := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := mem_iUnion.mp hy
      exact hn.1
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_ge y
      exact mem_iUnion.mpr ⟨n, hy, hn⟩
  have hEmono (t : ℝ≥0) : Monotone (fun n => E (B n) t) :=
    fun _ _ hij _ hy => ⟨hy.1, hBmono hij hy.2⟩
  have hEunion (t : ℝ≥0) : (⋃ n, E (B n) t) = E A t := by
    ext ω
    constructor
    · intro h
      obtain ⟨n, hn⟩ := mem_iUnion.mp h
      exact ⟨hn.1, hn.2.1⟩
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_ge (shifted D.X x t ω)
      exact mem_iUnion.mpr ⟨n, h.1, h.2, hn⟩
  have hf (n : ℕ) : Measurable (f n) :=
    p2m88_source_occupation_sections_measurable Ω P D ψ hψ x hx (B n) (hA.inter measurableSet_Iic)
  have hfm : Monotone f := fun i j hij t => measure_mono (hEmono t hij)
  change m A = ∫⁻ t, P (E A t) ∂positiveTimeLebesgue
  calc
    m A = m (⋃ n, B n) := congrArg m hBunion.symm
    _ = ⨆ n, m (B n) := hBmono.measure_iUnion
    _ = ⨆ n, ∫⁻ t, f n t ∂positiveTimeLebesgue := by
      congr 1
      funext n
      exact hbound n
    _ = ∫⁻ t, ⨆ n, f n t ∂positiveTimeLebesgue := (lintegral_iSup hf hfm).symm
    _ = _ := by
      apply lintegral_congr
      intro t
      rw [← hEunion t, (hEmono t).measure_iUnion]
