-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_source_clock_factorized_occupation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:57:09.112896+00:00
-- url     : https://prove2.me/submissions/765d384c-9c5a-4fab-95ce-886139e01454

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_clock_pair_product
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_infimum_probability_support
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_source_avram_infimum_cdf
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_avram_clock_survival_occupation
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Source-faithful clock-law reduction. -/
theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ q : ℝ, 0 < q →
      0 < Phi ψ q ∧
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Iio 0) = 0 ∧
        (∀ b : ℝ, 0 ≤ b → cdf ν b =
          q / Phi ψ q * W q b - q * ∫ s in (0 : ℝ)..b, W q s) ∧
        ∀ x : ℝ, 0 ≤ x → ∀ A : Set ℝ, MeasurableSet A →
          (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
            P {ω | (t : WithTop ℝ≥0) <
              tauMinus (shifted D.X x) 0 ω ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) =
          (ENNReal.ofReal q)⁻¹ *
            ((expMeasure (Phi ψ q)).prod ν)
              {z : ℝ × ℝ | z.2 ≤ x ∧ x + z.1 - z.2 ∈ A} := by
  intro Ω mΩ P hP D ψ W hψ hW q hq
  have hzero : ψ 0 = 0 := by
    simpa [SpectrallyNegativeModel.toData] using (hψ 0 1 le_rfl (by norm_num)).2
  have hroot : Phi ψ q ∈ RightRootSet ψ q := (hW q hq.le).1.2.1
  have hv : ψ (Phi ψ q) = q := hroot.2
  have hφ : 0 < Phi ψ q := by
    by_contra hn
    have he : Phi ψ q = 0 := le_antisymm (le_of_not_gt hn) hroot.1
    rw [he, hzero] at hv
    exact hq.ne hv
  obtain ⟨F, X, hpath, hpsi⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  let M := P.prod (expMeasure q)
  let I : Ω × ℝ → ℝ := fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1}
  let J : Ω × ℝ → ℝ × ℝ := fun z => (X.X z.2.toNNReal z.1 + I z, I z)
  let ν := M.map I
  obtain ⟨hν, hsupport⟩ := p2m88_avram_infimum_probability_support Ω P F X q hq
  obtain ⟨hJ, hmap⟩ := p2m88_avram_clock_pair_product Ω P F X q
    (Phi ψ q) hq hφ ((hpsi _ hφ.le).trans hv)
  refine ⟨hφ, ν, hν, hsupport, ?_, ?_⟩
  · exact p2m88_source_avram_infimum_cdf Ω P D ψ W hψ hW F X hpath q hq
  · intro x hx A hA
    have htransfer :
        (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
            shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) =
        (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted X.X x) 0 ω ∧
            shifted X.X x t ω ∈ A} ∂positiveTimeLebesgue) := by
      apply lintegral_congr
      intro t
      congr 1
      apply measure_congr
      filter_upwards [hpath] with ω hω
      change ((t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
        shifted D.X x t ω ∈ A) =
        ((t : WithTop ℝ≥0) < tauMinus (shifted X.X x) 0 ω ∧
        shifted X.X x t ω ∈ A)
      simp only [tauMinus, shifted, hω]
    rw [htransfer, p2m88_avram_clock_survival_occupation Ω P F X q x hq hx A hA]
    let B : Set (ℝ × ℝ) := {z | z.2 ≤ x ∧ x + z.1 - z.2 ∈ A}
    have hB : MeasurableSet B :=
      (measurableSet_le measurable_snd measurable_const).inter
        (((measurable_const.add measurable_fst).sub measurable_snd) hA)
    have hmass := congrArg (fun μ : Measure (ℝ × ℝ) => μ B) hmap
    rw [Measure.map_apply hJ hB] at hmass
    have hset : J ⁻¹' B = {z : Ω × ℝ | I z ≤ x ∧
        x + X.X z.2.toNNReal z.1 ∈ A} := by
      ext z
      simp only [J, B, Set.mem_preimage, Set.mem_setOf_eq, ← add_assoc,
        add_sub_cancel_right]
    rw [hset] at hmass
    exact congrArg (fun m : ℝ≥0∞ => (ENNReal.ofReal q)⁻¹ * m) hmass
