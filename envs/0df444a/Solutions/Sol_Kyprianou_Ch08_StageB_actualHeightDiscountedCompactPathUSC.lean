-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actualHeightDiscountedCompactPathUSC
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:11:16.85036+00:00
-- url     : https://prove2.me/submissions/4b5c1138-bf19-4b7f-8981-838da7f2acad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Order.LeftRight
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
import Theorems.Thm_Kyprianou_Ch08_StageB_sourceReflectedPathRegularityAE
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal

private theorem compactAux {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (q : ℝ) :
  ∀ᵐ ω ∂P, discountedAt q (tauPlus D.X 1 ω) ≠ 0 → ∃ ζ : ℝ≥0, 0 < ζ ∧ tauPlus D.X 1 ω = (ζ : WithTop ℝ≥0) ∧ UpperSemicontinuousOn (fun t : ℝ≥0 => reflectAtSup D.X 0 t ω) (Icc 0 ζ) ∧ reflectAtSup D.X 0 0 ω = 0 ∧ reflectAtSup D.X 0 ζ ω = 0 := by
  filter_upwards [D.levy.cadlag_ae, sourceReflectedPathRegularityAE P D] with ω hc hreg
  intro hdisc
  have hX0 : D.X 0 ω = 0 := by simpa using congrFun D.levy.start_zero ω
  let S : Set (WithTop ℝ≥0) := {s | ∃ u : ℝ≥0, 0 < u ∧ (u : WithTop ℝ≥0) = s ∧ 1 < D.X u ω}
  have hτS : tauPlus D.X 1 ω = sInf S := rfl
  let M : ℝ≥0 → ℝ := fun t => runningSup D.X t ω
  have hbdd (T : ℝ≥0) : BddAbove {z : ℝ | ∃ u : ℝ≥0, u ≤ T ∧ z = D.X u ω} := Kyprianou.Ch01.cadlag_runningSup_bddAbove (fun s => D.X s ω) hc T
  have hMnonneg (T : ℝ≥0) : 0 ≤ M T := by dsimp [M]; rw [runningSup]; exact le_csSup (hbdd T) ⟨0, zero_le, hX0.symm⟩
  have hdom (T : ℝ≥0) : D.X T ω ≤ M T := by dsimp [M]; rw [runningSup]; exact le_csSup (hbdd T) ⟨T, le_rfl, rfl⟩
  have hfun : ∀ s : ℝ≥0, reflectAtSup D.X 0 s ω = M s - D.X s ω := by intro s; simp [M, reflectAtSup, max_eq_right (hMnonneg s)]
  have hright0 : Tendsto (fun s : ℝ≥0 => D.X s ω) (𝓝 (0 : ℝ≥0)) (𝓝 0) := by simpa [Set.Ici_zero_eq_univ, hX0] using (hc 0).1.tendsto
  have hτne : tauPlus D.X 1 ω ≠ ⊤ := by intro htop; apply hdisc; simp [discountedAt, htop]
  cases hτ : tauPlus D.X 1 ω with
  | top => exact (hτne hτ).elim
  | coe ζ =>
    have hζpos : 0 < ζ := by
      by_contra hnot; have hζ0 : ζ = 0 := le_antisymm (le_of_not_gt hnot) bot_le; have hτ0 : tauPlus D.X 1 ω = 0 := by simpa [hζ0] using hτ
      obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hright0.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
      let δε : ℝ≥0 := ⟨ε, le_of_lt hεpos⟩
      have hsInf_lt : sInf S < (δε : WithTop ℝ≥0) := by rw [← hτS, hτ0]; exact_mod_cast hεpos
      obtain ⟨s, hsS, hslt⟩ := (sInf_lt_iff).1 hsInf_lt; rcases hsS with ⟨u, hu, hus, hXu⟩
      have hu_ltWT : (u : WithTop ℝ≥0) < (δε : WithTop ℝ≥0) := by simpa [← hus] using hslt
      have hu_lt : u < δε := by exact_mod_cast hu_ltWT
      have hu_lt_real : (u : ℝ) < ε := by change (u : ℝ) < (δε : ℝ); exact_mod_cast hu_lt
      have huball : u ∈ Metric.ball (0 : ℝ≥0) ε := by simpa [Metric.mem_ball, NNReal.dist_eq, abs_of_nonneg (NNReal.coe_nonneg u)] using hu_lt_real
      have hXu_lt : D.X u ω < (1 / 2 : ℝ) := hεsub huball
      linarith
    have hXζ : 1 ≤ D.X ζ ω := by
      by_contra hnot; have hlt : D.X ζ ω < 1 := lt_of_not_ge hnot
      obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp ((hc ζ).1.eventually (isOpen_Iio.mem_nhds hlt))
      let δ : ℝ≥0 := ⟨(ζ : ℝ) + ε, add_nonneg (NNReal.coe_nonneg ζ) (le_of_lt hεpos)⟩
      have hζδ : ζ < δ := by dsimp [δ]; exact_mod_cast (lt_add_of_pos_right (ζ : ℝ) hεpos)
      have hsInf_lt : sInf S < (δ : WithTop ℝ≥0) := by rw [← hτS, hτ]; exact_mod_cast hζδ
      obtain ⟨s, hsS, hslt⟩ := (sInf_lt_iff).1 hsInf_lt
      have hsS' : s ∈ S := hsS
      rcases hsS with ⟨u, hu, hus, hXu⟩
      have hζuWT : (ζ : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0) := by have hinf : sInf S ≤ s := sInf_le hsS'; rw [← hτ, hτS]; simpa [hus] using hinf
      have hζu : ζ ≤ u := by exact_mod_cast hζuWT
      have huδWT : (u : WithTop ℝ≥0) < (δ : WithTop ℝ≥0) := by simpa [← hus] using hslt
      have huδ : u < δ := by exact_mod_cast huδWT
      have huReal : (u : ℝ) < (ζ : ℝ) + ε := by
        change (u : ℝ) < (δ : ℝ)
        exact_mod_cast huδ
      have hζuReal : (ζ : ℝ) ≤ (u : ℝ) := by exact_mod_cast hζu
      have hdist : dist u ζ < ε := by rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr hζuReal)]; linarith
      have hmem : u ∈ Metric.ball ζ ε ∩ Ici ζ := ⟨by simpa [Metric.mem_ball] using hdist, hζu⟩
      have hXu_lt : D.X u ω < 1 := hεsub hmem
      linarith
    have hSupζ : M ζ = D.X ζ ω := by
      dsimp [M]; rw [runningSup]; apply le_antisymm
      · refine csSup_le ⟨D.X ζ ω, ⟨ζ, le_rfl, rfl⟩⟩ ?_; rintro z ⟨u, hu, rfl⟩
        by_cases huζ : u = ζ
        · subst u; rfl
        · have hult : u < ζ := lt_of_le_of_ne hu huζ; by_cases hu0 : u = 0
          · subst u; simpa [hX0] using (le_trans zero_le_one hXζ)
          · have hXule : D.X u ω ≤ 1 := by
              by_contra hn; have hsS : (u : WithTop ℝ≥0) ∈ S := ⟨u, pos_iff_ne_zero.mpr hu0, rfl, lt_of_not_ge hn⟩
              have hle : tauPlus D.X 1 ω ≤ (u : WithTop ℝ≥0) := by rw [hτS]; simpa using (sInf_le hsS)
              have hζle : (ζ : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0) := by simpa [hτ] using hle
              exact (not_lt_of_ge hζle) (by exact_mod_cast hult)
            exact hXule.trans hXζ
      · simpa [M, runningSup] using hdom ζ
    have hSup0 : M 0 = 0 := by
      dsimp [M]; rw [runningSup]; apply le_antisymm
      · refine csSup_le ⟨D.X 0 ω, ⟨0, le_rfl, rfl⟩⟩ ?_; rintro z ⟨u, hu, rfl⟩; have hu0 : u = 0 := le_antisymm hu bot_le; subst u; simpa [hX0]
      · simpa [M, runningSup] using hMnonneg 0
    refine ⟨ζ, hζpos, rfl, hreg.2 ζ, ?_, ?_⟩
    · rw [hfun 0, hSup0, hX0]
      norm_num
    · rw [hfun ζ, hSupζ]
      exact sub_self (D.X ζ ω)

theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (q : ℝ) :
  ∀ᵐ ω ∂P, discountedAt q (tauPlus D.X 1 ω) ≠ 0 → ∃ ζ : ℝ≥0, 0 < ζ ∧ tauPlus D.X 1 ω = (ζ : WithTop ℝ≥0) ∧ UpperSemicontinuousOn (fun t : ℝ≥0 => reflectAtSup D.X 0 t ω) (Set.Icc 0 ζ) ∧ reflectAtSup D.X 0 0 ω = 0 ∧ reflectAtSup D.X 0 ζ ω = 0 := by
  exact compactAux P D q
