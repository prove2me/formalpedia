-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_2_v2_scale_representation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:58:58.927809+00:00
-- url     : https://prove2.me/submissions/6c5654e2-52b6-47b3-bdc0-0c50a750ed25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Integrated parent solution for Prove2Me target
  Kyprianou.Ch08.StageB.source_result8_2_v2_scale_representation
  UUID: a2c584da-360d-4567-ae4c-ac67a244841f
  Mission: 774734e3-04f0-4425-85f7-4e268610a046
  Rev: 0df444a360eaa60ab8c11dca51a86af692955474
  Thread: 01a20359-33e9-7e73-90cf-026b790c3d68
  Owner: /root/scale_representation_proof (second integration owner)

v3: CE repair of candidate 45972 (remote CE, group E01 TYPE_MISMATCH at L46).
`AntitoneOn.intervalIntegrable` at the pinned revision expects
`AntitoneOn f (uIcc x a)`; convert the Icc antitone proof via
`Set.uIcc_of_le hle`. All else identical to v2 (canonical efd9 bridge).
-/
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_exit_ratio
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_exponent_quadratic_upper
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_positive_from_quadratic
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_up_before_down_excursion_exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

private lemma tail_finite {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (q : ℝ) (n : Measure ℝ) (hn : HasActualQExcursionHeightLaw P D ψ q n) {h : ℝ} (hh : 0 < h) : n (Set.Ici h) < ⊤ := (hn.2 1 h zero_lt_one hh).1

private lemma tail_anti {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (q : ℝ) (n : Measure ℝ) (hn : HasActualQExcursionHeightLaw P D ψ q n) {x a : ℝ} (hx : 0 < x) : AntitoneOn (fun t : ℝ => (n (Set.Ici t)).toReal) (Set.Icc x a) := by
  intro t1 ht1 t2 ht2 hle
  have p1 : 0 < t1 := lt_of_lt_of_le hx ht1.1
  have p2 : 0 < t2 := lt_of_lt_of_le hx ht2.1
  have f1 : n (Set.Ici t1) < ⊤ := tail_finite P D ψ q n hn p1
  have f2 : n (Set.Ici t2) < ⊤ := tail_finite P D ψ q n hn p2
  exact (ENNReal.toReal_le_toReal f2.ne f1.ne).mpr (measure_mono (Set.Ici_subset_Ici.mpr hle))

private lemma tail_int {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (q : ℝ) (n : Measure ℝ) (hn : HasActualQExcursionHeightLaw P D ψ q n) {x a : ℝ} (hx : 0 < x) (hxa : x < a) : IntegrableOn (fun t : ℝ => Phi ψ q + (n (Set.Ici t)).toReal) (Set.Icc x a) volume := by
  have hle : x ≤ a := le_of_lt hxa
  have hA : AntitoneOn (fun t : ℝ => (n (Set.Ici t)).toReal) (Set.Icc x a) := tail_anti P D ψ q n hn hx
  have hU : Set.uIcc x a = Set.Icc x a := Set.uIcc_of_le hle
  have hA' : AntitoneOn (fun t : ℝ => (n (Set.Ici t)).toReal) (Set.uIcc x a) := by rw [hU]; exact hA
  have hT : IntervalIntegrable (fun t : ℝ => (n (Set.Ici t)).toReal) volume x a := hA'.intervalIntegrable
  have hC : IntervalIntegrable (fun _ : ℝ => Phi ψ q) volume x a := intervalIntegrable_const
  have hAdd : IntervalIntegrable (fun t : ℝ => Phi ψ q + (n (Set.Ici t)).toReal) volume x a := by simpa using hC.add hT
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mp hAdd

private theorem pos_quad {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) {x : ℝ} (hx : 0 < x) : 0 < W q x := by
  obtain ⟨K, hK, hb⟩ := source_result81_exponent_quadratic_upper Ω P D ψ hψ
  exact source_result81_scale_positive_from_quadratic ψ q (W q) (hW q hq) K hK hb x hx

theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) (n : Measure ℝ) (hLaw : HasActualQExcursionHeightLaw P D ψ q n) : HasQExcursionScaleRepresentation ψ q (W q) n := by
  constructor
  · intro x hx
    exact pos_quad P D ψ W hψ hW q hq hx
  · intro x a hx hxa
    have hI : IntegrableOn (fun t : ℝ => Phi ψ q + (n (Set.Ici t)).toReal) (Set.Icc x a) volume := tail_int P D ψ q n hLaw hx hxa
    have ha : 0 < a := lt_trans hx hxa
    have hle : x ≤ a := le_of_lt hxa
    have hWa : 0 < W q a := pos_quad P D ψ W hψ hW q hq ha
    have hNe : W q a ≠ 0 := ne_of_gt hWa
    have hE : upBeforeDownExpectation P D.X q x a = W q x / W q a := source_result81_upper_exit_ratio Ω P D ψ hψ W hW q x a hq ha hle
    have hB : upBeforeDownExpectation P D.X q x a = Real.exp (-(∫ t in x..a, Phi ψ q + (n (Set.Ici t)).toReal)) := source_result8_2_v2_up_before_down_excursion_exponential P D ψ hψ q hq n hLaw x a hx hxa
    have hR : W q x / W q a = Real.exp (-(∫ t in x..a, Phi ψ q + (n (Set.Ici t)).toReal)) := by rw [← hE, hB]
    have hW : W q x = W q a * Real.exp (-(∫ t in x..a, Phi ψ q + (n (Set.Ici t)).toReal)) := by have h := (div_eq_iff hNe).mp hR; rw [h, mul_comm]
    exact ⟨hI, hW⟩
