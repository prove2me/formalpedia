-- Prove2me | solution 1 for OAI.Paper092.standardSimplex_volume
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:34:36.378171+00:00
-- url     : https://prove2.me/submissions/0920841c-4bea-4085-ac58-af8f4f3942c5

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/SimplexVolume.lean:L134-L147
-- (upload_full_project.md Phase 4): solution for node OAI.Paper092.standardSimplex_volume. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexVolume
import Theorems.Thm_OAI_Paper092_mem_standardSimplex_iff
import Theorems.Thm_OAI_Paper092_signChange_measurePreserving

-- ---- from OAI.Geometry.ProjectionVolume.SimplexGeometry ----
namespace OAI

noncomputable section

open Set MeasureTheory

namespace Paper092

theorem standardSimplex_isCompact (n : ℕ) : IsCompact (standardSimplex n) :=
  ((Set.finite_range _).insert 0).isCompact_convexHull ℝ

end Paper092

end

end OAI

-- ---- from OAI.Geometry.ProjectionVolume.SimplexVolume ----
namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Paper092

theorem measurableSet_coordinateSimplex (n : ℕ) : MeasurableSet (coordinateSimplex n) := by
  change MeasurableSet ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} ∩ {x | ∑ i, x i ≤ 1})
  refine MeasurableSet.inter ?_ ?_
  · rw [show {x : Fin n → ℝ | ∀ i, 0 ≤ x i} =
        ⋂ i : Fin n, {x : Fin n → ℝ | 0 ≤ x i} by ext; simp]
    exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i)
  · exact measurableSet_le (by fun_prop) measurable_const

theorem coordinateSimplex_volume_eq (n : ℕ) :
    volume (coordinateSimplex n) = volume (standardSimplex n) := by
  have hset : coordinateSimplex n =
      (WithLp.toLp 2) ⁻¹' standardSimplex n := by
    ext x
    exact (mem_standardSimplex_iff (WithLp.toLp 2 x)).symm
  rw [hset]
  exact (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    (standardSimplex_isCompact n).measurableSet.nullMeasurableSet

theorem signChange_abs {n : ℕ} (s : Fin n → Bool) (x : Fin n → ℝ) (i : Fin n) :
    |signChange s x i| = |x i| := by
  cases hs : s i <;> simp [signChange, hs]

theorem measurableSet_signedSimplex {n : ℕ} (s : Fin n → Bool) :
    MeasurableSet (signedSimplex s) :=
  (measurableSet_coordinateSimplex n).preimage (signChange_measurePreserving s).measurable

theorem signedSimplex_volume {n : ℕ} (s : Fin n → Bool) :
    volume (signedSimplex s) = volume (coordinateSimplex n) :=
  (signChange_measurePreserving s).measure_preimage
    (measurableSet_coordinateSimplex n).nullMeasurableSet

theorem signedSimplex_union (n : ℕ) :
    (⋃ s : Fin n → Bool, signedSimplex s) = {x : Fin n → ℝ | ∑ i, |x i| ≤ 1} := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    change (∀ i, 0 ≤ signChange s x i) ∧ ∑ i, signChange s x i ≤ 1 at hs
    change ∑ i, |x i| ≤ 1
    calc
      ∑ i, |x i| = ∑ i, signChange s x i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← signChange_abs s x i, abs_of_nonneg (hs.1 i)]
      _ ≤ 1 := hs.2
  · intro hx
    let s : Fin n → Bool := fun i => decide (0 ≤ x i)
    have hs (i : Fin n) : signChange s x i = |x i| := by
      by_cases h : 0 ≤ x i
      · simp [signChange, s, h, abs_of_nonneg h]
      · simp [signChange, s, h, abs_of_neg (lt_of_not_ge h)]
    apply mem_iUnion.mpr
    refine ⟨s, ?_⟩
    change (∀ i, 0 ≤ signChange s x i) ∧ ∑ i, signChange s x i ≤ 1
    simp_rw [hs]
    exact ⟨fun i => abs_nonneg _, hx⟩

theorem signedSimplex_pairwise_aedisjoint (n : ℕ) :
    Pairwise (fun s t : Fin n → Bool => AEDisjoint volume (signedSimplex s) (signedSimplex t)) := by
  intro s t hst
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ t i := Function.ne_iff.mp hst
  change volume (signedSimplex s ∩ signedSimplex t) = 0
  apply measure_mono_null (t := {x : Fin n → ℝ | x i = 0})
  · intro x hx
    have hs : 0 ≤ signChange s x i := hx.1.1 i
    have ht : 0 ≤ signChange t x i := hx.2.1 i
    change x i = 0
    cases hsi : s i <;> cases hti : t i <;>
      simp only [hsi, hti] at hi <;>
      simp only [signChange, hsi, hti, Bool.false_eq_true, ↓reduceIte] at hs ht <;>
      first | contradiction | linarith
  · exact Measure.pi_eval_preimage_null (fun _ : Fin n => (volume : Measure ℝ))
      (measure_singleton 0)

theorem signedSimplex_volume_sum (n : ℕ) :
    volume {x : Fin n → ℝ | ∑ i, |x i| ≤ 1} =
      (2 : ENNReal) ^ n * volume (coordinateSimplex n) := by
  rw [← signedSimplex_union, measure_iUnion₀ (signedSimplex_pairwise_aedisjoint n)
    (fun s => (measurableSet_signedSimplex s).nullMeasurableSet)]
  simp [signedSimplex_volume, tsum_fintype]

theorem l1Ball_volume (n : ℕ) :
    volume {x : Fin n → ℝ | ∑ i, |x i| ≤ 1} =
      ENNReal.ofReal ((2 : ℝ) ^ n / (Nat.factorial n : ℝ)) := by
  cases n with
  | zero =>
    have hzero : volume (univ : Set (Fin 0 → ℝ)) = 1 :=
      Measure.pi_empty_univ (fun _ : Fin 0 => (volume : Measure ℝ))
    simpa using hzero
  | succ n =>
    have h := MeasureTheory.volume_sum_rpow_le (Fin (n + 1)) (p := 1) (by norm_num) 1
    have hg : Real.Gamma (1 + 1 : ℝ) = 1 := by
      simpa using Real.Gamma_nat_eq_factorial 1
    simpa only [Fintype.card_fin, div_one, Real.rpow_one, ENNReal.ofReal_one,
      one_pow, one_mul, hg, mul_one, Real.Gamma_nat_eq_factorial] using h

theorem standardSimplex_volume (n : ℕ) :
    volume (standardSimplex n) = ENNReal.ofReal (1 / (Nat.factorial n : ℝ)) := by
  have h := (signedSimplex_volume_sum n).symm.trans (l1Ball_volume n)
  rw [coordinateSimplex_volume_eq] at h
  have htwo : (2 : ENNReal) ^ n ≠ 0 := by positivity
  have htop : (2 : ENNReal) ^ n ≠ ⊤ := by finiteness
  have hpow : (2 : ENNReal) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) := by
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  apply (ENNReal.mul_right_inj htwo htop).mp
  rw [h, hpow,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ n)]
  congr 1
  ring

end Paper092

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper092
open Set MeasureTheory
open scoped BigOperators ENNReal

theorem solution (n : ℕ) :
    volume (standardSimplex n) = ENNReal.ofReal (1 / (Nat.factorial n : ℝ)) := by
  first
    | exact OAI.Paper092.standardSimplex_volume n
    | exact OAI.Paper092.standardSimplex_volume
    | (apply OAI.Paper092.standardSimplex_volume <;> assumption)
    | (intros; apply OAI.Paper092.standardSimplex_volume <;> assumption)
