-- Prove2me | solution 1 for Kyprianou.Ch04.physicalWeightedIntegralErrorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:14:20.61275+00:00
-- url     : https://prove2.me/submissions/049db0bd-7856-4a5d-b41e-76a168d47933

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_boundedClockIntegralPerturbationV1
import Theorems.Thm_Kyprianou_Ch04_finitePhysicalAtomsSubwindowIntegralV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- The stopped finite-variation integral has a Lipschitz bound in the weight,
with the actual absolute marked ledger rather than an expected mark size. -/
theorem solution (R : Measure (ℝ × ℝ)) (T : NNReal)
    (S : Finset NNReal) (j H L : NNReal → ℝ) (b d : ℝ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T ∧ 1/2 < |j r|)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (hd : 0 ≤ d)
    (hH : IntegrableOn (fun s : ℝ => H s.toNNReal) (Ioc (0 : ℝ) (T : ℝ)))
    (hL : IntegrableOn (fun s : ℝ => L s.toNNReal) (Ioc (0 : ℝ) (T : ℝ)))
    (h : ∀ r ≤ T, 0 < r → |H r - L r| ≤ d) :
    ∀ t ≤ T,
      |(b * (∫ s in Icc (0 : ℝ) (t : ℝ), H s.toNNReal) +
        ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
          z.2 * H z.1.toNNReal ∂ R) -
       (b * (∫ s in Icc (0 : ℝ) (t : ℝ), L s.toNNReal) +
        ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
          z.2 * L z.1.toNNReal ∂ R)| ≤
      (|b| * (T : ℝ) + (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ
          {x : ℝ | 1/2 < |x|}, |z.2| ∂ R)) * d := by
  intro t ht
  let D : Set (ℝ × ℝ) := Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}
  have hD : MeasurableSet D := measurableSet_Icc.prod
    (measurableSet_lt measurable_const measurable_id.abs)
  have hledger : (∫ z in D, |z.2| ∂ R) = ∑ r ∈ S, |j r| := by
    rw [Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 R D S j hR D hD
      (Subset.rfl) (fun z => |z.2|)]
    apply Finset.sum_congr rfl
    intro r hr
    rw [if_pos]
    exact ⟨⟨r.coe_nonneg,by exact_mod_cast (hS r hr).2.1⟩,(hS r hr).2.2⟩
  have hb := Kyprianou.Ch04.boundedClockIntegralPerturbationV1
    (fun s => H s.toNNReal) (fun s => L s.toNNReal) T d hd hH hL
    (fun s hs => h s.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hs.2)
      (Real.toNNReal_pos.mpr hs.1)) t ht
  let A : Set (ℝ × ℝ) := Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}
  have hA : MeasurableSet A := measurableSet_Icc.prod
    (measurableSet_le measurable_const measurable_id.abs)
  have hAD : A ⊆ D := fun z hz =>
    ⟨⟨hz.1.1,hz.1.2.trans (by exact_mod_cast ht)⟩,
      (show (1/2 : ℝ) < 1 by norm_num).trans_le hz.2⟩
  have hj : |(∫ z in A, z.2 * H z.1.toNNReal ∂ R) -
      (∫ z in A, z.2 * L z.1.toNNReal ∂ R)| ≤ (∑ r ∈ S, |j r|) * d := by
    rw [Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 R D S j hR A hA hAD,
      Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 R D S j hR A hA hAD,
      ← Finset.sum_sub_distrib]
    simp only [Real.toNNReal_coe]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro r hr
    by_cases hz : ((r : ℝ),j r) ∈ A
    · rw [if_pos hz,if_pos hz,← mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_left (h r (hS r hr).2.1 (hS r hr).1) (abs_nonneg _)
    · simp [hz,mul_nonneg (abs_nonneg (j r)) hd]
  change |(b * _ + (∫ z in A, _ ∂ R)) - (b * _ + (∫ z in A, _ ∂ R))| ≤
    (|b| * (T : ℝ) + (∫ z in D, |z.2| ∂ R)) * d
  rw [hledger]
  rw [show ∀ a c u v : ℝ, (b*a+u)-(b*c+v)=b*(a-c)+(u-v) by intros; ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hb (abs_nonneg b)]
