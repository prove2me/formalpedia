-- Prove2me | solution 1 for Kyprianou.Ch04.finiteAtomWeightLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:18:32.344335+00:00
-- url     : https://prove2.me/submissions/be8f4aa3-398e-42ea-a05f-6c33f79389a5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finitePhysicalAtomsSubwindowIntegralV1
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Large marks on a finite retained-atom window admit termwise continuous weight limits. -/
theorem solution (R : Measure (ℝ × ℝ)) (T : NNReal)
    (S : Finset NNReal) (j : NNReal → ℝ)
    (hs : ∀ r ∈ S, 0 < r ∧ r ≤ T)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | (1/2:ℝ) < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (Y : ℕ → NNReal → ℝ) (L : NNReal → ℝ)
    (g : ℝ → ℝ → ℝ)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Ici (0 : ℝ) ×ˢ univ))
    (h : ∀ t : NNReal, 0 < t → t ≤ T →
      Tendsto (fun n => Y n t) atTop (𝓝 (L t))) :
    Tendsto (fun n => ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
      z.2 * g z.1 (Y n z.1.toNNReal) ∂ R) atTop
      (𝓝 (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
        z.2 * g z.1 (L z.1.toNNReal) ∂ R)) := by
  classical
  let A := Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}
  have hA : MeasurableSet A := measurableSet_Icc.prod
    (measurableSet_le measurable_const measurable_id.abs)
  have hSub : A ⊆ Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | (1/2:ℝ) < |x|} :=
    fun z hz => ⟨hz.1,lt_of_lt_of_le (by norm_num : (1/2 : ℝ) < 1) hz.2⟩
  have hI (Z : NNReal → ℝ) :
      (∫ z in A, z.2 * g z.1 (Z z.1.toNNReal) ∂ R) =
        ∑ r ∈ S, if ((r : ℝ),j r) ∈ A then j r * g r (Z r) else 0 := by
    rw [Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 R _ S j hR A hA hSub]
    simp only [Real.toNNReal_coe]
  change Tendsto (fun n => ∫ z in A, z.2 * g z.1 (Y n z.1.toNNReal) ∂ R) atTop
    (𝓝 (∫ z in A, z.2 * g z.1 (L z.1.toNNReal) ∂ R))
  simp only [hI]
  apply tendsto_finset_sum
  intro r hr
  by_cases hmem : ((r : ℝ),j r) ∈ A
  · simp only [if_pos hmem]
    have hp : Tendsto (fun n => ((r : ℝ),Y n r)) atTop
        (𝓝[Ici (0 : ℝ) ×ˢ (univ : Set ℝ)] ((r : ℝ),L r)) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.prodMk_nhds
        (h r (hs r hr).1 (hs r hr).2),Eventually.of_forall fun _ => ⟨r.coe_nonneg,mem_univ _⟩⟩
    exact tendsto_const_nhds.mul ((hg ((r : ℝ),L r) ⟨r.coe_nonneg,mem_univ _⟩).tendsto.comp hp)
  · simp only [if_neg hmem]
    exact tendsto_const_nhds
