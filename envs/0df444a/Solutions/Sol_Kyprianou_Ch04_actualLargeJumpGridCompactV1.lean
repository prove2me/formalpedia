-- Prove2me | solution 1 for Kyprianou.Ch04.actualLargeJumpGridCompactV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:56:10.091163+00:00
-- url     : https://prove2.me/submissions/c6eaafc9-3b06-4cbb-8a27-e8f241dd82bb

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Theorems.Thm_Kyprianou_Ch04_actualRetainedFiniteAtomsAEV1
import Theorems.Thm_Kyprianou_Ch04_physicalCommonRetainedAtomAffinePathsV1
import Theorems.Thm_Kyprianou_Ch04_finitePhysicalAtomsSubwindowIntegralV1
import Theorems.Thm_Kyprianou_Ch04_continuousWeightOnLeftLimitPathV1
import Theorems.Thm_Kyprianou_Ch04_compactLeftWeightBoundV1
import Theorems.Thm_Kyprianou_Ch04_finiteAffineGridCompactBoundLimitV1
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Set Filter Topology
open scoped NNReal ENNReal Classical
set_option autoImplicit false
/-- Apply the compact finite affine theorem to the actual large-jump path. -/
theorem solution : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν) (X L X2 : NNReal → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun u => X u w) (𝓝[<] t) (𝓝 (L t w)))
    (hN : ∀ᵐ w ∂P, N.N w = Kyprianou.Ch04.pathJumpMeasure X L w)
    (b : ℝ) (h2 : ∀ t w, X2 t w = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w))
    (g : ℝ → ℝ → ℝ)
    (hg : ContinuousOn (fun z : ℝ × ℝ => g z.1 z.2) (Ici (0 : ℝ) ×ˢ univ)),
    ∀ᵐ w ∂P, ∀ T : NNReal,
      Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
        let u := T * (i : NNReal) / (n : NNReal)
        let v := T * ((i+1 : ℕ) : NNReal) / (n : NNReal)
        g (u : ℝ) (L u w) * (X2 v w - X2 u w)) atTop
        (𝓝 (b * (∫ s in Icc (0 : ℝ) (T : ℝ), g s (L s.toNNReal w)) +
          ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
            z.2 * g z.1 (L z.1.toNNReal w) ∂(N.N w))) := by
  intro Ω m P hP ν hSigma hν N X L X2 hX hL hN b h2 g hg
  have hAtoms := Kyprianou.Ch04.actualRetainedFiniteAtomsAEV1 P ν hν N X L hX hL hN (1/2) (by norm_num)
  filter_upwards [hAtoms,hX.cadlag_ae,hL] with w hA hCad hEL
  intro T
  obtain ⟨S,hs,hR⟩ := hA T
  let j := fun r : NNReal => X r w - L r w
  let a := fun r => if 1 ≤ |j r| then j r else 0
  let H := fun r : NNReal => g (r : ℝ) (L r w)
  have hy (u : NNReal) (hu : u ≤ T) : X2 u w =
      b * (u : ℝ) + ∑ r ∈ S, if r ≤ u then a r else 0 := by
    rw [h2 u w]
    exact (Kyprianou.Ch04.physicalCommonRetainedAtomAffinePathsV1 (N.N w) T (1/2)
      b 0 (by norm_num) S j hs hR u hu).1
  have hH := Kyprianou.Ch04.continuousWeightOnLeftLimitPathV1
    (fun u => X u w) (fun u => L u w) g hEL hg
  obtain ⟨C,hC,hb⟩ := Kyprianou.Ch04.compactLeftWeightBoundV1
    (fun u => X u w) (fun u => L u w) g hCad hEL hg T
  have h := Kyprianou.Ch04.finiteAffineGridCompactBoundLimitV1 T S a H (fun u => X2 u w)
    b C (fun r hr => ⟨(hs r hr).1,(hs r hr).2.1⟩) hy hH hC hb
  let D := Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | (1/2 : ℝ) < |x|}
  let B := Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}
  have hB : MeasurableSet B := measurableSet_Icc.prod
    (measurableSet_le measurable_const measurable_id.abs)
  have hBD : B ⊆ D := prod_mono subset_rfl (fun x hx => (by norm_num : (1/2 : ℝ) < 1).trans_le hx)
  have hI : (∫ z in B, z.2 * g z.1 (L z.1.toNNReal w) ∂(N.N w)) =
      ∑ r ∈ S, a r * H r := by
    rw [Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 (N.N w) D S j hR B hB hBD]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [B,mem_prod,mem_Icc,mem_setOf_eq,r.coe_nonneg,true_and,
      NNReal.coe_le_coe,(hs r hr).2.1,Real.toNNReal_coe]
    by_cases h : 1 ≤ |j r| <;> simp [h,a,H]
  rw [← hI] at h
  have hTimeInt : (∫ s in Icc (0 : ℝ) (T : ℝ), H s.toNNReal) =
      ∫ s in Icc (0 : ℝ) (T : ℝ), g s (L s.toNNReal w) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    change g (s.toNNReal : ℝ) (L s.toNNReal w) = _
    rw [Real.coe_toNNReal _ hs.1]
  rw [hTimeInt] at h
  exact h
