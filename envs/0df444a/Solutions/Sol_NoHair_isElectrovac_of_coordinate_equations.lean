-- Prove2me | solution 1 for NoHair.isElectrovac_of_coordinate_equations
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T19:52:40.547665+00:00
-- url     : https://prove2.me/submissions/64cfed7a-12e5-4c5a-98c3-5d6cdf6be89c

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold BigOperators Topology

private theorem partial_eq_on_open {s : Set E4} (hs : IsOpen s) {f g : E4 → ℝ}
    (h : EqOn f g s) (k : Fin 4) {z : E4} (hz : z ∈ s) :
    coordPartial f k z = coordPartial g k z :=
  congrArg (fun L : E4 →L[ℝ] ℝ => L (coordBasis k))
    (h.eventuallyEq_of_mem (hs.mem_nhds hz)).fderiv_eq

private theorem einsteinMaxwell_of_eqOn {s : Set E4} (hs : IsOpen s)
    {G' G F' F : E4 → Matrix (Fin 4) (Fin 4) ℝ}
    (hG : EqOn G' G s) (hF : EqOn F' F s) {y : E4} (hy : y ∈ s)
    (hem : EinsteinMaxwellAt G F y) : EinsteinMaxwellAt G' F' y := by
  have dG (z : E4) (hz : z ∈ s) (i j k : Fin 4) :
      coordPartial (fun w => G' w i j) k z = coordPartial (fun w => G w i j) k z :=
    partial_eq_on_open hs (fun w hw => congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) (hG hw)) k hz
  have dF (z : E4) (hz : z ∈ s) (i j k : Fin 4) :
      coordPartial (fun w => F' w i j) k z = coordPartial (fun w => F w i j) k z :=
    partial_eq_on_open hs (fun w hw => congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) (hF hw)) k hz
  have chr (z : E4) (hz : z ∈ s) (i j k : Fin 4) :
      christoffel G' z i j k = christoffel G z i j k := by
    simp only [christoffel, invMetric, hG hz, dG z hz]
  have dChr (z : E4) (hz : z ∈ s) (i j k l : Fin 4) :
      coordPartial (fun w => christoffel G' w i j k) l z =
      coordPartial (fun w => christoffel G w i j k) l z :=
    partial_eq_on_open hs (fun w hw => chr w hw i j k) l hz
  have ric (i j : Fin 4) : ricci G' y i j = ricci G y i j := by
    simp only [ricci, riemann, dChr y hy, chr y hy]
  have flux (i j : Fin 4) :
      coordPartial (fun z => Real.sqrt |(G' z).det| * raiseBoth G' F' z i j) i y =
      coordPartial (fun z => Real.sqrt |(G z).det| * raiseBoth G F z i j) i y := by
    apply partial_eq_on_open hs _ i hy
    intro z hz
    simp only [raiseBoth, invMetric, hG hz, hF hz]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simpa only [einsteinTensor, scalarCurvature, maxwellSource, raiseBoth, invMetric,
      hG hy, hF hy, ric] using hem.1 i j
  · intro j
    simpa only [flux] using hem.2.1 j
  · intro i j k
    simpa only [dF y hy] using hem.2.2 i j k

theorem solution (U : TopologicalSpace.Opens E4) (G F : E4 → Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ y ∈ U, EinsteinMaxwellAt G F y) :
    IsElectrovac (M := U) (fun x => matrixBilin (G x.val)) (fun x => matrixBilin (F x.val)) := by
  intro c hc y hy
  obtain ⟨p, hp⟩ := TopologicalSpace.Opens.chart_eq (H := E4) ⟨c.symm y⟩ hc
  have hchart (x : U) : c = chartAt E4 x := hp.trans (by rfl)
  have hval (z : E4) (hz : z ∈ c.target) : (c.symm z).val = z := by
    have eqval (x : U) : c x = x.val := by rw [hchart x] <;> rfl
    exact (eqval (c.symm z)).symm.trans (c.right_inv hz)
  have derivAt (x : U) :
      (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) c.symm x.val : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
    rw [hchart x]
    have hd := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, E4)) (x := x)
    simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at hd
    exact hd
  have coeff (A : E4 → Matrix (Fin 4) (Fin 4) ℝ) :
      EqOn (pullbackCoeffs (M := U) (fun x => matrixBilin (A x.val)) c.symm) A c.target := by
    intro z hz
    have hd := derivAt (c.symm z)
    rw [hval z hz] at hd
    funext i j
    unfold pullbackCoeffs
    rw [hd]
    change matrixBilin (A (c.symm z).val) (coordBasis i) (coordBasis j) = A z i j
    rw [hval z hz]
    change Matrix.toLinearMap₂' ℝ (A z) (WithLp.ofLp (coordBasis i))
      (WithLp.ofLp (coordBasis j)) = A z i j
    simp only [coordBasis, EuclideanSpace.single, PiLp.ofLp_single]
    rw [Matrix.toLinearMap₂'_apply]
    simp_rw [← Finset.smul_sum]
    simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']
  apply einsteinMaxwell_of_eqOn c.open_target (coeff G) (coeff F) hy
  apply h
  rw [← hval y hy]
  exact (c.symm y).property
