-- Prove2me | solution 1 for NoHair.asymptoticallyFlatEnd_coordinate_cones
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:05:14.838653+00:00
-- url     : https://prove2.me/submissions/11848081-6021-4d9a-a76b-c5dea14ba714

import Definitions.Def_NoHair_spacetime

open NoHair Set
open scoped ContDiff Manifold BigOperators
noncomputable section
private abbrev I4 := 𝓘(ℝ,E4)

private theorem basis_sum (v : E4) : ∑ i, v i • coordBasis i = v := by
  ext j
  fin_cases j <;> simp [Fin.sum_univ_four,coordBasis]

private theorem evaluate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : V →L[ℝ] V →L[ℝ] ℝ) (L : E4 →L[ℝ] V) (v w : E4) :
    G (L v) (L w) = ∑ i, ∑ j, v i * (w j * G (L (coordBasis i)) (L (coordBasis j))) := by
  have repr (z : E4) : L z = ∑ i, z i • L (coordBasis i) := by
    calc
      L z = L (∑ i, z i • coordBasis i) := congrArg L (basis_sum z).symm
      _ = _ := by simp only [map_sum,map_smul]
  rw [repr v,repr w]
  simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem metric_symm {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    {g : BilinField M} (hg : IsLorentzian g) (x : M) (v w : TangentSpace I4 x) :
    g x w v = g x v w := by
  obtain ⟨b,hb⟩ := hg x
  have repr (u z : TangentSpace I4 x) :
      g x u z = ∑ i, ∑ j, b.repr u i * (b.repr z j * minkowski i j) := by
    conv_lhs => rw [← b.sum_repr u, ← b.sum_repr z]
    simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,hb,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [repr,repr]
  simp [minkowski,Fin.sum_univ_four]
  <;> ring

private theorem component_error {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold I4 ∞ M] {g F : BilinField M} {φ : ℝ → M → M}
    (E : AsymptoticallyFlatEnd g F φ) (y : E4) (hy : y ∈ exteriorRegion E.R)
    (hfar : 16 * |E.C| ≤ spatialRadius y) (v : E4) :
    let L := mfderiv I4 I4 E.ψ y
    |g (E.ψ y) (L v) (L v) - (-(v 0)^2+(v 1)^2+(v 2)^2+(v 3)^2)| ≤
      ((v 0)^2+(v 1)^2+(v 2)^2+(v 3)^2)/4 := by
  let L : E4 →L[ℝ] E4 := mfderiv I4 I4 E.ψ y
  let G := pullbackCoeffs g E.ψ y
  have hypos : 0 < spatialRadius y := E.R_pos.trans hy
  have hf : E.C / spatialRadius y ≤ 1/16 := (div_le_iff₀ hypos).mpr (by linarith [le_abs_self E.C])
  have entry (i j : Fin 4) : |G i j - minkowski i j| ≤ 1/16 :=
    (E.metric_decay y hy i j).trans hf
  have herr (i j : Fin 4) :
      |v i * (v j * (G i j - minkowski i j))| ≤ ((v i)^2+(v j)^2)/32 := by
    calc
      _ = (|v i| * |v j|) * |G i j-minkowski i j| := by rw [abs_mul,abs_mul,mul_assoc]
      _ ≤ (|v i| * |v j|)*(1/16) := mul_le_mul_of_nonneg_left (entry i j) (by positivity)
      _ ≤ _ := by nlinarith only [sq_nonneg (|v i| - |v j|),sq_abs (v i),sq_abs (v j)]
  have expand : g (E.ψ y) (L v) (L v) = ∑ i, ∑ j, v i * (v j * G i j) :=
    evaluate _ L v v
  have flat : (∑ i, ∑ j, v i * (v j * minkowski i j)) =
      -(v 0)^2+(v 1)^2+(v 2)^2+(v 3)^2 := by
    simp [minkowski,Fin.sum_univ_four]
    <;> ring
  have diff : g (E.ψ y) (L v) (L v) - (-(v 0)^2+(v 1)^2+(v 2)^2+(v 3)^2) =
      ∑ i, ∑ j, v i * (v j*(G i j-minkowski i j)) := by
    rw [expand,←flat]
    simp only [mul_sub,Finset.sum_sub_distrib]
  change |g (E.ψ y) (L v) (L v) - _| ≤ _
  rw [diff]
  calc
    _ ≤ ∑ i : Fin 4, |∑ j, v i * (v j * (G i j-minkowski i j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, ((v i)^2+(v j)^2)/32 := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => herr i j))
    _ = _ := by simp only [Fin.sum_univ_four]; ring

theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] {g F : BilinField M} {φ : ℝ → M → M}
    (E : AsymptoticallyFlatEnd g F φ)
    (hg : IsLorentzian g) (y : E4) (hy : y ∈ exteriorRegion E.R)
    (hfar : 16 * |E.C| ≤ spatialRadius y) :
    let L := mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) E.ψ y
    let B := fun v w : E4 => g (E.ψ y) (L v) (L w)
    (∀ v : E4, v 0 = 0 → 0 ≤ B v v) ∧
    (∀ u d : ℝ, 0 < u → 2 * |d| ≤ u →
      B (u • coordBasis 0 + d • coordBasis 1) (u • coordBasis 0 + d • coordBasis 1) < 0) ∧
    ∀ v w : E4, B v v < 0 → B w w < 0 → B v w * v 0 * w 0 < 0 := by
  let L : E4 →L[ℝ] E4 := mfderiv I4 I4 E.ψ y
  let B := fun v w : E4 => g (E.ψ y) (L v) (L w)
  have spatial (v : E4) (hv : v 0 = 0) : 0 ≤ B v v := by
    have he := neg_le_of_abs_le (component_error E y hy hfar v)
    change -(_/4) ≤ B v v - _ at he
    rw [hv] at he
    nlinarith only [he,sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]
  refine ⟨spatial,?_,?_⟩
  · intro u d hu hd
    let v := u • coordBasis 0 + d • coordBasis 1
    have v0 : v 0 = u := by simp [v,coordBasis]
    have v1 : v 1 = d := by simp [v,coordBasis]
    have v2 : v 2 = 0 := by simp [v,coordBasis]
    have v3 : v 3 = 0 := by simp [v,coordBasis]
    have he := (le_abs_self _).trans (component_error E y hy hfar v)
    change B v v - _ ≤ _ at he
    rw [v0,v1,v2,v3] at he
    have hs := (sq_le_sq₀ (show 0 ≤ 2*|d| by positivity) hu.le).mpr hd
    change B v v < 0
    nlinarith only [he,hs,sq_abs d,sq_pos_of_pos hu]
  · intro v w hv hw
    change B v v < 0 at hv
    change B w w < 0 at hw
    have hv0 : v 0 ≠ 0 := fun h => (not_lt_of_ge (spatial v h)) hv
    have hk := spatial ((w 0) • v - (v 0) • w) (by simp [smul_eq_mul,mul_comm])
    let G : E4 →L[ℝ] E4 →L[ℝ] ℝ := g (E.ψ y)
    have hsym : G (L w) (L v) = G (L v) (L w) := metric_symm hg (E.ψ y) (L v) (L w)
    change 0 ≤ G (L ((w 0) • v - (v 0) • w)) (L ((w 0) • v - (v 0) • w)) at hk
    change G (L v) (L v) < 0 at hv
    change G (L w) (L w) < 0 at hw
    change G (L v) (L w) * v 0 * w 0 < 0
    simp only [map_sub,map_smul,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,hsym] at hk
    nlinarith only [hk,mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hv.le,
      mul_neg_of_pos_of_neg (sq_pos_iff.mpr hv0) hw]
