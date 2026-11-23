-- Prove2me | solution 1 for NoHair.schwarzschild_timelike_end_exterior
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T06:59:44.618575+00:00
-- url     : https://prove2.me/submissions/50b4dfa4-fb06-4487-9bca-94719f5d5224

import Theorems.Thm_NoHair_kerrNewman_outerHorizon_futureTrapped
import Theorems.Thm_NoHair_kerrNewman_exterior_timelikeAccess
import Definitions.Def_NoHair_KerrNewmanEinstein_Base
import Definitions.Def_NoHair_kerrNewmanTimeDirection
open NoHair NoHair.KNE Set
open scoped ContDiff Manifold
noncomputable section

private abbrev U := kerrNewmanSpacetime 0

private theorem radius_eq (x : E4) : ksRadius 0 x = spatialRadius x := by
  let p := x 1^2+x 2^2+x 3^2
  have hp : 0 ≤ p := by dsimp [p]; positivity
  change Real.sqrt ((p-0^2+Real.sqrt ((p-0^2)^2+4*0^2*x 3^2))/2) = Real.sqrt p
  simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,zero_mul,add_zero,sub_zero,Real.sqrt_sq hp]
  congr 1; ring

private lemma basis_entry (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    matrixBilin A (coordBasis i) (coordBasis j) = A i j := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (coordBasis i)) (WithLp.ofLp (coordBasis j)) = _
  simp only [coordBasis, EuclideanSpace.single, PiLp.ofLp_single]
  rw [Matrix.toLinearMap₂'_apply]
  simp_rw [← Finset.smul_sum]
  simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']

private lemma tt (m : ℝ) (x : U) :
    kerrNewmanMetricField m 0 0 x (coordBasis 0) (coordBasis 0) = -1+2*m/(spatialRadius x.val) := by
  have hp : 0 < ksRadius 0 x.val := x.property
  change matrixBilin (kerrNewmanMetric m 0 0 x.val) (coordBasis 0) (coordBasis 0) = _
  rw [basis_entry, ← radius_eq]
  have flat : minkowski 0 0=-1 := by simp [minkowski]
  simp only [kerrNewmanMetric,flat,ksNull_zero,mul_one]
  unfold ksProfile
  field_simp [hp.ne'] <;> ring

theorem solution (m : ℝ) (hm : 0 < m) (R : ℝ) (hR : 0 < R) :
    let S := kerrNewmanSpacetime 0
    let g := kerrNewmanMetricField m 0 0
    let T := kerrNewmanTimeDirection m 0 0
    let A := (Subtype.val : S → E4) ⁻¹' exteriorRegion R
    let D := (Subtype.val : S → E4) ⁻¹' kerrNewmanDOC m 0 0
    ((∀ x ∈ A, g x (coordBasis 0) (coordBasis 0) < 0) ↔ 2*m ≤ R) ∧
      (2*m ≤ R → chronoPastSet g T A = D ∧ domainOfOuterCommunications g T A = D) := by
  dsimp only
  let A := (Subtype.val : U → E4) ⁻¹' exteriorRegion R
  let D := (Subtype.val : U → E4) ⁻¹' kerrNewmanDOC m 0 0
  have ho : kerrNewmanOuterRadius m 0 0 = 2*m := by
    simp [kerrNewmanOuterRadius,Real.sqrt_sq hm.le,two_mul]
  have par : IsKerrNewmanBlackHoleParams m 0 0 := ⟨hm,by nlinarith [sq_nonneg m]⟩
  constructor
  · constructor
    · intro h
      by_contra! bad
      let ρ := (R+2*m)/2
      have rpos : 0 < ρ := by dsimp [ρ]; positivity
      let z : E4 := WithLp.toLp 2 ![0,ρ,0,0]
      have rz : spatialRadius z=ρ := by
        change Real.sqrt (ρ^2+0^2+0^2)=ρ
        simp [Real.sqrt_sq rpos.le]
      let x : U := ⟨z, by change 0<ksRadius 0 z; rw [radius_eq,rz]; exact rpos⟩
      have hx : x∈A := by change R<spatialRadius z; rw [rz]; dsimp [ρ]; linarith
      have hneg := h x hx
      rw [tt] at hneg
      change -1+2*m/spatialRadius z < 0 at hneg
      rw [rz] at hneg
      have less := (div_lt_one rpos).1 (show 2*m/ρ<1 by linarith)
      dsimp [ρ] at less
      linarith
    · intro h x hx
      rw [tt]
      have hr : R < spatialRadius x.val := hx
      have less := (div_lt_one (hR.trans hr)).2 (h.trans_lt hr)
      linarith
  · intro h
    let T := kerrNewmanTimeDirection m 0 0
    let g := kerrNewmanMetricField m 0 0
    have access := kerrNewman_exterior_timelikeAccess m 0 0 par R
    have past : chronoPastSet g T A = D := by
      apply Subset.antisymm _ (fun x hx => (access hx).1)
      intro x hx
      obtain ⟨q,hq⟩ := mem_iUnion.mp hx
      obtain ⟨hqA,γ,hγ,h0,h1⟩ := mem_iUnion.mp hq
      have far : kerrNewmanOuterRadius m 0 0 < ksRadius 0 q.val := by
        rw [ho,radius_eq]; exact h.trans_lt hqA
      change kerrNewmanOuterRadius m 0 0 < ksRadius 0 x.val
      by_contra! low
      have stop := (kerrNewman_outerHorizon_futureTrapped m 0 0 par).2 γ hγ
        (h0 ▸ low : ksRadius 0 (γ 0).val ≤ kerrNewmanOuterRadius m 0 0)
      rw [h1] at stop
      exact far.not_ge stop
    refine ⟨past,?_⟩
    change chronoFutureSet g T A ∩ chronoPastSet g T A = D
    rw [past]
    exact inter_eq_right.mpr (fun x hx => (access hx).2)
