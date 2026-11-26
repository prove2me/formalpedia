-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_reference_noise_is_standard_brownian
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:44:28.849094+00:00
-- url     : https://prove2.me/submissions/cf0be3bd-f570-4316-bb11-f63aa39d5e28

import Definitions.Def_ManyServerQED_Scheduling_Model
import Theorems.Thm_ManyServerQED_Scheduling_independent_brownian_normalized_linear_combination
import Theorems.Thm_ManyServerQED_Scheduling_independent_disjoint_groups_of_primitive_fields

open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open ManyServerQED.Scheduling

set_option maxHeartbeats 1700000 in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    {k : ℕ} (M : SystemSequence Ω k) {P' : Measure Ω'} [IsProbabilityMeasure P']
    (B : Fin (k+k+k) → ℝ≥0 → Ω' → ℝ)
    (hB : ∀ j, IsBrownianReal (B j) P') (hBm : ∀ j t, Measurable (B j t))
    (hI : iIndepFun (fun j ω (t : ℝ≥0) => B j t ω) P') :
    let W (t : ℝ≥0) (ω : Ω') (i : Fin k) :=
      (Real.sqrt (M.lam i*M.cU2 i)*B (Fin.castAdd k (Fin.castAdd k i)) t ω -
        Real.sqrt (M.mu i)*B (Fin.castAdd k (Fin.natAdd k i)) ((M.rho i).toNNReal*t) ω) /
        M.diffData.r i
    (∀ i, IsBrownianReal (fun t ω => W t ω i) P') ∧
      iIndepFun (fun i ω (t : ℝ≥0) => W t ω i) P' := by
  intro W
  let π : (Fin k ⊕ Fin k) ⊕ Fin k ≃ Fin (k+k+k) :=
    (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv
  let A (i : Fin k) := π (.inl (.inl i))
  let S (i : Fin k) := π (.inl (.inr i))
  have hAS (i j : Fin k) : A i ≠ S j := by
    intro h
    have h' := π.injective h
    cases h'
  have hAa : Function.Injective A := by
    intro i j h
    have h' := π.injective h
    injection h' with he
    injection he
  have hSa : Function.Injective S := by
    intro i j h
    have h' := π.injective h
    injection h' with he
    injection he
  let D := M.diffData
  let scale (i : Fin k) := (M.rho i).toNNReal
  have hScale (i : Fin k) : 0 < M.rho i := div_pos (M.lam_pos i) (M.mu_pos i)
  have hScaleCo (i : Fin k) : ((scale i):ℝ) = M.rho i :=
    Real.coe_toNNReal _ (hScale i).le
  have hScale0 (i : Fin k) : scale i ≠ 0 := by
    intro h
    have he := hScaleCo i
    rw [h,NNReal.coe_zero] at he
    exact (hScale i).ne' he.symm
  let BA (i : Fin k) := B (A i)
  let BS (i : Fin k) (t : ℝ≥0) (ω : Ω') :=
    (Real.sqrt (scale i:ℝ))⁻¹ * B (S i) (scale i*t) ω
  have hBS (i : Fin k) : IsBrownianReal (BS i) P' := (hB (S i)).smul (hScale0 i)
  have hPair (i : Fin k) : IndepFun (fun ω t => BA i t ω) (fun ω t => BS i t ω) P' := by
    let g (v : ℝ≥0 → ℝ) (t : ℝ≥0) :=
      (Real.sqrt (scale i:ℝ))⁻¹ * v (scale i*t)
    have hg : Measurable g := measurable_pi_lambda _ (fun t =>
      (measurable_pi_apply (scale i*t)).const_mul _)
    exact (hI.indepFun (hAS i i)).comp measurable_id hg
  refine ⟨?_,?_⟩
  · intro i
    let a := Real.sqrt (M.lam i*M.cU2 i)/D.r i
    let b := -Real.sqrt (M.lam i)/D.r i
    have hV : 0 ≤ M.cU2 i := variance_nonneg _ _
    have hW : a^2+b^2=1 := by
      dsimp [a,b]
      rw [div_pow,div_pow,neg_sq,Real.sq_sqrt (mul_nonneg (M.lam_pos i).le hV),
        Real.sq_sqrt (M.lam_pos i).le,← add_div]
      have hEq : (D.r i)^2 = M.lam i*M.cU2 i+M.lam i :=
        Real.sq_sqrt (by positivity [M.lam_pos i,hV])
      rw [← hEq]
      exact div_self (pow_ne_zero _ (D.r_pos i).ne')
    have h := independent_brownian_normalized_linear_combination (BA i) (BS i)
      (hB (A i)) (hBS i) (hPair i) a b hW
    have hEq : (fun t ω => a*BA i t ω+b*BS i t ω) = fun t ω => W t ω i := by
      funext t ω
      have hh : Real.sqrt (M.lam i) = Real.sqrt (M.mu i)*Real.sqrt (scale i:ℝ) := by
        rw [← Real.sqrt_mul (M.mu_pos i).le,hScaleCo]
        congr 1
        unfold SystemSequence.rho
        field_simp [(M.mu_pos i).ne']
      have hp : 0 < Real.sqrt (scale i:ℝ) := Real.sqrt_pos.2 (hScaleCo i ▸ hScale i)
      change a*BA i t ω+b*BS i t ω =
        (Real.sqrt (M.lam i*M.cU2 i)*BA i t ω -
          Real.sqrt (M.mu i)*B (S i) (scale i*t) ω)/D.r i
      dsimp [a,b,BS]
      rw [hh]
      field_simp [hp.ne',(D.r_pos i).ne']
      ring
    exact hEq ▸ h
  · let G (j : Fin (k+k+k)) := MeasurableSpace.comap (fun ω (t : ℝ≥0) => B j t ω) inferInstance
    let U (i : Fin k) : Set (Fin (k+k+k)) := {A i,S i}
    let L (i : Fin k) := ⨆ j ∈ U i, G j
    have hG (j : Fin (k+k+k)) : G j ≤ mΩ' :=
      (measurable_pi_lambda _ (hBm j)).comap_le
    have hU : Pairwise (fun i j => Disjoint (U i) (U j)) := by
      intro i j hij
      apply Set.disjoint_left.2
      intro x hx hy
      simp only [U,mem_insert_iff,mem_singleton_iff] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact hij (hAa (hx.symm.trans hy))
      · exact hAS i j (hx.symm.trans hy)
      · exact hAS j i (hy.symm.trans hx)
      · exact hij (hSa (hx.symm.trans hy))
    have hL : iIndep L P' :=
      independent_disjoint_groups_of_primitive_fields G hG ((iIndepFun_iff_iIndep _ _ _).1 hI) U hU
    apply (iIndepFun_iff_iIndep _ _ _).2
    apply iIndep_of_iIndep_of_le hL
    intro i
    have hA : @Measurable Ω' _ (L i) inferInstance (fun ω (t : ℝ≥0) => B (A i) t ω) :=
      measurable_iff_comap_le.2 (le_iSup₂_of_le (A i) (by simp [U]) le_rfl)
    have hS : @Measurable Ω' _ (L i) inferInstance (fun ω (t : ℝ≥0) => B (S i) t ω) :=
      measurable_iff_comap_le.2 (le_iSup₂_of_le (S i) (by simp [U]) le_rfl)
    letI : MeasurableSpace Ω' := L i
    have hWm : Measurable (fun ω (t : ℝ≥0) => W t ω i) := by
      apply measurable_pi_lambda
      intro t
      exact ((((measurable_pi_apply t).comp hA).const_mul (Real.sqrt (M.lam i*M.cU2 i))).sub
        (((measurable_pi_apply (scale i*t)).comp hS).const_mul (Real.sqrt (M.mu i)))).div_const (D.r i)
    exact hWm.comap_le
