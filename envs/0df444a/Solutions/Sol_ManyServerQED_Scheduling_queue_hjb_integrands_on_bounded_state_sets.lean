-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_integrands_on_bounded_state_sets
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:54:54.612612+00:00
-- url     : https://prove2.me/submissions/ff74c9cd-6ea6-4248-99aa-e6758d593a33

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
open Filter Topology Set MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

set_option maxHeartbeats 1200000 in
theorem solution {k : ℕ}
    (D : DiffusionData k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (ϱ mL : ℝ) (hA2 : Assumption2 Lt ϱ mL) (f : (Fin k → ℝ) → ℝ)
    (hH : IsHJBSolution D (costOfTilde Lt) γ f) :
    let L := costOfTilde Lt
    let c (t : ℝ) (z u : Fin k → ℝ) := Real.exp (-γ*t)*L z u
    let g (t : ℝ) (z u : Fin k → ℝ) := Real.exp (-γ*t)*
      ((∑ i, drift D z u i*grad f z i)+L z u-hamiltonian D L z (grad f z))
    Continuous (Function.uncurry L) ∧
    Continuous (Function.uncurry (fun t => Function.uncurry (c t))) ∧
    Continuous (Function.uncurry (fun t => Function.uncurry (g t))) ∧
    (∀ t z u, u ∈ stdSimplex ℝ (Fin k) → 0 ≤ c t z u ∧ 0 ≤ g t z u) ∧
    (∃ a > 0, ∀ z u, u ∈ stdSimplex ℝ (Fin k) →
      ∀ i, |drift D z u i| ≤ a*(1+l1norm z)) ∧
    ∀ T B : ℝ, ∃ A > 0, ∀ t ∈ Icc (0:ℝ) T, ∀ z u,
      ‖z‖ ≤ B → u ∈ stdSimplex ℝ (Fin k) →
      (∀ i, |drift D z u i| ≤ A) ∧ |c t z u| ≤ A ∧ |g t z u| ≤ A := by
  intro L c g
  have hL : Continuous (Function.uncurry L) := by
    let g (p : (Fin k → ℝ) × (Fin k → ℝ)) :=
      (max (∑ j, p.1 j) 0 • p.2,p.1-max (∑ j, p.1 j) 0 • p.2)
    have hg : Continuous g := by unfold g; fun_prop
    exact hA2.tilde_cont.comp hg
  have hb : Continuous (fun p : (Fin k → ℝ) × (Fin k → ℝ) => drift D p.1 p.2) := by
    unfold drift
    fun_prop
  have hgrad : Continuous (grad f) := by
    apply continuous_pi
    intro i
    exact (hH.1.continuous_fderiv two_ne_zero).clm_apply continuous_const
  have hHam : Continuous (fun z => hamiltonian D L z (grad f z)) := by
    have he (z : Fin k → ℝ) :
        hamiltonian D L z (grad f z) = γ*f z -
          (1/2)*∑ i, D.r i^2 * iteratedFDeriv ℝ 2 f z (fun _ => Pi.single i 1) := by
      linarith only [hH.2 z]
    simp_rw [he]
    have hD2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
      (hH.1.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
    have ht (i : Fin k) : Continuous (fun z => iteratedFDeriv ℝ 2 f z (fun _ => Pi.single i 1)) := by
      simp_rw [iteratedFDeriv_two_apply]
      exact (hD2.clm_apply continuous_const).clm_apply continuous_const
    exact (hH.1.continuous.const_mul _).sub
      ((continuous_finsetSum _ fun i _ => (ht i).const_mul (D.r i ^ 2)).const_mul _)
  have hdis : Continuous (fun t : ℝ => Real.exp (-γ*t)) := by fun_prop
  have hc : Continuous (Function.uncurry (fun t => Function.uncurry (c t))) := by
    exact (hdis.comp continuous_fst).mul (hL.comp continuous_snd)
  have hg : Continuous (Function.uncurry (fun t => Function.uncurry (g t))) := by
    have hd : Continuous (fun p : ℝ × ((Fin k → ℝ) × (Fin k → ℝ)) =>
        ∑ i, drift D p.2.1 p.2.2 i*grad f p.2.1 i) := by
      apply continuous_finsetSum
      intro i _
      exact ((continuous_apply i).comp (hb.comp continuous_snd)).mul
        ((continuous_apply i).comp (hgrad.comp (continuous_fst.comp continuous_snd)))
    exact (hdis.comp continuous_fst).mul ((hd.add (hL.comp continuous_snd)).sub
      (hHam.comp (continuous_fst.comp continuous_snd)))
  have hNonneg (t : ℝ) (z u : Fin k → ℝ) (hu : u ∈ stdSimplex ℝ (Fin k)) :
      0 ≤ c t z u ∧ 0 ≤ g t z u := by
    refine ⟨mul_nonneg (Real.exp_nonneg _) (hA2.cost.nonneg z u hu),?_⟩
    apply mul_nonneg (Real.exp_nonneg _)
    apply sub_nonneg.2
    unfold hamiltonian
    apply ciInf_le _ (⟨u,hu⟩ : stdSimplex ℝ (Fin k))
    let q (u : Fin k → ℝ) := (∑ i, drift D z u i*grad f z i)+L z u
    have hq : Continuous q := by
      apply Continuous.add _ (hL.comp (continuous_const.prodMk continuous_id))
      apply continuous_finsetSum
      intro i _
      exact (((continuous_apply i).comp hb).comp (continuous_const.prodMk continuous_id)).mul_const _
    have hB := (isCompact_stdSimplex (𝕜 := ℝ) (ι := Fin k)).image hq
    change BddBelow (range (fun (v : stdSimplex ℝ (Fin k)) => q v))
    refine hB.bddBelow.mono ?_
    rintro _ ⟨v,rfl⟩
    exact ⟨v.1,v.2,rfl⟩
  have hLinear : ∃ a > 0, ∀ z u, u ∈ stdSimplex ℝ (Fin k) →
      ∀ i, |drift D z u i| ≤ a*(1+l1norm z) := by
    let a : ℝ := 1+∑ i, (|D.ell i|+|D.mu i-D.theta i|+|D.mu i|)
    have hA (i : Fin k) : |D.ell i|+|D.mu i-D.theta i|+|D.mu i| ≤ a := by
      have h := single_le_sum (f := fun i => |D.ell i|+|D.mu i-D.theta i|+|D.mu i|)
        (fun j _ => by positivity) (mem_univ i)
      dsimp [a]
      linarith
    refine ⟨a,by dsimp [a]; positivity,?_⟩
    intro z u hu i
    have hZ : 0 ≤ l1norm z := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hz (i : Fin k) : |z i| ≤ l1norm z :=
      single_le_sum (f := fun j => |z j|) (fun _ _ => abs_nonneg _) (mem_univ i)
    have hU : |u i| ≤ 1 := by
      rw [abs_of_nonneg (hu.1 i)]
      rw [← hu.2]
      exact single_le_sum (fun j _ => hu.1 j) (mem_univ i)
    have hsum : max (∑ j, z j) 0 ≤ l1norm z := by
      apply max_le _ hZ
      exact sum_le_sum (fun j _ => le_abs_self (z j))
    have hmax : 0 ≤ max (∑ j, z j) 0 := le_max_right _ _
    have hm : |(D.mu i-D.theta i)*max (∑ j, z j) 0*u i| ≤
        |D.mu i-D.theta i| *l1norm z := by
      rw [abs_mul,abs_mul,abs_of_nonneg hmax]
      calc
        _ ≤ (|D.mu i-D.theta i| * max (∑ j, z j) 0)*1 :=
          mul_le_mul_of_nonneg_left hU (mul_nonneg (abs_nonneg _) hmax)
        _ ≤ _ := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    have hD2 := mul_le_mul_of_nonneg_left (hz i) (abs_nonneg (D.mu i))
    have hA' : |D.mu i-D.theta i|+|D.mu i| ≤ a := by
      linarith [hA i,abs_nonneg (D.ell i)]
    have hEll : |D.ell i| ≤ a := by
      linarith [hA i,abs_nonneg (D.mu i-D.theta i),abs_nonneg (D.mu i)]
    have hD3 := mul_le_mul_of_nonneg_right hA' hZ
    rw [add_mul] at hD3
    have h := (abs_sub (D.ell i + (D.mu i-D.theta i)*max (∑ j, z j) 0*u i)
      (D.mu i*z i)).trans
      (add_le_add_left (abs_add_le _ _) _)
    rw [abs_mul (D.mu i) (z i)] at h
    unfold drift
    rw [mul_add,mul_one]
    linarith only [h,hm,hD2,hD3,hEll]
  refine ⟨hL,hc,hg,hNonneg,hLinear,?_⟩
  intro T B
  let S := Set.prod (Set.Icc (0:ℝ) T) (Set.prod (Metric.closedBall (0 : Fin k → ℝ) B) (stdSimplex ℝ (Fin k)))
  have hS : IsCompact S := isCompact_Icc.prod
    ((isCompact_closedBall _ _).prod (isCompact_stdSimplex (𝕜 := ℝ) (ι := Fin k)))
  let bnd (p : ℝ × ((Fin k → ℝ) × (Fin k → ℝ))) :=
    ‖drift D p.2.1 p.2.2‖ + |c p.1 p.2.1 p.2.2| + |g p.1 p.2.1 p.2.2|
  have hBnd : Continuous bnd := ((hb.comp continuous_snd).norm.add hc.abs).add hg.abs
  obtain ⟨C,hC⟩ := (hS.image hBnd).bddAbove
  refine ⟨max C 0+1,by linarith [le_max_right C 0],?_⟩
  intro t ht z u hz hu
  have h := hC (show bnd (t,z,u) ∈ bnd '' S from
    ⟨(t,z,u),⟨ht,by simpa only [Metric.mem_closedBall,dist_zero_right],hu⟩,rfl⟩)
  change ‖drift D z u‖ + |c t z u| + |g t z u| ≤ C at h
  have hA := le_max_left C 0
  refine ⟨fun i => ?_,by linarith [norm_nonneg (drift D z u),abs_nonneg (g t z u)],
    by linarith [norm_nonneg (drift D z u),abs_nonneg (c t z u)]⟩
  have hh := norm_le_pi_norm (drift D z u) i
  rw [Real.norm_eq_abs] at hh
  linarith [abs_nonneg (c t z u),abs_nonneg (g t z u)]
