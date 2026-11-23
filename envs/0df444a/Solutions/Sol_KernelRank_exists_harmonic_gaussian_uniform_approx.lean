-- Prove2me | solution 1 for KernelRank.exists_harmonic_gaussian_uniform_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:50:22.150638+00:00
-- url     : https://prove2.me/submissions/0b64e34f-1397-4e2a-be14-b12c618dcb51

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
import Theorems.Thm_KernelRank_IsSumOfProducts_add
import Theorems.Thm_KernelRank_IsSumOfProducts_comp
import Theorems.Thm_KernelRank_IsSumOfProducts_finsetSum
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same


section
open Complex Polynomial
open scoped Topology
namespace KernelRank
section LowerSemicontinuity
end LowerSemicontinuity
section AdjugateBorderRank
end AdjugateBorderRank
section UniversalApproximation
private lemma sum_Icc_neg_eq_zero_add_sum_fin {α : Type*} [AddCommMonoid α] (g : ℤ → α) :
    ∀ M : ℕ, ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), g n =
      g 0 + ∑ m : Fin M, (g ((m : ℕ) + 1 : ℤ) + g (-(((m : ℕ) + 1 : ℕ) : ℤ)))
  | 0 => by simp
  | M + 1 => by
    have hset : Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ) =
        insert ((M + 1 : ℕ) : ℤ)
          (insert (-((M + 1 : ℕ) : ℤ)) (Finset.Icc (-(M : ℤ)) (M : ℤ))) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot1 : -((M + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    have hnot2 : ((M + 1 : ℕ) : ℤ) ∉
        insert (-((M + 1 : ℕ) : ℤ)) (Finset.Icc (-(M : ℤ)) (M : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert hnot2, Finset.sum_insert hnot1,
      sum_Icc_neg_eq_zero_add_sum_fin g M, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have h1 : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by push_cast; rfl
    rw [h1]
    abel
private lemma re_mul_exp_neg_I_mul (z : ℂ) (θ : ℝ) :
    (z * exp (-(I * (θ : ℂ)))).re = (star z * exp (I * (θ : ℂ))).re := by
  have h1 : exp (I * (θ : ℂ)) = Real.cos θ + Real.sin θ * I := by
    rw [mul_comm I (θ : ℂ), exp_mul_I]
    simp
  have h2 : exp (-(I * (θ : ℂ))) = Real.cos θ - Real.sin θ * I := by
    have : -(I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
    simp [sub_eq_add_neg]
  rw [h1, h2]
  simp [Complex.mul_re]
end UniversalApproximation
end KernelRank
end

set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d)
    {ψ : ℝ → ℝ} (hψ_cont : ContinuousOn ψ (Set.Ici 0))
    (hψ_zero : Filter.Tendsto ψ Filter.atTop (𝓝 0))
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ω₀ : ℝ) (M : ℕ) (a₀ : ℝ) (a : Fin M → ℂ),
      0 < ω₀ ∧
      separableRank (fun x : Fin d → ℝ =>
        a₀ * Real.exp (-α * ∑ j, x j ^ 2) +
          ∑ m : Fin M,
            (a m * exp (((-α : ℝ) + I * (((m : ℕ) + 1 : ℝ) * ω₀)) * (∑ j, x j ^ 2 : ℝ))).re) ≤
        (1 + d * M : ℕ) ∧
      ∀ x : Fin d → ℝ,
        |(a₀ * Real.exp (-α * ∑ j, x j ^ 2) +
            ∑ m : Fin M,
              (a m * exp (((-α : ℝ) + I * (((m : ℕ) + 1 : ℝ) * ω₀)) *
                (∑ j, x j ^ 2 : ℝ))).re) -
          ψ (∑ j, x j ^ 2)| < ε := by
  let ψ₀ (s : ℝ) : ℝ := ψ (max s 0)
  have hψ₀_cont : Continuous ψ₀ :=
    hψ_cont.comp_continuous (continuous_id.max continuous_const) fun s => le_max_right s 0
  have hψ₀_eq (s : ℝ) (hs : 0 ≤ s) : ψ₀ s = ψ s := by simp [ψ₀, max_eq_left hs]
  obtain ⟨S₁, hS₁⟩ := Metric.tendsto_atTop.mp hψ_zero (ε / 4) (by positivity)
  let S₀ : ℝ := max S₁ 1
  have hS₀_ge1 : 1 ≤ S₀ := le_max_right S₁ 1
  have hψ_tail (s : ℝ) (hs : S₀ ≤ s) : |ψ₀ s| < ε / 4 := by
    have hs0 : 0 ≤ s := by linarith
    rw [hψ₀_eq s hs0]
    have hd_lt := hS₁ s ((le_max_left S₁ 1).trans hs)
    simpa [Real.dist_eq] using hd_lt
  have hprod_cont : Continuous (fun u : ℝ => Real.exp (α * u) * ψ₀ u) := by fun_prop
  obtain ⟨B_raw, hB_raw⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc 0 (S₀ + 1)) hprod_cont.continuousOn
  let B : ℝ := max B_raw 0
  let M_bound : ℝ := max B |ψ₀ 0| + 1
  have hM_pos : 0 < M_bound := by positivity
  have hlim_exp : Filter.Tendsto (fun t : ℝ => Real.exp (-α * t) * M_bound)
      Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => α * t) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hα Filter.tendsto_id
    have h2 : Filter.Tendsto (fun t : ℝ => Real.exp (-α * t)) Filter.atTop (𝓝 0) := by
      have heq : (fun t : ℝ => Real.exp (-α * t)) = fun t => Real.exp (-(α * t)) := by
        funext t; ring_nf
      rw [heq]
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    simpa using h2.mul_const M_bound
  obtain ⟨T₁, hT₁⟩ := Metric.tendsto_atTop.mp hlim_exp (ε / 4) (by positivity)
  let T : ℝ := max (T₁ + 1) (S₀ + 3)
  have hT_gt : S₀ + 2 < T := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hT_pos : 0 < T := by linarith
  have _ : Fact (0 < T) := ⟨hT_pos⟩
  let ω₀ : ℝ := 2 * Real.pi / T
  have hω₀_pos : 0 < ω₀ := by positivity
  let c₁ (u : ℝ) : ℝ := max 0 (min 1 (S₀ + 1 - u))
  let c₂ (u : ℝ) : ℝ := max 0 (min 1 (u - (T - 1)))
  let g_raw (u : ℝ) : ℝ := c₁ u * (Real.exp (α * u) * ψ₀ u) + c₂ u * ψ₀ 0
  have hg_cont : Continuous g_raw := by dsimp only [g_raw, c₁, c₂]; fun_prop
  have hg_0T : (g_raw 0 : ℂ) = (g_raw T : ℂ) := by
    congr 1
    have hc1_0 : c₁ 0 = 1 := by
      dsimp only [c₁]; rw [min_eq_left (by linarith), max_eq_right zero_le_one]
    have hc2_0 : c₂ 0 = 0 := by
      dsimp only [c₂]; rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    have hc1_T : c₁ T = 0 := by
      dsimp only [c₁]; rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    have hc2_T : c₂ T = 1 := by
      dsimp only [c₂]; rw [show T - (T - 1) = 1 by ring, min_self, max_eq_right zero_le_one]
    simp [g_raw, hc1_0, hc2_0, hc1_T, hc2_T]
  let G : C(AddCircle T, ℂ) :=
    ⟨AddCircle.liftIco T 0 (fun u => (g_raw u : ℂ)),
      AddCircle.liftIco_zero_continuous hg_0T
        (Complex.continuous_ofReal.comp hg_cont).continuousOn⟩
  have hG_bound (z : AddCircle T) : |(G z).re| ≤ M_bound := by
    let u_sub := AddCircle.equivIco T 0 z
    let u : ℝ := u_sub.1
    have hu_mem : u ∈ Set.Ico 0 T := ⟨u_sub.2.1, by linarith [u_sub.2.2]⟩
    have hz_eq : (u : AddCircle T) = z := (AddCircle.equivIco T 0).symm_apply_apply z
    have hGu : G z = (g_raw u : ℂ) := by
      rw [← hz_eq]
      change AddCircle.liftIco T 0 (fun v => (g_raw v : ℂ)) (u : AddCircle T) = _
      exact AddCircle.liftIco_zero_coe_apply hu_mem
    rw [hGu, Complex.ofReal_re]
    have hu0 : 0 ≤ u := hu_mem.1
    by_cases huS : u ≤ S₀ + 1
    · have hc2_z : c₂ u = 0 := by
        dsimp only [c₂]
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      have hc1_b : |c₁ u| ≤ 1 := by
        dsimp only [c₁]
        rw [abs_of_nonneg (le_max_left _ _)]
        exact max_le zero_le_one (min_le_left _ _)
      have hBb : |Real.exp (α * u) * ψ₀ u| ≤ B := by
        have hb := hB_raw u ⟨hu0, huS⟩
        rw [Real.norm_eq_abs] at hb
        exact hb.trans (le_max_left _ _)
      have hterm : |g_raw u| ≤ B := by
        dsimp only [g_raw]
        rw [hc2_z, zero_mul, add_zero, abs_mul]
        calc
          |c₁ u| * |Real.exp (α * u) * ψ₀ u| ≤ 1 * B :=
            mul_le_mul hc1_b hBb (abs_nonneg _) zero_le_one
          _ = B := one_mul B
      exact hterm.trans ((le_max_left B |ψ₀ 0|).trans (by linarith))
    · have hc1_z : c₁ u = 0 := by
        dsimp only [c₁]
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      have hc2_b : |c₂ u| ≤ 1 := by
        dsimp only [c₂]
        rw [abs_of_nonneg (le_max_left _ _)]
        exact max_le zero_le_one (min_le_left _ _)
      have hterm : |g_raw u| ≤ |ψ₀ 0| := by
        dsimp only [g_raw]
        rw [hc1_z, zero_mul, zero_add, abs_mul]
        calc
          |c₂ u| * |ψ₀ 0| ≤ 1 * |ψ₀ 0| :=
            mul_le_mul_of_nonneg_right hc2_b (abs_nonneg _)
          _ = |ψ₀ 0| := one_mul _
      exact hterm.trans ((le_max_right B |ψ₀ 0|).trans (by linarith))
  have hG_mem : G ∈ (Submodule.span ℂ (Set.range (fourier (T := T)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  obtain ⟨P_trig, hP_span, hGP_dist⟩ :=
    Metric.mem_closure_iff.mp hG_mem (ε / 4) (by positivity)
  obtain ⟨c, hc_eq⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hP_span
  let M : ℕ := c.support.sup Int.natAbs
  let a₀ : ℝ := (c 0).re
  let a (m : Fin M) : ℂ := c ((m : ℕ) + 1 : ℤ) + star (c (-(((m : ℕ) + 1 : ℕ) : ℤ)))
  have htrig_re (s : ℝ) : (P_trig (s : AddCircle T)).re =
      a₀ + ∑ m : Fin M, (a m * exp (I * ((((m : ℕ) + 1 : ℝ) * ω₀) * (s : ℂ)))).re := by
    have hP_eval : P_trig (s : AddCircle T) =
        ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), c n * fourier (T := T) n (s : AddCircle T) := by
      rw [← hc_eq]
      change (∑ n ∈ c.support, (c n • fourier (T := T) n)) (s : AddCircle T) = _
      rw [ContinuousMap.coe_sum, Finset.sum_apply]
      simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_subset (fun n hn => ?_) (fun n _ hn => ?_)
      · have hle : n.natAbs ≤ M := Finset.le_sup hn
        rw [Finset.mem_Icc]
        omega
      · have hcz : c n = 0 := Finsupp.notMem_support_iff.mp hn
        simp [hcz]
    rw [hP_eval, Complex.re_sum, sum_Icc_neg_eq_zero_add_sum_fin]
    congr 1
    · simp [a₀]
    · refine Finset.sum_congr rfl fun m _ => ?_
      let θ : ℝ := (((m : ℕ) + 1 : ℝ) * ω₀) * s
      let n_pos : ℤ := (m : ℕ) + 1
      let n_neg : ℤ := -(((m : ℕ) + 1 : ℕ) : ℤ)
      have hpos_arg : 2 * ↑Real.pi * I * (n_pos : ℂ) * (s : ℂ) / (T : ℂ) =
          I * (θ : ℂ) := by
        dsimp only [θ, ω₀, n_pos]
        push_cast
        field_simp [hT_pos.ne']
      have hneg_arg : 2 * ↑Real.pi * I * (n_neg : ℂ) * (s : ℂ) / (T : ℂ) =
          -(I * (θ : ℂ)) := by
        dsimp only [θ, ω₀, n_neg]
        push_cast
        field_simp [hT_pos.ne']
      change (c n_pos * fourier (T := T) n_pos (s : AddCircle T)).re +
          (c n_neg * fourier (T := T) n_neg (s : AddCircle T)).re = _
      rw [fourier_coe_apply, fourier_coe_apply, hpos_arg, hneg_arg, re_mul_exp_neg_I_mul]
      dsimp only [a, n_pos, n_neg, θ]
      rw [← Complex.add_re, ← add_mul]
      congr 2
      push_cast
      rfl
  have hφ_eq (s : ℝ) :
      a₀ * Real.exp (-α * s) +
        ∑ m : Fin M, (a m * exp (((-α : ℝ) + I * (((m : ℕ) + 1 : ℝ) * ω₀)) * (s : ℂ))).re =
      Real.exp (-α * s) * (P_trig (s : AddCircle T)).re := by
    rw [htrig_re s, mul_add, mul_comm a₀ (Real.exp (-α * s)), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    have hexp_split : exp (((-α : ℝ) + I * (((m : ℕ) + 1 : ℝ) * ω₀)) * (s : ℂ)) =
        (Real.exp (-α * s) : ℂ) * exp (I * ((((m : ℕ) + 1 : ℝ) * ω₀) * (s : ℂ))) := by
      rw [add_mul, Complex.exp_add, ← Complex.ofReal_mul, Complex.ofReal_exp]
      congr 2
      push_cast
      ring
    rw [hexp_split, ← mul_assoc, mul_comm (a m) (Real.exp (-α * s) : ℂ), mul_assoc,
      Complex.re_ofReal_mul]
  have hrank : separableRank (fun x : Fin d → ℝ =>
      a₀ * Real.exp (-α * ∑ j, x j ^ 2) +
        ∑ m : Fin M,
          (a m * exp (((-α : ℝ) + I * (((m : ℕ) + 1 : ℝ) * ω₀)) * (∑ j, x j ^ 2 : ℝ))).re) ≤
      (1 + d * M : ℕ) := by
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    obtain ⟨i₀⟩ := ‹Nonempty (Fin d)›
    have h0_prod : IsSumOfProducts
        (fun x : Fin d → ℝ => a₀ * Real.exp (-α * ∑ j, x j ^ 2)) 1 := by
      refine ⟨fun _ j u => (if j = i₀ then a₀ else 1) * Real.exp (-α * u ^ 2), fun x => ?_⟩
      simp only [Fin.sum_univ_one]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]
      congr 1
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
      have her : ∏ j ∈ Finset.univ.erase i₀, (if j = i₀ then a₀ else (1 : ℝ)) = 1 :=
        Finset.prod_eq_one fun j hj => by simp [Finset.ne_of_mem_erase hj]
      simp [her]
    have hm_prod (m : Fin M) : IsSumOfProducts
        (fun x : Fin d → ℝ =>
          (a m * exp (((-α : ℝ) + I * (((m : ℕ) + 1 : ℝ) * ω₀)) * (∑ j, x j ^ 2 : ℝ))).re) d := by
      let rate : ℂ := (-α : ℝ) + I * (((m : ℕ) + 1 : ℝ) * ω₀)
      have hcpx : IsSumOfProducts
          (fun x : Fin d → ℝ => a m * exp (rate * (∑ j, x j ^ 2 : ℝ))) 1 := by
        refine ⟨fun _ j u => (if j = i₀ then a m else 1) * exp (rate * (u ^ 2 : ℝ)), fun x => ?_⟩
        simp only [Fin.sum_univ_one]
        rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
        congr 1
        · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
          have her : ∏ j ∈ Finset.univ.erase i₀, (if j = i₀ then a m else (1 : ℂ)) = 1 :=
            Finset.prod_eq_one fun j hj => by simp [Finset.ne_of_mem_erase hj]
          simp [her]
        · congr 1
          rw [← Finset.mul_sum]
          push_cast
          rfl
      have hre := hcpx.re (by omega)
      rw [one_mul] at hre
      exact hre
    have hsum_prod := IsSumOfProducts.finsetSum hm_prod
    have hcard : (∑ _ : Fin M, d) = d * M := by simp [mul_comm]
    rw [hcard] at hsum_prod
    exact iInf₂_le _ (h0_prod.add hsum_prod)
  refine ⟨ω₀, M, a₀, a, hω₀_pos, hrank, fun x => ?_⟩
  set s := ∑ j : Fin d, x j ^ 2
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => sq_nonneg (x j)
  rw [hφ_eq s, ← hψ₀_eq s hs0]
  have hexp_le1 : Real.exp (-α * s) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have hexp_pos : 0 < Real.exp (-α * s) := Real.exp_pos _
  have htrig_err : |Real.exp (-α * s) * (P_trig (s : AddCircle T)).re -
      Real.exp (-α * s) * (G (s : AddCircle T)).re| < ε / 4 := by
    rw [← mul_sub, abs_mul, abs_of_pos hexp_pos]
    have hpt : |(P_trig (s : AddCircle T)).re - (G (s : AddCircle T)).re| < ε / 4 := by
      have h1 : |(P_trig (s : AddCircle T)).re - (G (s : AddCircle T)).re| ≤
          ‖P_trig (s : AddCircle T) - G (s : AddCircle T)‖ := by
        rw [← Complex.sub_re]
        exact Complex.abs_re_le_norm _
      have h2 : ‖P_trig (s : AddCircle T) - G (s : AddCircle T)‖ ≤ ‖P_trig - G‖ :=
        ContinuousMap.norm_coe_le_norm (P_trig - G) (s : AddCircle T)
      have h3 : ‖P_trig - G‖ < ε / 4 := by
        rwa [dist_comm, dist_eq_norm] at hGP_dist
      exact (h1.trans h2).trans_lt h3
    calc
      Real.exp (-α * s) * |(P_trig (s : AddCircle T)).re - (G (s : AddCircle T)).re|
          ≤ 1 * |(P_trig (s : AddCircle T)).re - (G (s : AddCircle T)).re| :=
        mul_le_mul_of_nonneg_right hexp_le1 (abs_nonneg _)
      _ < ε / 4 := by linarith
  have hG_err : |Real.exp (-α * s) * (G (s : AddCircle T)).re - ψ₀ s| < 3 * (ε / 4) := by
    by_cases hsT : s < T - 1
    · have hs_Ico : s ∈ Set.Ico 0 T := ⟨hs0, by linarith⟩
      have hGs : (G (s : AddCircle T)).re = g_raw s := by
        have hcoe : G (s : AddCircle T) = (g_raw s : ℂ) := by
          simpa [G] using AddCircle.liftIco_zero_coe_apply (p := T)
            (f := fun v => (g_raw v : ℂ)) hs_Ico
        rw [hcoe, Complex.ofReal_re]
      rw [hGs]
      have hc2_z : c₂ s = 0 := by
        dsimp only [c₂]
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      have hg_s : Real.exp (-α * s) * g_raw s = c₁ s * ψ₀ s := by
        dsimp only [g_raw]
        rw [hc2_z, zero_mul, add_zero, ← mul_assoc, mul_comm (Real.exp (-α * s)) (c₁ s),
          mul_assoc, ← mul_assoc (Real.exp (-α * s)), ← Real.exp_add]
        have : -α * s + α * s = 0 := by ring
        rw [this, Real.exp_zero, one_mul]
      rw [hg_s]
      by_cases hsS : s ≤ S₀
      · have hc1_1 : c₁ s = 1 := by
          dsimp only [c₁]
          rw [min_eq_left (by linarith), max_eq_right zero_le_one]
        rw [hc1_1, one_mul, sub_self, abs_zero]
        positivity
      · push Not at hsS
        have hc1_01 : 0 ≤ c₁ s ∧ c₁ s ≤ 1 := by
          dsimp only [c₁]
          exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
        have hsub : |c₁ s * ψ₀ s - ψ₀ s| ≤ |ψ₀ s| := by
          rw [show c₁ s * ψ₀ s - ψ₀ s = (c₁ s - 1) * ψ₀ s by ring, abs_mul]
          have : |c₁ s - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
          calc
            |c₁ s - 1| * |ψ₀ s| ≤ 1 * |ψ₀ s| :=
              mul_le_mul_of_nonneg_right this (abs_nonneg _)
            _ = |ψ₀ s| := one_mul _
        exact (hsub.trans_lt (hψ_tail s hsS.le)).trans (by linarith)
    · push Not at hsT
      have hsS : S₀ ≤ s := by linarith
      have hsT1 : T₁ ≤ s := by
        have : T₁ + 1 ≤ T := le_max_left _ _
        linarith
      have hexp_tail : Real.exp (-α * s) * M_bound < ε / 4 := by
        have hd_lt := hT₁ s hsT1
        rw [Real.dist_eq, sub_zero, abs_of_pos (mul_pos hexp_pos hM_pos)] at hd_lt
        exact hd_lt
      have h1 : |Real.exp (-α * s) * (G (s : AddCircle T)).re| < ε / 4 := by
        rw [abs_mul, abs_of_pos hexp_pos]
        exact (mul_le_mul_of_nonneg_left (hG_bound _) hexp_pos.le).trans_lt hexp_tail
      have h2 : |ψ₀ s| < ε / 4 := hψ_tail s hsS
      have htri : |Real.exp (-α * s) * (G (s : AddCircle T)).re - ψ₀ s| ≤
          |Real.exp (-α * s) * (G (s : AddCircle T)).re| + |ψ₀ s| := abs_sub _ _
      linarith
  have htri_tot : |Real.exp (-α * s) * (P_trig (s : AddCircle T)).re - ψ₀ s| ≤
      |Real.exp (-α * s) * (P_trig (s : AddCircle T)).re -
        Real.exp (-α * s) * (G (s : AddCircle T)).re| +
      |Real.exp (-α * s) * (G (s : AddCircle T)).re - ψ₀ s| := by
    simpa using abs_add_le
      (Real.exp (-α * s) * (P_trig (s : AddCircle T)).re -
        Real.exp (-α * s) * (G (s : AddCircle T)).re)
      (Real.exp (-α * s) * (G (s : AddCircle T)).re - ψ₀ s)
  linarith
end KernelRank
