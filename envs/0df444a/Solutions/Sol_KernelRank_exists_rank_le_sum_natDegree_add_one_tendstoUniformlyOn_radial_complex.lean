-- Prove2me | solution 1 for KernelRank.exists_rank_le_sum_natDegree_add_one_tendstoUniformlyOn_radial_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:48:10.92179+00:00
-- url     : https://prove2.me/submissions/2a88a382-07d7-4d20-8467-a7bf20483a8b

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
import Theorems.Thm_KernelRank_IsSumOfProducts_add
import Theorems.Thm_KernelRank_IsSumOfProducts_comp
import Theorems.Thm_KernelRank_IsSumOfProducts_finsetSum
import Theorems.Thm_KernelRank_abs_exp_sub_one_sub_le
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same



set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank
namespace KernelRank
theorem _root_.solution
    {d : ℕ} (hd : 2 ≤ d) (S : Finset ℂ) (P : ℂ → ℂ[X]) :
    ∃ F : ℝ → (Fin d → ℝ) → ℂ,
      (∀ h, separableRank (F h) ≤ (∑ μ ∈ S, ((P μ).natDegree + 1) : ℕ)) ∧
      ∀ C : Set (Fin d → ℝ), IsCompact C →
        TendstoUniformlyOn F (fun x => ∑ μ ∈ S, expPoly (P μ) μ (∑ j, x j ^ 2))
          (𝓝[≠] (0 : ℝ)) C := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i₀⟩ := ‹Nonempty (Fin d)›
  let Fμ (μ : ℂ) (h : ℝ) (x : Fin d → ℝ) : ℂ :=
    (P μ).eval ((h⁻¹ * (Real.exp (h * ∑ j, x j ^ 2) - 1) : ℝ) : ℂ) *
      exp (μ * (∑ j, x j ^ 2 : ℝ))
  have hFμ_prod (μ : ℂ) (h : ℝ) : IsSumOfProducts (Fμ μ h) ((P μ).natDegree + 1) := by
    let k := (P μ).natDegree
    let L_C : ℂ[X] := Polynomial.C (-(h : ℂ)⁻¹) + Polynomial.C ((h : ℂ)⁻¹) * Polynomial.X
    have hLC_deg : L_C.natDegree ≤ 1 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
      simpa using (Polynomial.natDegree_C_mul_X_pow_le ((h : ℂ)⁻¹) 1)
    let Q_C : ℂ[X] := (P μ).comp L_C
    have hQC_deg : Q_C.natDegree < k + 1 := by
      refine Nat.lt_succ_of_le (Polynomial.natDegree_comp_le.trans ?_)
      exact (Nat.mul_le_mul le_rfl hLC_deg).trans (by simp [k])
    refine ⟨fun m j u =>
      (if j = i₀ then Q_C.coeff m else 1) *
        exp ((μ + (m : ℕ) * (h : ℂ)) * (u ^ 2 : ℝ)), fun x => ?_⟩
    dsimp only [Fμ]
    set s := ∑ j : Fin d, x j ^ 2
    let u_s : ℝ := h⁻¹ * (Real.exp (h * s) - 1)
    have hLC_eval : L_C.eval (exp ((h : ℂ) * (s : ℂ))) = (u_s : ℂ) := by
      simp only [L_C, u_s, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_X, ← Complex.ofReal_mul]
      rw [← Complex.ofReal_exp]
      push_cast
      ring
    rw [← hLC_eval, ← Polynomial.eval_comp, Polynomial.eval_eq_sum_range' hQC_deg,
      ← Fin.sum_univ_eq_sum_range (fun m => Q_C.coeff m * exp ((h : ℂ) * (s : ℂ)) ^ m) (k + 1),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hprod : (∏ j : Fin d,
        (if j = i₀ then Q_C.coeff m else 1) *
          exp ((μ + (m : ℕ) * (h : ℂ)) * (x j ^ 2 : ℝ))) =
        Q_C.coeff m * ∏ j : Fin d, exp ((μ + (m : ℕ) * (h : ℂ)) * (x j ^ 2 : ℝ)) := by
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
      have her : ∏ j ∈ Finset.univ.erase i₀, (if j = i₀ then Q_C.coeff m else (1 : ℂ)) = 1 :=
        Finset.prod_eq_one fun j hj => by simp [Finset.ne_of_mem_erase hj]
      simp [her]
    rw [hprod, ← Complex.exp_sum, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
    have hs_cast : (∑ j : Fin d, (μ + (m : ℕ) * (h : ℂ)) * (x j ^ 2 : ℝ)) =
        (μ + (m : ℕ) * (h : ℂ)) * (s : ℂ) := by
      rw [← Finset.mul_sum]
      push_cast [s]
      rfl
    rw [hs_cast]
    have : (m : ℕ) * ((h : ℂ) * (s : ℂ)) + μ * (s : ℂ) =
        (μ + (m : ℕ) * (h : ℂ)) * (s : ℂ) := by ring
    rw [this]
  refine ⟨fun h x => ∑ μ ∈ S, Fμ μ h x, fun h => ?_, fun C hC => ?_⟩
  · have hsum := IsSumOfProducts.finsetSum (α := S)
      (K := fun μ : S => Fμ μ.1 h) (N := fun μ : S => (P μ.1).natDegree + 1)
      (fun μ => hFμ_prod μ.1 h)
    have hfun : (fun x : Fin d → ℝ => ∑ μ : S, Fμ μ.1 h x) = fun x => ∑ μ ∈ S, Fμ μ h x := by
      funext x
      exact Finset.sum_coe_sort S (fun μ => Fμ μ h x)
    have hcost : (∑ μ : S, ((P μ.1).natDegree + 1)) = ∑ μ ∈ S, ((P μ).natDegree + 1) :=
      Finset.sum_coe_sort S (fun μ => (P μ).natDegree + 1)
    rw [hfun, hcost] at hsum
    exact iInf₂_le _ hsum
  · have hμ_tend (μ : ℂ) : TendstoUniformlyOn (Fμ μ)
        (fun x : Fin d → ℝ => expPoly (P μ) μ (∑ j, x j ^ 2)) (𝓝[≠] (0 : ℝ)) C := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hcontS : Continuous (fun x : Fin d → ℝ => ∑ j : Fin d, x j ^ 2) := by fun_prop
      obtain ⟨B, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ C, ∑ j : Fin d, x j ^ 2 ≤ B := by
        rcases C.eq_empty_or_nonempty with rfl | hne
        · exact ⟨0, le_rfl, by simp⟩
        · obtain ⟨x₀, _, hmax⟩ := hC.exists_isMaxOn hne hcontS.continuousOn
          exact ⟨∑ j : Fin d, x₀ j ^ 2,
            Finset.sum_nonneg fun j _ => sq_nonneg (x₀ j), fun x hx => hmax hx⟩
      let g (p : ℝ × ℝ) : ℂ := (P μ).eval (p.1 : ℂ) * exp (μ * (p.2 : ℂ))
      have hg_cont : Continuous g :=
        ((P μ).continuous_aeval.comp (Complex.continuous_ofReal.comp continuous_fst)).mul
          (Complex.continuous_exp.comp
            (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)))
      let K_box : Set (ℝ × ℝ) := Set.Icc (-1) (B + 1) ×ˢ Set.Icc 0 B
      obtain ⟨δ_u, hδ_u_pos, hδ_u⟩ := Metric.uniformContinuousOn_iff.mp
        ((isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hg_cont.continuousOn)
        ε hε
      let M_B : ℝ := max 1 ((B + 1) ^ 2 * Real.exp (B + 1))
      have hM_B_pos : 0 < M_B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      let η : ℝ := min 1 (min δ_u 1 / (2 * M_B))
      have hη_pos : 0 < η :=
        lt_min zero_lt_one (div_pos (lt_min hδ_u_pos zero_lt_one) (mul_pos zero_lt_two hM_B_pos))
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hη_pos)] with h hh0 hball x hxC
      have hhη : |h| < η := by simpa [Real.dist_eq] using hball
      set s := ∑ j : Fin d, x j ^ 2
      have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => sq_nonneg (x j)
      have hsB : s ≤ B := hB.2 x hxC
      have hh1 : |h| ≤ 1 := le_of_lt (lt_of_lt_of_le hhη (min_le_left _ _))
      let u_s : ℝ := h⁻¹ * (Real.exp (h * s) - 1)
      have hu_diff : |u_s - s| < min δ_u 1 := by
        have hh0' : h ≠ 0 := hh0
        have hh_pos : 0 < |h| := abs_pos.mpr hh0'
        have hsub : u_s - s = h⁻¹ * (Real.exp (h * s) - 1 - h * s) := by
          dsimp only [u_s]; field_simp [hh0']
        have habs_hs : |h * s| ≤ B + 1 := by
          rw [abs_mul, abs_of_nonneg hs0]; nlinarith
        have hexp_b := abs_exp_sub_one_sub_le (h * s)
        have hrem : |u_s - s| ≤ |h| * M_B := by
          rw [hsub, abs_mul, abs_inv]
          calc
            |h|⁻¹ * |Real.exp (h * s) - 1 - h * s|
                ≤ |h|⁻¹ * ((h * s) ^ 2 * Real.exp |h * s|) := by gcongr
            _ = |h| * (s ^ 2 * Real.exp |h * s|) := by
                have : (h * s) ^ 2 = |h| * |h| * s ^ 2 := by rw [mul_pow, ← sq_abs h, sq]
                rw [this]; field_simp [hh_pos.ne']
            _ ≤ |h| * ((B + 1) ^ 2 * Real.exp (B + 1)) := by
                refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg h)
                exact mul_le_mul (pow_le_pow_left₀ hs0 (by linarith) 2)
                  (Real.exp_le_exp.mpr habs_hs) (Real.exp_pos _).le (sq_nonneg _)
            _ ≤ |h| * M_B := mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg h)
        calc
          |u_s - s| ≤ |h| * M_B := hrem
          _ < η * M_B := mul_lt_mul_of_pos_right hhη hM_B_pos
          _ ≤ (min δ_u 1 / (2 * M_B)) * M_B :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hM_B_pos.le
          _ = min δ_u 1 / 2 := by field_simp [hM_B_pos.ne']
          _ < min δ_u 1 := half_lt_self (lt_min hδ_u_pos zero_lt_one)
      have hu_box : (u_s, s) ∈ K_box := by
        have hu1 : |u_s - s| ≤ 1 := le_of_lt (lt_of_lt_of_le hu_diff (min_le_right _ _))
        rw [abs_le] at hu1
        exact ⟨⟨by linarith, by linarith⟩, ⟨hs0, hsB⟩⟩
      have hs_box : (s, s) ∈ K_box := ⟨⟨by linarith, by linarith⟩, ⟨hs0, hsB⟩⟩
      have hdist : dist (s, s) (u_s, s) < δ_u := by
        rw [Prod.dist_eq]
        simp only [dist_self, max_eq_left dist_nonneg]
        rw [Real.dist_eq, abs_sub_comm]
        exact lt_of_lt_of_le hu_diff (min_le_left _ _)
      exact hδ_u (s, s) hs_box (u_s, s) hu_box hdist
    clear * - hμ_tend
    induction S using Finset.cons_induction with
    | empty =>
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      exact Filter.Eventually.of_forall fun _ _ _ => by simpa using hε
    | cons μ S hnot ih =>
      simp_rw [Finset.sum_cons]
      exact (hμ_tend μ).add ih
end KernelRank
