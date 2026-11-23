-- Prove2me | solution 1 for KernelRank.exists_rank_le_borderTotalCost_tendstoUniformlyOn_radial_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:40:46.766537+00:00
-- url     : https://prove2.me/submissions/d2c46994-e82c-4e7c-8bf5-1351ef0c5982

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
import Theorems.Thm_KernelRank_abs_exp_sub_one_sub_le
import Theorems.Thm_KernelRank_IsSumOfProducts_add
import Theorems.Thm_KernelRank_IsSumOfProducts_comp
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same


section
open Complex Polynomial Filter Topology
namespace KernelRank
private lemma natDegree_C_add_C_mul_X_le {R : Type*} [Semiring R] (a b : R) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
  simpa using (Polynomial.natDegree_C_mul_X_pow_le b 1)
private lemma isSumOfProducts_component_expDiff {d : ℕ} (hd : 2 ≤ d) (c : Component)
    (hc : c.WellFormed) (h : ℝ) :
    IsSumOfProducts
      (fun x : Fin d → ℝ =>
        (c.poly.eval ((h⁻¹ * (Real.exp (h * ∑ j, x j ^ 2) - 1) : ℝ) : ℂ) *
          exp (c.rate * (∑ j, x j ^ 2 : ℝ))).re)
      (c.borderCost d) := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i₀⟩ := ‹Nonempty (Fin d)›
  let k := c.poly.natDegree
  by_cases him : c.rate.im = 0
  · have hcost : c.borderCost d = k + 1 := by simp [Component.borderCost, him, k]
    rw [hcost]
    have hcoeff_im : ∀ q, (c.poly.coeff q).im = 0 := hc.2.2 him
    let P_R : ℝ[X] :=
      ∑ q ∈ Finset.range (k + 1), Polynomial.C (c.poly.coeff q).re * Polynomial.X ^ q
    have hPR_deg : P_R.natDegree ≤ k := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun q hq => ?_
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq))
    let L_R : ℝ[X] := Polynomial.C (-h⁻¹) + Polynomial.C h⁻¹ * Polynomial.X
    have hLR_deg : L_R.natDegree ≤ 1 := natDegree_C_add_C_mul_X_le _ _
    let Q_R : ℝ[X] := P_R.comp L_R
    have hQR_deg : Q_R.natDegree < k + 1 := by
      refine Nat.lt_succ_of_le (Polynomial.natDegree_comp_le.trans ?_)
      exact (Nat.mul_le_mul hPR_deg hLR_deg).trans (by simp)
    have hrate_eq : c.rate = (c.rate.re : ℂ) := by
      apply Complex.ext <;> simp [him]
    have hpoly_eq (u : ℝ) : c.poly.eval (u : ℂ) = ((P_R.eval u : ℝ) : ℂ) := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self k)]
      change _ = (((Polynomial.evalRingHom u) P_R : ℝ) : ℂ)
      simp only [P_R, map_sum, Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Complex.ofReal_sum, Complex.ofReal_mul,
        Complex.ofReal_pow]
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 1
      apply Complex.ext <;> simp [hcoeff_im q]
    refine ⟨fun m j u =>
      (if j = i₀ then Q_R.coeff m else 1) *
        Real.exp ((c.rate.re + (m : ℕ) * h) * u ^ 2), fun x => ?_⟩
    dsimp only
    set s := ∑ j : Fin d, x j ^ 2
    let u_s : ℝ := h⁻¹ * (Real.exp (h * s) - 1)
    have hexp_re : exp (c.rate * (s : ℂ)) = (Real.exp (c.rate.re * s) : ℂ) := by
      conv_lhs => rw [hrate_eq]
      rw [← Complex.ofReal_mul, Complex.ofReal_exp]
    change (c.poly.eval (u_s : ℂ) * exp (c.rate * (s : ℂ))).re = _
    rw [hpoly_eq u_s, hexp_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hLR_eval : L_R.eval (Real.exp (h * s)) = u_s := by
      simp [L_R, u_s]
      ring
    have hQR_eval : P_R.eval u_s = ∑ m : Fin (k + 1), Q_R.coeff m * Real.exp (h * s) ^ (m : ℕ) := by
      rw [← hLR_eval, ← Polynomial.eval_comp,
        Polynomial.eval_eq_sum_range' hQR_deg,
        Fin.sum_univ_eq_sum_range (fun m => Q_R.coeff m * Real.exp (h * s) ^ m) (k + 1)]
    rw [hQR_eval, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hprod : (∏ j : Fin d,
        (if j = i₀ then Q_R.coeff m else 1) *
          Real.exp ((c.rate.re + (m : ℕ) * h) * x j ^ 2)) =
        Q_R.coeff m * ∏ j : Fin d, Real.exp ((c.rate.re + (m : ℕ) * h) * x j ^ 2) := by
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
      have her : ∏ j ∈ Finset.univ.erase i₀, (if j = i₀ then Q_R.coeff m else (1 : ℝ)) = 1 :=
        Finset.prod_eq_one fun j hj => by simp [Finset.ne_of_mem_erase hj]
      simp [her]
    rw [hprod, ← Real.exp_sum, ← Finset.mul_sum, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    have : (m : ℕ) * (h * s) + c.rate.re * s = (c.rate.re + (m : ℕ) * h) * s := by ring
    rw [this]
  · have hcost : c.borderCost d = (k + 1) * d := by
      simp [Component.borderCost, him, k, mul_comm]
    rw [hcost]
    let L_C : ℂ[X] := Polynomial.C (-(h : ℂ)⁻¹) + Polynomial.C ((h : ℂ)⁻¹) * Polynomial.X
    have hLC_deg : L_C.natDegree ≤ 1 := natDegree_C_add_C_mul_X_le _ _
    let Q_C : ℂ[X] := c.poly.comp L_C
    have hQC_deg : Q_C.natDegree < k + 1 := by
      refine Nat.lt_succ_of_le (Polynomial.natDegree_comp_le.trans ?_)
      exact (Nat.mul_le_mul le_rfl hLC_deg).trans (by simp [k])
    have hcpx : IsSumOfProducts
        (fun x : Fin d → ℝ =>
          c.poly.eval ((h⁻¹ * (Real.exp (h * ∑ j, x j ^ 2) - 1) : ℝ) : ℂ) *
            exp (c.rate * (∑ j, x j ^ 2 : ℝ)))
        (k + 1) := by
      refine ⟨fun m j u =>
        (if j = i₀ then Q_C.coeff m else 1) *
          exp ((c.rate + (m : ℕ) * (h : ℂ)) * (u ^ 2 : ℝ)), fun x => ?_⟩
      dsimp only
      set s := ∑ j : Fin d, x j ^ 2
      let u_s : ℝ := h⁻¹ * (Real.exp (h * s) - 1)
      have hLC_eval : L_C.eval (exp ((h : ℂ) * (s : ℂ))) = (u_s : ℂ) := by
        simp only [L_C, u_s, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
          Polynomial.eval_X, ← Complex.ofReal_mul]
        rw [← Complex.ofReal_exp]
        push_cast
        ring
      change c.poly.eval (u_s : ℂ) * exp (c.rate * (s : ℂ)) = _
      rw [← hLC_eval, ← Polynomial.eval_comp, Polynomial.eval_eq_sum_range' hQC_deg,
        ← Fin.sum_univ_eq_sum_range (fun m => Q_C.coeff m * exp ((h : ℂ) * (s : ℂ)) ^ m) (k + 1),
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hprod : (∏ j : Fin d,
          (if j = i₀ then Q_C.coeff m else 1) *
            exp ((c.rate + (m : ℕ) * (h : ℂ)) * (x j ^ 2 : ℝ))) =
          Q_C.coeff m * ∏ j : Fin d, exp ((c.rate + (m : ℕ) * (h : ℂ)) * (x j ^ 2 : ℝ)) := by
        rw [Finset.prod_mul_distrib]
        congr 1
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
        have her : ∏ j ∈ Finset.univ.erase i₀, (if j = i₀ then Q_C.coeff m else (1 : ℂ)) = 1 :=
          Finset.prod_eq_one fun j hj => by simp [Finset.ne_of_mem_erase hj]
        simp [her]
      rw [hprod, ← Complex.exp_sum, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
      have hs_cast : (∑ j : Fin d, (c.rate + (m : ℕ) * (h : ℂ)) * (x j ^ 2 : ℝ)) =
          (c.rate + (m : ℕ) * (h : ℂ)) * (s : ℂ) := by
        rw [← Finset.mul_sum]
        push_cast [s]
        rfl
      rw [hs_cast]
      have : (m : ℕ) * ((h : ℂ) * (s : ℂ)) + c.rate * (s : ℂ) =
          (c.rate + (m : ℕ) * (h : ℂ)) * (s : ℂ) := by ring
      rw [this]
    exact hcpx.re (by omega)
private lemma exists_isSumOfProducts_borderTotalCost_tendstoUniformlyOn
    {d : ℕ} (hd : 2 ≤ d) (cs : List Component) (hcs : ∀ c ∈ cs, c.WellFormed) :
    ∃ F : ℝ → (Fin d → ℝ) → ℝ,
      (∀ h, IsSumOfProducts (F h) (borderTotalCost d cs)) ∧
      ∀ C : Set (Fin d → ℝ), IsCompact C →
        TendstoUniformlyOn F (fun x => profile cs (∑ j, x j ^ 2)) (𝓝[≠] (0 : ℝ)) C := by
  induction cs with
  | nil =>
    refine ⟨fun _ _ => 0, fun _ => ?_, fun C _ => ?_⟩
    · dsimp only [borderTotalCost, List.map_nil, List.sum_nil]
      exact ⟨fun n => n.elim0, fun _ => by
        symm
        apply Finset.sum_eq_zero
        intro i _
        exact Fin.elim0 i⟩
    · rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      exact Filter.Eventually.of_forall fun _ _ _ => by simpa [profile] using hε
  | cons c cs ih =>
    have hc : c.WellFormed := hcs c List.mem_cons_self
    have hcs' : ∀ c' ∈ cs, c'.WellFormed := fun c' hc' => hcs c' (List.mem_cons_of_mem c hc')
    obtain ⟨F', hrank', htend'⟩ := ih hcs'
    let Fc (h : ℝ) (x : Fin d → ℝ) : ℝ :=
      (c.poly.eval ((h⁻¹ * (Real.exp (h * ∑ j, x j ^ 2) - 1) : ℝ) : ℂ) *
        exp (c.rate * (∑ j, x j ^ 2 : ℝ))).re
    refine ⟨fun h x => Fc h x + F' h x, fun h => ?_, fun C hC => ?_⟩
    · exact (isSumOfProducts_component_expDiff hd c hc h).add (hrank' h)
    · have hFc_tend : TendstoUniformlyOn Fc (fun x => c.eval (∑ j, x j ^ 2)) (𝓝[≠] (0 : ℝ)) C := by
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        have hcontS : Continuous (fun x : Fin d → ℝ => ∑ j : Fin d, x j ^ 2) := by fun_prop
        obtain ⟨B, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ C, ∑ j : Fin d, x j ^ 2 ≤ B := by
          rcases C.eq_empty_or_nonempty with rfl | hne
          · exact ⟨0, le_rfl, by simp⟩
          · obtain ⟨x₀, hx₀, hmax⟩ := hC.exists_isMaxOn hne hcontS.continuousOn
            exact ⟨∑ j : Fin d, x₀ j ^ 2,
              Finset.sum_nonneg fun j _ => sq_nonneg (x₀ j), fun x hx => hmax hx⟩
        let g (p : ℝ × ℝ) : ℝ := (c.poly.eval (p.1 : ℂ) * exp (c.rate * (p.2 : ℂ))).re
        have hg_cont : Continuous g := by
          refine Complex.continuous_re.comp (Continuous.mul ?_ ?_)
          · exact c.poly.continuous_aeval.comp (Complex.continuous_ofReal.comp continuous_fst)
          · exact Complex.continuous_exp.comp
              (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd))
        let K_box : Set (ℝ × ℝ) := Set.Icc (-1) (B + 1) ×ˢ Set.Icc 0 B
        have hK_comp : IsCompact K_box := isCompact_Icc.prod isCompact_Icc
        obtain ⟨δ_u, hδ_u_pos, hδ_u⟩ := Metric.uniformContinuousOn_iff.mp
          (hK_comp.uniformContinuousOn_of_continuous hg_cont.continuousOn) ε hε
        let M_B : ℝ := max 1 ((B + 1) ^ 2 * Real.exp (B + 1))
        have hM_B_pos : 0 < M_B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
        let η : ℝ := min 1 (min δ_u 1 / (2 * M_B))
        have hη_pos : 0 < η :=
          lt_min zero_lt_one (div_pos (lt_min hδ_u_pos zero_lt_one) (mul_pos zero_lt_two hM_B_pos))
        have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), h ≠ 0 ∧ |h| < η := by
          filter_upwards [self_mem_nhdsWithin,
            nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hη_pos)] with h hh0 hball
          exact ⟨hh0, by simpa [Real.dist_eq] using hball⟩
        filter_upwards [hev] with h ⟨hh0, hhη⟩ x hxC
        set s := ∑ j : Fin d, x j ^ 2
        have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => sq_nonneg (x j)
        have hsB : s ≤ B := hB.2 x hxC
        have hh1 : |h| ≤ 1 := le_of_lt (lt_of_lt_of_le hhη (min_le_left _ _))
        let u_s : ℝ := h⁻¹ * (Real.exp (h * s) - 1)
        have hu_diff : |u_s - s| < min δ_u 1 := by
          have hh_pos : 0 < |h| := abs_pos.mpr hh0
          have hsub : u_s - s = h⁻¹ * (Real.exp (h * s) - 1 - h * s) := by
            dsimp only [u_s]
            field_simp [hh0]
          have habs_hs : |h * s| ≤ B + 1 := by
            rw [abs_mul, abs_of_nonneg hs0]
            nlinarith
          have hexp_b := abs_exp_sub_one_sub_le (h * s)
          have hrem : |u_s - s| ≤ |h| * M_B := by
            rw [hsub, abs_mul, abs_inv]
            calc
              |h|⁻¹ * |Real.exp (h * s) - 1 - h * s|
                  ≤ |h|⁻¹ * ((h * s) ^ 2 * Real.exp |h * s|) := by gcongr
              _ = |h| * (s ^ 2 * Real.exp |h * s|) := by
                  have : (h * s) ^ 2 = |h| * |h| * s ^ 2 := by
                    rw [mul_pow, ← sq_abs h, sq]
                  rw [this]
                  field_simp [hh_pos.ne']
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
        change dist (g (s, s)) (g (u_s, s)) < ε
        exact hδ_u (s, s) hs_box (u_s, s) hu_box hdist
      have hprof_cons : (fun x : Fin d → ℝ => profile (c :: cs) (∑ j, x j ^ 2)) =
          fun x => c.eval (∑ j, x j ^ 2) + profile cs (∑ j, x j ^ 2) := by
        funext x
        simp [profile]
      rw [hprof_cons]
      exact hFc_tend.add (htend' C hC)
end KernelRank
end

set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank
namespace KernelRank
theorem _root_.solution
    {d : ℕ} (hd : 2 ≤ d) (cs : List Component) (hcs : ∀ c ∈ cs, c.WellFormed) :
    ∃ F : ℝ → (Fin d → ℝ) → ℝ,
      (∀ h, separableRank (F h) ≤ (borderTotalCost d cs : ℕ)) ∧
      ∀ C : Set (Fin d → ℝ), IsCompact C →
        TendstoUniformlyOn F (fun x => profile cs (∑ j, x j ^ 2)) (𝓝[≠] (0 : ℝ)) C := by
  obtain ⟨F, hF, htend⟩ := exists_isSumOfProducts_borderTotalCost_tendstoUniformlyOn hd cs hcs
  exact ⟨F, fun h => iInf₂_le _ (hF h), htend⟩
end KernelRank
