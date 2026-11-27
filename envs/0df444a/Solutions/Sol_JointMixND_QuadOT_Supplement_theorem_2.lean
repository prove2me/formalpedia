-- Prove2me | solution 1 for JointMixND.QuadOT.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:32.821699+00:00
-- url     : https://prove2.me/submissions/5ac32e41-c4cc-4827-be99-1b7966e64d79

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Basic
import Definitions.Def_JointMixND_QuadOT_Supplement_Dependence

open MeasureTheory ProbabilityTheory
open scoped NNReal

open JointMixND
open JointMixND.QuadOT
open JointMixND.QuadOT.Supplement

theorem solution {n : ℕ} (m : Fin n → ℝ) (v : Fin n → ℝ≥0) :
    ((∃ P : Measure (Fin n → ℝ), HasMarginals (fun i => gaussianReal (m i) (v i)) P ∧
        IsJointMix P ∧ IsNCD P) ↔ ∀ j, 2 * (v j : ℝ) ≤ ∑ i, (v i : ℝ)) ∧
    ((∃ P : Measure (Fin n → ℝ), HasMarginals (fun i => gaussianReal (m i) (v i)) P ∧
        IsJointMix P ∧ IsNA P) ↔ ∀ j, 2 * (v j : ℝ) ≤ ∑ i, (v i : ℝ)) ∧
    ((∀ j, 2 * (v j : ℝ) ≤ ∑ i, (v i : ℝ)) →
      ∃ P : Measure (Fin n → ℝ), HasMarginals (fun i => gaussianReal (m i) (v i)) P ∧
        IsJointMix P ∧ IsGaussian P ∧ IsNCD P ∧ IsNA P) := by
          -- basic facts about a law with Gaussian marginals
          have hmem : ∀ P : Measure (Fin n → ℝ), HasMarginals (fun i => gaussianReal (m i) (v i)) P →
              ∀ i, MemLp (fun x : Fin n → ℝ => x i) 2 P := by
            intro P hP i
            have h1 : MemLp id 2 (P.map (fun x : Fin n → ℝ => x i)) := by
              rw [hP.2 i]; exact memLp_id_gaussianReal 2
            exact (memLp_map_measure_iff aestronglyMeasurable_id
              (measurable_pi_apply i).aemeasurable).1 h1
          have hvar : ∀ P : Measure (Fin n → ℝ), HasMarginals (fun i => gaussianReal (m i) (v i)) P →
              ∀ i, Var[fun x : Fin n → ℝ => x i; P] = v i := by
            intro P hP i
            have := variance_map (μ := P) (X := id) (Y := fun x : Fin n → ℝ => x i)
              aemeasurable_id (measurable_pi_apply i).aemeasurable
            rw [hP.2 i, variance_id_gaussianReal] at this
            exact this.symm
          have hfwd : ∀ P : Measure (Fin n → ℝ), HasMarginals (fun i => gaussianReal (m i) (v i)) P →
              IsJointMix P → IsNCD P → ∀ j, 2 * (v j : ℝ) ≤ ∑ i, (v i : ℝ) := by
            intro P hP hJ hN j
            haveI := hP.1
            obtain ⟨c, hc⟩ := hJ
            set s := Finset.univ.erase j with hs
            have hY : (fun x : Fin n → ℝ => ∑ i ∈ s, x i) =ᵐ[P] (fun x => c - x j) := by
              filter_upwards [hc] with x hx
              rw [← hx, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]; ring
            have hV1 : Var[fun x : Fin n → ℝ => ∑ i ∈ s, x i; P] = v j := by
              rw [variance_congr hY, variance_const_sub (measurable_pi_apply j).aestronglyMeasurable,
                hvar P hP j]
            have hV2 : Var[fun x : Fin n → ℝ => ∑ i ∈ s, x i; P] ≤ ∑ i ∈ s, (v i : ℝ) := by
              rw [← covariance_self (by fun_prop),
                covariance_fun_sum_fun_sum' (fun i _ => hmem P hP i) (fun i _ => hmem P hP i)]
              apply Finset.sum_le_sum
              intro i hi
              rw [← Finset.add_sum_erase _ _ hi, covariance_self (measurable_pi_apply i).aemeasurable,
                hvar P hP i]
              have : ∑ k ∈ s.erase i, covariance (fun x : Fin n → ℝ => x i) (fun x => x k) P ≤ 0 :=
                Finset.sum_nonpos (fun k hk => hN i k (Finset.ne_of_mem_erase hk).symm)
              linarith
            have := Finset.add_sum_erase Finset.univ (fun i => (v i : ℝ)) (Finset.mem_univ j)
            rw [← this]; linarith
          have hNA : ∀ P : Measure (Fin n → ℝ), HasMarginals (fun i => gaussianReal (m i) (v i)) P →
              IsNA P → IsNCD P := by
            intro P hP hA i j hij
            have hd : Disjoint ({i} : Finset (Fin n)) {j} := Finset.disjoint_singleton.2 hij
            have key := hA {i} {j} hd (fun y => y ⟨i, Finset.mem_singleton_self i⟩)
              (fun y => y ⟨j, Finset.mem_singleton_self j⟩)
              (fun a b h => h _) (fun a b h => h _) (hmem P hP i) (hmem P hP j)
            simpa [restrictTo] using key
          have hC : (∀ j, 2 * (v j : ℝ) ≤ ∑ i, (v i : ℝ)) →
              ∃ P : Measure (Fin n → ℝ), HasMarginals (fun i => gaussianReal (m i) (v i)) P ∧
                IsJointMix P ∧ IsGaussian P ∧ IsNCD P ∧ IsNA P := by
            intro hv
            obtain ⟨S, hSpsd, hSd, hSo, hSr, w, hw0, hSw⟩ : ∃ S : Matrix (Fin n) (Fin n) ℝ, S.PosSemidef ∧
                (∀ i, S i i = v i) ∧ (∀ i j, i ≠ j → S i j ≤ 0) ∧ (∀ i, ∑ j, S i j = 0) ∧
                ∃ w : Fin n × Fin n → ℝ, (∀ p, 0 ≤ w p) ∧ ∀ i j, S i j = ∑ p, w p *
                  (((if p.1 = i then (1:ℝ) else 0) - (if p.2 = i then 1 else 0)) *
                    ((if p.1 = j then (1:ℝ) else 0) - (if p.2 = j then 1 else 0))) := by
              obtain ⟨w, hw0, hwsum⟩ : ∃ w : Fin n × Fin n → ℝ, (∀ p, 0 ≤ w p) ∧
                  ∀ i, ∑ p : Fin n × Fin n, w p * ((if p.1 = i then (1:ℝ) else 0) -
                    (if p.2 = i then 1 else 0)) ^ 2 = (v i : ℝ) := by
                have hcoef : ∀ (w : Fin n × Fin n → ℝ) i, ∑ p : Fin n × Fin n, w p *
                    ((if p.1 = i then (1:ℝ) else 0) - (if p.2 = i then 1 else 0)) ^ 2 =
                    ∑ b, w (i, b) + ∑ a, w (a, i) - 2 * w (i, i) := by
                  intro w i
                  have h : ∀ p : Fin n × Fin n, w p *
                      ((if p.1 = i then (1:ℝ) else 0) - (if p.2 = i then 1 else 0)) ^ 2 =
                      (if p.1 = i then w p else 0) + (if p.2 = i then w p else 0) -
                        2 * (if p = (i, i) then w p else 0) := by
                    rintro ⟨a, b⟩
                    by_cases h1 : a = i <;> by_cases h2 : b = i <;> simp [h1, h2]
                    ring
                  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
                    Fintype.sum_prod_type]
                  simp [ite_and, Finset.sum_ite_irrel]
                  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]; simp
                set S := ∑ i, (v i : ℝ) with hS
                by_cases hex : ∃ i0, 2 * (v i0 : ℝ) = S
                · obtain ⟨i0, hi0⟩ := hex
                  refine ⟨fun p => if p.1 = i0 then (v p.2 : ℝ) else 0, fun p => ?_, fun i => ?_⟩
                  · dsimp only; split_ifs <;> simp
                  · rw [hcoef]
                    by_cases hi : i = i0
                    · subst hi; simp; linarith
                    · simp [hi, Ne.symm hi]
                · push Not at hex
                  have hlt : ∀ i, 0 < S - 2 * (v i : ℝ) := fun i =>
                    sub_pos.2 (lt_of_le_of_ne (hv i) (hex i))
                  set r : Fin n → ℝ := fun i => (v i : ℝ) / (S - 2 * v i) with hr
                  set R := ∑ i, r i with hR
                  have hr0 : ∀ i, 0 ≤ r i := fun i => div_nonneg (v i).2 (hlt i).le
                  have hR0 : 0 ≤ R := Finset.sum_nonneg fun i _ => hr0 i
                  refine ⟨fun p => (v p.1 : ℝ) * (r p.2 / (1 + R)), fun p => ?_, fun i => ?_⟩
                  · exact mul_nonneg (v p.1).2 (div_nonneg (hr0 _) (by linarith))
                  · rw [hcoef]
                    simp only
                    rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_div, ← hR, ← hS]
                    have h1 : r i * (S - 2 * v i) = v i := div_mul_cancel₀ _ (hlt i).ne'
                    have h2 : (1 + R) ≠ 0 := by positivity
                    rw [show (v i : ℝ) * (R / (1 + R)) + S * (r i / (1 + R)) - 2 * (v i * (r i / (1 + R)))
                      = (v i * R + r i * (S - 2 * v i)) / (1 + R) by ring, h1, div_eq_iff h2]
                    ring
              let A : Matrix (Fin n × Fin n) (Fin n) ℝ := fun p i =>
                Real.sqrt (w p) * ((if p.1 = i then (1:ℝ) else 0) - (if p.2 = i then 1 else 0))
              have hS : ∀ i j, (A.conjTranspose * A) i j = ∑ p, w p *
                  (((if p.1 = i then (1:ℝ) else 0) - (if p.2 = i then 1 else 0)) *
                    ((if p.1 = j then (1:ℝ) else 0) - (if p.2 = j then 1 else 0))) := by
                intro i j
                rw [Matrix.mul_apply]
                refine Finset.sum_congr rfl fun p _ => ?_
                rw [Matrix.conjTranspose_apply, star_trivial]
                simp only [A]
                have := Real.mul_self_sqrt (hw0 p)
                linear_combination (((if p.1 = i then (1:ℝ) else 0) - (if p.2 = i then 1 else 0)) *
                    ((if p.1 = j then (1:ℝ) else 0) - (if p.2 = j then 1 else 0))) * this
              refine ⟨A.conjTranspose * A, Matrix.posSemidef_conjTranspose_mul_self A, fun i => ?_,
                fun i j hij => ?_, fun i => ?_, ⟨w, hw0, hS⟩⟩
              · rw [hS, ← hwsum i]; simp_rw [sq]
              · rw [hS]
                refine Finset.sum_nonpos fun p _ => mul_nonpos_of_nonneg_of_nonpos (hw0 p) ?_
                by_cases h1 : p.1 = i <;> by_cases h2 : p.2 = i <;> by_cases h3 : p.1 = j <;>
                  by_cases h4 : p.2 = j <;> simp_all
                all_goals (subst_vars; simp_all)
              · simp_rw [hS]
                rw [Finset.sum_comm]
                refine Finset.sum_eq_zero fun p _ => ?_
                rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib]
                simp
            set G := multivariateGaussian (WithLp.toLp 2 m) S with hG
            set L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ) with hL
            have hLapp : ∀ x i, L x i = x i := fun x i => rfl
            have hLm : Measurable L := L.continuous.measurable
            refine ⟨G.map L, ⟨inferInstance, fun i => ?_⟩, ?_, inferInstance, ?_, ?_⟩
            · rw [Measure.map_map (measurable_pi_apply i) hLm]
              have := (measurePreserving_eval_multivariateGaussian (μ := WithLp.toLp 2 m) hSpsd (i := i)).map_eq
              convert this using 2
              · rfl
              · rw [hSd i]; simp
            · have hcov : ∀ i j, cov[fun x : Fin n → ℝ => x i, fun x => x j; G.map L] = S i j := by
                intro i j
                rw [covariance_map (measurable_pi_apply i).aestronglyMeasurable
                  (measurable_pi_apply j).aestronglyMeasurable hLm.aemeasurable]
                exact covariance_eval_multivariateGaussian hSpsd i j
              have hmemP : ∀ i, MemLp (fun x : Fin n → ℝ => x i) 2 (G.map L) := by
                intro i
                exact (memLp_map_measure_iff (measurable_pi_apply i).aestronglyMeasurable
                  hLm.aemeasurable).2 (IsGaussian.memLp_dual G (EuclideanSpace.proj i) 2 (by simp))
              have hV : Var[fun x : Fin n → ℝ => ∑ i, x i; G.map L] = 0 := by
                rw [← covariance_self (by fun_prop), covariance_fun_sum_fun_sum hmemP hmemP]
                simp_rw [hcov, hSr]; simp
              exact ⟨_, ae_eq_integral_of_variance_eq_zero (memLp_finsetSum _ fun i _ => hmemP i) hV⟩
            · intro i j hij
              rw [covariance_map (measurable_pi_apply i).aestronglyMeasurable
                  (measurable_pi_apply j).aestronglyMeasurable hLm.aemeasurable]
              exact (covariance_eval_multivariateGaussian hSpsd i j).le.trans (hSo i j hij)
            · -- 1-D Chebyshev (Harris) inequality: proven building block.
              have cheb : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (f g : ℝ → ℝ), Monotone f →
                  Antitone g → MemLp f 2 μ → MemLp g 2 μ →
                  ∫ x, f x * g x ∂μ ≤ (∫ x, f x ∂μ) * ∫ x, g x ∂μ := by
                intro μ _ f g hf hg hf2 hg2
                have hfg : Integrable (fun x => f x * g x) μ := hf2.integrable_mul hg2
                have hfi : Integrable f μ := hf2.integrable one_le_two
                have hgi : Integrable g μ := hg2.integrable one_le_two
                have h1 : Integrable (fun z : ℝ × ℝ => f z.1 * g z.1) (μ.prod μ) := by
                  exact hfg.comp_fst μ
                have h2 : Integrable (fun z : ℝ × ℝ => f z.2 * g z.2) (μ.prod μ) := by
                  exact hfg.comp_snd μ
                have h3 : Integrable (fun z : ℝ × ℝ => f z.1 * g z.2) (μ.prod μ) := hfi.mul_prod hgi
                have h4 : Integrable (fun z : ℝ × ℝ => f z.2 * g z.1) (μ.prod μ) := by
                  simpa only [mul_comm] using hgi.mul_prod hfi
                have hle : ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) ∂(μ.prod μ) ≤ 0 := by
                  refine integral_nonpos fun z => ?_
                  rcases le_total z.1 z.2 with h | h
                  · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hf h)) (sub_nonneg.2 (hg h))
                  · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hf h)) (sub_nonpos.2 (hg h))
                have hexp : ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) ∂(μ.prod μ) =
                    ∫ z, f z.1 * g z.1 ∂(μ.prod μ) + ∫ z, f z.2 * g z.2 ∂(μ.prod μ)
                      - ∫ z, f z.1 * g z.2 ∂(μ.prod μ) - ∫ z, f z.2 * g z.1 ∂(μ.prod μ) := by
                  have e : (fun z : ℝ × ℝ => (f z.1 - f z.2) * (g z.1 - g z.2)) = fun z =>
                      (f z.1 * g z.1 + f z.2 * g z.2) - f z.1 * g z.2 - f z.2 * g z.1 := by ext z; ring
                  have h12 : Integrable (fun z : ℝ × ℝ => f z.1 * g z.1 + f z.2 * g z.2) (μ.prod μ) := h1.add h2
                  have h123 : Integrable (fun z : ℝ × ℝ => f z.1 * g z.1 + f z.2 * g z.2 - f z.1 * g z.2)
                    (μ.prod μ) := h12.sub h3
                  rw [e, integral_sub h123 h4, integral_sub h12 h3, integral_add h1 h2]
                have e1 : ∫ z, f z.1 * g z.1 ∂(μ.prod μ) = ∫ x, f x * g x ∂μ := by
                  simpa using integral_prod_mul (μ := μ) (ν := μ) (fun x => f x * g x) (fun _ => (1:ℝ))
                have e2 : ∫ z, f z.2 * g z.2 ∂(μ.prod μ) = ∫ x, f x * g x ∂μ := by
                  simpa using integral_prod_mul (μ := μ) (ν := μ) (fun _ => (1:ℝ)) (fun x => f x * g x)
                have e3 : ∫ z, f z.1 * g z.2 ∂(μ.prod μ) = (∫ x, f x ∂μ) * ∫ x, g x ∂μ :=
                  integral_prod_mul (μ := μ) (ν := μ) f g
                have e4 : ∫ z, f z.2 * g z.1 ∂(μ.prod μ) = (∫ x, f x ∂μ) * ∫ x, g x ∂μ := by
                  rw [← e3, ← integral_prod_swap]; simp [mul_comm]
                linarith
              -- edge representation X = m + A^T Z, Z i.i.d. N(0,1) indexed by ordered pairs
              -- edge representation X = m + A^T Z, Z i.i.d. N(0,1) indexed by ordered pairs
              set Φ : (Fin n × Fin n → ℝ) → Fin n → ℝ := fun z i => m i + ∑ p, Real.sqrt (w p) *
                ((if p.1 = i then (1:ℝ) else 0) - (if p.2 = i then 1 else 0)) * z p with hΦ
              open Complex in
              have hrep : G.map L = (Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1)).map Φ := by
                rw [hG, hL, hΦ]
                set c : Fin n × Fin n → Fin n → ℝ := fun p i =>
                  (if p.1 = i then (1:ℝ) else 0) - (if p.2 = i then 1 else 0) with hc
                set π := Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1) with hπ
                set Φ : (Fin n × Fin n → ℝ) → Fin n → ℝ := fun z i => m i + ∑ p, Real.sqrt (w p) *
                  ((if p.1 = i then (1:ℝ) else 0) - (if p.2 = i then 1 else 0)) * z p with hΦ
                have hΦm : Measurable Φ := by
                  rw [hΦ]; fun_prop
                have key : multivariateGaussian (WithLp.toLp 2 m) S = π.map (fun z => WithLp.toLp 2 (Φ z)) := by
                  apply Measure.ext_of_charFun
                  funext x
                  rw [charFun_multivariateGaussian hSpsd, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
                  set b : Fin n × Fin n → ℝ := fun p => ∑ i, x i * (Real.sqrt (w p) * c p i) with hb
                  have hpi := charFun_pi (μ := fun _ : Fin n × Fin n => gaussianReal 0 1) (WithLp.toLp 2 b)
                  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)] at hpi
                  simp only [charFun_gaussianReal] at hpi
                  have hin : ∀ z, inner ℝ (WithLp.toLp 2 (Φ z)) x = inner ℝ x (WithLp.toLp 2 m) +
                      inner ℝ (WithLp.toLp 2 z) (WithLp.toLp 2 b) := by
                    intro z
                    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hΦ, hb, hc]
                    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
                    congr 1
                    · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
                    · rw [Finset.sum_comm]
                      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring
                  simp_rw [hin, ofReal_add, add_mul, Complex.exp_add]
                  rw [← hπ] at hpi
                  rw [integral_const_mul, hpi, ← Complex.exp_sum, ← Complex.exp_add]
                  congr 1
                  have hq : ∑ p, b p ^ 2 = x.ofLp ⬝ᵥ S.mulVec x.ofLp := by
                    simp only [dotProduct, Matrix.mulVec, hSw, hb, hc]
                    simp only [sq, Finset.mul_sum, Finset.sum_mul]
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl fun i _ => ?_
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => ?_
                    have := Real.mul_self_sqrt (hw0 p)
                    linear_combination (x.ofLp i * x.ofLp j * ((if p.1 = i then (1:ℝ) else 0) - (if p.2 = i then 1 else 0)) * ((if p.1 = j then (1:ℝ) else 0) - (if p.2 = j then 1 else 0))) * this
                  rw [← hq]
                  simp only [ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, ofReal_one, one_mul, zero_sub]
                  rw [Finset.sum_neg_distrib, ← Finset.sum_div]
                  push_cast
                  ring
                rw [key, Measure.map_map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).continuous.measurable
                  (by fun_prop)]
                rfl
              set γ0 : Measure ℝ := gaussianReal 0 1 with hγ0
              haveI : IsProbabilityMeasure γ0 := by rw [hγ0]; infer_instance
              open Function in
              have hupd : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (r : κ),
                  MeasurePreserving (fun x : (κ → ℝ) × ℝ => update x.1 r x.2)
                    ((Measure.pi fun _ : κ => γ0).prod γ0) (Measure.pi fun _ : κ => γ0) := by
                intro κ _ _ r
                refine ⟨by fun_prop, ?_⟩
                symm
                refine Measure.pi_eq fun s hs => ?_
                rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
                have hpre : (fun x : (κ → ℝ) × ℝ => update x.1 r x.2) ⁻¹' Set.pi Set.univ s =
                    Set.pi Set.univ (update s r Set.univ) ×ˢ s r := by
                  ext ⟨z, a⟩
                  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
                  rw [forall_update_iff z (fun q y => y ∈ s q), forall_update_iff s (fun q t => z q ∈ t)]
                  simp only [Set.mem_univ, true_and]
                  tauto
                rw [hpre, Measure.prod_prod, Measure.pi_pi]
                have : (fun q => γ0 (update s r Set.univ q)) = update (fun q => γ0 (s q)) r 1 := by
                  ext q; by_cases h : q = r
                  · subst h; simp
                  · simp [h]
                rw [this, Finset.prod_update_of_mem (Finset.mem_univ r), one_mul,
                  ← Finset.prod_erase_mul _ _ (Finset.mem_univ r), Finset.sdiff_singleton_eq_erase]
              open Function in
              have hmix : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Finset ι),
                  MeasurePreserving (fun (ω : ι ⊕ ι → ℝ) (q : ι) => ω (if q ∈ S then .inl q else .inr q))
                    (Measure.pi fun _ : ι ⊕ ι => γ0) (Measure.pi fun _ : ι => γ0) := by
                intro ι _ _ S
                have hm : Measurable (fun (ω : ι ⊕ ι → ℝ) (q : ι) => ω (if q ∈ S then .inl q else .inr q)) :=
                  measurable_pi_lambda _ (fun q => measurable_pi_apply _)
                refine ⟨hm, ?_⟩
                symm
                refine Measure.pi_eq fun s hs => ?_
                rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
                have hpre : (fun (ω : ι ⊕ ι → ℝ) (q : ι) => ω (if q ∈ S then .inl q else .inr q)) ⁻¹'
                    Set.pi Set.univ s = Set.pi Set.univ (Sum.elim (fun q => if q ∈ S then s q else Set.univ)
                      (fun q => if q ∈ S then Set.univ else s q)) := by
                  ext ω
                  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Sum.forall,
                    Sum.elim_inl, Sum.elim_inr]
                  constructor
                  · intro h
                    exact ⟨fun q => by have := h q; split_ifs at this ⊢ <;> simp_all,
                      fun q => by have := h q; split_ifs at this ⊢ <;> simp_all⟩
                  · rintro ⟨h1, h2⟩ q
                    have := h1 q; have := h2 q
                    split_ifs at * <;> simp_all
                rw [hpre, Measure.pi_pi, Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
                refine Finset.prod_congr rfl fun q _ => ?_
                simp only [Sum.elim_inl, Sum.elim_inr]
                split_ifs <;> simp
              open Function in
              have harris : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F G : (ι → ℝ) → ℝ),
                  MemLp F 2 (Measure.pi fun _ : ι => γ0) → MemLp G 2 (Measure.pi fun _ : ι => γ0) →
                  (∀ p (z w : ι → ℝ), MemLp (fun a => F (update z p a)) 2 γ0 →
                    MemLp (fun a => G (update w p a)) 2 γ0 →
                    ∫ a, F (update z p a) * G (update w p a) ∂γ0 ≤
                      (∫ a, F (update z p a) ∂γ0) * ∫ a, G (update w p a) ∂γ0) →
                  ∫ z, F z * G z ∂(Measure.pi fun _ : ι => γ0) ≤
                    (∫ z, F z ∂(Measure.pi fun _ : ι => γ0)) * ∫ z, G z ∂(Measure.pi fun _ : ι => γ0) := by
                intro ι _ _ F G hF hG hstep
                set π := Measure.pi fun _ : ι => γ0 with hπ
                set π2 := Measure.pi fun _ : ι ⊕ ι => γ0 with hπ2
                set mix : Finset ι → (ι ⊕ ι → ℝ) → ι → ℝ :=
                  fun S ω q => ω (if q ∈ S then .inl q else .inr q) with hmixdef
                have hmixS : ∀ S, MeasurePreserving (mix S) π2 π := hmix ι
                have hFm : ∀ S, MemLp (fun ω => F (mix S ω)) 2 π2 := fun S => hF.comp_measurePreserving (hmixS S)
                have hGm : ∀ S, MemLp (fun ω => G (mix S ω)) 2 π2 := fun S => hG.comp_measurePreserving (hmixS S)
                have hint : ∀ S T, Integrable (fun ω => F (mix S ω) * G (mix T ω)) π2 :=
                  fun S T => (hFm S).integrable_mul (hGm T)
                have hsec : ∀ K : (ι ⊕ ι → ℝ) × ℝ → ℝ, MemLp K 2 (π2.prod γ0) →
                    ∀ᵐ ω ∂π2, MemLp (fun a => K (ω, a)) 2 γ0 := by
                  intro K hK
                  have h1 := hK.aestronglyMeasurable.prodMk_left
                  have h2 := ((memLp_two_iff_integrable_sq hK.1).1 hK).prod_right_ae
                  filter_upwards [h1, h2] with ω h1 h2
                  exact (memLp_two_iff_integrable_sq h1).2 h2
                set I : Finset ι → ℝ := fun S => ∫ ω, F (mix Finset.univ ω) * G (mix S ω) ∂π2 with hI
                have hstepI : ∀ p S, p ∉ S → I (insert p S) ≤ I S := by
                  intro p S hp
                  set U : (ι ⊕ ι → ℝ) × (ℝ × ℝ) → (ι ⊕ ι → ℝ) :=
                    fun x => update (update x.1 (.inr p) x.2.1) (.inl p) x.2.2 with hUdef
                  have hU : MeasurePreserving U (π2.prod (γ0.prod γ0)) π2 := by
                    have h := (hupd (ι ⊕ ι) (.inl p)).comp (((hupd (ι ⊕ ι) (.inr p)).prod
                      (MeasurePreserving.id γ0)).comp (measurePreserving_prodAssoc π2 γ0 γ0).symm)
                    convert h using 1
                    funext x; rfl
                  have e1 : ∀ x, mix Finset.univ (U x) = update (mix Finset.univ x.1) p x.2.2 := by
                    intro x; funext q
                    by_cases hq : q = p
                    · subst hq; simp [mix, U]
                    · simp [mix, U, hq, update_apply]
                  have e2 : ∀ x, mix (insert p S) (U x) = update (mix S x.1) p x.2.2 := by
                    intro x; funext q
                    by_cases hq : q = p
                    · subst hq; simp [mix, U]
                    · by_cases hqS : q ∈ S <;> simp [mix, U, hq, hqS, update_apply]
                  have e3 : ∀ x, mix S (U x) = update (mix S x.1) p x.2.1 := by
                    intro x; funext q
                    by_cases hq : q = p
                    · subst hq; simp [mix, U, hp]
                    · by_cases hqS : q ∈ S <;> simp [mix, U, hq, hqS, update_apply]
                  have hIU : ∀ T, I T = ∫ x, F (mix Finset.univ (U x)) * G (mix T (U x)) ∂(π2.prod (γ0.prod γ0)) := by
                    intro T
                    have := integral_map (μ := π2.prod (γ0.prod γ0)) hU.measurable.aemeasurable
                      (f := fun ω => F (mix Finset.univ ω) * G (mix T ω))
                      (by rw [hU.map_eq]; exact (hint _ _).aestronglyMeasurable)
                    rw [hU.map_eq] at this
                    exact this
                  have hintU : ∀ T, Integrable (fun x => F (mix Finset.univ (U x)) * G (mix T (U x)))
                      (π2.prod (γ0.prod γ0)) := fun T => hU.integrable_comp_of_integrable (hint _ T)
                  have hL := hintU (insert p S)
                  have hR := hintU S
                  simp only [e1, e2, e3] at hL hR
                  rw [hIU, hIU]
                  simp only [e1, e2, e3]
                  rw [integral_prod _ hL, integral_prod _ hR]
                  refine integral_mono_ae hL.integral_prod_left hR.integral_prod_left ?_
                  have hK1 : MemLp (fun x : (ι ⊕ ι → ℝ) × ℝ => F (update (mix Finset.univ x.1) p x.2)) 2
                      (π2.prod γ0) := by
                    have := (hFm Finset.univ).comp_measurePreserving (hupd _ (.inl p))
                    convert this using 2 with x
                    congr 1; funext q
                    by_cases hq : q = p
                    · subst hq; simp [mix]
                    · simp [mix, hq, update_apply]
                  have hK2 : MemLp (fun x : (ι ⊕ ι → ℝ) × ℝ => G (update (mix S x.1) p x.2)) 2
                      (π2.prod γ0) := by
                    have := (hGm S).comp_measurePreserving (hupd _ (.inr p))
                    convert this using 2 with x
                    congr 1; funext q
                    by_cases hq : q = p
                    · subst hq; simp [mix, hp]
                    · by_cases hqS : q ∈ S <;> simp [mix, hq, hqS, update_apply]
                  filter_upwards [hsec _ hK1, hsec _ hK2] with ω h1 h2
                  have hl : ∫ y : ℝ × ℝ, F (update (mix Finset.univ ω) p y.2) * G (update (mix S ω) p y.2)
                      ∂(γ0.prod γ0) = ∫ a, F (update (mix Finset.univ ω) p a) * G (update (mix S ω) p a) ∂γ0 := by
                    simpa using integral_prod_mul (μ := γ0) (ν := γ0) (fun _ => (1:ℝ))
                      (fun a => F (update (mix Finset.univ ω) p a) * G (update (mix S ω) p a))
                  have hr : ∫ y : ℝ × ℝ, F (update (mix Finset.univ ω) p y.2) * G (update (mix S ω) p y.1)
                      ∂(γ0.prod γ0) = (∫ a, F (update (mix Finset.univ ω) p a) ∂γ0) *
                        ∫ a, G (update (mix S ω) p a) ∂γ0 := by
                    rw [mul_comm, ← integral_prod_mul]
                    simp only [mul_comm]
                  rw [hl, hr]
                  exact hstep p _ _ h1 h2
                have hIall : ∀ S, I S ≤ I ∅ := by
                  intro S
                  induction S using Finset.induction_on with
                  | empty => exact le_rfl
                  | insert p S hp ih => exact (hstepI p S hp).trans ih
                have hIuniv : I Finset.univ = ∫ z, F z * G z ∂π := by
                  have := integral_map (μ := π2) (hmixS Finset.univ).measurable.aemeasurable
                    (f := fun z => F z * G z)
                    (by rw [(hmixS Finset.univ).map_eq]; exact (hF.integrable_mul hG).aestronglyMeasurable)
                  rw [(hmixS Finset.univ).map_eq] at this
                  exact this.symm
                have hI0 : I ∅ = (∫ z, F z ∂π) * ∫ z, G z ∂π := by
                  have hm := measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ ι => γ0)
                  rw [← integral_prod_mul]
                  rw [← hm.integral_comp' (g := fun z : (ι → ℝ) × (ι → ℝ) => F z.1 * G z.2)]
                  simp only [I]
                  congr 1; funext ω
                  congr 2 <;> funext q <;> simp [mix, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
                have := hIall Finset.univ
                rw [hIuniv, hI0] at this
                exact this
              have hΦm : Measurable Φ := by rw [hΦ]; fun_prop
              have hupdΦ : ∀ (p : Fin n × Fin n) z a i, Φ (Function.update z p a) i = Φ z i +
                  Real.sqrt (w p) * ((if p.1 = i then (1:ℝ) else 0) - (if p.2 = i then 1 else 0)) * (a - z p) := by
                intro p z a i
                simp only [hΦ]
                rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ (Finset.mem_univ p),
                  Function.update_self, Finset.sum_congr rfl (fun q hq => by
                    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)])]
                ring
              rw [hrep]
              intro A B hAB f g hf hg hfm hgm
              have hF2 : MemLp (fun z => f (restrictTo A (Φ z))) 2 (Measure.pi fun _ : Fin n × Fin n => γ0) :=
                (memLp_map_measure_iff hfm.1 hΦm.aemeasurable).1 hfm
              have hG2 : MemLp (fun z => g (restrictTo B (Φ z))) 2 (Measure.pi fun _ : Fin n × Fin n => γ0) :=
                (memLp_map_measure_iff hgm.1 hΦm.aemeasurable).1 hgm
              rw [covariance_map hfm.1 hgm.1 hΦm.aemeasurable]
              change cov[fun z => f (restrictTo A (Φ z)), fun z => g (restrictTo B (Φ z));
                Measure.pi fun _ : Fin n × Fin n => γ0] ≤ 0
              rw [covariance_eq_sub hF2 hG2]
              have key := harris (Fin n × Fin n) (fun z => f (restrictTo A (Φ z)))
                (fun z => g (restrictTo B (Φ z))) hF2 hG2 ?_
              · simp only [Pi.mul_apply, Function.comp_def] at key ⊢
                linarith
              intro p z z' h1 h2
              have hconst : ∀ (C : Finset (Fin n)) (h : (C → ℝ) → ℝ), p.1 ∉ C → p.2 ∉ C → ∀ y a,
                  h (restrictTo C (Φ (Function.update y p a))) = h (restrictTo C (Φ y)) := by
                intro C h hp1 hp2 y a
                congr 1; funext i
                simp only [restrictTo, hupdΦ]
                have : p.1 ≠ (i : Fin n) := fun e => hp1 (e ▸ i.2)
                have : p.2 ≠ (i : Fin n) := fun e => hp2 (e ▸ i.2)
                simp [*]
              have hdisj : ∀ x, x ∈ A → x ∉ B := fun x hx hx' => Finset.disjoint_left.1 hAB hx hx'
              by_cases hB : p.1 ∉ B ∧ p.2 ∉ B
              · have e := hconst B g hB.1 hB.2 z'
                simp only [e]
                rw [integral_mul_const, integral_const]; simp
              by_cases hA : p.1 ∉ A ∧ p.2 ∉ A
              · have e := hconst A f hA.1 hA.2 z
                simp only [e]
                rw [integral_const_mul, integral_const]; simp
              by_cases h1A : p.1 ∈ A
              · have h2B : p.2 ∈ B := by
                  by_contra h; exact hB ⟨hdisj _ h1A, h⟩
                have h2A : p.2 ∉ A := fun h => hdisj _ h h2B
                have h1B : p.1 ∉ B := hdisj _ h1A
                refine cheb γ0 _ _ ?_ ?_ h1 h2
                · intro a b hab; apply hf; intro i
                  simp only [restrictTo, hupdΦ]
                  have : p.2 ≠ (i : Fin n) := fun e => h2A (e ▸ i.2)
                  have hc : 0 ≤ Real.sqrt (w p) * ((if p.1 = (i : Fin n) then (1:ℝ) else 0) -
                      (if p.2 = (i : Fin n) then 1 else 0)) := by
                    rw [if_neg this]; split_ifs <;> simp [Real.sqrt_nonneg]
                  nlinarith [mul_le_mul_of_nonneg_left hab hc]
                · intro a b hab; apply hg; intro i
                  simp only [restrictTo, hupdΦ]
                  have : p.1 ≠ (i : Fin n) := fun e => h1B (e ▸ i.2)
                  have hc : Real.sqrt (w p) * ((if p.1 = (i : Fin n) then (1:ℝ) else 0) -
                      (if p.2 = (i : Fin n) then 1 else 0)) ≤ 0 := by
                    rw [if_neg this]; split_ifs <;> simp [Real.sqrt_nonneg]
                  nlinarith [mul_le_mul_of_nonpos_left hab hc]
              · have h2A : p.2 ∈ A := by
                  by_contra h; exact hA ⟨h1A, h⟩
                have h1B : p.1 ∈ B := by
                  by_contra h; exact hB ⟨h, hdisj _ h2A⟩
                have h2B : p.2 ∉ B := hdisj _ h2A
                have key2 := cheb γ0 _ _ ?_ ?_ h2 h1
                · convert key2 using 1
                  · congr 1; funext a; ring
                  · ring
                · intro a b hab; apply hg; intro i
                  simp only [restrictTo, hupdΦ]
                  have : p.2 ≠ (i : Fin n) := fun e => h2B (e ▸ i.2)
                  have hc : 0 ≤ Real.sqrt (w p) * ((if p.1 = (i : Fin n) then (1:ℝ) else 0) -
                      (if p.2 = (i : Fin n) then 1 else 0)) := by
                    rw [if_neg this]; split_ifs <;> simp [Real.sqrt_nonneg]
                  nlinarith [mul_le_mul_of_nonneg_left hab hc]
                · intro a b hab; apply hf; intro i
                  simp only [restrictTo, hupdΦ]
                  have : p.1 ≠ (i : Fin n) := fun e => h1A (e ▸ i.2)
                  have hc : Real.sqrt (w p) * ((if p.1 = (i : Fin n) then (1:ℝ) else 0) -
                      (if p.2 = (i : Fin n) then 1 else 0)) ≤ 0 := by
                    rw [if_neg this]; split_ifs <;> simp [Real.sqrt_nonneg]
                  nlinarith [mul_le_mul_of_nonpos_left hab hc]
          refine ⟨⟨fun ⟨P, h1, h2, h3⟩ => hfwd P h1 h2 h3, fun h => ?_⟩,
            ⟨fun ⟨P, h1, h2, h3⟩ => hfwd P h1 h2 (hNA P h1 h3), fun h => ?_⟩, hC⟩
          · obtain ⟨P, h1, h2, _, h4, _⟩ := hC h; exact ⟨P, h1, h2, h4⟩
          · obtain ⟨P, h1, h2, _, _, h5⟩ := hC h; exact ⟨P, h1, h2, h5⟩
