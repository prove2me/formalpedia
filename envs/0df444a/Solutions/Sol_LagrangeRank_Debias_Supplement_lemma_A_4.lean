-- Prove2me | solution 1 for LagrangeRank.Debias.Supplement.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:32:26.019064+00:00
-- url     : https://prove2.me/submissions/bbbc1a31-0da8-45f9-90d6-09b18b1e9c0d

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Supplement_BTL

open LagrangeRank
open LagrangeRank.Debias
open LagrangeRank.Debias.Supplement

open MeasureTheory ProbabilityTheory Matrix Filter Topology
/-- Both conditional score CLTs, with the source's working-event interpretation made explicit. -/
theorem solution (κ c K : ℝ) (hκ : 1 ≤ κ) (hc : 0 < c) (hK : 0 < K) :
    ∃ C0 : ℝ, 0 < C0 ∧
    ∀ (n L : ℕ → ℕ) (p : ℕ → unitInterval) (θ : (t : ℕ) → Vec (n t))
      (g : (t : ℕ) → Graph (n t)) (i j : (t : ℕ) → Fin (n t)),
      Regime n L p → Density C0 n p → Rates32 n L p →
      (∀ t, Parameter κ (θ t)) → (∀ t, i t ≠ j t) →
      Tendsto (fun t => (outcomeLaw (L t) (θ t)
        {y | ¬SourceBounds (p t) c K (g t,y) (θ t)}).toReal) atTop (𝓝 0) →
      TendstoInDistribution (fun t y =>
        Real.sqrt (L t) * ((trueBlock (g t,y) (θ t)) *ᵥ grad (loss (g t,y)) (θ t)) (j t) /
          Real.sqrt (trueBlock (g t,y) (θ t) (j t) (j t)))
        atTop id (fun t => outcomeLaw (L t) (θ t)) (gaussianReal 0 1) ∧
      TendstoInDistribution (fun t y =>
        Real.sqrt (L t) *
          (((trueBlock (g t,y) (θ t)) *ᵥ grad (loss (g t,y)) (θ t)) (i t) -
           ((trueBlock (g t,y) (θ t)) *ᵥ grad (loss (g t,y)) (θ t)) (j t)) /
          Real.sqrt (pairVar (trueBlock (g t,y) (θ t)) (i t) (j t)))
        atTop id (fun t => outcomeLaw (L t) (θ t)) (gaussianReal 0 1) := by
          have prodbound : ∀ {ι : Type} (s : Finset ι) (u v : ι → ℂ), (∀ i ∈ s, ‖u i‖ ≤ 1) → (∀ i ∈ s, ‖v i‖ ≤ 1) →
              ‖∏ i ∈ s, u i - ∏ i ∈ s, v i‖ ≤ ∑ i ∈ s, ‖u i - v i‖ := by
            intro ι s u v hu hv
            classical
            induction s using Finset.induction_on with
            | empty => simp
            | insert a s ha ih =>
              rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
              have h1 := ih (fun i hi => hu i (Finset.mem_insert_of_mem hi)) (fun i hi => hv i (Finset.mem_insert_of_mem hi))
              have hua := hu a (Finset.mem_insert_self a s)
              have hpv : ‖∏ i ∈ s, v i‖ ≤ 1 := by
                rw [norm_prod]; exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i hi => hv i (Finset.mem_insert_of_mem hi))
              calc ‖u a * ∏ i ∈ s, u i - v a * ∏ i ∈ s, v i‖
                  = ‖u a * (∏ i ∈ s, u i - ∏ i ∈ s, v i) + (u a - v a) * ∏ i ∈ s, v i‖ := by ring_nf
                _ ≤ ‖u a‖ * ‖∏ i ∈ s, u i - ∏ i ∈ s, v i‖ + ‖u a - v a‖ * ‖∏ i ∈ s, v i‖ := by
                    refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
                _ ≤ 1 * (∑ i ∈ s, ‖u i - v i‖) + ‖u a - v a‖ * 1 := by gcongr
                _ = _ := by ring
          have expb : ∀ x : ℝ, |x| ≤ 1 → ‖Complex.exp (x * Complex.I) - (1 + x * Complex.I + (x * Complex.I)^2/2)‖ ≤ |x|^3 := by
            intro x hx
            have hn : ‖(x : ℂ) * Complex.I‖ ≤ 1 := by simpa using hx
            have := Complex.exp_bound hn (n := 3) (by norm_num)
            have e : ∑ m ∈ Finset.range 3, ((x:ℂ) * Complex.I) ^ m / (m.factorial : ℂ) = 1 + x * Complex.I + (x * Complex.I)^2/2 := by
              simp [Finset.sum_range_succ, Nat.factorial]
            rw [e] at this
            have hn' : ‖(x : ℂ) * Complex.I‖ = |x| := by simp
            rw [hn'] at this
            refine this.trans ?_
            have : 0 ≤ |x|^3 := by positivity
            norm_num; nlinarith
          have termb : ∀ (q a s r : ℝ), 0 ≤ q → q ≤ 1 → 0 < r → |s| * |a| / r ≤ 1 → s^2 / r^2 ≤ 1 →
              a^2 * (q*(1-q)) ≤ 1 →
              ‖(q:ℝ) • Complex.exp (↑s * ↑(a * (q - 1) / r) * Complex.I) + (1 - q : ℝ) • Complex.exp (↑s * ↑(a * q / r) * Complex.I)
                - Complex.exp (((-(s^2 * (a^2 * (q*(1-q))) / r^2 / 2)) : ℝ) : ℂ)‖ ≤
                (|s| * |a| / r + s^2 / r^2) * (s^2 * (a^2 * (q*(1-q))) / r^2) := by
            intro q a s r hq0 hq1 hr hsa hs ha
            set x1 := s * (a * (q - 1) / r) with hx1
            set x0 := s * (a * q / r) with hx0
            set V := s^2 * (a^2 * (q*(1-q))) / r^2 with hV
            have hV0 : 0 ≤ V := by
              rw [hV]; apply div_nonneg _ (by positivity)
              apply mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (mul_nonneg hq0 (by linarith)))
            have h1 : q * x1 + (1 - q) * x0 = 0 := by rw [hx1, hx0]; field_simp; ring
            have h2 : q * x1^2 + (1-q) * x0^2 = V := by rw [hx1, hx0, hV]; field_simp; ring
            have bx1 : |x1| ≤ |s| * |a| / r := by
              rw [hx1, abs_mul, abs_div, abs_mul, abs_of_pos hr]
              have : |q - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
              have : |s| * (|a| * |q - 1| / r) ≤ |s| * (|a| * 1 / r) := by gcongr
              simpa [mul_div_assoc] using this
            have bx0 : |x0| ≤ |s| * |a| / r := by
              rw [hx0, abs_mul, abs_div, abs_mul, abs_of_pos hr]
              have : |q| ≤ 1 := by rw [abs_le]; constructor <;> linarith
              have : |s| * (|a| * |q| / r) ≤ |s| * (|a| * 1 / r) := by gcongr
              simpa [mul_div_assoc] using this
            have e1 := expb x1 (bx1.trans hsa)
            have e0 := expb x0 (bx0.trans hsa)
            have c1 : |x1|^3 ≤ |s| * |a| / r * x1^2 := by
              have : |x1|^3 = |x1| * x1^2 := by rw [pow_succ, sq_abs]; ring
              rw [this]; gcongr
            have c0 : |x0|^3 ≤ |s| * |a| / r * x0^2 := by
              have : |x0|^3 = |x0| * x0^2 := by rw [pow_succ, sq_abs]; ring
              rw [this]; gcongr
            have hid : (q:ℝ) • Complex.exp (↑s * ↑(a * (q - 1) / r) * Complex.I) + (1 - q : ℝ) • Complex.exp (↑s * ↑(a * q / r) * Complex.I)
                - Complex.exp (((-(V / 2)) : ℝ) : ℂ) =
                (q:ℂ) * (Complex.exp (x1 * Complex.I) - (1 + x1 * Complex.I + (x1 * Complex.I)^2/2)) +
                ((1 - q : ℝ):ℂ) * (Complex.exp (x0 * Complex.I) - (1 + x0 * Complex.I + (x0 * Complex.I)^2/2)) +
                ((1 - V/2 - Real.exp (-(V/2)) : ℝ) : ℂ) := by
              have h1' : (q:ℂ) * x1 + (1 - q) * x0 = 0 := by exact_mod_cast h1
              have h2' : (q:ℂ) * x1^2 + (1 - q) * x0^2 = V := by exact_mod_cast h2
              simp only [Complex.real_smul, hx1, hx0, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_exp,
                Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h1' h2' ⊢
              linear_combination Complex.I * h1' + (Complex.I^2/2) * h2' + ((V:ℂ)/2) * Complex.I_sq
            rw [hid]
            have hu : |-(V/2)| ≤ 1 := by
              rw [abs_neg, abs_of_nonneg (by linarith)]
              have : V ≤ s^2 / r^2 := by
                rw [hV]; gcongr; calc s^2 * (a^2 * (q*(1-q))) ≤ s^2 * 1 := by gcongr
                  _ = s^2 := by ring
              linarith
            have ee := Real.abs_exp_sub_one_sub_id_le hu
            have hV2 : V ≤ s^2 / r^2 := by
                rw [hV]; gcongr; calc s^2 * (a^2 * (q*(1-q))) ≤ s^2 * 1 := by gcongr
                  _ = s^2 := by ring
            have n3 : ‖(((1 - V/2 - Real.exp (-(V/2))) : ℝ) : ℂ)‖ ≤ (-(V/2))^2 := by
              rw [Complex.norm_real, Real.norm_eq_abs]
              have : 1 - V/2 - Real.exp (-(V/2)) = -(Real.exp (-(V/2)) - 1 - (-(V/2))) := by ring
              rw [this, abs_neg]; exact ee
            have hq1' : 0 ≤ 1 - q := by linarith
            calc _ ≤ ‖(q:ℂ) * (Complex.exp (x1 * Complex.I) - (1 + x1 * Complex.I + (x1 * Complex.I)^2/2))‖ +
                ‖((1 - q : ℝ):ℂ) * (Complex.exp (x0 * Complex.I) - (1 + x0 * Complex.I + (x0 * Complex.I)^2/2))‖ +
                ‖(((1 - V/2 - Real.exp (-(V/2))) : ℝ) : ℂ)‖ := norm_add₃_le
              _ ≤ q * (|s| * |a| / r * x1^2) + (1 - q) * (|s| * |a| / r * x0^2) + (-(V/2))^2 := by
                rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_nonneg hq0, abs_of_nonneg hq1']
                gcongr
                · exact e1.trans c1
                · exact e0.trans c0
              _ = |s| * |a| / r * V + V * (V / 4) := by rw [← h2]; ring
              _ ≤ |s| * |a| / r * V + V * (s^2/r^2) := by
                have h4 : V/4 ≤ s^2/r^2 := by linarith
                linarith [mul_le_mul_of_nonneg_left h4 hV0]
              _ = _ := by rw [hV]; ring
          have core : ∀ (n L : ℕ → ℕ) (θ : (t:ℕ) → Vec (n t)) (a : (t:ℕ) → Edge (n t) → ℝ) (δ : ℝ), 0 < δ →
              Tendsto L atTop atTop → (∀ t e, δ ≤ (winProb (θ t) e : ℝ) * (1 - winProb (θ t) e)) →
              (∀ᶠ t in atTop, ∑ e, a t e ^ 2 * ((winProb (θ t) e : ℝ) * (1 - winProb (θ t) e)) = 1) →
              TendstoInDistribution (fun t (y : Outcomes (n t) (L t)) =>
                ∑ e, a t e * (Real.sqrt (L t) * ((winProb (θ t) e : ℝ) - ybar y e))) atTop id
                (fun t => outcomeLaw (L t) (θ t)) (gaussianReal 0 1) := by
            intro n L θ a δ hδ hL hq hsum
            refine ⟨fun t => (Measurable.of_discrete).aemeasurable, measurable_id.aemeasurable, ?_⟩
            refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun s => ?_
            simp only [ProbabilityMeasure.coe_mk, Measure.map_id, charFun_gaussianReal]
            set M : ℝ := 1 + 1/δ with hM
            set ε : ℕ → ℝ := fun t => (|s| * M * (Real.sqrt (L t))⁻¹ + s^2 * ((Real.sqrt (L t))⁻¹)^2) * s^2 with hε
            have hr : Tendsto (fun t => (Real.sqrt (L t))⁻¹) atTop (𝓝 0) :=
              tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hL))
            have hεt : Tendsto ε atTop (𝓝 0) := by
              have := ((hr.const_mul (|s| * M)).add ((hr.pow 2).const_mul (s^2))).mul_const (s^2)
              simpa [ε] using this
            have ev1 : ∀ᶠ t in atTop, |s| * M * (Real.sqrt (L t))⁻¹ ≤ 1 := by
              have := hr.const_mul (|s| * M); rw [mul_zero] at this
              exact this.eventually (ge_mem_nhds (by norm_num))
            have ev2 : ∀ᶠ t in atTop, s^2 * ((Real.sqrt (L t))⁻¹)^2 ≤ 1 := by
              have := (hr.pow 2).const_mul (s^2); rw [zero_pow two_ne_zero, mul_zero] at this
              exact this.eventually (ge_mem_nhds (by norm_num))
            have ev3 : ∀ᶠ t in atTop, 0 < L t := hL.eventually_gt_atTop 0
            rw [tendsto_iff_norm_sub_tendsto_zero]
            refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hεt
            filter_upwards [hsum, ev1, ev2, ev3] with t hs1 h1 h2 h3
            set r := Real.sqrt (L t) with hrdef
            have hr0 : 0 < r := Real.sqrt_pos.2 (by exact_mod_cast h3)
            have hrr : r^2 = (L t : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
            set q : Edge (n t) → ℝ := fun e => (winProb (θ t) e : ℝ) with hqdef
            have hSig : ∀ g : Edge (n t) → ℝ, ∑ x : Fin (L t) × Edge (n t), g x.2 = (L t : ℝ) * ∑ e, g e := by
              intro g
              rw [Fintype.sum_prod_type_right]
              simp [Finset.sum_const, Finset.mul_sum]
            have hX : ∀ y : Outcomes (n t) (L t), ∑ e, a t e * (r * (q e - ybar y e)) =
                ∑ x : Fin (L t) × Edge (n t), a t x.2 * (q x.2 - if y x then 1 else 0) / r := by
              intro y
              rw [Fintype.sum_prod_type_right]
              refine Finset.sum_congr rfl fun e _ => ?_
              simp only [ybar]
              rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_sub_distrib]
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              have hL0 : (L t : ℝ) ≠ 0 := Nat.cast_ne_zero.2 h3.ne'
              rw [← hrr]; field_simp
            have hcf : charFun (Measure.map (fun y : Outcomes (n t) (L t) =>
                ∑ e, a t e * (r * ((winProb (θ t) e : ℝ) - ybar y e))) (outcomeLaw (L t) (θ t))) s =
                ∏ x : Fin (L t) × Edge (n t), ((q x.2 : ℝ) • Complex.exp (↑s * ↑(a t x.2 * (q x.2 - 1) / r) * Complex.I) +
                  (1 - q x.2 : ℝ) • Complex.exp (↑s * ↑(a t x.2 * q x.2 / r) * Complex.I)) := by
              rw [charFun_apply_real, integral_map (Measurable.of_discrete).aemeasurable (by fun_prop)]
              have hE : ∀ y : Outcomes (n t) (L t), Complex.exp (↑s * ↑(∑ e, a t e * (r * ((winProb (θ t) e : ℝ) - ybar y e))) * Complex.I) =
                  ∏ x : Fin (L t) × Edge (n t), (fun x (b : Bool) => Complex.exp (↑s * ↑(a t x.2 * (q x.2 - if b then 1 else 0) / r) * Complex.I)) x (y x) := by
                intro y
                rw [hX y, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul, Complex.exp_sum]
              simp_rw [hE]
              rw [outcomeLaw]
              refine (integral_fintype_prod_eq_prod (𝕜 := ℂ) (E := fun _ : Fin (L t) × Edge (n t) => Bool)
                (μ := fun x => bernoulliMeasure true false (winProb (θ t) x.2))
                (fun x (b : Bool) => Complex.exp (↑s * ↑(a t x.2 * (q x.2 - if b then 1 else 0) / r) * Complex.I))).trans ?_
              refine Finset.prod_congr rfl fun x _ => ?_
              rw [integral_bernoulliMeasure]
              simp only [q]; simp
            rw [hcf]
            have hs1' : ∑ e, a t e ^ 2 * (q e * (1 - q e)) = 1 := hs1
            have hq01 : ∀ e, 0 ≤ q e ∧ q e ≤ 1 := fun e => ⟨(winProb (θ t) e).2.1, (winProb (θ t) e).2.2⟩
            have hnn : ∀ e, 0 ≤ a t e ^ 2 * (q e * (1 - q e)) := fun e =>
              mul_nonneg (sq_nonneg _) (mul_nonneg (hq01 e).1 (by linarith [(hq01 e).2]))
            have ha2 : ∀ e, a t e ^ 2 * (q e * (1 - q e)) ≤ 1 := fun e => by
              exact (Finset.single_le_sum (f := fun e => a t e ^ 2 * (q e * (1 - q e))) (fun e _ => hnn e) (Finset.mem_univ e)).trans hs1'.le
            have haM : ∀ e, |a t e| ≤ M := fun e => by
              have h5 : δ * a t e ^ 2 ≤ 1 := by
                calc δ * a t e ^ 2 ≤ (q e * (1 - q e)) * a t e ^ 2 := mul_le_mul_of_nonneg_right (hq t e) (sq_nonneg _)
                  _ = a t e ^ 2 * (q e * (1 - q e)) := mul_comm _ _
                  _ ≤ 1 := ha2 e
              have h6 : a t e ^ 2 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
              have h7 : |a t e| ≤ 1 + a t e ^ 2 := by
                have := sq_abs (a t e)
                have := sq_nonneg (|a t e| - 1/2)
                linarith [show (|a t e| - 1/2)^2 = |a t e|^2 - |a t e| + 1/4 by ring]
              rw [hM]; linarith
            have hT : Complex.exp (↑s * ↑(0:ℝ) * Complex.I - ↑((1 : NNReal) : ℝ) * ↑s ^ 2 / 2) =
                ∏ x : Fin (L t) × Edge (n t), Complex.exp (((-(s^2 * (a t x.2 ^ 2 * (q x.2 * (1 - q x.2))) / r^2 / 2)) : ℝ) : ℂ) := by
              rw [← Complex.exp_sum, ← Complex.ofReal_sum, hSig (fun e => -(s^2 * (a t e ^ 2 * (q e * (1 - q e))) / r^2 / 2))]
              congr 1
              have : ∑ e, -(s^2 * (a t e ^ 2 * (q e * (1 - q e))) / r^2 / 2) = -(s^2/r^2/2) * ∑ e, a t e ^ 2 * (q e * (1 - q e)) := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun e _ => ?_; ring
              rw [this, hs1', ← hrr]
              have hr0c : (r:ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
              push_cast
              field_simp
              ring
            rw [hT]
            refine (prodbound Finset.univ (fun x : Fin (L t) × Edge (n t) => (q x.2 : ℝ) • Complex.exp (↑s * ↑(a t x.2 * (q x.2 - 1) / r) * Complex.I) +
                  (1 - q x.2 : ℝ) • Complex.exp (↑s * ↑(a t x.2 * q x.2 / r) * Complex.I))
                (fun x : Fin (L t) × Edge (n t) => Complex.exp (((-(s^2 * (a t x.2 ^ 2 * (q x.2 * (1 - q x.2))) / r^2 / 2)) : ℝ) : ℂ)) ?_ ?_).trans ?_
            · intro x _
              refine (norm_add_le _ _).trans ?_
              rw [norm_smul, norm_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I,
                Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hq01 x.2).1,
                abs_of_nonneg (by linarith [(hq01 x.2).2])]
              linarith
            · intro x _
              rw [Complex.norm_exp_ofReal, Real.exp_le_one_iff]
              have := hnn x.2
              have : 0 ≤ s^2 * (a t x.2 ^ 2 * (q x.2 * (1 - q x.2))) / r^2 / 2 :=
                div_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) (hnn x.2)) (sq_nonneg _)) zero_le_two
              linarith
            · have hr2 : s^2 / r^2 = s^2 * r⁻¹^2 := by field_simp
              calc _ ≤ ∑ x : Fin (L t) × Edge (n t), (|s| * M * r⁻¹ + s^2 * r⁻¹^2) * (s^2 * (a t x.2 ^ 2 * (q x.2 * (1 - q x.2))) / r^2) := by
                    refine Finset.sum_le_sum fun x _ => ?_
                    refine (termb (q x.2) (a t x.2) s r (hq01 x.2).1 (hq01 x.2).2 hr0 ?_ ?_ (ha2 x.2)).trans ?_
                    · calc |s| * |a t x.2| / r ≤ |s| * M / r := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (haM x.2) (abs_nonneg s)) hr0.le
                        _ = |s| * M * r⁻¹ := by ring
                        _ ≤ 1 := h1
                    · rw [hr2]; exact h2
                    · refine mul_le_mul_of_nonneg_right (add_le_add ?_ hr2.le) (div_nonneg (mul_nonneg (sq_nonneg _) (hnn x.2)) (sq_nonneg _))
                      calc |s| * |a t x.2| / r ≤ |s| * M / r := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (haM x.2) (abs_nonneg s)) hr0.le
                          _ = |s| * M * r⁻¹ := by ring
                _ = ε t := by
                    rw [← Finset.mul_sum, hSig (fun e => s^2 * (a t e ^ 2 * (q e * (1 - q e))) / r^2)]
                    have : ∑ e, s^2 * (a t e ^ 2 * (q e * (1 - q e))) / r^2 = s^2 / r^2 * ∑ e, a t e ^ 2 * (q e * (1 - q e)) := by
                      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun e _ => ?_; ring
                    rw [this, hs1', ← hrr]
                    simp only [ε]
                    rw [← hrdef]
                    field_simp
          have gradF : ∀ (m : ℕ) (φ φ' : Edge m → ℝ → ℝ), (∀ e x, HasDerivAt (φ e) (φ' e x) x) → ∀ θ : Vec m,
              grad (fun θ : Vec m => ∑ e, φ e (θ e.val.2 - θ e.val.1)) θ =
                fun i => ∑ e, φ' e (θ e.val.2 - θ e.val.1) * ((Pi.single e.val.2 (1:ℝ) : Vec m) i - (Pi.single e.val.1 (1:ℝ) : Vec m) i) := by
            intro m φ φ' hφ θ
            funext i
            let ℓ : Edge m → (Vec m →L[ℝ] ℝ) := fun e => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) e.val.2 - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) e.val.1
            have hF : HasFDerivAt (fun θ : Vec m => ∑ e, φ e (θ e.val.2 - θ e.val.1))
                (∑ e, φ' e (θ e.val.2 - θ e.val.1) • ℓ e) θ := by
              apply HasFDerivAt.fun_sum
              intro e _
              exact (hφ e (ℓ e θ)).comp_hasFDerivAt θ (ℓ e).hasFDerivAt
            simp only [grad, hF.fderiv, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
              Pi.smul_apply, smul_eq_mul]
            refine Finset.sum_congr rfl fun e _ => ?_
            simp [ℓ, Pi.single_comm]
          have hessF : ∀ (m : ℕ) (ψ ψ' : Edge m → ℝ → ℝ), (∀ e x, HasDerivAt (ψ e) (ψ' e x) x) → ∀ θ : Vec m,
              fderiv ℝ (fun θ : Vec m => fun i => ∑ e, ψ e (θ e.val.2 - θ e.val.1) * ((Pi.single e.val.2 (1:ℝ) : Vec m) i - (Pi.single e.val.1 (1:ℝ) : Vec m) i)) θ =
                ∑ e, (ψ' e (θ e.val.2 - θ e.val.1) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) e.val.2 - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) e.val.1 : Vec m →L[ℝ] ℝ)).smulRight
                  (Pi.single e.val.2 (1:ℝ) - Pi.single e.val.1 (1:ℝ) : Vec m) := by
            intro m ψ ψ' hψ θ
            let ℓ : Edge m → (Vec m →L[ℝ] ℝ) := fun e => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) e.val.2 - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) e.val.1
            have : (fun θ : Vec m => fun i => ∑ e, ψ e (θ e.val.2 - θ e.val.1) * ((Pi.single e.val.2 (1:ℝ) : Vec m) i - (Pi.single e.val.1 (1:ℝ) : Vec m) i)) =
                fun θ => ∑ e, ψ e (ℓ e θ) • (Pi.single e.val.2 (1:ℝ) - Pi.single e.val.1 (1:ℝ) : Vec m) := by
              funext θ i; simp [ℓ]
            rw [this]
            apply HasFDerivAt.fderiv
            apply HasFDerivAt.fun_sum
            intro e _
            exact ((hψ e (ℓ e θ)).comp_hasFDerivAt θ (ℓ e).hasFDerivAt).smul_const _
          have lossD : ∀ (m L' : ℕ) (s : Data m L') (θ : Vec m),
              grad (loss s) θ = (fun i => ∑ e, (if s.1 e then (winProb θ e : ℝ) - ybar s.2 e else 0) *
                  ((Pi.single e.val.2 (1:ℝ) : Vec m) i - (Pi.single e.val.1 (1:ℝ) : Vec m) i)) ∧
              hess (loss s) θ = (fun i k => ∑ e, (if s.1 e then (winProb θ e : ℝ) * (1 - winProb θ e) else 0) *
                  ((Pi.single e.val.2 (1:ℝ) : Vec m) k - (Pi.single e.val.1 (1:ℝ) : Vec m) k) *
                  ((Pi.single e.val.2 (1:ℝ) : Vec m) i - (Pi.single e.val.1 (1:ℝ) : Vec m) i)) := by
            intro m L' s θ
            have hw : ∀ (θ : Vec m) (e : Edge m), (winProb θ e : ℝ) = Real.exp (θ e.val.2 - θ e.val.1) / (1 + Real.exp (θ e.val.2 - θ e.val.1)) := by
              intro θ e
              simp only [winProb, Real.exp_sub]
              have := Real.exp_pos (θ e.val.1)
              have := Real.exp_pos (θ e.val.2)
              field_simp
            let φ : Edge m → ℝ → ℝ := fun e x => if s.1 e then -(ybar s.2 e) * x + Real.log (1 + Real.exp x) else 0
            let φ' : Edge m → ℝ → ℝ := fun e x => if s.1 e then -(ybar s.2 e) + Real.exp x / (1 + Real.exp x) else 0
            let ψ' : Edge m → ℝ → ℝ := fun e x => if s.1 e then Real.exp x / (1 + Real.exp x)^2 else 0
            have hφ : ∀ e x, HasDerivAt (φ e) (φ' e x) x := by
              intro e x
              simp only [φ, φ']
              split_ifs
              · have h1 : HasDerivAt (fun x => Real.log (1 + Real.exp x)) (Real.exp x / (1 + Real.exp x)) x :=
                  ((Real.hasDerivAt_exp x).const_add 1).log (by positivity)
                have h2 : HasDerivAt (fun x => -(ybar s.2 e) * x + Real.log (1 + Real.exp x)) (-(ybar s.2 e) * 1 + Real.exp x / (1 + Real.exp x)) x := ((hasDerivAt_id x).const_mul (-(ybar s.2 e))).add h1
                convert h2 using 1; ring
              · exact hasDerivAt_const x 0
            have hψ : ∀ e x, HasDerivAt (φ' e) (ψ' e x) x := by
              intro e x
              simp only [φ', ψ']
              split_ifs
              · have h1 : HasDerivAt (fun x => Real.exp x / (1 + Real.exp x)) (Real.exp x / (1 + Real.exp x)^2) x := by
                  have h3 : HasDerivAt (fun x => Real.exp x / (1 + Real.exp x)) ((Real.exp x * (1 + Real.exp x) - Real.exp x * Real.exp x) / (1 + Real.exp x)^2) x :=
                    (Real.hasDerivAt_exp x).div ((Real.hasDerivAt_exp x).const_add 1) (by positivity)
                  exact h3.congr_deriv (by ring)
                exact h1.const_add _
              · exact hasDerivAt_const x 0
            have hL : loss s = fun θ : Vec m => ∑ e, φ e (θ e.val.2 - θ e.val.1) := rfl
            have hg : grad (loss s) = fun θ : Vec m => fun i => ∑ e, φ' e (θ e.val.2 - θ e.val.1) *
                ((Pi.single e.val.2 (1:ℝ) : Vec m) i - (Pi.single e.val.1 (1:ℝ) : Vec m) i) := by
              funext θ; rw [hL, gradF m φ φ' hφ θ]
            constructor
            · rw [hg]; funext i
              refine Finset.sum_congr rfl fun e _ => ?_
              simp only [φ', hw]; split_ifs <;> ring
            · funext i k
              simp only [hess]
              rw [hg, hessF m φ' ψ' hψ θ]
              simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
              refine Finset.sum_congr rfl fun e _ => ?_
              simp only [ψ', hw]
              split_ifs
              · have : 0 < 1 + Real.exp (θ e.val.2 - θ e.val.1) := by positivity
                simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.proj_apply, Pi.sub_apply, Pi.single_comm k]
                field_simp
                ring
              · simp
          have blk : ∀ (m : ℕ) (H : Matrix (Fin m) (Fin m) ℝ), IsUnit (borderedHessian H (fun _ => 1)).det →
              (∀ i, ∑ l, (borderedHessian H (fun _ => 1))⁻¹.toBlocks₁₁ i l = 0) ∧
              (∀ i k, ∑ l, (borderedHessian H (fun _ => 1))⁻¹.toBlocks₁₁ i l * H l k +
                (borderedHessian H (fun _ => 1))⁻¹ (Sum.inl i) (Sum.inr ()) = if i = k then 1 else 0) := by
            intro m H ht
            have hM := Matrix.nonsing_inv_mul _ ht
            constructor
            · intro i
              have := congrFun (congrFun hM (Sum.inl i)) (Sum.inr ())
              simpa [Matrix.mul_apply, Fintype.sum_sum_type, borderedHessian, Matrix.toBlocks₁₁] using this
            · intro i k
              have := congrFun (congrFun hM (Sum.inl i)) (Sum.inl k)
              simpa [Matrix.mul_apply, Fintype.sum_sum_type, borderedHessian, Matrix.toBlocks₁₁, Matrix.one_apply] using this
          refine ⟨1, one_pos, ?_⟩
          intro n L p θ g i j hreg _hden _hrate hpar hij hsrc
          set δ : ℝ := 1 / (2 + 2 * κ) with hδdef
          have hδ : 0 < δ := by rw [hδdef]; exact div_pos one_pos (by linarith)
          have hδq : ∀ t e, δ ≤ (winProb (θ t) e : ℝ) * (1 - winProb (θ t) e) := by
            intro t e
            have h1 := (hpar t).2 e.val.1 e.val.2
            have h2 := (hpar t).2 e.val.2 e.val.1
            have hw : (winProb (θ t) e : ℝ) = Real.exp (θ t e.val.2) / (Real.exp (θ t e.val.1) + Real.exp (θ t e.val.2)) := rfl
            rw [hw]
            rw [Real.exp_sub] at h1 h2
            have E1 := Real.exp_pos (θ t e.val.1)
            have E2 := Real.exp_pos (θ t e.val.2)
            rw [div_le_iff₀ E2] at h1
            rw [div_le_iff₀ E1] at h2
            have key : Real.exp (θ t e.val.2) / (Real.exp (θ t e.val.1) + Real.exp (θ t e.val.2)) *
                (1 - Real.exp (θ t e.val.2) / (Real.exp (θ t e.val.1) + Real.exp (θ t e.val.2))) =
                Real.exp (θ t e.val.1) * Real.exp (θ t e.val.2) / (Real.exp (θ t e.val.1) + Real.exp (θ t e.val.2))^2 := by
              field_simp; ring
            rw [key, hδdef, div_le_div_iff₀ (by linarith) (by positivity)]
            set u1 := Real.exp (θ t e.val.1)
            set u2 := Real.exp (θ t e.val.2)
            have k1 := mul_le_mul_of_nonneg_left h1 E1.le
            have k2 := mul_le_mul_of_nonneg_left h2 E2.le
            have q1 : 1 * (u1 + u2)^2 = u1 * u1 + u2 * u2 + 2 * (u1 * u2) := by ring
            have q2 : u1 * u2 * (2 + 2 * κ) = 2 * (u1 * u2) + u1 * (κ * u2) + u2 * (κ * u1) := by ring
            rw [q1, q2]; linarith
          let D : (t : ℕ) → Edge (n t) → Vec (n t) := fun t e l =>
            (Pi.single e.val.2 (1:ℝ) : Vec (n t)) l - (Pi.single e.val.1 (1:ℝ) : Vec (n t)) l
          let cw : (t : ℕ) → Edge (n t) → ℝ := fun t e =>
            if g t e then (winProb (θ t) e : ℝ) * (1 - winProb (θ t) e) else 0
          let H : (t : ℕ) → Matrix (Fin (n t)) (Fin (n t)) ℝ := fun t i k => ∑ e, cw t e * D t e k * D t e i
          have hH : ∀ t (y : Outcomes (n t) (L t)), hess (loss (g t, y)) (θ t) = H t :=
            fun t y => (lossD _ _ (g t, y) (θ t)).2
          have hc0 : ∀ t e, 0 ≤ cw t e := by
            intro t e; simp only [cw]; split_ifs
            · exact le_trans hδ.le (hδq t e)
            · exact le_rfl
          have hdet : ∀ᶠ t in atTop, IsUnit (borderedHessian (H t) (fun _ => 1)).det := by
            have := hsrc.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))
            filter_upwards [this] with t ht
            by_contra hnot
            have hall : ∀ y : Outcomes (n t) (L t), y ∈ {y | ¬SourceBounds (p t) c K (g t, y) (θ t)} := by
              intro y hy
              apply hnot
              have h5 := hy.2.2.2.2.1
              rwa [hH] at h5
            rw [Set.eq_univ_of_forall hall, measure_univ, ENNReal.toReal_one] at ht
            exact lt_irrefl _ ht
          let A : (t : ℕ) → Matrix (Fin (n t)) (Fin (n t)) ℝ := fun t => (borderedHessian (H t) (fun _ => 1))⁻¹.toBlocks₁₁
          have hA : ∀ t (y : Outcomes (n t) (L t)), trueBlock (g t, y) (θ t) = A t := by
            intro t y; simp only [trueBlock, inverseAt, hH, A]
          have vec : ∀ v : (t : ℕ) → Vec (n t), (∀ t (b : ℝ), ∃ k, v t k ≠ b) →
              TendstoInDistribution (fun t (y : Outcomes (n t) (L t)) =>
                Real.sqrt (L t) * (v t ⬝ᵥ (A t *ᵥ grad (loss (g t, y)) (θ t))) / Real.sqrt (v t ⬝ᵥ (A t *ᵥ v t)))
                atTop id (fun t => outcomeLaw (L t) (θ t)) (gaussianReal 0 1) := by
            intro v hv
            let r : (t : ℕ) → Vec (n t) := fun t => v t ᵥ* A t
            let V : ℕ → ℝ := fun t => v t ⬝ᵥ (A t *ᵥ v t)
            let a : (t : ℕ) → Edge (n t) → ℝ := fun t e => (if g t e then r t ⬝ᵥ D t e else 0) / Real.sqrt (V t)
            have hrH : ∀ t (w : Vec (n t)) k, (w ᵥ* H t) k = ∑ e, cw t e * (w ⬝ᵥ D t e) * D t e k := by
              intro t w k
              simp only [Matrix.vecMul, dotProduct, H, Finset.mul_sum, Finset.sum_mul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun e _ => ?_
              refine Finset.sum_congr rfl fun l _ => ?_
              ring
            have hkey : ∀ᶠ t in atTop, 0 < V t ∧ ∑ e, cw t e * (r t ⬝ᵥ D t e)^2 = V t := by
              filter_upwards [hdet] with t ht
              obtain ⟨b1, b2⟩ := blk _ (H t) ht
              set β := ∑ i, v t i * (borderedHessian (H t) (fun _ => 1))⁻¹ (Sum.inl i) (Sum.inr ()) with hβ
              have hrH2 : ∀ k, (r t ᵥ* H t) k = v t k - β := by
                intro k
                simp only [r]
                rw [Matrix.vecMul_vecMul]
                have hAH : ∀ i, (A t * H t) i k = (if i = k then 1 else 0) -
                    (borderedHessian (H t) (fun _ => 1))⁻¹ (Sum.inl i) (Sum.inr ()) := by
                  intro i; rw [Matrix.mul_apply]; linarith [b2 i k]
                simp only [Matrix.vecMul, dotProduct, hAH, mul_sub, Finset.sum_sub_distrib, hβ]
                congr 1
                simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
              have hsr : ∑ k, r t k = 0 := by
                simp only [r, Matrix.vecMul, dotProduct]
                rw [Finset.sum_comm]
                refine Finset.sum_eq_zero fun i _ => ?_
                rw [← Finset.mul_sum, show ∑ k, A t i k = 0 from b1 i, mul_zero]
              have hV : V t = r t ⬝ᵥ v t := by
                simp only [V, r]; rw [Matrix.dotProduct_mulVec]
              have hQ : ∑ e, cw t e * (r t ⬝ᵥ D t e)^2 = (r t ᵥ* H t) ⬝ᵥ r t := by
                rw [show (r t ᵥ* H t) ⬝ᵥ r t = ∑ k, (r t ᵥ* H t) k * r t k from rfl]
                simp_rw [hrH t (r t), Finset.sum_mul]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun e _ => ?_
                calc cw t e * (r t ⬝ᵥ D t e)^2 = cw t e * (r t ⬝ᵥ D t e) * ∑ k, r t k * D t e k := by
                      rw [sq, ← mul_assoc]; rfl
                  _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
              have hQV : (r t ᵥ* H t) ⬝ᵥ r t = V t := by
                have : (r t ᵥ* H t) ⬝ᵥ r t = ∑ k, (v t k * r t k) - β * ∑ k, r t k := by
                  simp only [dotProduct, hrH2, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
                rw [this, hsr, mul_zero, sub_zero, hV, dotProduct_comm]; rfl
              refine ⟨?_, hQ.trans hQV⟩
              by_contra hneg
              push Not at hneg
              have hnn : ∀ e, 0 ≤ cw t e * (r t ⬝ᵥ D t e)^2 := fun e => mul_nonneg (hc0 t e) (sq_nonneg _)
              have hterm : ∀ e, cw t e * (r t ⬝ᵥ D t e) = 0 := by
                intro e
                have h0 : cw t e * (r t ⬝ᵥ D t e)^2 = 0 := by
                  have := Finset.single_le_sum (f := fun e => cw t e * (r t ⬝ᵥ D t e)^2) (fun e _ => hnn e) (Finset.mem_univ e)
                  have := hQ.trans hQV
                  linarith [hnn e]
                rcases mul_eq_zero.1 h0 with h | h
                · rw [h, zero_mul]
                · rw [pow_eq_zero_iff two_ne_zero] at h; rw [h, mul_zero]
              obtain ⟨k, hk⟩ := hv t β
              apply hk
              have := hrH2 k
              rw [hrH t (r t) k] at this
              simp only [hterm, zero_mul, Finset.sum_const_zero] at this
              linarith
            have hsum : ∀ᶠ t in atTop, ∑ e, a t e ^ 2 * ((winProb (θ t) e : ℝ) * (1 - winProb (θ t) e)) = 1 := by
              filter_upwards [hkey] with t ht
              obtain ⟨hVpos, hQ⟩ := ht
              have : ∀ e, a t e ^ 2 * ((winProb (θ t) e : ℝ) * (1 - winProb (θ t) e)) = cw t e * (r t ⬝ᵥ D t e)^2 / V t := by
                intro e; simp only [a, cw]; rw [div_pow, Real.sq_sqrt hVpos.le]; split_ifs <;> ring
              simp_rw [this]; rw [← Finset.sum_div, hQ, div_self hVpos.ne']
            have hc := core n L θ a δ hδ hreg.L_inf hδq hsum
            refine ⟨fun t => (Measurable.of_discrete).aemeasurable, by fun_prop, hc.tendsto.congr' ?_⟩
            filter_upwards [hkey] with t _
            apply Subtype.ext
            show Measure.map _ (outcomeLaw (L t) (θ t)) = Measure.map _ (outcomeLaw (L t) (θ t))
            congr 1
            funext y
            rw [(lossD _ _ (g t, y) (θ t)).1, Matrix.dotProduct_mulVec]
            have hG : (v t ᵥ* A t) ⬝ᵥ (fun i => ∑ e, (if (g t, y).1 e then (winProb (θ t) e : ℝ) - ybar (g t, y).2 e else 0) *
                  ((Pi.single e.val.2 (1:ℝ) : Vec (n t)) i - (Pi.single e.val.1 (1:ℝ) : Vec (n t)) i)) =
                ∑ e, (if g t e then r t ⬝ᵥ D t e else 0) * ((winProb (θ t) e : ℝ) - ybar y e) := by
              simp only [dotProduct, Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun e _ => ?_
              split_ifs
              · rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun l _ => ?_; simp only [r, D]; ring
              · simp
            rw [hG, Finset.mul_sum, Finset.sum_div]
            refine Finset.sum_congr rfl fun e _ => ?_
            simp only [a]; ring
          have hne : ∀ t, ∃ k : Fin (n t), k ≠ j t := by
            intro t
            have : Nontrivial (Fin (n t)) := Fin.nontrivial_iff_two_le.2 (hreg.n_ge t)
            exact exists_ne (j t)
          constructor
          · have e1 : (fun t (y : Outcomes (n t) (L t)) => Real.sqrt (L t) * ((trueBlock (g t,y) (θ t)) *ᵥ grad (loss (g t,y)) (θ t)) (j t) /
                  Real.sqrt (trueBlock (g t,y) (θ t) (j t) (j t))) =
                (fun t (y : Outcomes (n t) (L t)) => Real.sqrt (L t) * ((Pi.single (j t) 1 : Vec (n t)) ⬝ᵥ (A t *ᵥ grad (loss (g t, y)) (θ t))) /
                  Real.sqrt ((Pi.single (j t) 1 : Vec (n t)) ⬝ᵥ (A t *ᵥ (Pi.single (j t) 1 : Vec (n t))))) := by
              funext t y; rw [hA, single_dotProduct, single_dotProduct, one_mul, one_mul, Matrix.mulVec_single_one]; rfl
            rw [e1]
            refine vec _ fun t b => ?_
            by_cases hb : b = 1
            · obtain ⟨k, hk⟩ := hne t
              refine ⟨k, ?_⟩
              rw [Pi.single_eq_of_ne hk, hb]; exact zero_ne_one
            · refine ⟨j t, ?_⟩
              rw [Pi.single_eq_same]; exact fun h => hb h.symm
          · have e2 : (fun t (y : Outcomes (n t) (L t)) => Real.sqrt (L t) *
                  (((trueBlock (g t,y) (θ t)) *ᵥ grad (loss (g t,y)) (θ t)) (i t) -
                   ((trueBlock (g t,y) (θ t)) *ᵥ grad (loss (g t,y)) (θ t)) (j t)) /
                  Real.sqrt (pairVar (trueBlock (g t,y) (θ t)) (i t) (j t))) =
                (fun t (y : Outcomes (n t) (L t)) => Real.sqrt (L t) * ((Pi.single (i t) 1 - Pi.single (j t) 1 : Vec (n t)) ⬝ᵥ (A t *ᵥ grad (loss (g t, y)) (θ t))) /
                  Real.sqrt ((Pi.single (i t) 1 - Pi.single (j t) 1 : Vec (n t)) ⬝ᵥ (A t *ᵥ (Pi.single (i t) 1 - Pi.single (j t) 1 : Vec (n t))))) := by
              funext t y
              rw [hA, pairVar]
              have hn : ∀ w : Vec (n t), w (i t) - w (j t) = (Pi.single (i t) 1 - Pi.single (j t) 1 : Vec (n t)) ⬝ᵥ w := fun w => by
                rw [sub_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul]
              rw [hn]
            rw [e2]
            refine vec _ fun t b => ?_
            by_cases hb : b = 1
            · refine ⟨j t, ?_⟩
              rw [Pi.sub_apply, Pi.single_eq_of_ne (hij t).symm, Pi.single_eq_same, hb]; norm_num
            · refine ⟨i t, ?_⟩
              rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (hij t), sub_zero]; exact fun h => hb h.symm
