-- Prove2me | solution 1 for MarketInterference.FluidBias.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:09:39.483482+00:00
-- url     : https://prove2.me/submissions/b8fb5947-6755-446f-a607-7d3259a48554

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_Supplement_RandomAllocation

open MarketInterference
open MarketInterference.FluidBias
open MarketInterference.FluidBias.Supplement

open MeasureTheory Filter

theorem solution {nd ns : ℕ} {I E Ω : Type} [Fintype I] [Fintype E]
    [DecidableEq I] [DecidableEq E] [MeasurableSpace Ω]
    (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (ρ : ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (htreat : ∀ i, 0 ≤ lam i + beta i) (hpi : ∀ j, 0 ≤ pi j)
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → Counts nd ns)
    (hlaw : ∀ n, HasExperimentLaw μ (X n) lam beta pi ρ (n + 1 : ℕ))
    (A : ∀ n, BlindAllocation N μ (X n) (n + 1 : ℕ))
    (hprimal : ∃! x, IsOptimal N 1 (lam + ρ • beta) pi x)
    (hdual : ∃! q, IsOptimalDual N 1 (lam + ρ • beta) pi q)
    (hsign : (∀ i, 0 ≤ beta i) ∨ (∀ i, beta i ≤ 0)) :
    (∀ n, Integrable (fun ω => twoLP N ρ (n + 1 : ℕ) (X n ω)) μ) ∧
    (∀ᵐ ω ∂μ, Tendsto (fun n => twoLP N ρ (n + 1 : ℕ) (X n ω)) atTop
      (nhds (Delta N lam beta pi))) ∧
    Tendsto (fun n => ∫ ω, twoLP N ρ (n + 1 : ℕ) (X n ω) ∂μ) atTop
      (nhds (Delta N lam beta pi)) := by
        classical
        -- boundedness of objective
        obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ e, |N.v e| * N.k e := ⟨_, rfl⟩
        have hobj : ∀ d s x, Feasible N 1 d s x → |obj N x| ≤ B := by
          intro d s x hx
          rw [hB, obj]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
          have h := hx.1 e
          rw [abs_mul, abs_of_nonneg h.1]
          have h2 := h.2
          rw [one_mul] at h2
          exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        have hB0 : 0 ≤ B := by
          rw [hB]
          exact Finset.sum_nonneg fun e _ => mul_nonneg (abs_nonneg _) (N.k_nonneg e)
        have hbdd : ∀ d s, BddAbove (obj N '' {x | Feasible N 1 d s x}) := by
          rintro d s
          refine ⟨B, ?_⟩
          rintro _ ⟨x, hx, rfl⟩
          exact (abs_le.1 (hobj d s x hx)).2
        have hPhiB : ∀ d s, |Phi N 1 d s| ≤ B := by
          intro d s
          rw [Phi]
          rcases Set.eq_empty_or_nonempty (obj N '' {x | Feasible N 1 d s x}) with h | h
          · rw [h]; simpa using hB0
          · rw [abs_le]
            refine ⟨?_, csSup_le h ?_⟩
            · obtain ⟨_, x, hx, rfl⟩ := h
              exact (abs_le.1 (hobj d s x hx)).1.trans (le_csSup (hbdd d s) ⟨x, hx, rfl⟩)
            · rintro _ ⟨x, hx, rfl⟩
              exact (abs_le.1 (hobj d s x hx)).2
        have hzero : ∀ d s, (∀ i, 0 ≤ d i) → (∀ j, 0 ≤ s j) → Feasible N 1 d s 0 := by
          intro d s hd hs
          refine ⟨fun e => ⟨le_rfl, by simpa using N.k_nonneg e⟩, ?_, ?_, ?_⟩ <;> intro i <;> simp [hd, hs]
        -- continuity of Phi
        have hcont : ∀ (dn : ℕ → Fin nd → ℝ) (sn : ℕ → Fin ns → ℝ) (d : Fin nd → ℝ) (s : Fin ns → ℝ),
            (∀ n i, 0 ≤ dn n i) → (∀ n j, 0 ≤ sn n j) → (∀ i, 0 ≤ d i) → (∀ j, 0 ≤ s j) →
            (∀ i, Tendsto (fun n => dn n i) atTop (nhds (d i))) →
            (∀ j, Tendsto (fun n => sn n j) atTop (nhds (s j))) →
            Tendsto (fun n => Phi N 1 (dn n) (sn n)) atTop (nhds (Phi N 1 d s)) := by
          intro dn sn d s hdn hsn hd hs hdl hsl
          refine tendsto_order.2 ⟨?_, ?_⟩
          · intro c hc
            obtain ⟨_, ⟨x, hx, rfl⟩, hcx⟩ := exists_lt_of_lt_csSup
              (⟨_, 0, hzero d s hd hs, rfl⟩ : (obj N '' {x | Feasible N 1 d s x}).Nonempty) hc
            have hx : Feasible N 1 d s x := hx
            obtain ⟨θ, hθc, hθ0, hθ1⟩ : ∃ θ : ℝ, c < θ * obj N x ∧ 0 < θ ∧ θ < 1 := by
              have hcθ : Tendsto (fun θ : ℝ => θ * obj N x) (nhdsWithin 1 (Set.Iio 1))
                  (nhds (1 * obj N x)) :=
                ((continuous_id.mul continuous_const).tendsto 1).mono_left nhdsWithin_le_nhds
              rw [one_mul] at hcθ
              have h1 := hcθ.eventually (lt_mem_nhds hcx)
              have h2 : ∀ᶠ θ : ℝ in nhdsWithin 1 (Set.Iio 1), 0 < θ :=
                nhdsWithin_le_nhds (lt_mem_nhds one_pos)
              have h3 : ∀ᶠ θ : ℝ in nhdsWithin 1 (Set.Iio 1), θ < 1 := self_mem_nhdsWithin
              exact ((h1.and (h2.and h3))).exists
            have key : ∀ (m : ℕ) (f : ℕ → Fin m → ℝ) (g : Fin m → ℝ), (∀ n i, 0 ≤ f n i) →
                (∀ i, 0 ≤ g i) → (∀ i, Tendsto (fun n => f n i) atTop (nhds (g i))) →
                ∀ᶠ n in atTop, ∀ i, θ * g i ≤ f n i := by
              intro m f g hf hg hl
              rw [eventually_all]
              intro i
              rcases (hg i).eq_or_lt with h | h
              · rw [← h]; filter_upwards with n
                rw [mul_zero]; exact hf n i
              · have : θ * g i < g i := by nlinarith
                filter_upwards [(hl i).eventually (lt_mem_nhds this)] with n hn using hn.le
            filter_upwards [key _ dn d hdn hd hdl, key _ sn s hsn hs hsl] with n h1 h2
            refine hθc.trans_le ?_
            have hf : Feasible N 1 (dn n) (sn n) (fun e => θ * x e) := by
              refine ⟨fun e => ⟨mul_nonneg hθ0.le (hx.1 e).1, ?_⟩, fun i => ?_, fun j => ?_, fun u => ?_⟩
              · have := (hx.1 e).2
                have h0 := (hx.1 e).1
                nlinarith
              · rw [← Finset.mul_sum]
                exact (mul_le_mul_of_nonneg_left (hx.2.1 i) hθ0.le).trans (h1 i)
              · rw [← Finset.mul_sum]
                exact (mul_le_mul_of_nonneg_left (hx.2.2.1 j) hθ0.le).trans (h2 j)
              · rw [← Finset.mul_sum, ← Finset.mul_sum, hx.2.2.2 u]
            refine le_csSup (hbdd _ _) ⟨_, hf, ?_⟩
            simp only [obj, Finset.mul_sum]
            exact Finset.sum_congr rfl fun e _ => by ring
          · intro c hc
            obtain ⟨c', hc1, hc2⟩ := exists_between hc
            have hev : ∀ᶠ n in atTop, ∀ x, Feasible N 1 (dn n) (sn n) x → obj N x ≤ c' := by
              by_contra hcon
              rw [not_eventually] at hcon
              obtain ⟨φ, hφ, hφ2⟩ := extraction_of_frequently_atTop hcon
              push Not at hφ2
              choose x hx hxo using hφ2
              have hK : IsCompact (Set.pi Set.univ (fun e : E => Set.Icc (0:ℝ) (N.k e))) :=
                isCompact_univ_pi fun e => isCompact_Icc
              obtain ⟨y, hy, ψ, hψ, hlim⟩ := hK.tendsto_subseq (x := x) (fun n e _ =>
                ⟨((hx n).1 e).1, by simpa using ((hx n).1 e).2⟩)
              have hl : ∀ e, Tendsto (fun n => x (ψ n) e) atTop (nhds (y e)) := by
                intro e
                exact (tendsto_pi_nhds.1 hlim e)
              have hsub : Tendsto (fun n => φ (ψ n)) atTop atTop :=
                hφ.tendsto_atTop.comp hψ.tendsto_atTop
              have hyf : Feasible N 1 d s y := by
                refine ⟨fun e => ?_, fun i => ?_, fun j => ?_, fun u => ?_⟩
                · have := hy e (Set.mem_univ e)
                  exact ⟨this.1, by simpa using this.2⟩
                · exact le_of_tendsto_of_tendsto' (tendsto_finsetSum _ fun e _ => hl e)
                    ((hdl i).comp hsub) (fun n => (hx (ψ n)).2.1 i)
                · exact le_of_tendsto_of_tendsto' (tendsto_finsetSum _ fun e _ => hl e)
                    ((hsl j).comp hsub) (fun n => (hx (ψ n)).2.2.1 j)
                · exact tendsto_nhds_unique_of_eventuallyEq (tendsto_finsetSum _ fun e _ => hl e)
                    (tendsto_finsetSum _ fun e _ => hl e)
                    (Eventually.of_forall fun n => (hx (ψ n)).2.2.2 u)
              have hyo : c' ≤ obj N y := by
                refine ge_of_tendsto' (f := fun n => obj N (x (ψ n))) (x := atTop) ?_
                  (fun n => (hxo (ψ n)).le)
                exact tendsto_finsetSum _ fun e _ => (hl e).const_mul _
              have : obj N y ≤ Phi N 1 d s := le_csSup (hbdd _ _) ⟨y, hyf, rfl⟩
              linarith
            filter_upwards [hev] with n hn
            refine lt_of_le_of_lt (csSup_le ⟨_, 0, hzero _ _ (hdn n) (hsn n), rfl⟩ ?_) hc2
            rintro _ ⟨x, hx, rfl⟩
            exact hn x hx
        -- Poisson moment generating function and Chernoff
        have hP : ∀ (r s a : ℝ), 0 ≤ r →
            (ProbabilityTheory.poissonMeasure (Real.toNNReal r)).real {k : ℕ | a ≤ s * (k:ℝ)} ≤
              Real.exp (-a + r * (Real.exp s - 1)) := by
          intro r s a hr
          have hs : HasSum (fun k : ℕ => Real.exp (-r) * r ^ k / (k.factorial : ℝ) * Real.exp (s * k))
              (Real.exp (r * (Real.exp s - 1))) := by
            have h := (NormedSpace.expSeries_div_hasSum_exp (r * Real.exp s)).mul_left (Real.exp (-r))
            rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add] at h
            have e1 : (fun k : ℕ => Real.exp (-r) * r ^ k / (k.factorial : ℝ) * Real.exp (s * k)) =
                fun k : ℕ => Real.exp (-r) * ((r * Real.exp s) ^ k / (k.factorial : ℝ)) := by
              funext k
              rw [mul_pow, ← Real.exp_nat_mul, mul_comm s]
              ring
            have e2 : r * (Real.exp s - 1) = -r + r * Real.exp s := by ring
            rw [e1, e2]
            exact h
          have hr' : ((Real.toNNReal r : NNReal) : ℝ) = r := Real.coe_toNNReal r hr
          have hint : Integrable (fun k : ℕ => Real.exp (s * k))
              (ProbabilityTheory.poissonMeasure (Real.toNNReal r)) := by
            rw [ProbabilityTheory.integrable_poissonMeasure_iff, hr']
            simpa using hs.summable
          have hval : ∫ k : ℕ, Real.exp (s * k) ∂(ProbabilityTheory.poissonMeasure (Real.toNNReal r))
              = Real.exp (r * (Real.exp s - 1)) := by
            rw [ProbabilityTheory.integral_poissonMeasure, hr']
            simpa using hs.tsum_eq
          have hch := ProbabilityTheory.measure_ge_le_exp_mul_mgf
            (μ := ProbabilityTheory.poissonMeasure (Real.toNNReal r))
            (X := fun k : ℕ => s * (k:ℝ)) (t := 1) a zero_le_one (by simpa using hint)
          refine hch.trans (le_of_eq ?_)
          rw [ProbabilityTheory.mgf]
          simp only [one_mul]
          rw [hval, ← Real.exp_add]
          congr 1; ring
        -- almost sure convergence
        have hAS : ∀ (r : ℝ) (Y : ℕ → Ω → ℕ), 0 ≤ r → (∀ n, Measurable (Y n)) →
            (∀ n, Measure.map (Y n) μ =
              ProbabilityTheory.poissonMeasure (Real.toNNReal (r * ((n + 1 : ℕ) : ℝ)))) →
            ∀ᵐ ω ∂μ, Tendsto (fun n => (Y n ω : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (nhds r) := by
          intro r Y hr hY hYl
          have hBC : ∀ s b : ℝ, 0 < b - r * (Real.exp s - 1) →
              ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, s * (Y n ω : ℝ) < b * ((n + 1 : ℕ) : ℝ) := by
            intro s b hc
            set c := b - r * (Real.exp s - 1) with hcdef
            have hle : ∀ n, μ {ω | b * ((n + 1 : ℕ) : ℝ) ≤ s * (Y n ω : ℝ)} ≤
                ENNReal.ofReal (Real.exp (-c) ^ (n + 1)) := by
              intro n
              have h1 : μ {ω | b * ((n + 1 : ℕ) : ℝ) ≤ s * (Y n ω : ℝ)} =
                  Measure.map (Y n) μ {k : ℕ | b * ((n + 1 : ℕ) : ℝ) ≤ s * (k:ℝ)} := by
                rw [Measure.map_apply (hY n) (MeasurableSet.of_discrete)]
                rfl
              rw [h1, hYl n, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
              refine ENNReal.ofReal_le_ofReal ?_
              refine (hP (r * ((n + 1 : ℕ) : ℝ)) s (b * ((n + 1 : ℕ) : ℝ)) (by positivity)).trans
                (le_of_eq ?_)
              rw [← Real.exp_nat_mul]
              congr 1
              rw [hcdef]; ring
            have hsum : Summable (fun n : ℕ => Real.exp (-c) ^ (n + 1)) := by
              refine (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (Real.exp_pos _).le ?_)
              rw [Real.exp_lt_one_iff]; linarith
            have hne : (∑' n, μ {ω | b * ((n + 1 : ℕ) : ℝ) ≤ s * (Y n ω : ℝ)}) ≠ ⊤ :=
              ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hle)
            filter_upwards [ae_eventually_notMem hne] with ω hω
            filter_upwards [hω] with n hn
            simpa using hn
          have hex : ∀ u : ℝ, 0 < u → ∀ ε : ℝ, 0 < ε → u ≤ 1 → r * u < ε →
              0 < u * (r + ε) - r * (Real.exp u - 1) ∧ 0 < (-u) * (r - ε) - r * (Real.exp (-u) - 1) := by
            intro u hu ε hε hu1 hru
            have h1 := Real.abs_exp_sub_one_sub_id_le (x := u) (by rw [abs_of_pos hu]; exact hu1)
            have h2 := Real.abs_exp_sub_one_sub_id_le (x := -u) (by rw [abs_neg, abs_of_pos hu]; exact hu1)
            have h1' := mul_le_mul_of_nonneg_left (abs_le.1 h1).2 hr
            have h2' := mul_le_mul_of_nonneg_left (abs_le.1 h2).2 hr
            have h3 := mul_lt_mul_of_pos_left hru hu
            constructor <;> nlinarith
          have hm : ∀ m : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
              |(Y n ω : ℝ) / ((n + 1 : ℕ) : ℝ) - r| < 1 / ((m:ℝ) + 1) := by
            intro m
            have hε : 0 < 1 / ((m:ℝ) + 1) := by positivity
            set ε := 1 / ((m:ℝ) + 1)
            obtain ⟨u, hu0, hu1, hu2⟩ : ∃ u : ℝ, 0 < u ∧ u ≤ 1 ∧ r * u < ε := by
              refine ⟨min 1 (ε / (r + 1)), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
              have h1 : r * min 1 (ε / (r + 1)) ≤ r * (ε / (r + 1)) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) hr
              refine h1.trans_lt ?_
              rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
              nlinarith
            obtain ⟨ha, hb⟩ := hex u hu0 ε hε hu1 hu2
            filter_upwards [hBC _ _ ha, hBC _ _ hb] with ω h1 h2
            filter_upwards [h1, h2] with n h1 h2
            have hn : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
            rw [abs_lt]
            constructor
            · rw [lt_sub_iff_add_lt, lt_div_iff₀ hn]
              have : u * ((r - ε) * ((n + 1 : ℕ) : ℝ)) < u * (Y n ω : ℝ) := by linarith
              have := lt_of_mul_lt_mul_left this hu0.le
              linarith
            · rw [sub_lt_iff_lt_add, div_lt_iff₀ hn]
              have : u * (Y n ω : ℝ) < u * ((r + ε) * ((n + 1 : ℕ) : ℝ)) := by linarith
              have := lt_of_mul_lt_mul_left this hu0.le
              linarith
          filter_upwards [ae_all_iff.2 hm] with ω hω
          rw [Metric.tendsto_nhds]
          intro ε hε
          obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
          filter_upwards [hω m] with n hn
          rw [Real.dist_eq]
          exact hn.trans hm
        -- marginals
        have hmX : ∀ n, Measurable (X n) := fun n => (hlaw n).1
        have hpo : ∀ (m : ℕ) (f : Fin m → ℝ), IsProbabilityMeasure
            (MarketInterference.FiniteSample.poisLaw f) := by
          intro m f
          unfold MarketInterference.FiniteSample.poisLaw
          infer_instance
        have hpm : ∀ (m : ℕ) (f : Fin m → ℝ) (i : Fin m), Measure.map (fun z : Fin m → ℕ => z i)
            (MarketInterference.FiniteSample.poisLaw f) =
            ProbabilityTheory.poissonMeasure (Real.toNNReal (f i)) := by
          intro m f i
          unfold MarketInterference.FiniteSample.poisLaw
          exact (measurePreserving_eval (fun i => ProbabilityTheory.poissonMeasure (Real.toNNReal (f i))) i).map_eq
        have hC : ∀ i, ∀ᵐ ω ∂μ, Tendsto (fun n => ((X n ω).1.1 i : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop
            (nhds ((1 - ρ) * lam i)) := by
          intro i
          refine hAS ((1 - ρ) * lam i) (fun n ω => (X n ω).1.1 i)
            (mul_nonneg (by linarith) (hlam i)) (fun n => ?_) (fun n => ?_)
          · exact (measurable_pi_apply i).comp (measurable_fst.comp (measurable_fst.comp (hmX n)))
          · have h : (fun ω => (X n ω).1.1 i) = (fun z : Fin nd → ℕ => z i) ∘ Prod.fst ∘ Prod.fst ∘ X n := rfl
            rw [h, ← Measure.map_map (measurable_pi_apply i)
              (measurable_fst.comp (measurable_fst.comp (hmX n))),
              ← Measure.map_map measurable_fst (measurable_fst.comp (hmX n)),
              ← Measure.map_map measurable_fst (hmX n), (hlaw n).2]
            unfold MarketInterference.FiniteSample.experimentLaw
            rw [measurePreserving_fst.map_eq, measurePreserving_fst.map_eq, hpm]
        have hT : ∀ i, ∀ᵐ ω ∂μ, Tendsto (fun n => ((X n ω).1.2 i : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop
            (nhds (ρ * (lam i + beta i))) := by
          intro i
          refine hAS (ρ * (lam i + beta i)) (fun n ω => (X n ω).1.2 i)
            (mul_nonneg hρ.le (htreat i)) (fun n => ?_) (fun n => ?_)
          · exact (measurable_pi_apply i).comp (measurable_snd.comp (measurable_fst.comp (hmX n)))
          · have h : (fun ω => (X n ω).1.2 i) = (fun z : Fin nd → ℕ => z i) ∘ Prod.snd ∘ Prod.fst ∘ X n := rfl
            rw [h, ← Measure.map_map (measurable_pi_apply i)
              (measurable_snd.comp (measurable_fst.comp (hmX n))),
              ← Measure.map_map measurable_snd (measurable_fst.comp (hmX n)),
              ← Measure.map_map measurable_fst (hmX n), (hlaw n).2]
            unfold MarketInterference.FiniteSample.experimentLaw
            rw [measurePreserving_fst.map_eq, measurePreserving_snd.map_eq, hpm]
        have hS : ∀ j, ∀ᵐ ω ∂μ, Tendsto (fun n => ((X n ω).2 j : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop
            (nhds (pi j)) := by
          intro j
          refine hAS (pi j) (fun n ω => (X n ω).2 j) (hpi j) (fun n => ?_) (fun n => ?_)
          · exact (measurable_pi_apply j).comp (measurable_snd.comp (hmX n))
          · have h : (fun ω => (X n ω).2 j) = (fun z : Fin ns → ℕ => z j) ∘ Prod.snd ∘ X n := rfl
            rw [h, ← Measure.map_map (measurable_pi_apply j) (measurable_snd.comp (hmX n)),
              ← Measure.map_map measurable_snd (hmX n), (hlaw n).2]
            unfold MarketInterference.FiniteSample.experimentLaw
            rw [measurePreserving_snd.map_eq, hpm]
        have hAEm : ∀ n, AEStronglyMeasurable (fun ω => twoLP N ρ (n + 1 : ℕ) (X n ω)) μ := by
          intro n
          have : Measurable (fun z : Counts nd ns => twoLP N ρ (n + 1 : ℕ) z) := Measurable.of_discrete
          exact (this.comp (hmX n)).aestronglyMeasurable
        have hbd : ∀ n ω, ‖twoLP N ρ (n + 1 : ℕ) (X n ω)‖ ≤ 2 * B := by
          intro n ω
          rw [Real.norm_eq_abs, twoLP]
          refine (abs_sub _ _).trans ?_
          have h1 := hPhiB (controlMLE ρ ((n + 1 : ℕ) : ℝ) (X n ω) + effectMLE ρ ((n + 1 : ℕ) : ℝ) (X n ω))
            (supplyMLE ((n + 1 : ℕ) : ℝ) (X n ω))
          have h2 := hPhiB (controlMLE ρ ((n + 1 : ℕ) : ℝ) (X n ω)) (supplyMLE ((n + 1 : ℕ) : ℝ) (X n ω))
          linarith
        have hlimae : ∀ᵐ ω ∂μ, Tendsto (fun n => twoLP N ρ (n + 1 : ℕ) (X n ω)) atTop
            (nhds (Delta N lam beta pi)) := by
          filter_upwards [ae_all_iff.2 hC, ae_all_iff.2 hT, ae_all_iff.2 hS] with ω h1 h2 h3
          have h1ρ : 0 < 1 - ρ := by linarith
          unfold Delta Psi twoLP
          refine Tendsto.sub ?_ ?_
          · refine hcont _ _ _ _ ?_ ?_ ?_ hpi ?_ ?_
            · intro n i
              simp only [effectMLE, add_sub_cancel, treatmentMLE]
              positivity
            · intro n j
              simp only [supplyMLE]
              positivity
            · intro i
              simpa using htreat i
            · intro i
              have := (h2 i).div_const ρ
              rw [mul_div_cancel_left₀ _ hρ.ne'] at this
              simp only [effectMLE, add_sub_cancel, one_smul, Pi.add_apply, treatmentMLE]
              refine this.congr fun n => ?_
              simp only [treatmentMLE, Pi.sub_apply]
              rw [div_div, mul_comm ρ]
              ring
            · intro j
              exact h3 j
          · refine hcont _ _ _ _ ?_ ?_ ?_ hpi ?_ ?_
            · intro n i
              simp only [controlMLE]
              positivity
            · intro n j
              simp only [supplyMLE]
              positivity
            · intro i
              simpa using hlam i
            · intro i
              have := (h1 i).div_const (1 - ρ)
              rw [mul_div_cancel_left₀ _ h1ρ.ne'] at this
              simp only [controlMLE, zero_smul, add_zero]
              refine this.congr fun n => ?_
              rw [div_div, mul_comm (1 - ρ)]
            · intro j
              exact h3 j
        refine ⟨fun n => ?_, hlimae, ?_⟩
        · exact Integrable.of_bound (hAEm n) (2 * B) (Eventually.of_forall (hbd n))
        · have := tendsto_integral_of_dominated_convergence (fun _ => 2 * B) hAEm
            (integrable_const _) (fun n => Eventually.of_forall (hbd n)) hlimae
          simpa using this
