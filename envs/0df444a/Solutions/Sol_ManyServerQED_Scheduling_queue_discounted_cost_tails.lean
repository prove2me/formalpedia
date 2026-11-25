-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_discounted_cost_tails
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T20:55:59.225177+00:00
-- url     : https://prove2.me/submissions/533844ad-061e-4fd1-a99c-c7b51e19fdae

import Theorems.Thm_ManyServerQED_Scheduling_lemma_3
import Mathlib

open MeasureTheory Set Filter Topology
open scoped ENNReal

private theorem discounted_poly_integrable (C p γ : ℝ) (hp : 0 ≤ p) (hγ : 0 < γ) :
    IntegrableOn (fun t : ℝ => C * (Real.exp (-γ * t) * (1 + t ^ p))) (Ioi 0) := by
  have hExp : IntegrableOn (fun t : ℝ => Real.exp (-γ * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hγ) 0
  have hProd : IntegrableOn (fun t : ℝ => Real.exp (-γ * t) * t ^ p) (Ioi 0) := by
    simpa only [Real.rpow_one, mul_comm] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := p) (b := γ) (by linarith)
        (by norm_num) hγ)
  change Integrable _ (volume.restrict (Ioi 0 : Set ℝ))
  simpa only [Pi.add_apply, mul_add, mul_one] using (hExp.add hProd).const_mul C

private theorem polynomial_discounted_cost_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : ℕ → Ω → ℝ → ℝ≥0∞) (hc : ∀ n, Measurable (Function.uncurry (c n)))
    (C p γ : ℝ) (hC : 0 ≤ C) (hp : 0 ≤ p) (hγ : 0 < γ)
    (N : ℕ) (hBound : ∀ n ≥ N, ∀ t > 0, (∫⁻ ω, c n ω t ∂P) ≤ ENNReal.ofReal (C * (1 + t ^ p))) :
    (∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ n ≥ N, (∫⁻ ω, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-γ * t)) * c n ω t
      ∂volume ∂P) ≤ K) ∧
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ T : ℕ, ∀ n ≥ N,
      (∫⁻ ω, ∫⁻ t in Ioi (T : ℝ), ENNReal.ofReal (Real.exp (-γ * t)) * c n ω t ∂volume ∂P) < ε) := by
  let H (t : ℝ) := ENNReal.ofReal (C * (Real.exp (-γ * t) * (1 + t ^ p)))
  let μ : Measure ℝ := (volume.restrict (Ioi (0 : ℝ))).withDensity H
  have hMass : μ univ < ⊤ := by
    rw [show μ univ = ∫⁻ t in Ioi (0 : ℝ), H t ∂volume by
      simp only [μ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]]
    let f (t : ℝ) := C * (Real.exp (-γ * t) * (1 + t ^ p))
    have hi : Integrable f (volume.restrict (Ioi 0)) := discounted_poly_integrable C p γ hp hγ
    change (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (f t) ∂volume) < ⊤
    exact (lintegral_ofReal_le_lintegral_enorm f).trans_lt hi.hasFiniteIntegral
  have htail (T : ℕ) : μ (Ioi (T : ℝ)) = ∫⁻ t in Ioi (T : ℝ), H t ∂volume := by
    change ((volume.restrict (Ioi (0 : ℝ))).withDensity H) _ = _
    rw [withDensity_apply H measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
    have hsub : Ioi (T : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (Nat.cast_nonneg T)
    simp only [inter_eq_left.2 hsub]
  have hbound (n : ℕ) (hn : N ≤ n) (T : ℕ) :
      (∫⁻ ω, ∫⁻ t in Ioi (T : ℝ), ENNReal.ofReal (Real.exp (-γ * t)) * c n ω t ∂volume ∂P) ≤
        μ (Ioi (T : ℝ)) := by
    let u (ω : Ω) (t : ℝ) := ENNReal.ofReal (Real.exp (-γ * t)) * c n ω t
    have hW : Measurable (Function.uncurry u) := by
      exact ((measurable_snd.const_mul (-γ)).exp.ennreal_ofReal).mul (hc n)
    change (∫⁻ ω, ∫⁻ t in Ioi (T : ℝ), u ω t ∂volume ∂P) ≤ μ (Ioi (T : ℝ))
    rw [lintegral_lintegral_swap hW.aemeasurable, htail]
    apply setLIntegral_mono_ae' measurableSet_Ioi
    refine ae_of_all _ (fun t ht => ?_)
    have ht0 : 0 < t := (Nat.cast_nonneg T).trans_lt ht
    have hr : 0 ≤ C * (1 + t ^ p) := mul_nonneg hC (add_nonneg zero_le_one (Real.rpow_nonneg ht0.le _))
    dsimp [u, H]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_right (hBound n hn t ht0) _).trans_eq ?_
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    ring
  have hμt : Tendsto (fun T : ℕ => μ (Ioi (T : ℝ))) atTop (𝓝 0) := by
    have hm : Antitone (fun T : ℕ => Ioi (T : ℝ)) := fun a b h => Ioi_subset_Ioi (by exact_mod_cast h)
    have he : (⋂ T : ℕ, Ioi (T : ℝ)) = (∅ : Set ℝ) := by
      apply eq_empty_iff_forall_notMem.2
      intro t ht
      obtain ⟨n, hn⟩ := exists_nat_gt t
      exact (not_lt_of_ge hn.le) (mem_iInter.1 ht n)
    have h := tendsto_measure_iInter_atTop (μ := μ) (fun _ => measurableSet_Ioi.nullMeasurableSet)
      hm ⟨0, ne_top_of_le_ne_top hMass.ne (measure_mono (subset_univ _))⟩
    rwa [he, measure_empty] at h
  refine ⟨⟨μ univ, hMass, fun n hn => ?_⟩, fun ε hε => ?_⟩
  · have hb := (hbound n hn 0).trans (measure_mono (subset_univ _))
    simpa only [Nat.cast_zero] using hb
  · obtain ⟨T, hT⟩ := ((tendsto_order.1 hμt).2 ε hε).exists
    exact ⟨T, fun n hn => (hbound n hn T).trans_lt hT⟩

open scoped NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem sum_Xhat {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (n : ℕ) (X : Ω → ℝ → Fin k → ℝ) (ω : Ω) (t : ℝ) :
    ∑ j, M.Xhat n X ω t j = (∑ j, X ω t j - n) / Real.sqrt n := by
  unfold SystemSequence.Xhat
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have : ∑ i, M.rho i = 1 := M.sum_rho
  rw [this, one_mul]

private theorem integrand_eq {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (n : ℕ) (hn : 1 ≤ n) (u0 : Fin k → ℝ) (X Ψ : Ω → ℝ → Fin k → ℝ) (ω : Ω) (t : ℝ)
    (hnn : ∀ i, 0 ≤ X ω t i - Ψ ω t i)
    (hwc : max (∑ i, X ω t i - n) 0 = ∑ i, (X ω t i - Ψ ω t i)) :
    Lt (Phihat n X Ψ ω t) (M.Psihat n Ψ ω t) =
      costOfTilde Lt (M.Xhat n X ω t) (uProc n u0 X Ψ ω t) := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hPhi : Phihat n X Ψ ω t = max (∑ j, M.Xhat n X ω t j) 0 • uProc n u0 X Ψ ω t := by
    rw [sum_Xhat]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Phihat, uProc]
    split_ifs with hpos
    · rw [max_eq_left (div_nonneg hpos.le hsn.le)]
      field_simp
    · push Not at hpos
      rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg hpos hsn.le), zero_mul]
      have h0 : ∑ i, (X ω t i - Ψ ω t i) = 0 := by rw [← hwc, max_eq_right hpos]
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)] at h0
      rw [h0 i (Finset.mem_univ _), zero_div]
  unfold costOfTilde
  rw [← hPhi]
  congr 1
  funext i
  simp only [SystemSequence.Psihat, Pi.sub_apply, SystemSequence.Xhat, Phihat]
  ring


set_option maxHeartbeats 1300000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU) (hγ : 0 < γ)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hPol : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
      IsWorkConserving n (X n) (Ψ n))
    (hX : ∀ n, 1 ≤ n → Measurable (fun z : Ω × ℝ≥0 => X n z.1 z.2))
    (hΨ : ∀ n, 1 ≤ n → Measurable (fun z : Ω × ℝ≥0 => Ψ n z.1 z.2)) :
    ∃ N : ℕ, ∀ ε : ℝ≥0∞, 0 < ε → ∃ T : ℕ, ∀ n ≥ N,
      (∫⁻ ω, ∫⁻ t in Ioi (T:ℝ),
        ENNReal.ofReal (Real.exp (-γ*t) * costOfTilde Lt (M.Xhat n (X n) ω t)
          (uProc n u0 (X n) (Ψ n) ω t)) ∂volume ∂M.P) < ε := by
  letI : IsProbabilityMeasure M.P := M.isProb
  have hC (n : ℕ) (hn : 1 ≤ n) : M.IsControlled n (X0 n) (X n) (Ψ n) :=
    (hPol n hn).1.controlled
  let g (n : ℕ) (ω : Ω) (t : ℝ) := if 1 ≤ n then ENNReal.ofReal
    (Lt (Phihat n (X n) (Ψ n) ω t.toNNReal) (M.Psihat n (Ψ n) ω t.toNNReal)) else 0
  have hg (n : ℕ) : Measurable (Function.uncurry (g n)) := by
    by_cases hn : 1 ≤ n
    · simp only [g, if_pos hn]
      let p (z : Ω × ℝ) := (z.1,z.2.toNNReal)
      have hp : Measurable p := measurable_fst.prodMk measurable_snd.real_toNNReal
      have hx := (hX n hn).comp hp
      have hψ := (hΨ n hn).comp hp
      have hΦ : Measurable (fun z : Ω × ℝ => Phihat n (X n) (Ψ n) z.1 z.2.toNNReal) := by
        apply measurable_pi_lambda
        intro i
        exact (((measurable_pi_apply i).comp hx).sub ((measurable_pi_apply i).comp hψ)).div_const _
      have hPm : Measurable (fun z : Ω × ℝ => M.Psihat n (Ψ n) z.1 z.2.toNNReal) := by
        apply measurable_pi_lambda
        intro i
        exact (((measurable_pi_apply i).comp hψ).sub_const (M.rho i * n)).div_const _
      exact (hA2.tilde_cont.measurable.comp (hΦ.prodMk hPm)).ennreal_ofReal
    · simp only [g, if_neg hn]
      exact measurable_const
  have hGt (n : ℕ) (hn : 1 ≤ n) (ω : Ω) (t : ℝ) (ht : 0 ≤ t) :
      g n ω t = ENNReal.ofReal (costOfTilde Lt (M.Xhat n (X n) ω t) (uProc n u0 (X n) (Ψ n) ω t)) := by
    dsimp only [g]
    rw [Real.coe_toNNReal _ ht, integrand_eq M Lt n hn u0 (X n) (Ψ n) ω t
      (fun i => (hC n hn).phi_nonneg ω t i ht) ((hPol n hn).2.2 ω t ht), if_pos hn]
  have hUm (n : ℕ) (hn : 1 ≤ n) (ω : Ω) (t : ℝ) (ht : 0 ≤ t) :
      uProc n u0 (X n) (Ψ n) ω t ∈ stdSimplex ℝ (Fin k) := by
    unfold uProc
    split_ifs with h
    · refine ⟨fun i => div_nonneg ((hC n hn).phi_nonneg ω t i ht) h.le, ?_⟩
      rw [← Finset.sum_div, ← (hPol n hn).2.2 ω t ht, max_eq_left h.le, div_self h.ne']
    · exact hu0
  obtain ⟨a, ha, hA⟩ := hA2.cost.growth
  obtain ⟨c, m, hMom⟩ := lemma_3 M mL mU hA3
  obtain ⟨N, hN⟩ := hMom x X0 hX0 X Ψ hPol
  let b := max c 0 * (1 + l1norm x ^ m)
  have hx0 : 0 ≤ l1norm x := Finset.sum_nonneg (fun i _ => abs_nonneg (x i))
  have hb : 0 ≤ b := mul_nonneg (le_max_right c 0) (by positivity)
  have hU : 0 ≤ mU := hA3.1.trans' (by norm_num)
  have hV (n : ℕ) (ω : Ω) (t : ℝ) : 0 ≤ l1norm (M.Xhat n (X n) ω t) :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hExp (n : ℕ) (hn : max N 1 ≤ n) (t : ℝ) (ht : 0 < t) :
      (∫⁻ ω, g n ω t ∂M.P) ≤ ENNReal.ofReal ((a * (2 + b)) * (1 + t ^ (m : ℝ))) := by
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have hNn : N ≤ n := (le_max_left _ _).trans hn
    let v (ω : Ω) := ENNReal.ofReal (l1norm (M.Xhat n (X n) ω t)) ^ mU
    have hpoint (ω : Ω) : g n ω t ≤ ENNReal.ofReal a * (2 + v ω) := by
      rw [hGt n hn1 ω t ht.le]
      let z := l1norm (M.Xhat n (X n) ω t)
      have hz : 0 ≤ z := hV n ω t
      have hpow : z ^ mL ≤ 1 + z ^ mU := by
        rcases le_total z 1 with h | h
        · exact (Real.rpow_le_one hz h hA2.cost.mL_nonneg).trans (le_add_of_nonneg_right (Real.rpow_nonneg hz _))
        · exact (Real.rpow_le_rpow_of_exponent_le h hA3.2.1.le).trans (le_add_of_nonneg_left zero_le_one)
      calc
        _ ≤ ENNReal.ofReal (a * (1 + z ^ mL)) := ENNReal.ofReal_le_ofReal (hA _ (hUm n hn1 ω t ht.le) _)
        _ ≤ ENNReal.ofReal (a * (2 + z ^ mU)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith) ha.le)
        _ = _ := by
          rw [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_add (by norm_num : 0 ≤ (2 : ℝ)) (Real.rpow_nonneg hz _),
            ← ENNReal.ofReal_rpow_of_nonneg hz hU]
          simp only [v, z, ENNReal.ofReal_ofNat]
    have htM : (∫⁻ ω, v ω ∂M.P) ≤ ENNReal.ofReal (b * (1 + t ^ m)) := by
      refine (hN n hNn t ht.le).trans (ENNReal.ofReal_le_ofReal ?_)
      unfold b
      gcongr
      exact le_max_left _ _
    have hw : ENNReal.ofReal a * (2 + ENNReal.ofReal (b * (1 + t ^ m))) =
        ENNReal.ofReal (a * (2 + b * (1 + t ^ m))) := by
      rw [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_add (by norm_num : 0 ≤ (2 : ℝ))
        (mul_nonneg hb (by positivity)), ENNReal.ofReal_ofNat]
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal a * (2 + v ω) ∂M.P := lintegral_mono hpoint
      _ = ENNReal.ofReal a * (2 + ∫⁻ ω, v ω ∂M.P) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
          lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal a * (2 + ENNReal.ofReal (b * (1 + t ^ m))) := by gcongr
      _ = ENNReal.ofReal (a * (2 + b * (1 + t ^ m))) := hw
      _ ≤ _ := by
        rw [Real.rpow_natCast]
        apply ENNReal.ofReal_le_ofReal
        have hh : 0 ≤ t ^ m := pow_nonneg ht.le _
        nlinarith [mul_nonneg ha.le hh]
  obtain ⟨_, hB⟩ := polynomial_discounted_cost_bound M.P g hg (a * (2 + b)) (m : ℝ)
    γ (by positivity) (Nat.cast_nonneg _) hγ (max N 1) hExp
  refine ⟨max N 1, fun ε hε => ?_⟩
  obtain ⟨T, hT⟩ := hB ε hε
  refine ⟨T, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  refine lt_of_eq_of_lt ?_ (hT n hn)
  congr 1
  funext ω
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : 0 ≤ t := (Nat.cast_nonneg T).trans ht.le
  simp only [hGt n hn1 ω t ht0, ENNReal.ofReal_mul (Real.exp_nonneg _)]
