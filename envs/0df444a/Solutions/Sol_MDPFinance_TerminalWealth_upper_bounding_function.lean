-- Prove2me | solution 1 for MDPFinance.TerminalWealth.upper_bounding_function
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T03:10:33.803132+00:00
-- url     : https://prove2.me/submissions/da86a297-11cd-49a1-91cb-5f4fec212732

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market

open MeasureTheory ProbabilityTheory


namespace MDPFinance.TerminalWealth

section UBF
set_option linter.unusedSectionVars false
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

lemma ubf_dot_meas (R : Ω → Fin d → ℝ) (hR : Measurable R) (a : Fin d → ℝ) :
    Measurable (fun ω => ∑ k, a k * R ω k) := by
  apply Finset.measurable_sum
  intro k _
  exact (measurable_pi_apply k |>.comp hR).const_mul _

lemma ubf_dot_bound (R : Ω → Fin d → ℝ) (a : Fin d → ℝ) (ω : Ω) :
    |∑ k, a k * R ω k| ≤ ‖a‖ * ∑ k, |R ω k| := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have := norm_le_pi_norm a k
  simpa [Real.norm_eq_abs] using this

lemma ubf_dot_int (μ : Measure Ω) (R : Ω → Fin d → ℝ) (hR : Measurable R)
    (hint : Integrable (fun ω => ∑ k, |R ω k|) μ) (a : Fin d → ℝ) :
    Integrable (fun ω => ∑ k, a k * R ω k) μ := by
  refine Integrable.mono' (hint.const_mul ‖a‖) (ubf_dot_meas R hR a).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ω => by
    simpa [Real.norm_eq_abs] using ubf_dot_bound R a ω

lemma ubf_dot_sub (R : Ω → Fin d → ℝ) (a b : Fin d → ℝ) (ω : Ω) :
    ∑ k, a k * R ω k - ∑ k, b k * R ω k = ∑ k, (a - b) k * R ω k := by
  rw [← Finset.sum_sub_distrib]; simp [sub_mul]

lemma ubf_key (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → Fin d → ℝ) (hR : Measurable R)
    (hint : Integrable (fun ω => ∑ k, |R ω k|) μ) (hNA : NoArbitrageOnePeriod μ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : Fin d → ℝ,
      ∫ ω, ∑ k, a k * R ω k ∂μ ≤ C * ∫ ω, max (-(∑ k, a k * R ω k)) 0 ∂μ := by
  classical
  set K : ℝ := ∫ ω, ∑ k, |R ω k| ∂μ with hK
  have hK0 : 0 ≤ K := integral_nonneg fun ω => Finset.sum_nonneg fun k _ => abs_nonneg _
  let φ : (Fin d → ℝ) → ℝ := fun a => ∫ ω, max (-(∑ k, a k * R ω k)) 0 ∂μ
  let ψ : (Fin d → ℝ) → ℝ := fun a => ∫ ω, ∑ k, a k * R ω k ∂μ
  have hφint : ∀ a : Fin d → ℝ, Integrable (fun ω => max (-(∑ k, a k * R ω k)) 0) μ := fun a =>
    (ubf_dot_int μ R hR hint a).neg_part
  have hψle : ∀ a, ψ a ≤ ‖a‖ * K := by
    intro a
    rw [hK, ← integral_const_mul]
    refine integral_mono (ubf_dot_int μ R hR hint a) (hint.const_mul _) fun ω => ?_
    exact (le_abs_self _).trans (ubf_dot_bound R a ω)
  have hφlip : ∀ a b, dist (φ a) (φ b) ≤ K * dist a b := by
    intro a b
    rw [Real.dist_eq, ← integral_sub (hφint a) (hφint b)]
    refine (abs_integral_le_integral_abs).trans ?_
    rw [hK, ← integral_mul_const]
    refine integral_mono ((hφint a).sub (hφint b)).abs (hint.mul_const _) fun ω => ?_
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [show -(∑ k, a k * R ω k) - -(∑ k, b k * R ω k) = -(∑ k, (a - b) k * R ω k) by
      rw [← ubf_dot_sub]; ring, abs_neg]
    refine (ubf_dot_bound R (a - b) ω).trans (le_of_eq ?_)
    rw [dist_eq_norm]; ring
  have hφcont : Continuous φ := by
    have : LipschitzWith K.toNNReal φ := LipschitzWith.of_dist_le_mul fun a b => by
      rw [Real.coe_toNNReal _ hK0]; exact hφlip a b
    exact this.continuous
  have hφnn : ∀ a, 0 ≤ φ a := fun a => integral_nonneg fun ω => le_max_right _ _
  have hφsmul : ∀ (c : ℝ), 0 ≤ c → ∀ a, φ (c • a) = c * φ a := by
    intro c hc a
    simp only [φ, ← integral_const_mul]
    congr 1; ext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show ∑ k, c * a k * R ω k = c * ∑ k, a k * R ω k by
      rw [Finset.mul_sum]; congr 1; ext k; ring]
    rw [show -(c * ∑ k, a k * R ω k) = c * -(∑ k, a k * R ω k) by ring]
    have := mul_max_of_nonneg (-(∑ k, a k * R ω k)) 0 hc
    rw [mul_zero] at this; exact this.symm
  -- the null submodule
  let L : Submodule ℝ (Fin d → ℝ) :=
    { carrier := {a | ∀ᵐ ω ∂μ, ∑ k, a k * R ω k = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        filter_upwards [ha, hb] with ω h1 h2
        simp [add_mul, Finset.sum_add_distrib, h1, h2]
      zero_mem' := by simp
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at *
        filter_upwards [ha] with ω h1
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [show ∑ k, c * a k * R ω k = c * ∑ k, a k * R ω k by
          rw [Finset.mul_sum]; congr 1; ext k; ring, h1, mul_zero] }
  have hφzero : ∀ a, φ a = 0 → a ∈ L := by
    intro a ha
    have h1 : (fun ω => max (-(∑ k, a k * R ω k)) 0) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω => le_max_right _ _) (hφint a)).1 ha
    have h2 : ∀ᵐ ω ∂μ, 0 ≤ ∑ k, a k * R ω k := by
      filter_upwards [h1] with ω h
      have : max (-(∑ k, a k * R ω k)) 0 = 0 := h
      have := le_max_left (-(∑ k, a k * R ω k)) 0
      linarith
    have h3 : μ {ω | 0 < ∑ k, a k * R ω k} = 0 := by
      by_contra hne
      exact hNA ⟨a, h2, pos_iff_ne_zero.2 hne⟩
    have h4 : ∀ᵐ ω ∂μ, ¬ (0 < ∑ k, a k * R ω k) := by
      rw [ae_iff]; simpa using h3
    show ∀ᵐ ω ∂μ, ∑ k, a k * R ω k = 0
    filter_upwards [h2, h4] with ω h h'
    exact le_antisymm (not_lt.1 h') h
  have hLφ : ∀ a l, l ∈ L → φ (a + l) = φ a := by
    intro a l hl
    apply integral_congr_ae
    have hl' : ∀ᵐ ω ∂μ, ∑ k, l k * R ω k = 0 := hl
    filter_upwards [hl'] with ω h
    simp [add_mul, Finset.sum_add_distrib, h]
  have hLψ : ∀ a l, l ∈ L → ψ (a + l) = ψ a := by
    intro a l hl
    apply integral_congr_ae
    have hl' : ∀ᵐ ω ∂μ, ∑ k, l k * R ω k = 0 := hl
    filter_upwards [hl'] with ω h
    simp [add_mul, Finset.sum_add_distrib, h]
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl L
  have hWc : IsClosed (W : Set (Fin d → ℝ)) := Submodule.closed_of_finiteDimensional W
  let S : Set (Fin d → ℝ) := (W : Set (Fin d → ℝ)) ∩ Metric.sphere 0 1
  have hScomp : IsCompact S := (isCompact_sphere 0 1).inter_left hWc
  -- reduce to W
  have hdecomp : ∀ a, ∃ w ∈ W, ∃ l ∈ L, a = w + l := by
    intro a
    have : a ∈ L ⊔ W := by rw [hW.sup_eq_top]; trivial
    obtain ⟨l, hl, w, hw, h⟩ := Submodule.mem_sup.1 this
    exact ⟨w, hw, l, hl, by rw [← h, add_comm]⟩
  by_cases hS : S.Nonempty
  · obtain ⟨u0, hu0S, hmin⟩ := hScomp.exists_isMinOn hS hφcont.continuousOn
    set m := φ u0
    have hm : 0 < m := by
      rcases (hφnn u0).lt_or_eq with h | h
      · exact h
      · exfalso
        have h1 : u0 ∈ L := hφzero u0 h.symm
        have h2 : u0 ∈ W := hu0S.1
        have : u0 = 0 := by
          have := hW.inf_eq_bot
          have hmem : u0 ∈ L ⊓ W := ⟨h1, h2⟩
          rw [this] at hmem; simpa using hmem
        have h3 := hu0S.2
        rw [this] at h3; simp at h3
    refine ⟨K / m, div_nonneg hK0 hm.le, fun a => ?_⟩
    obtain ⟨w, hw, l, hl, rfl⟩ := hdecomp a
    show ψ (w + l) ≤ K / m * φ (w + l)
    rw [hLψ w l hl, hLφ w l hl]
    by_cases hw0 : w = 0
    · subst hw0; simp only [ψ]; simp; exact mul_nonneg (div_nonneg hK0 hm.le) (hφnn 0)
    have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw0
    have huS : ‖w‖⁻¹ • w ∈ S := by
      refine ⟨W.smul_mem _ hw, ?_⟩
      simp [norm_smul, hnw.ne']
    have h1 : m ≤ φ (‖w‖⁻¹ • w) := hmin huS
    have h2 : φ w = ‖w‖ * φ (‖w‖⁻¹ • w) := by
      rw [← hφsmul _ hnw.le, smul_smul, mul_inv_cancel₀ hnw.ne', one_smul]
    have h3 : ‖w‖ * m ≤ φ w := by rw [h2]; exact mul_le_mul_of_nonneg_left h1 hnw.le
    calc ψ w ≤ ‖w‖ * K := hψle w
      _ = K / m * (‖w‖ * m) := by field_simp
      _ ≤ K / m * φ w := mul_le_mul_of_nonneg_left h3 (div_nonneg hK0 hm.le)
  · refine ⟨0, le_rfl, fun a => ?_⟩
    obtain ⟨w, hw, l, hl, rfl⟩ := hdecomp a
    show ψ (w + l) ≤ 0 * φ (w + l)
    rw [hLψ w l hl, zero_mul]
    by_cases hw0 : w = 0
    · subst hw0; simp [ψ]
    exfalso
    have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw0
    exact hS ⟨‖w‖⁻¹ • w, W.smul_mem _ hw, by simp [norm_smul, hnw.ne']⟩

lemma ubf_U_bound (M : TerminalWealthMarket Ω d)
    (hdomU : M.domU = Set.Ici (0 : ℝ) ∨ M.domU = Set.Ioi (0 : ℝ)) :
    ∃ cg : ℝ, 0 ≤ cg ∧ ∀ x ∈ M.domU, max (M.U x) 0 ≤ cg * (1 + x) := by
  have h1 : (1 : ℝ) ∈ M.domU := by rcases hdomU with h | h <;> rw [h] <;> norm_num
  have h2 : (1/2 : ℝ) ∈ M.domU := by rcases hdomU with h | h <;> rw [h] <;> norm_num
  have hpos : ∀ x ∈ M.domU, 0 ≤ x := by
    intro x hx; rcases hdomU with h | h <;> rw [h] at hx
    · exact hx
    · exact le_of_lt hx
  set s : ℝ := 2 * (M.U 1 - M.U (1/2)) with hs
  have hs0 : 0 ≤ s := by
    have := M.hU_mono h2 h1 (by norm_num); rw [hs]; linarith
  refine ⟨|M.U 1| + s, by positivity, fun x hx => ?_⟩
  have hx0 := hpos x hx
  have hUx : M.U x ≤ |M.U 1| + s * x := by
    rcases le_or_gt x 1 with hle | hlt
    · have := M.hU_mono.monotoneOn hx h1 hle
      have := le_abs_self (M.U 1)
      nlinarith
    · have hsl := M.hU_concave.concaveOn.slope_anti_adjacent h2 hx (by norm_num : (1/2:ℝ) < 1) hlt
      have e : (M.U (1:ℝ) - M.U (1/2)) / (1 - 1/2) = s := by rw [hs]; ring
      rw [e, div_le_iff₀ (by linarith)] at hsl
      have := le_abs_self (M.U 1)
      nlinarith
  have hab : 0 ≤ |M.U 1| := abs_nonneg _
  apply max_le
  · nlinarith
  · positivity

lemma ubf_core (M : TerminalWealthMarket Ω d)
    (hdomU : M.domU = Set.Ici (0 : ℝ) ∨ M.domU = Set.Ioi (0 : ℝ)) (hFM2 : M.FM2) :
    ∃ cr cg αb : ℝ, 0 ≤ cr ∧ 0 ≤ cg ∧ 0 ≤ αb ∧
      (∀ n < M.N, ∀ x ∈ M.domU, max (0 : ℝ) 0 ≤ cr * (1 + x)) ∧
      (∀ x ∈ M.domU, max (M.U x) 0 ≤ cg * (1 + x)) ∧
      (∀ n < M.N, ∀ x ∈ M.domU, ∀ a ∈ M.D n x,
        (∫ ω, (1 + (1 + M.i (n + 1)) * (x + ∑ k, a k * M.R (n + 1) ω k)) ∂M.measIP) ≤
          αb * (1 + x)) := by
  classical
  haveI := M.isProb
  have hpos : ∀ x ∈ M.domU, 0 ≤ x := by
    intro x hx; rcases hdomU with h | h <;> rw [h] at hx
    · exact hx
    · exact le_of_lt hx
  obtain ⟨cg, hcg0, hcg⟩ := ubf_U_bound M hdomU
  have hC : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (n < M.N → ∀ a : Fin d → ℝ,
      ∫ ω, ∑ k, a k * M.R (n + 1) ω k ∂M.measIP ≤
        C * ∫ ω, max (-(∑ k, a k * M.R (n + 1) ω k)) 0 ∂M.measIP) := by
    intro n
    by_cases hn : n < M.N
    · obtain ⟨C, hC0, hC⟩ := ubf_key M.measIP (M.R (n + 1)) (M.hR_meas (n+1) (by omega) (by omega))
        (hFM2 (n+1) (by omega) (by omega)) (M.hNA (n+1) (by omega) (by omega))
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hn⟩
  choose C hC0 hC using hC
  set αb : ℝ := 1 + ∑ n ∈ Finset.range M.N, (1 + M.i (n + 1)) * (1 + C n) with hαb
  have hterm : ∀ n < M.N, 0 < 1 + M.i (n + 1) := fun n hn => M.hi_pos (n+1) (by omega) (by omega)
  have hsum_nn : ∀ n ∈ Finset.range M.N, 0 ≤ (1 + M.i (n + 1)) * (1 + C n) := by
    intro n hn
    rw [Finset.mem_range] at hn
    exact mul_nonneg (hterm n hn).le (by linarith [hC0 n])
  have hαb1 : 1 ≤ αb := by
    rw [hαb]; linarith [Finset.sum_nonneg hsum_nn]
  refine ⟨0, cg, αb, le_rfl, hcg0, by linarith, fun n _ x _ => by simp, hcg, ?_⟩
  intro n hn x hx a ha
  have hx0 := hpos x hx
  have hc := hterm n hn
  have hRm := M.hR_meas (n+1) (by omega) (by omega)
  have hRi := hFM2 (n+1) (by omega) (by omega)
  have hdi := ubf_dot_int M.measIP (M.R (n+1)) hRm hRi a
  -- a.s. nonneg wealth
  have hae : ∀ᵐ ω ∂M.measIP, max (-(∑ k, a k * M.R (n + 1) ω k)) 0 ≤ x := by
    have ha' : ∀ᵐ ω ∂M.measIP,
        (1 + M.i (n + 1)) * (x + ∑ k, a k * M.R (n + 1) ω k) ∈ M.domU := ha
    filter_upwards [ha'] with ω h
    have h0 := hpos _ h
    have : 0 ≤ x + ∑ k, a k * M.R (n + 1) ω k := by
      by_contra hneg; push_neg at hneg
      have := mul_neg_of_pos_of_neg hc hneg; linarith
    exact max_le (by linarith) hx0
  have hφ : ∫ ω, max (-(∑ k, a k * M.R (n + 1) ω k)) 0 ∂M.measIP ≤ x := by
    have := integral_mono_ae hdi.neg_part (integrable_const x) hae
    simpa using this
  have hψ := (hC n hn a).trans (mul_le_mul_of_nonneg_left hφ (hC0 n))
  have hint_eq : (∫ ω, (1 + (1 + M.i (n + 1)) * (x + ∑ k, a k * M.R (n + 1) ω k)) ∂M.measIP)
      = 1 + (1 + M.i (n + 1)) * (x + ∫ ω, ∑ k, a k * M.R (n + 1) ω k ∂M.measIP) := by
    have hi2 : Integrable (fun ω => x + ∑ k, a k * M.R (n + 1) ω k) M.measIP :=
      (integrable_const x).add hdi
    rw [integral_add (integrable_const _) (hi2.const_mul _),
      integral_const_mul, integral_add (integrable_const _) hdi]
    simp
  rw [hint_eq]
  have hle : (1 + M.i (n + 1)) * (1 + C n) ≤ αb := by
    rw [hαb]
    have := Finset.single_le_sum hsum_nn (Finset.mem_range.2 hn)
    linarith
  have h3 : (1 + M.i (n + 1)) * (x + ∫ ω, ∑ k, a k * M.R (n + 1) ω k ∂M.measIP)
      ≤ (1 + M.i (n + 1)) * (1 + C n) * x := by
    have := mul_le_mul_of_nonneg_left (show x + ∫ ω, ∑ k, a k * M.R (n + 1) ω k ∂M.measIP ≤
      (1 + C n) * x by linarith) hc.le
    linarith
  nlinarith

end UBF

end MDPFinance.TerminalWealth

open MDPFinance.TerminalWealth


theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d)
    (hdomU : M.domU = Set.Ici (0 : ℝ) ∨ M.domU = Set.Ioi (0 : ℝ)) (hFM2 : M.FM2) :
    ∃ cr cg αb : ℝ, 0 ≤ cr ∧ 0 ≤ cg ∧ 0 ≤ αb ∧
      (∀ n < M.N, ∀ x ∈ M.domU, max (0 : ℝ) 0 ≤ cr * (1 + x)) ∧
      (∀ x ∈ M.domU, max (M.U x) 0 ≤ cg * (1 + x)) ∧
      (∀ n < M.N, ∀ x ∈ M.domU, ∀ a ∈ M.D n x,
        (∫ ω, (1 + (1 + M.i (n + 1)) * (x + ∑ k, a k * M.R (n + 1) ω k)) ∂M.measIP) ≤
          αb * (1 + x)) := by
  exact ubf_core M hdomU hFM2
