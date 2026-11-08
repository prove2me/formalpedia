-- Prove2me | solution 1 for InfoBargaining.SellerPayoff.proposition_2_seller_payoff_reversals
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T03:00:25.468971+00:00
-- url     : https://prove2.me/submissions/9cb45f8c-e480-438e-9a91-afb0195d720a

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior_measure
import Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior_costDomain
import Definitions.Def_InfoBargaining_SellerPayoff_sellerPayoffMaterial
import Definitions.Def_InfoBargaining_SellerPayoff_sellerPayoffOpportunity

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology

namespace InfoBargaining.SellerPayoff

/-- pointwise integrand of the total surplus, pulled back to the prior -/
noncomputable def p2rF (μ : Measure ℝ) (α c u : ℝ) : ℝ :=
  max (α * u + (1 - α) * priorMean μ - c) 0

section Generic

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem p2r_tS_eq (α c : ℝ) :
    totalSurplus μ α c = ∫ u, p2rF μ α c u ∂μ := by
  unfold totalSurplus postMeanLaw p2rF
  rw [integral_map (by fun_prop) (by fun_prop : Continuous fun v : ℝ => max (v - c) 0).aestronglyMeasurable]

theorem p2r_int (hI : Integrable (fun u : ℝ => u) μ) (α c : ℝ) :
    Integrable (fun u => p2rF μ α c u) μ := by
  have h : Integrable (fun u : ℝ => α * u + (1 - α) * priorMean μ - c) μ :=
    ((hI.const_mul α).add (integrable_const _)).sub (integrable_const c)
  unfold p2rF
  exact h.pos_part

theorem p2r_ile (hI : Integrable (fun u : ℝ => u) μ) (F G : ℝ → ℝ) (hF : Integrable F μ)
    (hG : Integrable G μ) (t : ℝ) (h : ∀ u, F u + t * (u - priorMean μ) ≤ G u) :
    ∫ u, F u ∂μ ≤ ∫ u, G u ∂μ := by
  have hL : Integrable (fun u : ℝ => t * (u - priorMean μ)) μ :=
    (hI.sub (integrable_const _)).const_mul t
  have h0 : ∫ u, t * (u - priorMean μ) ∂μ = 0 := by
    rw [integral_const_mul, integral_sub hI (integrable_const _)]
    simp [priorMean]
  calc ∫ u, F u ∂μ = ∫ u, (F u + t * (u - priorMean μ)) ∂μ := by
        rw [integral_add hF hL, h0, add_zero]
    _ ≤ ∫ u, G u ∂μ := integral_mono (hF.add hL) hG h

theorem p2r_posf (m α β w : ℝ) (hα : 0 ≤ α) (hab : α ≤ β) :
    (w ≤ m → β * w + (1 - β) * m ≤ α * w + (1 - α) * m ∧ α * w + (1 - α) * m ≤ m) ∧
    (m ≤ w → α * w + (1 - α) * m ≤ β * w + (1 - β) * m ∧ m ≤ α * w + (1 - α) * m) := by
  refine ⟨fun hw => ⟨?_, ?_⟩, fun hw => ⟨?_, ?_⟩⟩ <;> nlinarith

theorem p2r_nonneg (α c : ℝ) : 0 ≤ totalSurplus μ α c := by
  rw [p2r_tS_eq]; exact integral_nonneg fun u => le_max_right _ _

theorem p2r_mono (hI : Integrable (fun u : ℝ => u) μ) (c α β : ℝ) (hα : 0 ≤ α) (hab : α ≤ β) :
    totalSurplus μ α c ≤ totalSurplus μ β c := by
  rw [p2r_tS_eq, p2r_tS_eq]
  rcases le_total c (priorMean μ) with hc | hc
  · refine p2r_ile hI _ _ (p2r_int hI α c) (p2r_int hI β c) (β - α) (fun w => ?_)
    have hp := p2r_posf (priorMean μ) α β w hα hab
    have hd : (β * w + (1 - β) * priorMean μ) - (α * w + (1 - α) * priorMean μ)
        = (β - α) * (w - priorMean μ) := by ring
    unfold p2rF
    rcases le_total w (priorMean μ) with hw | hw
    · obtain ⟨h1, h2⟩ := hp.1 hw
      have : (β - α) * (w - priorMean μ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      simp only [max_def]; split_ifs <;> linarith
    · obtain ⟨h1, h2⟩ := hp.2 hw
      simp only [max_def]; split_ifs <;> linarith
  · refine p2r_ile hI _ _ (p2r_int hI α c) (p2r_int hI β c) 0 (fun w => ?_)
    have hp := p2r_posf (priorMean μ) α β w hα hab
    unfold p2rF
    rcases le_total w (priorMean μ) with hw | hw
    · obtain ⟨h1, h2⟩ := hp.1 hw
      simp only [max_def]; split_ifs <;> linarith
    · obtain ⟨h1, h2⟩ := hp.2 hw
      simp only [max_def]; split_ifs <;> linarith

theorem p2r_anti (hI : Integrable (fun u : ℝ => u) μ) (α c c' : ℝ) (h : c ≤ c') :
    totalSurplus μ α c' ≤ totalSurplus μ α c := by
  rw [p2r_tS_eq, p2r_tS_eq]
  exact integral_mono (p2r_int hI α c') (p2r_int hI α c)
    (fun u => by unfold p2rF; exact max_le_max (by linarith) le_rfl)

theorem p2r_lip (hI : Integrable (fun u : ℝ => u) μ) (α c c' : ℝ) (h : c ≤ c') :
    totalSurplus μ α c ≤ totalSurplus μ α c' + (c' - c) := by
  rw [p2r_tS_eq, p2r_tS_eq]
  have key : ∫ u, p2rF μ α c u ∂μ ≤ ∫ u, (p2rF μ α c' u + (c' - c)) ∂μ :=
    integral_mono (p2r_int hI α c) ((p2r_int hI α c').add (integrable_const _)) (fun u => by
      simp only [p2rF, max_def]; split_ifs <;> linarith)
  rw [integral_add (p2r_int hI α c') (integrable_const _), integral_const] at key
  simpa using key

theorem p2r_cont (hI : Integrable (fun u : ℝ => u) μ) (α : ℝ) :
    Continuous (fun c => totalSurplus μ α c) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun c c' => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq]
  simp only [NNReal.coe_one, one_mul]
  rcases le_total c c' with h | h
  · have h1 := p2r_lip hI α c c' h
    have h2 := p2r_anti hI α c c' h
    rw [abs_of_nonpos (by linarith : c - c' ≤ 0), abs_le]
    constructor <;> linarith
  · have h1 := p2r_lip hI α c' c h
    have h2 := p2r_anti hI α c' c h
    rw [abs_of_nonneg (by linarith : 0 ≤ c - c'), abs_le]
    constructor <;> linarith

theorem p2r_diff_low (hI : Integrable (fun u : ℝ => u) μ) (c c' α β : ℝ) (hcc : c ≤ c')
    (hc' : c' ≤ priorMean μ) (hα : 0 ≤ α) (hab : α ≤ β) :
    totalSurplus μ α c' - totalSurplus μ α c ≤ totalSurplus μ β c' - totalSurplus μ β c := by
  have key : ∫ w, (p2rF μ α c' w + p2rF μ β c w) ∂μ ≤
      ∫ w, (p2rF μ β c' w + p2rF μ α c w) ∂μ := by
    refine p2r_ile hI _ _ ((p2r_int hI α c').add (p2r_int hI β c))
      ((p2r_int hI β c').add (p2r_int hI α c)) 0 (fun w => ?_)
    have hp := p2r_posf (priorMean μ) α β w hα hab
    unfold p2rF
    rcases le_total w (priorMean μ) with hw | hw
    · obtain ⟨h1, h2⟩ := hp.1 hw
      simp only [max_def]; split_ifs <;> linarith
    · obtain ⟨h1, h2⟩ := hp.2 hw
      simp only [max_def]; split_ifs <;> linarith
  rw [integral_add (p2r_int hI α c') (p2r_int hI β c),
    integral_add (p2r_int hI β c') (p2r_int hI α c)] at key
  rw [p2r_tS_eq, p2r_tS_eq, p2r_tS_eq, p2r_tS_eq]
  linarith

theorem p2r_diff_high (hI : Integrable (fun u : ℝ => u) μ) (c c' α β : ℝ) (hcc : c ≤ c')
    (hc : priorMean μ ≤ c) (hα : 0 ≤ α) (hab : α ≤ β) :
    totalSurplus μ β c' - totalSurplus μ β c ≤ totalSurplus μ α c' - totalSurplus μ α c := by
  have key : ∫ w, (p2rF μ β c' w + p2rF μ α c w) ∂μ ≤
      ∫ w, (p2rF μ α c' w + p2rF μ β c w) ∂μ := by
    refine p2r_ile hI _ _ ((p2r_int hI β c').add (p2r_int hI α c))
      ((p2r_int hI α c').add (p2r_int hI β c)) 0 (fun w => ?_)
    have hp := p2r_posf (priorMean μ) α β w hα hab
    unfold p2rF
    rcases le_total w (priorMean μ) with hw | hw
    · obtain ⟨h1, h2⟩ := hp.1 hw
      simp only [max_def]; split_ifs <;> linarith
    · obtain ⟨h1, h2⟩ := hp.2 hw
      simp only [max_def]; split_ifs <;> linarith
  rw [integral_add (p2r_int hI β c') (p2r_int hI α c),
    integral_add (p2r_int hI α c') (p2r_int hI β c)] at key
  rw [p2r_tS_eq, p2r_tS_eq, p2r_tS_eq, p2r_tS_eq]
  linarith

/-- the gain is maximal at the prior mean -/
theorem p2r_gain_le_m (hI : Integrable (fun u : ℝ => u) μ) (c αl αh : ℝ) (hα : 0 ≤ αl)
    (hab : αl ≤ αh) :
    totalSurplus μ αh c - totalSurplus μ αl c ≤
      totalSurplus μ αh (priorMean μ) - totalSurplus μ αl (priorMean μ) := by
  rcases le_total c (priorMean μ) with hc | hc
  · have := p2r_diff_low hI c (priorMean μ) αl αh hc le_rfl hα hab; linarith
  · have := p2r_diff_high hI (priorMean μ) c αl αh hc le_rfl hα hab; linarith

theorem p2r_convex (hI : Integrable (fun u : ℝ => u) μ) (c αl αh α : ℝ) (hl : αl ≤ α)
    (hh : α ≤ αh) :
    (αh - αl) * totalSurplus μ α c ≤
      (αh - α) * totalSurplus μ αl c + (α - αl) * totalSurplus μ αh c := by
  have key := integral_mono ((p2r_int hI α c).const_mul (αh - αl))
    (((p2r_int hI αl c).const_mul (αh - α)).add ((p2r_int hI αh c).const_mul (α - αl)))
    (fun u => by
      simp only [p2rF, Pi.add_apply]
      have ha : 0 ≤ αh - α := by linarith
      have hb : 0 ≤ α - αl := by linarith
      have key : (αh - αl) * (α * u + (1 - α) * priorMean μ - c) =
          (αh - α) * (αl * u + (1 - αl) * priorMean μ - c) +
            (α - αl) * (αh * u + (1 - αh) * priorMean μ - c) := by ring
      have e1 := mul_le_mul_of_nonneg_left (le_max_left (αl * u + (1 - αl) * priorMean μ - c) 0) ha
      have e2 := mul_le_mul_of_nonneg_left (le_max_left (αh * u + (1 - αh) * priorMean μ - c) 0) hb
      have e3 := mul_nonneg ha (le_max_right (αl * u + (1 - αl) * priorMean μ - c) 0)
      have e4 := mul_nonneg hb (le_max_right (αh * u + (1 - αh) * priorMean μ - c) 0)
      rcases le_total (α * u + (1 - α) * priorMean μ - c) 0 with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith)
  rw [integral_add' ((p2r_int hI αl c).const_mul _) ((p2r_int hI αh c).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul] at key
  rw [p2r_tS_eq, p2r_tS_eq, p2r_tS_eq]
  exact key

/-- optimal information is an endpoint, chosen by the gain -/
theorem p2r_opt (hI : Integrable (fun u : ℝ => u) μ) (αl αh kbar θb c : ℝ) (hαl : 0 < αl)
    (hlh : αl < αh) (hθ : 0 ≤ θb) :
    optimalInfo μ αl αh kbar θb c =
      if kbar < θb * (totalSurplus μ αh c - totalSurplus μ αl c) then αh else αl := by
  have hD : 0 < αh - αl := by linarith
  have e0 : kbar * (αl - αl) / (αh - αl) = 0 := by simp
  have e1 : kbar * (αh - αl) / (αh - αl) = kbar := by field_simp
  have hob : ∀ α ∈ Set.Icc αl αh, (αh - αl) * buyerObjective μ αl αh kbar θb c α ≤
      (αh - α) * buyerObjective μ αl αh kbar θb c αl +
        (α - αl) * buyerObjective μ αl αh kbar θb c αh := by
    intro α hα
    have hc := p2r_convex hI c αl αh α hα.1 hα.2
    have e2 : (αh - αl) * (kbar * (α - αl) / (αh - αl)) = kbar * (α - αl) := by field_simp
    simp only [buyerObjective, infoCost, e0, e1, sub_zero]
    nlinarith [mul_le_mul_of_nonneg_left hc hθ]
  have vl : buyerObjective μ αl αh kbar θb c αl = θb * totalSurplus μ αl c := by
    simp only [buyerObjective, infoCost, e0, sub_zero]
  have vh : buyerObjective μ αl αh kbar θb c αh = θb * totalSurplus μ αh c - kbar := by
    simp only [buyerObjective, infoCost, e1]
  unfold optimalInfo
  by_cases hk : kbar < θb * (totalSurplus μ αh c - totalSurplus μ αl c)
  · rw [if_pos hk]
    have hgt : buyerObjective μ αl αh kbar θb c αl < buyerObjective μ αl αh kbar θb c αh := by
      rw [vl, vh]; linarith
    have hset : {α | α ∈ Set.Icc αl αh ∧ ∀ β ∈ Set.Icc αl αh,
        buyerObjective μ αl αh kbar θb c β ≤ buyerObjective μ αl αh kbar θb c α} = {αh} := by
      ext α
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hα, hmax⟩
        have h1 := hob α hα
        have h2 := hmax αh ⟨hlh.le, le_rfl⟩
        by_contra hne
        have hlt : α < αh := lt_of_le_of_ne hα.2 hne
        nlinarith [mul_lt_mul_of_pos_left hgt (by linarith : (0:ℝ) < αh - α)]
      · intro hα
        rw [hα]
        refine ⟨⟨hlh.le, le_rfl⟩, fun β hβ => ?_⟩
        have h1 := hob β hβ
        have h3 : (αh - αl) * buyerObjective μ αl αh kbar θb c β ≤
            (αh - αl) * buyerObjective μ αl αh kbar θb c αh := by
          nlinarith [mul_le_mul_of_nonneg_left hgt.le (by linarith [hβ.2] : (0:ℝ) ≤ αh - β)]
        exact le_of_mul_le_mul_left h3 hD
    rw [hset, csInf_singleton]
  · rw [if_neg hk]
    have hle : buyerObjective μ αl αh kbar θb c αh ≤ buyerObjective μ αl αh kbar θb c αl := by
      rw [vl, vh]; push_neg at hk; linarith
    apply IsLeast.csInf_eq
    refine ⟨⟨⟨le_rfl, hlh.le⟩, fun β hβ => ?_⟩, fun α hα => hα.1.1⟩
    have h1 := hob β hβ
    have h3 : (αh - αl) * buyerObjective μ αl αh kbar θb c β ≤
        (αh - αl) * buyerObjective μ αl αh kbar θb c αl := by
      nlinarith [mul_le_mul_of_nonneg_left hle (by linarith [hβ.1] : (0:ℝ) ≤ β - αl)]
    exact le_of_mul_le_mul_left h3 hD

theorem p2r_top (hI : Integrable (fun u : ℝ => u) μ) (α : ℝ) :
    Tendsto (fun c => totalSurplus μ α c) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun c u => p2rF μ α c u) (f := fun _ => (0:ℝ))
    (fun u => |α * u + (1 - α) * priorMean μ|)
    (Eventually.of_forall fun c => (p2r_int hI α c).aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with c hc
      refine Eventually.of_forall fun u => ?_
      simp only [p2rF, Real.norm_eq_abs]
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [le_abs_self (α * u + (1 - α) * priorMean μ)]) (abs_nonneg _))
    ((hI.const_mul α).add (integrable_const _)).abs
    (Eventually.of_forall fun u => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (α * u + (1 - α) * priorMean μ)] with c hc
      simp only [p2rF]
      rw [max_eq_right (by linarith)])
  simp only [integral_zero] at h
  exact h.congr' (Eventually.of_forall fun c => (p2r_tS_eq α c).symm)

theorem p2r_bot (hI : Integrable (fun u : ℝ => u) μ) :
    Tendsto (fun a => ∫ u, max (a - u) 0 ∂μ) atBot (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atBot)
    (F := fun a u => max (a - u) 0) (f := fun _ => (0:ℝ)) (fun u => |u|)
    (Eventually.of_forall fun a =>
      (by fun_prop : Continuous fun u : ℝ => max (a - u) 0).aestronglyMeasurable)
    (by
      filter_upwards [eventually_le_atBot (0:ℝ)] with a ha
      refine Eventually.of_forall fun u => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [neg_le_abs u]) (abs_nonneg _))
    hI.abs
    (Eventually.of_forall fun u => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_le_atBot u] with a ha
      rw [max_eq_right (by linarith)])
  simpa using h

theorem p2r_K_pos (hI : Integrable (fun u : ℝ => u) μ) (hac : μ ≪ volume) :
    0 < ∫ u, max (u - priorMean μ) 0 ∂μ := by
  set m := priorMean μ with hm
  have hint0 : Integrable (fun u : ℝ => u - m) μ := hI.sub (integrable_const m)
  have hint : Integrable (fun u => max (u - m) 0) μ := hint0.pos_part
  rcases (integral_nonneg (μ := μ) (f := fun u => max (u - m) 0)
      (fun u => le_max_right (u - m) 0)).lt_or_eq with h | h
  · exact h
  exfalso
  have h0 : (fun u => max (u - m) 0) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun u => le_max_right _ _) hint).1 h.symm
  have hle : ∀ᵐ u ∂μ, u ≤ m := h0.mono fun u hu => by
    simp only [Pi.zero_apply] at hu; linarith [le_max_left (u - m) 0]
  have hint2 : Integrable (fun u => m - u) μ := (integrable_const m).sub hI
  have hz : ∫ u, (m - u) ∂μ = 0 := by
    rw [integral_sub (integrable_const m) hI]; simp [hm, priorMean]
  have h1 : (fun u => m - u) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (hle.mono fun u hu => by
      simp only [Pi.zero_apply]; linarith) hint2).1 hz
  have hsing : μ {m} = 0 := hac (Real.volume_singleton)
  have hae : ∀ᵐ u ∂μ, u ∈ ({m} : Set ℝ) := h1.mono fun u hu => by
    simp only [Pi.zero_apply] at hu; simp only [Set.mem_singleton_iff]; linarith
  have hu : μ ({m} ∪ {a | ¬ a ∈ ({m} : Set ℝ)}) = 0 := measure_union_null hsing (ae_iff.1 hae)
  rw [show ({m} ∪ {a | ¬ a ∈ ({m} : Set ℝ)}) = Set.univ from Set.union_compl_self _,
    measure_univ] at hu
  exact one_ne_zero hu

end Generic

section Parts

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem p2r_part_i (hI : Integrable (fun u : ℝ => u) μ) (αl αh kbar c : ℝ) (h0 : 0 < αl)
    (h1 : αl < αh) (hk : 0 < kbar) :
    ∃ θt : ℝ, 0 < θt ∧ θt ≤ 1 ∧
      (∀ θs ∈ Set.Ioo (0:ℝ) 1, optimalInfo μ αl αh kbar (1 - θs) c = αh ↔ θt < 1 - θs) ∧
      (∀ θ₁ ∈ Set.Ioo (0:ℝ) 1, ∀ θ₂ ∈ Set.Ioo (0:ℝ) 1, θ₁ < θ₂ →
        (sellerPayoffMaterial μ αl αh kbar θ₂ c < sellerPayoffMaterial μ αl αh kbar θ₁ c →
          θ₁ < 1 - θt ∧ 1 - θt ≤ θ₂) ∧
        (sellerPayoffOpportunity μ αl αh kbar θ₂ c < sellerPayoffOpportunity μ αl αh kbar θ₁ c →
          θ₁ < 1 - θt ∧ 1 - θt ≤ θ₂)) ∧
      (∀ θ ∈ Set.Ioo (0:ℝ) 1, θ ≠ 1 - θt →
        ContinuousAt (fun θs => sellerPayoffMaterial μ αl αh kbar θs c) θ ∧
        ContinuousAt (fun θs => sellerPayoffOpportunity μ αl αh kbar θs c) θ) := by
  have hg : totalSurplus μ αl c ≤ totalSurplus μ αh c := p2r_mono hI c αl αh h0.le h1.le
  have hAl0 : 0 ≤ totalSurplus μ αl c := p2r_nonneg αl c
  have hAh0 : 0 ≤ totalSurplus μ αh c := p2r_nonneg αh c
  obtain ⟨θt, ht0, ht1, hiff⟩ : ∃ θt : ℝ, 0 < θt ∧ θt ≤ 1 ∧
      ∀ θs ∈ Set.Ioo (0:ℝ) 1,
        (kbar < (1 - θs) * (totalSurplus μ αh c - totalSurplus μ αl c) ↔ θt < 1 - θs) := by
    by_cases hkg : kbar < totalSurplus μ αh c - totalSurplus μ αl c
    · have hgp : 0 < totalSurplus μ αh c - totalSurplus μ αl c := lt_trans hk hkg
      refine ⟨kbar / (totalSurplus μ αh c - totalSurplus μ αl c), div_pos hk hgp,
        (div_le_one hgp).2 hkg.le, fun θs _ => ?_⟩
      rw [div_lt_iff₀ hgp]
    · refine ⟨1, one_pos, le_rfl, fun θs hθ => ?_⟩
      push_neg at hkg
      constructor
      · intro h
        nlinarith [mul_nonneg hθ.1.le (sub_nonneg.2 hg)]
      · intro h; linarith [hθ.1]
  have hoptS : ∀ θs ∈ Set.Ioo (0:ℝ) 1, θt < 1 - θs →
      optimalInfo μ αl αh kbar (1 - θs) c = αh := by
    intro θs hθ h
    rw [p2r_opt hI αl αh kbar (1 - θs) c h0 h1 (by linarith [hθ.2]), if_pos ((hiff θs hθ).2 h)]
  have hoptN : ∀ θs ∈ Set.Ioo (0:ℝ) 1, ¬ θt < 1 - θs →
      optimalInfo μ αl αh kbar (1 - θs) c = αl := by
    intro θs hθ h
    rw [p2r_opt hI αl αh kbar (1 - θs) c h0 h1 (by linarith [hθ.2]),
      if_neg (fun h' => h ((hiff θs hθ).1 h'))]
  refine ⟨θt, ht0, ht1, fun θs hθ => ?_, fun θ₁ h1' θ₂ h2' h12 => ⟨fun hlt => ?_, fun hlt => ?_⟩,
    fun θ hθ hne => ?_⟩
  · constructor
    · intro h; by_contra h'; rw [hoptN θs hθ h'] at h; exact h1.ne h
    · intro h; exact hoptS θs hθ h
  · unfold sellerPayoffMaterial at hlt
    by_cases a2 : θt < 1 - θ₂
    · have a1 : θt < 1 - θ₁ := by linarith
      rw [hoptS θ₂ h2' a2, hoptS θ₁ h1' a1] at hlt
      nlinarith [mul_le_mul_of_nonneg_right h12.le hAh0]
    · by_cases a1 : θt < 1 - θ₁
      · exact ⟨by linarith, by linarith⟩
      · rw [hoptN θ₂ h2' a2, hoptN θ₁ h1' a1] at hlt
        nlinarith [mul_le_mul_of_nonneg_right h12.le hAl0]
  · unfold sellerPayoffOpportunity at hlt
    by_cases a2 : θt < 1 - θ₂
    · have a1 : θt < 1 - θ₁ := by linarith
      rw [hoptS θ₂ h2' a2, hoptS θ₁ h1' a1] at hlt
      nlinarith [mul_le_mul_of_nonneg_right h12.le hAh0]
    · by_cases a1 : θt < 1 - θ₁
      · exact ⟨by linarith, by linarith⟩
      · rw [hoptN θ₂ h2' a2, hoptN θ₁ h1' a1] at hlt
        nlinarith [mul_le_mul_of_nonneg_right h12.le hAl0]
  · have cU : ∀ A : ℝ, Continuous fun x : ℝ => x * A := fun A => by fun_prop
    have cV : ∀ A : ℝ, Continuous fun x : ℝ => c + x * A := fun A => by fun_prop
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hN : Set.Ioo 0 (1 - θt) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds ⟨hθ.1, hlt⟩
      constructor
      · refine ((cU (totalSurplus μ αh c)).continuousAt (x := θ)).congr ?_
        filter_upwards [hN] with x hx
        unfold sellerPayoffMaterial
        rw [hoptS x ⟨hx.1, by linarith [hx.2]⟩ (by linarith [hx.2]), mul_comm]
      · refine ((cV (totalSurplus μ αh c)).continuousAt (x := θ)).congr ?_
        filter_upwards [hN] with x hx
        unfold sellerPayoffOpportunity
        rw [hoptS x ⟨hx.1, by linarith [hx.2]⟩ (by linarith [hx.2]), mul_comm]
    · have hN : Set.Ioo (1 - θt) 1 ∈ 𝓝 θ := isOpen_Ioo.mem_nhds ⟨hgt, hθ.2⟩
      constructor
      · refine ((cU (totalSurplus μ αl c)).continuousAt (x := θ)).congr ?_
        filter_upwards [hN] with x hx
        unfold sellerPayoffMaterial
        rw [hoptN x ⟨by linarith [hx.1], hx.2⟩ (by linarith [hx.1]), mul_comm]
      · refine ((cV (totalSurplus μ αl c)).continuousAt (x := θ)).congr ?_
        filter_upwards [hN] with x hx
        unfold sellerPayoffOpportunity
        rw [hoptN x ⟨by linarith [hx.1], hx.2⟩ (by linarith [hx.1]), mul_comm]

theorem p2r_thresh (hI : Integrable (fun u : ℝ => u) μ) (αl αh kbar θ : ℝ) (h0 : 0 < αl)
    (h1 : αl < αh) (hk : 0 < kbar) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hm : 0 ≤ priorMean μ) :
    ∃ cl ch : ℝ, cl ≤ priorMean μ ∧ priorMean μ ≤ ch ∧ ∀ c : ℝ, 0 < c →
      (kbar < θ * (totalSurplus μ αh c - totalSurplus μ αl c) ↔ cl < c ∧ c < ch) := by
  obtain ⟨S, hS⟩ : ∃ S : Set ℝ, ∀ c, c ∈ S ↔
      kbar < θ * (totalSurplus μ αh c - totalSurplus μ αl c) := ⟨_, fun c => Iff.rfl⟩
  have hgm : ∀ c, totalSurplus μ αh c - totalSurplus μ αl c ≤
      totalSurplus μ αh (priorMean μ) - totalSurplus μ αl (priorMean μ) :=
    fun c => p2r_gain_le_m hI c αl αh h0.le h1.le
  have hconv : ∀ a c b, a ≤ c → c ≤ b → a ∈ S → b ∈ S → c ∈ S := by
    intro a c b hac hcb ha hb
    rw [hS] at ha hb ⊢
    rcases le_total c (priorMean μ) with hc | hc
    · have := p2r_diff_low hI a c αl αh hac hc h0.le h1.le
      have hga : totalSurplus μ αh a - totalSurplus μ αl a ≤
          totalSurplus μ αh c - totalSurplus μ αl c := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hga hθ0]
    · have := p2r_diff_high hI c b αl αh hcb hc h0.le h1.le
      have hgb : totalSurplus μ αh b - totalSurplus μ αl b ≤
          totalSurplus μ αh c - totalSurplus μ αl c := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hgb hθ0]
  have hSeq : S = {c | kbar < θ * (totalSurplus μ αh c - totalSurplus μ αl c)} := Set.ext hS
  have hopen : IsOpen S := by
    rw [hSeq]
    exact isOpen_lt continuous_const
      (continuous_const.mul ((p2r_cont hI αh).sub (p2r_cont hI αl)))
  obtain ⟨R, hR⟩ := eventually_atTop.1 ((p2r_top hI αh).eventually (gt_mem_nhds hk))
  have hR' : ∀ c, R ≤ c → c ∉ S := by
    intro c hc hcS
    rw [hS] at hcS
    have e1 := hR c hc
    have e2 := p2r_nonneg (μ := μ) αl c
    have e3 := p2r_mono hI c αl αh h0.le h1.le
    nlinarith [mul_le_mul_of_nonneg_right hθ1 (sub_nonneg.2 e3)]
  by_cases hmS : priorMean μ ∈ S
  · have hTne : (S ∩ Set.Ici 0).Nonempty := ⟨priorMean μ, hmS, hm⟩
    have hTb : BddBelow (S ∩ Set.Ici 0) := ⟨0, fun x hx => hx.2⟩
    have hTa : BddAbove (S ∩ Set.Ici 0) := ⟨R, fun x hx => by
      by_contra h
      exact hR' x (le_of_lt (lt_of_not_ge h)) hx.1⟩
    refine ⟨sInf (S ∩ Set.Ici 0), sSup (S ∩ Set.Ici 0), csInf_le hTb ⟨hmS, hm⟩,
      le_csSup hTa ⟨hmS, hm⟩, fun c hc => ?_⟩
    rw [← hS]
    constructor
    · intro hcS
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen c hcS
      constructor
      · have hδ0 : 0 < min (ε / 2) (c / 2) := lt_min (by linarith) (by linarith)
        have hδ1 : min (ε / 2) (c / 2) ≤ ε / 2 := min_le_left _ _
        have hδ2 : min (ε / 2) (c / 2) ≤ c / 2 := min_le_right _ _
        have hmem : c - min (ε / 2) (c / 2) ∈ S ∩ Set.Ici 0 := by
          refine ⟨hball ?_, ?_⟩
          · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
          · rw [Set.mem_Ici]; linarith
        exact lt_of_le_of_lt (csInf_le hTb hmem) (by linarith)
      · have hmem : c + ε / 2 ∈ S ∩ Set.Ici 0 := by
          refine ⟨hball ?_, ?_⟩
          · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
          · rw [Set.mem_Ici]; linarith
        exact lt_of_lt_of_le (by linarith) (le_csSup hTa hmem)
    · rintro ⟨hl, hh⟩
      obtain ⟨a, ha, hac⟩ := exists_lt_of_csInf_lt hTne hl
      obtain ⟨b, hb, hcb⟩ := exists_lt_of_lt_csSup hTne hh
      exact hconv a c b hac.le hcb.le ha.1 hb.1
  · refine ⟨priorMean μ, priorMean μ, le_rfl, le_rfl, fun c hc => ?_⟩
    constructor
    · intro h
      exfalso
      apply hmS
      rw [hS]
      nlinarith [mul_le_mul_of_nonneg_left (hgm c) hθ0]
    · rintro ⟨ha, hb⟩; linarith

theorem p2r_part_ii (hI : Integrable (fun u : ℝ => u) μ) (D : Set ℝ) (hD : D ⊆ Set.Ioi 0)
    (hm : 0 ≤ priorMean μ) (αl αh kbar : ℝ) (h0 : 0 < αl) (h1 : αl < αh) (hk : 0 < kbar) :
    ∀ θs ∈ Set.Ioo (0:ℝ) 1, ∃ cl ch : ℝ,
      cl ≤ priorMean μ ∧ priorMean μ ≤ ch ∧
      (∀ c ∈ D, optimalInfo μ αl αh kbar (1 - θs) c = αh ↔ cl < c ∧ c < ch) ∧
      (∀ c₁ ∈ D, ∀ c₂ ∈ D, c₁ < c₂ →
        (sellerPayoffMaterial μ αl αh kbar θs c₁ < sellerPayoffMaterial μ αl αh kbar θs c₂ →
          c₁ ≤ cl ∧ cl < c₂) ∧
        (sellerPayoffOpportunity μ αl αh kbar θs c₂ <
            sellerPayoffOpportunity μ αl αh kbar θs c₁ →
          c₁ < ch ∧ ch ≤ c₂)) ∧
      (∀ c ∈ D, c ≠ cl → c ≠ ch →
        ContinuousAt (fun x => sellerPayoffMaterial μ αl αh kbar θs x) c ∧
        ContinuousAt (fun x => sellerPayoffOpportunity μ αl αh kbar θs x) c) := by
  intro θs hθ
  obtain ⟨cl, ch, hcl, hch, hiff⟩ := p2r_thresh hI αl αh kbar (1 - θs) h0 h1 hk
    (by linarith [hθ.2]) (by linarith [hθ.1]) hm
  have hθ0 : 0 ≤ θs := hθ.1.le
  have hoptS : ∀ c, 0 < c → cl < c → c < ch → optimalInfo μ αl αh kbar (1 - θs) c = αh :=
    fun c hc a b => by
      rw [p2r_opt hI αl αh kbar (1 - θs) c h0 h1 (by linarith [hθ.2]),
        if_pos ((hiff c hc).2 ⟨a, b⟩)]
  have hoptN : ∀ c, 0 < c → ¬ (cl < c ∧ c < ch) →
      optimalInfo μ αl αh kbar (1 - θs) c = αl := fun c hc h => by
    rw [p2r_opt hI αl αh kbar (1 - θs) c h0 h1 (by linarith [hθ.2]),
      if_neg (fun h' => h ((hiff c hc).1 h'))]
  have Am : ∀ c, totalSurplus μ αl c ≤ totalSurplus μ αh c :=
    fun c => p2r_mono hI c αl αh h0.le h1.le
  have hθd : ∀ c₁ c₂ : ℝ, c₁ ≤ c₂ → θs * (c₂ - c₁) ≤ c₂ - c₁ := fun c₁ c₂ h => by
    nlinarith [mul_le_mul_of_nonneg_right hθ.2.le (show 0 ≤ c₂ - c₁ by linarith)]
  refine ⟨cl, ch, hcl, hch, fun c hc => ⟨fun h => ?_, fun h => hoptS c (hD hc) h.1 h.2⟩,
    fun c₁ hc₁ c₂ hc₂ h12 => ⟨fun hlt => ?_, fun hlt => ?_⟩, fun c hc hne1 hne2 => ?_⟩
  · by_contra h'
    rw [hoptN c (hD hc) h'] at h
    exact h1.ne h
  · unfold sellerPayoffMaterial at hlt
    by_cases s2 : cl < c₂ ∧ c₂ < ch
    · by_cases s1 : cl < c₁ ∧ c₁ < ch
      · rw [hoptS c₂ (hD hc₂) s2.1 s2.2, hoptS c₁ (hD hc₁) s1.1 s1.2] at hlt
        nlinarith [mul_le_mul_of_nonneg_left (p2r_anti hI αh c₁ c₂ h12.le) hθ0]
      · refine ⟨?_, s2.1⟩
        by_contra h
        exact s1 ⟨lt_of_not_ge h, by linarith [s2.2]⟩
    · rw [hoptN c₂ (hD hc₂) s2] at hlt
      by_cases s1 : cl < c₁ ∧ c₁ < ch
      · rw [hoptS c₁ (hD hc₁) s1.1 s1.2] at hlt
        nlinarith [mul_le_mul_of_nonneg_left (p2r_anti hI αh c₁ c₂ h12.le) hθ0,
          mul_le_mul_of_nonneg_left (Am c₂) hθ0]
      · rw [hoptN c₁ (hD hc₁) s1] at hlt
        nlinarith [mul_le_mul_of_nonneg_left (p2r_anti hI αl c₁ c₂ h12.le) hθ0]
  · unfold sellerPayoffOpportunity at hlt
    have hd := hθd c₁ c₂ h12.le
    by_cases s1 : cl < c₁ ∧ c₁ < ch
    · by_cases s2 : cl < c₂ ∧ c₂ < ch
      · rw [hoptS c₂ (hD hc₂) s2.1 s2.2, hoptS c₁ (hD hc₁) s1.1 s1.2] at hlt
        nlinarith [mul_le_mul_of_nonneg_left (p2r_lip hI αh c₁ c₂ h12.le) hθ0]
      · refine ⟨s1.2, ?_⟩
        by_contra h
        exact s2 ⟨by linarith [s1.1], lt_of_not_ge h⟩
    · rw [hoptN c₁ (hD hc₁) s1] at hlt
      by_cases s2 : cl < c₂ ∧ c₂ < ch
      · rw [hoptS c₂ (hD hc₂) s2.1 s2.2] at hlt
        nlinarith [mul_le_mul_of_nonneg_left (p2r_lip hI αl c₁ c₂ h12.le) hθ0,
          mul_le_mul_of_nonneg_left (Am c₂) hθ0]
      · rw [hoptN c₂ (hD hc₂) s2] at hlt
        nlinarith [mul_le_mul_of_nonneg_left (p2r_lip hI αl c₁ c₂ h12.le) hθ0]
  · have cU : ∀ α, Continuous fun x => θs * totalSurplus μ α x :=
      fun α => continuous_const.mul (p2r_cont hI α)
    have cV : ∀ α, Continuous fun x => x + θs * totalSurplus μ α x :=
      fun α => continuous_id.add (cU α)
    by_cases s : cl < c ∧ c < ch
    · have hN : Set.Ioi 0 ∩ Set.Ioo cl ch ∈ 𝓝 c :=
        (isOpen_Ioi.inter isOpen_Ioo).mem_nhds ⟨hD hc, s⟩
      constructor
      · refine ((cU αh).continuousAt (x := c)).congr ?_
        filter_upwards [hN] with x hx
        unfold sellerPayoffMaterial
        rw [hoptS x hx.1 hx.2.1 hx.2.2]
      · refine ((cV αh).continuousAt (x := c)).congr ?_
        filter_upwards [hN] with x hx
        unfold sellerPayoffOpportunity
        rw [hoptS x hx.1 hx.2.1 hx.2.2]
    · obtain ⟨N, hN, hNx⟩ : ∃ N ∈ 𝓝 c, ∀ x ∈ N, 0 < x ∧ ¬ (cl < x ∧ x < ch) := by
        by_cases hlo : c < cl
        · exact ⟨Set.Ioi 0 ∩ Set.Iio cl, (isOpen_Ioi.inter isOpen_Iio).mem_nhds ⟨hD hc, hlo⟩,
            fun x hx => ⟨hx.1, fun h' => by linarith [Set.mem_Iio.1 hx.2, h'.1]⟩⟩
        · have hhi : ch < c := by
            by_contra hh
            exact s ⟨lt_of_le_of_ne (le_of_not_gt hlo) (fun e => hne1 e.symm),
              lt_of_le_of_ne (le_of_not_gt hh) hne2⟩
          exact ⟨Set.Ioi 0 ∩ Set.Ioi ch, (isOpen_Ioi.inter isOpen_Ioi).mem_nhds ⟨hD hc, hhi⟩,
            fun x hx => ⟨hx.1, fun h' => by linarith [Set.mem_Ioi.1 hx.2, h'.2]⟩⟩
      constructor
      · refine ((cU αl).continuousAt (x := c)).congr ?_
        filter_upwards [hN] with x hx
        unfold sellerPayoffMaterial
        rw [hoptN x (hNx x hx).1 (hNx x hx).2]
      · refine ((cV αl).continuousAt (x := c)).congr ?_
        filter_upwards [hN] with x hx
        unfold sellerPayoffOpportunity
        rw [hoptN x (hNx x hx).1 (hNx x hx).2]

end Parts

section May

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem p2r_Am (a : ℝ) (ha : 0 ≤ a) :
    totalSurplus μ a (priorMean μ) = a * ∫ u, max (u - priorMean μ) 0 ∂μ := by
  rw [p2r_tS_eq, ← integral_const_mul]
  congr 1
  ext u
  unfold p2rF
  rcases le_total (u - priorMean μ) 0 with h | h
  · have := mul_nonpos_of_nonneg_of_nonpos ha h
    rw [max_eq_right h, max_eq_right (by nlinarith)]; ring
  · have := mul_nonneg ha h
    rw [max_eq_left h, max_eq_left (by nlinarith)]; ring

theorem p2r_may_i (hI : Integrable (fun u : ℝ => u) μ)
    (hK : 0 < ∫ u, max (u - priorMean μ) 0 ∂μ) (D : Set ℝ) (hmD : priorMean μ ∈ D) :
    ∃ αl αh kbar c θ₁ θ₂ : ℝ, 0 < αl ∧ αl < αh ∧ αh < 1 ∧ 0 < kbar ∧ c ∈ D ∧
      0 < θ₁ ∧ θ₁ < θ₂ ∧ θ₂ < 1 ∧
      sellerPayoffMaterial μ αl αh kbar θ₂ c < sellerPayoffMaterial μ αl αh kbar θ₁ c ∧
      sellerPayoffOpportunity μ αl αh kbar θ₂ c < sellerPayoffOpportunity μ αl αh kbar θ₁ c := by
  have e1 := p2r_Am (μ := μ) (1/2) (by norm_num)
  have e2 := p2r_Am (μ := μ) (1/4) (by norm_num)
  obtain ⟨K, hKd⟩ : ∃ K, ∫ u, max (u - priorMean μ) 0 ∂μ = K := ⟨_, rfl⟩
  rw [hKd] at hK e1 e2
  have o1 : optimalInfo μ (1/4) (1/2) (K/8) (1 - 3/8) (priorMean μ) = 1/2 := by
    rw [p2r_opt hI _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num), if_pos (by rw [e1, e2]; linarith)]
  have o2 : optimalInfo μ (1/4) (1/2) (K/8) (1 - 1/2) (priorMean μ) = 1/4 := by
    rw [p2r_opt hI _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num),
      if_neg (by rw [e1, e2]; intro h; linarith)]
  refine ⟨1/4, 1/2, K/8, priorMean μ, 3/8, 1/2, by norm_num, by norm_num, by norm_num,
    by positivity, hmD, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · unfold sellerPayoffMaterial; rw [o1, o2, e1, e2]; linarith
  · unfold sellerPayoffOpportunity; rw [o1, o2, e1, e2]; linarith

theorem p2r_may_ii (hI : Integrable (fun u : ℝ => u) μ)
    (hK : 0 < ∫ u, max (u - priorMean μ) 0 ∂μ) (D : Set ℝ) (hm : 0 < priorMean μ)
    (hDm : Set.Ioc 0 (priorMean μ) ⊆ D) :
    ∃ αl αh kbar θs c₁ c₂ : ℝ, 0 < αl ∧ αl < αh ∧ αh < 1 ∧ 0 < kbar ∧ 0 < θs ∧ θs < 1 ∧
      c₁ ∈ D ∧ c₂ ∈ D ∧ c₁ < c₂ ∧
      sellerPayoffMaterial μ αl αh kbar θs c₁ < sellerPayoffMaterial μ αl αh kbar θs c₂ := by
  obtain ⟨a0, ha0⟩ := eventually_atBot.1 ((p2r_bot (μ := μ) hI).eventually (gt_mem_nhds (half_pos hK)))
  obtain ⟨K, hKd⟩ : ∃ K, ∫ u, max (u - priorMean μ) 0 ∂μ = K := ⟨_, rfl⟩
  rw [hKd] at hK ha0
  obtain ⟨ah, hah⟩ : ∃ ah : ℝ, ah = min (1/2) (priorMean μ / (2 * (priorMean μ + |a0|))) := ⟨_, rfl⟩
  have hpos : 0 < 2 * (priorMean μ + |a0|) := by positivity
  have hah0 : 0 < ah := by rw [hah]; exact lt_min (by norm_num) (div_pos hm hpos)
  have hah1 : ah ≤ 1/2 := by rw [hah]; exact min_le_left _ _
  have hah2 : ah * (2 * (priorMean μ + |a0|)) ≤ priorMean μ := by
    rw [← le_div_iff₀ hpos, hah]; exact min_le_right _ _
  have e1 := p2r_Am (μ := μ) ah hah0.le
  have e2 := p2r_Am (μ := μ) (ah/2) (by positivity)
  rw [hKd] at e1 e2
  obtain ⟨a', ha'⟩ : ∃ a' : ℝ, a' = (priorMean μ/2 - (1 - ah) * priorMean μ) / ah := ⟨_, rfl⟩
  have hA : ah * a' = priorMean μ/2 - (1 - ah) * priorMean μ := by rw [ha']; field_simp
  have ha'0 : a' ≤ a0 := by
    rw [ha', div_le_iff₀ hah0]
    nlinarith [mul_le_mul_of_nonneg_left (neg_abs_le a0) hah0.le]
  have hlt := ha0 a' ha'0
  have hIp : Integrable (fun u : ℝ => max (priorMean μ/2 - (ah * u + (1 - ah) * priorMean μ)) 0) μ :=
    ((integrable_const _).sub ((hI.const_mul ah).add (integrable_const _))).pos_part
  have hput : ∫ u, p2rF μ ah (priorMean μ/2) u ∂μ ≤
      ∫ u, (p2rF μ (ah/2) (priorMean μ/2) u + max (priorMean μ/2 - (ah * u + (1 - ah) * priorMean μ)) 0) ∂μ := by
    refine p2r_ile hI _ _ (p2r_int hI ah (priorMean μ/2)) ((p2r_int hI (ah/2) (priorMean μ/2)).add hIp) (ah/2 - ah)
      (fun u => ?_)
    unfold p2rF
    have := le_max_left (ah / 2 * u + (1 - ah / 2) * priorMean μ - priorMean μ / 2) 0
    have := le_max_left (priorMean μ / 2 - (ah * u + (1 - ah) * priorMean μ)) 0
    have := le_max_right (priorMean μ / 2 - (ah * u + (1 - ah) * priorMean μ)) 0
    have := le_max_right (ah / 2 * u + (1 - ah / 2) * priorMean μ - priorMean μ / 2) 0
    rcases le_total (ah * u + (1 - ah) * priorMean μ - priorMean μ / 2) 0 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  rw [integral_add (p2r_int hI (ah/2) (priorMean μ/2)) hIp, ← p2r_tS_eq, ← p2r_tS_eq] at hput
  have hpe : ∫ u, max (priorMean μ/2 - (ah * u + (1 - ah) * priorMean μ)) 0 ∂μ = ah * ∫ u, max (a' - u) 0 ∂μ := by
    rw [← integral_const_mul]
    congr 1
    ext u
    have e : priorMean μ/2 - (ah * u + (1 - ah) * priorMean μ) = ah * (a' - u) := by rw [mul_sub, hA]; ring
    rw [e]
    rcases le_total (a' - u) 0 with h | h
    · have := mul_nonpos_of_nonneg_of_nonpos hah0.le h
      rw [max_eq_right h, max_eq_right this]; ring
    · have := mul_nonneg hah0.le h
      rw [max_eq_left h, max_eq_left this]
  rw [hpe] at hput
  have hG0 : totalSurplus μ ah (priorMean μ/2) - totalSurplus μ (ah/2) (priorMean μ/2) < ah * K / 2 := by
    have := mul_lt_mul_of_pos_left hlt hah0
    linarith
  have hG0' : 0 ≤ totalSurplus μ ah (priorMean μ/2) - totalSurplus μ (ah/2) (priorMean μ/2) := by
    have := p2r_mono hI (priorMean μ/2) (ah/2) ah (by positivity) (by linarith); linarith
  have hKah : 0 < ah * K := mul_pos hah0 hK
  obtain ⟨cl, ch, hcl, hch, hiff⟩ := p2r_thresh hI (ah/2) ah
    ((totalSurplus μ ah (priorMean μ/2) - totalSurplus μ (ah/2) (priorMean μ/2) + ah * K / 2) / 4) (1 - 1/2)
    (by positivity) (by linarith) (by positivity) (by norm_num) (by norm_num) hm.le
  have hmS : cl < priorMean μ ∧ priorMean μ < ch := (hiff _ hm).1 (by rw [e1, e2]; linarith)
  have hc0 : ¬ (cl < priorMean μ/2 ∧ priorMean μ/2 < ch) := fun h => by
    have := (hiff (priorMean μ/2) (by linarith)).2 h
    linarith
  have hc0l : priorMean μ/2 ≤ cl := by
    by_contra h
    exact hc0 ⟨lt_of_not_ge h, by linarith [hmS.2]⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min ((totalSurplus μ ah (priorMean μ/2) - totalSurplus μ (ah/2) (priorMean μ/2) +
      ah * K / 2) / 4) ((priorMean μ - cl)/2) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by positivity) (by linarith [hmS.1])
  have hδ1 : δ ≤ (totalSurplus μ ah (priorMean μ/2) - totalSurplus μ (ah/2) (priorMean μ/2) + ah * K / 2) / 4 := by
    rw [hδ]; exact min_le_left _ _
  have hδ2 : δ ≤ (priorMean μ - cl)/2 := by rw [hδ]; exact min_le_right _ _
  have g2 := (hiff (cl + δ) (by linarith)).2 ⟨by linarith, by linarith [hmS.2]⟩
  have o1 : optimalInfo μ (ah/2) ah
      ((totalSurplus μ ah (priorMean μ/2) - totalSurplus μ (ah/2) (priorMean μ/2) + ah * K / 2) / 4) (1 - 1/2) cl
      = ah/2 := by
    rw [p2r_opt hI _ _ _ _ _ (by positivity) (by linarith) (by norm_num),
      if_neg (fun h => by have := (hiff cl (by linarith)).1 h; linarith [this.1])]
  have o2 : optimalInfo μ (ah/2) ah
      ((totalSurplus μ ah (priorMean μ/2) - totalSurplus μ (ah/2) (priorMean μ/2) + ah * K / 2) / 4) (1 - 1/2)
      (cl + δ) = ah := by
    rw [p2r_opt hI _ _ _ _ _ (by positivity) (by linarith) (by norm_num), if_pos g2]
  refine ⟨ah/2, ah, (totalSurplus μ ah (priorMean μ/2) - totalSurplus μ (ah/2) (priorMean μ/2) + ah * K / 2) / 4,
    1/2, cl, cl + δ, by positivity, by linarith, by linarith, by positivity, by norm_num,
    by norm_num, hDm ⟨by linarith, by linarith [hmS.1]⟩, hDm ⟨by linarith, by linarith⟩,
    by linarith, ?_⟩
  unfold sellerPayoffMaterial
  rw [o1, o2]
  have := p2r_lip hI (ah/2) cl (cl + δ) (by linarith)
  linarith

theorem p2r_may_iii (hI : Integrable (fun u : ℝ => u) μ)
    (hK : 0 < ∫ u, max (u - priorMean μ) 0 ∂μ) (D : Set ℝ) (hm : 0 < priorMean μ) (R : ℝ)
    (hmR : priorMean μ < R) (hRD : Set.Icc (priorMean μ) R ⊆ D)
    (hR : totalSurplus μ (1/2) R ≤ (∫ u, max (u - priorMean μ) 0 ∂μ) / 8) :
    ∃ αl αh kbar θs c₁ c₂ : ℝ, 0 < αl ∧ αl < αh ∧ αh < 1 ∧ 0 < kbar ∧ 0 < θs ∧ θs < 1 ∧
      c₁ ∈ D ∧ c₂ ∈ D ∧ c₁ < c₂ ∧
      sellerPayoffOpportunity μ αl αh kbar θs c₂ < sellerPayoffOpportunity μ αl αh kbar θs c₁ := by
  have e1 := p2r_Am (μ := μ) (1/2) (by norm_num)
  have e2 := p2r_Am (μ := μ) (1/4) (by norm_num)
  obtain ⟨K, hKd⟩ : ∃ K, ∫ u, max (u - priorMean μ) 0 ∂μ = K := ⟨_, rfl⟩
  rw [hKd] at hK e1 e2 hR
  obtain ⟨cl, ch, hcl, hch, hiff⟩ := p2r_thresh hI (1/4) (1/2) (K/16) (1 - 1/2) (by norm_num)
    (by norm_num) (by positivity) (by norm_num) (by norm_num) hm.le
  have hmS : cl < priorMean μ ∧ priorMean μ < ch := (hiff _ hm).1 (by rw [e1, e2]; linarith)
  have hRS : ¬ (cl < R ∧ R < ch) := fun h => by
    have h1 := (hiff R (by linarith)).2 h
    have h2 := p2r_nonneg (μ := μ) (1/4) R
    linarith
  have hchR : ch ≤ R := by
    by_contra h
    exact hRS ⟨by linarith [hmS.1], lt_of_not_ge h⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (K/32) ((ch - priorMean μ)/2) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by positivity) (by linarith [hmS.2])
  have hδ1 : δ ≤ K/32 := by rw [hδ]; exact min_le_left _ _
  have hδ2 : δ ≤ (ch - priorMean μ)/2 := by rw [hδ]; exact min_le_right _ _
  have g1 := (hiff (ch - δ) (by linarith)).2 ⟨by linarith [hmS.1], by linarith⟩
  have o1 : optimalInfo μ (1/4) (1/2) (K/16) (1 - 1/2) (ch - δ) = 1/2 := by
    rw [p2r_opt hI _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num), if_pos g1]
  have o2 : optimalInfo μ (1/4) (1/2) (K/16) (1 - 1/2) ch = 1/4 := by
    rw [p2r_opt hI _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num),
      if_neg (fun h => by have := (hiff ch (by linarith)).1 h; linarith [this.2])]
  refine ⟨1/4, 1/2, K/16, 1/2, ch - δ, ch, by norm_num, by norm_num, by norm_num, by positivity,
    by norm_num, by norm_num, hRD ⟨by linarith, by linarith⟩, hRD ⟨by linarith, hchR⟩,
    by linarith, ?_⟩
  unfold sellerPayoffOpportunity
  rw [o1, o2]
  have := p2r_anti hI (1/4) (ch - δ) ch (by linarith)
  linarith

end May

theorem p2r_main (μ : Measure ℝ) [IsProbabilityMeasure μ] (hI : Integrable (fun u : ℝ => u) μ)
    (hac : μ ≪ volume) (D : Set ℝ) (hD : D ⊆ Set.Ioi 0) (hm : 0 < priorMean μ)
    (hDm : Set.Ioc 0 (priorMean μ) ⊆ D) (R : ℝ) (hmR : priorMean μ < R)
    (hRD : Set.Icc (priorMean μ) R ⊆ D)
    (hR : totalSurplus μ (1/2) R ≤ (∫ u, max (u - priorMean μ) 0 ∂μ) / 8) :
    (∀ αl αh kbar : ℝ, 0 < αl → αl < αh → αh < 1 → 0 < kbar →
      (∀ c ∈ D, ∃ θt : ℝ, 0 < θt ∧ θt ≤ 1 ∧
        (∀ θs ∈ Set.Ioo (0:ℝ) 1,
          optimalInfo μ αl αh kbar (1 - θs) c = αh ↔ θt < 1 - θs) ∧
        (∀ θ₁ ∈ Set.Ioo (0:ℝ) 1, ∀ θ₂ ∈ Set.Ioo (0:ℝ) 1, θ₁ < θ₂ →
          (sellerPayoffMaterial μ αl αh kbar θ₂ c <
              sellerPayoffMaterial μ αl αh kbar θ₁ c →
            θ₁ < 1 - θt ∧ 1 - θt ≤ θ₂) ∧
          (sellerPayoffOpportunity μ αl αh kbar θ₂ c <
              sellerPayoffOpportunity μ αl αh kbar θ₁ c →
            θ₁ < 1 - θt ∧ 1 - θt ≤ θ₂)) ∧
        (∀ θ ∈ Set.Ioo (0:ℝ) 1, θ ≠ 1 - θt →
          ContinuousAt (fun θs => sellerPayoffMaterial μ αl αh kbar θs c) θ ∧
          ContinuousAt (fun θs => sellerPayoffOpportunity μ αl αh kbar θs c) θ)) ∧
      (∀ θs ∈ Set.Ioo (0:ℝ) 1, ∃ cl ch : ℝ,
        cl ≤ priorMean μ ∧ priorMean μ ≤ ch ∧
        (∀ c ∈ D,
          optimalInfo μ αl αh kbar (1 - θs) c = αh ↔ cl < c ∧ c < ch) ∧
        (∀ c₁ ∈ D, ∀ c₂ ∈ D, c₁ < c₂ →
          (sellerPayoffMaterial μ αl αh kbar θs c₁ <
              sellerPayoffMaterial μ αl αh kbar θs c₂ →
            c₁ ≤ cl ∧ cl < c₂) ∧
          (sellerPayoffOpportunity μ αl αh kbar θs c₂ <
              sellerPayoffOpportunity μ αl αh kbar θs c₁ →
            c₁ < ch ∧ ch ≤ c₂)) ∧
        (∀ c ∈ D, c ≠ cl → c ≠ ch →
          ContinuousAt (fun x => sellerPayoffMaterial μ αl αh kbar θs x) c ∧
          ContinuousAt (fun x => sellerPayoffOpportunity μ αl αh kbar θs x) c))) ∧
    (∃ αl αh kbar c θ₁ θ₂ : ℝ, 0 < αl ∧ αl < αh ∧ αh < 1 ∧ 0 < kbar ∧ c ∈ D ∧
      0 < θ₁ ∧ θ₁ < θ₂ ∧ θ₂ < 1 ∧
      sellerPayoffMaterial μ αl αh kbar θ₂ c <
        sellerPayoffMaterial μ αl αh kbar θ₁ c ∧
      sellerPayoffOpportunity μ αl αh kbar θ₂ c <
        sellerPayoffOpportunity μ αl αh kbar θ₁ c) ∧
    (∃ αl αh kbar θs c₁ c₂ : ℝ, 0 < αl ∧ αl < αh ∧ αh < 1 ∧ 0 < kbar ∧ 0 < θs ∧ θs < 1 ∧
      c₁ ∈ D ∧ c₂ ∈ D ∧ c₁ < c₂ ∧
      sellerPayoffMaterial μ αl αh kbar θs c₁ <
        sellerPayoffMaterial μ αl αh kbar θs c₂) ∧
    (∃ αl αh kbar θs c₁ c₂ : ℝ, 0 < αl ∧ αl < αh ∧ αh < 1 ∧ 0 < kbar ∧ 0 < θs ∧ θs < 1 ∧
      c₁ ∈ D ∧ c₂ ∈ D ∧ c₁ < c₂ ∧
      sellerPayoffOpportunity μ αl αh kbar θs c₂ <
        sellerPayoffOpportunity μ αl αh kbar θs c₁) := by
  have hK := p2r_K_pos hI hac
  exact ⟨fun αl αh kbar h0 h1 _ hk => ⟨fun c _ => p2r_part_i hI αl αh kbar c h0 h1 hk,
    p2r_part_ii hI D hD hm.le αl αh kbar h0 h1 hk⟩, p2r_may_i hI hK D (hDm ⟨hm, le_rfl⟩),
    p2r_may_ii hI hK D hm hDm, p2r_may_iii hI hK D hm R hmR hRD hR⟩

/-- the unbounded-domain R -/
theorem p2r_R_unb (μ : Measure ℝ) [IsProbabilityMeasure μ] (hI : Integrable (fun u : ℝ => u) μ)
    (hac : μ ≪ volume) : ∃ R, priorMean μ < R ∧
      totalSurplus μ (1/2) R ≤ (∫ u, max (u - priorMean μ) 0 ∂μ) / 8 := by
  have hK := p2r_K_pos hI hac
  obtain ⟨R0, hR0⟩ := eventually_atTop.1 ((p2r_top hI (1/2)).eventually
    (gt_mem_nhds (by positivity : (0:ℝ) < (∫ u, max (u - priorMean μ) 0 ∂μ) / 8)))
  exact ⟨max R0 (priorMean μ + 1), by linarith [le_max_right R0 (priorMean μ + 1)],
    (hR0 _ (le_max_left _ _)).le⟩

/-- the bounded-support R: u ≤ 1 a.e. -/
theorem p2r_R_bdd (μ : Measure ℝ) [IsProbabilityMeasure μ] (h1 : ∀ᵐ u ∂μ, u ≤ 1) :
    totalSurplus μ (1/2) ((1 + priorMean μ) / 2) = 0 := by
  have h : (fun u => p2rF μ (1/2) ((1 + priorMean μ) / 2) u) =ᵐ[μ] fun _ => (0:ℝ) :=
    h1.mono fun u hu => by
      simp only [p2rF]
      exact max_eq_right (by linarith)
  rw [p2r_tS_eq, integral_congr_ae h]
  simp

theorem p2r_int_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (hac : μ ≪ volume) (f : ℝ → ℝ)
    (hf0 : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) (b : ℝ) (hfb : ∀ u, u ≠ b → f u ≠ 0) :
    0 < ∫ u, f u ∂μ := by
  rw [integral_pos_iff_support_of_nonneg_ae hf0 hfi]
  have h1 : μ ({b}ᶜ) = 1 :=
    (prob_compl_eq_one_iff (measurableSet_singleton b)).2 (hac Real.volume_singleton)
  have h2 : ({b}ᶜ : Set ℝ) ⊆ Function.support f := fun u hu => hfb u hu
  calc (0 : ENNReal) < 1 := one_pos
    _ = μ {b}ᶜ := h1.symm
    _ ≤ μ (Function.support f) := measure_mono h2

theorem p2r_facts01 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hac : μ ≪ volume)
    (h0 : ∀ᵐ u ∂μ, 0 ≤ u) (h1 : ∀ᵐ u ∂μ, u ≤ 1) :
    Integrable (fun u : ℝ => u) μ ∧ 0 < priorMean μ ∧ priorMean μ < 1 := by
  have hI : Integrable (fun u : ℝ => u) μ :=
    Integrable.of_bound measurable_id.aestronglyMeasurable 1 (by
      filter_upwards [h0, h1] with u a b
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
  refine ⟨hI, p2r_int_pos μ hac (fun u => u) h0 hI 0 (fun u hu => hu), ?_⟩
  have := p2r_int_pos μ hac (fun u => 1 - u) (h1.mono fun u hu => by
      simp only [Pi.zero_apply]; linarith) ((integrable_const 1).sub hI) 1
    (fun u hu h => hu (by linarith))
  rw [integral_sub (integrable_const 1) hI] at this
  simp at this
  unfold priorMean
  linarith

theorem p2r_unif_facts :
    IsProbabilityMeasure ((volume : Measure ℝ).restrict (Set.Icc 0 1)) ∧
    (volume : Measure ℝ).restrict (Set.Icc 0 1) ≪ volume ∧
    (∀ᵐ u ∂((volume : Measure ℝ).restrict (Set.Icc 0 1)), 0 ≤ u) ∧
    (∀ᵐ u ∂((volume : Measure ℝ).restrict (Set.Icc 0 1)), u ≤ 1) :=
  ⟨⟨by simp⟩, Measure.absolutelyContinuous_of_le Measure.restrict_le_self,
    (ae_restrict_mem measurableSet_Icc).mono fun _ hu => hu.1,
    (ae_restrict_mem measurableSet_Icc).mono fun _ hu => hu.2⟩

theorem p2r_beta_facts (lam : ℝ) (hlam : 0 < lam) :
    IsProbabilityMeasure (ProbabilityTheory.betaMeasure 1 lam) ∧
    ProbabilityTheory.betaMeasure 1 lam ≪ volume ∧
    (∀ᵐ u ∂(ProbabilityTheory.betaMeasure 1 lam), 0 ≤ u) ∧
    (∀ᵐ u ∂(ProbabilityTheory.betaMeasure 1 lam), u ≤ 1) := by
  have hmeas : Measurable (ProbabilityTheory.betaPDF 1 lam) :=
    (ProbabilityTheory.measurable_betaPDFReal 1 lam).ennreal_ofReal
  have hs : ∀ᵐ u ∂((volume : Measure ℝ).withDensity (ProbabilityTheory.betaPDF 1 lam)),
      0 < u ∧ u < 1 :=
    (ae_withDensity_iff hmeas).2 (Eventually.of_forall fun u hu =>
      ⟨lt_of_not_ge fun h => hu (ProbabilityTheory.betaPDF_eq_zero_of_nonpos h),
        lt_of_not_ge fun h => hu (ProbabilityTheory.betaPDF_eq_zero_of_one_le h)⟩)
  exact ⟨ProbabilityTheory.isProbabilityMeasureBeta one_pos hlam,
    withDensity_absolutelyContinuous _ _, hs.mono fun _ h => h.1.le, hs.mono fun _ h => h.2.le⟩


theorem p2r_xexp (b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-b * x)) (Set.Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (by norm_num) one_pos
    hb).congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]

theorem p2r_abs_int (h : ℝ → ℝ) (hh : IntegrableOn h (Set.Ioi 0)) :
    Integrable (fun x => h |x|) := by
  have hf : IntegrableOn (fun x => h |x|) (Set.Ioi 0) :=
    hh.congr_fun (fun x hx => by rw [abs_of_pos (show (0:ℝ) < x from hx)]) measurableSet_Ioi
  have int_Iic : IntegrableOn (fun x ↦ h |x|) (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, Set.neg_preimage, Set.neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
  have := int_Iic.union hf
  rwa [Set.Iic_union_Ioi, integrableOn_univ] at this

theorem p2r_exp_facts (uhat : ℝ) (hu : 0 < uhat) :
    IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 / uhat)) ∧
    ProbabilityTheory.expMeasure (1 / uhat) ≪ volume ∧
    (∀ᵐ u ∂(ProbabilityTheory.expMeasure (1 / uhat)), 0 ≤ u) ∧
    Integrable (fun u : ℝ => u) (ProbabilityTheory.expMeasure (1 / uhat)) := by
  have hr : 0 < 1 / uhat := by positivity
  have hmeas : Measurable (ProbabilityTheory.gammaPDF 1 (1/uhat)) :=
    (ProbabilityTheory.measurable_gammaPDFReal 1 (1/uhat)).ennreal_ofReal
  refine ⟨ProbabilityTheory.isProbabilityMeasure_expMeasure hr,
    withDensity_absolutelyContinuous _ _, ?_, ?_⟩
  · exact (ae_withDensity_iff hmeas).2 (Eventually.of_forall fun u hu =>
      le_of_not_gt fun h => hu (ProbabilityTheory.gammaPDF_of_neg h))
  · show Integrable _ ((volume : Measure ℝ).withDensity (ProbabilityTheory.gammaPDF 1 (1/uhat)))
    rw [integrable_withDensity_iff_integrable_smul' hmeas
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hdom := p2r_abs_int (fun x => (1/uhat) * (x * Real.exp (-(1/uhat) * x)))
      ((p2r_xexp _ hr).const_mul _)
    refine hdom.mono' ((hmeas.ennreal_toReal.smul measurable_id).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    have hpos : 0 ≤ (1/uhat) * (|x| * Real.exp (-(1/uhat) * |x|)) := by positivity
    rcases lt_or_ge x 0 with hx | hx
    · simp [ProbabilityTheory.gammaPDF_of_neg hx]; positivity
    · rw [ProbabilityTheory.gammaPDF_of_nonneg hx, ENNReal.toReal_ofReal (by positivity),
        abs_of_nonneg hx]
      simp only [Real.Gamma_one, sub_self, Real.rpow_zero, Real.rpow_one, smul_eq_mul]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      ring_nf; exact le_rfl

noncomputable def p2rG (t : ℝ) : ℝ := Real.exp (-t) / (1 + Real.exp (-t)) ^ 2

theorem p2rG_nonneg (t : ℝ) : 0 ≤ p2rG t := by unfold p2rG; positivity

theorem p2rG_cont : Continuous p2rG := by
  unfold p2rG
  exact Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity)

theorem p2rG_even (t : ℝ) : p2rG (-t) = p2rG t := by
  unfold p2rG
  rw [neg_neg, Real.exp_neg]
  have := Real.exp_pos t
  field_simp
  ring

theorem p2rG_abs (t : ℝ) : p2rG |t| = p2rG t := by
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  exact p2rG_even t

theorem p2rG_le (t : ℝ) : p2rG t ≤ Real.exp (-1 * |t|) := by
  rw [← p2rG_abs, neg_one_mul]
  unfold p2rG
  exact div_le_self (Real.exp_pos _).le
    (one_le_pow₀ (by linarith [Real.exp_pos (-|t|)]))

theorem p2rG_int : Integrable p2rG := by
  refine (p2r_abs_int (fun x => Real.exp (-1 * x)) (exp_neg_integrableOn_Ioi 0 one_pos)).mono'
    p2rG_cont.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (p2rG_nonneg x)]
  exact p2rG_le x

theorem p2rG_int_mul : Integrable (fun t => t * p2rG t) := by
  refine (p2r_abs_int (fun x => x * Real.exp (-1 * x)) (p2r_xexp 1 one_pos)).mono'
    (continuous_id.mul p2rG_cont).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (p2rG_nonneg x)]
  exact mul_le_mul_of_nonneg_left (p2rG_le x) (abs_nonneg x)

theorem p2rG_integral : ∫ t, p2rG t = 1 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t => (1 + Real.exp (-t))⁻¹) (p2rG t) t := by
    intro t
    have h1 := (((hasDerivAt_neg t).exp).const_add 1).inv (by positivity)
    exact h1.congr_deriv (by unfold p2rG; ring)
  have htop : Tendsto (fun t : ℝ => (1 + Real.exp (-t))⁻¹) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1:ℝ))).add Real.tendsto_exp_neg_atTop_nhds_zero
    simpa using this.inv₀ (by norm_num)
  have hbot : Tendsto (fun t : ℝ => (1 + Real.exp (-t))⁻¹) atBot (𝓝 0) :=
    (tendsto_atTop_add_const_left _ 1
      (Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop)).inv_tendsto_atTop
  rw [integral_of_hasDerivAt_of_tendsto hd p2rG_int hbot htop]
  norm_num

theorem p2rG_mean0 : ∫ t, t * p2rG t = 0 := by
  have h := integral_neg_eq_self (fun t => t * p2rG t) (volume : Measure ℝ)
  simp only [p2rG_even, neg_mul, integral_neg] at h
  linarith

theorem p2r_log_facts (uhat : ℝ) (hu : 0 < uhat) :
    IsProbabilityMeasure ((volume : Measure ℝ).withDensity
      (fun u => ENNReal.ofReal (Real.exp (-(u - uhat)) / (1 + Real.exp (-(u - uhat))) ^ 2))) ∧
    (volume : Measure ℝ).withDensity
      (fun u => ENNReal.ofReal (Real.exp (-(u - uhat)) / (1 + Real.exp (-(u - uhat))) ^ 2))
      ≪ volume ∧
    Integrable (fun u : ℝ => u) ((volume : Measure ℝ).withDensity
      (fun u => ENNReal.ofReal (Real.exp (-(u - uhat)) / (1 + Real.exp (-(u - uhat))) ^ 2))) ∧
    0 < priorMean ((volume : Measure ℝ).withDensity
      (fun u => ENNReal.ofReal (Real.exp (-(u - uhat)) / (1 + Real.exp (-(u - uhat))) ^ 2))) := by
  change IsProbabilityMeasure ((volume : Measure ℝ).withDensity
      (fun u => ENNReal.ofReal (p2rG (u - uhat)))) ∧
    (volume : Measure ℝ).withDensity (fun u => ENNReal.ofReal (p2rG (u - uhat))) ≪ volume ∧
    Integrable (fun u : ℝ => u) ((volume : Measure ℝ).withDensity
      (fun u => ENNReal.ofReal (p2rG (u - uhat)))) ∧
    0 < priorMean ((volume : Measure ℝ).withDensity (fun u => ENNReal.ofReal (p2rG (u - uhat))))
  have hmeas : Measurable (fun u => ENNReal.ofReal (p2rG (u - uhat))) :=
    (p2rG_cont.comp (continuous_sub_right uhat)).measurable.ennreal_ofReal
  have hlt : ∀ᵐ u ∂(volume : Measure ℝ), ENNReal.ofReal (p2rG (u - uhat)) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hk : Integrable (fun t => t * p2rG t + uhat * p2rG t) :=
    p2rG_int_mul.add (p2rG_int.const_mul uhat)
  have hke : ∀ u : ℝ, (ENNReal.ofReal (p2rG (u - uhat))).toReal • u =
      (fun t => t * p2rG t + uhat * p2rG t) (u - uhat) := by
    intro u
    rw [ENNReal.toReal_ofReal (p2rG_nonneg _), smul_eq_mul]
    ring
  refine ⟨⟨?_⟩, withDensity_absolutelyContinuous _ _, ?_, ?_⟩
  · rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (p2rG_int.comp_sub_right uhat)
        (Eventually.of_forall fun _ => p2rG_nonneg _),
      integral_sub_right_eq_self (fun t => p2rG t) uhat, p2rG_integral, ENNReal.ofReal_one]
  · rw [integrable_withDensity_iff_integrable_smul' hmeas hlt]
    exact (hk.comp_sub_right uhat).congr (Eventually.of_forall fun u => (hke u).symm)
  · unfold priorMean
    rw [integral_withDensity_eq_integral_toReal_smul hmeas hlt]
    simp_rw [hke]
    rw [integral_sub_right_eq_self (fun t => t * p2rG t + uhat * p2rG t) uhat,
      integral_add p2rG_int_mul (p2rG_int.const_mul uhat), integral_const_mul,
      p2rG_mean0, p2rG_integral]
    linarith

end InfoBargaining.SellerPayoff

open MeasureTheory InfoBargaining.SellerPayoff in
theorem solution (P : FocalPrior) :
    (∀ αl αh kbar : ℝ, 0 < αl → αl < αh → αh < 1 → 0 < kbar →
      -- (i): in θs, at each fixed c; θt is Corollary 1 (i)'s θ̃
      (∀ c ∈ P.costDomain, ∃ θt : ℝ, 0 < θt ∧ θt ≤ 1 ∧
        (∀ θs ∈ Set.Ioo (0:ℝ) 1,
          optimalInfo P.measure αl αh kbar (1 - θs) c = αh ↔ θt < 1 - θs) ∧
        (∀ θ₁ ∈ Set.Ioo (0:ℝ) 1, ∀ θ₂ ∈ Set.Ioo (0:ℝ) 1, θ₁ < θ₂ →
          (sellerPayoffMaterial P.measure αl αh kbar θ₂ c <
              sellerPayoffMaterial P.measure αl αh kbar θ₁ c →
            θ₁ < 1 - θt ∧ 1 - θt ≤ θ₂) ∧
          (sellerPayoffOpportunity P.measure αl αh kbar θ₂ c <
              sellerPayoffOpportunity P.measure αl αh kbar θ₁ c →
            θ₁ < 1 - θt ∧ 1 - θt ≤ θ₂)) ∧
        (∀ θ ∈ Set.Ioo (0:ℝ) 1, θ ≠ 1 - θt →
          ContinuousAt (fun θs => sellerPayoffMaterial P.measure αl αh kbar θs c) θ ∧
          ContinuousAt (fun θs => sellerPayoffOpportunity P.measure αl αh kbar θs c) θ)) ∧
      -- (ii) and (iii): in c, at each fixed θs; cl, ch are Corollary 1 (ii)'s thresholds
      (∀ θs ∈ Set.Ioo (0:ℝ) 1, ∃ cl ch : ℝ,
        cl ≤ priorMean P.measure ∧ priorMean P.measure ≤ ch ∧
        (∀ c ∈ P.costDomain,
          optimalInfo P.measure αl αh kbar (1 - θs) c = αh ↔ cl < c ∧ c < ch) ∧
        (∀ c₁ ∈ P.costDomain, ∀ c₂ ∈ P.costDomain, c₁ < c₂ →
          (sellerPayoffMaterial P.measure αl αh kbar θs c₁ <
              sellerPayoffMaterial P.measure αl αh kbar θs c₂ →
            c₁ ≤ cl ∧ cl < c₂) ∧
          (sellerPayoffOpportunity P.measure αl αh kbar θs c₂ <
              sellerPayoffOpportunity P.measure αl αh kbar θs c₁ →
            c₁ < ch ∧ ch ≤ c₂)) ∧
        (∀ c ∈ P.costDomain, c ≠ cl → c ≠ ch →
          ContinuousAt (fun x => sellerPayoffMaterial P.measure αl αh kbar θs x) c ∧
          ContinuousAt (fun x => sellerPayoffOpportunity P.measure αl αh kbar θs x) c))) ∧
    -- "may" in (i): a fall of both payoffs in θs
    (∃ αl αh kbar c θ₁ θ₂ : ℝ, 0 < αl ∧ αl < αh ∧ αh < 1 ∧ 0 < kbar ∧ c ∈ P.costDomain ∧
      0 < θ₁ ∧ θ₁ < θ₂ ∧ θ₂ < 1 ∧
      sellerPayoffMaterial P.measure αl αh kbar θ₂ c <
        sellerPayoffMaterial P.measure αl αh kbar θ₁ c ∧
      sellerPayoffOpportunity P.measure αl αh kbar θ₂ c <
        sellerPayoffOpportunity P.measure αl αh kbar θ₁ c) ∧
    -- "may" in (ii): a rise of U_s* in c
    (∃ αl αh kbar θs c₁ c₂ : ℝ, 0 < αl ∧ αl < αh ∧ αh < 1 ∧ 0 < kbar ∧ 0 < θs ∧ θs < 1 ∧
      c₁ ∈ P.costDomain ∧ c₂ ∈ P.costDomain ∧ c₁ < c₂ ∧
      sellerPayoffMaterial P.measure αl αh kbar θs c₁ <
        sellerPayoffMaterial P.measure αl αh kbar θs c₂) ∧
    -- "may" in (iii): a fall of V_s* in c
    (∃ αl αh kbar θs c₁ c₂ : ℝ, 0 < αl ∧ αl < αh ∧ αh < 1 ∧ 0 < kbar ∧ 0 < θs ∧ θs < 1 ∧
      c₁ ∈ P.costDomain ∧ c₂ ∈ P.costDomain ∧ c₁ < c₂ ∧
      sellerPayoffOpportunity P.measure αl αh kbar θs c₂ <
        sellerPayoffOpportunity P.measure αl αh kbar θs c₁) := by
  cases P with
  | uniform =>
    obtain ⟨hP, hac, h0, h1⟩ := p2r_unif_facts
    obtain ⟨hI, hm, hm1⟩ := p2r_facts01 _ hac h0 h1
    refine p2r_main ((volume : Measure ℝ).restrict (Set.Icc 0 1)) hI hac (Set.Ioo 0 1) (fun x hx => hx.1) hm
      (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hm1⟩) ((1 + priorMean ((volume : Measure ℝ).restrict (Set.Icc 0 1))) / 2) (by linarith)
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) ?_
    rw [p2r_R_bdd _ h1]
    exact div_nonneg (integral_nonneg fun _ => le_max_right _ _) (by norm_num)
  | exponential uhat huhat =>
    obtain ⟨hP, hac, h0, hI⟩ := p2r_exp_facts uhat huhat
    have hm : 0 < priorMean (ProbabilityTheory.expMeasure (1 / uhat)) :=
      p2r_int_pos _ hac (fun u => u) h0 hI 0 (fun u hu => hu)
    obtain ⟨R, hmR, hR⟩ := p2r_R_unb _ hI hac
    exact p2r_main _ hI hac (Set.Ioi 0) (fun x hx => hx) hm (fun x hx => hx.1) R hmR
      (fun x hx => lt_of_lt_of_le hm hx.1) hR
  | logistic uhat huhat =>
    obtain ⟨hP, hac, hI, hm⟩ := p2r_log_facts uhat huhat
    obtain ⟨R, hmR, hR⟩ := p2r_R_unb _ hI hac
    exact p2r_main _ hI hac (Set.Ioi 0) (fun x hx => hx) hm (fun x hx => hx.1) R hmR
      (fun x hx => lt_of_lt_of_le hm hx.1) hR
  | modPareto lam hlam =>
    obtain ⟨hP, hac, h0, h1⟩ := p2r_beta_facts lam hlam
    obtain ⟨hI, hm, hm1⟩ := p2r_facts01 _ hac h0 h1
    refine p2r_main (ProbabilityTheory.betaMeasure 1 lam) hI hac (Set.Ioo 0 1) (fun x hx => hx.1) hm
      (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hm1⟩) ((1 + priorMean (ProbabilityTheory.betaMeasure 1 lam)) / 2) (by linarith)
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) ?_
    rw [p2r_R_bdd _ h1]
    exact div_nonneg (integral_nonneg fun _ => le_max_right _ _) (by norm_num)
