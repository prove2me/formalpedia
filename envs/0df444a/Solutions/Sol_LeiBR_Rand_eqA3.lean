-- Prove2me | solution 1 for LeiBR.Rand.eqA3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T10:53:55.574078+00:00
-- url     : https://prove2.me/submissions/0d030339-89b4-4021-88a6-ee5b1c4aa1d3

import Theorems.Thm_LeiBR_Rand_eq9_contraction
import Theorems.Thm_LeiBR_Rand_prox_br_fixed_point
import Definitions.Def_LeiBR_Rand_SA
import Definitions.Def_LeiBR_Rand_Algorithm2
import Definitions.Def_LeiBR_Rand_Constants
open MeasureTheory ProbabilityTheory

namespace LeiBR2AuxA3

lemma mid_strong {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {X : Set E}
    (hX : Convex ℝ X) {g : E → ℝ} (hg : ConvexOn ℝ X g) {mu : ℝ} (hmu : 0 ≤ mu) {c u z : E}
    (hu : u ∈ X) (hz : z ∈ X)
    (hmin : IsMinOn (fun y => g y + mu / 2 * ‖y - c‖ ^ 2) X u) :
    mu / 4 * ‖z - u‖ ^ 2 ≤ (g z + mu / 2 * ‖z - c‖ ^ 2) - (g u + mu / 2 * ‖u - c‖ ^ 2) := by
  set m : E := (1/2 : ℝ) • u + (1/2 : ℝ) • z with hm
  have hmX : m ∈ X := hX hu hz (by norm_num) (by norm_num) (by norm_num)
  have hgm : g m ≤ (1/2 : ℝ) • g u + (1/2 : ℝ) • g z :=
    hg.2 hu hz (by norm_num) (by norm_num) (by norm_num)
  have hmin' := hmin hmX
  simp only [Set.mem_ofPred_eq] at hmin'
  have hpar := parallelogram_law_with_norm ℝ (u - c) (z - c)
  have h1 : u - c + (z - c) = (2:ℝ) • (m - c) := by
    rw [hm]; module
  have h2 : u - c - (z - c) = -(z - u) := by abel
  rw [h1, h2, norm_neg, norm_smul] at hpar
  simp only [smul_eq_mul] at hgm
  have : ‖(2:ℝ)‖ = 2 := by norm_num
  rw [this] at hpar
  nlinarith [sq_nonneg ‖z - u‖]

open LeiBR.Rand in
lemma feas_update {N : ℕ} {n : Fin N → ℕ} (G : Game N n) {y : LeiBR.Sync.Profile n}
    (hy : G.Feasible y) (i : Fin N) {z : LeiBR.Sync.Strat n i} (hz : z ∈ G.X i) :
    G.Feasible (Function.update y i z) := by
  intro j
  by_cases h : j = i
  · subst h; simpa using hz
  · rw [Function.update_of_ne h]; exact hy j

open LeiBR.Rand in
lemma xhat_contOn {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    {μξ : Measure (EuclideanSpace ℝ (Fin d))}
    {ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ}
    {gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i} {M : Fin N → ℝ}
    (hA1 : Assumption1 G μξ ψ gψ M) {mu : ℝ} (hmu : 0 < mu)
    {xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n} (hxhat : IsProxBR G mu xhat) (i : Fin N) :
    ContinuousOn (fun y => xhat y i) {y | G.Feasible y} := by
  set S : Set (LeiBR.Sync.Profile n) := {y | G.Feasible y} with hSdef
  have hS : S = Set.univ.pi G.X := by
    ext y; simp [hSdef, Game.Feasible]
  have hSc : IsCompact S := hS ▸ isCompact_univ_pi hA1.compact
  obtain ⟨U, -, hSU, hsm⟩ := hA1.smooth
  have hfc : ContinuousOn (G.f i) S := ((hsm i).continuousOn).mono hSU
  let h : LeiBR.Sync.Profile n × LeiBR.Sync.Strat n i → ℝ :=
    fun p => G.f i (Function.update p.1 i p.2) + mu / 2 * ‖p.2 - p.1 i‖ ^ 2
  have hK : IsCompact (S ×ˢ G.X i) := hSc.prod (hA1.compact i)
  have hcont : ContinuousOn h (S ×ˢ G.X i) := by
    refine ContinuousOn.add ?_ (Continuous.continuousOn (by fun_prop))
    refine hfc.comp (Continuous.update continuous_fst i continuous_snd).continuousOn ?_
    intro p hp
    exact feas_update G hp.1 i hp.2
  have huc := (Metric.uniformContinuousOn_iff).1 (hK.uniformContinuousOn_of_continuous hcont)
  refine Metric.continuousOn_iff.2 fun y hy ε hε => ?_
  obtain ⟨δ, hδ, hδh⟩ := huc (mu * ε ^ 2 / 4) (by positivity)
  refine ⟨δ, hδ, fun y' hy' hd => ?_⟩
  have hu := (hxhat y hy i).1
  have hu' := (hxhat y' hy' i).1
  have hcv : ∀ y0, y0 ∈ S → ConvexOn ℝ (G.X i) (fun z => G.f i (Function.update y0 i z)) := by
    intro y0 hy0
    obtain ⟨V, -, hXV, hc⟩ := hA1.convexOn i y0 hy0
    exact hc.subset hXV (hA1.convex i)
  have sc1 := mid_strong (hA1.convex i) (hcv y hy) hmu.le hu hu' (hxhat y hy i).2
  have sc2 := mid_strong (hA1.convex i) (hcv y' hy') hmu.le hu' hu (hxhat y' hy' i).2
  have d1 := hδh (y, xhat y' i) ⟨hy, hu'⟩ (y', xhat y' i) ⟨hy', hu'⟩
    (by rw [Prod.dist_eq]; simp; rw [dist_comm]; exact hd)
  have d2 := hδh (y', xhat y i) ⟨hy', hu⟩ (y, xhat y i) ⟨hy, hu⟩
    (by rw [Prod.dist_eq]; simp; exact hd)
  simp only [h, Real.dist_eq] at d1 d2
  rw [abs_lt] at d1 d2
  rw [dist_eq_norm]
  rw [norm_sub_rev (xhat y i) (xhat y' i)] at sc2
  have hsq : ‖xhat y' i - xhat y i‖ ^ 2 < ε ^ 2 := by
    have : mu * ‖xhat y' i - xhat y i‖ ^ 2 < mu * ε ^ 2 := by nlinarith
    exact lt_of_mul_lt_mul_left this hmu.le
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq


end LeiBR2AuxA3

open LeiBR.Rand LeiBR2AuxA3

theorem solution {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 G μξ ψ gψ M) (mu : ℝ) (hmu : 0 < mu)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : IsProxBR G mu xhat)
    (hA2 : Assumption2 G mu) (xstar : LeiBR.Sync.Profile n) (hNE : G.IsNE xstar)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) (k : ℕ) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1)
    (xk : Ω → LeiBR.Sync.Profile n) (hxk_meas : StronglyMeasurable[F k] xk)
    (hxk_feas : ∀ ω, G.Feasible (xk ω))
    (χ : Fin N → Ω → ℕ) (hχ1 : ∀ i ω, χ i ω ≤ 1) (hχ_meas : ∀ i, Measurable (χ i))
    (hχ_prob : ∀ i, P {ω | χ i ω = 1} = ENNReal.ofReal (p i))
    (hχ_indep : ∀ i, Indep (MeasurableSpace.comap (χ i) inferInstance) (F k) P) :
    P[fun ω => wnorm p ((fun i => xk ω i + (χ i ω : ℝ) • (xhat (xk ω) i - xk ω i)) - xstar) ^ 2 | F k]
      ≤ᵐ[P] fun ω => wnorm p (xk ω - xstar) ^ 2
        - (1 - contrFactor G mu ^ 2) * blockNorm (xk ω - xstar) ^ 2 := by
  have hxkm : Measurable[F k] xk := hxk_meas.measurable
  have hxs : G.Feasible xstar := hNE.1
  have hdiam : ∀ i (a b : LeiBR.Sync.Strat n i), a ∈ G.X i → b ∈ G.X i →
      ‖a - b‖ ^ 2 ≤ Metric.diam (G.X i) ^ 2 := by
    intro i a b ha hb
    have := Metric.dist_le_diam_of_mem (hA1.compact i).isBounded ha hb
    rw [dist_eq_norm] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hAm : ∀ i, Measurable[F k] (fun ω => ‖xk ω i - xstar i‖ ^ 2) := fun i =>
    (show Measurable fun y : LeiBR.Sync.Profile n => ‖y i - xstar i‖ ^ 2 by fun_prop).comp hxkm
  have hBm : ∀ i, Measurable[F k] (fun ω => ‖xhat (xk ω) i - xstar i‖ ^ 2) := by
    intro i
    have hc := (xhat_contOn G hA1 hmu hxhat i).domRestrict
    have hm : Measurable[F k] fun ω => (⟨xk ω, hxk_feas ω⟩ : {y | G.Feasible y}) :=
      hxkm.subtype_mk
    have hc2 : Continuous fun s : {y | G.Feasible y} => ‖xhat s.1 i - xstar i‖ ^ 2 :=
      ((hc.sub continuous_const).norm.pow 2)
    have h3 := @Measurable.comp Ω {y | G.Feasible y} ℝ (F k) _ _ _ _ hc2.measurable hm
    exact h3
  set D : Fin N → Ω → ℝ := fun i ω =>
    (‖xhat (xk ω) i - xstar i‖ ^ 2 - ‖xk ω i - xstar i‖ ^ 2) / p i with hD
  have hDm : ∀ i, Measurable[F k] (D i) := fun i => ((hBm i).sub (hAm i)).div_const _
  have hDb : ∀ i ω, |D i ω| ≤ Metric.diam (G.X i) ^ 2 / p i := by
    intro i ω
    have h1 := hdiam i _ _ (hxhat (xk ω) (hxk_feas ω) i).1 (hxs i)
    have h2 := hdiam i _ _ (hxk_feas ω i) (hxs i)
    simp only [hD]
    rw [abs_div, abs_of_pos (hp i)]
    refine div_le_div_of_nonneg_right ?_ (hp i).le
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg ‖xhat (xk ω) i - xstar i‖, sq_nonneg ‖xk ω i - xstar i‖]
  set c : Fin N → Ω → ℝ := fun i ω => (χ i ω : ℝ) with hc
  have hcm : ∀ i, Measurable (c i) := fun i => measurable_from_nat.comp (hχ_meas i)
  have hcb : ∀ i ω, |c i ω| ≤ 1 := fun i ω => by
    simp only [hc]; rw [abs_of_nonneg (by positivity)]; exact_mod_cast hχ1 i ω
  have hcint : ∀ i, Integrable (c i) P := fun i =>
    Integrable.of_bound (hcm i).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hcb i ω)
  have hcval : ∀ i, ∫ ω, c i ω ∂P = p i := by
    intro i
    have hms : MeasurableSet {ω | χ i ω = 1} := (hχ_meas i) (measurableSet_singleton 1)
    have : c i = {ω | χ i ω = 1}.indicator 1 := by
      funext ω
      have := hχ1 i ω
      by_cases h : χ i ω = 1
      · simp [hc, Set.indicator, h]
      · have h0 : χ i ω = 0 := by omega
        simp [hc, Set.indicator, h0]
    rw [this, integral_indicator_one hms, Measure.real, hχ_prob i, ENNReal.toReal_ofReal (hp i).le]
  set g : Fin N → Ω → ℝ := fun i ω => D i ω * c i ω with hg
  have hgint : ∀ i, Integrable (g i) P := by
    intro i
    refine Integrable.of_bound (((hDm i).mono (F.le k) le_rfl).mul (hcm i)).aestronglyMeasurable
      (Metric.diam (G.X i) ^ 2 / p i) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    simp only [hg, abs_mul]
    calc |D i ω| * |c i ω| ≤ Metric.diam (G.X i) ^ 2 / p i * 1 :=
          mul_le_mul (hDb i ω) (hcb i ω) (abs_nonneg _) (by have := hp i; positivity)
      _ = _ := mul_one _
  set f1 : Ω → ℝ := fun ω => ∑ i, ‖xk ω i - xstar i‖ ^ 2 / p i with hf1
  have hf1m : Measurable[F k] f1 := Finset.measurable_sum _ fun i _ => (hAm i).div_const _
  have hf1int : Integrable f1 P := by
    refine Integrable.of_bound (hf1m.mono (F.le k) le_rfl).aestronglyMeasurable
      (∑ i, Metric.diam (G.X i) ^ 2 / p i) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hp i).le)]
    exact Finset.sum_le_sum fun i _ =>
      div_le_div_of_nonneg_right (hdiam i _ _ (hxk_feas ω i) (hxs i)) (hp i).le
  have hfun : (fun ω => wnorm p ((fun i => xk ω i + (χ i ω : ℝ) • (xhat (xk ω) i - xk ω i)) - xstar) ^ 2)
      = f1 + ∑ i, g i := by
    funext ω
    rw [Pi.add_apply, Finset.sum_apply]
    unfold wnorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hp i).le)]
    simp only [hf1, hg, hD, hc]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hχ1 i ω
    rw [Pi.sub_apply]
    rcases (show χ i ω = 0 ∨ χ i ω = 1 by omega) with h | h
    · simp [h]
    · simp only [h, Nat.cast_one, one_smul]
      rw [show xk ω i + (xhat (xk ω) i - xk ω i) - xstar i = xhat (xk ω) i - xstar i by abel]
      field_simp
      ring
  rw [hfun]
  have e1 := condExp_add hf1int (integrable_finsetSum' Finset.univ fun i _ => hgint i) (F k)
  have e2 := condExp_finsetSum (μ := P) (s := Finset.univ) (fun i _ => hgint i) (F k)
  have e3 : ∀ i, ∀ᵐ ω ∂P, P[g i | F k] ω = D i ω * p i := by
    intro i
    have h1 := condExp_mul_of_stronglyMeasurable_left (m := F k) (μ := P) (f := D i) (g := c i)
      (hDm i).stronglyMeasurable (hgint i) (hcint i)
    have hcsm : StronglyMeasurable[MeasurableSpace.comap (χ i) inferInstance] (c i) :=
      (measurable_from_nat.comp (comap_measurable (χ i))).stronglyMeasurable
    have h2 := condExp_indep_eq (μ := P) (hχ_meas i).comap_le (F.le k) hcsm (hχ_indep i)
    filter_upwards [h1, h2] with ω h h'
    have : g i = D i * c i := rfl
    rw [this, h, Pi.mul_apply, h', hcval i]
  filter_upwards [e1, e2, ae_all_iff.2 e3] with ω h1 h2 h3
  rw [h1, Pi.add_apply, condExp_of_stronglyMeasurable (F.le k) hf1m.stronglyMeasurable hf1int, h2,
    Finset.sum_apply]
  rw [Finset.sum_congr rfl fun i _ => h3 i]
  -- pointwise algebra
  have hDp : ∀ i, D i ω * p i = ‖xhat (xk ω) i - xstar i‖ ^ 2 - ‖xk ω i - xstar i‖ ^ 2 := by
    intro i; simp only [hD]; field_simp [(hp i).ne']
  rw [Finset.sum_congr rfl fun i _ => hDp i, Finset.sum_sub_distrib]
  have hw : wnorm p (xk ω - xstar) ^ 2 = f1 ω := by
    unfold wnorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hp i).le)]
    rfl
  have hb1 : blockNorm (xk ω - xstar) ^ 2 = ∑ i, ‖xk ω i - xstar i‖ ^ 2 := by
    unfold blockNorm; rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]; rfl
  have hfix : xhat xstar = xstar := funext fun i =>
    prox_br_fixed_point G μξ ψ gψ M hA1 mu hmu xhat hxhat xstar hNE i
  have h9 := eq9_contraction G μξ ψ gψ M hA1 mu hmu xhat hxhat hA2 xstar (xk ω) hxs (hxk_feas ω)
  rw [hfix] at h9
  have hb2 : blockNorm (xhat (xk ω) - xstar) ^ 2 = ∑ i, ‖xhat (xk ω) i - xstar i‖ ^ 2 := by
    unfold blockNorm; rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]; rfl
  have hbn0 : 0 ≤ blockNorm (xhat (xk ω) - xstar) := Real.sqrt_nonneg _
  have hsq : blockNorm (xhat (xk ω) - xstar) ^ 2 ≤
      contrFactor G mu ^ 2 * blockNorm (xk ω - xstar) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hbn0 h9 2
  rw [hw]
  nlinarith
