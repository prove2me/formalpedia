-- Prove2me | solution 1 for LeiBR.Rand.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:08:34.029149+00:00
-- url     : https://prove2.me/submissions/c0a49fae-d038-4996-b1fa-bacbd24d8d15

import Theorems.Thm_LeiBR_Rand_eqB1
import Theorems.Thm_LeiBR_Rand_lemma_2
open MeasureTheory ProbabilityTheory

namespace LeiBR2AuxL5

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


section coin
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (F : Filtration ℕ mΩ) (c : ℕ → Ω → ℕ) (pp : ℝ)
  (hle : ∀ k ω, c k ω ≤ 1) (hmeas : ∀ k, Measurable[F (k + 1)] (c k))
  (hprob : ∀ k, P {ω | c k ω = 1} = ENNReal.ofReal pp) (hp0 : 0 ≤ pp)
  (hind : ∀ k, Indep (MeasurableSpace.comap (c k) inferInstance) (F k) P)
include hle hmeas hprob hp0 hind

lemma coin_cast (k : ℕ) (ω : Ω) : (c k ω : ℝ) = {ω | c k ω = 1}.indicator 1 ω := by
  have := hle k ω
  by_cases h : c k ω = 1
  · simp [Set.indicator, h]
  · have h0 : c k ω = 0 := by omega
    simp [Set.indicator, h0]

lemma coin_integral (k : ℕ) : ∫ ω, (c k ω : ℝ) ∂P = pp := by
  have hm : MeasurableSet {ω | c k ω = 1} :=
    (hmeas k).mono (F.le (k + 1)) le_rfl (measurableSet_singleton 1)
  rw [show (fun ω => (c k ω : ℝ)) = {ω | c k ω = 1}.indicator 1 from
    funext (coin_cast P F c pp hle hmeas hprob hp0 hind k)]
  rw [integral_indicator_one hm, Measure.real, hprob k, ENNReal.toReal_ofReal hp0]

lemma coin_mul (k : ℕ) (Y : Ω → ℝ) (hY : Measurable[F k] Y) :
    ∫ ω, Y ω * (c k ω : ℝ) ∂P = (∫ ω, Y ω ∂P) * pp := by
  have hind' : IndepFun Y (fun ω => (c k ω : ℝ)) P := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left (hind k).symm hY.comap_le) ?_
    exact (measurable_from_nat.comp (comap_measurable (c k))).comap_le
  have := hind'.integral_mul_eq_mul_integral
    (hY.mono (F.le k) le_rfl).aestronglyMeasurable
    ((measurable_from_nat.comp ((hmeas k).mono (F.le (k + 1)) le_rfl))).aestronglyMeasurable
  simp only [Pi.mul_apply] at this
  rw [this, coin_integral P F c pp hle hmeas hprob hp0 hind k]

lemma beta_meas (k : ℕ) : Measurable[F k] (fun ω => ∑ l ∈ Finset.range k, c l ω) := by
  refine Finset.measurable_sum _ fun l hl => ?_
  have : l + 1 ≤ k := Finset.mem_range.1 hl
  exact (hmeas l).mono (F.mono this) le_rfl

lemma beta_le (k : ℕ) (ω : Ω) : ∑ l ∈ Finset.range k, c l ω ≤ k := by
  calc ∑ l ∈ Finset.range k, c l ω ≤ ∑ _l ∈ Finset.range k, 1 :=
        Finset.sum_le_sum fun l _ => hle l ω
    _ = k := by simp

lemma rpow_beta (r : ℝ) (hr : 0 ≤ r) (k : ℕ) :
    ∫ ω, r ^ (∑ l ∈ Finset.range k, c l ω) ∂P = (pp * (r - 1) + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpt : ∀ ω, r ^ (∑ l ∈ Finset.range (k + 1), c l ω) =
        r ^ (∑ l ∈ Finset.range k, c l ω) + (r - 1) * (r ^ (∑ l ∈ Finset.range k, c l ω) * (c k ω : ℝ)) := by
      intro ω
      rw [Finset.sum_range_succ, pow_add]
      have := hle k ω
      rcases (show c k ω = 0 ∨ c k ω = 1 by omega) with h | h <;> simp [h] <;> ring
    simp_rw [hpt]
    have hYm : Measurable[F k] (fun ω => r ^ (∑ l ∈ Finset.range k, c l ω)) :=
      measurable_from_nat.comp (beta_meas P F c pp hle hmeas hprob hp0 hind k)
    have hbd : ∀ ω, |r ^ (∑ l ∈ Finset.range k, c l ω)| ≤ (r + 1) ^ k := by
      intro ω
      rw [abs_of_nonneg (by positivity)]
      exact (pow_le_pow_left₀ hr (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) (beta_le P F c pp hle hmeas hprob hp0 hind k ω))
    have hYi : Integrable (fun ω => r ^ (∑ l ∈ Finset.range k, c l ω)) P :=
      Integrable.of_bound (hYm.mono (F.le k) le_rfl).aestronglyMeasurable ((r + 1) ^ k)
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hbd ω)
    have hYci : Integrable (fun ω => r ^ (∑ l ∈ Finset.range k, c l ω) * (c k ω : ℝ)) P := by
      refine Integrable.of_bound ((hYm.mono (F.le k) le_rfl).mul
        (measurable_from_nat.comp ((hmeas k).mono (F.le (k + 1)) le_rfl))).aestronglyMeasurable ((r + 1) ^ k)
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |(c k ω : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg (by positivity)]; exact_mod_cast hle k ω
      calc |r ^ (∑ l ∈ Finset.range k, c l ω)| * |(c k ω : ℝ)| ≤ (r + 1) ^ k * 1 :=
            mul_le_mul (hbd ω) h1 (abs_nonneg _) (by positivity)
        _ = (r + 1) ^ k := mul_one _
    rw [integral_add hYi (hYci.const_mul _), integral_const_mul,
      coin_mul P F c pp hle hmeas hprob hp0 hind k _ hYm, ih, pow_succ]
    ring

end coin


lemma amgm (z y : ℝ) (hz : 0 ≤ z) (hy : 0 < y) : Real.sqrt z ≤ (z / y + y) / 2 := by
  have hs := Real.sq_sqrt hz
  have h0 := Real.sqrt_nonneg z
  rw [div_add' _ _ _ hy.ne', div_div, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt z - y)]

lemma sqrt_cond {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) (k : ℕ) (Z X : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hZm : Measurable Z) (CZ : ℝ) (hZb : ∀ ω, Z ω ≤ CZ)
    (hX0 : ∀ ω, 0 ≤ X ω) (hXm : Measurable[F k] X) (CX : ℝ) (hXb : ∀ ω, X ω ≤ CX)
    (hcond : P[Z | F k] ≤ᵐ[P] fun ω => c ^ 2 * X ω ^ 2) :
    ∫ ω, Real.sqrt (Z ω) ∂P ≤ c * ∫ ω, X ω ∂P := by
  have hXm' : Measurable X := hXm.mono (F.le k) le_rfl
  have hXi : Integrable X P := Integrable.of_bound hXm'.aestronglyMeasurable CX
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]; exact hXb ω)
  have hZi : Integrable Z P := Integrable.of_bound hZm.aestronglyMeasurable CZ
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hZ0 ω)]; exact hZb ω)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set Y : Ω → ℝ := fun ω => c * X ω + δ with hY
  have hYpos : ∀ ω, 0 < Y ω := fun ω => by have := hX0 ω; simp only [hY]; positivity
  set W : Ω → ℝ := fun ω => 1 / Y ω with hW
  have hWm : Measurable[F k] W := ((hXm.const_mul c).add_const δ).const_div 1
  have hWb : ∀ ω, ‖W ω‖ ≤ 1 / δ := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_pos (by simp only [hW]; exact one_div_pos.2 (hYpos ω))]
    have := hX0 ω
    exact one_div_le_one_div_of_le hδ (by simp only [hY]; nlinarith)
  have hWZi : Integrable (fun ω => W ω * Z ω) P :=
    hZi.bdd_mul (hWm.mono (F.le k) le_rfl).aestronglyMeasurable (ae_of_all _ hWb)
  have hpt : ∀ ω, Real.sqrt (Z ω) ≤ (W ω * Z ω + Y ω) / 2 := by
    intro ω
    have := amgm (Z ω) (Y ω) (hZ0 ω) (hYpos ω)
    simp only [hW]; rw [one_div_mul_eq_div]; exact this
  have hYi : Integrable Y P := (hXi.const_mul c).add (integrable_const δ)
  have h1 : ∫ ω, Real.sqrt (Z ω) ∂P ≤ ∫ ω, (W ω * Z ω + Y ω) / 2 ∂P :=
    integral_mono_of_nonneg (ae_of_all _ fun ω => Real.sqrt_nonneg _)
      ((hWZi.add hYi).div_const 2) (ae_of_all _ hpt)
  -- tower property
  have h2 : ∫ ω, W ω * Z ω ∂P = ∫ ω, W ω * (P[Z | F k]) ω ∂P := by
    rw [← integral_condExp (F.le k) (f := fun ω => W ω * Z ω)]
    refine integral_congr_ae ?_
    have := condExp_mul_of_stronglyMeasurable_left (m := F k) (μ := P) (f := W) (g := Z)
      hWm.stronglyMeasurable hWZi hZi
    filter_upwards [this] with ω h
    exact h
  have h3 : ∫ ω, W ω * (P[Z | F k]) ω ∂P ≤ ∫ ω, c * X ω ∂P := by
    refine integral_mono_ae ((integrable_condExp).bdd_mul (hWm.mono (F.le k) le_rfl).aestronglyMeasurable
      (ae_of_all _ hWb)) (hXi.const_mul c) ?_
    filter_upwards [hcond] with ω h
    have hW0 : 0 ≤ W ω := by simp only [hW]; exact (one_div_pos.2 (hYpos ω)).le
    calc W ω * (P[Z | F k]) ω ≤ W ω * (c ^ 2 * X ω ^ 2) := mul_le_mul_of_nonneg_left h hW0
      _ ≤ c * X ω := by
        simp only [hW, hY]
        have := hX0 ω
        rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg hc this]
  rw [integral_div, integral_add hWZi hYi, h2] at h1
  have h4 : ∫ ω, Y ω ∂P = c * ∫ ω, X ω ∂P + δ := by
    simp only [hY]
    rw [integral_add (hXi.const_mul c) (integrable_const δ), integral_const_mul]
    simp
  rw [h4] at h1
  rw [integral_const_mul] at h3
  linarith

lemma int_le_sqrt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX0 : ∀ ω, 0 ≤ X ω) (hXm : Measurable X) (CX : ℝ) (hXb : ∀ ω, X ω ≤ CX) :
    ∫ ω, X ω ∂P ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂P) := by
  have hXi : Integrable X P := Integrable.of_bound hXm.aestronglyMeasurable CX
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]; exact hXb ω)
  have hX2i : Integrable (fun ω => X ω ^ 2) P := Integrable.of_bound (hXm.pow_const 2).aestronglyMeasurable
    (CX ^ 2) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (hX0 ω) (hXb ω) 2)
  set S := ∫ ω, X ω ^ 2 ∂P with hS
  have hS0 : 0 ≤ S := integral_nonneg fun ω => sq_nonneg _
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set y := Real.sqrt S + δ with hy
  have hy0 : 0 < y := by positivity
  have hpt : ∀ ω, X ω ≤ (X ω ^ 2 / y + y) / 2 := by
    intro ω
    have := amgm (X ω ^ 2) y (sq_nonneg _) hy0
    rwa [Real.sqrt_sq (hX0 ω)] at this
  have h1 : ∫ ω, X ω ∂P ≤ ∫ ω, (X ω ^ 2 / y + y) / 2 ∂P :=
    integral_mono hXi (((hX2i.div_const y).add (integrable_const y)).div_const 2) hpt
  rw [integral_div, integral_add (hX2i.div_const y) (integrable_const y), integral_div] at h1
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
  have hSy : S / y ≤ Real.sqrt S := by
    rw [div_le_iff₀ hy0]
    have := Real.sq_sqrt hS0
    have := Real.sqrt_nonneg S
    nlinarith
  rw [← hS] at h1
  linarith


lemma wnorm_tri {N : ℕ} {n : Fin N → ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 < p i)
    (a b : LeiBR.Sync.Profile n) : LeiBR.Rand.wnorm p (a + b) ≤ LeiBR.Rand.wnorm p a + LeiBR.Rand.wnorm p b := by
  let ua : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun i => ‖a i‖ / Real.sqrt (p i))
  let ub : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun i => ‖b i‖ / Real.sqrt (p i))
  have hw : ∀ v : LeiBR.Sync.Profile n,
      LeiBR.Rand.wnorm p v = ‖(WithLp.toLp 2 (fun i => ‖v i‖ / Real.sqrt (p i)) : EuclideanSpace ℝ (Fin N))‖ := by
    intro v
    rw [EuclideanSpace.norm_eq]
    unfold LeiBR.Rand.wnorm
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Real.norm_eq_abs, sq_abs]
    rw [div_pow, Real.sq_sqrt (hp i).le]
  have hle : LeiBR.Rand.wnorm p (a + b) ≤ ‖ua + ub‖ := by
    rw [EuclideanSpace.norm_eq]
    unfold LeiBR.Rand.wnorm
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    simp only [ua, ub, WithLp.ofLp_add, Pi.add_apply, Real.norm_eq_abs, sq_abs]
    have hs := Real.sqrt_pos.2 (hp i)
    rw [← add_div, div_pow, Real.sq_sqrt (hp i).le]
    refine div_le_div_of_nonneg_right ?_ (hp i).le
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
  rw [hw a, hw b]
  exact hle.trans (norm_add_le ua ub)

lemma meas_sqdist {Ω : Type*} [MeasurableSpace Ω] {m' : ℕ} (f g : Ω → EuclideanSpace ℝ (Fin m'))
    (hf : Measurable f) (hg : Measurable g) : Measurable fun ω => ‖f ω - g ω‖ ^ 2 :=
  (hf.sub hg).norm.pow_const 2

end LeiBR2AuxL5

open LeiBR.Rand LeiBR2AuxL5

theorem solution {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 G μξ ψ gψ M) (mu : ℝ) (hmu : 0 < mu)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : IsProxBR G mu xhat)
    (hA2 : Assumption2 G mu) (xstar : LeiBR.Sync.Profile n) (hNE : G.IsNE xstar) (hN : 0 < N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (p : Fin N → ℝ)
    (χ : Fin N → ℕ → Ω → ℕ) (w : ∀ i, ℕ → Ω → LeiBR.Sync.Strat n i) (x0 : LeiBR.Sync.Profile n)
    (x : ℕ → Ω → LeiBR.Sync.Profile n) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (C : ℝ) (hC : ∀ i, ‖x0 i - xstar i‖ ≤ C)
    (hrun : IsAlg2Run G xhat P F p χ w (fun i k ω => η ^ (beta χ i k ω + 1)) x0 x)
    (q : ℝ) (hq : ctil p (contrFactor G mu) η < q) (hq1 : q < 1) (k : ℕ) :
    ∫ ω, wnorm p (x k ω - xstar) ∂P ≤
      Real.sqrt N * (Ctil p C + Dtil p (contrFactor G mu) η q) * q ^ k := by
  have hp0 := hrun.p_pos
  have hp1 := hrun.p_le_one
  have i0 : Fin N := ⟨0, hN⟩
  haveI : Nonempty (Fin N) := ⟨i0⟩
  have hpmin_le : ∀ i, pmin p ≤ p i := fun i => ciInf_le (Finite.bddBelow_range p) i
  obtain ⟨i1, hi1⟩ := exists_eq_ciInf_of_finite (f := p)
  have hpmin0 : 0 < pmin p := by
    have : pmin p = p i1 := by unfold pmin; rw [hi1]
    rw [this]; exact hp0 i1
  have hpmin1 : pmin p ≤ 1 := (hpmin_le i0).trans (hp1 i0)
  set a := contrFactor G mu with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have ha1 : a < 1 := hA2
  have hat2 : 0 ≤ 1 - pmin p * (1 - a ^ 2) := by
    have h1 : pmin p * (1 - a ^ 2) ≤ 1 * (1 - a ^ 2) :=
      mul_le_mul_of_nonneg_right hpmin1 (by nlinarith)
    nlinarith
  have hat_sq : atil p a ^ 2 = 1 - pmin p * (1 - a ^ 2) := Real.sq_sqrt hat2
  have hat0 : 0 ≤ atil p a := Real.sqrt_nonneg _
  have hη2 : 0 < η ^ 2 := by positivity
  have hη21 : η ^ 2 < 1 := by nlinarith
  have het2 : 0 < 1 - pmin p * (1 - η ^ 2) := by
    have h1 : pmin p * (1 - η ^ 2) ≤ 1 * (1 - η ^ 2) :=
      mul_le_mul_of_nonneg_right hpmin1 (by linarith)
    nlinarith
  have het0 : 0 < etatil p η := Real.sqrt_pos.2 het2
  have het_sq : etatil p η ^ 2 = 1 - pmin p * (1 - η ^ 2) := Real.sq_sqrt het2.le
  set ct := ctil p a η with hctdef
  have hact : atil p a ≤ ct := le_max_left _ _
  have hetc : etatil p η ≤ ct := le_max_right _ _
  have hct0 : 0 < ct := het0.trans_le hetc
  have hq0 : 0 < q := hct0.trans hq
  -- iterates: feasibility and measurability
  have hfeas : ∀ k ω, G.Feasible (x k ω) := by
    intro k
    induction k with
    | zero => intro ω; rw [hrun.init ω]; exact hrun.x0_feas
    | succ k ih =>
      intro ω i
      rw [hrun.step k ω i]
      split_ifs
      · exact hrun.w_mem i k ω
      · exact ih ω i
  have hxm : ∀ k, Measurable[F k] (x k) := by
    intro k
    induction k with
    | zero =>
      have : x 0 = fun _ => x0 := funext hrun.init
      rw [this]; exact measurable_const
    | succ k ih =>
      have : x (k + 1) = fun ω i => if χ i k ω = 1 then w i k ω else x k ω i := by
        funext ω i; exact hrun.step k ω i
      rw [this]
      refine @measurable_pi_lambda Ω (Fin N) (fun i => LeiBR.Sync.Strat n i) (F (k + 1)) _ _ fun i => ?_
      have hs : MeasurableSet[F (k + 1)] {ω | χ i k ω = 1} :=
        (hrun.coin_meas i k) (measurableSet_singleton 1)
      exact @Measurable.ite Ω _ _ _ (F (k + 1)) _ (fun ω => χ i k ω = 1) _ hs
        (hrun.w_meas i k).measurable
        (((measurable_pi_apply i).comp ih).mono (F.mono k.le_succ) le_rfl)
  have hxm' : ∀ k, Measurable (x k) := fun k => (hxm k).mono (F.le k) le_rfl
  have hwm : ∀ i k, Measurable (w i k) := fun i k =>
    (hrun.w_meas i k).measurable.mono (F.le _) le_rfl
  have hxh : ∀ k i, Measurable[F k] (fun ω => xhat (x k ω) i) := by
    intro k i
    have hc := (xhat_contOn G hA1 hmu hxhat i).domRestrict
    have hm : Measurable[F k] fun ω : Ω => (⟨x k ω, hfeas k ω⟩ : {y | G.Feasible y}) :=
      (hxm k).subtype_mk
    exact @Measurable.comp Ω {y | G.Feasible y} _ (F k) _ _ _ _ hc.measurable hm
  have hxh' : ∀ k i, Measurable (fun ω => xhat (x k ω) i) := fun k i => (hxh k i).mono (F.le k) le_rfl
  have hxs : G.Feasible xstar := hNE.1
  have hdiam : ∀ i (a b : LeiBR.Sync.Strat n i), a ∈ G.X i → b ∈ G.X i →
      ‖a - b‖ ^ 2 ≤ Metric.diam (G.X i) ^ 2 := by
    intro i a b ha hb
    have := Metric.dist_le_diam_of_mem (hA1.compact i).isBounded ha hb
    rw [dist_eq_norm] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  set Wb := Real.sqrt (∑ i, Metric.diam (G.X i) ^ 2 / p i) with hWb
  have hwb : ∀ v : LeiBR.Sync.Profile n, (∀ i, ‖v i‖ ^ 2 ≤ Metric.diam (G.X i) ^ 2) → wnorm p v ≤ Wb :=
    fun v hv => Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
      div_le_div_of_nonneg_right (hv i) (hp0 i).le)
  have hwnc : Continuous fun v : LeiBR.Sync.Profile n => wnorm p v := by
    unfold wnorm; fun_prop
  have hwn0 : ∀ v : LeiBR.Sync.Profile n, 0 ≤ wnorm p v := fun v => Real.sqrt_nonneg _
  have hcm : ∀ i k, Measurable fun ω => (χ i k ω : ℝ) := fun i k =>
    measurable_from_nat.comp ((hrun.coin_meas i k).mono (F.le _) le_rfl)
  have hind : ∀ i k, Indep (MeasurableSpace.comap (χ i k) inferInstance) (F k) P :=
    fun i k => indep_of_indep_of_le_right (hrun.coin_indep i k) le_sup_left
  set u : ℕ → ℝ := fun k => ∫ ω, wnorm p (x k ω - xstar) ∂P with hu
  have hu0 : ∀ k, 0 ≤ u k := fun k => integral_nonneg fun ω => hwn0 _
  have hstep : ∀ k, u (k + 1) ≤ atil p a * u k + Real.sqrt N * η * etatil p η ^ k := by
    intro k
    set t : Ω → LeiBR.Sync.Profile n := fun ω i => x k ω i + (χ i k ω : ℝ) • (xhat (x k ω) i - x k ω i)
      with ht
    set e : Ω → LeiBR.Sync.Profile n := fun ω i => (χ i k ω : ℝ) • (w i k ω - xhat (x k ω) i) with he
    have h01 : ∀ i ω, χ i k ω = 0 ∨ χ i k ω = 1 := fun i ω => by
      have := hrun.coin_le_one i k ω; omega
    have htfeas : ∀ ω, G.Feasible (t ω) := by
      intro ω i
      rcases h01 i ω with h | h
      · simp only [ht, h, Nat.cast_zero, zero_smul, add_zero]; exact hfeas k ω i
      · simp only [ht, h, Nat.cast_one, one_smul, add_sub_cancel]
        exact (hxhat (x k ω) (hfeas k ω) i).1
    have hdec : ∀ ω, x (k + 1) ω - xstar = (t ω - xstar) + e ω := by
      intro ω; funext i
      simp only [Pi.add_apply, Pi.sub_apply, ht, he]
      rw [hrun.step k ω i]
      rcases h01 i ω with h | h
      · simp [h]
      · simp only [h, if_true, Nat.cast_one, one_smul]; abel
    have htri : ∀ ω, wnorm p (x (k + 1) ω - xstar) ≤ wnorm p (t ω - xstar) + wnorm p (e ω) := by
      intro ω; rw [hdec ω]; exact wnorm_tri p hp0 _ _
    have htm : Measurable t := by
      refine measurable_pi_lambda _ fun i => ?_
      exact ((measurable_pi_apply i).comp (hxm' k)).add
        ((hcm i k).smul ((hxh' k i).sub ((measurable_pi_apply i).comp (hxm' k))))
    have hem : Measurable e := by
      refine measurable_pi_lambda _ fun i => ?_
      exact (hcm i k).smul ((hwm i k).sub (hxh' k i))
    have hebd : ∀ ω i, ‖e ω i‖ ^ 2 ≤ Metric.diam (G.X i) ^ 2 := by
      intro ω i
      have hd := hdiam i _ _ (hrun.w_mem i k ω) (hxhat (x k ω) (hfeas k ω) i).1
      rcases h01 i ω with h | h
      · simp only [he, h, Nat.cast_zero, zero_smul]; simp; positivity
      · simp only [he, h, Nat.cast_one, one_smul]; exact hd
    have hm1 : Measurable fun ω => wnorm p (t ω - xstar) := hwnc.measurable.comp (htm.sub_const _)
    have hm2 : Measurable fun ω => wnorm p (e ω) := hwnc.measurable.comp hem
    have hb1 : ∀ ω, wnorm p (t ω - xstar) ≤ Wb := fun ω =>
      hwb _ fun i => hdiam i _ _ (htfeas ω i) (hxs i)
    have hb2 : ∀ ω, wnorm p (e ω) ≤ Wb := fun ω => hwb _ (hebd ω)
    have hi1 : Integrable (fun ω => wnorm p (t ω - xstar)) P :=
      Integrable.of_bound hm1.aestronglyMeasurable Wb (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hwn0 _)]; exact hb1 ω)
    have hi2 : Integrable (fun ω => wnorm p (e ω)) P :=
      Integrable.of_bound hm2.aestronglyMeasurable Wb (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hwn0 _)]; exact hb2 ω)
    have hI1 : u (k + 1) ≤ ∫ ω, wnorm p (t ω - xstar) ∂P + ∫ ω, wnorm p (e ω) ∂P := by
      rw [← integral_add hi1 hi2]
      exact integral_mono_of_nonneg (ae_of_all _ fun ω => hwn0 _) (hi1.add hi2) (ae_of_all _ htri)
    -- the exact-step part, by (B.1)
    have hB1 := eqB1 G μξ ψ gψ M hA1 mu hmu xhat hxhat hA2 xstar hNE P F k p hp0 hp1 (x k)
      (hxm k).stronglyMeasurable (hfeas k) (fun i => χ i k) (fun i ω => hrun.coin_le_one i k ω)
      (fun i => (hrun.coin_meas i k).mono (F.le _) le_rfl) (fun i => hrun.coin_prob i k)
      (fun i => hind i k)
    have hI2 : ∫ ω, wnorm p (t ω - xstar) ∂P ≤ atil p a * u k := by
      have hc := sqrt_cond P F k (fun ω => wnorm p (t ω - xstar) ^ 2) (fun ω => wnorm p (x k ω - xstar))
        (atil p a) hat0 (fun ω => sq_nonneg _) (hm1.pow_const 2) (Wb ^ 2)
        (fun ω => pow_le_pow_left₀ (hwn0 _) (hb1 ω) 2) (fun ω => hwn0 _)
        (hwnc.measurable.comp ((hxm k).sub_const _)) Wb
        (fun ω => hwb _ fun i => hdiam i _ _ (hfeas k ω i) (hxs i)) (by
          rw [hat_sq]; exact hB1)
      simpa only [Real.sqrt_sq (hwn0 _)] using hc
    -- the error part
    have hI3 : ∫ ω, wnorm p (e ω) ∂P ≤ Real.sqrt (∫ ω, wnorm p (e ω) ^ 2 ∂P) :=
      int_le_sqrt P _ (fun ω => hwn0 _) hm2 Wb hb2
    have hYm : ∀ i, Measurable fun ω => ‖w i k ω - xhat (x k ω) i‖ ^ 2 := fun i =>
      ((hwm i k).sub (hxh' k i)).norm.pow_const 2
    have hYb : ∀ i ω, ‖w i k ω - xhat (x k ω) i‖ ^ 2 ≤ Metric.diam (G.X i) ^ 2 := fun i ω =>
      hdiam i _ _ (hrun.w_mem i k ω) (hxhat (x k ω) (hfeas k ω) i).1
    have hYi : ∀ i, Integrable (fun ω => ‖w i k ω - xhat (x k ω) i‖ ^ 2) P := fun i =>
      Integrable.of_bound (hYm i).aestronglyMeasurable _ (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hYb i ω)
    have hesq : ∀ ω, wnorm p (e ω) ^ 2 =
        ∑ i, (χ i k ω : ℝ) * ‖w i k ω - xhat (x k ω) i‖ ^ 2 / p i := by
      intro ω
      unfold wnorm
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hp0 i).le)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases h01 i ω with h | h
      · simp [he, h]
      · simp [he, h]
    have hterm : ∀ i, ∫ ω, (χ i k ω : ℝ) * ‖w i k ω - xhat (x k ω) i‖ ^ 2 / p i ∂P
        ≤ η ^ 2 * etatil p η ^ (2 * k) := by
      intro i
      -- independence of the coin from (F_k, w_{i,k})
      have hYm' : Measurable[F k ⊔ MeasurableSpace.comap (w i k) inferInstance]
          (fun ω => ‖w i k ω - xhat (x k ω) i‖ ^ 2) :=
        @meas_sqdist Ω (F k ⊔ MeasurableSpace.comap (w i k) inferInstance) (n i) (w i k)
          (fun ω => xhat (x k ω) i) ((comap_measurable (w i k)).mono le_sup_right le_rfl)
          ((hxh k i).mono le_sup_left le_rfl)
      have hindep : IndepFun (fun ω => ‖w i k ω - xhat (x k ω) i‖ ^ 2) (fun ω => (χ i k ω : ℝ)) P := by
        rw [IndepFun_iff_Indep]
        refine indep_of_indep_of_le_right
          (indep_of_indep_of_le_left (hrun.coin_indep i k).symm hYm'.comap_le) ?_
        exact (measurable_from_nat.comp (comap_measurable (χ i k))).comap_le
      have hmul := hindep.integral_mul_eq_mul_integral (hYm i).aestronglyMeasurable
        (hcm i k).aestronglyMeasurable
      simp only [Pi.mul_apply] at hmul
      have hcoin := coin_integral P F (χ i) (p i) (hrun.coin_le_one i) (hrun.coin_meas i)
        (hrun.coin_prob i) (hp0 i).le (hind i) k
      have e1 : ∫ ω, (χ i k ω : ℝ) * ‖w i k ω - xhat (x k ω) i‖ ^ 2 / p i ∂P =
          ∫ ω, ‖w i k ω - xhat (x k ω) i‖ ^ 2 ∂P := by
        rw [integral_div]
        simp_rw [mul_comm (χ i k _ : ℝ)]
        rw [hmul, hcoin]
        field_simp [(hp0 i).ne']
      rw [e1]
      -- inexactness and (B.3)
      obtain ⟨-, hcond⟩ := hrun.inexact i k
      have hαm : Measurable fun ω => (η ^ (beta χ i k ω + 1)) ^ 2 :=
        (measurable_from_nat (f := fun b : ℕ => (η ^ (b + 1)) ^ 2)).comp ((beta_meas P F (χ i) (p i) (hrun.coin_le_one i) (hrun.coin_meas i)
          (hrun.coin_prob i) (hp0 i).le (hind i) k).mono (F.le k) le_rfl)
      have hαi : Integrable (fun ω => (η ^ (beta χ i k ω + 1)) ^ 2) P :=
        Integrable.of_bound hαm.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← pow_mul]
          exact pow_le_one₀ hη0.le hη1.le)
      have h1 : ∫ ω, ‖w i k ω - xhat (x k ω) i‖ ^ 2 ∂P ≤ ∫ ω, (η ^ (beta χ i k ω + 1)) ^ 2 ∂P := by
        rw [← integral_condExp (F.le k)]
        exact integral_mono_ae integrable_condExp hαi hcond
      have h2 : ∫ ω, (η ^ (beta χ i k ω + 1)) ^ 2 ∂P = η ^ 2 * (p i * (η ^ 2 - 1) + 1) ^ k := by
        have : (fun ω => (η ^ (beta χ i k ω + 1)) ^ 2) =
            fun ω => η ^ 2 * (η ^ 2) ^ (∑ l ∈ Finset.range k, χ i l ω) := by
          funext ω; unfold LeiBR.Rand.beta; rw [← pow_mul, ← pow_mul, pow_succ]; ring
        rw [this, integral_const_mul, rpow_beta P F (χ i) (p i) (hrun.coin_le_one i)
          (hrun.coin_meas i) (hrun.coin_prob i) (hp0 i).le (hind i) (η ^ 2) hη2.le k]
      have h3 : (p i * (η ^ 2 - 1) + 1) ^ k ≤ etatil p η ^ (2 * k) := by
        rw [pow_mul, het_sq]
        refine pow_le_pow_left₀ ?_ ?_ k
        · have := hp1 i; nlinarith
        · have := hpmin_le i; nlinarith
      rw [h2] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left h3 hη2.le)
    have hI4 : ∫ ω, wnorm p (e ω) ^ 2 ∂P ≤ N * (η ^ 2 * etatil p η ^ (2 * k)) := by
      simp_rw [hesq]
      rw [integral_finsetSum _ fun i _ => ?_]
      · calc ∑ i, ∫ ω, (χ i k ω : ℝ) * ‖w i k ω - xhat (x k ω) i‖ ^ 2 / p i ∂P
            ≤ ∑ _i : Fin N, η ^ 2 * etatil p η ^ (2 * k) := Finset.sum_le_sum fun i _ => hterm i
          _ = N * (η ^ 2 * etatil p η ^ (2 * k)) := by simp
      · refine Integrable.of_bound (((hcm i k).mul (hYm i)).div_const _).aestronglyMeasurable
          (Metric.diam (G.X i) ^ 2 / p i) (ae_of_all _ fun ω => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by have := hp0 i; positivity)]
        refine div_le_div_of_nonneg_right ?_ (hp0 i).le
        rcases h01 i ω with h | h
        · simp [h]; positivity
        · simp only [h, Nat.cast_one, one_mul]; exact hYb i ω
    have hsq : Real.sqrt (N * (η ^ 2 * etatil p η ^ (2 * k))) = Real.sqrt N * η * etatil p η ^ k := by
      rw [Real.sqrt_mul (Nat.cast_nonneg N), show η ^ 2 * etatil p η ^ (2 * k) = (η * etatil p η ^ k) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
      ring
    have hI5 : ∫ ω, wnorm p (e ω) ∂P ≤ Real.sqrt N * η * etatil p η ^ k :=
      hI3.trans (hsq ▸ Real.sqrt_le_sqrt hI4)
    linarith
  set B := Real.sqrt N * η / etatil p η with hBdef
  have hB : 0 ≤ B := by positivity
  have hrec : ∀ k, u k ≤ ct ^ k * u 0 + B * k * ct ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 := hstep k
      have hpow : etatil p η ^ k * etatil p η ≤ ct ^ k * ct :=
        mul_le_mul (pow_le_pow_left₀ het0.le hetc k) hetc het0.le (by positivity)
      have h2 : Real.sqrt N * η * etatil p η ^ k ≤ B * ct ^ (k + 1) := by
        rw [hBdef, pow_succ, div_mul_eq_mul_div, le_div_iff₀ het0]
        have : 0 ≤ Real.sqrt N * η := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hpow this]
      have h3 : atil p a * u k ≤ ct * u k := mul_le_mul_of_nonneg_right hact (hu0 k)
      have h4 : ct * u k ≤ ct * (ct ^ k * u 0 + B * k * ct ^ k) :=
        mul_le_mul_of_nonneg_left ih hct0.le
      have e : ct * (ct ^ k * u 0 + B * k * ct ^ k) + B * ct ^ (k + 1) =
          ct ^ (k + 1) * u 0 + B * ((k + 1 : ℕ) : ℝ) * ct ^ (k + 1) := by push_cast; ring
      linarith
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC i0)
  have hu0b : u 0 ≤ Real.sqrt N * Ctil p C := by
    have h0 : u 0 = wnorm p (x0 - xstar) := by
      simp only [hu, hrun.init, integral_const, probReal_univ, one_smul]
    rw [h0]; unfold wnorm Ctil
    calc Real.sqrt (∑ i, ‖(x0 - xstar) i‖ ^ 2 / p i) ≤ Real.sqrt (∑ i, C ^ 2 / p i) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
            div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hC i) 2) (hp0 i).le)
      _ = Real.sqrt N * (C * Real.sqrt (∑ i, ((N : ℝ)⁻¹ * (p i)⁻¹))) := by
          have hN' : (0:ℝ) < N := by exact_mod_cast hN
          rw [← Real.sqrt_sq hC0, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul hN'.le,
            Real.sqrt_sq hC0]
          congr 1
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          field_simp
  have hl2 := lemma_2 ct q (Dconst q ct) hct0 (hq.trans hq1) hq hq1 le_rfl (k : ℝ) (Nat.cast_nonneg k)
  rw [Real.rpow_natCast, Real.rpow_natCast] at hl2
  have hck : ct ^ k ≤ q ^ k := pow_le_pow_left₀ hct0.le hq.le k
  have hCt0 : 0 ≤ Ctil p C := mul_nonneg hC0 (Real.sqrt_nonneg _)
  calc u k ≤ ct ^ k * u 0 + B * k * ct ^ k := hrec k
    _ ≤ q ^ k * (Real.sqrt N * Ctil p C) + B * (Dconst q ct * q ^ k) := by
        have e1 : ct ^ k * u 0 ≤ q ^ k * (Real.sqrt N * Ctil p C) :=
          mul_le_mul hck hu0b (hu0 0) (by positivity)
        have e2 : B * k * ct ^ k ≤ B * (Dconst q ct * q ^ k) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hl2 hB
        linarith
    _ = Real.sqrt N * (Ctil p C + Dtil p a η q) * q ^ k := by
        unfold Dtil
        rw [hBdef, ← hctdef]
        field_simp
