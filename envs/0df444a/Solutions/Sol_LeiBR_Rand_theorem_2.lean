-- Prove2me | solution 1 for LeiBR.Rand.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T10:46:11.348462+00:00
-- url     : https://prove2.me/submissions/ab81beec-d605-4900-93dc-e0bc7a0e4734

import Theorems.Thm_LeiBR_Rand_remark_6
import Theorems.Thm_LeiBR_Rand_lemma_6
open MeasureTheory ProbabilityTheory

namespace LeiBR2Aux

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

lemma proj_lip {m : ℕ} {X : Set (EuclideanSpace ℝ (Fin m))} (hX : Convex ℝ X)
    {Pr : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hP : SpectralProjGrad.Shared.IsProjOnto X Pr) : LipschitzWith 2 Pr := by
  have key : ∀ z y, y ∈ X → (2:ℝ) / 4 * ‖y - Pr z‖ ^ 2 ≤
      (0 + 2 / 2 * ‖y - z‖ ^ 2) - (0 + 2 / 2 * ‖Pr z - z‖ ^ 2) := by
    intro z y hy
    refine mid_strong (g := fun _ => (0:ℝ)) hX (convexOn_const 0 hX) (by norm_num) (hP z).1 hy ?_
    intro w hw
    simp only [Set.mem_ofPred_eq]
    have := (hP z).2 w hw
    rw [norm_sub_rev z, norm_sub_rev z] at this
    have h0 : 0 ≤ ‖Pr z - z‖ := norm_nonneg _
    nlinarith
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  have k1 := key z (Pr z') (hP z').1
  have k2 := key z' (Pr z) (hP z).1
  rw [dist_eq_norm, dist_eq_norm]
  have hid : ‖Pr z' - z‖^2 - ‖Pr z - z‖^2 + ‖Pr z - z'‖^2 - ‖Pr z' - z'‖^2
      = 2 * inner ℝ (Pr z - Pr z') (z - z') := by
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, real_inner_comm]; ring
  have hcs := real_inner_le_norm (Pr z - Pr z') (z - z')
  rw [norm_sub_rev (Pr z') (Pr z)] at k1
  have hsq : ‖Pr z - Pr z'‖ ^ 2 ≤ 2 * ‖Pr z - Pr z'‖ * ‖z - z'‖ := by nlinarith
  push_cast
  rcases (norm_nonneg (Pr z - Pr z')).eq_or_lt with h | h
  · rw [← h]; positivity
  · nlinarith


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


open LeiBR.Rand in
lemma saIter_mem {m : ℕ} {X : Set (EuclideanSpace ℝ (Fin m))}
    {Pr : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)} (hP : ∀ z, Pr z ∈ X)
    (dir : ℕ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (mu : ℝ)
    {z1 : EuclideanSpace ℝ (Fin m)} (hz1 : z1 ∈ X) : ∀ t, saIter Pr dir mu z1 t ∈ X
  | 0 => hz1
  | 1 => hz1
  | (_ + 2) => hP _

open LeiBR.Rand in
lemma saIter_meas {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (i : Fin N)
    {Pr : LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i} (hPr : Measurable Pr)
    {gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i}
    (hg : Measurable (Function.uncurry (gψ i))) (mu : ℝ)
    {y : Ω → LeiBR.Sync.Profile n} (hy : Measurable y) {s : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    (hs : ∀ t, Measurable (s (t + 1))) (t : ℕ) :
    Measurable fun ω => saIter Pr (fun t' z => saDir gψ mu i (y ω) (s t' ω) z) mu (y ω i) t := by
  have hyi : Measurable fun ω => y ω i := (measurable_pi_apply i).comp hy
  suffices H : ∀ t, Measurable fun ω =>
      saIter Pr (fun t' z => saDir gψ mu i (y ω) (s t' ω) z) mu (y ω i) (t + 1) by
    rcases t with _ | t
    · exact hyi
    · exact H t
  intro t
  induction t with
  | zero => exact hyi
  | succ t ih =>
    show Measurable fun ω => Pr (saIter Pr (fun t' z => saDir gψ mu i (y ω) (s t' ω) z) mu (y ω i) (t + 1) -
      (1 / (mu * (((t + 1 : ℕ) : ℝ) + 1))) • saDir gψ mu i (y ω) (s (t + 1) ω)
        (saIter Pr (fun t' z => saDir gψ mu i (y ω) (s t' ω) z) mu (y ω i) (t + 1)))
    have hupd : Measurable fun ω => Function.update (y ω) i
        (saIter Pr (fun t' z => saDir gψ mu i (y ω) (s t' ω) z) mu (y ω i) (t + 1)) :=
      measurable_update'.comp (hy.prodMk ih)
    have hgg : Measurable fun ω => gψ i (Function.update (y ω) i
        (saIter Pr (fun t' z => saDir gψ mu i (y ω) (s t' ω) z) mu (y ω i) (t + 1))) (s (t + 1) ω) :=
      hg.comp (hupd.prodMk (hs t))
    have hdir : Measurable fun ω => saDir gψ mu i (y ω) (s (t + 1) ω)
        (saIter Pr (fun t' z => saDir gψ mu i (y ω) (s t' ω) z) mu (y ω i) (t + 1)) :=
      hgg.add ((ih.sub hyi).const_smul mu)
    exact hPr.comp (ih.sub (hdir.const_smul (1 / (mu * (((t + 1 : ℕ) : ℝ) + 1)))))



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

lemma rpow_beta (r : ℝ) (hr : 1 ≤ r) (k : ℕ) :
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
    have hbd : ∀ ω, |r ^ (∑ l ∈ Finset.range k, c l ω)| ≤ r ^ k := by
      intro ω
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_right₀ hr (beta_le P F c pp hle hmeas hprob hp0 hind k ω)
    have hYi : Integrable (fun ω => r ^ (∑ l ∈ Finset.range k, c l ω)) P :=
      Integrable.of_bound (hYm.mono (F.le k) le_rfl).aestronglyMeasurable (r ^ k)
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hbd ω)
    have hYci : Integrable (fun ω => r ^ (∑ l ∈ Finset.range k, c l ω) * (c k ω : ℝ)) P := by
      refine Integrable.of_bound ((hYm.mono (F.le k) le_rfl).mul
        (measurable_from_nat.comp ((hmeas k).mono (F.le (k + 1)) le_rfl))).aestronglyMeasurable (r ^ k)
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |(c k ω : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg (by positivity)]; exact_mod_cast hle k ω
      calc |r ^ (∑ l ∈ Finset.range k, c l ω)| * |(c k ω : ℝ)| ≤ r ^ k * 1 :=
            mul_le_mul (hbd ω) h1 (abs_nonneg _) (by positivity)
        _ = r ^ k := mul_one _
    rw [integral_add hYi (hYci.const_mul _), integral_const_mul,
      coin_mul P F c pp hle hmeas hprob hp0 hind k _ hYm, ih, pow_succ]
    ring

lemma complexity (Q : ℝ) (hQ : 0 ≤ Q) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (K : ℕ) :
    ∫ ω, ∑ k ∈ Finset.range K,
        (⌈Q / η ^ (2 * (∑ l ∈ Finset.range k, c l ω + 1))⌉₊ : ℝ) * (c k ω : ℝ) ∂P ≤
      ∑ k ∈ Finset.range K, (Q * (η ^ 2)⁻¹ * pp * (pp * ((η ^ 2)⁻¹ - 1) + 1) ^ k + pp) := by
  set r : ℝ := (η ^ 2)⁻¹ with hr
  have hη2 : 0 < η ^ 2 := by positivity
  have hr1 : 1 ≤ r := by
    rw [hr]; exact one_le_inv₀ hη2 |>.2 (by nlinarith)
  set f : ℕ → Ω → ℝ := fun k ω =>
    (Q * r * r ^ (∑ l ∈ Finset.range k, c l ω) + 1) * (c k ω : ℝ) with hf
  have hcm : ∀ k, Measurable (fun ω => (c k ω : ℝ)) := fun k =>
    measurable_from_nat.comp ((hmeas k).mono (F.le (k + 1)) le_rfl)
  have hfm : ∀ k, Measurable (f k) := fun k =>
    ((measurable_from_nat.comp ((beta_meas P F c pp hle hmeas hprob hp0 hind k).mono
      (F.le k) le_rfl)).const_mul _ |>.add_const 1).mul (hcm k)
  have hfb : ∀ k ω, |f k ω| ≤ Q * r * r ^ k + 1 := by
    intro k ω
    have h1 : (c k ω : ℝ) ≤ 1 := by exact_mod_cast hle k ω
    have h2 : r ^ (∑ l ∈ Finset.range k, c l ω) ≤ r ^ k :=
      pow_le_pow_right₀ hr1 (beta_le P F c pp hle hmeas hprob hp0 hind k ω)
    have h3 : 0 ≤ Q * r * r ^ (∑ l ∈ Finset.range k, c l ω) := by positivity
    have h4 : (0:ℝ) ≤ c k ω := by positivity
    rw [abs_of_nonneg (by positivity)]
    calc (Q * r * r ^ (∑ l ∈ Finset.range k, c l ω) + 1) * (c k ω : ℝ)
        ≤ (Q * r * r ^ (∑ l ∈ Finset.range k, c l ω) + 1) * 1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ Q * r * r ^ k + 1 := by
          have : Q * r * r ^ (∑ l ∈ Finset.range k, c l ω) ≤ Q * r * r ^ k :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
          linarith
  have hfi : ∀ k, Integrable (f k) P := fun k =>
    Integrable.of_bound (hfm k).aestronglyMeasurable _
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hfb k ω)
  have hpt : ∀ ω, ∑ k ∈ Finset.range K,
      (⌈Q / η ^ (2 * (∑ l ∈ Finset.range k, c l ω + 1))⌉₊ : ℝ) * (c k ω : ℝ) ≤ ∑ k ∈ Finset.range K, f k ω := by
    intro ω
    refine Finset.sum_le_sum fun k _ => ?_
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ Q / η ^ (2 * (∑ l ∈ Finset.range k, c l ω + 1)) by positivity)
    have heq : Q / η ^ (2 * (∑ l ∈ Finset.range k, c l ω + 1)) = Q * r * r ^ (∑ l ∈ Finset.range k, c l ω) := by
      rw [hr, pow_mul, pow_succ, inv_pow, div_eq_mul_inv, mul_inv]; ring
    rw [heq] at hceil ⊢
    exact mul_le_mul_of_nonneg_right hceil.le (by positivity)
  have hmono : ∫ ω, ∑ k ∈ Finset.range K,
      (⌈Q / η ^ (2 * (∑ l ∈ Finset.range k, c l ω + 1))⌉₊ : ℝ) * (c k ω : ℝ) ∂P ≤
      ∫ ω, ∑ k ∈ Finset.range K, f k ω ∂P :=
    integral_mono_of_nonneg (ae_of_all _ fun ω => Finset.sum_nonneg fun k _ => by positivity)
      (integrable_finsetSum _ fun k _ => hfi k) (ae_of_all _ hpt)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_finsetSum _ fun k _ => hfi k]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hYm : Measurable[F k] (fun ω => r ^ (∑ l ∈ Finset.range k, c l ω)) :=
    measurable_from_nat.comp (beta_meas P F c pp hle hmeas hprob hp0 hind k)
  have e1 : f k = fun ω => (Q * r) * (r ^ (∑ l ∈ Finset.range k, c l ω) * (c k ω : ℝ)) + (c k ω : ℝ) := by
    funext ω; simp only [hf]; ring
  have hYci : Integrable (fun ω => r ^ (∑ l ∈ Finset.range k, c l ω) * (c k ω : ℝ)) P := by
    refine Integrable.of_bound ((hYm.mono (F.le k) le_rfl).mul (hcm k)).aestronglyMeasurable (r ^ k)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |(c k ω : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]; exact_mod_cast hle k ω
    have h2 : |r ^ (∑ l ∈ Finset.range k, c l ω)| ≤ r ^ k := by
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_right₀ hr1 (beta_le P F c pp hle hmeas hprob hp0 hind k ω)
    calc |r ^ (∑ l ∈ Finset.range k, c l ω)| * |(c k ω : ℝ)| ≤ r ^ k * 1 :=
          mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
      _ = r ^ k := mul_one _
  have hci : Integrable (fun ω => (c k ω : ℝ)) P :=
    Integrable.of_bound (hcm k).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact_mod_cast hle k ω)
  rw [e1, integral_add (hYci.const_mul _) hci, integral_const_mul,
    coin_mul P F c pp hle hmeas hprob hp0 hind k _ hYm,
    rpow_beta P F c pp hle hmeas hprob hp0 hind r hr1 k,
    coin_integral P F c pp hle hmeas hprob hp0 hind k]
  ring

end coin

lemma final_alg (pp pm Q η q εt : ℝ) (hpp : 0 < pp) (hpp1 : pp ≤ 1) (hpm : pp ≤ pm) (hQ : 0 ≤ Q)
    (hη0 : 0 < η) (hη1 : η < 1) (hq0 : 0 < q) (hq1 : q < 1) (hε0 : 0 < εt) (hε1 : εt < 1) :
    ∑ k ∈ Finset.range ⌈Real.log (1 / εt) / Real.log (1 / q)⌉₊,
        (Q * (η ^ 2)⁻¹ * pp * (pp * ((η ^ 2)⁻¹ - 1) + 1) ^ k + pp) ≤
      pp * Q / (η ^ 2 * (1 / Real.sqrt (pm * ((η ^ 2)⁻¹ - 1) + 1)) ^ 2 *
        Real.log (1 / (1 / Real.sqrt (pm * ((η ^ 2)⁻¹ - 1) + 1)) ^ 2)) *
        (1 / εt) ^ (Real.log (1 / (1 / Real.sqrt (pm * ((η ^ 2)⁻¹ - 1) + 1)) ^ 2) / Real.log (1 / q)) +
      (⌈Real.log (1 / εt) / Real.log (1 / q)⌉₊ : ℝ) := by
  set L := Real.log (1 / εt) / Real.log (1 / q) with hL
  set K := ⌈L⌉₊ with hK
  set r : ℝ := (η ^ 2)⁻¹ with hr
  have hη2 : 0 < η ^ 2 := by positivity
  have hη21 : η ^ 2 < 1 := by nlinarith
  have hr1 : 1 < r := by rw [hr]; exact (one_lt_inv₀ hη2).2 hη21
  set ρ := pm * (r - 1) + 1 with hρ
  have hpm0 : 0 < pm := lt_of_lt_of_le hpp hpm
  have hρ1 : 1 < ρ := by rw [hρ]; nlinarith
  have hρ0 : 0 < ρ := by linarith
  have he0 : (1 / Real.sqrt ρ) ^ 2 = 1 / ρ := by
    rw [div_pow, Real.sq_sqrt hρ0.le, one_pow]
  rw [he0, one_div_one_div]
  have hlρ : 0 < Real.log ρ := Real.log_pos hρ1
  have hlq : 0 < Real.log (1 / q) := Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hq0).2 hq1)
  have hlε : 0 < Real.log (1 / εt) := Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hε0).2 hε1)
  have hL0 : 0 ≤ L := by positivity
  -- the rpow term
  have hrp : (1 / εt) ^ (Real.log ρ / Real.log (1 / q)) = ρ ^ L := by
    rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hρ0, hL]; ring_nf
  rw [hrp]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  have hsum1 : ∑ k ∈ Finset.range K, (pp * (r - 1) + 1) ^ k ≤ ∑ k ∈ Finset.range K, ρ ^ k :=
    Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (by nlinarith) (by rw [hρ]; nlinarith) k
  have hgeom : ∑ k ∈ Finset.range K, ρ ^ k ≤ ρ ^ K / Real.log ρ := by
    rw [geom_sum_eq hρ1.ne']
    have h1 : ρ ^ K - 1 ≤ ρ ^ K := by linarith
    have h2 : Real.log ρ ≤ ρ - 1 := Real.log_le_sub_one_of_pos hρ0
    calc (ρ ^ K - 1) / (ρ - 1) ≤ ρ ^ K / (ρ - 1) := div_le_div_of_nonneg_right h1 (by linarith)
      _ ≤ ρ ^ K / Real.log ρ := div_le_div_of_nonneg_left (by positivity) hlρ h2
  have hKL : (K : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one hL0).le
  have hpowK : ρ ^ K ≤ ρ ^ L * ρ := by
    rw [← Real.rpow_add_one hρ0.ne', ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hρ1.le hKL
  have hA : 0 ≤ Q * r * pp := by positivity
  have hmain : Q * r * pp * ∑ k ∈ Finset.range K, (pp * (r - 1) + 1) ^ k ≤
      pp * Q / (η ^ 2 * (1 / ρ) * Real.log ρ) * ρ ^ L := by
    calc Q * r * pp * ∑ k ∈ Finset.range K, (pp * (r - 1) + 1) ^ k
        ≤ Q * r * pp * (ρ ^ L * ρ / Real.log ρ) := by
          refine mul_le_mul_of_nonneg_left (hsum1.trans (hgeom.trans ?_)) hA
          exact div_le_div_of_nonneg_right hpowK hlρ.le
      _ = pp * Q / (η ^ 2 * (1 / ρ) * Real.log ρ) * ρ ^ L := by
          rw [hr]; field_simp
  have hK' : (K : ℝ) * pp ≤ K := by
    have : (0:ℝ) ≤ K := by positivity
    nlinarith
  linarith


open LeiBR.Rand in
lemma saIterRand_meas {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (i : Fin N)
    {Pr : LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i} (hPr : Measurable Pr)
    {gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i}
    (hg : Measurable (Function.uncurry (gψ i))) (mu : ℝ)
    {y : Ω → LeiBR.Sync.Profile n} (hy : Measurable y) {s : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
    (hs : ∀ t, Measurable (s (t + 1))) {jj : Ω → ℕ} (hj : Measurable jj) :
    Measurable fun ω => saIter Pr (fun t' z => saDir gψ mu i (y ω) (s t' ω) z) mu (y ω i) (jj ω) := by
  have H : Measurable (fun q : Ω × ℕ =>
      saIter Pr (fun t' z => saDir gψ mu i (y q.1) (s t' q.1) z) mu (y q.1 i) q.2) :=
    measurable_from_prod_countable_left fun m => saIter_meas i hPr hg mu hy hs m
  exact H.comp (measurable_id.prodMk hj)

end LeiBR2Aux

open LeiBR.Rand LeiBR2Aux

theorem solution {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 G μξ ψ gψ M) (mu : ℝ) (hmu : 0 < mu)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : IsProxBR G mu xhat)
    (hA2 : Assumption2 G mu) (xstar : LeiBR.Sync.Profile n) (hNE : G.IsNE xstar) (hN : 0 < N)
    (proj : ∀ i, LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i)
    (hproj : ∀ i, SpectralProjGrad.Shared.IsProjOnto (G.X i) (proj i))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (p : Fin N → ℝ)
    (χ : Fin N → ℕ → Ω → ℕ) (ξs : Fin N → ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (x0 : LeiBR.Sync.Profile n) (x : ℕ → Ω → LeiBR.Sync.Profile n) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (C : ℝ) (hC : ∀ i, ‖x0 i - xstar i‖ ≤ C)
    (q : ℝ) (hq : ctil p (contrFactor G mu) η < q) (hq1 : q < 1)
    (hrun : IsAlg2SARun G proj gψ mu μξ P F p χ ξs
      (fun i k ω => ⌈Qconst G M mu i / η ^ (2 * (beta χ i k ω + 1))⌉₊) x0 x)
    (ε : ℝ) (hε : 0 < ε)
    (hεtil : ε / (Real.sqrt (N * pmax p) * (Ctil p C + Dtil p (contrFactor G mu) η q)) < 1) :
    let εt := ε / (Real.sqrt (N * pmax p) * (Ctil p C + Dtil p (contrFactor G mu) η q))
    let K := ⌈Real.log (1 / εt) / Real.log (1 / q)⌉₊
    (∫ ω, blockNorm (x K ω - xstar) ∂P ≤ ε) ∧
    ∀ i, ∫ ω, ∑ k ∈ Finset.range K,
        (⌈Qconst G M mu i / η ^ (2 * (beta χ i k ω + 1))⌉₊ : ℝ) * (χ i k ω : ℝ) ∂P ≤
      p i * Qconst G M mu i / (η ^ 2 * etatil0 p η ^ 2 * Real.log (1 / etatil0 p η ^ 2)) *
        (1 / εt) ^ (Real.log (1 / etatil0 p η ^ 2) / Real.log (1 / q)) + (K : ℝ) := by
  intro εt K
  have hp0 := hrun.p_pos
  have hp1 := hrun.p_le_one
  have i0 : Fin N := ⟨0, hN⟩
  have hpmax : ∀ i, p i ≤ pmax p := fun i => le_ciSup (Finite.bddAbove_range p) i
  have hpmin1 : pmin p ≤ 1 := (ciInf_le (Finite.bddBelow_range p) i0).trans (hp1 i0)
  have hpmax0 : 0 < pmax p := (hp0 i0).trans_le (hpmax i0)
  have hη2 : 0 < η ^ 2 := by positivity
  have hη21 : η ^ 2 < 1 := by nlinarith
  have het : 0 < etatil p η := by
    unfold etatil
    refine Real.sqrt_pos.2 ?_
    have := mul_le_mul_of_nonneg_right hpmin1 (show 0 ≤ 1 - η ^ 2 by linarith)
    nlinarith
  have hct : 0 < ctil p (contrFactor G mu) η := lt_of_lt_of_le het (le_max_right _ _)
  have hq0 : 0 < q := hct.trans hq
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC i0)
  have hCt : 0 ≤ Ctil p C := mul_nonneg hC0 (Real.sqrt_nonneg _)
  have hD : 0 < Dconst q (ctil p (contrFactor G mu) η) := by
    unfold Dconst
    have : 0 < Real.log (q / ctil p (contrFactor G mu) η) := Real.log_pos ((one_lt_div hct).2 hq)
    positivity
  have hDt : 0 < Dtil p (contrFactor G mu) η q := by
    unfold Dtil; positivity
  have hB : 0 < Real.sqrt (N * pmax p) * (Ctil p C + Dtil p (contrFactor G mu) η q) := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    have : 0 < Real.sqrt (N * pmax p) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hεt0 : 0 < εt := div_pos hε hB
  have hQ : ∀ i, 0 < Qconst G M mu i := by
    intro i; unfold Qconst; have := hA1.M_pos i; positivity
  have hind : ∀ i k, Indep (MeasurableSpace.comap (χ i k) inferInstance) (F k) P :=
    fun i k => indep_of_indep_of_le_right (hrun.coin_indep i k) le_sup_left
  have hβm : ∀ i k, Measurable[F k] (beta χ i k) := fun i k =>
    beta_meas P F (χ i) (p i) (hrun.coin_le_one i) (hrun.coin_meas i) (hrun.coin_prob i)
      (hp0 i).le (hind i) k
  have hjm : ∀ i k, Measurable[F k]
      (fun ω => ⌈Qconst G M mu i / η ^ (2 * (beta χ i k ω + 1))⌉₊) := fun i k =>
    (measurable_from_nat (f := fun b => ⌈Qconst G M mu i / η ^ (2 * (b + 1))⌉₊)).comp (hβm i k)
  have hprojm : ∀ i, Measurable (proj i) := fun i =>
    (proj_lip (hA1.convex i) (hproj i)).continuous.measurable
  -- feasibility
  have hfeas : ∀ k ω, G.Feasible (x k ω) := by
    intro k
    induction k with
    | zero => intro ω; rw [hrun.init ω]; exact hrun.x0_feas
    | succ k ih =>
      intro ω i
      rw [hrun.step k ω i]
      split_ifs
      · exact saIter_mem (fun z => (hproj i z).1) _ _ (ih ω i) _
      · exact ih ω i
  -- σ-algebras
  let 𝒢 : Fin N → ℕ → MeasurableSpace Ω := fun i k =>
    F k ⊔ ⨆ t, MeasurableSpace.comap (ξs i k (t + 1)) inferInstance
  have h𝒢le : ∀ i k, 𝒢 i k ≤ F (k + 1) := fun i k =>
    sup_le (F.mono k.le_succ) (iSup_le fun t => (hrun.sample_meas i k (t + 1)).comap_le)
  have hsG : ∀ i k t, Measurable[𝒢 i k] (ξs i k (t + 1)) := fun i k t =>
    Measurable.of_comap_le ((le_iSup (fun t => MeasurableSpace.comap (ξs i k (t + 1)) inferInstance) t).trans
      le_sup_right)
  let w : ∀ i, ℕ → Ω → LeiBR.Sync.Strat n i := fun i k ω =>
    saIter (proj i) (fun t z => saDir gψ mu i (x k ω) (ξs i k t ω) z) mu (x k ω i)
      (⌈Qconst G M mu i / η ^ (2 * (beta χ i k ω + 1))⌉₊)
  have meas_w : ∀ k, Measurable[F k] (x k) → ∀ i, Measurable[𝒢 i k] (w i k) := by
    intro k hxk i
    exact @saIterRand_meas Ω (𝒢 i k) N n d i (proj i) (hprojm i) gψ (hA1.gψ_meas i) mu (x k)
      (hxk.mono le_sup_left le_rfl) (ξs i k) (hsG i k) _ ((hjm i k).mono le_sup_left le_rfl)
  have hxm : ∀ k, Measurable[F k] (x k) := by
    intro k
    induction k with
    | zero =>
      have : x 0 = fun _ => x0 := funext hrun.init
      rw [this]; exact measurable_const
    | succ k ih =>
      have hw := meas_w k ih
      have : x (k + 1) = fun ω i => if χ i k ω = 1 then w i k ω else x k ω i := by
        funext ω i; exact hrun.step k ω i
      rw [this]
      refine @measurable_pi_lambda Ω (Fin N) (fun i => LeiBR.Sync.Strat n i) (F (k + 1)) _ _ fun i => ?_
      have hs : MeasurableSet[F (k + 1)] {ω | χ i k ω = 1} :=
        (hrun.coin_meas i k) (measurableSet_singleton 1)
      exact @Measurable.ite Ω _ _ _ (F (k + 1)) _ (fun ω => χ i k ω = 1) _ hs ((hw i).mono (h𝒢le i k) le_rfl)
        (((measurable_pi_apply i).comp ih).mono (F.mono k.le_succ) le_rfl)
  have hxm' : ∀ k, Measurable (x k) := fun k => (hxm k).mono (F.le k) le_rfl
  have hxh : ∀ k i, Measurable (fun ω => xhat (x k ω) i) := by
    intro k i
    have hc := (xhat_contOn G hA1 hmu hxhat i).domRestrict
    have hm : Measurable fun ω : Ω => (⟨x k ω, hfeas k ω⟩ : {y | G.Feasible y}) :=
      (hxm' k).subtype_mk
    exact hc.measurable.comp hm
  have hdiam : ∀ i (a b : LeiBR.Sync.Strat n i), a ∈ G.X i → b ∈ G.X i →
      ‖a - b‖ ^ 2 ≤ Metric.diam (G.X i) ^ 2 := by
    intro i a b ha hb
    have := Metric.dist_le_diam_of_mem (hA1.compact i).isBounded ha hb
    rw [dist_eq_norm] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hsamb : ∀ i k t, Measurable (ξs i k t) := fun i k t =>
    (hrun.sample_meas i k t).mono (F.le _) le_rfl
  -- the inexactness condition (33)
  have hinexact : ∀ i k, Integrable (fun ω => ‖w i k ω - xhat (x k ω) i‖ ^ 2) P ∧
      P[fun ω => ‖w i k ω - xhat (x k ω) i‖ ^ 2 | F k] ≤ᵐ[P]
        fun ω => (η ^ (beta χ i k ω + 1)) ^ 2 := by
    intro i k
    set g : Ω → ℝ := fun ω => ‖w i k ω - xhat (x k ω) i‖ ^ 2 with hgdef
    let Gm : ℕ → Ω → ℝ := fun m ω =>
      ‖saIter (proj i) (fun t' z => saDir gψ mu i (x k ω) (ξs i k t' ω) z) mu (x k ω i) m
        - xhat (x k ω) i‖ ^ 2
    have hmemS : ∀ m ω, saIter (proj i) (fun t' z => saDir gψ mu i (x k ω) (ξs i k t' ω) z) mu
        (x k ω i) m ∈ G.X i := fun m ω => saIter_mem (fun z => (hproj i z).1) _ _ (hfeas k ω i) m
    have hxhmem : ∀ ω, xhat (x k ω) i ∈ G.X i := fun ω => (hxhat (x k ω) (hfeas k ω) i).1
    have hGint : ∀ m, Integrable (Gm m) P := by
      intro m
      refine Integrable.of_bound ((((saIter_meas i (hprojm i) (hA1.gψ_meas i) mu (hxm' k)
        (fun t => hsamb i k (t + 1)) m).sub (hxh k i)).norm.pow_const 2).aestronglyMeasurable)
        (Metric.diam (G.X i) ^ 2) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hdiam i _ _ (hmemS m ω) (hxhmem ω)
    have hwamb : Measurable (w i k) :=
      (meas_w k (hxm k) i).mono ((h𝒢le i k).trans (F.le _)) le_rfl
    have hgint : Integrable g P := by
      refine Integrable.of_bound (((hwamb.sub (hxh k i)).norm.pow_const 2).aestronglyMeasurable)
        (Metric.diam (G.X i) ^ 2) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hdiam i _ _ (hmemS _ ω) (hxhmem ω)
    refine ⟨hgint, ?_⟩
    have hA : ∀ m : ℕ, MeasurableSet[F k] {ω | ⌈Qconst G M mu i / η ^ (2 * (beta χ i k ω + 1))⌉₊ = m} :=
      fun m => (hjm i k) (measurableSet_singleton m)
    have hind_eq : ∀ m : ℕ, {ω | ⌈Qconst G M mu i / η ^ (2 * (beta χ i k ω + 1))⌉₊ = m}.indicator g =
        {ω | ⌈Qconst G M mu i / η ^ (2 * (beta χ i k ω + 1))⌉₊ = m}.indicator (Gm m) := by
      intro m; funext ω
      by_cases hω : ω ∈ {ω | ⌈Qconst G M mu i / η ^ (2 * (beta χ i k ω + 1))⌉₊ = m}
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        simp only [Set.mem_ofPred_eq] at hω
        simp only [hgdef, Gm, w, hω]
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
    have hloc : ∀ m : ℕ, ∀ᵐ ω ∂P,
        {ω | ⌈Qconst G M mu i / η ^ (2 * (beta χ i k ω + 1))⌉₊ = m}.indicator (P[g | F k]) ω =
        {ω | ⌈Qconst G M mu i / η ^ (2 * (beta χ i k ω + 1))⌉₊ = m}.indicator (P[Gm m | F k]) ω := by
      intro m
      have e1 := condExp_indicator (m := F k) hgint (hA m)
      have e2 := condExp_indicator (m := F k) (hGint m) (hA m)
      rw [hind_eq m] at e1
      filter_upwards [e1, e2] with ω h1 h2
      rw [← h1, ← h2]
    have hb : ∀ m : ℕ, ∀ᵐ ω ∂P, 1 ≤ m → P[Gm m | F k] ω ≤ Qconst G M mu i / ((m : ℝ) + 1) := by
      intro m
      rcases Nat.eq_zero_or_pos m with hm | hm
      · exact ae_of_all _ fun ω h => absurd h (by omega)
      · have := lemma_6 G μξ ψ gψ M hA1 mu hmu xhat hxhat proj hproj P F k (x k)
          (hxm k).stronglyMeasurable (hfeas k) (ξs i k) (hsamb i k) (hrun.sample_law i k)
          (hrun.sample_iid i k) (hrun.sample_indep i k) i m hm
        filter_upwards [this] with ω h _
        exact h
    filter_upwards [ae_all_iff.2 hloc, ae_all_iff.2 hb] with ω h1 h2
    set m := ⌈Qconst G M mu i / η ^ (2 * (beta χ i k ω + 1))⌉₊ with hm
    have hωm : ω ∈ {ω | ⌈Qconst G M mu i / η ^ (2 * (beta χ i k ω + 1))⌉₊ = m} := by
      simp only [Set.mem_ofPred_eq, hm]
    have h1m := h1 m
    rw [Set.indicator_of_mem hωm, Set.indicator_of_mem hωm] at h1m
    have hpos : 0 < Qconst G M mu i / η ^ (2 * (beta χ i k ω + 1)) := div_pos (hQ i) (by positivity)
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 hpos))
    rw [h1m]
    refine (h2 m hm1).trans ?_
    have hle : Qconst G M mu i / η ^ (2 * (beta χ i k ω + 1)) ≤ (m : ℝ) := Nat.le_ceil _
    have hηp : 0 < η ^ (2 * (beta χ i k ω + 1)) := by positivity
    rw [div_le_iff₀ hηp] at hle
    rw [div_le_iff₀ (by positivity), ← pow_mul, mul_comm (beta χ i k ω + 1) 2]
    nlinarith
  have hrun2 : IsAlg2Run G xhat P F p χ w (fun i k ω => η ^ (beta χ i k ω + 1)) x0 x :=
    { p_pos := hrun.p_pos
      p_le_one := hrun.p_le_one
      coin_le_one := hrun.coin_le_one
      coin_meas := hrun.coin_meas
      coin_prob := hrun.coin_prob
      coin_indep := fun i k => indep_of_indep_of_le_right (hrun.coin_indep i k)
        (sup_le le_sup_left (meas_w k (hxm k) i).comap_le)
      x0_feas := hrun.x0_feas
      init := hrun.init
      step := fun k ω i => hrun.step k ω i
      w_mem := fun i k ω => saIter_mem (fun z => (hproj i z).1) _ _ (hfeas k ω i) _
      w_meas := fun i k => ((meas_w k (hxm k) i).mono (h𝒢le i k) le_rfl).stronglyMeasurable
      α_nonneg := fun i k ω => by positivity
      α_meas := fun i k =>
        (measurable_from_nat (f := fun b => η ^ (b + 1))).comp (hβm i k)
      inexact := hinexact }
  obtain ⟨-, r2⟩ := remark_6 G μξ ψ gψ M hA1 mu hmu xhat hxhat hA2 xstar hNE hN P F p χ w x0 x η
    hη0 hη1 C hC hrun2 q hq hq1 K
  obtain ⟨r1, -⟩ := remark_6 G μξ ψ gψ M hA1 mu hmu xhat hxhat hA2 xstar hNE hN P F p χ w x0 x η
    hη0 hη1 C hC hrun2 q hq hq1 K
  have hεt1 : εt < 1 := hεtil
  have hlq : 0 < Real.log (1 / q) := Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hq0).2 hq1)
  have hlε : 0 < Real.log (1 / εt) := Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hεt0).2 hεt1)
  refine ⟨?_, ?_⟩
  · -- ε-NE₂
    have hqK : q ^ K ≤ εt := by
      rw [← Real.log_le_log_iff (by positivity) hεt0, Real.log_pow]
      have hKL : Real.log (1 / εt) / Real.log (1 / q) ≤ K := Nat.le_ceil _
      have hlq' : Real.log q = - Real.log (1 / q) := by
        rw [one_div, Real.log_inv]; ring
      have hle' : Real.log εt = - Real.log (1 / εt) := by
        rw [one_div, Real.log_inv]; ring
      rw [hlq', hle']
      rw [div_le_iff₀ hlq] at hKL
      nlinarith
    calc ∫ ω, blockNorm (x K ω - xstar) ∂P
        ≤ Real.sqrt (N * pmax p) * (Ctil p C + Dtil p (contrFactor G mu) η q) * q ^ K := r1.trans r2
      _ ≤ Real.sqrt (N * pmax p) * (Ctil p C + Dtil p (contrFactor G mu) η q) * εt :=
          mul_le_mul_of_nonneg_left hqK hB.le
      _ = ε := by
          show Real.sqrt (N * pmax p) * (Ctil p C + Dtil p (contrFactor G mu) η q) *
            (ε / (Real.sqrt (N * pmax p) * (Ctil p C + Dtil p (contrFactor G mu) η q))) = ε
          field_simp
  · -- expected number of SG steps
    intro i
    have hc := complexity P F (χ i) (p i) (hrun.coin_le_one i) (hrun.coin_meas i) (hrun.coin_prob i)
      (hp0 i).le (hind i) (Qconst G M mu i) (hQ i).le η hη0 hη1 K
    have hf := final_alg (p i) (pmax p) (Qconst G M mu i) η q εt (hp0 i) (hp1 i) (hpmax i) (hQ i).le
      hη0 hη1 hq0 hq1 hεt0 hεt1
    unfold etatil0
    exact hc.trans hf
