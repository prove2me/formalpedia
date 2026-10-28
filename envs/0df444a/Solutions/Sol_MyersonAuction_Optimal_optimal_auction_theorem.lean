-- Prove2me | solution 1 for MyersonAuction.Optimal.optimal_auction_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T13:54:18.937554+00:00
-- url     : https://prove2.me/submissions/798b5ad2-62b8-47a2-bf1a-582aaa810216

import Mathlib
import Definitions.Def_MyersonAuction_Optimal_Ironing

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace MyersonAuction.Optimal.Pf

variable {ι : Type} [Fintype ι]

/-- Marginal law of bidder `i`. -/
def mu (E : Environment ι) (i : ι) : Measure ℝ :=
  (volume.restrict (Set.Icc (E.a i) (E.b i))).withDensity (fun s => ENNReal.ofReal (E.f i s))

lemma mu_apply (E : Environment ι) (i : ι) (A : Set ℝ) (hA : MeasurableSet A) :
    mu E i A = ENNReal.ofReal (∫ s in A ∩ Set.Icc (E.a i) (E.b i), E.f i s) := by
  rw [mu, withDensity_apply _ hA, Measure.restrict_restrict hA,
    ofReal_integral_eq_lintegral_ofReal]
  · exact ((E.f_cont i).integrableOn_Icc).mono_set Set.inter_subset_right
  · filter_upwards [ae_restrict_mem (hA.inter measurableSet_Icc)] with s hs
    exact (E.f_pos i s hs.2).le

instance mu_prob (E : Environment ι) (i : ι) : IsProbabilityMeasure (mu E i) := by
  constructor
  rw [mu_apply E i _ MeasurableSet.univ, Set.univ_inter, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (E.a_lt_b i).le, E.f_int i, ENNReal.ofReal_one]

lemma dist_box (E : Environment ι) (s : ι → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) :
    distribution E (Set.univ.pi s) = ∏ i, mu E i (s i) := by
  have hS : MeasurableSet (Set.univ.pi fun i => s i ∩ Set.Icc (E.a i) (E.b i)) :=
    MeasurableSet.univ_pi fun i => (hs i).inter measurableSet_Icc
  have hset : Set.univ.pi s ∩ support E =
      Set.univ.pi fun i => s i ∩ Set.Icc (E.a i) (E.b i) := by
    simp only [support]; rw [← Set.pi_inter_distrib]
  rw [distribution, withDensity_apply _ (MeasurableSet.univ_pi hs),
    Measure.restrict_restrict (MeasurableSet.univ_pi hs), hset]
  have hint : Integrable (fun t : ι → ℝ => ∏ i, E.f i (t i))
      (volume.restrict (Set.univ.pi fun i => s i ∩ Set.Icc (E.a i) (E.b i))) := by
    rw [volume_pi, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod fun i =>
      ((E.f_cont i).integrableOn_Icc).mono_set Set.inter_subset_right
  have hnn : 0 ≤ᵐ[volume.restrict (Set.univ.pi fun i => s i ∩ Set.Icc (E.a i) (E.b i))]
      (fun t : ι → ℝ => ∏ i, E.f i (t i)) := by
    filter_upwards [ae_restrict_mem hS] with t ht
    exact Finset.prod_nonneg fun i _ => (E.f_pos i (t i) (ht i (Set.mem_univ i)).2).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg]
  · exact Finset.prod_congr rfl fun i _ => (mu_apply E i (s i) (hs i)).symm
  · intro i _
    exact setIntegral_nonneg ((hs i).inter measurableSet_Icc) fun x hx => (E.f_pos i x hx.2).le

lemma dist_eq_pi (E : Environment ι) : distribution E = Measure.pi (mu E) :=
  (Measure.pi_eq (dist_box E)).symm

instance dist_prob (E : Environment ι) : IsProbabilityMeasure (distribution E) := by
  rw [dist_eq_pi]; infer_instance

variable [DecidableEq ι]

omit [Fintype ι] in
lemma update_preimage_box (i : ι) (s : ι → Set ℝ) :
    (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
  ext ⟨t, x⟩
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
  constructor
  · intro h
    refine ⟨fun j => ?_, by simpa using h i⟩
    by_cases hj : j = i
    · subst hj; simp
    · simpa [Function.update_of_ne hj] using h j
  · rintro ⟨h1, h2⟩ j
    by_cases hj : j = i
    · subst hj; simpa using h2
    · simpa [Function.update_of_ne hj] using h1 j

lemma update_measurePreserving (E : Environment ι) (i : ι) :
    MeasurePreserving (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
      ((Measure.pi (mu E)).prod (mu E i)) (Measure.pi (mu E)) := by
  refine ⟨measurable_update', ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs), update_preimage_box,
    Measure.prod_prod, Measure.pi_pi]
  have : (fun j => mu E j (Function.update s i Set.univ j)) =
      Function.update (fun j => mu E j (s j)) i 1 := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [this, Finset.prod_update_of_mem (Finset.mem_univ i), one_mul,
    ← Finset.mul_prod_erase Finset.univ (fun j => mu E j (s j)) (Finset.mem_univ i), mul_comm]
  congr 1
  apply Finset.prod_congr (by ext; simp) (fun _ _ => rfl)

/-- Fubini over the `i`-th coordinate. -/
lemma integral_update (E : Environment ι) (i : ι) (φ : (ι → ℝ) → ℝ)
    (hφ : Integrable φ (distribution E)) :
    ∫ t, φ t ∂distribution E =
      ∫ s, (∫ t, φ (Function.update t i s) ∂distribution E) ∂mu E i := by
  rw [dist_eq_pi] at hφ ⊢
  have hmp := update_measurePreserving E i
  have hint : Integrable (fun p : (ι → ℝ) × ℝ => φ (Function.update p.1 i p.2))
      ((Measure.pi (mu E)).prod (mu E i)) :=
    (hmp.integrable_comp hφ.aestronglyMeasurable).mpr hφ
  have h1 : ∫ t, φ t ∂Measure.pi (mu E) =
      ∫ p, φ (Function.update p.1 i p.2) ∂((Measure.pi (mu E)).prod (mu E i)) := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable
      (by rw [hmp.map_eq]; exact hφ.aestronglyMeasurable)
  rw [h1, integral_prod_symm _ hint]


omit [DecidableEq ι] in
lemma mem_support (E : Environment ι) {u : ι → ℝ} :
    u ∈ support E ↔ ∀ j, u j ∈ Set.Icc (E.a j) (E.b j) := by
  unfold support; simp only [Set.mem_pi, Set.mem_univ, true_implies]

omit [DecidableEq ι] in
lemma ae_support (E : Environment ι) : ∀ᵐ t ∂distribution E, t ∈ support E := by
  have hs : MeasurableSet (support E) := MeasurableSet.univ_pi fun i => measurableSet_Icc
  unfold distribution
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hs)

lemma update_mem_support (E : Environment ι) (i : ι) {t : ι → ℝ} (ht : t ∈ support E)
    {r : ℝ} (hr : r ∈ Set.Icc (E.a i) (E.b i)) : Function.update t i r ∈ support E := by
  rw [mem_support] at ht ⊢
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hr
  · rw [Function.update_of_ne hj]; exact ht j

omit [DecidableEq ι] in
/-- A continuous version of `e j`. -/
def eC (E : Environment ι) (j : ι) (x : ℝ) : ℝ :=
  E.e j (Set.projIcc (E.a j) (E.b j) (E.a_lt_b j).le x)

omit [DecidableEq ι] in
lemma eC_cont (E : Environment ι) (j : ι) : Continuous (eC E j) :=
  (E.e_cont j).comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun x => (Set.projIcc (E.a j) (E.b j) (E.a_lt_b j).le x).2)

omit [DecidableEq ι] in
lemma eC_eq (E : Environment ι) (j : ι) {x : ℝ} (hx : x ∈ Set.Icc (E.a j) (E.b j)) :
    eC E j x = E.e j x := by
  simp [eC, Set.projIcc_of_mem _ hx]

omit [DecidableEq ι] in
lemma eC_bound (E : Environment ι) (j : ι) : ∃ M, ∀ x, |eC E j x| ≤ M := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (E.e_cont j)
  exact ⟨C, fun x => by
    simpa [eC, Real.norm_eq_abs] using hC _ (Set.projIcc (E.a j) (E.b j) (E.a_lt_b j).le x).2⟩

/-- A continuous version of `bidderValue`. -/
def bvC (E : Environment ι) (i : ι) (u : ι → ℝ) : ℝ :=
  u i + ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), eC E j (u j)

lemma bvC_cont (E : Environment ι) (i : ι) : Continuous (bvC E i) :=
  (continuous_apply i).add (continuous_finsetSum _ fun j _ => (eC_cont E j).comp (continuous_apply j))

lemma bv_eq_bvC (E : Environment ι) (i : ι) {u : ι → ℝ} (hu : u ∈ support E) :
    bidderValue E i u = bvC E i u := by
  rw [mem_support] at hu
  simp only [bidderValue, bvC]
  congr 1
  exact Finset.sum_congr rfl fun j _ => (eC_eq E j (hu j)).symm

lemma bvC_bound (E : Environment ι) : ∃ B, ∀ i u, |bvC E i u| ≤ |u i| + B := by
  choose M hM using eC_bound E
  refine ⟨∑ j, M j, fun i u => ?_⟩
  have hM0 : ∀ j, 0 ≤ M j := fun j => (abs_nonneg _).trans (hM j 0)
  calc |bvC E i u| ≤ |u i| + |∑ j ∈ Finset.univ.filter (fun j => j ≠ i), eC E j (u j)| :=
        abs_add_le _ _
    _ ≤ |u i| + ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), |eC E j (u j)| := by
        gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ |u i| + ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), M j := by
        gcongr with j; exact hM j _
    _ ≤ |u i| + ∑ j, M j := by
        gcongr
        all_goals first | exact Finset.subset_univ _ | exact fun j _ _ => hM0 j

lemma bv_update (E : Environment ι) (i : ι) (t : ι → ℝ) (s r : ℝ) :
    bidderValue E i (Function.update t i s) = bidderValue E i (Function.update t i r) + (s - r) := by
  have h : ∀ v : ℝ, bidderValue E i (Function.update t i v) =
      v + ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), E.e j (t j) := by
    intro v
    simp only [bidderValue, Function.update_self]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.mem_filter.mp hj).2]
  rw [h, h]; ring

lemma bvr_aesm (E : Environment ι) (i : ι) (r : ℝ) (hr : r ∈ Set.Icc (E.a i) (E.b i)) :
    AEStronglyMeasurable (fun t => bidderValue E i (Function.update t i r)) (distribution E) := by
  have hc : Continuous (fun t : ι → ℝ => Function.update t i r) :=
    continuous_id.update i continuous_const
  refine ((bvC_cont E i).comp hc).aestronglyMeasurable.congr ?_
  filter_upwards [ae_support E] with t ht
  exact (bv_eq_bvC E i (update_mem_support E i ht hr)).symm

lemma bvr_integrable_mul (E : Environment ι) (i : ι) (r : ℝ) (hr : r ∈ Set.Icc (E.a i) (E.b i))
    (φ : (ι → ℝ) → ℝ) (hφ : Integrable φ (distribution E)) :
    Integrable (fun t => bidderValue E i (Function.update t i r) * φ t) (distribution E) := by
  obtain ⟨B, hB⟩ := bvC_bound E
  refine hφ.bdd_mul (c := |r| + B) (bvr_aesm E i r hr) ?_
  filter_upwards [ae_support E] with t ht
  rw [bv_eq_bvC E i (update_mem_support E i ht hr), Real.norm_eq_abs]
  simpa using hB i (Function.update t i r)

lemma report_eq (E : Environment ι) (p x : Outcome ι) (hW : WellDefined E p x) (i : ι) (s r : ℝ)
    (hr : r ∈ Set.Icc (E.a i) (E.b i)) :
    reportUtility E p x i s r = interimUtility E p x i r + (s - r) * Q E p i r := by
  obtain ⟨hp, hx⟩ := (hW i).2.2 r hr
  have hbv := bvr_integrable_mul E i r hr _ hp
  unfold reportUtility interimUtility Q
  have hadd : ∫ t, (bidderValue E i (Function.update t i r) * p i (Function.update t i r) -
        x i (Function.update t i r) + (s - r) * p i (Function.update t i r)) ∂distribution E =
      (∫ t, (bidderValue E i (Function.update t i r) * p i (Function.update t i r) -
        x i (Function.update t i r)) ∂distribution E) +
        (s - r) * ∫ t, p i (Function.update t i r) ∂distribution E := by
    have hAX : Integrable (fun t => bidderValue E i (Function.update t i r) *
        p i (Function.update t i r) - x i (Function.update t i r)) (distribution E) := hbv.sub hx
    rw [integral_add hAX (hp.const_mul (s - r)), integral_const_mul]
  rw [← hadd]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [bv_update E i t s r]; ring

lemma U_ge {E : Environment ι} {p x : Outcome ι} (hF : Feasible E p x) (i : ι) {s r : ℝ}
    (hs : s ∈ Set.Icc (E.a i) (E.b i)) (hr : r ∈ Set.Icc (E.a i) (E.b i)) :
    interimUtility E p x i r + (s - r) * Q E p i r ≤ interimUtility E p x i s := by
  rw [← report_eq E p x hF.1 i s r hr]; exact hF.2.2.2 i s hs r hr

lemma monotoneQ_of_feasible {E : Environment ι} {p x : Outcome ι} (hF : Feasible E p x) :
    MonotoneQ E p := by
  intro i s hs r hr hsr
  rcases hsr.eq_or_lt with rfl | hlt
  · rfl
  have h1 := U_ge hF i hs hr
  have h2 := U_ge hF i hr hs
  have : (r - s) * Q E p i s ≤ (r - s) * Q E p i r := by linarith
  exact le_of_mul_le_mul_left this (by linarith)

omit [Fintype ι] [DecidableEq ι] in
lemma eq_of_incr_bound {a s : ℝ} (has : a ≤ s) (D Q : ℝ → ℝ)
    (h : ∀ r u, a ≤ r → r ≤ u → u ≤ s → |D u - D r| ≤ (u - r) * (Q u - Q r)) :
    D s = D a := by
  have key : ∀ n : ℕ, 0 < n → |D s - D a| ≤ (s - a) * (Q s - Q a) / n := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    set δ := (s - a) / n with hδ
    have hδ0 : 0 ≤ δ := div_nonneg (by linarith) hnR.le
    let r : ℕ → ℝ := fun k => a + k * δ
    have hrn : r n = s := by simp only [r, hδ]; field_simp; ring
    have hr0 : r 0 = a := by simp [r]
    have hstep : ∀ k, r (k + 1) - r k = δ := fun k => by simp only [r]; push_cast; ring
    have hle : ∀ k, k ≤ n → a ≤ r k ∧ r k ≤ s := by
      intro k hk
      refine ⟨by simp only [r]; nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)], ?_⟩
      have : (k : ℝ) * δ ≤ n * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hδ0
      have h2 : (n : ℝ) * δ = s - a := by rw [hδ]; field_simp
      simp only [r]; linarith
    have tel1 : D s - D a = ∑ k ∈ Finset.range n, (D (r (k + 1)) - D (r k)) := by
      rw [Finset.sum_range_sub (fun k => D (r k)), hrn, hr0]
    have tel2 : Q s - Q a = ∑ k ∈ Finset.range n, (Q (r (k + 1)) - Q (r k)) := by
      rw [Finset.sum_range_sub (fun k => Q (r k)), hrn, hr0]
    calc |D s - D a| = |∑ k ∈ Finset.range n, (D (r (k + 1)) - D (r k))| := by rw [tel1]
      _ ≤ ∑ k ∈ Finset.range n, |D (r (k + 1)) - D (r k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, δ * (Q (r (k + 1)) - Q (r k)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := Finset.mem_range.mp hk
          have h1 := hle k hk'.le
          have h2 := hle (k + 1) hk'
          have := h (r k) (r (k + 1)) h1.1 (by linarith [hstep k]) h2.2
          rwa [hstep k] at this
      _ = δ * (Q s - Q a) := by rw [← Finset.mul_sum, ← tel2]
      _ = (s - a) * (Q s - Q a) / n := by rw [hδ]; ring
  by_contra hne
  have hpos : 0 < |D s - D a| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (|(s - a) * (Q s - Q a)| / |D s - D a|)
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
    exact_mod_cast this
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hk := key n hn0
  have : (s - a) * (Q s - Q a) / n < |D s - D a| := by
    rw [div_lt_iff₀ hnpos]
    calc (s - a) * (Q s - Q a) ≤ |(s - a) * (Q s - Q a)| := le_abs_self _
      _ < |D s - D a| * n := by
          rw [div_lt_iff₀ hpos] at hn
          exact lt_of_lt_of_eq hn (mul_comm _ _)
  linarith

lemma envelope_of_feasible {E : Environment ι} {p x : Outcome ι} (hF : Feasible E p x) :
    EnvelopeAndBaseIR E p x := by
  refine ⟨fun i s hs => ?_, fun i => hF.2.2.1 i (E.a i) ⟨le_rfl, (E.a_lt_b i).le⟩⟩
  have hmono := monotoneQ_of_feasible hF i
  have hMon : MonotoneOn (Q E p i) (Set.Icc (E.a i) (E.b i)) :=
    fun s hs r hr h => hmono s hs r hr h
  have hint : ∀ u v, u ∈ Set.Icc (E.a i) (E.b i) → v ∈ Set.Icc (E.a i) (E.b i) →
      IntervalIntegrable (Q E p i) volume u v := fun u v hu hv =>
    (hMon.mono (Set.uIcc_subset_Icc hu hv)).intervalIntegrable
  have haI : E.a i ∈ Set.Icc (E.a i) (E.b i) := ⟨le_rfl, (E.a_lt_b i).le⟩
  let D : ℝ → ℝ := fun u => interimUtility E p x i u - ∫ r in E.a i..u, Q E p i r
  have key := eq_of_incr_bound hs.1 D (Q E p i) (fun r u har hru hus => by
    have hr : r ∈ Set.Icc (E.a i) (E.b i) := ⟨har, hru.trans (hus.trans hs.2)⟩
    have hu : u ∈ Set.Icc (E.a i) (E.b i) := ⟨har.trans hru, hus.trans hs.2⟩
    have h1 := U_ge hF i hu hr
    have h2 := U_ge hF i hr hu
    have hsplit : ∫ v in E.a i..u, Q E p i v =
        (∫ v in E.a i..r, Q E p i v) + ∫ v in r..u, Q E p i v :=
      (intervalIntegral.integral_add_adjacent_intervals (hint _ _ haI hr) (hint _ _ hr hu)).symm
    have hlo : (u - r) * Q E p i r ≤ ∫ v in r..u, Q E p i v := by
      have := intervalIntegral.integral_mono_on hru intervalIntegrable_const (hint r u hr hu)
        (fun v hv => hMon hr ⟨har.trans hv.1, hv.2.trans hu.2⟩ hv.1)
      simpa [intervalIntegral.integral_const, smul_eq_mul] using this
    have hhi : ∫ v in r..u, Q E p i v ≤ (u - r) * Q E p i u := by
      have := intervalIntegral.integral_mono_on hru (hint r u hr hu) intervalIntegrable_const
        (fun v hv => hMon ⟨har.trans hv.1, hv.2.trans hu.2⟩ hu hv.2)
      simpa [intervalIntegral.integral_const, smul_eq_mul] using this
    rw [abs_le]
    simp only [D]
    rw [hsplit]
    constructor <;> nlinarith)
  simp only [D, intervalIntegral.integral_same, sub_zero] at key
  linarith

/-- Child K1 (Myerson 1981, Lemma 2, necessity). -/
theorem K1 {E : Environment ι} {p x : Outcome ι} (hF : Feasible E p x) :
    MonotoneQ E p ∧ EnvelopeAndBaseIR E p x :=
  ⟨monotoneQ_of_feasible hF, envelope_of_feasible hF⟩


section K2

omit [DecidableEq ι] in
lemma ae_mu_Icc (E : Environment ι) (i : ι) : ∀ᵐ s ∂mu E i, s ∈ Set.Icc (E.a i) (E.b i) :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)

omit [DecidableEq ι] in
lemma aesm_mu {E : Environment ι} {i : ι} {ψ : ℝ → ℝ}
    (hψ : ContinuousOn ψ (Set.Icc (E.a i) (E.b i))) : AEStronglyMeasurable ψ (mu E i) :=
  (hψ.aestronglyMeasurable measurableSet_Icc).mono_ac (withDensity_absolutelyContinuous _ _)

omit [DecidableEq ι] in
lemma aesm_coord {E : Environment ι} (i : ι) {ψ : ℝ → ℝ} (hψ : AEStronglyMeasurable ψ (mu E i)) :
    AEStronglyMeasurable (fun t : ι → ℝ => ψ (t i)) (distribution E) := by
  rw [dist_eq_pi]; exact hψ.comp_measurePreserving (measurePreserving_eval _ i)

omit [DecidableEq ι] in
lemma integral_mu (E : Environment ι) (i : ι) (g : ℝ → ℝ) :
    ∫ s, g s ∂mu E i = ∫ s in Set.Icc (E.a i) (E.b i), E.f i s * g s := by
  rw [mu, integral_withDensity_eq_integral_toReal_smul₀]
  · refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    simp only [ENNReal.toReal_ofReal (E.f_pos i s hs).le, smul_eq_mul]
  · exact ENNReal.measurable_ofReal.comp_aemeasurable ((E.f_cont i).aemeasurable measurableSet_Icc)
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

omit [DecidableEq ι] in
lemma coord_mul_int {E : Environment ι} (j : ι) {ψ : ℝ → ℝ}
    (hψ : ContinuousOn ψ (Set.Icc (E.a j) (E.b j))) {φ : (ι → ℝ) → ℝ}
    (hφ : Integrable φ (distribution E)) :
    Integrable (fun t => ψ (t j) * φ t) (distribution E) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ
  refine hφ.bdd_mul (c := C) (aesm_coord j (aesm_mu hψ)) ?_
  filter_upwards [ae_support E] with t ht
  exact hC _ ((mem_support E).mp ht j)

omit [DecidableEq ι] in
lemma sv_mul_int {E : Environment ι} {φ : (ι → ℝ) → ℝ} (hφ : Integrable φ (distribution E)) :
    Integrable (fun t => sellerValue E t * φ t) (distribution E) := by
  have h : (fun t => sellerValue E t * φ t) =
      fun t => E.t0 * φ t + ∑ j, E.e j (t j) * φ t := by
    funext t; simp only [sellerValue, add_mul, Finset.sum_mul]
  rw [h]
  exact (hφ.const_mul _).add (integrable_finsetSum _ fun j _ => coord_mul_int j (E.e_cont j) hφ)

lemma bv_mul_int {E : Environment ι} (i : ι) {φ : (ι → ℝ) → ℝ}
    (hφ : Integrable φ (distribution E)) :
    Integrable (fun t => bidderValue E i t * φ t) (distribution E) := by
  have h : (fun t => bidderValue E i t * φ t) =
      fun t => t i * φ t + ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), E.e j (t j) * φ t := by
    funext t; simp only [bidderValue, add_mul, Finset.sum_mul]
  rw [h]
  exact (coord_mul_int i continuousOn_id hφ).add
    (integrable_finsetSum _ fun j _ => coord_mul_int j (E.e_cont j) hφ)

lemma bv_sub_sv (E : Environment ι) (i : ι) (t : ι → ℝ) :
    bidderValue E i t - sellerValue E t = t i - E.e i (t i) - E.t0 := by
  simp only [bidderValue, sellerValue]
  rw [Finset.filter_ne' Finset.univ i, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  ring

omit [DecidableEq ι] in
lemma F_contOn (E : Environment ι) (i : ι) : ContinuousOn (F E i) (Set.Icc (E.a i) (E.b i)) := by
  have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := E.a i)
    (b := E.b i) (f := E.f i)
    (by rw [Set.uIcc_of_le (E.a_lt_b i).le]; exact (E.f_cont i).integrableOn_Icc)
  rw [Set.uIcc_of_le (E.a_lt_b i).le] at h
  exact h

omit [DecidableEq ι] in
lemma vv_contOn (E : Environment ι) (i : ι) :
    ContinuousOn (virtualValue E i) (Set.Icc (E.a i) (E.b i)) := by
  have h2 : virtualValue E i = fun s => s - E.e i s - (1 - F E i s) / E.f i s := rfl
  rw [h2]
  exact (continuousOn_id.sub (E.e_cont i)).sub ((continuousOn_const.sub (F_contOn E i)).div
    (E.f_cont i) fun s hs => (E.f_pos i s hs).ne')

omit [Fintype ι] [DecidableEq ι] in
/-- Fubini on the triangle `r ≤ s`. -/
lemma triangle {a b : ℝ} (f Q : ℝ → ℝ) (hf : IntegrableOn f (Set.Icc a b))
    (hQ : IntegrableOn Q (Set.Icc a b)) :
    ∫ s in Set.Icc a b, f s * ∫ r in a..s, Q r =
      ∫ r in Set.Icc a b, (∫ s in r..b, f s) * Q r := by
  let K : ℝ × ℝ → ℝ := {z | z.2 ≤ z.1}.indicator (fun z => f z.1 * Q z.2)
  have hK : Integrable K ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc a b))) :=
    (Integrable.mul_prod hf hQ).indicator (measurableSet_le measurable_snd measurable_fst)
  have hL : ∀ s ∈ Set.Icc a b, f s * ∫ r in a..s, Q r = ∫ r in Set.Icc a b, K (s, r) := by
    intro s hs
    have h1 : ∫ r in a..s, Q r = ∫ r in Set.Icc a b, (Set.Iic s).indicator Q r := by
      rw [setIntegral_indicator measurableSet_Iic, intervalIntegral.integral_of_le hs.1,
        ← integral_Icc_eq_integral_Ioc]
      congr 2
      ext r; simp only [Set.mem_Icc, Set.mem_inter_iff, Set.mem_Iic]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hs.2⟩, h2⟩
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    rw [h1, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [K, Set.indicator, Set.mem_Iic, Set.mem_ofPred_eq]
    split_ifs <;> simp
  have hR : ∀ r ∈ Set.Icc a b, (∫ s in r..b, f s) * Q r = ∫ s in Set.Icc a b, K (s, r) := by
    intro r hr
    have h1 : ∫ s in r..b, f s = ∫ s in Set.Icc a b, (Set.Ici r).indicator f s := by
      rw [setIntegral_indicator measurableSet_Ici, intervalIntegral.integral_of_le hr.2,
        ← integral_Icc_eq_integral_Ioc]
      congr 2
      ext s; simp only [Set.mem_Icc, Set.mem_inter_iff, Set.mem_Ici]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨hr.1.trans h1, h2⟩, h1⟩
      · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
    rw [h1, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [K, Set.indicator, Set.mem_Ici, Set.mem_ofPred_eq]
    split_ifs <;> simp
  rw [setIntegral_congr_fun measurableSet_Icc hL, setIntegral_congr_fun measurableSet_Icc hR]
  exact integral_integral_swap (f := fun s r => K (s, r)) hK

lemma per_i {E : Environment ι} {p x : Outcome ι} (hW : WellDefined E p x)
    (hEnv : EnvelopeAndBaseIR E p x) (hMQ : MonotoneQ E p) (i : ι) :
    ∫ t, (x i t - sellerValue E t * p i t) ∂distribution E =
      ∫ t, (virtualValue E i (t i) - E.t0) * p i t ∂distribution E -
        interimUtility E p x i (E.a i) := by
  have hp := (hW i).1
  have hx := (hW i).2.1
  have hab := (E.a_lt_b i).le
  have hQmono : MonotoneOn (Q E p i) (Set.Icc (E.a i) (E.b i)) := fun s hs r hr h => hMQ i s hs r hr h
  have hQint : IntegrableOn (Q E p i) (Set.Icc (E.a i) (E.b i)) := hQmono.integrableOn_isCompact isCompact_Icc
  have hfint : IntegrableOn (E.f i) (Set.Icc (E.a i) (E.b i)) := (E.f_cont i).integrableOn_Icc
  -- integrability of the pieces
  have hbvp : Integrable (fun t => bidderValue E i t * p i t - x i t) (distribution E) :=
    (bv_mul_int i hp).sub hx
  have hlin : ContinuousOn (fun s => s - E.e i s - E.t0) (Set.Icc (E.a i) (E.b i)) :=
    (continuousOn_id.sub (E.e_cont i)).sub continuousOn_const
  have hcoord : Integrable (fun t => (t i - E.e i (t i) - E.t0) * p i t) (distribution E) :=
    coord_mul_int i hlin hp
  have hvv : Integrable (fun t => (virtualValue E i (t i) - E.t0) * p i t) (distribution E) :=
    coord_mul_int i ((vv_contOn E i).sub continuousOn_const) hp
  -- (A)
  have hA : ∫ t, (x i t - sellerValue E t * p i t) ∂distribution E =
      ∫ t, (t i - E.e i (t i) - E.t0) * p i t ∂distribution E -
        ∫ t, (bidderValue E i t * p i t - x i t) ∂distribution E := by
    rw [← integral_sub hcoord hbvp]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have := bv_sub_sv E i t
    simp only
    rw [← this]; ring
  -- (C) and (D) and (E) via Fubini over coordinate i
  have hC : ∫ t, (t i - E.e i (t i) - E.t0) * p i t ∂distribution E =
      ∫ s, (s - E.e i s - E.t0) * Q E p i s ∂mu E i := by
    rw [integral_update E i _ hcoord]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [Function.update_self, Q]
    rw [integral_const_mul]
  have hD : ∫ t, (bidderValue E i t * p i t - x i t) ∂distribution E =
      ∫ s, interimUtility E p x i s ∂mu E i := by
    rw [integral_update E i _ hbvp]; rfl
  have hE : ∫ t, (virtualValue E i (t i) - E.t0) * p i t ∂distribution E =
      ∫ s, (virtualValue E i s - E.t0) * Q E p i s ∂mu E i := by
    rw [integral_update E i _ hvv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [Function.update_self, Q]
    rw [integral_const_mul]
  -- move to Lebesgue integrals on Icc
  rw [hA, hC, hD, hE, integral_mu, integral_mu, integral_mu]
  have i1 : IntegrableOn (fun s => E.f i s * ((s - E.e i s - E.t0) * Q E p i s)) (Set.Icc (E.a i) (E.b i)) := by
    have := hQint.continuousOn_mul ((E.f_cont i).mul hlin) isCompact_Icc
    refine this.congr_fun (fun s _ => by simp only [Pi.mul_apply]; ring) measurableSet_Icc
  have i2 : IntegrableOn (fun s => (1 - F E i s) * Q E p i s) (Set.Icc (E.a i) (E.b i)) :=
    hQint.continuousOn_mul (continuousOn_const.sub (F_contOn E i)) isCompact_Icc
  have hF' : ∫ s in (Set.Icc (E.a i) (E.b i)), E.f i s * ((virtualValue E i s - E.t0) * Q E p i s) =
      (∫ s in (Set.Icc (E.a i) (E.b i)), E.f i s * ((s - E.e i s - E.t0) * Q E p i s)) -
        ∫ s in (Set.Icc (E.a i) (E.b i)), (1 - F E i s) * Q E p i s := by
    have h := integral_sub i1 i2
    beta_reduce at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    have hf0 := (E.f_pos i s hs).ne'
    simp only [virtualValue]
    field_simp
    ring
  -- envelope: U = U(a) + ∫ Q on Icc
  have hV : IntegrableOn (fun s => E.f i s * ∫ r in E.a i..s, Q E p i r) (Set.Icc (E.a i) (E.b i)) := by
    refine IntegrableOn.continuousOn_mul (g := E.f i) ?_ ?_ isCompact_Icc |>.congr_fun
      (fun _ _ => rfl) measurableSet_Icc
    · exact (E.f_cont i)
    · have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := E.a i)
        (b := E.b i) (f := Q E p i) (by rw [Set.uIcc_of_le hab]; exact hQint)
      rw [Set.uIcc_of_le hab] at this
      exact this.integrableOn_Icc
  have hG' : ∫ s in (Set.Icc (E.a i) (E.b i)), E.f i s * interimUtility E p x i s =
      interimUtility E p x i (E.a i) + ∫ s in (Set.Icc (E.a i) (E.b i)), (1 - F E i s) * Q E p i s := by
    have e1 : ∫ s in (Set.Icc (E.a i) (E.b i)), E.f i s * interimUtility E p x i s =
        ∫ s in (Set.Icc (E.a i) (E.b i)), (interimUtility E p x i (E.a i) * E.f i s +
          E.f i s * ∫ r in E.a i..s, Q E p i r) := by
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      rw [hEnv.1 i s hs]; ring
    have hfI : ∫ s in (Set.Icc (E.a i) (E.b i)), E.f i s = 1 := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, E.f_int i]
    rw [e1, integral_add (hfint.const_mul _) hV, integral_const_mul, hfI, mul_one,
      triangle _ _ hfint hQint]
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    congr 1
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hfint.mono_set (Set.uIcc_subset_Icc ⟨le_rfl, hab⟩ hr)).intervalIntegrable
      (hfint.mono_set (Set.uIcc_subset_Icc hr ⟨hab, le_rfl⟩)).intervalIntegrable
    rw [E.f_int i] at hsplit
    simp only [F]
    linarith
  rw [hF', hG']
  ring

/-- Child K2 (Myerson 1981, Lemma 3, eq. (4.7)). -/
theorem K2 {E : Environment ι} {p x : Outcome ι} (hW : WellDefined E p x)
    (hEnv : EnvelopeAndBaseIR E p x) (hMQ : MonotoneQ E p) :
    sellerUtility E p x = (∫ t, sellerValue E t ∂distribution E) + virtualObjective E p -
      ∑ i, interimUtility E p x i (E.a i) := by
  have hsv : Integrable (fun t => sellerValue E t) (distribution E) := by
    simpa using sv_mul_int (E := E) (φ := fun _ => (1 : ℝ)) (integrable_const _)
  have hterm : ∀ i, Integrable (fun t => x i t - sellerValue E t * p i t) (distribution E) :=
    fun i => (hW i).2.1.sub (sv_mul_int (hW i).1)
  have hvv : ∀ i, Integrable (fun t => (virtualValue E i (t i) - E.t0) * p i t)
      (distribution E) :=
    fun i => coord_mul_int i ((vv_contOn E i).sub continuousOn_const) (hW i).1
  have h1 : sellerUtility E p x =
      ∫ t, (sellerValue E t + ∑ i, (x i t - sellerValue E t * p i t)) ∂distribution E := by
    unfold sellerUtility
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [h1, integral_add hsv (integrable_finsetSum _ fun i _ => hterm i),
    integral_finsetSum _ fun i _ => hterm i]
  unfold virtualObjective
  rw [integral_finsetSum _ fun i _ => hvv i]
  simp only [per_i hW hEnv hMQ, Finset.sum_sub_distrib]
  ring

end K2


open Set

section DBlock


/-- The candidate set of the two-point convex envelope (same formula as `G`). -/
def Gset (H : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {z : ℝ | ∃ w r₁ r₂ : ℝ, w ∈ Icc 0 1 ∧ r₁ ∈ Icc 0 1 ∧ r₂ ∈ Icc 0 1 ∧
    w * r₁ + (1 - w) * r₂ = q ∧ z = w * H r₁ + (1 - w) * H r₂}

def Genv (H : ℝ → ℝ) (q : ℝ) : ℝ := sInf (Gset H q)

variable {H : ℝ → ℝ}

lemma Gset_nonempty {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) : (Gset H q).Nonempty :=
  ⟨H q, 1, q, q, ⟨zero_le_one, le_rfl⟩, hq, hq, by ring, by ring⟩

lemma Gset_bdd {M : ℝ} (hM : ∀ r ∈ Icc (0:ℝ) 1, -M ≤ H r) (q : ℝ) : BddBelow (Gset H q) := by
  refine ⟨-M, ?_⟩
  rintro z ⟨w, r1, r2, hw, hr1, hr2, -, rfl⟩
  nlinarith [mul_le_mul_of_nonneg_left (hM r1 hr1) hw.1,
    mul_le_mul_of_nonneg_left (hM r2 hr2) (sub_nonneg.2 hw.2)]

lemma Genv_le {q : ℝ} (hb : BddBelow (Gset H q)) (hq : q ∈ Icc (0:ℝ) 1) : Genv H q ≤ H q :=
  csInf_le hb ⟨1, q, q, ⟨zero_le_one, le_rfl⟩, hq, hq, by ring, by ring⟩

lemma le_Genv_of_affine {α β q : ℝ} (hℓ : ∀ r ∈ Icc (0:ℝ) 1, α + β * r ≤ H r)
    (hq : q ∈ Icc (0:ℝ) 1) : α + β * q ≤ Genv H q := by
  refine le_csInf (Gset_nonempty hq) ?_
  rintro z ⟨w, r1, r2, hw, hr1, hr2, hq', rfl⟩
  rw [← hq']
  nlinarith [mul_le_mul_of_nonneg_left (hℓ r1 hr1) hw.1,
    mul_le_mul_of_nonneg_left (hℓ r2 hr2) (sub_nonneg.2 hw.2)]

lemma Genv_zero (hb : BddBelow (Gset H 0)) : Genv H 0 = H 0 := by
  refine le_antisymm (Genv_le hb ⟨le_rfl, zero_le_one⟩) (le_csInf (Gset_nonempty ⟨le_rfl, zero_le_one⟩) ?_)
  rintro z ⟨w, r1, r2, hw, hr1, hr2, hq', rfl⟩
  have h1 : w * r1 = 0 := by nlinarith [mul_nonneg hw.1 hr1.1, mul_nonneg (sub_nonneg.2 hw.2) hr2.1]
  have h2 : (1 - w) * r2 = 0 := by nlinarith [mul_nonneg hw.1 hr1.1, mul_nonneg (sub_nonneg.2 hw.2) hr2.1]
  have e1 : w * H r1 = w * H 0 := by
    rcases mul_eq_zero.1 h1 with h | h <;> simp [h]
  have e2 : (1 - w) * H r2 = (1 - w) * H 0 := by
    rcases mul_eq_zero.1 h2 with h | h <;> simp [h]
  rw [e1, e2]; ring_nf; exact le_rfl

lemma Genv_one (hb : BddBelow (Gset H 1)) : Genv H 1 = H 1 := by
  refine le_antisymm (Genv_le hb ⟨zero_le_one, le_rfl⟩) (le_csInf (Gset_nonempty ⟨zero_le_one, le_rfl⟩) ?_)
  rintro z ⟨w, r1, r2, hw, hr1, hr2, hq', rfl⟩
  have h1 : w * (1 - r1) = 0 := by
    nlinarith [mul_nonneg hw.1 (sub_nonneg.2 hr1.2), mul_nonneg (sub_nonneg.2 hw.2) (sub_nonneg.2 hr2.2)]
  have h2 : (1 - w) * (1 - r2) = 0 := by
    nlinarith [mul_nonneg hw.1 (sub_nonneg.2 hr1.2), mul_nonneg (sub_nonneg.2 hw.2) (sub_nonneg.2 hr2.2)]
  have e1 : w * H r1 = w * H 1 := by
    rcases mul_eq_zero.1 h1 with h | h
    · simp [h]
    · rw [show r1 = 1 by linarith]
  have e2 : (1 - w) * H r2 = (1 - w) * H 1 := by
    rcases mul_eq_zero.1 h2 with h | h
    · simp [h]
    · rw [show r2 = 1 by linarith]
  rw [e1, e2]; ring_nf; exact le_rfl

/-- Chord bound. -/
lemma Genv_le_chord {l r q : ℝ} (hb : BddBelow (Gset H q)) (hl : l ∈ Icc (0:ℝ) 1)
    (hr : r ∈ Icc (0:ℝ) 1) (hlq : l ≤ q) (hqr : q ≤ r) (hlr : l < r) :
    Genv H q * (r - l) ≤ (r - q) * H l + (q - l) * H r := by
  have hd : 0 < r - l := sub_pos.2 hlr
  have key : Genv H q ≤ (r - q) / (r - l) * H l + (1 - (r - q) / (r - l)) * H r :=
    csInf_le hb ⟨(r - q) / (r - l), l, r,
      ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).2 (by linarith)⟩, hl, hr,
      by field_simp; ring, rfl⟩
  have e : (r - q) / (r - l) * H l + (1 - (r - q) / (r - l)) * H r =
      ((r - q) * H l + (q - l) * H r) / (r - l) := by field_simp; ring
  rw [e, le_div_iff₀ hd] at key
  exact key

/-- Finite reduction: any convex combination dominates the envelope. -/
lemma Genv_le_finite {κ : Type} [Fintype κ] (c p : κ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hsum : ∑ k, c k = 1) (hp : ∀ k, p k ∈ Icc (0:ℝ) 1) {q : ℝ} (hq : ∑ k, c k * p k = q)
    (hb : BddBelow (Gset H q)) : Genv H q ≤ ∑ k, c k * H (p k) := by
  classical
  set V := ∑ k, c k * H (p k)
  set g := Genv H q
  -- left/right indicators
  let L : κ → ℝ := fun k => if p k ≤ q then c k else 0
  let R : κ → ℝ := fun k => if p k ≤ q then 0 else c k
  have hLR : ∀ k, L k + R k = c k := fun k => by simp only [L, R]; split_ifs <;> ring
  have hL0 : ∀ k, 0 ≤ L k := fun k => by simp only [L]; split_ifs; exacts [hc k, le_rfl]
  have hR0 : ∀ k, 0 ≤ R k := fun k => by simp only [R]; split_ifs; exacts [le_rfl, hc k]
  set D := ∑ j, R j * (p j - q)
  have hbal : ∑ k, L k * (q - p k) = D := by
    have h0 : ∑ k, c k * (q - p k) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, hq]; ring
    have : ∑ k, c k * (q - p k) = ∑ k, L k * (q - p k) - D := by
      simp only [D, ← hLR, add_mul, Finset.sum_add_distrib]
      rw [← sub_eq_zero]
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      ring_nf
      refine Finset.sum_eq_zero fun k _ => by ring
    linarith
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun j _ => by
    simp only [R]; split_ifs with h
    · simp
    · exact mul_nonneg (hc j) (by linarith [not_le.mp h])
  -- the double sum
  have hterm : ∀ k j, L k * R j * (g * (p j - p k)) ≤
      L k * R j * ((p j - q) * H (p k) + (q - p k) * H (p j)) := by
    intro k j
    simp only [L, R]
    split_ifs with hk hj
    · simp
    · exact mul_le_mul_of_nonneg_left
        (by have := Genv_le_chord hb (hp k) (hp j) hk (not_le.mp hj).le
              (lt_of_le_of_lt hk (not_le.mp hj)); linarith)
        (mul_nonneg (hc k) (hc j))
    · simp
    · simp
  have hsumT := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm k j
  have lhs : ∑ k, ∑ j, L k * R j * (g * (p j - p k)) = g * D := by
    have : ∀ k j, L k * R j * (g * (p j - p k)) =
        g * (L k * (R j * (p j - q)) + R j * (L k * (q - p k))) := fun k j => by ring
    simp only [this, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [hbal]
    have hc1 : ∑ k, L k + ∑ j, R j = 1 := by rw [← Finset.sum_add_distrib]; simp [hLR, hsum]
    have hD : ∑ i, R i * (p i - q) = D := rfl
    rw [hD]
    calc g * ((∑ k, L k) * D + (∑ j, R j) * D) = g * ((∑ k, L k + ∑ j, R j) * D) := by ring
      _ = g * D := by rw [hc1, one_mul]
  have rhs : ∑ k, ∑ j, L k * R j * ((p j - q) * H (p k) + (q - p k) * H (p j)) = D * V := by
    have : ∀ k j, L k * R j * ((p j - q) * H (p k) + (q - p k) * H (p j)) =
        (L k * H (p k)) * (R j * (p j - q)) + (R j * H (p j)) * (L k * (q - p k)) :=
      fun k j => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [hbal]
    have hV : V = ∑ k, L k * H (p k) + ∑ k, R k * H (p k) := by
      simp only [V, ← Finset.sum_add_distrib, ← add_mul, hLR]
    have hD : ∑ i, R i * (p i - q) = D := rfl
    rw [hV, hD]; ring
  rw [lhs, rhs] at hsumT
  rcases hD0.lt_or_eq with hDpos | hDz
  · nlinarith
  · -- degenerate: all mass at q
    have hRz : ∀ j, R j * (p j - q) = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ?_)).1 hDz.symm
      · exact fun j => this j (Finset.mem_univ j)
      · simp only [R]; split_ifs with h
        · simp
        · exact mul_nonneg (hc j) (by linarith [not_le.mp h])
    have hLz : ∀ k, L k * (q - p k) = 0 := by
      have h2 : ∑ k, L k * (q - p k) = 0 := by rw [hbal, ← hDz]
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => ?_)).1 h2
      · exact fun k => this k (Finset.mem_univ k)
      · simp only [L]; split_ifs with h
        · exact mul_nonneg (hc k) (by linarith)
        · simp
    have hV : V = H q := by
      have : ∀ k, c k * H (p k) = c k * H q := by
        intro k
        have h1 := hLz k
        have h2 := hRz k
        simp only [L, R] at h1 h2
        split_ifs at h1 h2 with h
        · rcases mul_eq_zero.1 h1 with h' | h'
          · simp [h']
          · rw [show p k = q by linarith]
        · rcases mul_eq_zero.1 h2 with h' | h'
          · simp [h']
          · rw [show p k = q by linarith]
      simp only [V, this, ← Finset.sum_mul, hsum, one_mul]
    have hqI : q ∈ Icc (0:ℝ) 1 := by
      rw [← hq]
      constructor
      · exact Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (hp k).1
      · calc ∑ k, c k * p k ≤ ∑ k, c k * 1 :=
              Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hp k).2 (hc k)
          _ = 1 := by simp [hsum]
    rw [hV]; exact Genv_le hb hqI

/-! ### D2: convexity -/

lemma Genv_convex (hb : ∀ q, BddBelow (Gset H q)) : ConvexOn ℝ (Icc 0 1) (Genv H) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb' hab
  simp only [smul_eq_mul]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨z1, ⟨w1, x1, x2, hw1, hx1, hx2, hxq, rfl⟩, hz1⟩ :=
    exists_lt_of_csInf_lt (Gset_nonempty (H := H) hx) (lt_add_of_pos_right (Genv H x) hε)
  obtain ⟨z2, ⟨w2, y1, y2, hw2, hy1, hy2, hyq, rfl⟩, hz2⟩ :=
    exists_lt_of_csInf_lt (Gset_nonempty (H := H) hy) (lt_add_of_pos_right (Genv H y) hε)
  let c : Fin 4 → ℝ := ![a * w1, a * (1 - w1), b * w2, b * (1 - w2)]
  let p : Fin 4 → ℝ := ![x1, x2, y1, y2]
  have hc : ∀ k, 0 ≤ c k := by
    intro k
    fin_cases k
    · exact mul_nonneg ha hw1.1
    · exact mul_nonneg ha (sub_nonneg.2 hw1.2)
    · exact mul_nonneg hb' hw2.1
    · exact mul_nonneg hb' (sub_nonneg.2 hw2.2)
  have hsum : ∑ k, c k = 1 := by
    simp only [c, Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination hab
  have hp : ∀ k, p k ∈ Icc (0:ℝ) 1 := by
    intro k
    fin_cases k
    exacts [hx1, hx2, hy1, hy2]
  have hq : ∑ k, c k * p k = a * x + b * y := by
    simp only [c, p, Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination a * hxq + b * hyq
  have key := Genv_le_finite (H := H) c p hc hsum hp hq (hb _)
  simp only [c, p, Fin.sum_univ_four] at key
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at key
  have e1 := mul_le_mul_of_nonneg_left hz1.le ha
  have e2 := mul_le_mul_of_nonneg_left hz2.le hb'
  have e3 : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
  nlinarith

/-! ### D3: one-sided derivatives -/

lemma hasDerivWithinAt_Ioi_of_bdd {S : Set ℝ} {f : ℝ → ℝ} {x c : ℝ} (hfc : ConvexOn ℝ S f)
    (hx : x ∈ S) (hxc : x < c) (hIoo : Ioo x c ⊆ S) (hbdd : BddBelow (slope f x '' Ioo x c)) :
    HasDerivWithinAt f (sInf (slope f x '' Ioo x c)) (Ioi x) x := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Ioi, lt_self_iff_false, not_false_eq_true, sdiff_singleton_eq_self]
  exact ((hfc.monotoneOn_slope_gt hx).mono fun z hz => ⟨hIoo hz, hz.1⟩).tendsto_nhdsWithin_Ioo_right
    (nonempty_Ioo.2 hxc) hbdd

lemma hasDerivWithinAt_Iio_of_bdd {S : Set ℝ} {f : ℝ → ℝ} {x c : ℝ} (hfc : ConvexOn ℝ S f)
    (hx : x ∈ S) (hcx : c < x) (hIoo : Ioo c x ⊆ S) (hbdd : BddAbove (slope f x '' Ioo c x)) :
    HasDerivWithinAt f (sSup (slope f x '' Ioo c x)) (Iio x) x := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Iio, lt_self_iff_false, not_false_eq_true, sdiff_singleton_eq_self]
  exact ((hfc.monotoneOn_slope_lt hx).mono fun z hz => ⟨hIoo hz, hz.2⟩).tendsto_nhdsWithin_Ioo_left
    (nonempty_Ioo.2 hcx) hbdd

variable (H) in
/-- Same formula as `g`: right derivative on `[0,1)`, left derivative at `1`. -/
def gEnv (q : ℝ) : ℝ :=
  if q < 1 then derivWithin (Genv H) (Ioi q) q else derivWithin (Genv H) (Iio 1) 1

lemma Genv_hasDerivRight {M : ℝ} (hb : ∀ q, BddBelow (Gset H q))
    (hL0 : ∀ r ∈ Icc (0:ℝ) 1, H 0 - M * r ≤ H r) {q : ℝ} (hq : q ∈ Ico (0:ℝ) 1) :
    HasDerivWithinAt (Genv H) (gEnv H q) (Ioi q) q := by
  have hconv := Genv_convex hb
  have hd : DifferentiableWithinAt ℝ (Genv H) (Ioi q) q := by
    rcases hq.1.eq_or_lt with h0 | hq0
    · subst h0
      refine (hasDerivWithinAt_Ioi_of_bdd hconv ⟨le_rfl, zero_le_one⟩ zero_lt_one
        Ioo_subset_Icc_self ⟨-M, ?_⟩).differentiableWithinAt
      rintro _ ⟨y, hy, rfl⟩
      rw [slope_def_field, sub_zero, le_div_iff₀ hy.1]
      have := le_Genv_of_affine (H := H) (α := H 0) (β := -M)
        (fun r hr => by linarith [hL0 r hr]) (Ioo_subset_Icc_self hy)
      rw [Genv_zero (hb 0)]; linarith
    · exact hconv.differentiableWithinAt_Ioi_of_mem_interior (by rw [interior_Icc]; exact ⟨hq0, hq.2⟩)
  unfold gEnv; rw [if_pos hq.2]; exact hd.hasDerivWithinAt

lemma Genv_hasDerivLeft1 {M : ℝ} (hb : ∀ q, BddBelow (Gset H q))
    (hL1 : ∀ r ∈ Icc (0:ℝ) 1, H 1 - M * (1 - r) ≤ H r) :
    HasDerivWithinAt (Genv H) (gEnv H 1) (Iio 1) 1 := by
  have hconv := Genv_convex hb
  have hd : DifferentiableWithinAt ℝ (Genv H) (Iio 1) 1 := by
    refine (hasDerivWithinAt_Iio_of_bdd hconv ⟨zero_le_one, le_rfl⟩ zero_lt_one
      Ioo_subset_Icc_self ⟨M, ?_⟩).differentiableWithinAt
    rintro _ ⟨y, hy, rfl⟩
    rw [slope_def_field, div_le_iff_of_neg (by linarith [hy.2])]
    have := le_Genv_of_affine (H := H) (α := H 1 - M) (β := M)
      (fun r hr => by linarith [hL1 r hr]) (Ioo_subset_Icc_self hy)
    rw [Genv_one (hb 1)]; linarith
  unfold gEnv; rw [if_neg (lt_irrefl 1)]; exact hd.hasDerivWithinAt

lemma gEnv_mono {M : ℝ} (hb : ∀ q, BddBelow (Gset H q))
    (hL0 : ∀ r ∈ Icc (0:ℝ) 1, H 0 - M * r ≤ H r)
    (hL1 : ∀ r ∈ Icc (0:ℝ) 1, H 1 - M * (1 - r) ≤ H r) :
    MonotoneOn (gEnv H) (Icc 0 1) := by
  have hconv := Genv_convex hb
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with h | hlt
  · rw [h]
  have hx1 : x < 1 := hlt.trans_le hy.2
  have h1 : gEnv H x ≤ slope (Genv H) x y :=
    hconv.le_slope_of_hasDerivWithinAt_Ioi hx hy hlt (Genv_hasDerivRight hb hL0 ⟨hx.1, hx1⟩)
  refine h1.trans ?_
  rcases hy.2.eq_or_lt with h | hy1
  · subst h
    exact hconv.slope_le_of_hasDerivWithinAt_Iio hx hy hlt (Genv_hasDerivLeft1 hb hL1)
  · have hd := Genv_hasDerivRight hb hL0 ⟨hy.1, hy1⟩
    rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi] at hd
    apply ge_of_tendsto hd
    filter_upwards [Ioo_mem_nhdsGT hy1] with z hz
    rw [slope_def_field, slope_def_field]
    exact hconv.slope_mono_adjacent hx ⟨hy.1.trans hz.1.le, hz.2.le⟩ hlt hz.1

lemma Genv_contOn {M : ℝ} (hb : ∀ q, BddBelow (Gset H q))
    (hL0 : ∀ r ∈ Icc (0:ℝ) 1, H 0 - M * r ≤ H r)
    (hL1 : ∀ r ∈ Icc (0:ℝ) 1, H 1 - M * (1 - r) ≤ H r) :
    ContinuousOn (Genv H) (Icc 0 1) := by
  have hconv := Genv_convex hb
  intro x hx
  rcases hx.1.eq_or_lt with h0 | hx0
  · subst h0
    have := (Genv_hasDerivRight hb hL0 ⟨le_rfl, zero_lt_one⟩).continuousWithinAt
    rw [continuousWithinAt_Ioi_iff_Ici] at this
    exact this.mono Icc_subset_Ici_self
  rcases hx.2.eq_or_lt with h1 | hx1
  · subst h1
    have := (Genv_hasDerivLeft1 hb hL1).continuousWithinAt
    rw [continuousWithinAt_Iio_iff_Iic] at this
    exact this.mono Icc_subset_Iic_self
  have hint : x ∈ interior (Icc (0:ℝ) 1) := by rw [interior_Icc]; exact ⟨hx0, hx1⟩
  refine ContinuousAt.continuousWithinAt ?_
  rw [continuousAt_iff_continuous_left'_right']
  exact ⟨(hconv.hasDerivWithinAt_leftDeriv_of_mem_interior hint).continuousWithinAt,
    (hconv.hasDerivWithinAt_rightDeriv_of_mem_interior hint).continuousWithinAt⟩

/-! ### D4: where `G < H`, `G` is affine and `gEnv` is locally constant -/

/-- Chord inequality for convex functions. -/
lemma convex_chord {S : Set ℝ} {f : ℝ → ℝ} (hfc : ConvexOn ℝ S f) {x y z : ℝ}
    (hx : x ∈ S) (hz : z ∈ S) (hxy : x < y) (hyz : y < z) :
    f y * (z - x) ≤ (z - y) * f x + (y - x) * f z := by
  have h := hfc.slope_mono_adjacent hx hz hxy hyz
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at h
  nlinarith

lemma Genv_mem (hHc : ContinuousOn H (Icc 0 1)) {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    Genv H q ∈ Gset H q := by
  let K : Set (ℝ × ℝ × ℝ) := (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) ∩
    {z | z.1 * z.2.1 + (1 - z.1) * z.2.2 = q}
  let Φ : ℝ × ℝ × ℝ → ℝ := fun z => z.1 * H z.2.1 + (1 - z.1) * H z.2.2
  have hK : IsCompact K :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).inter_right
      (isClosed_eq (by fun_prop) continuous_const)
  have hΦ : ContinuousOn Φ K := by
    have h1 : ContinuousOn (fun z : ℝ × ℝ × ℝ => H z.2.1) K :=
      hHc.comp (by fun_prop) (fun z hz => hz.1.2.1)
    have h2 : ContinuousOn (fun z : ℝ × ℝ × ℝ => H z.2.2) K :=
      hHc.comp (by fun_prop) (fun z hz => hz.1.2.2)
    exact (continuousOn_fst.mul h1).add ((continuousOn_const.sub continuousOn_fst).mul h2)
  have hset : Gset H q = Φ '' K := by
    ext z
    constructor
    · rintro ⟨w, r1, r2, hw, hr1, hr2, hq', rfl⟩
      exact ⟨(w, r1, r2), ⟨⟨hw, hr1, hr2⟩, hq'⟩, rfl⟩
    · rintro ⟨⟨w, r1, r2⟩, ⟨⟨hw, hr1, hr2⟩, hq'⟩, rfl⟩
      exact ⟨w, r1, r2, hw, hr1, hr2, hq', rfl⟩
  have hne : (Gset H q).Nonempty := Gset_nonempty hq
  show sInf (Gset H q) ∈ Gset H q
  rw [hset] at hne ⊢
  exact (hK.image_of_continuousOn hΦ).sInf_mem hne

lemma Genv_affine_piece (hHc : ContinuousOn H (Icc 0 1))
    {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (hlt : Genv H q < H q) :
    ∃ l r : ℝ, l ∈ Icc (0:ℝ) 1 ∧ r ∈ Icc (0:ℝ) 1 ∧ l < q ∧ q < r ∧
      Genv H q * (r - l) = (r - q) * H l + (q - l) * H r := by
  obtain ⟨w, r1, r2, hw, hr1, hr2, hqw, hv⟩ := Genv_mem hHc hq
  have side : ∀ (w r1 r2 : ℝ), w ∈ Icc (0:ℝ) 1 → w * r1 + (1 - w) * r2 = q →
      Genv H q = w * H r1 + (1 - w) * H r2 → r1 < r2 →
      r1 < q ∧ q < r2 ∧ Genv H q * (r2 - r1) = (r2 - q) * H r1 + (q - r1) * H r2 := by
    intro w r1 r2 hw hqw hv h12
    have e1 : (1 - w) * (r2 - r1) = q - r1 := by linear_combination hqw
    have e2 : w * (r2 - r1) = r2 - q := by linear_combination -hqw
    refine ⟨?_, ?_, by linear_combination (r2 - r1) * hv + (H r2 - H r1) * hqw⟩
    · by_contra hc
      have : (1 - w) * (r2 - r1) ≤ 0 := by linarith [not_lt.1 hc]
      have hw1 : 1 - w ≤ 0 := by
        by_contra h'; nlinarith [mul_pos (not_le.1 h') (sub_pos.2 h12)]
      have hw' : w = 1 := le_antisymm hw.2 (by linarith)
      subst hw'
      have : r1 = q := by linarith
      subst this
      rw [hv] at hlt; simp at hlt
    · by_contra hc
      have : w * (r2 - r1) ≤ 0 := by linarith [not_lt.1 hc]
      have hw0 : w ≤ 0 := by
        by_contra h'; nlinarith [mul_pos (not_le.1 h') (sub_pos.2 h12)]
      have hw' : w = 0 := le_antisymm hw0 hw.1
      subst hw'
      have : r2 = q := by linarith
      subst this
      rw [hv] at hlt; simp at hlt
  rcases lt_trichotomy r1 r2 with h12 | h12 | h12
  · obtain ⟨a1, a2, a3⟩ := side w r1 r2 hw hqw hv h12
    exact ⟨r1, r2, hr1, hr2, a1, a2, a3⟩
  · subst h12
    have : r1 = q := by linear_combination hqw
    subst this
    rw [hv] at hlt; ring_nf at hlt; exact absurd hlt (lt_irrefl _)
  · obtain ⟨a1, a2, a3⟩ := side (1 - w) r2 r1 ⟨by linarith [hw.2], by linarith [hw.1]⟩
      (by linear_combination hqw) (by rw [hv]; ring) h12
    exact ⟨r2, r1, hr2, hr1, a1, a2, a3⟩

lemma gEnv_locconst {M : ℝ} (hHc : ContinuousOn H (Icc 0 1)) (hb : ∀ q, BddBelow (Gset H q))
    (hL0 : ∀ r ∈ Icc (0:ℝ) 1, H 0 - M * r ≤ H r)
    {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (hlt : Genv H q < H q) :
    ∃ l r : ℝ, l < q ∧ q < r ∧ ∀ y ∈ Ioo l r, gEnv H y = gEnv H q := by
  have hconv := Genv_convex hb
  obtain ⟨l, r, hl, hr, hlq, hqr, hch⟩ := Genv_affine_piece hHc hq hlt
  have hrl : 0 < r - l := by linarith
  -- sandwich: Genv q is the chord of Genv between l and r
  have hGl := Genv_le (hb l) hl
  have hGr := Genv_le (hb r) hr
  have hcq := convex_chord hconv hl hr hlq hqr
  have hqeq : Genv H q * (r - l) = (r - q) * Genv H l + (q - l) * Genv H r := by
    apply le_antisymm hcq
    nlinarith [mul_le_mul_of_nonneg_left hGl (by linarith : (0:ℝ) ≤ r - q),
      mul_le_mul_of_nonneg_left hGr (by linarith : (0:ℝ) ≤ q - l)]
  -- affine on [l, r]
  have haff : ∀ x ∈ Icc l r, Genv H x * (r - l) = (r - x) * Genv H l + (x - l) * Genv H r := by
    intro x hx
    have hxI : x ∈ Icc (0:ℝ) 1 := ⟨hl.1.trans hx.1, hx.2.trans hr.2⟩
    rcases hx.1.eq_or_lt with h | hlx
    · subst h; ring
    rcases hx.2.eq_or_lt with h | hxr
    · subst h; ring
    apply le_antisymm (convex_chord hconv hl hr hlx hxr)
    rcases lt_trichotomy x q with hxq | hxq | hxq
    · have h1 := convex_chord hconv hxI hr hxq hqr
      have h1' := mul_le_mul_of_nonneg_left h1 hrl.le
      have hid : (r - x) * (Genv H q * (r - l)) = (r - x) * ((r - q) * Genv H l + (q - l) * Genv H r) := by
        rw [hqeq]
      have : (r - q) * ((r - x) * Genv H l + (x - l) * Genv H r - Genv H x * (r - l)) ≤ 0 := by
        nlinarith
      by_contra hc
      have := mul_pos (by linarith : (0:ℝ) < r - q) (by linarith [not_le.1 hc] :
        (0:ℝ) < (r - x) * Genv H l + (x - l) * Genv H r - Genv H x * (r - l))
      linarith
    · subst hxq; exact hqeq.ge
    · have h1 := convex_chord hconv hl hxI hlq hxq
      have h1' := mul_le_mul_of_nonneg_left h1 hrl.le
      have hid : (x - l) * (Genv H q * (r - l)) = (x - l) * ((r - q) * Genv H l + (q - l) * Genv H r) := by
        rw [hqeq]
      have : (q - l) * ((r - x) * Genv H l + (x - l) * Genv H r - Genv H x * (r - l)) ≤ 0 := by
        nlinarith
      by_contra hc
      have := mul_pos (by linarith : (0:ℝ) < q - l) (by linarith [not_le.1 hc] :
        (0:ℝ) < (r - x) * Genv H l + (x - l) * Genv H r - Genv H x * (r - l))
      linarith
  -- right derivative is the slope on [l, r)
  set β := (Genv H r - Genv H l) / (r - l)
  have hder : ∀ y ∈ Ico l r, gEnv H y = β := by
    intro y hy
    have hy1 : y < 1 := hy.2.trans_le hr.2
    have hyI : y ∈ Ico (0:ℝ) 1 := ⟨hl.1.trans hy.1, hy1⟩
    have hA : HasDerivWithinAt (fun z => Genv H l + β * (z - l)) β (Ioi y) y := by
      have := ((hasDerivAt_id y).sub_const l).const_mul β
      simpa using (this.const_add (Genv H l)).hasDerivWithinAt
    have hEq : ∀ z ∈ Icc l r, Genv H z = Genv H l + β * (z - l) := by
      intro z hz
      have := haff z hz
      simp only [β]
      field_simp
      linear_combination this
    have hG : HasDerivWithinAt (Genv H) β (Ioi y) y := by
      refine hA.congr_of_eventuallyEq ?_ (hEq y ⟨hy.1, hy.2.le⟩)
      filter_upwards [Ioo_mem_nhdsGT hy.2, self_mem_nhdsWithin] with z hz hz'
      exact hEq z ⟨hy.1.trans (le_of_lt hz'), hz.2.le⟩
    exact (uniqueDiffWithinAt_Ioi y).eq_deriv _ (Genv_hasDerivRight hb hL0 hyI) hG
  refine ⟨l, r, hlq, hqr, fun y hy => ?_⟩
  rw [hder y ⟨hy.1.le, hy.2⟩, hder q ⟨hlq.le, hqr⟩]


end DBlock

section EBlock

variable (E : Environment ι) (i : ι)

lemma a_mem : E.a i ∈ Icc (E.a i) (E.b i) := ⟨le_rfl, (E.a_lt_b i).le⟩
lemma b_mem : E.b i ∈ Icc (E.a i) (E.b i) := ⟨(E.a_lt_b i).le, le_rfl⟩

lemma f_ii {x y : ℝ} (hx : x ∈ Icc (E.a i) (E.b i)) (hy : y ∈ Icc (E.a i) (E.b i)) :
    IntervalIntegrable (E.f i) volume x y :=
  ((E.f_cont i).mono (uIcc_subset_Icc hx hy)).intervalIntegrable

lemma vvf_ii {x y : ℝ} (hx : x ∈ Icc (E.a i) (E.b i)) (hy : y ∈ Icc (E.a i) (E.b i)) :
    IntervalIntegrable (fun s => virtualValue E i s * E.f i s) volume x y :=
  (((vv_contOn E i).mul (E.f_cont i)).mono (uIcc_subset_Icc hx hy)).intervalIntegrable

lemma F_strictMonoOn : StrictMonoOn (F E i) (Icc (E.a i) (E.b i)) := by
  intro x hx y hy hxy
  have hs : F E i y - F E i x = ∫ u in x..y, E.f i u :=
    intervalIntegral.integral_interval_sub_left (f_ii E i (a_mem E i) hy) (f_ii E i (a_mem E i) hx)
  have hpos : 0 < ∫ u in x..y, E.f i u :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (f_ii E i hx hy)
      (fun u hu => E.f_pos i u ⟨hx.1.trans hu.1.le, hu.2.le.trans hy.2⟩) hxy
  linarith

lemma F_a : F E i (E.a i) = 0 := intervalIntegral.integral_same
lemma F_b : F E i (E.b i) = 1 := E.f_int i

lemma F_mem {s : ℝ} (hs : s ∈ Icc (E.a i) (E.b i)) : F E i s ∈ Icc (0:ℝ) 1 := by
  have hm := (F_strictMonoOn E i).monotoneOn
  exact ⟨F_a E i ▸ hm (a_mem E i) hs hs.1, F_b E i ▸ hm hs (b_mem E i) hs.2⟩

lemma F_lt_one {s : ℝ} (hs : s ∈ Icc (E.a i) (E.b i)) (hsb : s < E.b i) : F E i s < 1 :=
  F_b E i ▸ F_strictMonoOn E i hs (b_mem E i) hsb

lemma inverseF_F {s : ℝ} (hs : s ∈ Icc (E.a i) (E.b i)) : inverseF E i (F E i s) = s := by
  unfold inverseF
  exact IsLeast.csInf_eq ⟨⟨hs, le_rfl⟩, fun u hu => ((F_strictMonoOn E i).le_iff_le hs hu.1).1 hu.2⟩

lemma inverseF_mem {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) : inverseF E i q ∈ Icc (E.a i) (E.b i) := by
  unfold inverseF
  have hbm : E.b i ∈ {s | s ∈ Icc (E.a i) (E.b i) ∧ q ≤ F E i s} :=
    ⟨b_mem E i, by rw [F_b]; exact hq.2⟩
  exact ⟨le_csInf ⟨_, hbm⟩ fun s hs => hs.1.1, csInf_le ⟨E.a i, fun s hs => hs.1.1⟩ hbm⟩

lemma h_F {s : ℝ} (hs : s ∈ Icc (E.a i) (E.b i)) : h E i (F E i s) = virtualValue E i s := by
  simp only [h, inverseF_F E i hs, virtualValue]

lemma F_hasDerivWithin {x : ℝ} (hx : x ∈ Icc (E.a i) (E.b i)) :
    HasDerivWithinAt (F E i) (E.f i x) (Icc (E.a i) (E.b i)) x := by
  haveI : Fact (x ∈ Icc (E.a i) (E.b i)) := ⟨hx⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right (f_ii E i (a_mem E i) hx)
    ((E.f_cont i).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x) ((E.f_cont i) x hx)

lemma F_image {s : ℝ} (hs : s ∈ Icc (E.a i) (E.b i)) :
    F E i '' Icc (E.a i) s = Icc 0 (F E i s) := by
  have hsub : Icc (E.a i) s ⊆ Icc (E.a i) (E.b i) := Icc_subset_Icc le_rfl hs.2
  apply Subset.antisymm
  · rw [← F_a E i]; exact ((F_strictMonoOn E i).monotoneOn.mono hsub).image_Icc_subset
  · rw [← F_a E i]; exact intermediate_value_Icc hs.1 ((F_contOn E i).mono hsub)

lemma H_F {s : ℝ} (hs : s ∈ Icc (E.a i) (E.b i)) :
    H E i (F E i s) = ∫ u in E.a i..s, virtualValue E i u * E.f i u := by
  have hsub : Icc (E.a i) s ⊆ Icc (E.a i) (E.b i) := Icc_subset_Icc le_rfl hs.2
  have hF0 : 0 ≤ F E i s := (F_mem E i hs).1
  unfold H
  rw [intervalIntegral.integral_of_le hF0, ← integral_Icc_eq_integral_Ioc, ← F_image E i hs,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
      (fun x hx => (F_hasDerivWithin E i (hsub hx)).mono hsub)
      ((F_strictMonoOn E i).injOn.mono hsub),
    intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
  simp only [smul_eq_mul]
  rw [abs_of_pos (E.f_pos i x (hsub hx)), h_F E i (hsub hx)]
  ring

lemma h_bound : ∃ M, ∀ q ∈ Icc (0:ℝ) 1, |h E i q| ≤ M := by
  obtain ⟨Ce, hCe⟩ := isCompact_Icc.exists_bound_of_continuousOn (E.e_cont i)
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (E.a_lt_b i).le) (E.f_cont i)
  have hm0 : 0 < E.f i m := E.f_pos i m hm
  refine ⟨max |E.a i| |E.b i| + Ce + 1 / E.f i m, fun q hq => ?_⟩
  have hs := inverseF_mem E i hq
  set s := inverseF E i q with hsdef
  have h1 : |s| ≤ max |E.a i| |E.b i| := abs_le_max_abs_abs hs.1 hs.2
  have h2 : |E.e i s| ≤ Ce := by simpa [Real.norm_eq_abs] using hCe s hs
  have hfs : E.f i m ≤ E.f i s := hmin hs
  have hfs0 : 0 < E.f i s := E.f_pos i s hs
  have h3 : |(1 - q) / E.f i s| ≤ 1 / E.f i m := by
    rw [abs_div, abs_of_pos hfs0, abs_of_nonneg (by linarith [hq.2])]
    calc (1 - q) / E.f i s ≤ 1 / E.f i s := by gcongr; linarith [hq.1]
      _ ≤ 1 / E.f i m := one_div_le_one_div_of_le hm0 hfs
  have : h E i q = s - E.e i s - (1 - q) / E.f i s := rfl
  rw [this]
  have := (abs_sub (s - E.e i s) ((1 - q) / E.f i s)).trans (add_le_add (abs_sub s (E.e i s)) le_rfl)
  linarith

lemma h_integrableOn : IntegrableOn (h E i) (Icc 0 1) := by
  have hI : Icc (0:ℝ) 1 = F E i '' Icc (E.a i) (E.b i) := by rw [F_image E i (b_mem E i), F_b]
  rw [hI, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc
    (fun x hx => F_hasDerivWithin E i hx) (F_strictMonoOn E i).injOn]
  have hEq : EqOn (fun x => E.f i x * virtualValue E i x)
      (fun x => |E.f i x| • h E i (F E i x)) (Icc (E.a i) (E.b i)) := fun x hx => by
    simp only [smul_eq_mul]; rw [abs_of_pos (E.f_pos i x hx), h_F E i hx]
  exact (((E.f_cont i).mul (vv_contOn E i)).integrableOn_Icc).congr_fun hEq measurableSet_Icc

lemma H_contOn : ContinuousOn (H E i) (Icc 0 1) := by
  have hc := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := (0:ℝ))
    (b := 1) (f := h E i) (by rw [uIcc_of_le zero_le_one]; exact h_integrableOn E i)
  rw [uIcc_of_le zero_le_one] at hc
  exact hc

lemma H_zero : H E i 0 = 0 := intervalIntegral.integral_same

lemma H_bounds : ∃ M, 0 ≤ M ∧ (∀ r ∈ Icc (0:ℝ) 1, H E i 0 - M * r ≤ H E i r) ∧
    (∀ r ∈ Icc (0:ℝ) 1, H E i 1 - M * (1 - r) ≤ H E i r) := by
  obtain ⟨M, hM⟩ := h_bound E i
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have hii : ∀ x y, x ∈ Icc (0:ℝ) 1 → y ∈ Icc (0:ℝ) 1 → IntervalIntegrable (h E i) volume x y :=
    fun x y hx hy => ((h_integrableOn E i).mono_set (uIcc_subset_Icc hx hy)).intervalIntegrable
  have hnorm : ∀ x y, x ∈ Icc (0:ℝ) 1 → y ∈ Icc (0:ℝ) 1 → x ≤ y →
      |∫ u in x..y, h E i u| ≤ M * (y - x) := by
    intro x y hx hy hxy
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := y) (C := M)
      (f := h E i) (fun u hu => by
        rw [uIoc_of_le hxy] at hu
        exact hM u ⟨hx.1.trans hu.1.le, hu.2.trans hy.2⟩)
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hxy)] at this
  refine ⟨M, hM0, fun r hr => ?_, fun r hr => ?_⟩
  · have := hnorm 0 r ⟨le_rfl, zero_le_one⟩ hr hr.1
    have e : H E i r = ∫ u in (0:ℝ)..r, h E i u := rfl
    rw [H_zero, e]
    linarith [(abs_le.1 this).1]
  · have := hnorm r 1 hr ⟨zero_le_one, le_rfl⟩ hr.2
    have e : H E i 1 - H E i r = ∫ u in r..1, h E i u :=
      intervalIntegral.integral_interval_sub_left (hii 0 1 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩)
        (hii 0 r ⟨le_rfl, zero_le_one⟩ hr)
    linarith [(abs_le.1 this).2]

lemma H_bdd (q : ℝ) : BddBelow (Gset (H E i) q) := by
  obtain ⟨M, hM0, hL0, -⟩ := H_bounds E i
  refine Gset_bdd (M := M) (fun r hr => ?_) q
  have := hL0 r hr
  rw [H_zero] at this
  nlinarith [hr.2]

lemma G_eq : G E i = Genv (H E i) := rfl
lemma g_eq : g E i = gEnv (H E i) := rfl

lemma GF_deriv {x : ℝ} (hx : x ∈ Ioo (E.a i) (E.b i)) :
    HasDerivWithinAt (fun s => G E i (F E i s)) (g E i (F E i x) * E.f i x) (Ioi x) x := by
  obtain ⟨M, -, hL0, -⟩ := H_bounds E i
  have hxI : x ∈ Icc (E.a i) (E.b i) := Ioo_subset_Icc_self hx
  have hF : HasDerivAt (F E i) (E.f i x) x :=
    (F_hasDerivWithin E i hxI).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  have hG := Genv_hasDerivRight (H_bdd E i) hL0 ⟨(F_mem E i hxI).1, F_lt_one E i hxI hx.2⟩
  have hmaps : MapsTo (F E i) (Ioo x (E.b i)) (Ioi (F E i x)) := fun y hy =>
    F_strictMonoOn E i hxI ⟨hx.1.le.trans hy.1.le, hy.2.le⟩ hy.1
  exact (hG.comp x hF.hasDerivWithinAt hmaps).mono_of_mem_nhdsWithin (Ioo_mem_nhdsGT hx.2)

lemma gF_mono : MonotoneOn (fun s => g E i (F E i s)) (Icc (E.a i) (E.b i)) := by
  obtain ⟨M, -, hL0, hL1⟩ := H_bounds E i
  exact (gEnv_mono (H_bdd E i) hL0 hL1).comp (F_strictMonoOn E i).monotoneOn
    (fun s hs => F_mem E i hs)

lemma gFf_ii {x y : ℝ} (hx : x ∈ Icc (E.a i) (E.b i)) (hy : y ∈ Icc (E.a i) (E.b i)) :
    IntervalIntegrable (fun s => g E i (F E i s) * E.f i s) volume x y :=
  (((gF_mono E i).mono (uIcc_subset_Icc hx hy)).intervalIntegrable).mul_continuousOn
    ((E.f_cont i).mono (uIcc_subset_Icc hx hy))

lemma int_gFf {σ : ℝ} (hσ : σ ∈ Icc (E.a i) (E.b i)) :
    ∫ s in σ..E.b i, g E i (F E i s) * E.f i s = G E i 1 - G E i (F E i σ) := by
  obtain ⟨M, -, hL0, hL1⟩ := H_bounds E i
  have hsub : Icc σ (E.b i) ⊆ Icc (E.a i) (E.b i) := Icc_subset_Icc hσ.1 le_rfl
  have hcont : ContinuousOn (fun s => G E i (F E i s)) (Icc σ (E.b i)) :=
    (Genv_contOn (H_bdd E i) hL0 hL1).comp ((F_contOn E i).mono hsub) (fun s hs => F_mem E i (hsub hs))
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hσ.2 hcont
    (fun x hx => GF_deriv E i ⟨hσ.1.trans_lt hx.1, hx.2⟩) (gFf_ii E i hσ (b_mem E i)), F_b]

lemma int_vvf {σ : ℝ} (hσ : σ ∈ Icc (E.a i) (E.b i)) :
    ∫ s in σ..E.b i, virtualValue E i s * E.f i s = H E i 1 - H E i (F E i σ) := by
  have e1 : H E i 1 = ∫ u in E.a i..E.b i, virtualValue E i u * E.f i u := by
    rw [← H_F E i (b_mem E i), F_b]
  rw [e1, H_F E i hσ, intervalIntegral.integral_interval_sub_left (vvf_ii E i (a_mem E i) (b_mem E i))
    (vvf_ii E i (a_mem E i) hσ)]

/-- Block E: the ironing integral over an upper interval. -/
lemma ironing_piece {σ : ℝ} (hσ : σ ∈ Icc (E.a i) (E.b i)) :
    ∫ s in σ..E.b i, (virtualValue E i s - ironedPriority E i s) * E.f i s =
      G E i (F E i σ) - H E i (F E i σ) := by
  have e : (fun s => (virtualValue E i s - ironedPriority E i s) * E.f i s) =
      fun s => virtualValue E i s * E.f i s - g E i (F E i s) * E.f i s := by
    funext s; simp only [ironedPriority]; ring
  rw [e, intervalIntegral.integral_sub (vvf_ii E i hσ (b_mem E i)) (gFf_ii E i hσ (b_mem E i)),
    int_vvf E i hσ, int_gFf E i hσ, G_eq, Genv_one (H_bdd E i 1)]
  ring

end EBlock


section FBlock

lemma upset_piece {a b : ℝ} (hab : a ≤ b) (ψ Qc : ℝ → ℝ) (hQ : Monotone Qc) (y : ℝ) :
    ∃ σ ∈ Icc a b, (∫ s in Ioc a b, {s | y < Qc s}.indicator ψ s) = ∫ s in σ..b, ψ s ∧
      (σ ∈ Ioo a b → ∀ l r, l < σ → σ < r →
        ∃ u ∈ Ioo l r ∩ Icc a b, ∃ v ∈ Ioo l r ∩ Icc a b, Qc u ≤ y ∧ y < Qc v) := by
  set S : Set ℝ := {s | y < Qc s} with hSdef
  have hS : MeasurableSet S := measurableSet_lt measurable_const hQ.measurable
  rw [setIntegral_indicator hS]
  by_cases hne : (S ∩ Icc a b).Nonempty
  · set σ := sInf (S ∩ Icc a b) with hσdef
    have hbdd : BddBelow (S ∩ Icc a b) := ⟨a, fun s hs => hs.2.1⟩
    have hσa : a ≤ σ := le_csInf hne fun s hs => hs.2.1
    have hσb : σ ≤ b := (csInf_le hbdd hne.some_mem).trans hne.some_mem.2.2
    have hsub1 : Ioc σ b ⊆ Ioc a b ∩ S := by
      intro s hs
      obtain ⟨s', hs', hs's⟩ := exists_lt_of_csInf_lt hne hs.1
      exact ⟨⟨hσa.trans_lt hs.1, hs.2⟩, lt_of_lt_of_le hs'.1 (hQ hs's.le)⟩
    have hsub2 : Ioc a b ∩ S ⊆ Icc σ b := fun s hs =>
      ⟨csInf_le hbdd ⟨hs.2, Ioc_subset_Icc_self hs.1⟩, hs.1.2⟩
    have hae : (Ioc a b ∩ S : Set ℝ) =ᵐ[volume] Ioc σ b :=
      (hsub2.eventuallyLE.trans_eq Ioc_ae_eq_Icc.symm).antisymm hsub1.eventuallyLE
    refine ⟨σ, ⟨hσa, hσb⟩, ?_, ?_⟩
    · rw [setIntegral_congr_set hae, intervalIntegral.integral_of_le hσb]
    · intro hσ l r hl hr
      obtain ⟨u, hu1, hu2⟩ := exists_between (max_lt hl hσ.1)
      obtain ⟨v, hv1, hv2⟩ := exists_between (lt_min hr hσ.2)
      have huI : u ∈ Icc a b := ⟨(le_max_right _ _).trans hu1.le, hu2.le.trans hσb⟩
      have hvI : v ∈ Icc a b := ⟨hσa.trans hv1.le, hv2.le.trans (min_le_right _ _)⟩
      refine ⟨u, ⟨⟨(le_max_left _ _).trans_lt hu1, hu2.trans hr⟩, huI⟩,
        v, ⟨⟨hl.trans hv1, hv2.trans_le (min_le_left _ _)⟩, hvI⟩, ?_, ?_⟩
      · by_contra hc
        have : σ ≤ u := csInf_le hbdd ⟨not_le.1 hc, huI⟩
        linarith
      · exact (hsub1 ⟨hv1, hv2.le.trans (min_le_right _ _)⟩).2
  · refine ⟨b, ⟨hab, le_rfl⟩, ?_, fun h => absurd h.2 (lt_irrefl b)⟩
    rw [intervalIntegral.integral_same]
    have : Ioc a b ∩ S = ∅ := by
      ext s
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hs hS'
      exact hne ⟨s, hS', Ioc_subset_Icc_self hs⟩
    rw [this, Measure.restrict_empty, integral_zero_measure]

lemma level_integral {α c β : ℝ} (hαc : α ≤ c) (hcβ : c ≤ β) (k : ℝ) :
    ∫ y in Ioc α β, (Iio c).indicator (fun _ => k) y = k * (c - α) := by
  rw [setIntegral_indicator measurableSet_Iio, setIntegral_const]
  have e : Ioc α β ∩ Iio c = Ioo α c := by
    ext x
    simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le.trans hcβ⟩, h2⟩
  rw [e, Real.volume_real_Ioo_of_le hαc, smul_eq_mul, mul_comm]

lemma layer_core {a b : ℝ} (hab : a ≤ b) (ψ Qc : ℝ → ℝ) (hψ : IntegrableOn ψ (Ioc a b))
    (hQ : Monotone Qc) (htot : ∫ s in a..b, ψ s = 0) :
    ∫ s in a..b, ψ s * Qc s = ∫ y in Qc a..Qc b, ∫ s in Ioc a b, {s | y < Qc s}.indicator ψ s := by
  have hQab : Qc a ≤ Qc b := hQ hab
  have hQm : Measurable Qc := hQ.measurable
  have hbd : ∀ s ∈ Ioc a b, ‖Qc s‖ ≤ max |Qc a| |Qc b| := fun s hs => by
    rw [Real.norm_eq_abs]; exact abs_le_max_abs_abs (hQ hs.1.le) (hQ hs.2)
  have hψQ : IntegrableOn (fun s => ψ s * Qc s) (Ioc a b) :=
    (Integrable.bdd_mul (c := max |Qc a| |Qc b|) hψ hQm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hbd))).congr
      (Filter.Eventually.of_forall fun s => mul_comm _ _)
  rw [intervalIntegral.integral_of_le hab] at htot
  let T : Set (ℝ × ℝ) := {z | z.2 < Qc z.1}
  have hT : MeasurableSet T := measurableSet_lt measurable_snd (hQm.comp measurable_fst)
  haveI : IsFiniteMeasure (volume.restrict (Ioc (Qc a) (Qc b))) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hint : Integrable (Function.uncurry fun s y => T.indicator (fun z => ψ z.1) (s, y))
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (Qc a) (Qc b)))) :=
    (hψ.comp_fst (volume.restrict (Ioc (Qc a) (Qc b)))).indicator hT
  calc ∫ s in a..b, ψ s * Qc s
      = ∫ s in Ioc a b, ψ s * (Qc s - Qc a) := by
        rw [intervalIntegral.integral_of_le hab]
        have : ∫ s in Ioc a b, ψ s * (Qc s - Qc a) =
            ∫ s in Ioc a b, (ψ s * Qc s - Qc a * ψ s) := by
          congr 1; funext s; ring
        rw [this, integral_sub hψQ (hψ.const_mul (Qc a)), integral_const_mul, htot]; ring
    _ = ∫ s in Ioc a b, ∫ y in Ioc (Qc a) (Qc b), T.indicator (fun z => ψ z.1) (s, y) := by
        refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
        rw [← level_integral (hQ hs.1.le) (hQ hs.2) (ψ s)]
        congr 1
    _ = ∫ y in Ioc (Qc a) (Qc b), ∫ s in Ioc a b, T.indicator (fun z => ψ z.1) (s, y) :=
        integral_integral_swap hint
    _ = ∫ y in Qc a..Qc b, ∫ s in Ioc a b, {s | y < Qc s}.indicator ψ s := by
        rw [intervalIntegral.integral_of_le hQab]
        congr 1

lemma layer_cake_le {a b : ℝ} (hab : a ≤ b) (ψ Q : ℝ → ℝ) (hψ : IntegrableOn ψ (Icc a b))
    (hQ : MonotoneOn Q (Icc a b)) (htot : ∫ s in a..b, ψ s = 0)
    (hpiece : ∀ σ ∈ Icc a b, ∫ s in σ..b, ψ s ≤ 0) :
    ∫ s in a..b, ψ s * Q s ≤ 0 := by
  set Qc : ℝ → ℝ := fun s => Q (projIcc a b hab s) with hQcdef
  have hQc : Monotone Qc := fun x y hxy =>
    hQ (projIcc a b hab x).2 (projIcc a b hab y).2 (monotone_projIcc hab hxy)
  have hcongr : ∫ s in a..b, ψ s * Q s = ∫ s in a..b, ψ s * Qc s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hab] at hs
    simp [Qc, projIcc_of_mem hab hs]
  rw [hcongr, layer_core hab ψ Qc (hψ.mono_set Ioc_subset_Icc_self) hQc htot,
    intervalIntegral.integral_of_le (hQc hab)]
  refine integral_nonpos fun y => ?_
  obtain ⟨σ, hσ, heq, -⟩ := upset_piece hab ψ Qc hQc y
  simp only [Pi.zero_apply]
  rw [heq]; exact hpiece σ hσ

lemma layer_cake_eq {a b : ℝ} (hab : a ≤ b) (ψ Q : ℝ → ℝ) (hψ : IntegrableOn ψ (Icc a b))
    (hQ : MonotoneOn Q (Icc a b)) (htot : ∫ s in a..b, ψ s = 0)
    (hloc : ∀ σ ∈ Ioo a b, ∫ s in σ..b, ψ s ≠ 0 →
      ∃ l r, l < σ ∧ σ < r ∧ ∀ y ∈ Ioo l r ∩ Icc a b, Q y = Q σ) :
    ∫ s in a..b, ψ s * Q s = 0 := by
  set Qc : ℝ → ℝ := fun s => Q (projIcc a b hab s) with hQcdef
  have hQc : Monotone Qc := fun x y hxy =>
    hQ (projIcc a b hab x).2 (projIcc a b hab y).2 (monotone_projIcc hab hxy)
  have hQcI : ∀ s ∈ Icc a b, Qc s = Q s := fun s hs => by simp [Qc, projIcc_of_mem hab hs]
  have hcongr : ∫ s in a..b, ψ s * Q s = ∫ s in a..b, ψ s * Qc s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hab] at hs
    simp only [hQcI s hs]
  have hz : ∀ y, ∫ s in Ioc a b, {s | y < Qc s}.indicator ψ s = 0 := by
    intro y
    obtain ⟨σ, hσ, heq, hbd⟩ := upset_piece hab ψ Qc hQc y
    rw [heq]
    by_contra hne
    rcases hσ.1.eq_or_lt with h | hσa
    · rw [← h] at hne; exact hne htot
    rcases hσ.2.eq_or_lt with h | hσb
    · rw [h] at hne; exact hne intervalIntegral.integral_same
    obtain ⟨l, r, hl, hr, hconst⟩ := hloc σ ⟨hσa, hσb⟩ hne
    obtain ⟨u, hu, v, hv, hu', hv'⟩ := hbd ⟨hσa, hσb⟩ l r hl hr
    rw [hQcI u hu.2, hconst u hu] at hu'
    rw [hQcI v hv.2, hconst v hv] at hv'
    linarith
  rw [hcongr, layer_core hab ψ Qc (hψ.mono_set Ioc_subset_Icc_self) hQc htot]
  simp only [hz, intervalIntegral.integral_zero]

end FBlock


section GBlock

variable (E : Environment ι)

omit [DecidableEq ι] in
/-- Winner set as a function of a priority vector (same formula as `winners`). -/
def Wset (c : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => E.t0 ≤ c i ∧ ∀ j, c j ≤ c i)

omit [DecidableEq ι] in
/-- Share as a function of a priority vector (same formula as `pbar`). -/
def share (c : ι → ℝ) : ι → ℝ := by
  classical
  exact fun i => if i ∈ Wset E c then 1 / (Wset E c).card else 0

lemma pbar_eq_share (i : ι) (t : ι → ℝ) :
    pbar E i t = share E (fun j => ironedPriority E j (t j)) i := by
  classical
  unfold pbar share winners Wset
  by_cases h : i ∈ Finset.univ.filter (fun i => E.t0 ≤ ironedPriority E i (t i) ∧
      ∀ j, ironedPriority E j (t j) ≤ ironedPriority E i (t i))
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

omit [DecidableEq ι] in
lemma mem_Wset {c : ι → ℝ} {i : ι} : i ∈ Wset E c ↔ E.t0 ≤ c i ∧ ∀ j, c j ≤ c i := by
  simp [Wset]

lemma share_of_mem {c : ι → ℝ} {i : ι} (h : i ∈ Wset E c) :
    share E c i = 1 / (Wset E c).card := by
  classical
  simp only [share]; rw [if_pos h]

lemma share_of_not_mem {c : ι → ℝ} {i : ι} (h : i ∉ Wset E c) : share E c i = 0 := by
  classical
  simp only [share]; rw [if_neg h]

lemma share_nonneg (c : ι → ℝ) (i : ι) : 0 ≤ share E c i := by
  by_cases h : i ∈ Wset E c
  · rw [share_of_mem E h]; positivity
  · rw [share_of_not_mem E h]

lemma share_le_one (c : ι → ℝ) (i : ι) : share E c i ≤ 1 := by
  by_cases h : i ∈ Wset E c
  · rw [share_of_mem E h]
    have : (1:ℝ) ≤ (Wset E c).card := by exact_mod_cast Finset.card_pos.2 ⟨i, h⟩
    rw [div_le_one (by linarith)]; exact this
  · rw [share_of_not_mem E h]; exact zero_le_one

lemma share_sum (c : ι → ℝ) (φ : ι → ℝ) :
    ∑ i, φ i * share E c i = (∑ i ∈ Wset E c, φ i) / (Wset E c).card := by
  classical
  have : ∀ i, φ i * share E c i = if i ∈ Wset E c then φ i / (Wset E c).card else 0 := by
    intro i
    by_cases h : i ∈ Wset E c
    · rw [share_of_mem E h, if_pos h]; ring
    · rw [share_of_not_mem E h, if_neg h, mul_zero]
  simp only [this]
  rw [← Finset.sum_filter, Finset.sum_div]
  congr 1
  ext i; simp

lemma share_sum_le_one (c : ι → ℝ) : ∑ i, share E c i ≤ 1 := by
  have h := share_sum E c (fun _ => 1)
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [h]
  rcases Nat.eq_zero_or_pos (Wset E c).card with h0 | hpos
  · simp [h0]
  · rw [div_self (by exact_mod_cast hpos.ne')]

/-- Pointwise optimality of the tied allocation (6.6)-(6.7). -/
lemma share_opt [Nonempty ι] (c p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i ≤ 1) :
    ∑ i, (c i - E.t0) * p i ≤ ∑ i, (c i - E.t0) * share E c i := by
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ c Finset.univ_nonempty
  have hk' : ∀ j, c j ≤ c k := fun j => hk j (Finset.mem_univ j)
  set m := max (c k - E.t0) 0
  have hle : ∑ i, (c i - E.t0) * p i ≤ m := by
    calc ∑ i, (c i - E.t0) * p i ≤ ∑ i, m * p i :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
            ((by linarith [hk' i] : c i - E.t0 ≤ c k - E.t0).trans (le_max_left _ _)) (hp0 i)
      _ = m * ∑ i, p i := by rw [Finset.mul_sum]
      _ ≤ m * 1 := mul_le_mul_of_nonneg_left hp1 (le_max_right _ _)
      _ = m := mul_one m
  refine hle.trans (le_of_eq ?_)
  rw [share_sum]
  by_cases ht : E.t0 ≤ c k
  · have hmem : ∀ i ∈ Wset E c, c i = c k := fun i hi =>
      le_antisymm (hk' i) (((mem_Wset E).1 hi).2 k)
    have hkW : k ∈ Wset E c := (mem_Wset E).2 ⟨ht, hk'⟩
    have hcard : ((Wset E c).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.2 ⟨k, hkW⟩).ne'
    rw [Finset.sum_congr rfl fun i hi => by rw [hmem i hi], Finset.sum_const, nsmul_eq_mul,
      mul_div_cancel_left₀ _ hcard]
    exact max_eq_left (by linarith)
  · have hempty : Wset E c = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro i hi
      exact ht ((((mem_Wset E).1 hi).1).trans (hk' i))
    rw [hempty]; simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, div_zero]
    exact max_eq_right (show c k - E.t0 ≤ 0 by linarith [not_le.1 ht])

/-- Own-priority monotonicity of the share. -/
lemma share_mono (c : ι → ℝ) (i : ι) {x y : ℝ} (hxy : x ≤ y) :
    share E (Function.update c i x) i ≤ share E (Function.update c i y) i := by
  by_cases hx : i ∈ Wset E (Function.update c i x)
  · obtain ⟨ht, hall⟩ := (mem_Wset E).1 hx
    simp only [Function.update_self] at ht hall
    have hy : i ∈ Wset E (Function.update c i y) := by
      refine (mem_Wset E).2 ⟨by simp only [Function.update_self]; linarith, fun j => ?_⟩
      simp only [Function.update_self]
      by_cases hj : j = i
      · subst hj; simp
      · have := hall j; simp only [Function.update_of_ne hj] at this ⊢; linarith
    have hsub : Wset E (Function.update c i y) ⊆ Wset E (Function.update c i x) := by
      intro j hj
      by_cases hji : j = i
      · subst hji; exact hx
      obtain ⟨htj, hallj⟩ := (mem_Wset E).1 hj
      simp only [Function.update_of_ne hji] at htj hallj
      have hyj : y ≤ c j := by have := hallj i; simpa using this
      refine (mem_Wset E).2 ⟨by simp only [Function.update_of_ne hji]; exact htj, fun k => ?_⟩
      simp only [Function.update_of_ne hji]
      by_cases hk : k = i
      · subst hk; simp only [Function.update_self]; linarith
      · have := hallj k; simp only [Function.update_of_ne hk] at this ⊢; exact this
    rw [share_of_mem E hx, share_of_mem E hy]
    have hpos : (0:ℝ) < (Wset E (Function.update c i y)).card := by
      exact_mod_cast Finset.card_pos.2 ⟨i, hy⟩
    exact one_div_le_one_div_of_le hpos (by exact_mod_cast Finset.card_le_card hsub)
  · rw [share_of_not_mem E hx]; exact share_nonneg E _ _

/-- Priorities of an updated profile. -/
lemma prio_update (t : ι → ℝ) (i : ι) (s : ℝ) :
    (fun j => ironedPriority E j (Function.update t i s j)) =
      Function.update (fun j => ironedPriority E j (t j)) i (ironedPriority E i s) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

lemma pbar_update_mono (t : ι → ℝ) (i : ι) {s r : ℝ} (hs : s ∈ Icc (E.a i) (E.b i))
    (hr : r ∈ Icc (E.a i) (E.b i)) (hsr : s ≤ r) :
    pbar E i (Function.update t i s) ≤ pbar E i (Function.update t i r) := by
  rw [pbar_eq_share, pbar_eq_share, prio_update, prio_update]
  exact share_mono E _ i (gF_mono E i hs hr hsr)

lemma pbar_update_congr (t : ι → ℝ) (i : ι) {s r : ℝ}
    (h : ironedPriority E i s = ironedPriority E i r) :
    pbar E i (Function.update t i s) = pbar E i (Function.update t i r) := by
  rw [pbar_eq_share, pbar_eq_share, prio_update, prio_update, h]

end GBlock


section HBlock

/-! ### Measurability of the tied allocation -/

omit [DecidableEq ι] in
/-- Ironed priority with the argument clamped to the support (monotone on all of ℝ). -/
def cbarC (E : Environment ι) (j : ι) (s : ℝ) : ℝ :=
  ironedPriority E j (Set.projIcc (E.a j) (E.b j) (E.a_lt_b j).le s)

lemma cbarC_mono (E : Environment ι) (j : ι) : Monotone (cbarC E j) := by
  intro x y hxy
  exact gF_mono E j (Set.projIcc _ _ _ x).2 (Set.projIcc _ _ _ y).2
    (Set.monotone_projIcc (E.a_lt_b j).le hxy)

lemma cbarC_meas (E : Environment ι) (j : ι) : Measurable (cbarC E j) :=
  (cbarC_mono E j).measurable

lemma cbarC_eq (E : Environment ι) (j : ι) {s : ℝ} (hs : s ∈ Icc (E.a j) (E.b j)) :
    cbarC E j s = ironedPriority E j s := by
  simp only [cbarC, Set.projIcc_of_mem _ hs]

lemma cbarC_bound (E : Environment ι) (j : ι) : ∃ M, ∀ s, ‖cbarC E j s‖ ≤ M := by
  refine ⟨|ironedPriority E j (E.a j)| + |ironedPriority E j (E.b j)|, fun s => ?_⟩
  have hlo : ironedPriority E j (E.a j) ≤ cbarC E j s :=
    gF_mono E j (a_mem E j) (Set.projIcc _ _ _ s).2 (Set.projIcc _ _ _ s).2.1
  have hhi : cbarC E j s ≤ ironedPriority E j (E.b j) :=
    gF_mono E j (Set.projIcc _ _ _ s).2 (b_mem E j) (Set.projIcc _ _ _ s).2.2
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [neg_abs_le (ironedPriority E j (E.a j)), abs_nonneg (ironedPriority E j (E.b j))]
  · linarith [le_abs_self (ironedPriority E j (E.b j)), abs_nonneg (ironedPriority E j (E.a j))]

omit [DecidableEq ι] in
lemma Wset_card (E : Environment ι) (c : ι → ℝ) :
    ((Wset E c).card : ℝ) = ∑ j, (if E.t0 ≤ c j ∧ ∀ k, c k ≤ c j then (1:ℝ) else 0) := by
  rw [Wset, Finset.natCast_card_filter]

lemma share_eq_div (E : Environment ι) (c : ι → ℝ) (i : ι) :
    share E c i = (if E.t0 ≤ c i ∧ ∀ k, c k ≤ c i then (1:ℝ) else 0) /
      ∑ j, (if E.t0 ≤ c j ∧ ∀ k, c k ≤ c j then (1:ℝ) else 0) := by
  rw [← Wset_card]
  by_cases h : i ∈ Wset E c
  · rw [share_of_mem E h, if_pos ((mem_Wset E).1 h)]
  · rw [share_of_not_mem E h, if_neg (fun h' => h ((mem_Wset E).2 h')), zero_div]

omit [DecidableEq ι] in
lemma ind_meas (E : Environment ι) (j : ι) :
    Measurable (fun c : ι → ℝ => if E.t0 ≤ c j ∧ ∀ k, c k ≤ c j then (1:ℝ) else 0) := by
  refine Measurable.ite ?_ measurable_const measurable_const
  have : {c : ι → ℝ | E.t0 ≤ c j ∧ ∀ k, c k ≤ c j} =
      {c | E.t0 ≤ c j} ∩ ⋂ k, {c | c k ≤ c j} := by ext c; simp
  rw [this]
  exact (measurableSet_le measurable_const (measurable_pi_apply j)).inter
    (MeasurableSet.iInter fun k => measurableSet_le (measurable_pi_apply k) (measurable_pi_apply j))

lemma share_meas (E : Environment ι) (i : ι) : Measurable (fun c : ι → ℝ => share E c i) := by
  simp_rw [share_eq_div]
  exact (ind_meas E i).div (Finset.measurable_sum _ fun j _ => ind_meas E j)

omit [DecidableEq ι] in
/-- A measurable version of `pbar`, equal to it on the support. -/
def pbarC (E : Environment ι) (i : ι) (t : ι → ℝ) : ℝ :=
  share E (fun j => cbarC E j (t j)) i

lemma pbarC_meas (E : Environment ι) (i : ι) : Measurable (pbarC E i) :=
  (share_meas E i).comp
    (measurable_pi_lambda _ fun j => (cbarC_meas E j).comp (measurable_pi_apply j))

lemma pbarC_norm (E : Environment ι) (i : ι) (t : ι → ℝ) : ‖pbarC E i t‖ ≤ 1 := by
  unfold pbarC
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [share_nonneg E (fun j => cbarC E j (t j)) i],
    share_le_one E (fun j => cbarC E j (t j)) i⟩

lemma pbar_eq_pbarC (E : Environment ι) (i : ι) {t : ι → ℝ} (ht : t ∈ support E) :
    pbar E i t = pbarC E i t := by
  rw [pbar_eq_share, pbarC]
  congr 1; funext j; rw [cbarC_eq E j ((mem_support E).1 ht j)]

lemma pbar_nonneg (E : Environment ι) (i : ι) (t : ι → ℝ) : 0 ≤ pbar E i t := by
  rw [pbar_eq_share]; exact share_nonneg E _ _

/-- Integrability of anything that agrees on the support with a bounded measurable function. -/
lemma int_of_eq_support (E : Environment ι) {W Wm : (ι → ℝ) → ℝ} (hm : Measurable Wm)
    {C : ℝ} (hb : ∀ t, ‖Wm t‖ ≤ C) (heq : ∀ t ∈ support E, W t = Wm t) :
    Integrable W (distribution E) ∧ ∀ i, ∀ s ∈ Icc (E.a i) (E.b i),
      Integrable (fun t => W (Function.update t i s)) (distribution E) := by
  have hI : ∀ V : (ι → ℝ) → ℝ, Measurable V → (∀ t, ‖V t‖ ≤ C) →
      Integrable V (distribution E) := fun V hV hVb =>
    (integrable_const C).mono' hV.aestronglyMeasurable (Filter.Eventually.of_forall hVb)
  refine ⟨(hI Wm hm hb).congr ?_, fun i s hs =>
    (hI _ (hm.comp (measurable_update_left (a := i) (x := s))) (fun t => hb _)).congr ?_⟩
  · filter_upwards [ae_support E] with t ht; exact (heq t ht).symm
  · filter_upwards [ae_support E] with t ht
    exact (heq _ (update_mem_support E i ht hs)).symm

lemma pbar_int (E : Environment ι) (i : ι) :
    Integrable (pbar E i) (distribution E) ∧ ∀ i', ∀ s ∈ Icc (E.a i') (E.b i'),
      Integrable (fun t => pbar E i (Function.update t i' s)) (distribution E) :=
  int_of_eq_support E (pbarC_meas E i) (pbarC_norm E i) fun _ ht => pbar_eq_pbarC E i ht

def Vbar (E : Environment ι) (i : ι) (t : ι → ℝ) : ℝ :=
  ∫ r in E.a i..t i, pbar E i (Function.update t i r)

def Vm (E : Environment ι) (i : ι) (t : ι → ℝ) : ℝ :=
  ∫ r in E.a i..E.b i, (Iic (t i)).indicator (fun r => pbarC E i (Function.update t i r)) r

lemma Vm_meas (E : Environment ι) (i : ι) : Measurable (Vm E i) := by
  have hk : Measurable (fun p : (ι → ℝ) × ℝ =>
      (Iic (p.1 i)).indicator (fun r => pbarC E i (Function.update p.1 i r)) p.2) := by
    simp only [Set.indicator_apply, Set.mem_Iic]
    exact Measurable.ite (measurableSet_le measurable_snd ((measurable_pi_apply i).comp measurable_fst))
      ((pbarC_meas E i).comp measurable_update') measurable_const
  have : Vm E i = fun t => ∫ r in Ioc (E.a i) (E.b i),
      (Iic (t i)).indicator (fun r => pbarC E i (Function.update t i r)) r := by
    funext t; rw [Vm, intervalIntegral.integral_of_le (E.a_lt_b i).le]
  rw [this]
  exact (hk.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (E.a i) (E.b i)))).measurable

lemma Vm_norm (E : Environment ι) (i : ι) (t : ι → ℝ) : ‖Vm E i t‖ ≤ 1 * |E.b i - E.a i| := by
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun r _ => ?_
  rw [Set.indicator_apply]
  split_ifs
  · exact pbarC_norm E i _
  · simp

lemma Vbar_eq_Vm (E : Environment ι) (i : ι) {t : ι → ℝ} (ht : t ∈ support E) :
    Vbar E i t = Vm E i t := by
  have hti := (mem_support E).1 ht i
  rw [Vbar, Vm, intervalIntegral.integral_of_le hti.1, intervalIntegral.integral_of_le (E.a_lt_b i).le,
    setIntegral_indicator measurableSet_Iic]
  have hset : Ioc (E.a i) (E.b i) ∩ Iic (t i) = Ioc (E.a i) (t i) := by
    ext r; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hti.2⟩, h2⟩
  rw [hset]
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  exact pbar_eq_pbarC E i (update_mem_support E i ht ⟨hr.1.le, hr.2.trans hti.2⟩)

lemma Vbar_int (E : Environment ι) (i : ι) :
    Integrable (Vbar E i) (distribution E) ∧ ∀ i', ∀ s ∈ Icc (E.a i') (E.b i'),
      Integrable (fun t => Vbar E i (Function.update t i' s)) (distribution E) :=
  int_of_eq_support E (Vm_meas E i) (Vm_norm E i) fun _ ht => Vbar_eq_Vm E i ht

lemma xbar_eq (E : Environment ι) (i : ι) (t : ι → ℝ) :
    xbar E i t = bidderValue E i t * pbar E i t - Vbar E i t := by
  rw [xbar, Vbar, mul_comm]

lemma wd_bar (E : Environment ι) : WellDefined E (pbar E) (xbar E) := by
  intro i
  obtain ⟨hp, hpu⟩ := pbar_int E i
  obtain ⟨hV, hVu⟩ := Vbar_int E i
  refine ⟨hp, ?_, fun s hs => ⟨hpu i s hs, ?_⟩⟩
  · rw [show xbar E i = fun t => bidderValue E i t * pbar E i t - Vbar E i t from
      funext (xbar_eq E i)]
    exact (bv_mul_int i hp).sub hV
  · rw [show (fun t => xbar E i (Function.update t i s)) = fun t =>
      bidderValue E i (Function.update t i s) * pbar E i (Function.update t i s) -
        Vbar E i (Function.update t i s) from funext fun t => xbar_eq E i _]
    exact (bvr_integrable_mul E i s hs _ (hpu i s hs)).sub (hVu i s hs)

/-! ### Interim utility of the tied mechanism -/

lemma interim_bar (E : Environment ι) (i : ι) (s : ℝ) :
    interimUtility E (pbar E) (xbar E) i s =
      ∫ t, (∫ r in E.a i..s, pbar E i (Function.update t i r)) ∂distribution E := by
  unfold interimUtility
  congr 1; funext t
  rw [xbar_eq, Vbar]
  simp only [Function.update_self, Function.update_idem]
  ring

lemma interim_bar_eq (E : Environment ι) (i : ι) {s : ℝ} (hs : s ∈ Icc (E.a i) (E.b i)) :
    interimUtility E (pbar E) (xbar E) i s = ∫ r in E.a i..s, Q E (pbar E) i r := by
  rw [interim_bar]
  have h1 : ∫ t, (∫ r in E.a i..s, pbar E i (Function.update t i r)) ∂distribution E =
      ∫ t, (∫ r in Ioc (E.a i) s, pbarC E i (Function.update t i r)) ∂distribution E := by
    refine integral_congr_ae ?_
    filter_upwards [ae_support E] with t ht
    rw [intervalIntegral.integral_of_le hs.1]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    exact pbar_eq_pbarC E i (update_mem_support E i ht ⟨hr.1.le, hr.2.trans hs.2⟩)
  have h2 : ∫ r in E.a i..s, Q E (pbar E) i r =
      ∫ r in Ioc (E.a i) s, ∫ t, pbarC E i (Function.update t i r) ∂distribution E := by
    rw [intervalIntegral.integral_of_le hs.1]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    refine integral_congr_ae ?_
    filter_upwards [ae_support E] with t ht
    exact pbar_eq_pbarC E i (update_mem_support E i ht ⟨hr.1.le, hr.2.trans hs.2⟩)
  rw [h1, h2]
  have : IsFiniteMeasure (volume.restrict (Ioc (E.a i) s)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  refine integral_integral_swap ?_
  refine (integrable_const (1:ℝ)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact ((pbarC_meas E i).comp measurable_update').aestronglyMeasurable
  · exact pbarC_norm E i _

lemma Qbar_nonneg (E : Environment ι) (i : ι) (r : ℝ) : 0 ≤ Q E (pbar E) i r :=
  integral_nonneg fun t => pbar_nonneg E i _

lemma Qbar_mono (E : Environment ι) (i : ι) : MonotoneOn (Q E (pbar E) i) (Icc (E.a i) (E.b i)) := by
  intro s hs r hr hsr
  exact integral_mono ((pbar_int E i).2 i s hs) ((pbar_int E i).2 i r hr)
    (fun t => pbar_update_mono E t i hs hr hsr)

lemma ic_ineq {a b : ℝ} {q : ℝ → ℝ} (hQ : MonotoneOn q (Icc a b)) {s r : ℝ}
    (hs : s ∈ Icc a b) (hr : r ∈ Icc a b) :
    (∫ x in a..r, q x) + (s - r) * q r ≤ ∫ x in a..s, q x := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hs.1.trans hs.2⟩
  have hii : ∀ x y, x ∈ Icc a b → y ∈ Icc a b → IntervalIntegrable q volume x y :=
    fun x y hx hy => (hQ.mono (Set.uIcc_subset_Icc hx hy)).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii a r ha hr) (hii r s hr hs)]
  rcases le_total r s with h | h
  · have hm := intervalIntegral.integral_mono_on h intervalIntegrable_const (hii r s hr hs)
      (fun x hx => hQ hr ⟨hr.1.trans hx.1, hx.2.trans hs.2⟩ hx.1)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
    linarith
  · have hm := intervalIntegral.integral_mono_on h (hii s r hs hr) intervalIntegrable_const
      (fun x hx => hQ ⟨hs.1.trans hx.1, hx.2.trans hr.2⟩ hr hx.2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
    rw [intervalIntegral.integral_symm s r]
    linarith

theorem K4 (E : Environment ι) :
    Feasible E (pbar E) (xbar E) ∧ ∀ i, interimUtility E (pbar E) (xbar E) i (E.a i) = 0 := by
  have hW : WellDefined E (pbar E) (xbar E) := wd_bar E
  have hU := fun i s (hs : s ∈ Icc (E.a i) (E.b i)) => interim_bar_eq E i hs
  refine ⟨⟨hW, ?_, ?_, ?_⟩, fun i => ?_⟩
  · intro t _
    refine ⟨?_, fun i => pbar_nonneg E i t⟩
    simp_rw [pbar_eq_share]; exact share_sum_le_one E _
  · intro i s hs; rw [hU i s hs]
    exact intervalIntegral.integral_nonneg hs.1 fun r _ => Qbar_nonneg E i r
  · intro i s hs r hr
    rw [report_eq E _ _ hW i s r hr, hU i s hs, hU i r hr]
    exact ic_ineq (Qbar_mono E i) hs hr
  · rw [hU i _ (a_mem E i), intervalIntegral.integral_same]

/-! ### The ironing inequality (K3) -/

lemma coord_bdd_int {E : Environment ι} (j : ι) {ψ : ℝ → ℝ} (hψ : AEStronglyMeasurable ψ (mu E j))
    {C : ℝ} (hC : ∀ s ∈ Icc (E.a j) (E.b j), ‖ψ s‖ ≤ C) {φ : (ι → ℝ) → ℝ}
    (hφ : Integrable φ (distribution E)) :
    Integrable (fun t => ψ (t j) * φ t) (distribution E) := by
  refine hφ.bdd_mul (c := C) (aesm_coord j hψ) ?_
  filter_upwards [ae_support E] with t ht
  exact hC _ ((mem_support E).mp ht j)

lemma int1 (E : Environment ι) (i : ι) {φ : (ι → ℝ) → ℝ} (hφ : Integrable φ (distribution E)) :
    Integrable (fun t => (virtualValue E i (t i) - cbarC E i (t i)) * φ t) (distribution E) := by
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn (vv_contOn E i)
  obtain ⟨M, hM⟩ := cbarC_bound E i
  refine coord_bdd_int (ψ := fun s => virtualValue E i s - cbarC E i s) i
    ((aesm_mu (vv_contOn E i)).sub (cbarC_meas E i).aestronglyMeasurable) (C := C1 + M)
    (fun s hs => (norm_sub_le _ _).trans (add_le_add (hC1 s hs) (hM s))) hφ

lemma int2 (E : Environment ι) (i : ι) {φ : (ι → ℝ) → ℝ} (hφ : Integrable φ (distribution E)) :
    Integrable (fun t => (cbarC E i (t i) - E.t0) * φ t) (distribution E) := by
  obtain ⟨M, hM⟩ := cbarC_bound E i
  refine coord_bdd_int (ψ := fun s => cbarC E i s - E.t0) i
    ((cbarC_meas E i).sub measurable_const).aestronglyMeasurable (C := M + ‖E.t0‖)
    (fun s _ => (norm_sub_le _ _).trans (add_le_add (hM s) le_rfl)) hφ

lemma VO_split (E : Environment ι) (p : Outcome ι) (hp : ∀ i, Integrable (p i) (distribution E)) :
    virtualObjective E p =
      ∑ i, ∫ t, (virtualValue E i (t i) - cbarC E i (t i)) * p i t ∂distribution E +
      ∫ t, ∑ i, (cbarC E i (t i) - E.t0) * p i t ∂distribution E := by
  unfold virtualObjective
  rw [← integral_finsetSum _ fun i _ => int1 E i (hp i),
    ← integral_add (integrable_finsetSum _ fun i _ => int1 E i (hp i))
      (integrable_finsetSum _ fun i _ => int2 E i (hp i))]
  congr 1; funext t
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma term1_eq (E : Environment ι) (i : ι) (p : Outcome ι) (hp : Integrable (p i) (distribution E)) :
    ∫ t, (virtualValue E i (t i) - cbarC E i (t i)) * p i t ∂distribution E =
      ∫ s in E.a i..E.b i,
        ((virtualValue E i s - ironedPriority E i s) * E.f i s) * Q E p i s := by
  rw [integral_update E i _ (int1 E i hp)]
  simp only [Function.update_self]
  simp_rw [integral_const_mul]
  rw [integral_mu, intervalIntegral.integral_of_le (E.a_lt_b i).le, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  simp only [Q, cbarC_eq E i hs]; ring

lemma psi_int (E : Environment ι) (i : ι) :
    IntegrableOn (fun s => (virtualValue E i s - ironedPriority E i s) * E.f i s)
      (Icc (E.a i) (E.b i)) := by
  have h := (intervalIntegrable_iff_integrableOn_Icc_of_le (E.a_lt_b i).le).1
    ((vvf_ii E i (a_mem E i) (b_mem E i)).sub (gFf_ii E i (a_mem E i) (b_mem E i)))
  have e : (fun s => (virtualValue E i s - ironedPriority E i s) * E.f i s) =
      fun x => virtualValue E i x * E.f i x - g E i (F E i x) * E.f i x := by
    funext s; simp only [ironedPriority, sub_mul]
  rw [e]; exact h

lemma psi_tot (E : Environment ι) (i : ι) :
    ∫ s in E.a i..E.b i, (virtualValue E i s - ironedPriority E i s) * E.f i s = 0 := by
  rw [ironing_piece E i (a_mem E i), F_a, G_eq, Genv_zero (H_bdd E i 0), sub_self]

lemma term1_le (E : Environment ι) (p : Outcome ι) (hA : AdmissibleAllocation E p) (i : ι) :
    ∫ s in E.a i..E.b i,
      ((virtualValue E i s - ironedPriority E i s) * E.f i s) * Q E p i s ≤ 0 := by
  refine layer_cake_le (E.a_lt_b i).le _ _ (psi_int E i)
    (fun s hs r hr hsr => hA.2.1 i s hs r hr hsr) (psi_tot E i) (fun σ hσ => ?_)
  rw [ironing_piece E i hσ]
  have := Genv_le (H_bdd E i _) (F_mem E i hσ)
  rw [G_eq]; linarith

lemma term1_bar (E : Environment ι) (i : ι) :
    ∫ s in E.a i..E.b i,
      ((virtualValue E i s - ironedPriority E i s) * E.f i s) * Q E (pbar E) i s = 0 := by
  refine layer_cake_eq (E.a_lt_b i).le _ _ (psi_int E i) (Qbar_mono E i) (psi_tot E i)
    (fun σ hσ hne => ?_)
  have hσI : σ ∈ Icc (E.a i) (E.b i) := Ioo_subset_Icc_self hσ
  rw [ironing_piece E i hσI] at hne
  have hle := Genv_le (H_bdd E i _) (F_mem E i hσI)
  rw [G_eq] at hne
  have hlt : Genv (H E i) (F E i σ) < H E i (F E i σ) := lt_of_le_of_ne hle (sub_ne_zero.1 hne)
  obtain ⟨M, -, hL0, -⟩ := H_bounds E i
  obtain ⟨l, r, hl, hr, hconst⟩ :=
    gEnv_locconst (H_contOn E i) (H_bdd E i) hL0 (F_mem E i hσI) hlt
  have hcont : ContinuousAt (F E i) σ := (F_contOn E i).continuousAt (Icc_mem_nhds hσ.1 hσ.2)
  obtain ⟨l', r', hσ', hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.1 (hcont.preimage_mem_nhds (Ioo_mem_nhds hl hr))
  refine ⟨l', r', hσ'.1, hσ'.2, fun y hy => ?_⟩
  have hFy : F E i y ∈ Ioo l r := hsub hy.1
  have hip : ironedPriority E i y = ironedPriority E i σ := by
    simp only [ironedPriority, g_eq]; exact hconst _ hFy
  unfold Q
  congr 1; funext t
  exact pbar_update_congr E t i hip

lemma T2_le [Nonempty ι] (E : Environment ι) (p : Outcome ι) (hA : AdmissibleAllocation E p) :
    ∫ t, ∑ i, (cbarC E i (t i) - E.t0) * p i t ∂distribution E ≤
      ∫ t, ∑ i, (cbarC E i (t i) - E.t0) * pbar E i t ∂distribution E := by
  refine integral_mono_ae (integrable_finsetSum _ fun i _ => int2 E i (hA.2.2 i).1)
    (integrable_finsetSum _ fun i _ => int2 E i (pbar_int E i).1) ?_
  filter_upwards [ae_support E] with t ht
  have hpb : ∀ i, pbar E i t = pbarC E i t := fun i => pbar_eq_pbarC E i ht
  simp only [hpb, pbarC]
  exact share_opt E (fun j => cbarC E j (t j)) (fun i => p i t) (fun i => (hA.1 t ht).2 i)
    (hA.1 t ht).1

theorem K3 [Nonempty ι] (E : Environment ι) (p : Outcome ι) (hA : AdmissibleAllocation E p) :
    virtualObjective E p ≤ virtualObjective E (pbar E) := by
  have hpb : ∀ i, Integrable (pbar E i) (distribution E) := fun i => (pbar_int E i).1
  rw [VO_split E p (fun i => (hA.2.2 i).1), VO_split E (pbar E) hpb]
  have h1 : ∑ i, ∫ t, (virtualValue E i (t i) - cbarC E i (t i)) * p i t ∂distribution E ≤ 0 :=
    Finset.sum_nonpos fun i _ => by rw [term1_eq E i p (hA.2.2 i).1]; exact term1_le E p hA i
  have h2 : ∑ i, ∫ t, (virtualValue E i (t i) - cbarC E i (t i)) * pbar E i t ∂distribution E = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [term1_eq E i _ (hpb i)]; exact term1_bar E i
  have h3 := T2_le E p hA
  linarith

end HBlock


end MyersonAuction.Optimal.Pf

open MyersonAuction.Optimal in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : Environment ι) : IsOptimal E (pbar E) (xbar E) := by
  obtain ⟨hF, hU0⟩ := Pf.K4 E
  refine ⟨hF, fun p' x' hF' => ?_⟩
  obtain ⟨hMQ', hEnv'⟩ := Pf.K1 hF'
  obtain ⟨hMQ, hEnv⟩ := Pf.K1 hF
  rw [Pf.K2 hF'.1 hEnv' hMQ', Pf.K2 hF.1 hEnv hMQ]
  have hA : AdmissibleAllocation E p' :=
    ⟨hF'.2.1, hMQ', fun i => ⟨(hF'.1 i).1, fun s hs => ((hF'.1 i).2.2 s hs).1⟩⟩
  have h3 := Pf.K3 E p' hA
  have h4 : ∑ i, interimUtility E (pbar E) (xbar E) i (E.a i) = 0 :=
    Finset.sum_eq_zero fun i _ => hU0 i
  have h5 : 0 ≤ ∑ i, interimUtility E p' x' i (E.a i) :=
    Finset.sum_nonneg fun i _ => hEnv'.2 i
  linarith
