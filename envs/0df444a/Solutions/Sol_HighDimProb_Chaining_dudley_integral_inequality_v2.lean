-- Prove2me | solution 1 for HighDimProb.Chaining.dudley_integral_inequality_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T17:50:35.538383+00:00
-- url     : https://prove2.me/submissions/a87f2ff4-abf6-4947-90be-4d7e87cd546f

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm_v2
import Definitions.Def_HighDimProb_Chaining_CoveringNumber
import Definitions.Def_HighDimProb_Chaining_ProcessESup

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace DudleyAux

lemma pw (x L : ℝ) (hx : 0 ≤ x) (hL : 0 ≤ L) :
    x ≤ Real.sqrt L + 1 + Real.exp (x ^ 2 - L) := by
  by_cases h : x ≤ Real.sqrt L + 1
  · linarith [Real.exp_pos (x ^ 2 - L)]
  · push Not at h
    have hs := Real.sq_sqrt hL
    have hs0 := Real.sqrt_nonneg L
    have hm : 0 ≤ (x - Real.sqrt L) * (x + Real.sqrt L - 1) :=
      mul_nonneg (by linarith) (by linarith)
    have h1 : x - Real.sqrt L ≤ x ^ 2 - L := by nlinarith
    have h2 := Real.add_one_le_exp (x ^ 2 - L)
    linarith

lemma adm_of_lt {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ) (u : ℝ)
    (h : HighDimProb.Concentration.subgaussianNorm P Y < ENNReal.ofReal u) :
    ∃ t, 0 < t ∧ t < u ∧ Integrable (fun ω => Real.exp ((Y ω) ^ 2 / t ^ 2)) P ∧
      ∫ ω, Real.exp ((Y ω) ^ 2 / t ^ 2) ∂P ≤ 2 := by
  unfold HighDimProb.Concentration.subgaussianNorm at h
  simp only [iInf_lt_iff] at h
  obtain ⟨t, ht, hi, hle, hlt⟩ := h
  exact ⟨t, ht, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).1 hlt, hi, hle⟩

lemma adm_u {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ) (hY : Integrable Y P)
    (u : ℝ) (h : HighDimProb.Concentration.subgaussianNorm P Y < ENNReal.ofReal u) :
    Integrable (fun ω => Real.exp ((Y ω) ^ 2 / u ^ 2)) P ∧
      ∫ ω, Real.exp ((Y ω) ^ 2 / u ^ 2) ∂P ≤ 2 := by
  obtain ⟨t, ht, htu, hi, hle⟩ := adm_of_lt P Y u h
  have hpt : ∀ ω, Real.exp ((Y ω) ^ 2 / u ^ 2) ≤ Real.exp ((Y ω) ^ 2 / t ^ 2) := by
    intro ω
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    exact pow_le_pow_left₀ ht.le htu.le 2
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp ((Y ω) ^ 2 / u ^ 2)) P :=
    (Real.continuous_exp.comp ((continuous_pow 2).div_const (u ^ 2))).comp_aestronglyMeasurable
      hY.aestronglyMeasurable
  have hI : Integrable (fun ω => Real.exp ((Y ω) ^ 2 / u ^ 2)) P := by
    refine hi.mono' hmeas (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hpt ω
  exact ⟨hI, (integral_mono hI hi hpt).trans hle⟩

lemma integrable_sup' {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {ι : Type}
    (s : Finset ι) (hs : s.Nonempty) (Y : ι → Ω → ℝ) (hY : ∀ i ∈ s, Integrable (Y i) P) :
    Integrable (fun ω => s.sup' hs (fun i => Y i ω)) P := by
  have : (fun ω => s.sup' hs (fun i => Y i ω)) = s.sup' hs Y := by
    funext ω; rw [Finset.sup'_apply]
  rw [this]
  exact Finset.sup'_induction (p := fun f => Integrable f P) hs Y (fun a ha b hb => Integrable.sup ha hb) hY

theorem maxIneq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type} (s : Finset ι) (hs : s.Nonempty) (Y : ι → Ω → ℝ) (K : ℝ) (hK0 : 0 ≤ K)
    (hY : ∀ i ∈ s, Integrable (Y i) P ∧ ∫ ω, Y i ω ∂P = 0)
    (hK : ∀ i ∈ s, HighDimProb.Concentration.subgaussianNorm P (Y i) ≤ ENNReal.ofReal K) :
    ∫ ω, s.sup' hs (fun i => Y i ω) ∂P ≤ 5 * K * Real.sqrt (Real.log s.card) := by
  have hcard : 1 ≤ s.card := hs.card_pos
  rcases Nat.lt_or_ge s.card 2 with h1 | h2
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 (show s.card = 1 by omega)
    simp only [Finset.sup'_singleton, Finset.card_singleton, Nat.cast_one, Real.log_one,
      Real.sqrt_zero, mul_zero]
    exact (hY i (Finset.mem_singleton_self i)).2.le
  set n : ℕ := s.card with hn
  set L : ℝ := Real.log (2 * n) with hL
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
  have hLpos : 0 ≤ L := Real.log_nonneg (by linarith)
  have hexpL : Real.exp L = 2 * n := Real.exp_log (by linarith)
  have hlogn : (4 / 9 : ℝ) ≤ Real.log n := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hn2
    linarith
  have hLle : L ≤ 4 * Real.log n := by
    rw [hL, Real.log_mul (by norm_num) (by linarith)]
    have := Real.log_le_log (by norm_num) hn2
    linarith
  have hsq4 : Real.sqrt (4 * Real.log n) = 2 * Real.sqrt (Real.log n) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hsq : 2 / 3 ≤ Real.sqrt (Real.log n) := by
    have h49 : Real.sqrt (4 / 9) = 2 / 3 := by
      rw [show (4 / 9 : ℝ) = (2 / 3) ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    rw [← h49]; exact Real.sqrt_le_sqrt hlogn
  have hconst : Real.sqrt L + 2 ≤ 5 * Real.sqrt (Real.log n) := by
    have := Real.sqrt_le_sqrt hLle
    rw [hsq4] at this
    linarith
  have hsqpos : 0 < Real.sqrt (Real.log n) := by linarith
  -- main bound for every u > K
  have key : ∀ u : ℝ, K < u →
      ∫ ω, s.sup' hs (fun i => Y i ω) ∂P ≤ u * (Real.sqrt L + 2) := by
    intro u hu
    have hu0 : 0 < u := lt_of_le_of_lt hK0 hu
    have hlt : ∀ i ∈ s, HighDimProb.Concentration.subgaussianNorm P (Y i) < ENNReal.ofReal u :=
      fun i hi => lt_of_le_of_lt (hK i hi) ((ENNReal.ofReal_lt_ofReal_iff hu0).2 hu)
    have hadm := fun i hi => adm_u P (Y i) (hY i hi).1 u (hlt i hi)
    set F : Ω → ℝ := fun ω => ∑ j ∈ s, Real.exp ((Y j ω) ^ 2 / u ^ 2) with hF
    have hFi : Integrable F P := integrable_finsetSum _ fun j hj => (hadm j hj).1
    have hFint : ∫ ω, F ω ∂P ≤ 2 * n := by
      rw [hF, integral_finsetSum _ fun j hj => (hadm j hj).1]
      calc ∑ j ∈ s, ∫ ω, Real.exp ((Y j ω) ^ 2 / u ^ 2) ∂P ≤ ∑ j ∈ s, (2 : ℝ) :=
            Finset.sum_le_sum fun j hj => (hadm j hj).2
        _ = 2 * n := by rw [Finset.sum_const, nsmul_eq_mul, hn]; ring
    have hpt : ∀ ω, s.sup' hs (fun i => Y i ω) ≤
        u * (Real.sqrt L + 1) + u / (2 * n) * F ω := by
      intro ω
      apply Finset.sup'_le
      intro i hi
      have hx := pw (|Y i ω| / u) L (by positivity) hLpos
      have hsq' : (|Y i ω| / u) ^ 2 = (Y i ω) ^ 2 / u ^ 2 := by rw [div_pow, sq_abs]
      rw [hsq', Real.exp_sub, hexpL] at hx
      have hFge : Real.exp ((Y i ω) ^ 2 / u ^ 2) ≤ F ω :=
        Finset.single_le_sum (f := fun j => Real.exp ((Y j ω) ^ 2 / u ^ 2))
          (fun j _ => (Real.exp_pos _).le) hi
      have h1 : Y i ω ≤ |Y i ω| := le_abs_self _
      have h2 : |Y i ω| = u * (|Y i ω| / u) := by field_simp
      have h3 : u * (|Y i ω| / u) ≤ u * (Real.sqrt L + 1 + Real.exp ((Y i ω) ^ 2 / u ^ 2) / (2 * n)) :=
        mul_le_mul_of_nonneg_left hx hu0.le
      have h4 : u * (Real.exp ((Y i ω) ^ 2 / u ^ 2) / (2 * n)) ≤ u / (2 * n) * F ω := by
        rw [mul_div_assoc', div_mul_eq_mul_div]
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_left hFge hu0.le
      nlinarith
    have hRi : Integrable (fun ω => u * (Real.sqrt L + 1) + u / (2 * n) * F ω) P :=
      (integrable_const _).add (hFi.const_mul _)
    calc ∫ ω, s.sup' hs (fun i => Y i ω) ∂P
        ≤ ∫ ω, (u * (Real.sqrt L + 1) + u / (2 * n) * F ω) ∂P :=
          integral_mono (integrable_sup' P s hs Y fun i hi => (hY i hi).1) hRi hpt
      _ = u * (Real.sqrt L + 1) + u / (2 * n) * ∫ ω, F ω ∂P := by
          rw [integral_add (integrable_const _) (hFi.const_mul _), integral_const,
            integral_const_mul]
          simp
      _ ≤ u * (Real.sqrt L + 1) + u / (2 * n) * (2 * n) := by
          gcongr
      _ = u * (Real.sqrt L + 2) := by field_simp; ring
  -- let u ↓ K
  have hfin : (∫ ω, s.sup' hs (fun i => Y i ω) ∂P) / (5 * Real.sqrt (Real.log n)) ≤ K := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro u hu
    rw [div_le_iff₀ (by positivity)]
    have hu0 : 0 < u := lt_of_le_of_lt hK0 hu
    calc _ ≤ u * (Real.sqrt L + 2) := key u hu
      _ ≤ u * (5 * Real.sqrt (Real.log n)) := mul_le_mul_of_nonneg_left hconst hu0.le
  rw [div_le_iff₀ (by positivity)] at hfin
  linarith


open HighDimProb.Chaining

lemma cov_anti {T : Type} [MetricSpace T] {ε ε' : ℝ} (h : ε ≤ ε') :
    coveringNumber T ε' ≤ coveringNumber T ε := by
  unfold coveringNumber
  refine le_iInf fun N => ?_
  exact iInf_le_of_le ⟨N.1, fun t => (N.2 t).imp fun t' ht' => ⟨ht'.1, ht'.2.trans h⟩⟩ le_rfl

lemma net_exists {T : Type} [MetricSpace T] (ε : ℝ) (h : coveringNumber T ε ≠ ⊤) :
    ∃ s : Finset T, (∀ t, ∃ t' ∈ s, dist t t' ≤ ε) ∧ s.card ≤ (coveringNumber T ε).toNat := by
  have hce : coveringNumber T ε = ((coveringNumber T ε).toNat : ℕ∞) := (ENat.coe_toNat h).symm
  have hlt : coveringNumber T ε < (((coveringNumber T ε).toNat + 1 : ℕ) : ℕ∞) := by
    conv_lhs => rw [hce]
    exact_mod_cast Nat.lt_succ_self _
  have hlt' := hlt
  unfold coveringNumber at hlt'
  obtain ⟨N, hN⟩ := iInf_lt_iff.1 hlt'
  refine ⟨N.1, N.2, ?_⟩
  have : N.1.card < (coveringNumber T ε).toNat + 1 := by exact_mod_cast hN
  omega

lemma sep_exists {T : Type} [MetricSpace T] (T0 : Finset T) :
    ∃ η > 0, ∀ t ∈ T0, ∀ t' ∈ T0, t ≠ t' → η ≤ dist t t' := by
  classical
  set D := ((T0 ×ˢ T0).filter (fun p => p.1 ≠ p.2)).image (fun p => dist p.1 p.2) with hDdef
  by_cases hD : D.Nonempty
  · refine ⟨D.min' hD, ?_, ?_⟩
    · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 (D.min'_mem hD)
      rw [← hpe]
      simp only [Finset.mem_filter] at hp
      exact dist_pos.2 hp.2
    · intro t ht t' ht' hne
      apply D.min'_le
      exact Finset.mem_image.2
        ⟨(t, t'), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ht, ht'⟩, hne⟩, rfl⟩
  · refine ⟨1, one_pos, fun t ht t' ht' hne => absurd ⟨_, Finset.mem_image.2
      ⟨(t, t'), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ht, ht'⟩, hne⟩, rfl⟩⟩ hD⟩

lemma card_le_cov {T : Type} [MetricSpace T] (T0 : Finset T) (η ε : ℝ)
    (hsep : ∀ t ∈ T0, ∀ t' ∈ T0, t ≠ t' → η ≤ dist t t') (hε : 2 * ε < η)
    (h : coveringNumber T ε ≠ ⊤) : T0.card ≤ (coveringNumber T ε).toNat := by
  obtain ⟨s, hs, hcard⟩ := net_exists ε h
  refine le_trans ?_ hcard
  choose f hf using hs
  apply Finset.card_le_card_of_injOn f
  · intro t _
    exact (hf t).1
  · intro a ha b hb hab
    by_contra hne
    have h1 := hsep a ha b hb hne
    have h2 := dist_triangle a (f a) b
    have h3 := (hf a).2
    have h4 := (hf b).2
    rw [hab] at h2 h3
    rw [dist_comm] at h4
    linarith

lemma sqrtlog_mono {a b : ℕ} (h : a ≤ b) :
    Real.sqrt (Real.log a) ≤ Real.sqrt (Real.log b) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [Real.sqrt_nonneg]
  · exact Real.sqrt_le_sqrt (Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast h))

noncomputable def ig (T : Type) [MetricSpace T] (ε : ℝ) : ℝ≥0∞ :=
  if coveringNumber T ε = ⊤ then (⊤ : ℝ≥0∞)
  else ENNReal.ofReal (Real.sqrt (Real.log ((coveringNumber T ε).toNat : ℝ)))

lemma ig_anti {T : Type} [MetricSpace T] {ε ε' : ℝ} (h : ε ≤ ε') : ig T ε' ≤ ig T ε := by
  unfold ig
  by_cases h1 : coveringNumber T ε = ⊤
  · simp [h1]
  · have h2 := cov_anti (T := T) h
    have h3 : coveringNumber T ε' ≠ ⊤ := ne_top_of_le_ne_top h1 h2
    rw [if_neg h1, if_neg h3]
    apply ENNReal.ofReal_le_ofReal
    exact sqrtlog_mono (ENat.toNat_le_toNat h2 h1)

lemma cov_ne_top {T : Type} [MetricSpace T]
    (hI : ∫⁻ ε in Set.Ioi (0 : ℝ), ig T ε ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    coveringNumber T ε ≠ ⊤ := by
  intro htop
  apply hI
  have higε : ig T ε = ⊤ := by unfold ig; simp [htop]
  have hle : ∫⁻ x in Set.Ioc (0 : ℝ) ε, (⊤ : ℝ≥0∞) ≤ ∫⁻ x in Set.Ioi (0 : ℝ), ig T x := by
    calc ∫⁻ x in Set.Ioc (0 : ℝ) ε, (⊤ : ℝ≥0∞) ≤ ∫⁻ x in Set.Ioc (0 : ℝ) ε, ig T x := by
          apply lintegral_mono_ae
          refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun x hx => ?_)
          have := ig_anti (T := T) hx.2
          rw [higε] at this
          exact this
      _ ≤ _ := lintegral_mono_set Set.Ioc_subset_Ioi_self
  rw [setLIntegral_const, Real.volume_Ioc, ENNReal.top_mul (by simpa using hε)] at hle
  exact top_le_iff.1 hle

lemma dyadic_le {T : Type} [MetricSpace T] (R : ℝ) (hR : 0 < R) (M : ℕ) :
    ENNReal.ofReal (∑ k ∈ Finset.range M, R / 2 ^ (k + 1) *
        Real.sqrt (Real.log ((coveringNumber T (R / 2 ^ (k + 1))).toNat : ℝ)))
      ≤ 2 * ∫⁻ ε in Set.Ioi (0 : ℝ), ig T ε := by
  set A : ℕ → Set ℝ := fun k => Set.Ioc (R / 2 ^ (k + 2)) (R / 2 ^ (k + 1)) with hA
  have hdec : ∀ j k : ℕ, j ≤ k → R / 2 ^ k ≤ R / 2 ^ j := fun j k h =>
    div_le_div_of_nonneg_left hR.le (by positivity) (pow_le_pow_right₀ (by norm_num) h)
  have hterm : ∀ k, ENNReal.ofReal (R / 2 ^ (k + 1) *
      Real.sqrt (Real.log ((coveringNumber T (R / 2 ^ (k + 1))).toNat : ℝ)))
        ≤ 2 * ∫⁻ ε in A k, ig T ε := by
    intro k
    set c := Real.sqrt (Real.log ((coveringNumber T (R / 2 ^ (k + 1))).toNat : ℝ)) with hc
    have hlow : ∫⁻ ε in A k, ENNReal.ofReal c ≤ ∫⁻ ε in A k, ig T ε := by
      apply lintegral_mono_ae
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun x hx => ?_)
      refine le_trans ?_ (ig_anti (T := T) hx.2)
      unfold ig
      split_ifs <;> simp [hc]
    rw [setLIntegral_const, Real.volume_Ioc] at hlow
    have heq : R / 2 ^ (k + 1) - R / 2 ^ (k + 2) = (R / 2 ^ (k + 1)) / 2 := by
      rw [pow_succ 2 (k + 1)]; ring
    rw [heq] at hlow
    have hre : R / 2 ^ (k + 1) * c = 2 * (c * ((R / 2 ^ (k + 1)) / 2)) := by ring
    rw [hre, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ENNReal.ofReal_ofNat]
    gcongr
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range M)) A := by
    intro i _ j _ hij
    refine Set.disjoint_left.2 fun x hxi hxj => ?_
    simp only [hA, Set.mem_Ioc] at hxi hxj
    rcases lt_or_gt_of_ne hij with h | h
    · have := hdec (i + 2) (j + 1) (by omega)
      linarith [hxi.1, hxj.2]
    · have := hdec (j + 2) (i + 1) (by omega)
      linarith [hxj.1, hxi.2]
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
  calc ∑ k ∈ Finset.range M, ENNReal.ofReal (R / 2 ^ (k + 1) *
          Real.sqrt (Real.log ((coveringNumber T (R / 2 ^ (k + 1))).toNat : ℝ)))
      ≤ ∑ k ∈ Finset.range M, 2 * ∫⁻ ε in A k, ig T ε := Finset.sum_le_sum fun k _ => hterm k
    _ = 2 * ∫⁻ ε in ⋃ k ∈ Finset.range M, A k, ig T ε := by
        rw [← Finset.mul_sum, lintegral_biUnion_finset hdisj (fun k _ => measurableSet_Ioc)]
    _ ≤ 2 * ∫⁻ ε in Set.Ioi (0 : ℝ), ig T ε := by
        gcongr
        intro x hx
        simp only [Set.mem_iUnion] at hx
        obtain ⟨k, _, hk⟩ := hx
        exact lt_trans (by positivity) hk.1

lemma chain_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : Type} [DecidableEq T] (X : T → Ω → ℝ)
    (hX : ∀ t, Integrable (X t) P ∧ ∫ ω, X t ω ∂P = 0)
    (T0 : Finset T) (h0 : T0.Nonempty) (m : ℕ) (π : ℕ → T → T) (t0 : T)
    (hπ0 : ∀ t ∈ T0, π 0 t = t0) (hπm : ∀ t ∈ T0, π m t = t) :
    ∫ ω, T0.sup' h0 (fun t => X t ω) ∂P ≤
      ∑ n ∈ Finset.range m, ∫ ω, (T0.image (fun t => (π (n + 1) t, π n t))).sup' (h0.image _)
        (fun p => X p.1 ω - X p.2 ω) ∂P := by
  let G : ℕ → Ω → ℝ := fun n ω => (T0.image (fun t => (π (n + 1) t, π n t))).sup'
    (h0.image _) (fun p => X p.1 ω - X p.2 ω)
  have hGi : ∀ n, Integrable (G n) P := fun n =>
    integrable_sup' P (T0.image (fun t => (π (n + 1) t, π n t))) (h0.image _)
      (fun p ω => X p.1 ω - X p.2 ω) (fun p _ => (hX p.1).1.sub (hX p.2).1)
  have hpt : ∀ ω, T0.sup' h0 (fun t => X t ω) ≤ X t0 ω + ∑ n ∈ Finset.range m, G n ω := by
    intro ω
    apply Finset.sup'_le
    intro t ht
    have htel := Finset.sum_range_sub (fun n => X (π n t) ω) m
    try simp only at htel
    rw [hπm t ht, hπ0 t ht] at htel
    have hle : ∑ n ∈ Finset.range m, (X (π (n + 1) t) ω - X (π n t) ω) ≤
        ∑ n ∈ Finset.range m, G n ω := by
      apply Finset.sum_le_sum
      intro n _
      exact Finset.le_sup' (fun p : T × T => X p.1 ω - X p.2 ω)
        (Finset.mem_image_of_mem (fun t => (π (n + 1) t, π n t)) ht)
    linarith
  have hsumi : Integrable (fun ω => ∑ n ∈ Finset.range m, G n ω) P :=
    integrable_finsetSum _ fun n _ => hGi n
  calc ∫ ω, T0.sup' h0 (fun t => X t ω) ∂P
      ≤ ∫ ω, (X t0 ω + ∑ n ∈ Finset.range m, G n ω) ∂P :=
        integral_mono (integrable_sup' P T0 h0 X fun t _ => (hX t).1) ((hX t0).1.add hsumi) hpt
    _ = ∑ n ∈ Finset.range m, ∫ ω, G n ω ∂P := by
        rw [integral_add (hX t0).1 hsumi, (hX t0).2, zero_add,
          integral_finsetSum _ fun n _ => hGi n]

end DudleyAux

namespace DudleyAux
open HighDimProb.Chaining

lemma finite_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : Type} [MetricSpace T] (X : T → Ω → ℝ) (K : ℝ≥0)
    (hX : ∀ t, Integrable (X t) P ∧ ∫ ω, X t ω ∂P = 0)
    (hK : ∀ t s, HighDimProb.Concentration.subgaussianNorm P (fun ω => X t ω - X s ω) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (dist t s))
    (T0 : Finset T) (h0 : T0.Nonempty) :
    ((∫ ω, T0.sup' h0 (fun t => X t ω) ∂P : ℝ) : EReal) ≤
      ((ENNReal.ofReal 60 * (K : ℝ≥0∞) * ∫⁻ ε in Set.Ioi (0 : ℝ), ig T ε : ℝ≥0∞) : EReal) := by
  classical
  have ⟨t0, ht0⟩ := h0
  have hKd : ∀ t s (d : ℝ), dist t s ≤ d →
      HighDimProb.Concentration.subgaussianNorm P (fun ω => X t ω - X s ω) ≤
        ENNReal.ofReal ((K : ℝ) * d) := by
    intro t s d hd
    refine (hK t s).trans ?_
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hd K.coe_nonneg)
  have hmz : ∀ p : T × T, Integrable (fun ω => X p.1 ω - X p.2 ω) P ∧
      ∫ ω, (X p.1 ω - X p.2 ω) ∂P = 0 := fun p =>
    ⟨(hX p.1).1.sub (hX p.2).1, by
      rw [integral_sub (hX p.1).1 (hX p.2).1, (hX p.1).2, (hX p.2).2, sub_zero]⟩
  suffices hreal : ∃ S : ℝ, 0 ≤ S ∧ ENNReal.ofReal S ≤ 2 * ∫⁻ ε in Set.Ioi (0 : ℝ), ig T ε ∧
      ∫ ω, T0.sup' h0 (fun t => X t ω) ∂P ≤ 30 * K * S by
    obtain ⟨S, hS0, hSI, hE⟩ := hreal
    calc ((∫ ω, T0.sup' h0 (fun t => X t ω) ∂P : ℝ) : EReal)
        ≤ ((ENNReal.ofReal (∫ ω, T0.sup' h0 (fun t => X t ω) ∂P) : ℝ≥0∞) : EReal) := by
          rw [EReal.coe_ennreal_ofReal]
          exact le_max_left ((∫ ω, T0.sup' h0 (fun t => X t ω) ∂P : ℝ) : EReal) 0
      _ ≤ ((ENNReal.ofReal 60 * (K : ℝ≥0∞) * ∫⁻ ε in Set.Ioi (0 : ℝ), ig T ε : ℝ≥0∞) : EReal) := by
          rw [EReal.coe_ennreal_le_coe_ennreal_iff]
          calc ENNReal.ofReal (∫ ω, T0.sup' h0 (fun t => X t ω) ∂P)
              ≤ ENNReal.ofReal (30 * K * S) := ENNReal.ofReal_le_ofReal hE
            _ = ENNReal.ofReal 30 * K * ENNReal.ofReal S := by
                rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
                  ENNReal.ofReal_coe_nnreal]
            _ ≤ ENNReal.ofReal 30 * K * (2 * ∫⁻ ε in Set.Ioi (0 : ℝ), ig T ε) := by gcongr
            _ = ENNReal.ofReal 60 * (K : ℝ≥0∞) * ∫⁻ ε in Set.Ioi (0 : ℝ), ig T ε := by
                rw [show (60 : ℝ) = 30 * 2 by norm_num, ENNReal.ofReal_mul (by norm_num)]
                simp only [ENNReal.ofReal_ofNat]
                ring
  by_cases hK0 : (K : ℝ) = 0
  · refine ⟨0, le_rfl, by simp, ?_⟩
    have hc := chain_bound P X hX T0 h0 1 (fun n t => if n = 0 then t0 else t) t0
      (fun t _ => by simp) (fun t _ => by simp)
    rw [Finset.sum_range_one] at hc
    refine hc.trans ((maxIneq P _ _ (fun p ω => X p.1 ω - X p.2 ω) 0 le_rfl
      (fun p _ => hmz p) ?_).trans (by simp))
    intro p _
    have := hKd p.1 p.2 _ le_rfl
    rwa [hK0, zero_mul] at this
  by_cases hI : ∫⁻ ε in Set.Ioi (0 : ℝ), ig T ε = ⊤
  · have hKpos : 0 < (K : ℝ) := lt_of_le_of_ne K.coe_nonneg (Ne.symm hK0)
    refine ⟨max ((∫ ω, T0.sup' h0 (fun t => X t ω) ∂P) / (30 * K)) 0, le_max_right _ _,
      by rw [hI]; simp, ?_⟩
    calc _ = 30 * K * ((∫ ω, T0.sup' h0 (fun t => X t ω) ∂P) / (30 * K)) := by
          field_simp
      _ ≤ _ := by gcongr; exact le_max_left _ _
  -- main case: all covering numbers finite
  have hR : 0 < 1 + ∑ t ∈ T0, dist t t0 := by
    have := Finset.sum_nonneg (fun t (_ : t ∈ T0) => dist_nonneg (x := t) (y := t0)); linarith
  set R : ℝ := 1 + ∑ t ∈ T0, dist t t0 with hRdef
  have hdR : ∀ t ∈ T0, dist t t0 ≤ R := fun t ht => by
    have := Finset.single_le_sum (f := fun t => dist t t0) (fun _ _ => dist_nonneg) ht
    try simp only at this
    linarith
  have hdec : ∀ j k : ℕ, j ≤ k → R / 2 ^ k ≤ R / 2 ^ j := fun j k h =>
    div_le_div_of_nonneg_left hR.le (by positivity) (pow_le_pow_right₀ (by norm_num) h)
  obtain ⟨η, hη, hsep⟩ := sep_exists T0
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (2 * R / η) (one_lt_two : (1 : ℝ) < 2)
  have hm' : 2 * (R / 2 ^ m) < η := by
    rw [div_lt_iff₀ hη] at hm
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    linarith
  have hcov : ∀ k : ℕ, coveringNumber T (R / 2 ^ k) ≠ ⊤ := fun k =>
    cov_ne_top hI (by positivity)
  have hnet := fun k : ℕ => net_exists (T := T) (R / 2 ^ k) (hcov k)
  choose Snet hSnet hScard using hnet
  choose pr hpr hprd using hSnet
  let π : ℕ → T → T := fun n t => if n = 0 then t0 else if n = m + 1 then t else pr n t
  have hπd : ∀ n, n ≤ m + 1 → ∀ t ∈ T0, dist (π n t) t ≤ R / 2 ^ n := by
    intro n hn t ht
    simp only [π]
    split_ifs with h1 h2
    · subst h1; rw [dist_comm]; simpa using hdR t ht
    · simp only [dist_self]; positivity
    · rw [dist_comm]; exact hprd n t
  have hπc : ∀ n, 1 ≤ n → n ≤ m + 1 →
      (T0.image (π n)).card ≤ (coveringNumber T (R / 2 ^ n)).toNat := by
    intro n h1 h2
    rcases Nat.lt_or_ge n (m + 1) with h | h
    · have hsub : T0.image (π n) ⊆ Snet n := by
        intro x hx
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
        simp only [π, if_neg (by omega : n ≠ 0), if_neg (by omega : n ≠ m + 1)]
        exact hpr n t
      exact (Finset.card_le_card hsub).trans (hScard n)
    · have hn : n = m + 1 := by omega
      subst hn
      refine Finset.card_image_le.trans ?_
      apply card_le_cov T0 η _ hsep _ (hcov _)
      have := hdec m (m + 1) (by omega)
      linarith
  have hπ0c : (T0.image (π 0)).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro a ha b hb
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨t', _, rfl⟩ := Finset.mem_image.1 hb
    simp [π]
  have hlev : ∀ n ∈ Finset.range (m + 1),
      ∫ ω, (T0.image (fun t => (π (n + 1) t, π n t))).sup' (h0.image _)
          (fun p => X p.1 ω - X p.2 ω) ∂P ≤
        30 * K * (R / 2 ^ (n + 1) *
          Real.sqrt (Real.log ((coveringNumber T (R / 2 ^ (n + 1))).toNat : ℝ))) := by
    intro n hn
    rw [Finset.mem_range] at hn
    set Nn := (coveringNumber T (R / 2 ^ (n + 1))).toNat with hNn
    have hd : ∀ p ∈ T0.image (fun t => (π (n + 1) t, π n t)),
        dist p.1 p.2 ≤ 3 * (R / 2 ^ (n + 1)) := by
      intro p hp
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hp
      have h1 := hπd (n + 1) (by omega) t ht
      have h2 := hπd n (by omega) t ht
      have h3 := dist_triangle (π (n + 1) t) t (π n t)
      rw [dist_comm t] at h3
      have : R / 2 ^ n = 2 * (R / 2 ^ (n + 1)) := by rw [pow_succ]; field_simp
      simp only at h3 ⊢
      linarith
    have hc1 : (T0.image (π (n + 1))).card ≤ Nn := hπc (n + 1) (by omega) (by omega)
    have hc0 : (T0.image (π n)).card ≤ Nn := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        have : 1 ≤ (T0.image (π 1)).card := (h0.image _).card_pos
        exact hπ0c.trans (this.trans hc1)
      · refine (hπc n h (by omega)).trans ?_
        exact ENat.toNat_le_toNat (cov_anti (hdec n (n + 1) (by omega))) (hcov (n + 1))
    have hcard : (T0.image (fun t => (π (n + 1) t, π n t))).card ≤ Nn ^ 2 := by
      have hsub : T0.image (fun t => (π (n + 1) t, π n t)) ⊆
          (T0.image (π (n + 1))) ×ˢ (T0.image (π n)) := by
        intro p hp
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hp
        exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ ht, Finset.mem_image_of_mem _ ht⟩
      calc _ ≤ _ := Finset.card_le_card hsub
        _ = _ := Finset.card_product _ _
        _ ≤ Nn * Nn := Nat.mul_le_mul hc1 hc0
        _ = _ := (sq _).symm
    have hsl : Real.sqrt (Real.log ((T0.image (fun t => (π (n + 1) t, π n t))).card : ℝ)) ≤
        2 * Real.sqrt (Real.log (Nn : ℝ)) := by
      refine (sqrtlog_mono hcard).trans ?_
      rw [Nat.cast_pow, Real.log_pow]
      have hl0 : 0 ≤ Real.log (Nn : ℝ) := Real.log_natCast_nonneg _
      calc Real.sqrt (((2 : ℕ) : ℝ) * Real.log (Nn : ℝ))
          ≤ Real.sqrt (2 ^ 2 * Real.log (Nn : ℝ)) := Real.sqrt_le_sqrt (by push_cast; nlinarith)
        _ = 2 * Real.sqrt (Real.log (Nn : ℝ)) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    calc _ ≤ 5 * ((K : ℝ) * (3 * (R / 2 ^ (n + 1)))) *
            Real.sqrt (Real.log ((T0.image (fun t => (π (n + 1) t, π n t))).card : ℝ)) :=
          maxIneq P (T0.image (fun t => (π (n + 1) t, π n t))) (h0.image _)
            (fun p ω => X p.1 ω - X p.2 ω) ((K : ℝ) * (3 * (R / 2 ^ (n + 1)))) (by positivity)
            (fun p _ => hmz p) (fun p hp => hKd p.1 p.2 _ (hd p hp))
      _ ≤ 5 * ((K : ℝ) * (3 * (R / 2 ^ (n + 1)))) * (2 * Real.sqrt (Real.log (Nn : ℝ))) := by
          gcongr
      _ = _ := by ring
  refine ⟨∑ k ∈ Finset.range (m + 1), R / 2 ^ (k + 1) *
      Real.sqrt (Real.log ((coveringNumber T (R / 2 ^ (k + 1))).toNat : ℝ)),
    Finset.sum_nonneg fun k _ => by positivity, dyadic_le R hR (m + 1), ?_⟩
  calc _ ≤ _ := chain_bound P X hX T0 h0 (m + 1) π t0 (fun t _ => by simp [π])
        (fun t _ => by simp [π])
    _ ≤ ∑ n ∈ Finset.range (m + 1), 30 * K * (R / 2 ^ (n + 1) *
          Real.sqrt (Real.log ((coveringNumber T (R / 2 ^ (n + 1))).toNat : ℝ))) :=
        Finset.sum_le_sum hlev
    _ = _ := by rw [Finset.mul_sum]

end DudleyAux

open MeasureTheory ENNReal NNReal HighDimProb.Chaining in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {T : Type} [MetricSpace T] [Nonempty T] (X : T → Ω → ℝ) (K : ℝ≥0),
        (∀ t, Integrable (X t) P ∧ ∫ ω, X t ω ∂P = 0) →
        (∀ t s, HighDimProb.Concentration.subgaussianNorm P (fun ω => X t ω - X s ω) ≤
          (K : ℝ≥0∞) * ENNReal.ofReal (dist t s)) →
        processESup P X ≤
          ((ENNReal.ofReal C * (K : ℝ≥0∞) *
              ∫⁻ ε in Set.Ioi (0 : ℝ),
                (if coveringNumber T ε = ⊤ then (⊤ : ℝ≥0∞)
                 else ENNReal.ofReal
                   (Real.sqrt (Real.log ((coveringNumber T ε).toNat : ℝ)))) : ℝ≥0∞) : EReal) := by
  refine ⟨60, by norm_num, ?_⟩
  intro Ω _ P _ T _ _ X K hX hK
  unfold processESup
  refine iSup_le fun T0 => ?_
  exact DudleyAux.finite_bound P X K hX hK T0.1 T0.2
