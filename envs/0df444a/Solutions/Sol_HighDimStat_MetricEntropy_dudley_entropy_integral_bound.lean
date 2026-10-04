-- Prove2me | solution 1 for HighDimStat.MetricEntropy.dudley_entropy_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T13:16:40.730984+00:00
-- url     : https://prove2.me/submissions/c33f80ca-3ee6-4540-ae2e-9f2fa790bd04

import Mathlib
import Definitions.Def_HighDimStat_MetricEntropy_SubGaussianProcess
import Definitions.Def_HighDimStat_MetricEntropy_CoveringNumber
import Definitions.Def_HighDimStat_MetricEntropy_Diameter
import Definitions.Def_HighDimStat_MetricEntropy_IncrementSup
import Definitions.Def_HighDimStat_MetricEntropy_LocalIncrementSup
import Definitions.Def_HighDimStat_MetricEntropy_EntropyIntegral


open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace DudleyProof

lemma integrable_iSup_finite {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [Nonempty ι] (P : Measure Ω) (X : ι → Ω → ℝ)
    (hX : ∀ i, Integrable (X i) P) :
    Integrable (fun ω => ⨆ i, X i ω) P := by
  classical
  have hi : Integrable ((Finset.univ : Finset ι).sup' Finset.univ_nonempty X) P :=
    Finset.sup'_induction Finset.univ_nonempty X (p := fun Z : Ω → ℝ => Integrable Z P)
      (fun _ hf _ hg => hf.sup hg) (fun i _ => hX i)
  convert hi using 1
  funext ω
  rw [Finset.sup'_apply, Finset.sup'_univ_eq_ciSup]

/-- The exponential-moment maximum estimate, without any independence assumption. -/
lemma finite_max_mgf_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i, Integrable (X i) P) (β c : ℝ) (hβ : 0 < β)
    (hExp : ∀ i, Integrable (fun ω => Real.exp (β * X i ω)) P)
    (hMGF : ∀ i, ∫ ω, Real.exp (β * X i ω) ∂P ≤ Real.exp c) :
    β * (∫ ω, (⨆ i, X i ω) ∂P) ≤ Real.log (Fintype.card ι) + c := by
  classical
  let M : Ω → ℝ := fun ω => ⨆ i, X i ω
  have hM : Integrable M P := integrable_iSup_finite P X hX
  have hsum : Integrable (fun ω => ∑ i, Real.exp (β * X i ω)) P :=
    integrable_finsetSum Finset.univ (fun i _ => hExp i)
  have hpoint (ω : Ω) : Real.exp (β * M ω) ≤ ∑ i, Real.exp (β * X i ω) := by
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => X i ω)
    change Real.exp (β * (⨆ i, X i ω)) ≤ _
    rw [← hi]
    exact Finset.single_le_sum (f := fun j => Real.exp (β * X j ω))
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)
  have hEM : Integrable (fun ω => Real.exp (β * M ω)) P :=
    hsum.mono' (Real.continuous_exp.comp_aestronglyMeasurable
      (hM.const_mul β).aestronglyMeasurable) (Filter.Eventually.of_forall (fun ω => by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hpoint ω))
  have hJ := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (hM.const_mul β) hEM
  have hI : (∫ ω, Real.exp (β * M ω) ∂P) ≤
      (Fintype.card ι : ℝ) * Real.exp c := by
    calc
      _ ≤ ∫ ω, (∑ i, Real.exp (β * X i ω)) ∂P := integral_mono hEM hsum hpoint
      _ = ∑ i, ∫ ω, Real.exp (β * X i ω) ∂P :=
        integral_finsetSum Finset.univ (fun i _ => hExp i)
      _ ≤ ∑ _i : ι, Real.exp c := Finset.sum_le_sum (fun i _ => hMGF i)
      _ = _ := by simp
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have he : Real.exp (β * ∫ ω, M ω ∂P) ≤
      Real.exp (Real.log (Fintype.card ι) + c) := by
    rw [Real.exp_add, Real.exp_log hn]
    simpa only [integral_const_mul] using hJ.trans hI
  exact Real.exp_le_exp.mp he

end DudleyProof


open MeasureTheory

namespace DudleyProof
open HighDimStat.MetricEntropy

lemma exists_min_cover {T : Type*} [Fintype T] [PseudoMetricSpace T]
    (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ C : Finset T, C.card = CoveringNumber T δ ∧
      ∀ θ : T, ∃ θi ∈ C, dist θ θi ≤ δ := by
  classical
  unfold CoveringNumber
  change sInf {N : ℕ | ∃ C : Finset T, C.card = N ∧
    ∀ θ : T, ∃ θi ∈ C, dist θ θi ≤ δ} ∈
    {N : ℕ | ∃ C : Finset T, C.card = N ∧ ∀ θ : T, ∃ θi ∈ C, dist θ θi ≤ δ}
  apply csInf_mem
  exact ⟨Fintype.card T, Finset.univ, by simp, fun θ =>
    ⟨θ, Finset.mem_univ θ, by simpa using hδ⟩⟩

lemma dist_le_diameter {T : Type*} [Fintype T] [Nonempty T] [PseudoMetricSpace T]
    (x y : T) : dist x y ≤ Diameter T := by
  unfold Diameter
  exact le_ciSup (Set.finite_range (fun p : T × T => dist p.1 p.2)).bddAbove (x, y)

lemma diameter_nonneg {T : Type*} [Fintype T] [Nonempty T] [PseudoMetricSpace T] :
    0 ≤ Diameter T :=
  (dist_nonneg (x := Classical.choice inferInstance) (y := Classical.choice inferInstance)).trans
    (dist_le_diameter _ _)

lemma coveringNumber_le_one_of_diameter_nonpos {T : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] (δ : ℝ) (hδ : 0 ≤ δ) (hD : Diameter T ≤ 0) :
    CoveringNumber T δ ≤ 1 := by
  classical
  apply csInf_le (OrderBot.bddBelow _)
  refine ⟨{Classical.choice (inferInstance : Nonempty T)}, by simp, fun θ => ?_⟩
  refine ⟨Classical.choice inferInstance, by simp, ?_⟩
  exact (dist_le_diameter _ _).trans (hD.trans hδ)

lemma integrable_incrementSup {T Ω : Type*} [Fintype T] [Nonempty T]
    [MeasurableSpace Ω] (P : Measure Ω) (X : T → Ω → ℝ)
    (hX : ∀ θ, Integrable (X θ) P) : Integrable (IncrementSup X) P :=
  integrable_iSup_finite P (fun p : T × T => fun ω => X p.1 ω - X p.2 ω)
    (fun p => (hX p.1).sub (hX p.2))

lemma integrable_localIncrementSup {T Ω : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] [MeasurableSpace Ω] (P : Measure Ω) (X : T → Ω → ℝ)
    (hX : ∀ θ, Integrable (X θ) P) (δ : ℝ) (hδ : 0 ≤ δ) :
    Integrable (LocalIncrementSup X δ) P := by
  classical
  letI : Nonempty {p : T × T // dist p.1 p.2 ≤ δ} :=
    ⟨⟨(Classical.choice inferInstance, Classical.choice inferInstance), by simpa using hδ⟩⟩
  exact integrable_iSup_finite P
    (fun p : {p : T × T // dist p.1 p.2 ≤ δ} => fun ω => X p.1.1 ω - X p.1.2 ω)
    (fun p => (hX p.1.1).sub (hX p.1.2))


end DudleyProof


open MeasureTheory

namespace DudleyProof
open HighDimStat.MetricEntropy

lemma coveringNumber_pos {T : Type*} [Fintype T] [Nonempty T] [PseudoMetricSpace T]
    (δ : ℝ) (hδ : 0 ≤ δ) : 0 < CoveringNumber T δ := by
  obtain ⟨C, hcard, hcover⟩ := exists_min_cover (T := T) δ hδ
  obtain ⟨a, ha, _⟩ := hcover (Classical.choice inferInstance)
  rw [← hcard]
  exact Finset.card_pos.mpr ⟨a, ha⟩

lemma coveringNumber_antitone {T : Type*} [Fintype T] [PseudoMetricSpace T]
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    CoveringNumber T v ≤ CoveringNumber T u := by
  obtain ⟨C, hcard, hcover⟩ := exists_min_cover (T := T) u hu
  unfold CoveringNumber
  apply csInf_le (OrderBot.bddBelow _)
  refine ⟨C, hcard, fun θ => ?_⟩
  obtain ⟨a, ha, hdist⟩ := hcover θ
  exact ⟨a, ha, hdist.trans huv⟩

lemma coveringNumber_le_card {T : Type*} [Fintype T] [PseudoMetricSpace T]
    (δ : ℝ) (hδ : 0 ≤ δ) : CoveringNumber T δ ≤ Fintype.card T := by
  classical
  unfold CoveringNumber
  apply csInf_le (OrderBot.bddBelow _)
  exact ⟨Finset.univ, by simp, fun θ => ⟨θ, Finset.mem_univ θ, by simpa using hδ⟩⟩

lemma entropy_integrand_antitone {T : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] :
    AntitoneOn (fun u : ℝ => Real.sqrt (Real.log (CoveringNumber T u))) (Set.Ici 0) := by
  intro u hu v hv huv
  apply Real.sqrt_le_sqrt
  apply Real.log_le_log
  · exact_mod_cast coveringNumber_pos v hv
  · exact_mod_cast coveringNumber_antitone hu huv

lemma entropy_integrand_intervalIntegrable {T : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => Real.sqrt (Real.log (CoveringNumber T u))) volume a b := by
  apply AntitoneOn.intervalIntegrable
  apply entropy_integrand_antitone.mono
  rw [Set.uIcc_of_le hab]
  exact fun u hu => ha.trans hu.1

lemma entropyIntegral_nonneg {T : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] {a b : ℝ} (hab : a ≤ b) :
    0 ≤ EntropyIntegral T a b := by
  apply intervalIntegral.integral_nonneg hab
  intro u hu
  exact Real.sqrt_nonneg _

end DudleyProof


open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DudleyProof

lemma le_sqrt_of_mgf_quadratic (K c L : ℝ) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (h : ∀ β : ℝ, 0 < β → β * K ≤ L + c * β ^ 2 / 2) :
    K ≤ Real.sqrt (2 * c * L) := by
  by_contra hK
  have hgt : Real.sqrt (2 * c * L) < K := lt_of_not_ge hK
  have hKpos : 0 < K := (Real.sqrt_nonneg _).trans_lt hgt
  have hs : Real.sqrt (2 * c * L) ^ 2 = 2 * c * L :=
    Real.sq_sqrt (by positivity)
  by_cases hc0 : c = 0
  · have hb := h ((L + 1) / K) (div_pos (by linarith) hKpos)
    rw [hc0, zero_mul, zero_div, add_zero, div_mul_cancel₀ _ hKpos.ne'] at hb
    linarith
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have hb := h (K / c) (div_pos hKpos hcpos)
    have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * c by positivity)
    have he1 : 2 * c * (K / c * K) = 2 * K ^ 2 := by field_simp [hc0] <;> ring
    have he2 : 2 * c * (L + c * (K / c) ^ 2 / 2) = 2 * c * L + K ^ 2 := by
      field_simp [hc0]
      <;> ring
    rw [he1, he2] at hb'
    nlinarith [Real.sqrt_nonneg (2 * c * L)]

/-- The sharp finite sub-Gaussian maximum bound, including zero variance and singleton cases. -/
theorem finite_max_subgaussian {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (c : ℝ≥0) (hX : ∀ i, HasSubgaussianMGF (X i) c P) :
    (∫ ω, (⨆ i, X i ω) ∂P) ≤
      Real.sqrt (2 * (c : ℝ) * Real.log (Fintype.card ι)) := by
  apply le_sqrt_of_mgf_quadratic
  · exact c.coe_nonneg
  · exact Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  · intro β hβ
    have hb := finite_max_mgf_bound P X (fun i => (hX i).integrable) β
      ((c : ℝ) * β ^ 2 / 2) hβ (fun i => (hX i).integrable_exp_mul β)
      (fun i => (hX i).mgf_le β)
    exact hb

end DudleyProof


open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DudleyProof
open HighDimStat.MetricEntropy

lemma increment_hasSubgaussianMGF {T Ω : Type*} [PseudoMetricSpace T]
    [MeasurableSpace Ω] (P : Measure Ω) (X : T → Ω → ℝ)
    (hSG : SubGaussianProcess P X) (x y : T) :
    HasSubgaussianMGF (fun ω => X x ω - X y ω) ⟨dist x y ^ 2, sq_nonneg _⟩ P where
  integrable_exp_mul β := hSG.2.2.1 x y β
  mgf_le β := by
    change (∫ ω, Real.exp (β * (X x ω - X y ω)) ∂P) ≤
      Real.exp (dist x y ^ 2 * β ^ 2 / 2)
    apply (hSG.2.2.2 x y β).trans_eq
    congr 1
    ring

lemma increment_hasSubgaussianMGF_of_dist_le {T Ω : Type*} [PseudoMetricSpace T]
    [MeasurableSpace Ω] (P : Measure Ω) (X : T → Ω → ℝ)
    (hSG : SubGaussianProcess P X) (x y : T) (σ : ℝ) (hσ : 0 ≤ σ)
    (hxy : dist x y ≤ σ) :
    HasSubgaussianMGF (fun ω => X x ω - X y ω) ⟨σ ^ 2, sq_nonneg _⟩ P where
  integrable_exp_mul β := hSG.2.2.1 x y β
  mgf_le β := by
    apply (increment_hasSubgaussianMGF P X hSG x y).mgf_le β |>.trans
    apply Real.exp_le_exp.mpr
    have hs := pow_le_pow_left₀ dist_nonneg hxy 2
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hs (sq_nonneg β)) (by norm_num)

lemma ae_eq_of_dist_zero {T Ω : Type*} [PseudoMetricSpace T] [MeasurableSpace Ω]
    (P : Measure Ω) (X : T → Ω → ℝ) (hSG : SubGaussianProcess P X)
    (x y : T) (hxy : dist x y = 0) : X x =ᵐ[P] X y := by
  have hz := increment_hasSubgaussianMGF P X hSG x y
  have hc : (⟨dist x y ^ 2, sq_nonneg _⟩ : ℝ≥0) = 0 := by
    ext
    simp [hxy]
  rw [hc] at hz
  filter_upwards [hz.ae_eq_zero_of_hasSubgaussianMGF_zero] with ω hω
  exact sub_eq_zero.mp hω

end DudleyProof


open MeasureTheory
open scoped BigOperators

namespace DudleyProof
open HighDimStat.MetricEntropy

/-- A finite cover chain, before applying any probabilistic bounds to its edges. -/
lemma incrementSup_le_finite_chain {T Ω : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] (X : T → Ω → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (γ : ℕ → T → T) (m : ℕ) (a : T) (hbase : ∀ θ, γ 0 θ = a)
    (E : ℕ → Finset (T × T))
    (hEdge : ∀ k < m, ∀ θ, (γ (k + 1) θ, γ k θ) ∈ E k)
    (hEnd : ∀ θ, dist θ (γ m θ) ≤ δ) (ω : Ω) :
    IncrementSup X ω ≤ 2 * LocalIncrementSup X δ ω +
      ∑ k ∈ Finset.range m,
        ((⨆ p : ↥(E k), X p.1.1 ω - X p.1.2 ω) +
         (⨆ p : ↥(E k), X p.1.2 ω - X p.1.1 ω)) := by
  classical
  unfold IncrementSup
  apply ciSup_le
  intro p
  have h1 : X p.1 ω - X (γ m p.1) ω ≤ LocalIncrementSup X δ ω := by
    unfold LocalIncrementSup
    exact le_ciSup (f := fun q : {q : T × T // dist q.1 q.2 ≤ δ} =>
      X q.1.1 ω - X q.1.2 ω) (Set.finite_range _).bddAbove
      ⟨(p.1, γ m p.1), hEnd p.1⟩
  have h2 : X (γ m p.2) ω - X p.2 ω ≤ LocalIncrementSup X δ ω := by
    unfold LocalIncrementSup
    exact le_ciSup (f := fun q : {q : T × T // dist q.1 q.2 ≤ δ} =>
      X q.1.1 ω - X q.1.2 ω) (Set.finite_range _).bddAbove
      ⟨(γ m p.2, p.2), by simpa [dist_comm] using hEnd p.2⟩
  have hf : X (γ m p.1) ω - X a ω ≤
      ∑ k ∈ Finset.range m, (⨆ q : ↥(E k), X q.1.1 ω - X q.1.2 ω) := by
    rw [← hbase p.1, ← Finset.sum_range_sub (fun k => X (γ k p.1) ω) m]
    apply Finset.sum_le_sum
    intro k hk
    exact le_ciSup (f := fun q : ↥(E k) => X q.1.1 ω - X q.1.2 ω)
      (Set.finite_range _).bddAbove
      ⟨(γ (k + 1) p.1, γ k p.1), hEdge k (Finset.mem_range.mp hk) p.1⟩
  have hr : X a ω - X (γ m p.2) ω ≤
      ∑ k ∈ Finset.range m, (⨆ q : ↥(E k), X q.1.2 ω - X q.1.1 ω) := by
    have hid : X a ω - X (γ m p.2) ω =
        ∑ k ∈ Finset.range m, (X (γ k p.2) ω - X (γ (k + 1) p.2) ω) := by
      have ht := Finset.sum_range_sub (fun k => -X (γ k p.2) ω) m
      simpa only [neg_sub_neg, hbase, neg_sub] using ht.symm
    rw [hid]
    apply Finset.sum_le_sum
    intro k hk
    exact le_ciSup (f := fun q : ↥(E k) => X q.1.2 ω - X q.1.1 ω)
      (Set.finite_range _).bddAbove
      ⟨(γ (k + 1) p.2, γ k p.2), hEdge k (Finset.mem_range.mp hk) p.2⟩
  rw [Finset.sum_add_distrib]
  linarith

end DudleyProof


open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace DudleyProof
open HighDimStat.MetricEntropy

lemma expected_bounded_increments {T Ω ι : Type*} [PseudoMetricSpace T]
    [MeasurableSpace Ω] [Fintype ι] [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : T → Ω → ℝ) (hSG : SubGaussianProcess P X) (x y : ι → T)
    (r : ℝ) (hr : 0 ≤ r) (N : ℕ) (hN : 0 < N) (hcard : Fintype.card ι ≤ N ^ 2)
    (hdist : ∀ i, dist (x i) (y i) ≤ 3 * r) :
    (∫ ω, (⨆ i, X (x i) ω - X (y i) ω) ∂P) ≤
      6 * r * Real.sqrt (Real.log N) := by
  have hmax := finite_max_subgaussian P
    (fun i ω => X (x i) ω - X (y i) ω) ⟨(3 * r) ^ 2, sq_nonneg _⟩
    (fun i => increment_hasSubgaussianMGF_of_dist_le P X hSG (x i) (y i)
      (3 * r) (by positivity) (hdist i))
  apply hmax.trans
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hlog : Real.log (Fintype.card ι) ≤ 2 * Real.log N := by
    have hb := Real.log_le_log (show 0 < (Fintype.card ι : ℝ) by exact_mod_cast Fintype.card_pos)
      (show (Fintype.card ι : ℝ) ≤ (N : ℝ) ^ 2 by exact_mod_cast hcard)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hb
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hs := Real.sq_sqrt hL
  have hb := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * (3 * r) ^ 2 by positivity)
  change 2 * (3 * r) ^ 2 * Real.log (Fintype.card ι) ≤ _
  nlinarith [sq_nonneg r]

/-- Integrating a finite chain and controlling each forward and reverse edge maximum. -/
lemma expected_incrementSup_le_finite_chain {T Ω : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : T → Ω → ℝ) (hSG : SubGaussianProcess P X) (δ : ℝ) (hδ : 0 ≤ δ)
    (γ : ℕ → T → T) (m : ℕ) (a : T) (hbase : ∀ θ, γ 0 θ = a)
    (E : ℕ → Finset (T × T))
    (hEdge : ∀ k < m, ∀ θ, (γ (k + 1) θ, γ k θ) ∈ E k)
    (hEnd : ∀ θ, dist θ (γ m θ) ≤ δ)
    (r : ℕ → ℝ) (N : ℕ → ℕ)
    (hr : ∀ k < m, 0 ≤ r k) (hN : ∀ k < m, 0 < N k)
    (hcard : ∀ k < m, (E k).card ≤ (N k) ^ 2)
    (hdist : ∀ k < m, ∀ p ∈ E k, dist p.1 p.2 ≤ 3 * r k) :
    (∫ ω, IncrementSup X ω ∂P) ≤ 2 * (∫ ω, LocalIncrementSup X δ ω ∂P) +
      ∑ k ∈ Finset.range m, 12 * r k * Real.sqrt (Real.log (N k)) := by
  classical
  let U : ℕ → Ω → ℝ := fun k ω => ⨆ p : ↥(E k), X p.1.1 ω - X p.1.2 ω
  let V : ℕ → Ω → ℝ := fun k ω => ⨆ p : ↥(E k), X p.1.2 ω - X p.1.1 ω
  have hne (k : ℕ) (hk : k < m) : Nonempty ↥(E k) :=
    ⟨⟨(γ (k + 1) a, γ k a), hEdge k hk a⟩⟩
  have hU (k : ℕ) (hk : k < m) : Integrable (U k) P := by
    letI := hne k hk
    exact integrable_iSup_finite P _ (fun p => (hSG.1 p.1.1).sub (hSG.1 p.1.2))
  have hV (k : ℕ) (hk : k < m) : Integrable (V k) P := by
    letI := hne k hk
    exact integrable_iSup_finite P _ (fun p => (hSG.1 p.1.2).sub (hSG.1 p.1.1))
  have hbU (k : ℕ) (hk : k < m) :
      (∫ ω, U k ω ∂P) ≤ 6 * r k * Real.sqrt (Real.log (N k)) := by
    letI := hne k hk
    apply expected_bounded_increments P X hSG (fun p : ↥(E k) => p.1.1)
      (fun p : ↥(E k) => p.1.2) (r k) (hr k hk) (N k) (hN k hk)
    · simpa only [Fintype.card_coe] using hcard k hk
    · exact fun p => hdist k hk p p.2
  have hbV (k : ℕ) (hk : k < m) :
      (∫ ω, V k ω ∂P) ≤ 6 * r k * Real.sqrt (Real.log (N k)) := by
    letI := hne k hk
    apply expected_bounded_increments P X hSG (fun p : ↥(E k) => p.1.2)
      (fun p : ↥(E k) => p.1.1) (r k) (hr k hk) (N k) (hN k hk)
    · simpa only [Fintype.card_coe] using hcard k hk
    · exact fun p => by simpa only [dist_comm] using hdist k hk p p.2
  have hsum : Integrable (fun ω => ∑ k ∈ Finset.range m, (U k ω + V k ω)) P :=
    integrable_finsetSum (Finset.range m) (fun k hk =>
      (hU k (Finset.mem_range.mp hk)).add (hV k (Finset.mem_range.mp hk)))
  have hlocal := integrable_localIncrementSup P X hSG.1 δ hδ
  calc
    _ ≤ ∫ ω, (2 * LocalIncrementSup X δ ω + ∑ k ∈ Finset.range m, (U k ω + V k ω)) ∂P :=
      integral_mono (integrable_incrementSup P X hSG.1) ((hlocal.const_mul 2).add hsum)
        (incrementSup_le_finite_chain X δ hδ γ m a hbase E hEdge hEnd)
    _ = 2 * (∫ ω, LocalIncrementSup X δ ω ∂P) +
        ∑ k ∈ Finset.range m, ((∫ ω, U k ω ∂P) + (∫ ω, V k ω ∂P)) := by
      rw [integral_add (hlocal.const_mul 2) hsum, integral_const_mul,
        integral_finsetSum (Finset.range m) (f := fun k ω => U k ω + V k ω) (fun k hk =>
          (hU k (Finset.mem_range.mp hk)).add (hV k (Finset.mem_range.mp hk)))]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      exact integral_add (hU k (Finset.mem_range.mp hk)) (hV k (Finset.mem_range.mp hk))
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro k hk
      have hku := hbU k (Finset.mem_range.mp hk)
      have hkv := hbV k (Finset.mem_range.mp hk)
      linarith

end DudleyProof


open MeasureTheory
open scoped BigOperators

namespace DudleyProof
open HighDimStat.MetricEntropy

lemma entropy_scale_bound {T : Type*} [Fintype T] [Nonempty T] [PseudoMetricSpace T]
    (r : ℝ) (hr : 0 ≤ r) :
    r * Real.sqrt (Real.log (CoveringNumber T r)) ≤ 2 * EntropyIntegral T (r / 2) r := by
  let f : ℝ → ℝ := fun u => Real.sqrt (Real.log (CoveringNumber T u))
  have hi := entropy_integrand_intervalIntegrable (T := T) (show 0 ≤ r / 2 by positivity)
    (show r / 2 ≤ r by linarith)
  have hb : (∫ u in r / 2..r, f r) ≤ ∫ u in r / 2..r, f u := by
    apply intervalIntegral.integral_mono_on (show r / 2 ≤ r by linarith)
      intervalIntegrable_const hi
    intro u hu
    exact entropy_integrand_antitone (show 0 ≤ u from (show 0 ≤ r / 2 by positivity).trans hu.1)
      hr hu.2
  rw [intervalIntegral.integral_const] at hb
  change r * f r ≤ 2 * (∫ u in r / 2..r, f u)
  simp only [smul_eq_mul] at hb
  linarith

lemma dyadic_scale_nonneg (r : ℕ → ℝ) (hr0 : 0 ≤ r 0)
    (hstep : ∀ k, r (k + 1) = r k / 2) (k : ℕ) : 0 ≤ r k := by
  induction k with
  | zero => exact hr0
  | succ k ih => rw [hstep]; positivity

lemma dyadic_scale_antitone (r : ℕ → ℝ) (hr0 : 0 ≤ r 0)
    (hstep : ∀ k, r (k + 1) = r k / 2) : Antitone r := by
  apply antitone_nat_of_succ_le
  intro k
  rw [hstep]
  have := dyadic_scale_nonneg r hr0 hstep k
  linarith

/-- The sum of dyadic entropy terms is at most twice the corresponding entropy integral. -/
lemma dyadic_entropy_sum {T : Type*} [Fintype T] [Nonempty T] [PseudoMetricSpace T]
    (r : ℕ → ℝ) (hr0 : 0 ≤ r 0) (hstep : ∀ k, r (k + 1) = r k / 2) (m : ℕ) :
    (∑ k ∈ Finset.range m, r (k + 1) * Real.sqrt (Real.log (CoveringNumber T (r (k + 1))))) ≤
      2 * EntropyIntegral T (r (m + 1)) (r 1) := by
  let f : ℝ → ℝ := fun u => Real.sqrt (Real.log (CoveringNumber T u))
  have hnonneg := dyadic_scale_nonneg r hr0 hstep
  have hanti := dyadic_scale_antitone r hr0 hstep
  have hb (k : ℕ) : r (k + 1) * f (r (k + 1)) ≤
      2 * (∫ u in r (k + 2)..r (k + 1), f u) := by
    have := entropy_scale_bound (T := T) (r (k + 1)) (hnonneg (k + 1))
    simpa only [hstep (k + 1), Nat.add_assoc, EntropyIntegral] using this
  have hi (k : ℕ) : IntervalIntegrable f volume (r (k + 1)) (r (k + 2)) := by
    apply IntervalIntegrable.symm
    exact entropy_integrand_intervalIntegrable (hnonneg (k + 2)) (hanti (by omega))
  have ht := intervalIntegral.sum_integral_adjacent_intervals
    (f := f) (a := fun k => r (k + 1)) (n := m) (fun k _ => hi k)
  have heq : (∑ k ∈ Finset.range m, ∫ u in r (k + 2)..r (k + 1), f u) =
      EntropyIntegral T (r (m + 1)) (r 1) := by
    calc
      _ = ∑ k ∈ Finset.range m, -(∫ u in r (k + 1)..r (k + 2), f u) :=
        Finset.sum_congr rfl (fun k _ => intervalIntegral.integral_symm _ _)
      _ = -(∑ k ∈ Finset.range m, ∫ u in r (k + 1)..r (k + 2), f u) :=
        Finset.sum_neg_distrib _
      _ = -(∫ u in r 1..r (m + 1), f u) := congrArg Neg.neg ht
      _ = _ := (intervalIntegral.integral_symm _ _).symm
  calc
    _ ≤ ∑ k ∈ Finset.range m, 2 * (∫ u in r (k + 2)..r (k + 1), f u) :=
      Finset.sum_le_sum (fun k _ => hb k)
    _ = _ := by rw [← Finset.mul_sum, heq]

end DudleyProof


open MeasureTheory
open scoped BigOperators

namespace DudleyProof
open HighDimStat.MetricEntropy

lemma coveringNumber_diameter {T : Type*} [Fintype T] [Nonempty T] [PseudoMetricSpace T] :
    CoveringNumber T (Diameter T) = 1 := by
  classical
  have hpos := coveringNumber_pos (T := T) (Diameter T) (diameter_nonneg (T := T))
  have hle : CoveringNumber T (Diameter T) ≤ 1 := by
    unfold CoveringNumber
    apply csInf_le (OrderBot.bddBelow _)
    let a : T := Classical.choice inferInstance
    exact ⟨{a}, by simp, fun θ => ⟨a, by simp, dist_le_diameter θ a⟩⟩
  omega

/-- Build optimal covers and their nearest-point projections at every dyadic scale. -/
lemma expected_incrementSup_le_dyadic_chain {T Ω : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : T → Ω → ℝ) (hSG : SubGaussianProcess P X)
    (r : ℕ → ℝ) (hr0 : r 0 = Diameter T) (hstep : ∀ k, r (k + 1) = r k / 2)
    (m : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hm : r m ≤ δ) :
    (∫ ω, IncrementSup X ω ∂P) ≤ 2 * (∫ ω, LocalIncrementSup X δ ω ∂P) +
      ∑ k ∈ Finset.range m, 12 * r (k + 1) *
        Real.sqrt (Real.log (CoveringNumber T (r (k + 1)))) := by
  classical
  have hnonneg : ∀ k, 0 ≤ r k := dyadic_scale_nonneg r (hr0 ▸ diameter_nonneg) hstep
  have hanti := dyadic_scale_antitone r (hnonneg 0) hstep
  choose C hCcard hCcover using fun k => exists_min_cover (T := T) (r k) (hnonneg k)
  choose γ hγmem hγdist using hCcover
  have hC0 : (C 0).card = 1 := by rw [hCcard, hr0, coveringNumber_diameter]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hC0
  have hbase : ∀ θ, γ 0 θ = a := by
    intro θ
    have hmem := hγmem 0 θ
    rw [ha, Finset.mem_singleton] at hmem
    exact hmem
  let E : ℕ → Finset (T × T) := fun k =>
    ((C (k + 1)).product (C k)).filter (fun p => dist p.1 p.2 ≤ 3 * r (k + 1))
  have hEdge : ∀ k < m, ∀ θ, (γ (k + 1) θ, γ k θ) ∈ E k := by
    intro k hk θ
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hγmem (k + 1) θ, hγmem k θ⟩, ?_⟩
    have hd := dist_triangle (γ (k + 1) θ) θ (γ k θ)
    have h1 := hγdist (k + 1) θ
    have h2 := hγdist k θ
    rw [dist_comm (γ (k + 1) θ) θ] at hd
    have hs := hstep k
    linarith
  apply expected_incrementSup_le_finite_chain P X hSG δ hδ γ m a hbase E hEdge
    (fun θ => (hγdist m θ).trans hm) (fun k => r (k + 1))
    (fun k => CoveringNumber T (r (k + 1)))
  · exact fun k _ => hnonneg (k + 1)
  · exact fun k _ => coveringNumber_pos (r (k + 1)) (hnonneg (k + 1))
  · intro k hk
    calc
      (E k).card ≤ ((C (k + 1)).product (C k)).card := Finset.card_filter_le _ _
      _ = CoveringNumber T (r (k + 1)) * CoveringNumber T (r k) := by
        rw [Finset.product_eq_sprod, Finset.card_product, hCcard, hCcard]
      _ ≤ CoveringNumber T (r (k + 1)) * CoveringNumber T (r (k + 1)) := by
        apply Nat.mul_le_mul_left
        exact coveringNumber_antitone (hnonneg (k + 1)) (hanti (by omega))
      _ = _ := (pow_two _).symm
  · intro k hk p hp
    exact (Finset.mem_filter.mp hp).2

end DudleyProof


open MeasureTheory

namespace DudleyProof
open HighDimStat.MetricEntropy

/-- A finite pseudometric has a positive radius that only joins points at distance zero. -/
lemma exists_zero_distance_radius {T : Type*} [Fintype T] [Nonempty T] [PseudoMetricSpace T] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x y : T, dist x y ≤ ε → dist x y = 0 := by
  classical
  let f : T × T → ℝ := fun p => if dist p.1 p.2 = 0 then 1 else dist p.1 p.2
  have hf : ∀ p, 0 < f p := by
    intro p
    dsimp [f]
    split_ifs with h
    · norm_num
    · exact lt_of_le_of_ne dist_nonneg (Ne.symm h)
  obtain ⟨p, hp⟩ := exists_eq_ciInf_of_finite (f := f)
  have hi : 0 < (⨅ p, f p) := by rw [← hp]; exact hf p
  refine ⟨(⨅ p, f p) / 2, by positivity, fun x y hxy => ?_⟩
  by_contra hn
  have hb := ciInf_le (f := f) (Set.finite_range f).bddBelow (x, y)
  have he : f (x, y) = dist x y := by simp [f, hn]
  rw [he] at hb
  linarith

lemma localIncrementSup_eq_zero_radius {T Ω : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] (X : T → Ω → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hgap : ∀ x y : T, dist x y ≤ ε → dist x y = 0) :
    LocalIncrementSup X ε = LocalIncrementSup X 0 := by
  classical
  let a : T := Classical.choice inferInstance
  letI : Nonempty {p : T × T // dist p.1 p.2 ≤ ε} := ⟨⟨(a, a), by simpa using hε⟩⟩
  letI : Nonempty {p : T × T // dist p.1 p.2 ≤ 0} := ⟨⟨(a, a), by simp⟩⟩
  funext ω
  unfold LocalIncrementSup
  apply le_antisymm
  · apply ciSup_le
    intro p
    exact le_ciSup (f := fun q : {q : T × T // dist q.1 q.2 ≤ 0} =>
      X q.1.1 ω - X q.1.2 ω) (Set.finite_range _).bddAbove
      ⟨p.1, by rw [hgap p.1.1 p.1.2 p.2]⟩
  · apply ciSup_le
    intro p
    exact le_ciSup (f := fun q : {q : T × T // dist q.1 q.2 ≤ ε} =>
      X q.1.1 ω - X q.1.2 ω) (Set.finite_range _).bddAbove ⟨p.1, p.2.trans hε⟩

end DudleyProof


open MeasureTheory
open scoped BigOperators

namespace DudleyProof
open HighDimStat.MetricEntropy

theorem entropy_bound_positive_radius {T Ω : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : T → Ω → ℝ) (hSG : SubGaussianProcess P X)
    (δ : ℝ) (hδ : 0 < δ) (hδD : δ ≤ Diameter T) :
    (∫ ω, IncrementSup X ω ∂P) ≤ 2 * (∫ ω, LocalIncrementSup X δ ω ∂P) +
      32 * EntropyIntegral T (δ / 4) (Diameter T) := by
  let D := Diameter T
  have hD : 0 < D := hδ.trans_le hδD
  let r : ℕ → ℝ := fun k => D * (1 / 2 : ℝ) ^ k
  have hr0 : r 0 = Diameter T := by simp [r, D]
  have hstep : ∀ k, r (k + 1) = r k / 2 := by
    intro k
    dsimp [r]
    rw [pow_succ]
    ring
  have hn0 : 0 ≤ r 0 := hr0 ▸ diameter_nonneg
  have hanti := dyadic_scale_antitone r hn0 hstep
  obtain ⟨n, hnlow, hnupper⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hδ hD) ((div_le_one hD).mpr hδD)
    (show 0 < (1 / 2 : ℝ) by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
  let m := n + 1
  have hcancel : D * (δ / D) = δ := by field_simp [ne_of_gt hD]
  have hm : r m ≤ δ := by
    have hb := mul_lt_mul_of_pos_left hnlow hD
    rw [hcancel] at hb
    exact hb.le
  have hδrm : δ ≤ 2 * r m := by
    have hb := mul_le_mul_of_nonneg_left hnupper hD.le
    rw [hcancel] at hb
    have hs := hstep n
    change δ ≤ r n at hb
    dsimp [m]
    linarith
  have hlow : δ / 4 ≤ r (m + 1) := by
    rw [hstep]
    linarith
  have hchain := expected_incrementSup_le_dyadic_chain P X hSG r hr0 hstep m δ hδ.le hm
  have hsum := dyadic_entropy_sum (T := T) r hn0 hstep m
  have hsum12 : (∑ k ∈ Finset.range m, 12 * r (k + 1) *
      Real.sqrt (Real.log (CoveringNumber T (r (k + 1))))) =
      12 * (∑ k ∈ Finset.range m, r (k + 1) *
        Real.sqrt (Real.log (CoveringNumber T (r (k + 1))))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have htrunc : EntropyIntegral T (r (m + 1)) (r 1) ≤
      EntropyIntegral T (δ / 4) D := by
    unfold EntropyIntegral
    apply intervalIntegral.integral_mono_interval hlow
      (hanti (show 1 ≤ m + 1 by omega))
      (show r 1 ≤ D by simpa only [hr0] using hanti (show 0 ≤ 1 by omega))
    · exact Filter.Eventually.of_forall (fun _ => Real.sqrt_nonneg _)
    · exact entropy_integrand_intervalIntegrable (show 0 ≤ δ / 4 by positivity)
        (show δ / 4 ≤ D by linarith)
  have hJ : 0 ≤ EntropyIntegral T (δ / 4) D := entropyIntegral_nonneg (by linarith)
  rw [hsum12] at hchain
  nlinarith

theorem entropy_bound {T Ω : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : T → Ω → ℝ) (hSG : SubGaussianProcess P X)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδD : δ ≤ Diameter T) :
    (∫ ω, IncrementSup X ω ∂P) ≤ 2 * (∫ ω, LocalIncrementSup X δ ω ∂P) +
      32 * EntropyIntegral T (δ / 4) (Diameter T) := by
  by_cases hδpos : 0 < δ
  · exact entropy_bound_positive_radius P X hSG δ hδpos hδD
  have hδzero : δ = 0 := le_antisymm (le_of_not_gt hδpos) hδ
  subst δ
  by_cases hD : 0 < Diameter T
  · obtain ⟨ε, hε, hgap⟩ := exists_zero_distance_radius (T := T)
    let η := min ε (Diameter T)
    have hη : 0 < η := lt_min hε hD
    have hηD : η ≤ Diameter T := min_le_right _ _
    have hηε : η ≤ ε := min_le_left _ _
    have hlocal : LocalIncrementSup X η = LocalIncrementSup X 0 :=
      localIncrementSup_eq_zero_radius X η hη.le (fun x y hxy => hgap x y (hxy.trans hηε))
    have hb := entropy_bound_positive_radius P X hSG η hη hηD
    rw [hlocal] at hb
    have htrunc : EntropyIntegral T (η / 4) (Diameter T) ≤
        EntropyIntegral T 0 (Diameter T) := by
      unfold EntropyIntegral
      apply intervalIntegral.integral_mono_interval (show 0 ≤ η / 4 by positivity)
        (show η / 4 ≤ Diameter T by linarith) le_rfl
      · exact Filter.Eventually.of_forall (fun _ => Real.sqrt_nonneg _)
      · exact entropy_integrand_intervalIntegrable (le_refl 0) (diameter_nonneg (T := T))
    simpa only [zero_div] using hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left htrunc (by norm_num)))
  · have hDzero : Diameter T = 0 :=
      le_antisymm (le_of_not_gt hD) (diameter_nonneg (T := T))
    let r : ℕ → ℝ := fun _ => 0
    have hb := expected_incrementSup_le_dyadic_chain P X hSG r hDzero.symm
      (fun _ => by simp [r]) 0 0 (le_refl 0) (le_refl 0)
    simpa only [Finset.range_zero, Finset.sum_empty, zero_div, hDzero,
      EntropyIntegral, intervalIntegral.integral_same, mul_zero, add_zero] using hb

end DudleyProof


open HighDimStat.MetricEntropy
theorem solution {T Ω : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (X : T → Ω → ℝ) (hSG : SubGaussianProcess Prob X) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδD : δ ≤ Diameter T) :
    ∫ ω, IncrementSup X ω ∂Prob ≤
      2 * (∫ ω, LocalIncrementSup X δ ω ∂Prob) +
      32 * EntropyIntegral T (δ / 4) (Diameter T) := by
  exact DudleyProof.entropy_bound Prob X hSG δ hδ0 hδD

#print axioms solution
