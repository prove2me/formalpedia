-- Prove2me | solution 2 for Kyprianou.Ch01.finiteMeanRealCompoundPoissonLinearGrowth
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:24:32.749105+00:00
-- url     : https://prove2.me/submissions/d7d83fa2-c983-4659-aadb-46bce15173c6

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace CPLGAux

/-- Deterministic core. -/
lemma det (T S : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (n0 : ℕ)
    (hT : ∀ n, n0 ≤ n → a * ((n : ℝ) + 1) ≤ T n)
    (A : ℝ) (hA : 0 ≤ A) (hS : ∀ n, S n ≤ A * ((n : ℝ) + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t →
      S (jumpCount T t) ≤ K * (1 + t) := by
  refine ⟨A * ((n0 : ℝ) + 1 + 1 / a), by positivity, fun t ht => ?_⟩
  set N := jumpCount T t with hN
  have hNb : (N : ℝ) ≤ n0 + t / a := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0]; simp; positivity
    · have hNdef : N = sInf {n | t < T n} := by rw [hN]; rfl
      have hlt : N - 1 < sInf {n | t < T n} := by
        rw [← hNdef]; omega
      have hnot := Nat.notMem_of_lt_sInf hlt
      simp only [Set.mem_ofPred_eq, not_lt] at hnot
      by_cases hle : n0 ≤ N - 1
      · have h1 := hT (N - 1) hle
        have hc : ((N - 1 : ℕ) : ℝ) + 1 = N := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [hc] at h1
        have : (N : ℝ) ≤ t / a := by
          rw [le_div_iff₀ ha]; linarith
        have : (0:ℝ) ≤ n0 := by positivity
        linarith
      · push Not at hle
        have : (N : ℝ) ≤ n0 := by exact_mod_cast (by omega : N ≤ n0)
        have : 0 ≤ t / a := by positivity
        linarith
  calc S N ≤ A * ((N : ℝ) + 1) := hS N
    _ ≤ A * ((n0 : ℝ) + t / a + 1) := by gcongr
    _ ≤ A * ((n0 : ℝ) + 1 + 1 / a) * (1 + t) := by
        have h1 : t / a ≤ (1 / a) * (1 + t) + ((n0:ℝ) + 1) * t := by
          rw [div_eq_mul_one_div, mul_comm t]
          have : 0 ≤ ((n0:ℝ) + 1) * t := by positivity
          have : (1 / a) * t ≤ (1 / a) * (1 + t) := by
            apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          linarith
        have : (n0 : ℝ) + t / a + 1 ≤ ((n0 : ℝ) + 1 + 1 / a) * (1 + t) := by nlinarith
        calc A * ((n0 : ℝ) + t / a + 1) ≤ A * (((n0 : ℝ) + 1 + 1 / a) * (1 + t)) :=
              mul_le_mul_of_nonneg_left this hA
          _ = _ := by ring

lemma identDistrib_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {Z : ℕ → Ω → ℝ} {L : Measure ℝ} (hm : ∀ n, Measurable (Z n)) (hl : ∀ n, HasLaw (Z n) L Q)
    (n : ℕ) : IdentDistrib (Z n) (Z 0) Q Q :=
  ⟨(hm n).aemeasurable, (hm 0).aemeasurable, by rw [(hl n).map_eq, (hl 0).map_eq]⟩

lemma integrable_id_jumpLaw (offspring : PMF ℕ)
    (hFiniteMean : Summable (fun k : ℕ => (offspring k).toReal * (k : ℝ)))
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hSupport : jumpLaw {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ, jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    Integrable (fun x : ℝ => x) jumpLaw := by
  set A : Set ℝ := Set.range (fun k : ℕ => (k : ℝ) - 1) with hA
  have hAeq : {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = A := by
    ext x; simp [hA, eq_comm]
  have hAc : jumpLaw Aᶜ = 0 := by
    have hAm : MeasurableSet A := (Set.countable_range _).measurableSet
    rw [measure_compl hAm (measure_ne_top _ _), ← hAeq, hSupport]; simp
  have hinj : Function.Injective (fun k : ℕ => (k : ℝ) - 1) := by
    intro a b h; simpa using h
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hrestr : jumpLaw.restrict A = jumpLaw := Measure.restrict_eq_self_of_ae_mem
    (ae_iff.2 hAc)
  rw [← hrestr, lintegral_countable _ (Set.countable_range _)]
  rw [tsum_range (fun x : ℝ => ‖x‖ₑ * jumpLaw {x}) hinj]
  simp only [hJumpMass]
  have hsum : Summable (fun k : ℕ => (offspring k).toReal * ((k : ℝ) + 1)) := by
    have h2 : Summable (fun k : ℕ => (offspring k).toReal) :=
      ENNReal.summable_toReal (by rw [PMF.tsum_coe]; simp)
    simpa [mul_add] using hFiniteMean.add h2
  have hle : ∀ k : ℕ, ‖((k : ℝ) - 1)‖ₑ * offspring k ≤
      ENNReal.ofReal ((offspring k).toReal * ((k : ℝ) + 1)) := by
    intro k
    have hne : offspring k ≠ ⊤ := PMF.apply_ne_top offspring k
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hne, mul_comm]
    gcongr
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  calc ∑' k : ℕ, ‖((k : ℝ) - 1)‖ₑ * offspring k
      ≤ ∑' k : ℕ, ENNReal.ofReal ((offspring k).toReal * ((k : ℝ) + 1)) := ENNReal.tsum_le_tsum hle
    _ = ENNReal.ofReal (∑' k : ℕ, (offspring k).toReal * ((k : ℝ) + 1)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end CPLGAux

open CPLGAux in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (hFiniteMean : Summable
      (fun k : ℕ => (offspring k).toReal * (k : ℝ)))
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovSemigroup law)
    (hInitial : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hRates : IsBranchingRateGenerator law rate offspring)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ᵐ ω ∂Q,
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ t : ℝ≥0,
          ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω ≤
            K * (1 + (t : ℝ)) := by
  -- marks: SLLN
  have hmI : Integrable (marks 0) Q := by
    have hJ := integrable_id_jumpLaw offspring hFiniteMean jumpLaw hSupport hJumpMass
    rw [← (hdriver.law_mark 0).map_eq] at hJ
    exact (integrable_map_measure (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable
      (hdriver.measurable_mark 0).aemeasurable).1 hJ
  have hmInd : iIndepFun marks Q := by
    have h := ProbabilityTheory.iIndepFun.precomp (g := Sum.inr) Sum.inr_injective hdriver.indep
    exact h
  have hSL := strong_law_ae marks hmI (fun i j hij => hmInd.indepFun hij)
    (identDistrib_of_hasLaw hdriver.measurable_mark hdriver.law_mark)
  -- interarrivals: truncated SLLN
  set m : ℕ → Ω → ℝ := fun i ω => max (min (arrival i ω) 1) 0 with hm
  have hmeas_m : ∀ i, Measurable (m i) := fun i =>
    ((hdriver.measurable_interarrival i).min measurable_const).max measurable_const
  have hτInd : iIndepFun arrival Q := by
    have h := ProbabilityTheory.iIndepFun.precomp (g := Sum.inl) Sum.inl_injective hdriver.indep
    exact h
  have hmIndep : iIndepFun m Q :=
    hτInd.comp (fun _ x => max (min x 1) 0) (fun _ => (measurable_id.min measurable_const).max
      measurable_const)
  have hmId : ∀ i, IdentDistrib (m i) (m 0) Q Q := fun i =>
    (identDistrib_of_hasLaw hdriver.measurable_interarrival hdriver.law_interarrival i).comp
      ((measurable_id.min measurable_const).max measurable_const)
  have hmInt : Integrable (m 0) Q := by
    refine Integrable.mono' (integrable_const (1:ℝ)) (hmeas_m 0).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    simp only [hm, Real.norm_eq_abs]
    rw [abs_le]; constructor
    · linarith [le_max_right (min (arrival 0 ω) 1) 0]
    · exact max_le (min_le_right _ _) zero_le_one
  have hpos := hdriver.ae_interarrival_pos hrate
  have hmean : 0 < ∫ ω, m 0 ω ∂Q := by
    have hnn : 0 ≤ᵐ[Q] m 0 := Eventually.of_forall fun ω => le_max_right _ _
    rw [integral_pos_iff_support_of_nonneg_ae hnn hmInt]
    have hnull : Q (Function.support (m 0))ᶜ = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 hpos)
      intro ω hω
      simp only [mem_compl_iff, Function.mem_support, not_not, hm] at hω
      simp only [Set.mem_ofPred_eq, not_forall, not_lt]
      refine ⟨0, ?_⟩
      by_contra h
      push Not at h
      have : 0 < min (arrival 0 ω) 1 := lt_min h one_pos
      have := le_max_left (min (arrival 0 ω) 1) 0
      linarith
    by_contra h
    push Not at h
    have h0 : Q (Function.support (m 0)) = 0 := le_antisymm h zero_le
    have : Q univ = 0 := by
      rw [← union_compl_self (Function.support (m 0))]
      exact measure_union_null h0 hnull
    simp at this
  have hTL := strong_law_ae m hmInt (fun i j hij => hmIndep.indepFun hij) hmId
  filter_upwards [hSL, hTL, hpos] with ω hS hT hp
  set μ := ∫ ω, m 0 ω ∂Q
  -- linear lower bound for arrival times
  have hT' : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.range (n + 1), m i ω)
      atTop (nhds μ) := hT.comp (tendsto_add_atTop_nat 1)
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 (hT'.eventually (lt_mem_nhds (half_lt_self hmean)))
  have hmle : ∀ i, m i ω ≤ arrival i ω := fun i =>
    max_le (min_le_left _ _) (hp i).le
  have hTb : ∀ n, n0 ≤ n →
      μ / 2 * ((n : ℝ) + 1) ≤ ProbabilityTheory.arrival arrival n ω := by
    intro n hn
    have h1 := hn0 n hn
    simp only [smul_eq_mul] at h1
    have hpos' : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [lt_inv_mul_iff₀ hpos'] at h1
    unfold ProbabilityTheory.arrival
    calc μ / 2 * ((n : ℝ) + 1) ≤ ∑ i ∈ Finset.range (n + 1), m i ω := by
          push_cast at h1; linarith
      _ ≤ _ := Finset.sum_le_sum fun i _ => hmle i
  obtain ⟨B, hB⟩ := hS.bddAbove_range
  have hSb : ∀ n : ℕ, ∑ i ∈ Finset.range n, marks i ω ≤ |B| * ((n : ℝ) + 1) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0; simp
    · have h1 : (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, marks i ω ≤ B := hB ⟨n, rfl⟩
      simp only [smul_eq_mul] at h1
      have hnp : (0:ℝ) < n := by exact_mod_cast hn
      rw [inv_mul_le_iff₀ hnp] at h1
      have : B * n ≤ |B| * ((n : ℝ) + 1) := by
        have := le_abs_self B
        have : |B| * (n : ℝ) ≤ |B| * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg B)
        nlinarith
      linarith
  obtain ⟨K, hK0, hK⟩ := det (fun n => ProbabilityTheory.arrival arrival n ω)
    (fun n => ∑ i ∈ Finset.range n, marks i ω) (μ / 2) (by linarith) n0 hTb |B| (abs_nonneg B) hSb
  refine ⟨K, hK0, fun t => ?_⟩
  have := hK (t : ℝ) t.2
  unfold ProbabilityTheory.compoundPoisson piecewisePath
  simpa using this
