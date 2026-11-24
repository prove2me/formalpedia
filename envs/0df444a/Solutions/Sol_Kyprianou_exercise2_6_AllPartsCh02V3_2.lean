-- Prove2me | solution 2 for Kyprianou.exercise2_6_AllPartsCh02V3
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T22:45:14.887973+00:00
-- url     : https://prove2.me/submissions/5a6ed007-7d32-439e-be9f-7c2533b593c0

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration

open MeasureTheory ProbabilityTheory Filter Complex Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Exercise2_6Helpers

/-! ### Section 1: Reference intensity and Poisson count first moments -/

private lemma referenceIntensity_Ioc_prod (ν : Measure ℝ) [SigmaFinite ν]
    {a b : ℝ} (ha : 0 ≤ a) {A : Set ℝ} :
    LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A) =
      ENNReal.ofReal (b - a) * ν A := by
  unfold LevyStochCalc.Poisson.referenceIntensity
  rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc]
  have hsub : Set.Ioc a b ∩ Set.Ici (0 : ℝ) = Set.Ioc a b :=
    Set.inter_eq_left.mpr fun _ hx => ha.trans (le_of_lt hx.1)
  rw [hsub, Real.volume_Ioc]

private lemma referenceIntensity_Ioc_prod_ne_top (ν : Measure ℝ) [SigmaFinite ν]
    {a b : ℝ} (ha : 0 ≤ a) {A : Set ℝ} (hAfin : ν A < ⊤) :
    LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A) ≠ ⊤ := by
  rw [referenceIntensity_Ioc_prod ν ha]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin.ne

private lemma hasSum_poisson_first (μ : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ n / (n.factorial : ℝ) * (n : ℝ)) (μ : ℝ) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero,
    mul_zero, sub_zero]
  have hterm : (fun n : ℕ =>
      Real.exp (-(μ : ℝ)) * (μ : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ)) =
      fun n : ℕ => (Real.exp (-(μ : ℝ)) * (μ : ℝ)) * ((μ : ℝ) ^ n / (n.factorial : ℝ)) := by
    funext n
    rw [pow_succ, Nat.factorial_succ]
    push_cast
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [hterm]
  have hexp : HasSum (fun n : ℕ => (μ : ℝ) ^ n / (n.factorial : ℝ)) (Real.exp (μ : ℝ)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (μ : ℝ)
  have h := hexp.mul_left (Real.exp (-(μ : ℝ)) * (μ : ℝ))
  have hval : Real.exp (-(μ : ℝ)) * (μ : ℝ) * Real.exp (μ : ℝ) = (μ : ℝ) := by
    calc Real.exp (-(μ : ℝ)) * (μ : ℝ) * Real.exp (μ : ℝ)
        = (μ : ℝ) * (Real.exp (-(μ : ℝ)) * Real.exp (μ : ℝ)) := by ring
      _ = (μ : ℝ) * Real.exp (-(μ : ℝ) + (μ : ℝ)) := by rw [← Real.exp_add]
      _ = (μ : ℝ) := by simp
  rwa [hval] at h

private lemma prm_count_int_and_mean {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hSfin : LevyStochCalc.Poisson.referenceIntensity ν S ≠ ⊤) :
    Integrable (fun ω => (N.N ω S).toReal) P ∧
      ∫ ω, (N.N ω S).toReal ∂P = (LevyStochCalc.Poisson.referenceIntensity ν S).toReal := by
  let μ : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν S).toNNReal
  have hμ_eq : (μ : ℝ) = (LevyStochCalc.Poisson.referenceIntensity ν S).toReal := rfl
  have hN_meas : Measurable (fun ω => N.N ω S) := N.measurable_eval hS
  have hcast_meas : Measurable (fun n : ℕ => (n : ℝ≥0∞)) := measurable_of_countable _
  have hlaw : P.map (fun ω => N.N ω S) =
      (ProbabilityTheory.poissonMeasure μ).map (fun n : ℕ => (n : ℝ≥0∞)) :=
    N.poisson_law hS hSfin
  have htoReal_meas : Measurable (fun r : ℝ≥0∞ => r.toReal) := ENNReal.measurable_toReal
  have hpois_int : Integrable (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure μ) := by
    rw [ProbabilityTheory.integrable_poissonMeasure_iff]
    exact (hasSum_poisson_first μ).summable.congr fun n => by rw [Real.norm_eq_abs, Nat.abs_cast]
  have hpois_mean : ∫ n : ℕ, (n : ℝ) ∂(ProbabilityTheory.poissonMeasure μ) = (μ : ℝ) := by
    rw [ProbabilityTheory.integral_poissonMeasure]
    simpa only [smul_eq_mul] using (hasSum_poisson_first μ).tsum_eq
  have hint : Integrable (fun ω => (N.N ω S).toReal) P := by
    change Integrable ((fun r : ℝ≥0∞ => r.toReal) ∘ fun ω => N.N ω S) P
    rw [← integrable_map_measure htoReal_meas.aestronglyMeasurable hN_meas.aemeasurable, hlaw,
      integrable_map_measure htoReal_meas.aestronglyMeasurable hcast_meas.aemeasurable]
    simpa only [Function.comp_def, ENNReal.toReal_natCast] using hpois_int
  have hmean : ∫ ω, (N.N ω S).toReal ∂P = (LevyStochCalc.Poisson.referenceIntensity ν S).toReal := by
    have h1 : ∫ ω, (N.N ω S).toReal ∂P = ∫ r, r.toReal ∂(P.map (fun ω => N.N ω S)) :=
      (integral_map hN_meas.aemeasurable htoReal_meas.aestronglyMeasurable).symm
    have h2 : ∫ r, r.toReal ∂((ProbabilityTheory.poissonMeasure μ).map (fun n : ℕ => (n : ℝ≥0∞))) =
        ∫ n : ℕ, ((n : ℝ≥0∞).toReal) ∂(ProbabilityTheory.poissonMeasure μ) :=
      integral_map hcast_meas.aemeasurable htoReal_meas.aestronglyMeasurable
    rw [h1, hlaw, h2]
    simp only [ENNReal.toReal_natCast, hpois_mean, hμ_eq]
  exact ⟨hint, hmean⟩

private lemma prm_count_lintegral {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) :
    ∫⁻ ω, N.N ω S ∂P = LevyStochCalc.Poisson.referenceIntensity ν S := by
  by_cases hinf : LevyStochCalc.Poisson.referenceIntensity ν S = ⊤
  · have hae : ∀ᵐ ω ∂P, N.N ω S = ⊤ := N.infinite_at_infinite_intensity hS hinf
    rw [lintegral_congr_ae hae, lintegral_const, measure_univ, mul_one, hinf]
  · obtain ⟨hint, hmean⟩ := prm_count_int_and_mean N hS hinf
    have hae_fin : ∀ᵐ ω ∂P, N.N ω S ≠ ⊤ := by
      filter_upwards [N.integer_valued hS hinf] with ω ⟨k, hk⟩
      rw [hk]
      exact ENNReal.natCast_ne_top k
    have hae_eq : (fun ω => N.N ω S) =ᵐ[P] fun ω => ENNReal.ofReal ((N.N ω S).toReal) := by
      filter_upwards [hae_fin] with ω hω
      exact (ENNReal.ofReal_toReal hω).symm
    rw [lintegral_congr_ae hae_eq,
      ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg),
      hmean, ENNReal.ofReal_toReal hinf]

/-! ### Section 2: Campbell's First Formula for `lintegral` -/

private lemma prm_lintegral_simpleFunc {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (s : SimpleFunc (ℝ × ℝ) ℝ≥0∞) :
    Measurable (fun ω => ∫⁻ z, s z ∂(N.N ω)) ∧
      ∫⁻ ω, (∫⁻ z, s z ∂(N.N ω)) ∂P =
        ∫⁻ z, s z ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
  have hexp : ∀ μ : Measure (ℝ × ℝ),
      ∫⁻ z, s z ∂μ = ∑ c ∈ s.range, c * μ (s ⁻¹' {c}) := fun μ => by
    rw [SimpleFunc.lintegral_eq_lintegral, SimpleFunc.lintegral]
  have hmeas : Measurable (fun ω => ∫⁻ z, s z ∂(N.N ω)) := by
    simp_rw [hexp]
    exact Finset.measurable_sum s.range fun c _ =>
      measurable_const.mul (N.measurable_eval (s.measurableSet_preimage {c}))
  refine ⟨hmeas, ?_⟩
  simp_rw [hexp]
  rw [lintegral_finsetSum (s := s.range) (f := fun c ω => c * N.N ω (s ⁻¹' {c})) fun c _ =>
    measurable_const.mul (N.measurable_eval (s.measurableSet_preimage {c}))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [lintegral_const_mul _ (N.measurable_eval (s.measurableSet_preimage {c})),
    prm_count_lintegral N (s.measurableSet_preimage {c})]

private lemma prm_lintegral_campbell {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun ω => ∫⁻ z, f z ∂(N.N ω)) ∧
      ∫⁻ ω, (∫⁻ z, f z ∂(N.N ω)) ∂P =
        ∫⁻ z, f z ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
  let s : ℕ → SimpleFunc (ℝ × ℝ) ℝ≥0∞ := SimpleFunc.eapprox f
  have hmono_pt : Monotone (fun m z => s m z) := fun m₁ m₂ hm z =>
    SimpleFunc.monotone_eapprox f hm z
  have hsup_pt : ∀ z, (⨆ m, s m z) = f z := fun z =>
    SimpleFunc.iSup_eapprox_apply hf z
  have hconv : ∀ μ : Measure (ℝ × ℝ),
      ∫⁻ z, f z ∂μ = ⨆ m, ∫⁻ z, s m z ∂μ := fun μ => by
    have hEq : f = fun z => ⨆ m, s m z := funext fun z => (hsup_pt z).symm
    conv_lhs => rw [hEq]
    exact lintegral_iSup (fun m => (s m).measurable) hmono_pt
  have hmeas_m : ∀ m, Measurable (fun ω => ∫⁻ z, s m z ∂(N.N ω)) := fun m =>
    (prm_lintegral_simpleFunc N (s m)).1
  have hmono_ω : Monotone (fun m ω => ∫⁻ z, s m z ∂(N.N ω)) := fun m₁ m₂ hm ω =>
    lintegral_mono fun z => SimpleFunc.monotone_eapprox f hm z
  have hmeas : Measurable (fun ω => ∫⁻ z, f z ∂(N.N ω)) := by
    simp_rw [hconv]
    exact Measurable.iSup hmeas_m
  refine ⟨hmeas, ?_⟩
  simp_rw [hconv]
  rw [lintegral_iSup hmeas_m hmono_ω]
  congr 1
  funext m
  exact (prm_lintegral_simpleFunc N (s m)).2

private lemma prm_window_lintegral_campbell {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {a b : ℝ} (ha : 0 ≤ a) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    Measurable (fun ω => ∫⁻ z in (Set.Ioc a b ×ˢ Set.univ), g z.2 ∂(N.N ω)) ∧
      ∫⁻ ω, (∫⁻ z in (Set.Ioc a b ×ˢ Set.univ), g z.2 ∂(N.N ω)) ∂P =
        ENNReal.ofReal (b - a) * ∫⁻ x, g x ∂ν := by
  let W : Set (ℝ × ℝ) := Set.Ioc a b ×ˢ Set.univ
  have hW : MeasurableSet W := measurableSet_Ioc.prod MeasurableSet.univ
  let f : ℝ × ℝ → ℝ≥0∞ := W.indicator (fun z => g z.2)
  have hf : Measurable f := (hg.comp measurable_snd).indicator hW
  have hrew : ∀ μ : Measure (ℝ × ℝ),
      ∫⁻ z in (Set.Ioc a b ×ˢ Set.univ), g z.2 ∂μ = ∫⁻ z, f z ∂μ := fun μ =>
    (lintegral_indicator hW _).symm
  obtain ⟨hmeas, heq⟩ := prm_lintegral_campbell N hf
  simp_rw [hrew]
  refine ⟨hmeas, ?_⟩
  rw [heq]
  unfold LevyStochCalc.Poisson.referenceIntensity
  rw [lintegral_prod f hf.aemeasurable]
  have hinner : ∀ s : ℝ,
      (∫⁻ x, f (s, x) ∂ν) = (Set.Ioc a b).indicator (fun _ => ∫⁻ x, g x ∂ν) s := by
    intro s
    by_cases hs : s ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hs]
      congr 1; funext x
      exact Set.indicator_of_mem (show (s, x) ∈ W from ⟨hs, trivial⟩) _
    · rw [Set.indicator_of_notMem hs]
      have hzero : (fun x => f (s, x)) = fun _ => 0 := by
        funext x
        exact Set.indicator_of_notMem (fun h => hs h.1) _
      rw [hzero, lintegral_zero]
  simp_rw [hinner]
  rw [lintegral_indicator_const measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc]
  have hsub : Set.Ioc a b ∩ Set.Ici (0 : ℝ) = Set.Ioc a b :=
    Set.inter_eq_left.mpr fun _ hx => ha.trans (le_of_lt hx.1)
  rw [hsub, Real.volume_Ioc, mul_comm]

/-! ### Section 3: Lévy measure power integrability equivalence (`2 ≤ n`) -/

private lemma levy_abs_pow_integrable_iff_large
    {ν : Measure ℝ} (hν : ProbabilityTheory.IsLevyMeasure ν)
    {n : ℕ} (hn : 2 ≤ n) :
    Integrable (fun x : ℝ => |x| ^ n) ν ↔
      Integrable (fun x : ℝ => |x| ^ n) (ν.restrict {x : ℝ | 1 ≤ |x|}) := by
  let A : Set ℝ := {x : ℝ | 1 ≤ |x|}
  have hA : MeasurableSet A := isClosed_le continuous_const continuous_abs |>.measurableSet
  have hf_meas : Measurable (fun x : ℝ => |x| ^ n) :=
    (continuous_abs.pow n).measurable
  constructor
  · intro h
    exact h.restrict
  · intro hLarge
    refine ⟨hf_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hsplit := lintegral_add_compl (fun x : ℝ => ‖|x| ^ n‖ₑ) hA (μ := ν)
    rw [← hsplit]
    refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
    · simpa [hasFiniteIntegral_iff_enorm] using hLarge.hasFiniteIntegral
    · have hle : ∫⁻ x in Aᶜ, ‖|x| ^ n‖ₑ ∂ν ≤ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
        calc ∫⁻ x in Aᶜ, ‖|x| ^ n‖ₑ ∂ν
            ≤ ∫⁻ x in Aᶜ, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
              refine lintegral_mono_ae ?_
              filter_upwards [ae_restrict_mem hA.compl] with x hx
              have hlt : |x| < 1 := not_le.mp hx
              rw [Real.enorm_of_nonneg (by positivity)]
              apply ENNReal.ofReal_le_ofReal
              have h1 : |x| ^ n ≤ |x| ^ 2 :=
                pow_le_pow_of_le_one (abs_nonneg x) hlt.le hn
              have h2 : x ^ 2 ≤ 1 := by
                have := sq_abs x
                nlinarith [abs_nonneg x]
              rw [sq_abs] at h1
              exact h1.trans (le_min h2 le_rfl)
          _ ≤ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν :=
              lintegral_mono' Measure.restrict_le_self le_rfl
      exact lt_of_le_of_lt hle hν.2

/-! ### Section 4: Completed right-continuous natural Poisson filtration -/

@[instance_reducible]
private noncomputable def natMeasSpace
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (r : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ (v : ℝ≥0) (_ : v ≤ r) (A : Set ℝ) (_ : MeasurableSet A),
    MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) inferInstance

private lemma natMeasSpace_le
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (r : ℝ≥0) : natMeasSpace N r ≤ mΩ := by
  refine iSup₂_le fun v _ => iSup₂_le fun A hA => ?_
  exact (N.measurable_eval (measurableSet_Ioc.prod hA)).comap_le

private lemma natMeasSpace_mono
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {r₁ r₂ : ℝ≥0} (hr : r₁ ≤ r₂) : natMeasSpace N r₁ ≤ natMeasSpace N r₂ := by
  refine iSup₂_le fun v hv => iSup₂_le fun A hA => ?_
  exact le_iSup₂_of_le v (hv.trans hr) (le_iSup₂_of_le A hA le_rfl)

private lemma natMeasSpace_count_measurable
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {r v : ℝ≥0} (hv : v ≤ r) {A : Set ℝ} (hA : MeasurableSet A) :
    @Measurable Ω ℝ≥0∞ (natMeasSpace N r) inferInstance
      (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) := by
  have hle :
      MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) inferInstance ≤
        natMeasSpace N r :=
    le_iSup₂_of_le v hv (le_iSup₂_of_le A hA le_rfl)
  exact Measurable.mono (comap_measurable _) hle le_rfl

@[instance_reducible]
private def completedMeasSpace
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' E :=
    @MeasurableSet Ω mΩ E ∧ ∃ A : Set Ω, @MeasurableSet Ω m A ∧ P (symmDiff E A) = 0
  measurableSet_empty :=
    ⟨@MeasurableSet.empty Ω mΩ, ∅, @MeasurableSet.empty Ω m, by simp⟩
  measurableSet_compl E hE := by
    rcases hE with ⟨hEm, A, hAm, hAE⟩
    refine ⟨MeasurableSet.compl (m := mΩ) hEm, Aᶜ, MeasurableSet.compl (m := m) hAm, ?_⟩
    have hsym : symmDiff Eᶜ Aᶜ = symmDiff E A := by
      ext x; simp only [Set.mem_symmDiff, Set.mem_compl_iff]; tauto
    rw [hsym]
    exact hAE
  measurableSet_iUnion f hf := by
    refine ⟨MeasurableSet.iUnion (m := mΩ) (fun n => (hf n).1), ?_⟩
    choose A hAm hAE using fun n => (hf n).2
    refine ⟨⋃ n, A n, MeasurableSet.iUnion (m := m) hAm, ?_⟩
    have hsub : symmDiff (⋃ n, f n) (⋃ n, A n) ⊆ ⋃ n, symmDiff (f n) (A n) := by
      intro x hx
      simp only [Set.mem_symmDiff, Set.mem_iUnion] at hx ⊢
      rcases hx with ⟨⟨n, hfn⟩, hnot⟩ | ⟨⟨n, hAn⟩, hnot⟩
      · exact ⟨n, Or.inl ⟨hfn, fun h => hnot ⟨n, h⟩⟩⟩
      · exact ⟨n, Or.inr ⟨hAn, fun h => hnot ⟨n, h⟩⟩⟩
    exact measure_mono_null hsub (measure_iUnion_null hAE)

private noncomputable def completedNatFiltration
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) where
  seq r := completedMeasSpace P (natMeasSpace N r)
  mono' _ _ hr _ hE :=
    ⟨hE.1, let ⟨A, hAm, hAE⟩ := hE.2; ⟨A, natMeasSpace_mono N hr A hAm, hAE⟩⟩
  le' _ _ hE := hE.1

private lemma exists_completedPoissonFiltration
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν) :
    ∃ ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω),
      Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ := by
  let 𝒞 := completedNatFiltration P N
  refine ⟨𝒞.rightCont, ?_, ?_, ?_, ?_⟩
  · intro t v hv A hA
    have hbase : @Measurable Ω ℝ≥0∞ (𝒞 t) inferInstance
        (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) := by
      intro S hS
      have hm_nat : @MeasurableSet Ω (natMeasSpace N t)
          ((fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) ⁻¹' S) :=
        natMeasSpace_count_measurable N hv hA hS
      exact ⟨natMeasSpace_le N t _ hm_nat, _, hm_nat, by simp⟩
    exact hbase.mono (𝒞.le_rightCont t) le_rfl
  · intro t S hS hPS
    have hbase : @MeasurableSet Ω (𝒞 t) S :=
      ⟨hS, ∅, @MeasurableSet.empty Ω (natMeasSpace N t), by simpa using hPS⟩
    exact 𝒞.le_rightCont t S hbase
  · exact ⟨le_of_eq 𝒞.rightCont_self⟩
  · intro G hG1 hG2 hG3
    have hCG : 𝒞 ≤ G := by
      intro r E hE
      have hnat_le : natMeasSpace N r ≤ G r := by
        refine iSup₂_le fun v hv => iSup₂_le fun A hA => ?_
        exact (hG1 r v hv A hA).comap_le
      rcases hE with ⟨hE_amb, A, hA_nat, hsym⟩
      have hA_amb : MeasurableSet A := natMeasSpace_le N r A hA_nat
      have hA_G : @MeasurableSet Ω (G r) A := hnat_le A hA_nat
      have hEA_G : @MeasurableSet Ω (G r) (E \ A) :=
        hG2 r (E \ A) (hE_amb.diff hA_amb)
          (measure_mono_null Set.subset_union_left hsym)
      have hAE_G : @MeasurableSet Ω (G r) (A \ E) :=
        hG2 r (A \ E) (hA_amb.diff hE_amb)
          (measure_mono_null Set.subset_union_right hsym)
      have heq : E = (A \ (A \ E)) ∪ (E \ A) := by
        ext ω
        simp only [Set.mem_union, Set.mem_sdiff]
        tauto
      rw [heq]
      exact (hA_G.diff hAE_G).union hEA_G
    have hrc_mono : 𝒞.rightCont ≤ G.rightCont := fun t => by
      simp only [Filtration.rightCont_apply, nhdsWithin_Ioi_neBot (le_refl t), ↓reduceIte]
      exact iInf₂_mono fun j _ => hCG j
    exact hrc_mono.trans hG3.1

private lemma filtration_le_completed_of_lt
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ)
    {s u : ℝ≥0} (hsu : s < u) :
    ℱ s ≤ completedMeasSpace P (natMeasSpace N u) := by
  let 𝒞 := completedNatFiltration P N
  have h1 : ∀ t v : ℝ≥0, v ≤ t → ∀ A : Set ℝ, MeasurableSet A →
      @Measurable Ω ℝ≥0∞ (𝒞.rightCont t) inferInstance
        (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) := by
    intro t v hv A hA
    have hbase : @Measurable Ω ℝ≥0∞ (𝒞 t) inferInstance
        (fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) := by
      intro S hS
      have hm_nat : @MeasurableSet Ω (natMeasSpace N t)
          ((fun ω => N.N ω (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A)) ⁻¹' S) :=
        natMeasSpace_count_measurable N hv hA hS
      exact ⟨natMeasSpace_le N t _ hm_nat, _, hm_nat, by simp⟩
    exact hbase.mono (𝒞.le_rightCont t) le_rfl
  have h2 : ∀ t (S : Set Ω), MeasurableSet S → P S = 0 →
      @MeasurableSet Ω (𝒞.rightCont t) S := by
    intro t S hS hPS
    have hbase : @MeasurableSet Ω (𝒞 t) S :=
      ⟨hS, ∅, @MeasurableSet.empty Ω (natMeasSpace N t), by simpa using hPS⟩
    exact 𝒞.le_rightCont t S hbase
  have h3 : 𝒞.rightCont.IsRightContinuous := ⟨le_of_eq 𝒞.rightCont_self⟩
  have hle : ℱ ≤ 𝒞.rightCont := hℱ.2.2.2 𝒞.rightCont h1 h2 h3
  have hrc : 𝒞.rightCont s = ⨅ (j : ℝ≥0) (_ : j > s), 𝒞 j := by
    rw [Filtration.rightCont_apply]
    simp [nhdsWithin_Ioi_neBot (le_refl s)]
  calc
    ℱ s ≤ 𝒞.rightCont s := hle s
    _ = ⨅ (j : ℝ≥0) (_ : j > s), 𝒞 j := hrc
    _ ≤ 𝒞 u := iInf₂_le u hsu

private lemma natMeasSpace_indep_future_count
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {u t : ℝ≥0} (hut : u < t) {C : Set ℝ} (hC : MeasurableSet C) (hCfin : ν C ≠ ⊤) :
    ProbabilityTheory.Indep (natMeasSpace N u)
      (MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ C)) inferInstance) P := by
  have hind := N.joint_past_future_independent (NNReal.coe_nonneg u) (by exact_mod_cast hut) hC hCfin
  refine ProbabilityTheory.indep_of_indep_of_le_left hind ?_
  refine iSup₂_le fun v hv => iSup₂_le fun A hA => ?_
  have hmem : Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A ∈
      {D : Set (ℝ × ℝ) | D ⊆ Set.Iic (u : ℝ) ×ˢ Set.univ ∧ MeasurableSet D} := by
    refine ⟨?_, measurableSet_Ioc.prod hA⟩
    intro z hz
    exact ⟨hz.1.2.trans (by exact_mod_cast hv), trivial⟩
  exact le_iSup₂_of_le (Set.Ioc (0 : ℝ) (v : ℝ) ×ˢ A) hmem le_rfl

private lemma setLintegral_future_count_eq
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {u t : ℝ≥0} (hut : u < t) {C : Set ℝ} (hC : MeasurableSet C) (hCfin : ν C < ⊤)
    {A : Set Ω} (hA : @MeasurableSet Ω (natMeasSpace N u) A) :
    ∫⁻ ω in A, N.N ω (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ C) ∂P =
      P A * (ENNReal.ofReal ((t : ℝ) - (u : ℝ)) * ν C) := by
  have hA_amb : MeasurableSet A := natMeasSpace_le N u A hA
  let W : Set (ℝ × ℝ) := Set.Ioc (u : ℝ) (t : ℝ) ×ˢ C
  have hW : MeasurableSet W := measurableSet_Ioc.prod hC
  have hWfin : LevyStochCalc.Poisson.referenceIntensity ν W ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top ν (NNReal.coe_nonneg u) hCfin
  let f : Ω → ℝ := A.indicator (fun _ => (1 : ℝ))
  let g : Ω → ℝ := fun ω => (N.N ω W).toReal
  have hind : ProbabilityTheory.Indep (natMeasSpace N u)
      (MeasurableSpace.comap (fun ω => N.N ω W) inferInstance) P :=
    natMeasSpace_indep_future_count N hut hC hCfin.ne
  have hf_nat : @Measurable Ω ℝ (natMeasSpace N u) inferInstance f :=
    (@measurable_const ℝ Ω _ (natMeasSpace N u) _).indicator hA
  have hg_comap : @Measurable Ω ℝ
      (MeasurableSpace.comap (fun ω => N.N ω W) inferInstance) inferInstance g :=
    ENNReal.measurable_toReal.comp (comap_measurable _)
  have hindFun : f ⟂ᵢ[P] g := by
    rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
    intro s₁ s₂ hs₁ hs₂
    exact (ProbabilityTheory.Indep_iff _ _ _).mp hind _ _ (hf_nat hs₁) (hg_comap hs₂)
  have hf_meas : Measurable f := measurable_const.indicator hA_amb
  have hg_meas : Measurable g := ENNReal.measurable_toReal.comp (N.measurable_eval hW)
  have hmul : (fun ω => A.indicator g ω) = (fun ω => f ω * g ω) := by
    funext ω; by_cases hω : ω ∈ A <;> simp [f, hω]
  have hsetInt : ∫ ω in A, g ω ∂P = P.real A * (((t : ℝ) - (u : ℝ)) * (ν C).toReal) := by
    rw [← integral_indicator hA_amb, hmul,
      hindFun.integral_fun_mul_eq_mul_integral hf_meas.aestronglyMeasurable hg_meas.aestronglyMeasurable]
    have hf_int : ∫ ω, f ω ∂P = P.real A := by
      simp only [f, integral_indicator_const (1 : ℝ) hA_amb, smul_eq_mul, mul_one]
    have hg_int : ∫ ω, g ω ∂P = ((t : ℝ) - (u : ℝ)) * (ν C).toReal := by
      rw [(prm_count_int_and_mean N hW hWfin).2,
        referenceIntensity_Ioc_prod ν (NNReal.coe_nonneg u),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr (by exact_mod_cast hut.le))]
    rw [hf_int, hg_int]
  have hae_eq : (fun ω => N.N ω W) =ᵐ[P.restrict A] fun ω => ENNReal.ofReal (g ω) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [N.integer_valued hW hWfin] with ω ⟨k, hk⟩
    simp [g, hk]
  rw [lintegral_congr_ae hae_eq,
    ← ofReal_integral_eq_lintegral_ofReal (prm_count_int_and_mean N hW hWfin).1.integrableOn
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg),
    hsetInt]
  have htu : 0 ≤ (t : ℝ) - (u : ℝ) := sub_nonneg.mpr (by exact_mod_cast hut.le)
  rw [ENNReal.ofReal_mul measureReal_nonneg,
    ENNReal.ofReal_mul htu,
    Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top P A),
    ENNReal.ofReal_toReal hCfin.ne]

/-! ### Section 5: Measurability (`ℱ t` and ambient) and future set-integral identity -/

private lemma simpleFunc_window_lintegral_eq
    (μ : Measure (ℝ × ℝ)) {a b : ℝ} (s : SimpleFunc ℝ ℝ≥0∞) :
    ∫⁻ z in (Set.Ioc a b ×ˢ Set.univ), s z.2 ∂μ =
      ∑ c ∈ s.range, c * μ (Set.Ioc a b ×ˢ (s ⁻¹' {c})) := by
  let W : Set (ℝ × ℝ) := Set.Ioc a b ×ˢ Set.univ
  have hW : MeasurableSet W := measurableSet_Ioc.prod MeasurableSet.univ
  let t : SimpleFunc (ℝ × ℝ) ℝ≥0∞ := s.comp Prod.snd measurable_snd
  have ht_eq : ∫⁻ z in W, s z.2 ∂μ = t.lintegral (μ.restrict W) := by
    simpa [t] using SimpleFunc.lintegral_eq_lintegral t (μ.restrict W)
  rw [ht_eq, SimpleFunc.lintegral]
  have hrange : t.range ⊆ s.range := by
    intro c hc
    rw [SimpleFunc.mem_range] at hc ⊢
    rcases hc with ⟨z, rfl⟩
    exact ⟨z.2, rfl⟩
  rw [Finset.sum_subset hrange]
  · refine Finset.sum_congr rfl fun c _ => ?_
    have hpre : MeasurableSet (t ⁻¹' {c}) := t.measurableSet_preimage {c}
    rw [Measure.restrict_apply hpre]
    have hinter : (t ⁻¹' {c}) ∩ W = Set.Ioc a b ×ˢ (s ⁻¹' {c}) := by
      ext z
      simp [t, W, and_comm]
    rw [hinter]
  · intro c _ hnot
    have hempty : t ⁻¹' {c} = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hz
      apply hnot
      rw [SimpleFunc.mem_range]
      exact ⟨z, hz⟩
    rw [hempty, measure_empty, mul_zero]

private lemma prm_window_lintegral_measurable_F
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ)
    (t : ℝ≥0) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    @Measurable Ω ℝ≥0∞ (ℱ t) _
      (fun ω => ∫⁻ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ), g z.2 ∂(N.N ω)) := by
  let s : ℕ → SimpleFunc ℝ ℝ≥0∞ := SimpleFunc.eapprox g
  have hconv : ∀ ω : Ω,
      ∫⁻ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ), g z.2 ∂(N.N ω) =
        ⨆ m : ℕ, ∑ c ∈ (s m).range,
          c * N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ ((s m) ⁻¹' {c})) := fun ω => by
    have hEq : (fun z : ℝ × ℝ => g z.2) = fun z => ⨆ m, s m z.2 :=
      funext fun z => (SimpleFunc.iSup_eapprox_apply hg z.2).symm
    conv_lhs => rw [hEq]
    rw [lintegral_iSup (f := fun m (z : ℝ × ℝ) => s m z.2)
      (fun m => (s m).measurable.comp measurable_snd)
      (fun m₁ m₂ hm z => SimpleFunc.monotone_eapprox g hm z.2)]
    congr 1; funext m
    exact simpleFunc_window_lintegral_eq (N.N ω) (s m)
  simp_rw [hconv]
  refine Measurable.iSup (mδ := ℱ t) fun m => ?_
  refine Finset.measurable_sum (m := ℱ t) (s m).range fun c _ => ?_
  exact (@measurable_const ℝ≥0∞ Ω _ (ℱ t) _).mul
    (hℱ.1 t t le_rfl ((s m) ⁻¹' {c}) ((s m).measurableSet_preimage {c}))

private lemma prm_window_signed_integral_decomp
    (μ : Measure (ℝ × ℝ)) (W : Set (ℝ × ℝ)) {f : ℝ → ℝ} (hf : Measurable f) :
    let fPos : ℝ → ℝ := fun x => max (f x) 0
    let fNeg : ℝ → ℝ := fun x => max (-(f x)) 0
    (∫ z in W, f z.2 ∂μ) =
      if (∫⁻ z in W, ENNReal.ofReal |f z.2| ∂μ) < ⊤ then
        (∫⁻ z in W, ENNReal.ofReal (fPos z.2) ∂μ).toReal -
          (∫⁻ z in W, ENNReal.ofReal (fNeg z.2) ∂μ).toReal
      else 0 := by
  intro fPos fNeg
  have hpos_meas : Measurable (fun z : ℝ × ℝ => fPos z.2) :=
    (hf.max measurable_const).comp measurable_snd
  have hneg_meas : Measurable (fun z : ℝ × ℝ => fNeg z.2) :=
    (hf.neg.max measurable_const).comp measurable_snd
  have hpos_int_eq : ∫ z in W, fPos z.2 ∂μ = (∫⁻ z in W, ENNReal.ofReal (fPos z.2) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => le_max_right _ _)
      hpos_meas.aestronglyMeasurable
  have hneg_int_eq : ∫ z in W, fNeg z.2 ∂μ = (∫⁻ z in W, ENNReal.ofReal (fNeg z.2) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => le_max_right _ _)
      hneg_meas.aestronglyMeasurable
  by_cases hfin : (∫⁻ z in W, ENNReal.ofReal |f z.2| ∂μ) < ⊤
  · rw [if_pos hfin, ← hpos_int_eq, ← hneg_int_eq]
    have hpos_int : Integrable (fun z : ℝ × ℝ => fPos z.2) (μ.restrict W) := by
      refine ⟨hpos_meas.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hfin
      rw [Real.enorm_of_nonneg (le_max_right _ _)]
      exact ENNReal.ofReal_le_ofReal (max_le (le_abs_self _) (abs_nonneg _))
    have hneg_int : Integrable (fun z : ℝ × ℝ => fNeg z.2) (μ.restrict W) := by
      refine ⟨hneg_meas.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hfin
      rw [Real.enorm_of_nonneg (le_max_right _ _)]
      exact ENNReal.ofReal_le_ofReal (max_le (neg_le_abs _) (abs_nonneg _))
    have hsub : (fun z : ℝ × ℝ => f z.2) = fun z => fPos z.2 - fNeg z.2 := by
      funext z
      dsimp [fPos, fNeg]
      rcases le_total 0 (f z.2) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]
      · rw [max_eq_right h, max_eq_left (by linarith), zero_sub, neg_neg]
    rw [hsub, integral_sub hpos_int hneg_int]
  · rw [if_neg hfin]
    have hnot : ¬ Integrable (fun z : ℝ × ℝ => f z.2) (μ.restrict W) := by
      intro hint
      apply hfin
      have := hint.hasFiniteIntegral
      rw [hasFiniteIntegral_iff_enorm] at this
      simpa only [Real.enorm_eq_ofReal_abs] using this
    exact integral_undef hnot

private lemma prm_window_signed_integral_measurable_F
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ)
    (t : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f) :
    @Measurable Ω ℝ (ℱ t) _
      (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ), f z.2 ∂(N.N ω)) := by
  let W : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ
  have hEq : (fun ω => ∫ z in W, f z.2 ∂(N.N ω)) =
      fun ω => if (∫⁻ z in W, ENNReal.ofReal |f z.2| ∂(N.N ω)) < ⊤ then
        (∫⁻ z in W, ENNReal.ofReal (max (f z.2) 0) ∂(N.N ω)).toReal -
          (∫⁻ z in W, ENNReal.ofReal (max (-(f z.2)) 0) ∂(N.N ω)).toReal
      else 0 := funext fun ω => prm_window_signed_integral_decomp (N.N ω) W hf
  rw [hEq]
  have hAbs_F := prm_window_lintegral_measurable_F N hℱ t
    (g := fun x => ENNReal.ofReal |f x|)
    (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hf))
  have hPos_F := prm_window_lintegral_measurable_F N hℱ t
    (g := fun x => ENNReal.ofReal (max (f x) 0))
    (ENNReal.measurable_ofReal.comp (hf.max measurable_const))
  have hNeg_F := prm_window_lintegral_measurable_F N hℱ t
    (g := fun x => ENNReal.ofReal (max (-(f x)) 0))
    (ENNReal.measurable_ofReal.comp (hf.neg.max measurable_const))
  have hset : @MeasurableSet Ω (ℱ t) {ω | (∫⁻ z in W, ENNReal.ofReal |f z.2| ∂(N.N ω)) < ⊤} :=
    hAbs_F measurableSet_Iio
  exact Measurable.ite (m := ℱ t) hset
    ((ENNReal.measurable_toReal.comp hPos_F).sub (ENNReal.measurable_toReal.comp hNeg_F))
    (@measurable_const ℝ Ω _ (ℱ t) _)

private lemma prm_window_signed_integral_measurable_ambient
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {a b : ℝ} (ha : 0 ≤ a) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun ω => ∫ z in (Set.Ioc a b ×ˢ Set.univ), f z.2 ∂(N.N ω)) := by
  let W : Set (ℝ × ℝ) := Set.Ioc a b ×ˢ Set.univ
  have hEq : (fun ω => ∫ z in W, f z.2 ∂(N.N ω)) =
      fun ω => if (∫⁻ z in W, ENNReal.ofReal |f z.2| ∂(N.N ω)) < ⊤ then
        (∫⁻ z in W, ENNReal.ofReal (max (f z.2) 0) ∂(N.N ω)).toReal -
          (∫⁻ z in W, ENNReal.ofReal (max (-(f z.2)) 0) ∂(N.N ω)).toReal
      else 0 := funext fun ω => prm_window_signed_integral_decomp (N.N ω) W hf
  rw [hEq]
  have hAbs := (prm_window_lintegral_campbell N (b := b) ha
    (g := fun x => ENNReal.ofReal |f x|)
    (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hf))).1
  have hPos := (prm_window_lintegral_campbell N (b := b) ha
    (g := fun x => ENNReal.ofReal (max (f x) 0))
    (ENNReal.measurable_ofReal.comp (hf.max measurable_const))).1
  have hNeg := (prm_window_lintegral_campbell N (b := b) ha
    (g := fun x => ENNReal.ofReal (max (-(f x)) 0))
    (ENNReal.measurable_ofReal.comp (hf.neg.max measurable_const))).1
  exact Measurable.ite (hAbs measurableSet_Iio)
    ((ENNReal.measurable_toReal.comp hPos).sub (ENNReal.measurable_toReal.comp hNeg))
    measurable_const

private lemma prm_future_setLintegral_nonneg
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {u t : ℝ≥0} (hut : u < t)
    {A : Set Ω} (hA : @MeasurableSet Ω (natMeasSpace N u) A)
    {g : ℝ → ℝ} (hg_meas : Measurable g) (hg_nn : ∀ x, 0 ≤ g x) (hg_int : Integrable g ν) :
    ∫⁻ ω in A, (∫⁻ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ),
      ENNReal.ofReal (g z.2) ∂(N.N ω)) ∂P =
      P A * (ENNReal.ofReal ((t : ℝ) - (u : ℝ)) * ∫⁻ x, ENNReal.ofReal (g x) ∂ν) := by
  let h : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (g x)
  have hh_meas : Measurable h := ENNReal.measurable_ofReal.comp hg_meas
  have hh_fin : ∫⁻ x, h x ∂ν < ⊤ := by
    have := hg_int.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at this
    simpa only [h, Real.enorm_of_nonneg (hg_nn _)] using this
  let s : ℕ → SimpleFunc ℝ ℝ≥0∞ := SimpleFunc.eapprox h
  have hstep : ∀ m : ℕ,
      ∫⁻ ω in A, (∫⁻ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ), s m z.2 ∂(N.N ω)) ∂P =
        P A * (ENNReal.ofReal ((t : ℝ) - (u : ℝ)) * ∫⁻ x, s m x ∂ν) := by
    intro m
    simp_rw [simpleFunc_window_lintegral_eq _ (s m)]
    rw [lintegral_finsetSum (s := (s m).range)
      (f := fun c ω => c * N.N ω (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ ((s m) ⁻¹' {c}))) fun c _ =>
      measurable_const.mul (N.measurable_eval
        (measurableSet_Ioc.prod ((s m).measurableSet_preimage {c})))]
    have hterm : ∀ c ∈ (s m).range,
        ∫⁻ ω in A, c * N.N ω (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ ((s m) ⁻¹' {c})) ∂P =
          P A * (ENNReal.ofReal ((t : ℝ) - (u : ℝ)) * (c * ν ((s m) ⁻¹' {c}))) := by
      intro c _
      by_cases hc0 : c = 0
      · simp [hc0]
      · have hCmeas : MeasurableSet ((s m) ⁻¹' {c}) := (s m).measurableSet_preimage {c}
        have hCfin : ν ((s m) ⁻¹' {c}) < ⊤ := by
          have hsub : (s m) ⁻¹' {c} ⊆ {x : ℝ | c ≤ s m x} := fun x hx => le_of_eq hx.symm
          have hmarkov := mul_meas_ge_le_lintegral (s m).measurable c (μ := ν)
          have hle1 : c * ν ((s m) ⁻¹' {c}) ≤ ∫⁻ x, s m x ∂ν :=
            (mul_le_mul_right (measure_mono hsub) c).trans hmarkov
          have hle2 : ∫⁻ x, s m x ∂ν ≤ ∫⁻ x, h x ∂ν :=
            lintegral_mono fun x => by
              rw [← SimpleFunc.iSup_eapprox_apply hh_meas x]
              exact le_iSup (fun k => s k x) m
          exact ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top hh_fin.ne (hle1.trans hle2)) hc0
        rw [lintegral_const_mul _ (N.measurable_eval (measurableSet_Ioc.prod hCmeas)),
          setLintegral_future_count_eq N hut hCmeas hCfin hA]
        ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.mul_sum]
    congr 2
    rw [SimpleFunc.lintegral_eq_lintegral, SimpleFunc.lintegral]
  have hconv_ω : ∀ ω : Ω,
      ∫⁻ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ), ENNReal.ofReal (g z.2) ∂(N.N ω) =
        ⨆ m, ∫⁻ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ), s m z.2 ∂(N.N ω) := fun ω => by
    have hEq : (fun z : ℝ × ℝ => ENNReal.ofReal (g z.2)) = fun z => ⨆ m, s m z.2 :=
      funext fun z => (SimpleFunc.iSup_eapprox_apply hh_meas z.2).symm
    conv_lhs => rw [hEq]
    exact lintegral_iSup (f := fun m (z : ℝ × ℝ) => s m z.2)
      (fun m => (s m).measurable.comp measurable_snd)
      (fun m₁ m₂ hm z => SimpleFunc.monotone_eapprox h hm z.2)
  have hmeas_m : ∀ m : ℕ, Measurable (fun ω =>
      ∫⁻ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ), s m z.2 ∂(N.N ω)) := fun m => by
    simp_rw [simpleFunc_window_lintegral_eq _ (s m)]
    exact Finset.measurable_sum (s m).range fun c _ =>
      measurable_const.mul (N.measurable_eval
        (measurableSet_Ioc.prod ((s m).measurableSet_preimage {c})))
  have hmono_ω : Monotone (fun m ω =>
      ∫⁻ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ), s m z.2 ∂(N.N ω)) := fun m₁ m₂ hm ω =>
    lintegral_mono fun z => SimpleFunc.monotone_eapprox h hm z.2
  simp_rw [hconv_ω]
  rw [lintegral_iSup hmeas_m hmono_ω]
  simp_rw [hstep]
  have hconv_ν : ∫⁻ x, h x ∂ν = ⨆ m, ∫⁻ x, s m x ∂ν := by
    have hEq : h = fun x => ⨆ m, s m x := funext fun x => (SimpleFunc.iSup_eapprox_apply hh_meas x).symm
    conv_lhs => rw [hEq]
    exact lintegral_iSup (fun m => (s m).measurable) (fun m₁ m₂ hm x => SimpleFunc.monotone_eapprox h hm x)
  rw [hconv_ν, ENNReal.mul_iSup, ENNReal.mul_iSup]

private lemma prm_future_setIntegral_nonneg
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {u t : ℝ≥0} (hut : u < t)
    {A : Set Ω} (hA : @MeasurableSet Ω (natMeasSpace N u) A)
    {g : ℝ → ℝ} (hg_meas : Measurable g) (hg_nn : ∀ x, 0 ≤ g x) (hg_int : Integrable g ν) :
    ∫ ω in A, (∫ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ), g z.2 ∂(N.N ω)) ∂P =
      P.real A * (((t : ℝ) - (u : ℝ)) * ∫ x, g x ∂ν) := by
  let W : Set (ℝ × ℝ) := Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ
  have hL := prm_future_setLintegral_nonneg N hut hA hg_meas hg_nn hg_int
  have hX_meas : Measurable (fun ω => ∫ z in W, g z.2 ∂(N.N ω)) :=
    prm_window_signed_integral_measurable_ambient N (NNReal.coe_nonneg u) hg_meas
  have hX_nn : ∀ ω, 0 ≤ ∫ z in W, g z.2 ∂(N.N ω) := fun ω =>
    integral_nonneg fun z => hg_nn z.2
  have hX_eq_toReal : ∀ ω, (∫ z in W, g z.2 ∂(N.N ω)) =
      (∫⁻ z in W, ENNReal.ofReal (g z.2) ∂(N.N ω)).toReal := fun ω =>
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => hg_nn z.2)
      (hg_meas.comp measurable_snd).aestronglyMeasurable
  have hg_lint_fin : ∫⁻ x, ENNReal.ofReal (g x) ∂ν < ⊤ := by
    have := hg_int.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at this
    simpa only [Real.enorm_of_nonneg (hg_nn _)] using this
  have hcamp := prm_window_lintegral_campbell N (a := (u : ℝ)) (b := (t : ℝ))
    (NNReal.coe_nonneg u) (g := fun x => ENNReal.ofReal (g x)) (ENNReal.measurable_ofReal.comp hg_meas)
  have hae_fin : ∀ᵐ ω ∂P, ∫⁻ z in W, ENNReal.ofReal (g z.2) ∂(N.N ω) < ⊤ := by
    refine ae_lt_top hcamp.1 ?_
    change ∫⁻ ω, ∫⁻ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ), ENNReal.ofReal (g z.2) ∂(N.N ω) ∂P ≠ ⊤
    rw [hcamp.2]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg_lint_fin.ne
  have hX_int_eq : ∫ ω in A, (∫ z in W, g z.2 ∂(N.N ω)) ∂P =
      (∫⁻ ω in A, ENNReal.ofReal (∫ z in W, g z.2 ∂(N.N ω)) ∂P).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hX_nn)
      hX_meas.aestronglyMeasurable
  have hae_ofReal : (fun ω => ENNReal.ofReal (∫ z in W, g z.2 ∂(N.N ω))) =ᵐ[P.restrict A]
      fun ω => ∫⁻ z in W, ENNReal.ofReal (g z.2) ∂(N.N ω) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hae_fin] with ω hω
    rw [hX_eq_toReal ω, ENNReal.ofReal_toReal hω.ne]
  rw [hX_int_eq, lintegral_congr_ae hae_ofReal, hL,
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (by exact_mod_cast hut.le)),
    ← Measure.real,
    ← integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg_nn)
      hg_meas.aestronglyMeasurable]

private lemma prm_future_setIntegral_signed
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {u t : ℝ≥0} (hut : u < t)
    {A : Set Ω} (hA : @MeasurableSet Ω (natMeasSpace N u) A)
    {f : ℝ → ℝ} (hf_meas : Measurable f) (hf_int : Integrable f ν) :
    ∫ ω in A, (∫ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ), f z.2 ∂(N.N ω)) ∂P =
      P.real A * (((t : ℝ) - (u : ℝ)) * ∫ x, f x ∂ν) := by
  let W : Set (ℝ × ℝ) := Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ
  let fPos : ℝ → ℝ := fun x => max (f x) 0
  let fNeg : ℝ → ℝ := fun x => max (-(f x)) 0
  have hfPos_meas : Measurable fPos := hf_meas.max measurable_const
  have hfNeg_meas : Measurable fNeg := hf_meas.neg.max measurable_const
  have hfPos_nn : ∀ x, 0 ≤ fPos x := fun _ => le_max_right _ _
  have hfNeg_nn : ∀ x, 0 ≤ fNeg x := fun _ => le_max_right _ _
  have hfPos_int : Integrable fPos ν :=
    hf_int.norm.mono' hfPos_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (hfPos_nn x), Real.norm_eq_abs]
      exact max_le (le_abs_self _) (abs_nonneg _))
  have hfNeg_int : Integrable fNeg ν :=
    hf_int.norm.mono' hfNeg_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (hfNeg_nn x), Real.norm_eq_abs]
      exact max_le (neg_le_abs _) (abs_nonneg _))
  have hAbs_lint_fin : ∫⁻ x, ENNReal.ofReal |f x| ∂ν < ⊤ := by
    have := hf_int.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at this
    simpa only [Real.enorm_eq_ofReal_abs] using this
  have hcamp := prm_window_lintegral_campbell N (a := (u : ℝ)) (b := (t : ℝ))
    (NNReal.coe_nonneg u) (g := fun x => ENNReal.ofReal |f x|)
    (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hf_meas))
  have hae_fin : ∀ᵐ ω ∂P, ∫⁻ z in W, ENNReal.ofReal |f z.2| ∂(N.N ω) < ⊤ := by
    refine ae_lt_top hcamp.1 ?_
    change ∫⁻ ω, ∫⁻ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ), ENNReal.ofReal |f z.2| ∂(N.N ω) ∂P ≠ ⊤
    rw [hcamp.2]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAbs_lint_fin.ne
  have hae_split :
      (fun ω => ∫ z in W, f z.2 ∂(N.N ω)) =ᵐ[P.restrict A]
        fun ω => (∫ z in W, fPos z.2 ∂(N.N ω)) - ∫ z in W, fNeg z.2 ∂(N.N ω) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hae_fin] with ω hω
    have hpos_eq : ∫ z in W, fPos z.2 ∂(N.N ω) = (∫⁻ z in W, ENNReal.ofReal (fPos z.2) ∂(N.N ω)).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => hfPos_nn z.2)
        (hfPos_meas.comp measurable_snd).aestronglyMeasurable
    have hneg_eq : ∫ z in W, fNeg z.2 ∂(N.N ω) = (∫⁻ z in W, ENNReal.ofReal (fNeg z.2) ∂(N.N ω)).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => hfNeg_nn z.2)
        (hfNeg_meas.comp measurable_snd).aestronglyMeasurable
    rw [prm_window_signed_integral_decomp (N.N ω) W hf_meas, if_pos hω, hpos_eq, hneg_eq]
  have hPos_P_int : Integrable (fun ω => ∫ z in W, fPos z.2 ∂(N.N ω)) P := by
    refine ⟨(prm_window_signed_integral_measurable_ambient N (NNReal.coe_nonneg u) hfPos_meas).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hcampPos := prm_window_lintegral_campbell N (a := (u : ℝ)) (b := (t : ℝ))
      (NNReal.coe_nonneg u) (g := fun x => ENNReal.ofReal (fPos x))
      (ENNReal.measurable_ofReal.comp hfPos_meas)
    have hle : ∫⁻ ω, ‖∫ z in W, fPos z.2 ∂(N.N ω)‖ₑ ∂P ≤
        ∫⁻ ω, (∫⁻ z in W, ENNReal.ofReal (fPos z.2) ∂(N.N ω)) ∂P := by
      refine lintegral_mono fun ω => ?_
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
      rw [Real.enorm_of_nonneg (hfPos_nn z.2)]
    refine lt_of_le_of_lt hle ?_
    change ∫⁻ ω, ∫⁻ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ),
      ENNReal.ofReal (fPos z.2) ∂(N.N ω) ∂P < ⊤
    rw [hcampPos.2]
    have hfPos_fin : ∫⁻ x, ENNReal.ofReal (fPos x) ∂ν < ⊤ := by
      have := hfPos_int.hasFiniteIntegral
      rw [hasFiniteIntegral_iff_enorm] at this
      simpa only [Real.enorm_of_nonneg (hfPos_nn _)] using this
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfPos_fin
  have hNeg_P_int : Integrable (fun ω => ∫ z in W, fNeg z.2 ∂(N.N ω)) P := by
    refine ⟨(prm_window_signed_integral_measurable_ambient N (NNReal.coe_nonneg u) hfNeg_meas).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hcampNeg := prm_window_lintegral_campbell N (a := (u : ℝ)) (b := (t : ℝ))
      (NNReal.coe_nonneg u) (g := fun x => ENNReal.ofReal (fNeg x))
      (ENNReal.measurable_ofReal.comp hfNeg_meas)
    have hle : ∫⁻ ω, ‖∫ z in W, fNeg z.2 ∂(N.N ω)‖ₑ ∂P ≤
        ∫⁻ ω, (∫⁻ z in W, ENNReal.ofReal (fNeg z.2) ∂(N.N ω)) ∂P := by
      refine lintegral_mono fun ω => ?_
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
      rw [Real.enorm_of_nonneg (hfNeg_nn z.2)]
    refine lt_of_le_of_lt hle ?_
    change ∫⁻ ω, ∫⁻ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ),
      ENNReal.ofReal (fNeg z.2) ∂(N.N ω) ∂P < ⊤
    rw [hcampNeg.2]
    have hfNeg_fin : ∫⁻ x, ENNReal.ofReal (fNeg x) ∂ν < ⊤ := by
      have := hfNeg_int.hasFiniteIntegral
      rw [hasFiniteIntegral_iff_enorm] at this
      simpa only [Real.enorm_of_nonneg (hfNeg_nn _)] using this
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfNeg_fin
  have hf_sub : f = fun x => fPos x - fNeg x := by
    funext x
    dsimp [fPos, fNeg]
    rcases le_total 0 (f x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]
    · rw [max_eq_right h, max_eq_left (by linarith), zero_sub, neg_neg]
  rw [integral_congr_ae hae_split,
    integral_sub hPos_P_int.integrableOn hNeg_P_int.integrableOn,
    prm_future_setIntegral_nonneg N hut hA hfPos_meas hfPos_nn hfPos_int,
    prm_future_setIntegral_nonneg N hut hA hfNeg_meas hfNeg_nn hfNeg_int]
  conv_rhs => rw [hf_sub, integral_sub hfPos_int hfNeg_int]
  ring

end Exercise2_6Helpers

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (n : ℕ) (hn : 2 ≤ n) :
    (∀ (t : ℝ≥0), 0 < t →
       ((∫⁻ ω, ∫⁻ z in
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ),
            ENNReal.ofReal (|z.2| ^ n) ∂(N.N ω) ∂P) < ⊤ ↔
        Integrable (fun x : ℝ => |x| ^ n)
          (ν.restrict {x : ℝ | 1 ≤ |x|}))) ∧
    (Integrable (fun x : ℝ => |x| ^ n)
        (ν.restrict {x : ℝ | 1 ≤ |x|}) →
      ∃ ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω),
        Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ ∧
        MeasureTheory.Martingale
          (fun (t : ℝ≥0) ω =>
            (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ),
               z.2 ^ n ∂(N.N ω)) -
            (t : ℝ) * ∫ x, x ^ n ∂ν) ℱ P) := by
  have habs_meas : Measurable (fun x : ℝ => |x| ^ n) := (continuous_abs.pow n).measurable
  have hpow_meas : Measurable (fun x : ℝ => x ^ n) := (continuous_pow n).measurable
  constructor
  · -- Part 1: Campbell's formula + Lévy measure small-jump bound
    intro t ht
    have hcamp := (Exercise2_6Helpers.prm_window_lintegral_campbell N (a := (0 : ℝ)) (b := (t : ℝ))
      le_rfl (g := fun x => ENNReal.ofReal (|x| ^ n)) (ENNReal.measurable_ofReal.comp habs_meas)).2
    rw [hcamp, sub_zero]
    have ht_pos : (0 : ℝ≥0∞) < ENNReal.ofReal (t : ℝ) :=
      ENNReal.ofReal_pos.mpr (by exact_mod_cast ht)
    have hmul_iff : ENNReal.ofReal (t : ℝ) * ∫⁻ x, ENNReal.ofReal (|x| ^ n) ∂ν < ⊤ ↔
        ∫⁻ x, ENNReal.ofReal (|x| ^ n) ∂ν < ⊤ := by
      constructor
      · intro h
        exact ENNReal.lt_top_of_mul_ne_top_right h.ne ht_pos.ne'
      · intro h
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h
    rw [hmul_iff, ← Exercise2_6Helpers.levy_abs_pow_integrable_iff_large hν hn]
    constructor
    · intro hfin
      refine ⟨habs_meas.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      simpa only [Real.enorm_of_nonneg (by positivity : (0 : ℝ) ≤ |(_ : ℝ)| ^ n)] using hfin
    · intro hint
      have := hint.hasFiniteIntegral
      rw [hasFiniteIntegral_iff_enorm] at this
      simpa only [Real.enorm_of_nonneg (by positivity : (0 : ℝ) ≤ |(_ : ℝ)| ^ n)] using this
  · -- Part 2: Existence of completed Poisson filtration + compensated martingale property
    intro hLarge
    have hIntAbs : Integrable (fun x : ℝ => |x| ^ n) ν :=
      (Exercise2_6Helpers.levy_abs_pow_integrable_iff_large hν hn).mpr hLarge
    have hIntPow : Integrable (fun x : ℝ => x ^ n) ν :=
      hIntAbs.mono' hpow_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_pow])
    have hAbs_lint_fin : ∫⁻ x, ENNReal.ofReal (|x| ^ n) ∂ν < ⊤ := by
      have := hIntAbs.hasFiniteIntegral
      rw [hasFiniteIntegral_iff_enorm] at this
      simpa only [Real.enorm_of_nonneg (by positivity : (0 : ℝ) ≤ |(_ : ℝ)| ^ n)] using this
    obtain ⟨ℱ, hℱ⟩ := Exercise2_6Helpers.exists_completedPoissonFiltration P ν N
    refine ⟨ℱ, hℱ, ?_⟩
    let M : ℝ≥0 → Ω → ℝ := fun r ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (r : ℝ) ×ˢ Set.univ), z.2 ^ n ∂(N.N ω)) -
        (r : ℝ) * ∫ x, x ^ n ∂ν
    have hM_adapted : StronglyAdapted ℱ M := fun r => by
      have h1 : @Measurable Ω ℝ (ℱ r) _
          (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (r : ℝ) ×ˢ Set.univ), z.2 ^ n ∂(N.N ω)) :=
        Exercise2_6Helpers.prm_window_signed_integral_measurable_F N hℱ r hpow_meas
      have h1_sm : StronglyMeasurable[ℱ r]
          (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (r : ℝ) ×ˢ Set.univ), z.2 ^ n ∂(N.N ω)) :=
        @Measurable.stronglyMeasurable Ω ℝ _ (ℱ r) _ _ _ _ _ h1
      exact h1_sm.sub stronglyMeasurable_const
    have hM_int : ∀ r : ℝ≥0, Integrable (M r) P := fun r => by
      have hX_meas : Measurable
          (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (r : ℝ) ×ˢ Set.univ), z.2 ^ n ∂(N.N ω)) :=
        Exercise2_6Helpers.prm_window_signed_integral_measurable_ambient N le_rfl hpow_meas
      have hX_fin : HasFiniteIntegral
          (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (r : ℝ) ×ˢ Set.univ), z.2 ^ n ∂(N.N ω)) P := by
        rw [hasFiniteIntegral_iff_enorm]
        have hle : ∫⁻ ω, ‖∫ z in (Set.Ioc (0 : ℝ) (r : ℝ) ×ˢ Set.univ), z.2 ^ n ∂(N.N ω)‖ₑ ∂P ≤
            ∫⁻ ω, (∫⁻ z in (Set.Ioc (0 : ℝ) (r : ℝ) ×ˢ Set.univ),
              ENNReal.ofReal (|z.2| ^ n) ∂(N.N ω)) ∂P := by
          refine lintegral_mono fun ω => ?_
          refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
          rw [Real.enorm_eq_ofReal_abs, abs_pow]
        refine lt_of_le_of_lt hle ?_
        rw [(Exercise2_6Helpers.prm_window_lintegral_campbell N (a := (0 : ℝ)) (b := (r : ℝ))
          le_rfl (g := fun x => ENNReal.ofReal (|x| ^ n)) (ENNReal.measurable_ofReal.comp habs_meas)).2]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hAbs_lint_fin
      exact Integrable.sub ⟨hX_meas.aestronglyMeasurable, hX_fin⟩ (integrable_const _)
    refine ⟨hM_adapted, fun s t hst => ?_⟩
    rcases eq_or_lt_of_le hst with rfl | hst_lt
    · exact Filter.EventuallyEq.of_eq
        (condExp_of_stronglyMeasurable (ℱ.le s) (hM_adapted s) (hM_int s))
    · refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hM_int t)
        (fun E _ _ => (hM_int s).integrableOn) ?_
        (hM_adapted s).aestronglyMeasurable).symm
      -- Shared full-measure good event `G` on `W := (0, t] × univ`
      let W : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ
      have hcampW := Exercise2_6Helpers.prm_window_lintegral_campbell N (a := (0 : ℝ)) (b := (t : ℝ))
        le_rfl (g := fun x => ENNReal.ofReal (|x| ^ n)) (ENNReal.measurable_ofReal.comp habs_meas)
      let Z_enn : Ω → ℝ≥0∞ := fun ω => ∫⁻ z in W, ENNReal.ofReal (|z.2| ^ n) ∂(N.N ω)
      let Z : Ω → ℝ := fun ω => (Z_enn ω).toReal
      let G : Set Ω := {ω | Z_enn ω < ⊤}
      have hae_G : ∀ᵐ ω ∂P, ω ∈ G := by
        refine ae_lt_top hcampW.1 ?_
        change ∫⁻ ω, ∫⁻ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ),
          ENNReal.ofReal (|z.2| ^ n) ∂(N.N ω) ∂P ≠ ⊤
        rw [hcampW.2]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAbs_lint_fin.ne
      have hZ_int : Integrable Z P := by
        refine ⟨(ENNReal.measurable_toReal.comp hcampW.1).aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_enorm]
        have hle : ∫⁻ ω, ‖Z ω‖ₑ ∂P ≤ ∫⁻ ω, Z_enn ω ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.ofReal_toReal_le
        refine lt_of_le_of_lt hle ?_
        change ∫⁻ ω, ∫⁻ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ),
          ENNReal.ofReal (|z.2| ^ n) ∂(N.N ω) ∂P < ⊤
        rw [hcampW.2]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hAbs_lint_fin
      have hG_int_W : ∀ ω ∈ G,
          Integrable (fun z : ℝ × ℝ => |z.2| ^ n) ((N.N ω).restrict W) ∧
            Integrable (fun z : ℝ × ℝ => z.2 ^ n) ((N.N ω).restrict W) := by
        intro ω hω
        have h1 : Integrable (fun z : ℝ × ℝ => |z.2| ^ n) ((N.N ω).restrict W) := by
          refine ⟨(habs_meas.comp measurable_snd).aestronglyMeasurable, ?_⟩
          rw [hasFiniteIntegral_iff_enorm]
          simpa only [G, Set.mem_ofPred_eq, Z_enn,
            Real.enorm_of_nonneg (by positivity : (0 : ℝ) ≤ |(_ : ℝ)| ^ n)] using hω
        have h2 : Integrable (fun z : ℝ × ℝ => z.2 ^ n) ((N.N ω).restrict W) :=
          h1.mono' (hpow_meas.comp measurable_snd).aestronglyMeasurable
            (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_pow])
        exact ⟨h1, h2⟩
      have hZ_eq_on_G : ∀ ω ∈ G, Z ω = ∫ z in W, |z.2| ^ n ∂(N.N ω) := fun ω _ =>
        (integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun (z : ℝ × ℝ) => pow_nonneg (abs_nonneg z.2) n)
          (habs_meas.comp measurable_snd).aestronglyMeasurable).symm
      -- Step A: For any `u` with `s < u < t` and `A ∈ natMeasSpace N u`, `∫_A Δ(u, t) = 0`
      have hfuture_zero : ∀ (u : ℝ≥0) (hut : u < t) (A : Set Ω)
          (_ : @MeasurableSet Ω (Exercise2_6Helpers.natMeasSpace N u) A),
          ∫ ω in A, ((∫ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ), z.2 ^ n ∂(N.N ω)) -
            ((t : ℝ) - (u : ℝ)) * ∫ x, x ^ n ∂ν) ∂P = 0 := by
        intro u hut A hA
        have hXu_int : Integrable
            (fun ω => ∫ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ), z.2 ^ n ∂(N.N ω)) P := by
          refine ⟨(Exercise2_6Helpers.prm_window_signed_integral_measurable_ambient N
            (NNReal.coe_nonneg u) hpow_meas).aestronglyMeasurable, ?_⟩
          rw [hasFiniteIntegral_iff_enorm]
          have hle : ∫⁻ ω, ‖∫ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ), z.2 ^ n ∂(N.N ω)‖ₑ ∂P ≤
              ∫⁻ ω, (∫⁻ z in (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ Set.univ),
                ENNReal.ofReal (|z.2| ^ n) ∂(N.N ω)) ∂P := by
            refine lintegral_mono fun ω => ?_
            refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
            rw [Real.enorm_eq_ofReal_abs, abs_pow]
          refine lt_of_le_of_lt hle ?_
          rw [(Exercise2_6Helpers.prm_window_lintegral_campbell N (a := (u : ℝ)) (b := (t : ℝ))
            (NNReal.coe_nonneg u) (g := fun x => ENNReal.ofReal (|x| ^ n))
            (ENNReal.measurable_ofReal.comp habs_meas)).2]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hAbs_lint_fin
        rw [integral_sub hXu_int.integrableOn (integrable_const _),
          Exercise2_6Helpers.prm_future_setIntegral_signed N hut hA hpow_meas hIntPow,
          setIntegral_const, smul_eq_mul, sub_self]
      -- Step B: For any `E ∈ ℱ s`, send `u_k ↓ s` to prove `∫_E Δ(s, t) = 0`
      intro E hE_Fs _
      have hts_pos : (0 : ℝ) < (t : ℝ) - (s : ℝ) := sub_pos.mpr (by exact_mod_cast hst_lt)
      let u : ℕ → ℝ≥0 := fun k =>
        ⟨(s : ℝ) + ((t : ℝ) - (s : ℝ)) / ((k : ℝ) + 2), by positivity⟩
      have hsu : ∀ k : ℕ, s < u k := fun k => by
        change (s : ℝ) < (s : ℝ) + ((t : ℝ) - (s : ℝ)) / ((k : ℝ) + 2)
        have : (0 : ℝ) < ((t : ℝ) - (s : ℝ)) / ((k : ℝ) + 2) := by positivity
        linarith
      have hut : ∀ k : ℕ, u k < t := fun k => by
        change (s : ℝ) + ((t : ℝ) - (s : ℝ)) / ((k : ℝ) + 2) < (t : ℝ)
        have hdiv : ((t : ℝ) - (s : ℝ)) / ((k : ℝ) + 2) < (t : ℝ) - (s : ℝ) :=
          div_lt_self hts_pos (by linarith [Nat.cast_nonneg (α := ℝ) k])
        linarith
      have hu_tendsto : Tendsto (fun k => (u k : ℝ)) atTop (𝓝 (s : ℝ)) := by
        have hzero : Tendsto (fun k : ℕ => ((t : ℝ) - (s : ℝ)) / ((k : ℝ) + 2)) atTop (𝓝 0) := by
          simpa [div_eq_mul_inv] using
            (tendsto_const_nhds (x := (t : ℝ) - (s : ℝ))).mul
              (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
        change Tendsto (fun k : ℕ => (s : ℝ) + ((t : ℝ) - (s : ℝ)) / ((k : ℝ) + 2)) atTop (𝓝 (s : ℝ))
        simpa using (tendsto_const_nhds (x := (s : ℝ))).add hzero
      let Δu : ℕ → Ω → ℝ := fun k ω =>
        (∫ z in (Set.Ioc (u k : ℝ) (t : ℝ) ×ˢ Set.univ), z.2 ^ n ∂(N.N ω)) -
          ((t : ℝ) - (u k : ℝ)) * ∫ x, x ^ n ∂ν
      let Δs : Ω → ℝ := fun ω =>
        (∫ z in (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ), z.2 ^ n ∂(N.N ω)) -
          ((t : ℝ) - (s : ℝ)) * ∫ x, x ^ n ∂ν
      have hΔu_int_zero : ∀ k : ℕ, ∫ ω in E, Δu k ω ∂P = 0 := fun k => by
        have hle := Exercise2_6Helpers.filtration_le_completed_of_lt N hℱ (hsu k)
        rcases (hle E hE_Fs).2 with ⟨A, hA_nat, hEA⟩
        have hae_set : E =ᵐ[P] A := measure_symmDiff_eq_zero_iff.mp hEA
        rw [setIntegral_congr_set hae_set]
        exact hfuture_zero (u k) (hut k) A hA_nat
      have hΔu_meas : ∀ k : ℕ, Measurable (Δu k) := fun k =>
        (Exercise2_6Helpers.prm_window_signed_integral_measurable_ambient N
          (NNReal.coe_nonneg (u k)) hpow_meas).sub measurable_const
      have hΔu_on_G : ∀ ω ∈ G,
          (∀ k : ℕ, ‖Δu k ω‖ ≤ Z ω + (t : ℝ) * |∫ x, x ^ n ∂ν|) ∧
            Tendsto (fun k => Δu k ω) atTop (𝓝 (Δs ω)) := by
        intro ω hω
        obtain ⟨habs_int_W, hpow_int_W⟩ := hG_int_W ω hω
        have hbound : ∀ k : ℕ, ‖Δu k ω‖ ≤ Z ω + (t : ℝ) * |∫ x, x ^ n ∂ν| := fun k => by
          rw [Real.norm_eq_abs]
          have hsub_u : Set.Ioc (u k : ℝ) (t : ℝ) ×ˢ Set.univ ⊆ W :=
            Set.prod_mono (Set.Ioc_subset_Ioc_left (NNReal.coe_nonneg (u k))) le_rfl
          have h1 : |∫ z in (Set.Ioc (u k : ℝ) (t : ℝ) ×ˢ Set.univ), z.2 ^ n ∂(N.N ω)| ≤ Z ω := by
            rw [hZ_eq_on_G ω hω]
            refine (abs_integral_le_integral_abs).trans ?_
            simp_rw [abs_pow]
            exact setIntegral_mono_set habs_int_W (Filter.Eventually.of_forall fun _ => by positivity)
              (Filter.Eventually.of_forall hsub_u)
          have h2 : |((t : ℝ) - (u k : ℝ)) * ∫ x, x ^ n ∂ν| ≤ (t : ℝ) * |∫ x, x ^ n ∂ν| := by
            rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (hut k).le))]
            exact mul_le_mul_of_nonneg_right (by linarith [NNReal.coe_nonneg (u k)]) (abs_nonneg _)
          exact (abs_sub _ _).trans (add_le_add h1 h2)
        refine ⟨hbound, ?_⟩
        -- Convergence of the integral part via dominated convergence on `((N.N ω).restrict W)`
        have hint_tendsto :
            Tendsto (fun k => ∫ z in (Set.Ioc (u k : ℝ) (t : ℝ) ×ˢ Set.univ), z.2 ^ n ∂(N.N ω))
              atTop (𝓝 (∫ z in (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ), z.2 ^ n ∂(N.N ω))) := by
          have hrew_u : ∀ k : ℕ,
              ∫ z in (Set.Ioc (u k : ℝ) (t : ℝ) ×ˢ Set.univ), z.2 ^ n ∂(N.N ω) =
                ∫ z in W, (Set.Ioc (u k : ℝ) (t : ℝ) ×ˢ Set.univ).indicator
                  (fun z : ℝ × ℝ => z.2 ^ n) z ∂(N.N ω) := fun k => by
            have hsub_u : Set.Ioc (u k : ℝ) (t : ℝ) ×ˢ Set.univ ⊆ W :=
              Set.prod_mono (Set.Ioc_subset_Ioc_left (NNReal.coe_nonneg (u k))) le_rfl
            rw [setIntegral_indicator (measurableSet_Ioc.prod MeasurableSet.univ),
              Set.inter_eq_right.mpr hsub_u]
          have hrew_s :
              ∫ z in (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ), z.2 ^ n ∂(N.N ω) =
                ∫ z in W, (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ).indicator
                  (fun z : ℝ × ℝ => z.2 ^ n) z ∂(N.N ω) := by
            have hsub_s : Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ ⊆ W :=
              Set.prod_mono (Set.Ioc_subset_Ioc_left (NNReal.coe_nonneg s)) le_rfl
            rw [setIntegral_indicator (measurableSet_Ioc.prod MeasurableSet.univ),
              Set.inter_eq_right.mpr hsub_s]
          simp_rw [hrew_u, hrew_s]
          refine MeasureTheory.tendsto_integral_of_dominated_convergence
            (fun z : ℝ × ℝ => |z.2| ^ n)
            (fun k => ((hpow_meas.comp measurable_snd).indicator
              (measurableSet_Ioc.prod MeasurableSet.univ)).aestronglyMeasurable)
            habs_int_W
            (fun k => Filter.Eventually.of_forall fun z => by
              rw [Real.norm_eq_abs]
              by_cases hz : z ∈ Set.Ioc (u k : ℝ) (t : ℝ) ×ˢ Set.univ
              · rw [Set.indicator_of_mem hz, abs_pow]
              · rw [Set.indicator_of_notMem hz, abs_zero]; positivity)
            (Filter.Eventually.of_forall fun z => ?_)
          by_cases hz : z ∈ Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ
          · rw [Set.indicator_of_mem hz]
            have hev : ∀ᶠ k in atTop, (u k : ℝ) < z.1 :=
              hu_tendsto.eventually (gt_mem_nhds hz.1.1)
            refine tendsto_const_nhds.congr' ?_
            filter_upwards [hev] with k hk
            exact (Set.indicator_of_mem (show z ∈ Set.Ioc (u k : ℝ) (t : ℝ) ×ˢ Set.univ from ⟨⟨hk, hz.1.2⟩, trivial⟩) (fun z : ℝ × ℝ => z.2 ^ n)).symm
          · rw [Set.indicator_of_notMem hz]
            have hall : ∀ k : ℕ, z ∉ Set.Ioc (u k : ℝ) (t : ℝ) ×ˢ Set.univ := fun k hzk =>
              hz ⟨⟨lt_trans (by exact_mod_cast hsu k) hzk.1.1, hzk.1.2⟩, trivial⟩
            simp_rw [Set.indicator_of_notMem (hall _)]
            exact tendsto_const_nhds
        have hdrift_tendsto :
            Tendsto (fun k => ((t : ℝ) - (u k : ℝ)) * ∫ x, x ^ n ∂ν) atTop
              (𝓝 (((t : ℝ) - (s : ℝ)) * ∫ x, x ^ n ∂ν)) :=
          (tendsto_const_nhds.sub hu_tendsto).mul_const _
        exact hint_tendsto.sub hdrift_tendsto
      have hΔs_int_E : ∫ ω in E, Δs ω ∂P = 0 := by
        have htend : Tendsto (fun k => ∫ ω in E, Δu k ω ∂P) atTop (𝓝 (∫ ω in E, Δs ω ∂P)) := by
          refine MeasureTheory.tendsto_integral_of_dominated_convergence
            (fun ω => Z ω + (t : ℝ) * |∫ x, x ^ n ∂ν|)
            (fun k => (hΔu_meas k).aestronglyMeasurable)
            (hZ_int.add (integrable_const _)).integrableOn
            (fun k => ae_restrict_of_ae (hae_G.mono fun ω hω => (hΔu_on_G ω hω).1 k))
            (ae_restrict_of_ae (hae_G.mono fun ω hω => (hΔu_on_G ω hω).2))
        simp_rw [hΔu_int_zero] at htend
        exact tendsto_nhds_unique htend tendsto_const_nhds
      -- Step C: `M t =ᵐ[P] M s + Δs`, so `∫_E M s = ∫_E M t`
      have hMt_ae : M t =ᵐ[P] (fun ω => M s ω + Δs ω) := by
        filter_upwards [hae_G] with ω hω
        have hpow_int_W := (hG_int_W ω hω).2
        have hunion :
            (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ Set.univ) ∪ (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ) = W := by
          rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc (NNReal.coe_nonneg s)
            (by exact_mod_cast hst_lt.le)]
        have hdisj :
            Disjoint (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ (Set.univ : Set ℝ))
              (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
          rw [Set.disjoint_left]
          intro z hz1 hz2
          exact not_lt_of_ge hz1.1.2 hz2.1.1
        have hsub1 : Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ Set.univ ⊆ W :=
          Set.prod_mono (Set.Ioc_subset_Ioc_right (by exact_mod_cast hst_lt.le)) le_rfl
        have hsub2 : Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ ⊆ W :=
          Set.prod_mono (Set.Ioc_subset_Ioc_left (NNReal.coe_nonneg s)) le_rfl
        have hadd := setIntegral_union hdisj (measurableSet_Ioc.prod MeasurableSet.univ)
          (MeasureTheory.IntegrableOn.mono_set hpow_int_W hsub1)
          (MeasureTheory.IntegrableOn.mono_set hpow_int_W hsub2)
        rw [hunion] at hadd
        dsimp only [M, Δs]
        rw [show (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ) = W from rfl, hadd]
        ring
      have hΔs_int : Integrable Δs P := by
        have hsub_ae : (fun ω => M t ω - M s ω) =ᵐ[P] Δs := by
          filter_upwards [hMt_ae] with ω hω; linarith
        exact ((hM_int t).sub (hM_int s)).congr hsub_ae
      have hEq_E : ∫ ω in E, M t ω ∂P = ∫ ω in E, (M s ω + Δs ω) ∂P :=
        integral_congr_ae (ae_restrict_of_ae hMt_ae)
      rw [hEq_E, integral_add (hM_int s).integrableOn hΔs_int.integrableOn, hΔs_int_E, add_zero]
