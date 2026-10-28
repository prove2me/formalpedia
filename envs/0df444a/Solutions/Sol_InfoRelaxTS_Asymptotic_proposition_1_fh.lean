-- Prove2me | solution 1 for InfoRelaxTS.Asymptotic.proposition_1_fh
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:33:05.54693+00:00
-- url     : https://prove2.me/submissions/0fb4f731-7f50-4227-82cc-05cac2d84ce6

import Mathlib
import Definitions.Def_InfoRelaxTS_Asymptotic_Setting
import Theorems.Thm_InfoRelaxTS_Asymptotic_proposition_5
import Theorems.Thm_InfoRelaxTS_Asymptotic_display_109

open MeasureTheory ProbabilityTheory Filter Topology
open InfoRelaxTS InfoRelaxTS.Asymptotic

namespace IRS3

variable {K : ℕ} {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]

lemma measurable_iid (κ : Kernel Θ ℝ) [IsMarkovKernel κ] :
    Measurable (fun θ => Measure.infinitePi (fun _ : ℕ => κ θ)) := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet)
      (fun _ => by simp)) ?_
  rintro S ⟨s, t, ht, rfl⟩
  have ht' : ∀ i ∈ s, MeasurableSet (t i) := fun i _ => ht i (Set.mem_univ i)
  have : (fun θ => Measure.infinitePi (fun _ : ℕ => κ θ) ((s : Set ℕ).pi t)) =
      fun θ => ∏ i ∈ s, κ θ (t i) := funext fun θ => Measure.infinitePi_pi _ ht'
  rw [this]
  exact Finset.measurable_prod _ (fun i _ => κ.measurable_coe (ht i (Set.mem_univ i)))

noncomputable def iidK (κ : Kernel Θ ℝ) [IsMarkovKernel κ] : Kernel Θ (ℕ → ℝ) :=
  ⟨fun θ => Measure.infinitePi (fun _ => κ θ), measurable_iid κ⟩

instance (κ : Kernel Θ ℝ) [IsMarkovKernel κ] : IsMarkovKernel (iidK κ) :=
  ⟨fun θ => by simp only [iidK, Kernel.coe_mk]; infer_instance⟩

noncomputable def armK (κ : Kernel Θ ℝ) [IsMarkovKernel κ] : Kernel Θ (Θ × (ℕ → ℝ)) :=
  Kernel.deterministic id measurable_id ×ₖ iidK κ

instance (κ : Kernel Θ ℝ) [IsMarkovKernel κ] : IsMarkovKernel (armK κ) := by
  unfold armK; infer_instance

lemma armK_apply (κ : Kernel Θ ℝ) [IsMarkovKernel κ] (θ : Θ) :
    armK κ θ = (Measure.dirac θ).prod (Measure.infinitePi fun _ : ℕ => κ θ) := by
  rw [armK, Kernel.prod_apply, Kernel.deterministic_apply]; rfl

lemma I_eq (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)] (P : Fin K → Kernel Y Θ)
    (y : Fin K → Y) : I R P y = Measure.pi fun a => armK (R a) ∘ₘ P a (y a) := by
  unfold I
  congr 1
  funext a
  congr 1
  funext θ
  rw [armK_apply]

instance (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)] (P : Fin K → Kernel Y Θ)
    [∀ a, IsMarkovKernel (P a)] (y : Fin K → Y) : IsProbabilityMeasure (I R P y) := by
  rw [I_eq]
  haveI : ∀ a, IsProbabilityMeasure (armK (R a) ∘ₘ P a (y a)) := fun a => inferInstance
  infer_instance

lemma map_theta (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)] (P : Fin K → Kernel Y Θ)
    [∀ a, IsMarkovKernel (P a)] (y : Fin K → Y) :
    (I R P y).map (fun ω a => (ω a).1) = priorLaw P y := by
  rw [I_eq]
  haveI : ∀ a, SigmaFinite ((armK (R a) ∘ₘ P a (y a)).map Prod.fst) := fun a => by
    haveI := Measure.isProbabilityMeasure_map (μ := armK (R a) ∘ₘ P a (y a)) measurable_fst.aemeasurable
    infer_instance
  rw [Measure.pi_map_pi (fun a => measurable_fst.aemeasurable)]
  unfold priorLaw
  congr 1
  funext a
  rw [Measure.map_comp _ _ measurable_fst]
  have : (armK (R a)).map Prod.fst = Kernel.deterministic id measurable_id := by
    rw [← Kernel.fst_eq, armK, Kernel.fst_prod]
  rw [this, Measure.deterministic_comp_eq_map, Measure.map_id]

lemma measurable_mu (R : Fin K → Kernel Θ ℝ) (a : Fin K) : Measurable (Monotone.mu R a) :=
  (StronglyMeasurable.integral_kernel (κ := R a) (f := fun r : ℝ => r)
    stronglyMeasurable_id).measurable

lemma measurable_muBar (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ) (a : Fin K) :
    Measurable (Monotone.muBar R P a) :=
  (StronglyMeasurable.integral_kernel (κ := P a) (f := Monotone.mu R a)
    (measurable_mu R a).stronglyMeasurable).measurable

lemma measurable_yseq (U : Fin K → Y → ℝ → Y) (hU : ∀ a, Measurable (Function.uncurry (U a)))
    (y : Fin K → Y) (a : Fin K) (n : ℕ) :
    Measurable (fun ω : Outcome K Θ => yseq U y a ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have h2 : Measurable (fun ω : Outcome K Θ => (ω a).2 n) :=
      (measurable_pi_apply n).comp (measurable_snd.comp (measurable_pi_apply a))
    exact (hU a).comp (ih.prodMk h2)

lemma measurable_muHat (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ)
    (U : Fin K → Y → ℝ → Y) (hU : ∀ a, Measurable (Function.uncurry (U a)))
    (y : Fin K → Y) (a : Fin K) (n : ℕ) :
    Measurable (fun ω : Outcome K Θ => muHat R P U y a n ω) :=
  (measurable_muBar R P a).comp (measurable_yseq U hU y a n)

lemma measurable_theta : Measurable (fun (ω : Outcome K Θ) (a : Fin K) => (ω a).1) :=
  measurable_pi_lambda _ fun a => measurable_fst.comp (measurable_pi_apply a)

/-- Eventual almost-sure equality of discrete random variables implies convergence of the
point masses of their laws. -/
lemma law_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → Fin K) (Z : Ω → Fin K) (hX : ∀ T, Measurable (X T)) (hZ : Measurable Z)
    (h : ∀ᵐ ω ∂μ, ∀ᶠ T in atTop, X T ω = Z ω) (a : Fin K) :
    Tendsto (fun T => (μ.map (X T) {a}).toReal) atTop (𝓝 (μ.map Z {a}).toReal) := by
  have hs : ∀ T, MeasurableSet (X T ⁻¹' {a}) := fun T => hX T (measurableSet_singleton a)
  have hsZ : MeasurableSet (Z ⁻¹' {a}) := hZ (measurableSet_singleton a)
  simp_rw [Measure.map_apply (hX _) (measurableSet_singleton a),
    Measure.map_apply hZ (measurableSet_singleton a)]
  have e1 : ∀ T, (μ (X T ⁻¹' {a})).toReal = ∫ ω, (X T ⁻¹' {a}).indicator 1 ω ∂μ := fun T => by
    rw [integral_indicator_one (hs T)]; rfl
  have e2 : (μ (Z ⁻¹' {a})).toReal = ∫ ω, (Z ⁻¹' {a}).indicator 1 ω ∂μ := by
    rw [integral_indicator_one hsZ]; rfl
  simp_rw [e1, e2]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1)
    ?_ ?_
  · exact fun T => (stronglyMeasurable_one.indicator (hs T)).aestronglyMeasurable
  · intro T
    refine Eventually.of_forall fun ω => ?_
    by_cases hω : ω ∈ X T ⁻¹' {a} <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  · filter_upwards [h] with ω hω
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [hω] with T hT
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, hT]

/-- Any argmax selector applied to a vector with distinct entries picks the same arm. -/
lemma sel_eq_of_injective (s1 s2 : (Fin K → ℝ) → Fin K) (h1 : Gap.IsArgmaxSel s1)
    (h2 : Gap.IsArgmaxSel s2) (v : Fin K → ℝ) (hv : Function.Injective v) : s1 v = s2 v :=
  hv (le_antisymm (h2 v (s1 v)) (h1 v (s2 v)))

end IRS3

open IRS3 in
theorem solution {K : ℕ} [NeZero K] {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hU : ∀ a, Measurable (Function.uncurry (U a)))
    (hconj : IsConjugate R P U) (hint : RewardsIntegrable R P) (y : Fin K → Y)
    (hdistinct : ∀ i j : Fin K, i ≠ j → ∀ᵐ θ ∂(priorLaw P y), Monotone.mu R i (θ i) ≠ Monotone.mu R j (θ j))
    (selTS : (Fin K → ℝ) → Fin K) (hselTS : Gap.IsArgmaxSel selTS) (hselTSm : Measurable selTS)
    (selFH : (Fin K → ℝ) → Fin K) (hselFH : Gap.IsArgmaxSel selFH) (hselFHm : Measurable selFH) :
    ∀ a : Fin K, Tendsto (fun T : ℕ => (fhLaw R P U selFH T y {a}).toReal) atTop
      (𝓝 (tsLaw R P selTS y {a}).toReal) := by
  intro a
  have hconv : ∀ᵐ ω ∂(I R P y), ∀ b, Tendsto (fun n => muHat R P U y b n ω) atTop
      (𝓝 (Monotone.mu R b (ω b).1)) := by
    rw [ae_all_iff]; intro b
    filter_upwards [proposition_5 R P U hU hconj y b (hint b (y b))] with ω hω using hω.1
  have hinj : ∀ᵐ ω ∂(I R P y), Function.Injective (fun b => Monotone.mu R b (ω b).1) := by
    have h1 : ∀ᵐ θ ∂(priorLaw P y), ∀ i j : Fin K, i ≠ j →
        Monotone.mu R i (θ i) ≠ Monotone.mu R j (θ j) := by
      rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
      by_cases hij : i = j
      · exact Eventually.of_forall fun _ h => absurd hij h
      · filter_upwards [hdistinct i j hij] with θ h _ using h
    rw [← map_theta R P y] at h1
    have h2 := ae_of_ae_map (measurable_theta (K := K) (Θ := Θ)).aemeasurable h1
    filter_upwards [h2] with ω hω i j hij
    by_contra hne
    exact hω i j hne hij
  have hthm : ∀ b, Measurable (fun ω : Outcome K Θ => Monotone.mu R b (ω b).1) := fun b =>
    (measurable_mu R b).comp (measurable_fst.comp (measurable_pi_apply b))
  set Z : Outcome K Θ → Fin K := fun ω => selTS (fun b => Monotone.mu R b (ω b).1) with hZ
  have hZm : Measurable Z := hselTSm.comp (measurable_pi_lambda _ hthm)
  have hts : tsLaw R P selTS y = (I R P y).map Z := by
    unfold tsLaw
    rw [← map_theta R P y, Measure.map_map _ measurable_theta]
    · rfl
    · exact hselTSm.comp (measurable_pi_lambda _ fun b =>
        (measurable_mu R b).comp (measurable_pi_apply b))
  rw [hts]
  · -- IRS.FH
    refine law_tendsto (I R P y)
      (fun T ω => selFH fun b => muHat R P U y b (T - 1) ω) Z ?_ hZm ?_ a
    · intro T
      exact hselFHm.comp (measurable_pi_lambda _ fun b => measurable_muHat R P U hU y b (T - 1))
    · filter_upwards [hconv, hinj] with ω hω hiω
      have h109 := display_109 selFH hselFH (fun n b => muHat R P U y b n ω)
        (fun b => Monotone.mu R b (ω b).1) hiω hω
      filter_upwards [(tendsto_sub_atTop_nat 1).eventually h109] with T hT
      rw [hT]
      exact sel_eq_of_injective selFH selTS hselFH hselTS _ hiω
