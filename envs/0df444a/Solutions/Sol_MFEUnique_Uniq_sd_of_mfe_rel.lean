-- Prove2me | solution 1 for MFEUnique.Uniq.sd_of_mfe_rel
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:22:09.068993+00:00
-- url     : https://prove2.me/submissions/3c25e609-2571-4df3-8354-c13d530194b6

import Mathlib
import Definitions.Def_MFEUnique_Uniq_Equilibrium

open MeasureTheory StochIneqPO.Comparison Filter Topology
open MFEUnique.Uniq

namespace MFEUAux

variable {X : Type*} [MetricSpace X] [CompactSpace X] [PartialOrder X]
    [OrderClosedTopology X] [MeasurableSpace X] [BorelSpace X]

lemma isClosed_upperClosure_of_isClosed {F : Set X} (hF : IsClosed F) :
    IsClosed (upperClosure F : Set X) := by
  have hK : IsCompact ({p : X × X | p.1 ≤ p.2} ∩ F ×ˢ Set.univ) :=
    (hF.prod isClosed_univ).isCompact.inter_left (isClosed_le continuous_fst continuous_snd)
  have : (upperClosure F : Set X) = Prod.snd '' ({p : X × X | p.1 ≤ p.2} ∩ F ×ˢ Set.univ) := by
    ext y
    rw [SetLike.mem_coe, mem_upperClosure]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨(x, y), ⟨hxy, hx, Set.mem_univ _⟩, rfl⟩
    · rintro ⟨⟨x, y'⟩, ⟨hxy, hx, -⟩, rfl⟩
      exact ⟨x, hx, hxy⟩
  rw [this]
  exact (hK.image continuous_snd).isClosed

lemma le_of_null_upper {ν μ : Measure X} [IsFiniteMeasure ν]
    (h : ∀ F : Set X, IsClosed F → IsUpperSet F → ν F ≤ μ F)
    {U : Set X} (hU : IsUpperSet U) (hUm : NullMeasurableSet U ν) : ν U ≤ μ U := by
  obtain ⟨t, htU, htm, hae⟩ := hUm.exists_measurable_subset_ae_eq
  rw [← measure_congr hae]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨F, hFt, hFc, hlt⟩ := htm.exists_isClosed_lt_add (μ := ν) (measure_ne_top ν t)
    (ε := (ε : ENNReal)) (by exact_mod_cast hε.ne')
  have hsub : (upperClosure F : Set X) ⊆ U := fun y hy => by
    obtain ⟨x, hx, hxy⟩ := mem_upperClosure.1 hy
    exact hU hxy (htU (hFt hx))
  calc ν t ≤ ν F + ε := hlt.le
    _ ≤ ν (upperClosure F) + ε := by gcongr; exact subset_upperClosure
    _ ≤ μ (upperClosure F) + ε :=
        add_le_add (h _ (isClosed_upperClosure_of_isClosed hFc) (upperClosure F).upper) le_rfl
    _ ≤ μ U + ε := by gcongr

lemma lintegral_le_of_upper {ν μ : Measure X} [IsFiniteMeasure ν]
    (h : ∀ F : Set X, IsClosed F → IsUpperSet F → ν F ≤ μ F)
    {f : X → ℝ} (hf : Monotone f) (hf0 : ∀ x, 0 ≤ f x)
    (hν : AEMeasurable f ν) (hμ : AEMeasurable f μ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  rw [lintegral_eq_lintegral_meas_lt ν (Filter.Eventually.of_forall hf0) hν,
    lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall hf0) hμ]
  refine lintegral_mono fun t => ?_
  refine le_of_null_upper h ?_ (nullMeasurableSet_lt aemeasurable_const hν)
  intro a b hab ha
  exact lt_of_lt_of_le ha (hf hab)

lemma stochLE_of_upper {ν μ : Measure X} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (h : ∀ F : Set X, IsClosed F → IsUpperSet F → ν F ≤ μ F) : StochLE ν μ := by
  intro f hfm hfmono ⟨C, hC⟩
  set D := |C|
  have hfD : ∀ x, 0 ≤ f x + D := fun x => by
    have := hC x
    have := le_abs_self C
    have := neg_abs_le (f x)
    linarith
  have hint : ∀ (m : Measure X) [IsFiniteMeasure m], Integrable f m := fun m _ =>
    Integrable.of_bound hfm.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  have key : ∫ x, (f x + D) ∂ν ≤ ∫ x, (f x + D) ∂μ := by
    have h1 := ofReal_integral_eq_lintegral_ofReal ((hint ν).add (integrable_const D))
      (Filter.Eventually.of_forall hfD)
    have h2 := ofReal_integral_eq_lintegral_ofReal ((hint μ).add (integrable_const D))
      (Filter.Eventually.of_forall hfD)
    have h3 := lintegral_le_of_upper h (f := fun x => f x + D)
      (fun a b hab => by simpa using hfmono hab) hfD
      (hfm.add measurable_const).aemeasurable (hfm.add measurable_const).aemeasurable
    simp only [Pi.add_apply] at h1 h2
    rw [← h1, ← h2] at h3
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hfD)).1 h3
  rw [integral_add (hint ν) (integrable_const D), integral_add (hint μ) (integrable_const D)]
    at key
  simp only [integral_const, probReal_univ, one_smul] at key
  linarith

lemma upper_le_of_stochLE {ν μ : Measure X} [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (h : StochLE ν μ) {B : Set X} (hB : MeasurableSet B) (hU : IsUpperSet B) : ν B ≤ μ B := by
  have hmono : Monotone (B.indicator (1 : X → ℝ)) := by
    intro a b hab
    by_cases ha : a ∈ B
    · simp [Set.indicator_of_mem ha, Set.indicator_of_mem (hU hab ha)]
    · rw [Set.indicator_of_notMem ha]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) b
  have := h (B.indicator 1) (measurable_one.indicator hB) hmono
    ⟨1, fun x => by by_cases hx : x ∈ B <;> simp [hx]⟩
  rw [integral_indicator_one hB, integral_indicator_one hB] at this
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 this

variable {q J : ℕ} {A : Set (EuclideanSpace ℝ (Fin q))} {E : Type*} [TopologicalSpace E]

lemma Qk_apply (G : Game X q J E A) (g : X → ProbabilityMeasure X → A) (x : X)
    (s : ProbabilityMeasure X) {B : Set X} (hB : MeasurableSet B) :
    G.Qk g x s B = ∑ j, ENNReal.ofReal (G.p j) * B.indicator 1 (G.w x (g x s) s (G.ζ j)) := by
  simp only [Game.Qk, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hB]

lemma Qk_prob (G : Game X q J E A) (hG : G.Standing) (g : X → ProbabilityMeasure X → A)
    (x : X) (s : ProbabilityMeasure X) : IsProbabilityMeasure (G.Qk g x s) := by
  constructor
  rw [Qk_apply G g x s MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hG.p_nonneg j), hG.p_sum, ENNReal.ofReal_one]

lemma Mop_apply (G : Game X q J E A) (g : X → ProbabilityMeasure X → A)
    (s : ProbabilityMeasure X) (θ : Measure X)
    (hT : ∀ j, ENNReal.ofReal (G.p j) ≠ 0 →
      AEMeasurable (fun x => G.w x (g x s) s (G.ζ j)) θ)
    {B : Set X} (hB : MeasurableSet B) :
    G.Mop g s θ B = ∫⁻ x, G.Qk g x s B ∂θ := by
  simp_rw [Qk_apply G g _ s hB]
  rw [lintegral_finsetSum']
  · simp only [Game.Mop, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : ENNReal.ofReal (G.p j) = 0
    · simp [hj]
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_map' (measurable_one.indicator hB).aemeasurable (hT j hj),
        lintegral_indicator_one hB]
  · intro j _
    by_cases hj : ENNReal.ofReal (G.p j) = 0
    · simp only [hj, zero_mul]; exact aemeasurable_const
    · exact ((measurable_one.indicator hB).comp_aemeasurable (hT j hj)).const_mul _

lemma Qk_aemeas (G : Game X q J E A) (g : X → ProbabilityMeasure X → A)
    (s : ProbabilityMeasure X) (θ : Measure X)
    (hT : ∀ j, ENNReal.ofReal (G.p j) ≠ 0 →
      AEMeasurable (fun x => G.w x (g x s) s (G.ζ j)) θ)
    {B : Set X} (hB : MeasurableSet B) :
    AEMeasurable (fun x => G.Qk g x s B) θ := by
  simp_rw [Qk_apply G g _ s hB]
  refine Finset.aemeasurable_fun_sum _ fun j _ => ?_
  by_cases hj : ENNReal.ofReal (G.p j) = 0
  · simp only [hj, zero_mul]; exact aemeasurable_const
  · exact ((measurable_one.indicator hB).comp_aemeasurable (hT j hj)).const_mul _

lemma map_univ_le {Y : Type*} [MeasurableSpace Y] (f : X → Y) (θ : Measure X) :
    θ.map f Set.univ ≤ θ Set.univ := by
  by_cases hf : AEMeasurable f θ
  · rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ, Set.preimage_univ]
  · rw [Measure.map_of_not_aemeasurable hf]; simp

lemma Mop_univ_le (G : Game X q J E A) (hG : G.Standing) (g : X → ProbabilityMeasure X → A)
    (s : ProbabilityMeasure X) (θ : Measure X) : G.Mop g s θ Set.univ ≤ θ Set.univ := by
  simp only [Game.Mop, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  calc ∑ j, ENNReal.ofReal (G.p j) * θ.map (fun x => G.w x (g x s) s (G.ζ j)) Set.univ
      ≤ ∑ j, ENNReal.ofReal (G.p j) * θ Set.univ :=
        Finset.sum_le_sum fun j _ => mul_le_mul_right (map_univ_le _ _) _
    _ = θ Set.univ := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hG.p_nonneg j),
          hG.p_sum, ENNReal.ofReal_one, one_mul]

lemma aemeas_of_erg (G : Game X q J E A) (hG : G.Standing) (g : X → ProbabilityMeasure X → A)
    (herg : G.IsXErgodic g) (s : ProbabilityMeasure X) (θ : Measure X)
    [hθ : IsProbabilityMeasure θ] (j : Fin J) (hj : ENNReal.ofReal (G.p j) ≠ 0) :
    AEMeasurable (fun x => G.w x (g x s) s (G.ζ j)) θ := by
  by_contra hna
  obtain ⟨μ, -, -, hconv⟩ := herg s
  have hc := hconv ⟨θ, hθ⟩ (BoundedContinuousFunction.const X 1)
  simp only [BoundedContinuousFunction.const_apply, integral_const, smul_eq_mul, mul_one,
    probReal_univ] at hc
  set M := G.Mop g s
  have hp : 0 < G.p j := by
    by_contra h; push Not at h; exact hj (ENNReal.ofReal_eq_zero.2 h)
  -- mass of `M θ` plus `p j` is at most one
  have h1 : M θ Set.univ + ENNReal.ofReal (G.p j) ≤ 1 := by
    simp only [M, Game.Mop, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Measure.map_of_not_aemeasurable hna]
    simp only [Measure.coe_zero, Pi.zero_apply, mul_zero, zero_add]
    calc (∑ i ∈ Finset.univ.erase j,
          ENNReal.ofReal (G.p i) * θ.map (fun x => G.w x (g x s) s (G.ζ i)) Set.univ)
          + ENNReal.ofReal (G.p j)
        ≤ (∑ i ∈ Finset.univ.erase j, ENNReal.ofReal (G.p i)) + ENNReal.ofReal (G.p j) := by
          gcongr with i
          calc ENNReal.ofReal (G.p i) * θ.map (fun x => G.w x (g x s) s (G.ζ i)) Set.univ
              ≤ ENNReal.ofReal (G.p i) * θ Set.univ := mul_le_mul_right (map_univ_le _ _) _
            _ = ENNReal.ofReal (G.p i) := by rw [measure_univ, mul_one]
      _ = 1 := by
          rw [Finset.sum_erase_add _ _ (Finset.mem_univ j),
            ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hG.p_nonneg j), hG.p_sum,
            ENNReal.ofReal_one]
  have hiter : ∀ (n : ℕ) (ν : Measure X), (M^[n] ν) Set.univ ≤ ν Set.univ := by
    intro n
    induction n with
    | zero => intro ν; exact le_rfl
    | succ n ih =>
      intro ν
      rw [Function.iterate_succ_apply']
      exact (Mop_univ_le G hG g s _).trans (ih ν)
  have hbound : ∀ n : ℕ, ((M^[n + 1] θ) Set.univ).toReal ≤ 1 - G.p j := by
    intro n
    rw [Function.iterate_succ_apply]
    have hle := hiter n (M θ)
    have hfin : M θ Set.univ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
      (le_trans le_self_add h1)
    have h2 : (M θ Set.univ).toReal + G.p j ≤ 1 := by
      have := ENNReal.toReal_mono ENNReal.one_ne_top h1
      rwa [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le,
        ENNReal.toReal_one] at this
    have := ENNReal.toReal_mono hfin hle
    linarith
  have hc' := (tendsto_add_atTop_iff_nat 1).2 hc
  have := le_of_tendsto' hc' (fun n => by
    simpa [Measure.real] using hbound n)
  linarith

lemma Mop_prob (G : Game X q J E A) (hG : G.Standing) (g : X → ProbabilityMeasure X → A)
    (herg : G.IsXErgodic g) (s : ProbabilityMeasure X) (θ : Measure X)
    [IsProbabilityMeasure θ] : IsProbabilityMeasure (G.Mop g s θ) := by
  constructor
  rw [Mop_apply G g s θ (fun j hj => aemeas_of_erg G hG g herg s θ j hj) MeasurableSet.univ]
  simp_rw [(Qk_prob G hG g _ s).measure_univ]
  simp

end MFEUAux

open MFEUAux

theorem solution {X : Type*} [MetricSpace X] [CompactSpace X] [PartialOrder X]
    [OrderClosedTopology X] [MeasurableSpace X] [BorelSpace X]
    {q J : ℕ} {A : Set (EuclideanSpace ℝ (Fin q))} {E : Type*} [TopologicalSpace E]
    (G : Game X q J E A) (hG : G.Standing)
    (R : ProbabilityMeasure X → ProbabilityMeasure X → Prop)
    (g : X → ProbabilityMeasure X → A) (hg : ∀ x s, g x s ∈ G.Gopt x s)
    (hsingle : ∀ x s a, a ∈ G.Gopt x s → a = g x s)
    (herg : G.IsXErgodic g) (hinc : G.IncreasingInX g) (hdec : G.DecreasingInS R g) :
    ∀ (g₁ g₂ : X → ProbabilityMeasure X → A) (s₁ s₂ : ProbabilityMeasure X),
      G.IsMFE g₁ s₁ → G.IsMFE g₂ s₂ → R s₂ s₁ → StochLE (s₂ : Measure X) (s₁ : Measure X) := by
  intro g₁ g₂ s₁ s₂ h1 h2 hs
  have hfix : ∀ (g' : X → ProbabilityMeasure X → A) (s : ProbabilityMeasure X),
      G.IsMFE g' s → G.Mop g s (s : Measure X) = s := by
    intro g' s h
    have heq : ∀ x, g' x s = g x s := fun x => hsingle x s _ (h.1 x)
    have : G.Mop g' s = G.Mop g s := by
      funext θ; simp only [Game.Mop, heq]
    rw [← this]; exact h.2
  haveI : ∀ x s, IsProbabilityMeasure (G.Qk g x s) := fun x s => Qk_prob G hG g x s
  have hT : ∀ (s : ProbabilityMeasure X) (θ : Measure X) [IsProbabilityMeasure θ] (j : Fin J),
      ENNReal.ofReal (G.p j) ≠ 0 → AEMeasurable (fun x => G.w x (g x s) s (G.ζ j)) θ :=
    fun s θ _ j hj => aemeas_of_erg G hG g herg s θ j hj
  set M := G.Mop g s₁ with hM
  have hprob : ∀ n, IsProbabilityMeasure (M^[n] (s₂ : Measure X)) := by
    intro n
    induction n with
    | zero => simpa using (inferInstance : IsProbabilityMeasure (s₂ : Measure X))
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact Mop_prob G hG g herg s₁ _
  -- one step of the comparison
  have step : ∀ (θ : Measure X) [IsProbabilityMeasure θ],
      (∀ F : Set X, IsClosed F → IsUpperSet F → (s₂ : Measure X) F ≤ θ F) →
      ∀ B : Set X, MeasurableSet B → IsUpperSet B → (s₂ : Measure X) B ≤ M θ B := by
    intro θ _ hθ B hB hU
    have hfix2 := hfix g₂ s₂ h2
    calc (s₂ : Measure X) B = G.Mop g s₂ (s₂ : Measure X) B := by rw [hfix2]
      _ = ∫⁻ x, G.Qk g x s₂ B ∂(s₂ : Measure X) :=
          Mop_apply G g s₂ _ (fun j hj => hT s₂ _ j hj) hB
      _ ≤ ∫⁻ x, G.Qk g x s₁ B ∂(s₂ : Measure X) :=
          lintegral_mono fun x => upper_le_of_stochLE (hdec x s₁ s₂ hs) hB hU
      _ = ∫⁻ x, ENNReal.ofReal ((G.Qk g x s₁ B).toReal) ∂(s₂ : Measure X) := by
          simp_rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ∫⁻ x, ENNReal.ofReal ((G.Qk g x s₁ B).toReal) ∂θ := by
          refine lintegral_le_of_upper hθ ?_ (fun x => ENNReal.toReal_nonneg) ?_ ?_
          · intro x₁ x₂ hx
            exact ENNReal.toReal_mono (measure_ne_top _ _)
              (upper_le_of_stochLE (hinc s₁ x₁ x₂ hx) hB hU)
          · exact (Qk_aemeas G g s₁ _ (fun j hj => hT s₁ _ j hj) hB).ennreal_toReal
          · exact (Qk_aemeas G g s₁ _ (fun j hj => hT s₁ _ j hj) hB).ennreal_toReal
      _ = ∫⁻ x, G.Qk g x s₁ B ∂θ := by
          simp_rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ = M θ B := (Mop_apply G g s₁ θ (fun j hj => hT s₁ θ j hj) hB).symm
  have hup : ∀ n, ∀ B : Set X, MeasurableSet B → IsUpperSet B →
      (s₂ : Measure X) B ≤ (M^[n] (s₂ : Measure X)) B := by
    intro n
    induction n with
    | zero => intro B _ _; exact le_rfl
    | succ n ih =>
      intro B hB hU
      rw [Function.iterate_succ_apply']
      haveI := hprob n
      exact step _ (fun F hF hFU => ih F hF.measurableSet hFU) B hB hU
  obtain ⟨μ, -, hμuniq, hconv⟩ := herg s₁
  have hμ : s₁ = μ := hμuniq s₁ (hfix g₁ s₁ h1)
  let μs : ℕ → ProbabilityMeasure X := fun n => ⟨M^[n] (s₂ : Measure X), hprob n⟩
  have htend : Tendsto μs atTop (𝓝 s₁) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    rw [hμ]
    exact hconv s₂ f
  have hclosed : ∀ F : Set X, IsClosed F → IsUpperSet F → (s₂ : Measure X) F ≤ (s₁ : Measure X) F := by
    intro F hF hU
    calc (s₂ : Measure X) F ≤ limsup (fun n => (μs n : Measure X) F) atTop :=
          le_limsup_of_frequently_le
            (Frequently.of_forall fun n => hup n F hF.measurableSet hU)
      _ ≤ (s₁ : Measure X) F := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto htend hF
  exact stochLE_of_upper hclosed
