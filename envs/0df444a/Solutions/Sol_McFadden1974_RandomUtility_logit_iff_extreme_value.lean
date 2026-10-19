-- Prove2me | solution 1 for McFadden1974.RandomUtility.logit_iff_extreme_value
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T05:35:16.846044+00:00
-- url     : https://prove2.me/submissions/2aff654f-070c-4212-b546-bc5e819e7424

-- Licensed under Apache 2.0. Full exact theorem: McFadden full Gumbel/logit characterization, Lemmas 1 and 2.
import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model

open MeasureTheory ProbabilityTheory Finset


open MeasureTheory ProbabilityTheory Filter Topology Finset
open McFadden1974.RandomUtility

namespace McFaddenProof

lemma logit_den_pos {J : ℕ} (V : Fin J → ℝ) (i : Fin J) :
    0 < ∑ j, Real.exp (V j) := by
  exact Finset.sum_pos' (fun j _ => (Real.exp_pos (V j)).le)
    ⟨i, Finset.mem_univ i, Real.exp_pos (V i)⟩

lemma continuous_logitProb {J : ℕ} (i : Fin J) :
    Continuous (fun V : Fin J → ℝ => logitProb V i) := by
  unfold logitProb
  exact (Real.continuous_exp.comp (continuous_apply i)).div
    (continuous_finsetSum _ fun j _ => Real.continuous_exp.comp (continuous_apply j))
    (fun V => ne_of_gt (logit_den_pos V i))

lemma logitOn_injective_utilities (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {X : Type*} (u : X → ℝ) (hu : Function.Surjective u) (h : IsLogitOn μ u)
    {J : ℕ} (V : Fin J → ℝ) (hV : Function.Injective V) (i : Fin J) :
    selProb μ V i = logitProb V i := by
  choose x hx using fun j => hu (V j)
  have hi : Function.Injective x := by
    intro j k he
    apply hV
    rw [← hx j, ← hx k, he]
  simpa only [hx] using h J x hi i

lemma isLogitOn_of_isLogit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : IsLogit μ) {X : Type*} (u : X → ℝ) : IsLogitOn μ u := by
  intro J x _ i
  exact h J (fun j => u (x j)) i

lemma measurableSet_winner {J : ℕ} (V : Fin J → ℝ) (i : Fin J) :
    MeasurableSet {e : Fin J → ℝ | ∀ j, j ≠ i → V j + e j < V i + e i} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt (measurable_const.add (measurable_pi_apply j))
      (measurable_const.add (measurable_pi_apply i))

lemma selProb_eq_integral_indicator (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {J : ℕ} (V : Fin J → ℝ) (i : Fin J) :
    selProb μ V i = ∫ e, ({e : Fin J → ℝ | ∀ j, j ≠ i →
      V j + e j < V i + e i}).indicator (fun _ => (1 : ℝ)) e
      ∂Measure.pi (fun _ : Fin J => μ) := by
  rw [integral_indicator (measurableSet_winner V i)]
  simp [selProb, Measure.real]

end McFaddenProof


open MeasureTheory ProbabilityTheory Filter Topology Set

namespace McFaddenProof

lemma punctured_right_nonzero (x : ℝ) : ∀ᶠ d in 𝓝[>] x, d ≠ 0 := by
  by_cases hx : x = 0
  · subst x
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact ne_of_gt hd
  · exact (eventually_ne_nhds hx).filter_mono nhdsWithin_le_nhds

lemma punctured_left_nonzero (x : ℝ) : ∀ᶠ d in 𝓝[<] x, d ≠ 0 := by
  by_cases hx : x = 0
  · subst x
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact ne_of_lt hd
  · exact (eventually_ne_nhds hx).filter_mono nhdsWithin_le_nhds

lemma strict_distribution_identification (ν : Measure ℝ) [IsFiniteMeasure ν]
    (H : ℝ → ℝ) (hH : Continuous H)
    (h : ∀ d, d ≠ 0 → ν.real (Iio d) = H d) (x : ℝ) :
    ν.real (Iio x) = H x ∧ ν.real (Iic x) = H x := by
  have hlo : H x ≤ ν.real (Iio x) := by
    apply le_of_tendsto (hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto H (𝓝[<] x) (𝓝 (H x)))
    filter_upwards [self_mem_nhdsWithin, punctured_left_nonzero x] with d hd hn
    rw [← h d hn]
    exact measureReal_mono (Iio_subset_Iio hd.le)
  have hhi : ν.real (Iic x) ≤ H x := by
    apply ge_of_tendsto (hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto H (𝓝[>] x) (𝓝 (H x)))
    filter_upwards [self_mem_nhdsWithin, punctured_right_nonzero x] with d hd hn
    rw [← h d hn]
    exact measureReal_mono (Iic_subset_Iio.mpr hd)
  have hm : ν.real (Iio x) ≤ ν.real (Iic x) := measureReal_mono Iio_subset_Iic_self
  exact ⟨le_antisymm (hm.trans hhi) hlo, le_antisymm hhi (hlo.trans hm)⟩

lemma noAtoms_of_strict_distribution (ν : Measure ℝ) [IsFiniteMeasure ν]
    (H : ℝ → ℝ) (hH : Continuous H)
    (h : ∀ d, d ≠ 0 → ν.real (Iio d) = H d) : NullSingletonClass ν := by
  constructor
  intro x
  have he := strict_distribution_identification ν H hH h x
  have hu : ν.real (Iio x ∪ {x}) = ν.real (Iio x) + ν.real {x} :=
    measureReal_union (by simp) (measurableSet_singleton x)
  rw [Iio_union_right] at hu
  have hz : ν.real {x} = 0 := by linarith [he.1, he.2]
  exact (measureReal_eq_zero_iff (μ := ν)).mp hz

lemma continuous_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    Continuous (cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have h := ((integrable_const (μ := μ) (1 : ℝ)).integrableOn (s := Iic (x+1))).continuousOn_Iic_primitive_Iic
  have ht := h.continuousAt (Iic_mem_nhds (show x < x+1 by linarith))
  have he : (fun b => ∫ y in Iic b, (1 : ℝ) ∂μ) = cdf μ := by
    funext b
    simp [cdf_eq_real]
  rwa [he] at ht

end McFaddenProof


open MeasureTheory ProbabilityTheory Filter Topology Set
open McFadden1974.RandomUtility

namespace McFaddenProof

noncomputable def differenceLaw (μ : Measure ℝ) : Measure ℝ :=
  (μ.prod μ).map (fun z : ℝ × ℝ => z.2-z.1)

lemma measurable_difference : Measurable (fun z : ℝ × ℝ => z.2-z.1) :=
  measurable_snd.sub measurable_fst

instance differenceLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (differenceLaw μ) :=
  Measure.isProbabilityMeasure_map measurable_difference.aemeasurable

lemma binary_selProb (μ : Measure ℝ) [IsProbabilityMeasure μ] (d : ℝ) :
    selProb μ ![d,0] 0 = (differenceLaw μ).real (Iio d) := by
  have hm := measurePreserving_piFinTwo (fun _ : Fin 2 => μ)
  have he : {e : Fin 2 → ℝ | ∀ j, j ≠ 0 → ![d,0] j + e j < ![d,0] 0 + e 0} =
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) ⁻¹'
        {z : ℝ × ℝ | z.2-z.1 < d} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, MeasurableEquiv.piFinTwo_apply]
    constructor
    · intro h
      have hh := h 1 (by decide)
      simp at hh
      linarith
    · intro h j hj
      fin_cases j
      · exact (hj rfl).elim
      · simp
        linarith
  unfold selProb
  have hs : MeasurableSet {z : ℝ × ℝ | z.2-z.1 < d} :=
    measurableSet_lt measurable_difference measurable_const
  rw [he, hm.measure_preimage hs.nullMeasurableSet]
  rw [Measure.real, differenceLaw, Measure.map_apply measurable_difference measurableSet_Iio]
  rfl

lemma differenceLaw_logistic (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {X : Type*} (u : X → ℝ) (hu : Function.Surjective u) (h : IsLogitOn μ u)
    {d : ℝ} (hd : d ≠ 0) :
    (differenceLaw μ).real (Iio d) = Real.exp d / (Real.exp d + 1) := by
  have hi : Function.Injective (![d,0] : Fin 2 → ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hh := logitOn_injective_utilities μ u hu h ![d,0] hi 0
  rw [binary_selProb] at hh
  simpa [logitProb, Fin.sum_univ_two] using hh

lemma atomless_of_logitOn (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {X : Type*} (u : X → ℝ) (hu : Function.Surjective u) (h : IsLogitOn μ u) :
    NullSingletonClass μ := by
  have hc : Continuous (fun d : ℝ => Real.exp d / (Real.exp d+1)) :=
    Real.continuous_exp.div (Real.continuous_exp.add continuous_const)
      (fun d => ne_of_gt (by positivity))
  let : NullSingletonClass (differenceLaw μ) :=
    noAtoms_of_strict_distribution _ _ hc (fun d hd => differenceLaw_logistic μ u hu h hd)
  constructor
  intro x
  have hz : (μ.prod μ) {z : ℝ × ℝ | z.2-z.1 = 0} = 0 := by
    have hh := measure_singleton (μ := differenceLaw μ) (0 : ℝ)
    rwa [differenceLaw, Measure.map_apply measurable_difference (measurableSet_singleton 0)] at hh
  have hm : (μ.prod μ) ({x} ×ˢ {x}) = 0 := measure_mono_null (by
    rintro ⟨a,b⟩ ⟨ha,hb⟩
    simp_all) hz
  rw [Measure.prod_prod] at hm
  exact (mul_eq_zero.mp hm).elim id id

end McFaddenProof


open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open McFadden1974.RandomUtility

namespace McFaddenProof

lemma prod_erase_succAbove {n : ℕ} (i : Fin (n+1)) (f : Fin (n+1) → ℝ) :
    ∏ j ∈ Finset.univ.erase i, f j = ∏ j : Fin n, f (i.succAbove j) := by
  rw [Fin.univ_succAbove n i]
  simp

lemma selProb_eq_integral_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {J : ℕ} (V : Fin J → ℝ) (i : Fin J) :
    selProb μ V i = ∫ e, ∏ j ∈ Finset.univ.erase i,
      cdf μ (e + V i - V j) ∂μ := by
  cases J with
  | zero => exact Fin.elim0 i
  | succ n =>
    let s : Set (ℝ × (Fin n → ℝ)) := {z | ∀ j, V (i.succAbove j)+z.2 j < V i+z.1}
    have hs : MeasurableSet s := by
      dsimp [s]
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => measurableSet_lt
        (measurable_const.add ((measurable_pi_apply j).comp measurable_snd))
        (measurable_const.add measurable_fst)
    have he : {e : Fin (n+1) → ℝ | ∀ j, j ≠ i → V j+e j < V i+e i} =
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i) ⁻¹' s := by
      ext e
      change (∀ j, j ≠ i → V j+e j < V i+e i) ↔
        ∀ j, V (i.succAbove j)+e (i.succAbove j) < V i+e i
      rw [i.forall_iff_succAbove]
      simp
    have hsection (e : ℝ) : Prod.mk e ⁻¹' s =
        Set.univ.pi (fun j : Fin n => Iio (e+V i-V (i.succAbove j))) := by
      ext z
      simp only [s, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iio]
      constructor <;> intro h j <;> specialize h j <;> linarith
    unfold selProb
    rw [he, (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).measure_preimage hs.nullMeasurableSet,
      Measure.prod_apply hs, ← integral_toReal]
    · apply integral_congr_ae
      filter_upwards [] with e
      rw [hsection e, Measure.pi_pi, ENNReal.toReal_prod, prod_erase_succAbove]
      apply Finset.prod_congr rfl
      intro j _
      rw [measure_congr (Iio_ae_eq_Iic (μ := μ))]
      exact (cdf_eq_real μ _).symm
    · exact (measurable_measure_prodMk_left hs).aemeasurable
    · exact Filter.Eventually.of_forall fun e => measure_lt_top _ _

end McFaddenProof


open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open McFadden1974.RandomUtility

namespace McFaddenProof

lemma continuous_selProb (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {J : ℕ} (i : Fin J) :
    Continuous (fun V : Fin J → ℝ => selProb μ V i) := by
  simp_rw [selProb_eq_integral_cdf]
  apply continuous_iff_continuousAt.mpr
  intro V
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
  · exact Filter.Eventually.of_forall fun W =>
      (continuous_finsetProd _ fun j _ => (continuous_cdf μ).comp
        ((continuous_id.add continuous_const).sub continuous_const)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun W => Filter.Eventually.of_forall fun e => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun j _ => cdf_nonneg μ _)]
      exact Finset.prod_le_one (fun j _ => cdf_nonneg μ _) (fun j _ => cdf_le_one μ _)
  · exact integrable_const 1
  · exact Filter.Eventually.of_forall fun e =>
      (continuous_finsetProd _ fun j _ => (continuous_cdf μ).comp
        ((continuous_const.add (continuous_apply i)).sub (continuous_apply j))).continuousAt

lemma eventually_injective_perturb {J : ℕ} (V : Fin J → ℝ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, Function.Injective (fun j => V j+t*(j:ℝ)) := by
  have hp : ∀ i j : Fin J, ∀ᶠ t : ℝ in 𝓝[>] 0,
      V i+t*(i:ℝ) = V j+t*(j:ℝ) → i=j := by
    intro i j
    by_cases hij : i=j
    · exact Filter.Eventually.of_forall fun _ _ => hij
    by_cases hv : V i = V j
    · filter_upwards [self_mem_nhdsWithin] with t ht he
      have ht' : t ≠ 0 := ne_of_gt ht
      have hc : (i:ℝ) = (j:ℝ) := by
        apply mul_left_cancel₀ ht'
        linarith
      apply Fin.ext
      exact_mod_cast hc
    · have hc : Continuous (fun t : ℝ => (V i+t*(i:ℝ))-(V j+t*(j:ℝ))) := by fun_prop
      have hn : (V i+(0:ℝ)*(i:ℝ))-(V j+0*(j:ℝ)) ≠ 0 := by simpa using sub_ne_zero.mpr hv
      filter_upwards [(hc.continuousAt.eventually_ne hn).filter_mono nhdsWithin_le_nhds] with t ht he
      exact (ht (sub_eq_zero.mpr he)).elim
  simpa only [Filter.eventually_all, Function.Injective] using hp

lemma isLogit_of_isLogitOn (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {X : Type*} (u : X → ℝ) (hu : Function.Surjective u) (h : IsLogitOn μ u) :
    IsLogit μ := by
  let : NullSingletonClass μ := atomless_of_logitOn μ u hu h
  intro J V i
  have hc : Continuous (fun t : ℝ => fun j : Fin J => V j+t*(j:ℝ)) := by fun_prop
  have hs := ((continuous_selProb μ i).comp hc).continuousAt.tendsto.mono_left
    (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hl := ((continuous_logitProb i).comp hc).continuousAt.tendsto.mono_left
    (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have he : (fun t : ℝ => selProb μ (fun j => V j+t*(j:ℝ)) i) =ᶠ[𝓝[>] 0]
      (fun t => logitProb (fun j => V j+t*(j:ℝ)) i) := by
    filter_upwards [eventually_injective_perturb V] with t ht
    exact logitOn_injective_utilities μ u hu h _ ht i
  simpa using tendsto_nhds_unique (hs.congr' he) hl

end McFaddenProof


open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace McFaddenProof
open McFadden1974.RandomUtility

lemma boundedVariation_sub {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun x => f x - g x) s := by
  apply ne_of_lt
  apply lt_of_le_of_lt (b := eVariationOn f s + eVariationOn g s)
  · apply iSup_le
    rintro ⟨n,u,hu,hs⟩
    calc
      _ ≤ ∑ i ∈ Finset.range n,
          (edist (f (u (i+1))) (f (u i)) + edist (g (u (i+1))) (g (u i))) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add (dist_nonneg) (dist_nonneg)]
        exact ENNReal.ofReal_mono (dist_sub_sub_le _ _ _ _)
      _ = (∑ i ∈ Finset.range n, edist (f (u (i+1))) (f (u i))) +
          ∑ i ∈ Finset.range n, edist (g (u (i+1))) (g (u i)) := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (eVariationOn.sum_le hu hs) (eVariationOn.sum_le hu hs)
  · exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hf, lt_top_iff_ne_top.mpr hg⟩

lemma integrable_cdf_comp (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {g : ℝ → ℝ} (hg : Measurable g) : Integrable (fun x => cdf μ (g x)) μ := by
  apply (integrable_const (1 : ℝ)).mono' ((monotone_cdf μ).measurable.comp hg).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, Function.comp_def, abs_of_nonneg (cdf_nonneg μ _)] using cdf_le_one μ (g x)

lemma integrable_cdf_pow (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℝ) (K : ℕ) : Integrable (fun x => cdf μ (x+a)^K) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (((monotone_cdf μ).measurable.comp (measurable_id.add_const a)).pow_const K).aestronglyMeasurable
  filter_upwards [] with x
  change ‖cdf μ (x+a)^K‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (cdf_nonneg μ _) _)]
  exact pow_le_one₀ (cdf_nonneg μ _) (cdf_le_one μ _)

lemma cdf_functional_equation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hTC : TranslationComplete μ) (hcont : Continuous (cdf μ))
    (K : ℕ) (hK : 0 < K)
    (hint : ∀ a : ℝ, (∫ e, cdf μ (e+a-Real.log K) ∂μ) =
      ∫ e, cdf μ (e+a)^K ∂μ) :
    ∀ v : ℝ, cdf μ (v-Real.log K) = cdf μ v ^ K := by
  let h : ℝ → ℝ := fun t => cdf μ (t-Real.log K) - cdf μ t ^ K
  have hmono₁ : Monotone (fun t : ℝ => cdf μ (t-Real.log K)) :=
    (monotone_cdf μ).comp (fun _ _ hxy => sub_le_sub_right hxy _)
  have hmono₂ : Monotone (fun t : ℝ => cdf μ t ^ K) := by
    intro x y hxy
    exact pow_le_pow_left₀ (cdf_nonneg μ x) (monotone_cdf μ hxy) K
  have hv₁ : BoundedVariationOn (fun t : ℝ => cdf μ (t-Real.log K)) univ :=
    (hmono₁.monotoneOn univ).boundedVariationOn (C := 1) (fun t _ => by
      rw [abs_of_nonneg (cdf_nonneg μ _)]; exact cdf_le_one μ _)
  have hv₂ : BoundedVariationOn (fun t : ℝ => cdf μ t ^ K) univ :=
    (hmono₂.monotoneOn univ).boundedVariationOn (C := 1) (fun t _ => by
      rw [abs_of_nonneg (pow_nonneg (cdf_nonneg μ _) _)];
      exact pow_le_one₀ (cdf_nonneg μ _) (cdf_le_one μ _))
  have htop : Tendsto h atTop (𝓝 0) := by
    have h₁ := (tendsto_cdf_atTop μ).comp (by simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-Real.log K) tendsto_id)
    have h₂ := (tendsto_cdf_atTop μ).pow K
    simpa [h, sub_eq_add_neg] using h₁.sub h₂
  have hbot : Tendsto h atBot (𝓝 0) := by
    have h₁ := (tendsto_cdf_atBot μ).comp (by simpa only [sub_eq_add_neg] using tendsto_atBot_add_const_right atBot (-Real.log K) tendsto_id)
    have h₂ := (tendsto_cdf_atBot μ).pow K
    simpa [h, sub_eq_add_neg, zero_pow (Nat.ne_of_gt hK)] using h₁.sub h₂
  have hi : ∀ a : ℝ, ∫ e, h (e+a) ∂μ = 0 := by
    intro a
    dsimp [h]
    have hi₁ : Integrable (fun e => cdf μ (e+a-Real.log K)) μ :=
      integrable_cdf_comp μ (by fun_prop)
    rw [integral_sub hi₁ (integrable_cdf_pow μ a K), hint a, sub_self]
  have hae := hTC h (boundedVariation_sub hv₁ hv₂) htop hbot hi
  have hc : Continuous h := (hcont.comp (continuous_id.sub continuous_const)).sub (hcont.pow K)
  have he := MeasureTheory.Measure.eq_of_ae_eq hae hc continuous_const
  intro v
  have := congrFun he v
  exact sub_eq_zero.mp this

end McFaddenProof


open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace McFaddenProof
open McFadden1974.RandomUtility

lemma cdf_log_nat_ratio (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h0 : cdf μ 0 = Real.exp (-1))
    (heq : ∀ K : ℕ, 0 < K → ∀ v : ℝ, cdf μ (v-Real.log K) = cdf μ v ^ K)
    {K L : ℕ} (hK : 0 < K) (hL : 0 < L) :
    cdf μ (Real.log ((K : ℝ)/L)) = Real.exp (-(L : ℝ)/K) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hbase : cdf μ (-Real.log L) = Real.exp (-(L : ℝ)) := by
    have h := heq L hL 0
    simpa [h0, ← Real.exp_nat_mul] using h
  apply (pow_left_inj₀ (cdf_nonneg μ _) (Real.exp_pos _).le (Nat.ne_of_gt hK)).mp
  rw [← heq K hK, Real.log_div (ne_of_gt hKr) (ne_of_gt hLr)]
  have hid : Real.log (K : ℝ) - Real.log L - Real.log K = -Real.log L := by ring
  rw [hid, hbase, ← Real.exp_nat_mul]
  congr 1
  field_simp

lemma normalized_cdf_of_functional_equation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hcont : Continuous (cdf μ)) (h0 : cdf μ 0 = Real.exp (-1))
    (heq : ∀ K : ℕ, 0 < K → ∀ v : ℝ, cdf μ (v-Real.log K) = cdf μ v ^ K) :
    IsExtremeValue μ := by
  have hrat : ∀ q : ℚ, 0 < q → cdf μ (Real.log (q : ℝ)) = Real.exp (-1/(q : ℝ)) := by
    intro q hq
    have hnum : 0 < q.num := Rat.num_pos.mpr hq
    have habs : (q.num.natAbs : ℝ) = (q.num : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_pos (by exact_mod_cast hnum)]
    have hn : 0 < q.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hnum)
    have h := cdf_log_nat_ratio μ h0 heq hn q.pos
    have hqcast : (q : ℝ) = (q.num.natAbs : ℝ)/q.den := by rw [habs, Rat.cast_def]
    rw [← hqcast] at h
    convert h using 1
    rw [hqcast]
    field_simp
  intro v
  have hdense : Dense (Set.range (fun q : ℚ => (q : ℝ))) := Rat.denseRange_cast
  have hm : Real.exp v ∈ closure (Ioi (0 : ℝ) ∩ Set.range (fun q : ℚ => (q : ℝ))) :=
    hdense.open_subset_closure_inter isOpen_Ioi (Real.exp_pos v)
  obtain ⟨w,hw,ht⟩ := mem_closure_iff_seq_limit.mp hm
  have heach : ∀ n, cdf μ (Real.log (w n)) = Real.exp (-1 / w n) := by
    intro n
    obtain ⟨q,hq⟩ := (hw n).2
    change (q : ℝ) = w n at hq
    rw [← hq]
    have hp : (0 : ℝ) < (q : ℝ) := by rw [hq]; exact (hw n).1
    exact hrat q (by exact_mod_cast hp)
  have hleft : Tendsto (fun n => cdf μ (Real.log (w n))) atTop (𝓝 (cdf μ v)) := by
    have hlog := (Real.continuousAt_log (ne_of_gt (Real.exp_pos v))).tendsto.comp ht
    simpa only [Real.log_exp, Function.comp_def] using hcont.continuousAt.tendsto.comp hlog
  have hright : Tendsto (fun n => Real.exp (-1 / w n)) atTop
      (𝓝 (Real.exp (-Real.exp (-v)))) := by
    have hd := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 (-1))).div ht (ne_of_gt (Real.exp_pos v))
    have hh := Real.continuous_exp.continuousAt.tendsto.comp hd
    simpa [Real.exp_neg, neg_div, Function.comp_def, Pi.div_apply] using hh
  exact tendsto_nhds_unique hleft (hright.congr (fun n => (heach n).symm))

end McFaddenProof


open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped Topology
namespace McFaddenProof
open McFadden1974.RandomUtility

lemma prod_erase_zero {K : ℕ} (f : Fin (K+1) → ℝ) :
    (∏ j ∈ univ.erase (0 : Fin (K+1)), f j) = ∏ j : Fin K, f j.succ := by
  let g : Fin (K+1) → ℝ := Fin.cases 1 (fun j => f j.succ)
  calc
    _ = ∏ j ∈ univ.erase (0 : Fin (K+1)), g j := by
      apply prod_congr rfl
      intro j hj
      have hj0 := (mem_erase.mp hj).1
      cases j using Fin.cases with
      | zero => exact (hj0 rfl).elim
      | succ k => rfl
    _ = ∏ j, g j := Finset.prod_erase _ rfl
    _ = _ := by rw [Fin.prod_univ_succ]; simp [g]

lemma logit_cdf_integral_identity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hlogit : IsLogit μ)
    (hformula : ∀ {J : ℕ} (V : Fin J → ℝ) (i : Fin J),
      selProb μ V i = ∫ e, ∏ j ∈ univ.erase i, cdf μ (e + V i - V j) ∂μ)
    {K : ℕ} (hK : 0 < K) (a : ℝ) :
    (∫ e, cdf μ (e+a-Real.log K) ∂μ) = ∫ e, cdf μ (e+a)^K ∂μ := by
  let V : Fin (K+1) → ℝ := Fin.cases a (fun _ => 0)
  let W : Fin 2 → ℝ := Fin.cases a (fun _ => Real.log K)
  have hmany := (hformula V 0).symm.trans (hlogit (K+1) V 0)
  have htwo := (hformula W 0).symm.trans (hlogit 2 W 0)
  have hm : (∫ e, cdf μ (e+a)^K ∂μ) = Real.exp a / (Real.exp a + K) := by
    simpa [prod_erase_zero, V, logitProb, Fin.sum_univ_succ] using hmany
  have ht : (∫ e, cdf μ (e+a-Real.log K) ∂μ) =
      Real.exp a / (Real.exp a + K) := by
    have hKr : (0 : ℝ) < K := by exact_mod_cast hK
    simpa [prod_erase_zero, W, logitProb, Fin.sum_univ_succ, Real.exp_log hKr] using htwo
  exact ht.trans hm.symm

lemma extremeValue_of_full_logit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hlogit : IsLogit μ) (hcont : Continuous (cdf μ))
    (hTC : TranslationComplete μ) (h0 : cdf μ 0 = Real.exp (-1))
    (hformula : ∀ {J : ℕ} (V : Fin J → ℝ) (i : Fin J),
      selProb μ V i = ∫ e, ∏ j ∈ univ.erase i, cdf μ (e + V i - V j) ∂μ) :
    IsExtremeValue μ := by
  apply normalized_cdf_of_functional_equation μ hcont h0
  intro K hK
  exact cdf_functional_equation μ hTC hcont K hK
    (logit_cdf_integral_identity μ hlogit hformula hK)

end McFaddenProof


open MeasureTheory Filter Set
open scoped Topology
namespace McFaddenProof

lemma integrable_of_nonnegative_derivative {F f : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x, HasDerivAt F (f x) x) (hpos : ∀ x, 0 ≤ f x)
    (hbot : Tendsto F atBot (𝓝 a)) (htop : Tendsto F atTop (𝓝 b)) :
    Integrable f := by
  have hr : IntegrableOn f (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hd x) (fun x _ => hpos x) htop
  have hdneg : ∀ x, HasDerivAt (fun t => -F (-t)) (f (-x)) x := by
    intro x
    convert ((hd (-x)).comp x (hasDerivAt_neg' x)).neg using 1 <;> first | rfl | ring
  have hn : Tendsto (fun t => -F (-t)) atTop (𝓝 (-a)) :=
    (hbot.comp tendsto_neg_atTop_atBot).neg
  have hlneg : IntegrableOn (fun x => f (-x)) (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hdneg x) (fun x _ => hpos (-x)) hn
  have hl : IntegrableOn f (Iio (0 : ℝ)) := by
    apply ((Measure.measurePreserving_neg volume).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mp
    simpa [Function.comp_def] using hlneg
  have hl' : IntegrableOn f (Iic (0 : ℝ)) := (integrableOn_Iic_iff_integrableOn_Iio (by finiteness)).mpr hl
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hl'.union hr

lemma integral_of_nonnegative_derivative {F f : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x, HasDerivAt F (f x) x) (hpos : ∀ x, 0 ≤ f x)
    (hbot : Tendsto F atBot (𝓝 a)) (htop : Tendsto F atTop (𝓝 b)) :
    (∫ x, f x) = b-a :=
  integral_of_hasDerivAt_of_tendsto hd
    (integrable_of_nonnegative_derivative hd hpos hbot htop) hbot htop

end McFaddenProof


open MeasureTheory Filter Set
open scoped Topology
namespace McFaddenProof

noncomputable def gumbelCDF (C x : ℝ) : ℝ := Real.exp (-C * Real.exp (-x))
noncomputable def gumbelKernel (C x : ℝ) : ℝ := Real.exp (-x) * gumbelCDF C x

lemma gumbelKernel_pos (C x : ℝ) : 0 < gumbelKernel C x :=
  mul_pos (Real.exp_pos _) (Real.exp_pos _)

lemma hasDerivAt_gumbelCDF (C x : ℝ) :
    HasDerivAt (gumbelCDF C) (C * gumbelKernel C x) x := by
  have h := (((hasDerivAt_neg' x).exp).const_mul (-C)).exp
  unfold gumbelKernel gumbelCDF
  convert h using 1
  ring

lemma gumbelCDF_atTop (C : ℝ) : Tendsto (gumbelCDF C) atTop (𝓝 1) := by
  change Tendsto (fun x : ℝ => Real.exp (-C * Real.exp (-x))) atTop (𝓝 1)
  have he := Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  simpa [Function.comp_def] using
    Real.continuous_exp.continuousAt.tendsto.comp (he.const_mul (-C))

lemma gumbelCDF_atBot {C : ℝ} (hC : 0 < C) :
    Tendsto (gumbelCDF C) atBot (𝓝 0) := by
  change Tendsto (fun x : ℝ => Real.exp (-C * Real.exp (-x))) atBot (𝓝 0)
  have he := Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop
  have hm : Tendsto (fun x : ℝ => C * Real.exp (-x)) atBot atTop :=
    he.const_mul_atTop hC
  simpa [Function.comp_def, neg_mul] using Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hm)

lemma hasDerivAt_gumbelPrimitive {C : ℝ} (hC : 0 < C) (x : ℝ) :
    HasDerivAt (fun t => gumbelCDF C t / C) (gumbelKernel C x) x := by
  convert (hasDerivAt_gumbelCDF C x).div_const C using 1 <;>
    first | rfl | field_simp [ne_of_gt hC]

lemma integrable_gumbelKernel {C : ℝ} (hC : 0 < C) : Integrable (gumbelKernel C) := by
  apply integrable_of_nonnegative_derivative (hasDerivAt_gumbelPrimitive hC)
    (fun x => (gumbelKernel_pos C x).le)
  · simpa using (gumbelCDF_atBot hC).div_const C
  · exact (gumbelCDF_atTop C).div_const C

lemma integral_gumbelKernel {C : ℝ} (hC : 0 < C) :
    (∫ x, gumbelKernel C x) = 1/C := by
  have h := integral_of_nonnegative_derivative (hasDerivAt_gumbelPrimitive hC)
    (fun x => (gumbelKernel_pos C x).le)
    ((gumbelCDF_atBot hC).div_const C) ((gumbelCDF_atTop C).div_const C)
  simpa using h

lemma integral_Iic_gumbelKernel (x : ℝ) :
    (∫ t in Iic x, gumbelKernel 1 t) = gumbelCDF 1 x := by
  have h := integral_Iic_of_hasDerivAt_of_tendsto'
    (fun t (_ : t ∈ Iic x) => hasDerivAt_gumbelPrimitive (C := 1) zero_lt_one t)
    (integrable_gumbelKernel (C := 1) zero_lt_one).integrableOn
    ((gumbelCDF_atBot (C := 1) zero_lt_one).div_const 1)
  simpa using h

end McFaddenProof


open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace McFaddenProof
open McFadden1974.RandomUtility

lemma continuous_gumbelKernel (C : ℝ) : Continuous (gumbelKernel C) := by
  unfold gumbelKernel gumbelCDF
  fun_prop

noncomputable def gumbelMeasure : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (gumbelKernel 1 x))

instance : IsProbabilityMeasure gumbelMeasure where
  measure_univ := by
    rw [gumbelMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_gumbelKernel zero_lt_one)
        (Filter.Eventually.of_forall (fun x => (gumbelKernel_pos 1 x).le)),
      integral_gumbelKernel zero_lt_one]
    simp

lemma cdf_gumbelMeasure (x : ℝ) : cdf gumbelMeasure x = gumbelCDF 1 x := by
  rw [cdf_eq_real, gumbelMeasure, measureReal_def,
    withDensity_apply _ measurableSet_Iic]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => (gumbelKernel_pos 1 x).le))
    (continuous_gumbelKernel 1).aestronglyMeasurable]
  exact integral_Iic_gumbelKernel x

lemma measure_eq_gumbel (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hext : IsExtremeValue μ) : μ = gumbelMeasure := by
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_gumbelMeasure, hext x]
  simp [gumbelCDF]

lemma integral_eq_gumbel_density (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hext : IsExtremeValue μ) (f : ℝ → ℝ) :
    (∫ x, f x ∂μ) = ∫ x, gumbelKernel 1 x * f x := by
  rw [measure_eq_gumbel μ hext, gumbelMeasure,
    integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (gumbelKernel_pos 1 _).le, smul_eq_mul]
  · exact (continuous_gumbelKernel 1).measurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

end McFaddenProof


open MeasureTheory ProbabilityTheory Finset
namespace McFaddenProof
open McFadden1974.RandomUtility

lemma gumbel_product_identity {J : ℕ} (V : Fin J → ℝ) (i : Fin J) (e : ℝ) :
    gumbelKernel 1 e * (∏ j ∈ univ.erase i, Real.exp (-Real.exp (-(e + V i - V j)))) =
    gumbelKernel (∑ j, Real.exp (V j - V i)) e := by
  have hs (j : Fin J) : Real.exp (-(e + V i - V j)) =
      Real.exp (-e) * Real.exp (V j - V i) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hs]
  unfold gumbelKernel gumbelCDF
  simp only [neg_mul, one_mul]
  rw [mul_assoc]
  congr 1
  calc
    Real.exp (-Real.exp (-e)) *
        (∏ j ∈ univ.erase i, Real.exp (-(Real.exp (-e) * Real.exp (V j - V i)))) =
        ∏ j, Real.exp (-(Real.exp (-e) * Real.exp (V j - V i))) := by
      have h := Finset.mul_prod_erase univ
        (fun j => Real.exp (-(Real.exp (-e) * Real.exp (V j - V i)))) (mem_univ i)
      simpa using h
    _ = Real.exp (∑ j, -(Real.exp (-e) * Real.exp (V j - V i))) :=
      (Real.exp_sum _ _).symm
    _ = Real.exp (-((∑ j, Real.exp (V j - V i)) * Real.exp (-e))) := by
      congr 1
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      ring

lemma relative_exp_sum_pos {J : ℕ} (V : Fin J → ℝ) (i : Fin J) :
    0 < ∑ j, Real.exp (V j - V i) := by
  exact Finset.sum_pos' (fun _ _ => (Real.exp_pos _).le) ⟨i, mem_univ i, Real.exp_pos _⟩

lemma reciprocal_relative_exp_sum {J : ℕ} (V : Fin J → ℝ) (i : Fin J) :
    1 / (∑ j, Real.exp (V j - V i)) = logitProb V i := by
  simp_rw [Real.exp_sub]
  rw [← Finset.sum_div]
  unfold logitProb
  field_simp

lemma full_logit_of_extremeValue (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hext : IsExtremeValue μ)
    (hformula : ∀ {J : ℕ} (V : Fin J → ℝ) (i : Fin J),
      selProb μ V i = ∫ e, ∏ j ∈ univ.erase i, cdf μ (e + V i - V j) ∂μ) :
    IsLogit μ := by
  intro J V i
  rw [hformula, integral_eq_gumbel_density μ hext]
  calc
    _ = ∫ e, gumbelKernel (∑ j, Real.exp (V j - V i)) e := by
      apply integral_congr_ae
      filter_upwards [] with e
      have hp : (∏ j ∈ univ.erase i, cdf μ (e + V i - V j)) =
          ∏ j ∈ univ.erase i, Real.exp (-Real.exp (-(e + V i - V j))) := by
        apply Finset.prod_congr rfl
        intro j _
        exact hext _
      rw [hp]
      exact gumbel_product_identity V i e
    _ = logitProb V i := by
      rw [integral_gumbelKernel (relative_exp_sum_pos V i), reciprocal_relative_exp_sum]

end McFaddenProof


open MeasureTheory ProbabilityTheory Finset

namespace McFadden1974.RandomUtility

/-- **Lemmas 1 and 2 — the extreme value law characterizes logit random utility models**
(McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in Frontiers in Econometrics
(1974), pp. 111–112, Lemmas 1 and 2; PDF pp. 7–8; p. 111: "The next lemma establishes that under
mild conditions the distribution (13) characterizes the population choice models whose selection
probabilities satisfy Equation (12).").

Fix an alternative universe `X` and a representative utility map `u : X → ℝ` that is onto.
Let the shocks be i.i.d. with a translation complete law `μ` normalized by `G(0) = e^{−1}`.
Then the selection probabilities on every finite subset of `X` satisfy (12) if and only if
`G(ε) = e^{−e^{−ε}}` for every `ε`.

Formalization Note: the direction ← is Lemma 1 (which needs neither translation completeness nor
the normalization); → is Lemma 2 with the normalization `G(0) = e^{−1}`. The hypotheses are
satisfiable: the law (13) is translation complete (footnote 5, p. 111) and has `G(0) = e^{−1}`.
The selection probabilities are those of (2), with strict inequalities and no density assumed;
`IsLogitOn` covers finite subsets of `X`, including repeated utility values. -/
theorem native_mcfadden_recovery (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {X : Type*} (u : X → ℝ) (hu : Function.Surjective u)
    (hTC : TranslationComplete μ) (h0 : cdf μ 0 = Real.exp (-1)) :
    IsLogitOn μ u ↔ IsExtremeValue μ := by
  constructor
  · intro h
    let : NullSingletonClass μ := McFaddenProof.atomless_of_logitOn μ u hu h
    exact McFaddenProof.extremeValue_of_full_logit μ
      (McFaddenProof.isLogit_of_isLogitOn μ u hu h) (McFaddenProof.continuous_cdf μ)
      hTC h0 (McFaddenProof.selProb_eq_integral_cdf μ)
  · intro h
    have hm := McFaddenProof.measure_eq_gumbel μ h
    have : NullSingletonClass μ := by
      rw [hm]
      unfold McFaddenProof.gumbelMeasure
      infer_instance
    exact McFaddenProof.isLogitOn_of_isLogit μ
      (McFaddenProof.full_logit_of_extremeValue μ h (McFaddenProof.selProb_eq_integral_cdf μ)) u

end McFadden1974.RandomUtility



open MeasureTheory ProbabilityTheory Finset

namespace McFadden1974.RandomUtility

/-- **Lemmas 1 and 2 — the extreme value law characterizes logit random utility models**
(McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in Frontiers in Econometrics
(1974), pp. 111–112, Lemmas 1 and 2; PDF pp. 7–8; p. 111: "The next lemma establishes that under
mild conditions the distribution (13) characterizes the population choice models whose selection
probabilities satisfy Equation (12).").

Fix an alternative universe `X` and a representative utility map `u : X → ℝ` that is onto.
Let the shocks be i.i.d. with a translation complete law `μ` normalized by `G(0) = e^{−1}`.
Then the selection probabilities on every finite subset of `X` satisfy (12) if and only if
`G(ε) = e^{−e^{−ε}}` for every `ε`.

Formalization Note: the direction ← is Lemma 1 (which needs neither translation completeness nor
the normalization); → is Lemma 2 with the normalization `G(0) = e^{−1}`. The hypotheses are
satisfiable: the law (13) is translation complete (footnote 5, p. 111) and has `G(0) = e^{−1}`.
The selection probabilities are those of (2), with strict inequalities and no density assumed;
`IsLogitOn` covers finite subsets of `X`, including repeated utility values. -/
theorem logit_iff_extreme_value (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {X : Type*} (u : X → ℝ) (hu : Function.Surjective u)
    (hTC : TranslationComplete μ) (h0 : cdf μ 0 = Real.exp (-1)) :
    IsLogitOn μ u ↔ IsExtremeValue μ := by
  exact McFadden1974.RandomUtility.native_mcfadden_recovery μ u hu hTC h0

end McFadden1974.RandomUtility

open McFadden1974.RandomUtility

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {X : Type*} (u : X → ℝ) (hu : Function.Surjective u)
    (hTC : TranslationComplete μ) (h0 : cdf μ 0 = Real.exp (-1)) :
    IsLogitOn μ u ↔ IsExtremeValue μ := McFadden1974.RandomUtility.logit_iff_extreme_value μ u hu hTC h0
