-- Prove2me | solution 1 for NumStochOpt.QuasiFejer.theorem_6_2_projection_method_converges
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T00:52:04.67699+00:00
-- url     : https://prove2.me/submissions/49bb6c20-5282-4ecb-9aca-c01ce29fa1ff

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod
import Definitions.Def_NumStochOpt_QuasiFejer_StochQuasiFejer

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NumStochOpt.QuasiFejer

def sf_filtration {Ω : Type*} [m : MeasurableSpace Ω] {n : ℕ}
    (z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (hz : ∀ s, Measurable (z s)) :
    Filtration ℕ m where
  seq := historySigma z
  mono' := by
    intro i j hij
    exact iSup_le fun k => iSup_le fun hki =>
      le_iSup_of_le k (le_iSup_of_le (hki.trans hij) le_rfl)
  le' := fun s => iSup_le fun k => iSup_le fun _ => (hz k).comap_le

lemma sf_history_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (s : ℕ) :
    @Measurable Ω _ (historySigma z s) _ (z s) :=
  Measurable.of_comap_le (le_iSup_of_le s (le_iSup_of_le le_rfl le_rfl))

lemma sf_distance_adapted {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (hz : ∀ s, Measurable (z s))
    (w : EuclideanSpace ℝ (Fin n)) :
    StronglyAdapted (sf_filtration z hz) (fun s ω => ‖w - z s ω‖ ^ 2) := by
  intro s
  change StronglyMeasurable[historySigma z s] (fun ω => ‖w - z s ω‖ ^ 2)
  letI : MeasurableSpace Ω := historySigma z s
  exact ((measurable_const.sub (sf_history_measurable z s)).norm.pow_const 2).stronglyMeasurable

lemma sf_distance_integrable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (z : Ω → EuclideanSpace ℝ (Fin n))
    (hz : MemLp z 2 μ) (w : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun ω => ‖w - z ω‖ ^ 2) μ := by
  have h : MemLp (fun ω => w - z ω) 2 μ := (memLp_const w).sub hz
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h

end NumStochOpt.QuasiFejer


open MeasureTheory Filter Topology
open scoped ENNReal

namespace NumStochOpt.QuasiFejer

lemma sf_nonneg_l1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hi : Integrable f μ) (hn : 0 ≤ᵐ[μ] f) :
    eLpNorm f 1 μ = ENNReal.ofReal (∫ ω, f ω ∂μ) := by
  rw [eLpNorm_one_eq_lintegral_enorm, ofReal_integral_eq_lintegral_ofReal hi hn]
  exact lintegral_congr_ae (hn.mono fun ω h => Real.enorm_eq_ofReal h)

lemma sf_error_summable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (r : ℕ → Ω → ℝ) (hrm : ∀ s, Measurable (r s)) (hrn : ∀ s, 0 ≤ᵐ[μ] r s)
    (hrsum : ∑' s, ∫⁻ ω, ENNReal.ofReal (r s ω) ∂μ < ⊤) :
    (∀ s, Integrable (r s) μ) ∧ Summable (fun s => ∫ ω, r s ω ∂μ) := by
  have hi (s) : Integrable (r s) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hrm s).aestronglyMeasurable (hrn s)).1
      (ne_of_lt ((ENNReal.le_tsum s).trans_lt hrsum))
  refine ⟨hi, ?_⟩
  have h := ENNReal.summable_toReal hrsum.ne
  simpa only [← integral_eq_lintegral_of_nonneg_ae (hrn _) (hrm _).aestronglyMeasurable] using h

lemma sf_quasi_supermartingale {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (v r : ℕ → Ω → ℝ) (hva : StronglyAdapted ℱ v)
    (hvi : ∀ s, Integrable (v s) μ) (hvn : ∀ s, 0 ≤ᵐ[μ] v s)
    (hrm : ∀ s, Measurable (r s)) (hrn : ∀ s, 0 ≤ᵐ[μ] r s)
    (hrsum : ∑' s, ∫⁻ ω, ENNReal.ofReal (r s ω) ∂μ < ⊤)
    (hstep : ∀ s, μ[v (s + 1) | ℱ s] ≤ᵐ[μ] fun ω => v s ω + r s ω) :
    (∀ᵐ ω ∂μ, ∃ l : ℝ, Tendsto (fun s => v s ω) atTop (𝓝 l)) ∧
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ s, ∫⁻ ω, ENNReal.ofReal (v s ω) ∂μ < C := by
  classical
  obtain ⟨hri, hris⟩ := sf_error_summable μ r hrm hrn hrsum
  let E : ℝ := ∑' s, ∫ ω, r s ω ∂μ
  have hE : 0 ≤ E := tsum_nonneg fun s => integral_nonneg_of_ae (hrn s)
  have hpartial (s) : (∑ k ∈ Finset.range s, ∫ ω, r k ω ∂μ) ≤ E :=
    hris.sum_le_tsum _ (fun _ _ => integral_nonneg_of_ae (hrn _))
  have hvbound (s) : (∫ ω, v s ω ∂μ) ≤
      (∫ ω, v 0 ω ∂μ) + ∑ k ∈ Finset.range s, ∫ ω, r k ω ∂μ := by
    induction s with
    | zero => simp
    | succ s ih =>
      have h := integral_mono_ae (integrable_condExp (μ := μ) (m := ℱ s))
        ((hvi s).add (hri s)) (hstep s)
      rw [integral_condExp (ℱ.le s)] at h
      simp only [Pi.add_apply] at h
      rw [integral_add (hvi s) (hri s)] at h
      rw [Finset.sum_range_succ]
      linarith
  let e : ℕ → Ω → ℝ := fun s => μ[r s | ℱ s]
  have hei (s) : Integrable (e s) μ := integrable_condExp
  have hea (s) : StronglyMeasurable[ℱ s] (e s) := stronglyMeasurable_condExp
  have hen (s) : 0 ≤ᵐ[μ] e s := condExp_nonneg (hrn s)
  have heint (s) : (∫ ω, e s ω ∂μ) = ∫ ω, r s ω ∂μ := integral_condExp (ℱ.le s)
  have hesum : ∑' s, eLpNorm (e s) 1 μ < ⊤ := by
    have heq (s) : eLpNorm (e s) 1 μ = ∫⁻ ω, ENNReal.ofReal (r s ω) ∂μ := by
      rw [sf_nonneg_l1 μ (e s) (hei s) (hen s), heint s,
        ofReal_integral_eq_lintegral_ofReal (hri s) (hrn s)]
    simpa only [heq] using hrsum
  have hes : ∀ᵐ ω ∂μ, Summable (fun s => e s ω) := by
    have h := summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl
      (fun s => (hei s).aestronglyMeasurable) hesum.ne
    exact h.mono fun ω h => h.of_norm
  let a : ℕ → Ω → ℝ := fun s ω => ∑ k ∈ Finset.range s, e k ω
  have hai (s) : Integrable (a s) μ := integrable_finsetSum _ fun _ _ => hei _
  have haa (s) : StronglyMeasurable[ℱ s] (a s) := by
    convert (Finset.stronglyMeasurable_sum (Finset.range s) fun k hk =>
      (hea k).mono (ℱ.mono (Nat.le_of_lt (Finset.mem_range.1 hk)))) using 1
    funext ω
    simp [a]
  have han (s) : 0 ≤ᵐ[μ] a s := by
    filter_upwards [ae_all_iff.2 hen] with ω h
    exact Finset.sum_nonneg fun k _ => h k
  have haint (s) : (∫ ω, a s ω ∂μ) ≤ E := by
    simpa only [a, integral_finsetSum _ (fun _ _ => hei _), heint] using hpartial s
  have hstep' (s) : μ[v (s + 1) | ℱ s] ≤ᵐ[μ] fun ω => v s ω + e s ω := by
    have h := condExp_mono (m := ℱ s) integrable_condExp ((hvi s).add (hri s)) (hstep s)
    filter_upwards [h, condExp_add (hvi s) (hri s) (ℱ s),
      condExp_condExp_of_le (f := v (s + 1)) le_rfl (ℱ.le s)] with ω h h1 h2
    rw [h2, h1, condExp_of_stronglyMeasurable (ℱ.le s) (hva s) (hvi s)] at h
    exact h
  let f : ℕ → Ω → ℝ := fun s ω => a s ω - v s ω
  have hfa : StronglyAdapted ℱ f := fun s => (haa s).sub (hva s)
  have hfi (s) : Integrable (f s) μ := (hai s).sub (hvi s)
  have hfm : Submartingale f ℱ μ := by
    apply submartingale_nat hfa hfi
    intro s
    have haeq : a (s + 1) = fun ω => a s ω + e s ω := by
      funext ω; exact Finset.sum_range_succ _ _
    have hasm : StronglyMeasurable[ℱ s] (a (s + 1)) := by
      rw [haeq]; exact (haa s).add (hea s)
    filter_upwards [hstep' s, condExp_sub (hai (s + 1)) (hvi (s + 1)) (ℱ s)] with ω h h1
    change a s ω - v s ω ≤ μ[a (s + 1) - v (s + 1) | ℱ s] ω
    rw [h1, condExp_of_stronglyMeasurable (ℱ.le s) hasm (hai (s + 1))]
    rw [haeq]; dsimp; linarith
  let R : ℝ≥0∞ := ENNReal.ofReal ((∫ ω, v 0 ω ∂μ) + 2 * E)
  have hfb (s) : eLpNorm (f s) 1 μ ≤ R := by
    calc
      eLpNorm (f s) 1 μ ≤ eLpNorm (a s) 1 μ + eLpNorm (v s) 1 μ :=
        eLpNorm_sub_le (hai s).aestronglyMeasurable (hvi s).aestronglyMeasurable le_rfl
      _ = ENNReal.ofReal ((∫ ω, a s ω ∂μ) + ∫ ω, v s ω ∂μ) := by
        rw [sf_nonneg_l1 μ (a s) (hai s) (han s), sf_nonneg_l1 μ (v s) (hvi s) (hvn s),
          ENNReal.ofReal_add (integral_nonneg_of_ae (han s)) (integral_nonneg_of_ae (hvn s))]
      _ ≤ R := ENNReal.ofReal_le_ofReal (by
        have h1 := hvbound s
        have h2 := haint s
        have h3 := hpartial s
        linarith)
  refine ⟨?_, ?_⟩
  · filter_upwards [hfm.exists_ae_tendsto_of_bdd hfb, hes] with ω hf he
    obtain ⟨l, hl⟩ := hf
    refine ⟨(∑' s, e s ω) - l, ?_⟩
    have ha := he.hasSum.tendsto_sum_nat
    convert ha.sub hl using 1
    ext s; dsimp [a, f]; ring
  · let C := ENNReal.ofReal ((∫ ω, v 0 ω ∂μ) + E + 1)
    refine ⟨C, ENNReal.ofReal_lt_top, fun s => ?_⟩
    rw [← ofReal_integral_eq_lintegral_ofReal (hvi s) (hvn s)]
    apply ENNReal.ofReal_lt_ofReal_iff'.2
    constructor
    · have h1 := hvbound s
      have h2 := hpartial s
      linarith
    · have h0 := integral_nonneg_of_ae (hvn 0)
      linarith

end NumStochOpt.QuasiFejer


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NumStochOpt.QuasiFejer

lemma sf_distance_result {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (Z : Set (EuclideanSpace ℝ (Fin n)))
    (hz : IsStochQuasiFejer μ z Z) (w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ Z) :
    (∀ᵐ ω ∂μ, ∃ l : ℝ, Tendsto (fun s => ‖w - z s ω‖ ^ 2) atTop (𝓝 l)) ∧
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ s, ∫⁻ ω, ENNReal.ofReal (‖w - z s ω‖ ^ 2) ∂μ < C := by
  obtain ⟨hzm, hzl, r, hrm, hrn, hrs, hrstep⟩ := hz
  exact sf_quasi_supermartingale μ (sf_filtration z hzm) _ r
    (sf_distance_adapted z hzm w)
    (fun s => sf_distance_integrable μ (z s) (hzl s) w)
    (fun _ => ae_of_all _ fun _ => sq_nonneg _) hrm hrn hrs (hrstep w hw)

lemma sf_norm_result {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (Z : Set (EuclideanSpace ℝ (Fin n)))
    (hz : IsStochQuasiFejer μ z Z) :
    ∀ w ∈ Z,
      (∀ᵐ ω ∂μ, ∃ l : ℝ, Tendsto (fun s => ‖w - z (s + 1) ω‖ ^ 2) atTop (𝓝 l)) ∧
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ s, ∫⁻ ω, ENNReal.ofReal (‖w - z s ω‖ ^ 2) ∂μ < C := by
  intro w hw
  obtain ⟨hc, hb⟩ := sf_distance_result μ z Z hz w hw
  refine ⟨hc.mono ?_, hb⟩
  rintro ω ⟨l, hl⟩
  exact ⟨l, hl.comp (tendsto_add_atTop_nat 1)⟩

end NumStochOpt.QuasiFejer


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NumStochOpt.QuasiFejer

lemma sf_cluster_from_distance {n : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n)) (l : ℝ)
    (h : Tendsto (fun s => ‖w - u s‖ ^ 2) atTop (𝓝 l)) :
    ∃ a, MapClusterPt a atTop u := by
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ h).exists_norm_le
  have hu (s) : u s ∈ Metric.closedBall w (B + 1) := by
    have hb := hB (‖w - u s‖ ^ 2) (Set.mem_range_self s)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hb
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    have := norm_nonneg (w - u s)
    nlinarith [sq_nonneg (‖w - u s‖ - 1)]
  obtain ⟨a, _, ha⟩ := (isCompact_closedBall w (B + 1)).exists_mapClusterPt_of_frequently (l := atTop) (f := u)
    (Frequently.of_forall hu)
  exact ⟨a, ha⟩

lemma sf_accumulation_result {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (Z : Set (EuclideanSpace ℝ (Fin n)))
    (hZ : Z.Nonempty) (hz : IsStochQuasiFejer μ z Z) :
    ∀ᵐ ω ∂μ, ∃ a : EuclideanSpace ℝ (Fin n), MapClusterPt a atTop (fun s => z s ω) := by
  obtain ⟨w, hw⟩ := hZ
  filter_upwards [(sf_distance_result μ z Z hz w hw).1] with ω h
  obtain ⟨l, hl⟩ := h
  exact sf_cluster_from_distance (fun s => z s ω) w l hl

lemma sf_cluster_equidistant {n : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin n))
    (w a b : EuclideanSpace ℝ (Fin n))
    (h : ∃ l : ℝ, Tendsto (fun s => ‖w - u s‖ ^ 2) atTop (𝓝 l))
    (ha : MapClusterPt a atTop u) (hb : MapClusterPt b atTop u) :
    ‖w - a‖ = ‖w - b‖ := by
  obtain ⟨l, hl⟩ := h
  obtain ⟨φ, hφ, haφ⟩ := ha.tendsto_subseq
  obtain ⟨ψ, hψ, hbψ⟩ := hb.tendsto_subseq
  have hla : ‖w - a‖ ^ 2 = l := tendsto_nhds_unique
    ((tendsto_const_nhds.sub haφ).norm.pow 2) (hl.comp hφ.tendsto_atTop)
  have hlb : ‖w - b‖ ^ 2 = l := tendsto_nhds_unique
    ((tendsto_const_nhds.sub hbψ).norm.pow 2) (hl.comp hψ.tendsto_atTop)
  nlinarith [norm_nonneg (w - a), norm_nonneg (w - b)]

lemma sf_dense_distances {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (Z : Set (EuclideanSpace ℝ (Fin n)))
    (hz : IsStochQuasiFejer μ z Z) :
    ∃ D : Set (EuclideanSpace ℝ (Fin n)), D ⊆ Z ∧ D.Countable ∧ Z ⊆ closure D ∧
      ∀ᵐ ω ∂μ, ∀ w ∈ D, ∃ l : ℝ,
        Tendsto (fun s => ‖w - z s ω‖ ^ 2) atTop (𝓝 l) := by
  obtain ⟨D, hDZ, hDc, hZD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace Z).exists_countable_dense_subset
  refine ⟨D, hDZ, hDc, hZD, (ae_ball_iff hDc).2 ?_⟩
  exact fun w hw => (sf_distance_result μ z Z hz w (hDZ hw)).1

lemma sf_equidistant_result {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (Z : Set (EuclideanSpace ℝ (Fin n)))
    (hz : IsStochQuasiFejer μ z Z) :
    ∀ᵐ ω ∂μ, ∀ a b : EuclideanSpace ℝ (Fin n),
      MapClusterPt a atTop (fun s => z s ω) → MapClusterPt b atTop (fun s => z s ω) →
      a ≠ b → a ∉ Z → b ∉ Z → ∀ w ∈ Z, ‖w - a‖ = ‖w - b‖ := by
  obtain ⟨D, _, _, hZD, hD⟩ := sf_dense_distances μ z Z hz
  filter_upwards [hD] with ω h
  intro a b ha hb _ _ _ w hw
  have hc : IsClosed {w : EuclideanSpace ℝ (Fin n) | ‖w - a‖ = ‖w - b‖} :=
    isClosed_eq (continuous_id.sub continuous_const).norm
      (continuous_id.sub continuous_const).norm
  have hd : D ⊆ {w : EuclideanSpace ℝ (Fin n) | ‖w - a‖ = ‖w - b‖} :=
    fun w hw => sf_cluster_equidistant (fun s => z s ω) w a b (h w hw) ha hb
  exact closure_minimal hd hc (hZD hw)

end NumStochOpt.QuasiFejer


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000

namespace NumStochOpt.QuasiFejer

lemma sf_projection_spec {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hc : Convex ℝ X) (hcl : IsClosed X) (hne : X.Nonempty)
    (y : EuclideanSpace ℝ (Fin n)) :
    projX X y ∈ X ∧ ∀ w ∈ X, ‖y - projX X y‖ ^ 2 ≤ ‖y - w‖ ^ 2 := by
  classical
  letI : Nonempty X := hne.to_subtype
  have hb : BddBelow (Set.range (fun q : X => ‖y - q‖)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact norm_nonneg _
  obtain ⟨p, hp, heq⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hc y
  have hnorm (w) (hw : w ∈ X) : ‖y - p‖ ≤ ‖y - w‖ := by
    rw [heq]
    exact ciInf_le hb ⟨w, hw⟩
  have hex : ∃ p ∈ X, ∀ w ∈ X, ‖y - p‖ ^ 2 ≤ ‖y - w‖ ^ 2 :=
    ⟨p, hp, fun w hw => pow_le_pow_left₀ (norm_nonneg _) (hnorm w hw) 2⟩
  simpa only [projX, dif_pos hex] using hex.choose_spec

lemma sf_projection_bound {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hc : Convex ℝ X) (hcl : IsClosed X) (hne : X.Nonempty)
    (y w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ X) :
    ‖w - projX X y‖ ^ 2 ≤ ‖w - y‖ ^ 2 := by
  letI : Nonempty X := hne.to_subtype
  have hbd : BddBelow (Set.range (fun q : X => ‖y - q‖)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact norm_nonneg _
  obtain ⟨hp, hmin⟩ := sf_projection_spec X hc hcl hne y
  have heq : ‖y - projX X y‖ = ⨅ q : X, ‖y - q‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro q
      have := hmin q q.property
      nlinarith [norm_nonneg (y - projX X y), norm_nonneg (y - q)]
    · exact ciInf_le hbd ⟨_, hp⟩
  have hi := (norm_eq_iInf_iff_real_inner_le_zero hc hp).1 heq w hw
  have he : (y - projX X y) - (w - projX X y) = y - w := by abel
  have hh := norm_sub_sq_real (y - projX X y) (w - projX X y)
  rw [he, norm_sub_rev y w] at hh
  nlinarith [sq_nonneg ‖y - projX X y‖]

lemma sf_projection_step_bound {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hc : Convex ℝ X) (hcl : IsClosed X) (hne : X.Nonempty)
    (w x ξ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hw : w ∈ X) :
    ‖w - projX X (x - ρ • ξ)‖ ^ 2 ≤
      ‖w - x‖ ^ 2 + 2 * ρ * ⟪ξ, w - x⟫_ℝ + ρ ^ 2 * ‖ξ‖ ^ 2 := by
  have h := sf_projection_bound X hc hcl hne (x - ρ • ξ) w hw
  have he : w - (x - ρ • ξ) = (w - x) + ρ • ξ := by abel
  rw [he, norm_add_sq_real, inner_smul_right, real_inner_comm ξ (w - x),
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  nlinarith

lemma sf_scaled_memLp {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ρ : Ω → ℝ) (ξ : Ω → EuclideanSpace ℝ (Fin n))
    (hm : AEStronglyMeasurable ρ μ) (hi : Integrable ξ μ)
    (hsq : Integrable (fun ω => ρ ω ^ 2 * ‖ξ ω‖ ^ 2) μ) :
    MemLp (fun ω => ρ ω • ξ ω) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (hm.smul hi.aestronglyMeasurable)).2
  simpa only [Pi.smul_apply', norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using hsq

lemma sf_inner_integrable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure Ω) (f g : Ω → E) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun ω => ⟪f ω, g ω⟫_ℝ) μ := by
  exact memLp_one_iff_integrable.1 ((innerSL ℝ).memLp_of_bilin 1 hf hg)

end NumStochOpt.QuasiFejer


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NumStochOpt.QuasiFejer

lemma sf_one_step_result {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → Ω → ℝ) (s : ℕ)
    (hXconv : Convex ℝ X) (hXclosed : IsClosed X) (hXne : X.Nonempty)
    (hx_meas : ∀ k, Measurable (x k)) (hx_L2 : MemLp (x s) 2 μ)
    (hξ_int : Integrable (ξ s) μ)
    (hρξ_int : Integrable (fun ω => ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) μ)
    (hρ_adapt : StronglyMeasurable[historySigma x s] (ρ s))
    (hrec : ∀ ω, x (s + 1) ω = projX X (x s ω - ρ s ω • ξ s ω))
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) :
    condExp (historySigma x s) μ (fun ω => ‖xstar - x (s + 1) ω‖ ^ 2)
      ≤ᵐ[μ] fun ω => ‖xstar - x s ω‖ ^ 2
          + 2 * ρ s ω * ⟪(condExp (historySigma x s) μ (ξ s)) ω, xstar - x s ω⟫_ℝ
          + (condExp (historySigma x s) μ (fun ω' => ρ s ω' ^ 2 * ‖ξ s ω'‖ ^ 2)) ω := by
  let ℱ := sf_filtration x hx_meas
  have hm : historySigma x s ≤ ‹MeasurableSpace Ω› := ℱ.le s
  have hρm : AEStronglyMeasurable (ρ s) μ := (hρ_adapt.mono hm).aestronglyMeasurable
  have hp := sf_scaled_memLp μ (ρ s) (ξ s) hρm hξ_int hρξ_int
  have hd : MemLp (fun ω => xstar - x s ω) 2 μ := (memLp_const xstar).sub hx_L2
  have hdi := sf_distance_integrable μ (x s) hx_L2 xstar
  have hcross := sf_inner_integrable μ (fun ω => ρ s ω • ξ s ω)
    (fun ω => xstar - x s ω) hp hd
  let g : Ω → EuclideanSpace ℝ (Fin n) := fun ω => (2 * ρ s ω) • (xstar - x s ω)
  have hga : StronglyMeasurable[historySigma x s] g := by
    letI : MeasurableSpace Ω := historySigma x s
    exact (stronglyMeasurable_const.mul hρ_adapt).smul
      (stronglyMeasurable_const.sub (sf_history_measurable x s).stronglyMeasurable)
  have hgξ : Integrable (fun ω => ⟪g ω, ξ s ω⟫_ℝ) μ := by
    convert hcross.const_mul 2 using 1
    funext ω
    simp only [g, real_inner_smul_left, real_inner_comm (ξ s ω) (xstar - x s ω)]
    ring
  have hnext : Integrable (fun ω => ‖xstar - x (s + 1) ω‖ ^ 2) μ := by
    have hy : MemLp (fun ω => x s ω - ρ s ω • ξ s ω) 2 μ := hx_L2.sub hp
    apply (sf_distance_integrable μ _ hy xstar).mono_nonneg
      (((measurable_const.sub (hx_meas (s + 1))).norm.pow_const 2).aestronglyMeasurable)
      (ae_of_all _ fun _ => sq_nonneg _)
    exact ae_of_all _ fun ω => by
      simp only [Pi.sub_apply]
      rw [hrec ω]
      exact sf_projection_bound X hXconv hXclosed hXne _ xstar hxstar
  have hupperi : Integrable (fun ω => ‖xstar - x s ω‖ ^ 2 + ⟪g ω, ξ s ω⟫_ℝ +
      ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) μ := (hdi.add hgξ).add hρξ_int
  have hpoint : (fun ω => ‖xstar - x (s + 1) ω‖ ^ 2) ≤ᵐ[μ]
      (fun ω => ‖xstar - x s ω‖ ^ 2 + ⟪g ω, ξ s ω⟫_ℝ +
        ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) := by
    apply ae_of_all
    intro ω
    dsimp only
    rw [hrec ω]
    simpa only [g, real_inner_smul_left, real_inner_comm (ξ s ω) (xstar - x s ω)] using
      sf_projection_step_bound X hXconv hXclosed hXne xstar (x s ω) (ξ s ω) (ρ s ω) hxstar
  have hmono := condExp_mono (m := historySigma x s) hnext hupperi hpoint
  have hpull := condExp_bilin_of_stronglyMeasurable_left (B := innerSL ℝ) hga hgξ hξ_int
  have had := sf_distance_adapted x hx_meas xstar s
  filter_upwards [hmono, hpull,
    condExp_add (hdi.add hgξ) hρξ_int (historySigma x s),
    condExp_add hdi hgξ (historySigma x s)] with ω h h1 h2 h3
  change μ[(fun ω => ‖xstar - x (s + 1) ω‖ ^ 2) | historySigma x s] ω ≤
    μ[((fun ω => ‖xstar - x s ω‖ ^ 2) + (fun ω => ⟪g ω, ξ s ω⟫_ℝ)) +
      (fun ω => ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) | historySigma x s] ω at h
  rw [h2] at h
  simp only [Pi.add_apply] at h
  rw [h3] at h
  simp only [Pi.add_apply] at h
  rw [condExp_of_stronglyMeasurable hm had hdi] at h
  change μ[(fun ω => ⟪g ω, ξ s ω⟫_ℝ) | historySigma x s] ω =
    ⟪g ω, μ[ξ s | historySigma x s] ω⟫_ℝ at h1
  rw [h1] at h
  simpa only [g, innerSL_apply_apply, real_inner_smul_left,
    real_inner_comm _ (xstar - x s ω)] using h

end NumStochOpt.QuasiFejer


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NumStochOpt.QuasiFejer

lemma sf_iterates_mem {Ω : Type*} {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) (hc : Convex ℝ X) (hcl : IsClosed X)
    (hne : X.Nonempty) (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → Ω → ℝ)
    (hx0 : ∀ ω, x 0 ω ∈ X)
    (hr : ∀ s ω, x (s + 1) ω = projX X (x s ω - ρ s ω • ξ s ω)) :
    ∀ s ω, x s ω ∈ X := by
  intro s ω
  cases s with
  | zero => exact hx0 ω
  | succ s => rw [hr]; exact (sf_projection_spec X hc hcl hne _).1

lemma sf_compact_memLp {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : IsCompact X) (x : Ω → EuclideanSpace ℝ (Fin n))
    (hm : Measurable x) (hx : ∀ ω, x ω ∈ X) : MemLp x 2 μ := by
  obtain ⟨B, hB⟩ := hX.isBounded.exists_norm_le
  exact MemLp.of_bound hm.aestronglyMeasurable B (ae_of_all _ fun ω => hB _ (hx ω))

noncomputable def sf_error {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (ρ γ : ℕ → Ω → ℝ) (s : ℕ) : Ω → ℝ :=
  μ[(fun ω => 2 * ρ s ω * |γ s ω| + ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) | historySigma x s]

lemma sf_error_data {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ γ : ℕ → Ω → ℝ)
    (hx : ∀ s, Measurable (x s)) (hξ : ∀ s, Integrable (ξ s) μ)
    (hρ : ∀ s, StronglyMeasurable[historySigma x s] (ρ s))
    (hγ : ∀ s, StronglyMeasurable[historySigma x s] (γ s))
    (hρn : ∀ᵐ ω ∂μ, ∀ s, 0 ≤ ρ s ω)
    (hsum : ∑' s, ∫⁻ ω, ENNReal.ofReal
      (ρ s ω * |γ s ω| + ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) ∂μ < ⊤) :
    (∀ s, Integrable (fun ω => ρ s ω * |γ s ω|) μ) ∧
    (∀ s, Integrable (fun ω => ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) μ) ∧
    (∀ s, Measurable (sf_error μ x ξ ρ γ s)) ∧
    (∀ s, 0 ≤ᵐ[μ] sf_error μ x ξ ρ γ s) ∧
    (∑' s, ∫⁻ ω, ENNReal.ofReal (sf_error μ x ξ ρ γ s ω) ∂μ) < ⊤ := by
  let ℱ := sf_filtration x hx
  let a : ℕ → Ω → ℝ := fun s ω => ρ s ω * |γ s ω|
  let b : ℕ → Ω → ℝ := fun s ω => ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2
  have ham (s) : AEStronglyMeasurable (a s) μ :=
    by
      convert (((hρ s).mono (ℱ.le s)).aestronglyMeasurable.mul
        (((hγ s).mono (ℱ.le s)).aestronglyMeasurable.norm)) using 1
      funext ω
      simp [a, Real.norm_eq_abs]
  have hbm (s) : AEStronglyMeasurable (b s) μ :=
    (((hρ s).mono (ℱ.le s)).aestronglyMeasurable.pow 2).mul
      ((hξ s).aestronglyMeasurable.norm.pow 2)
  have han (s) : 0 ≤ᵐ[μ] a s := hρn.mono fun ω h => mul_nonneg (h s) (abs_nonneg _)
  have hbn (s) : 0 ≤ᵐ[μ] b s := ae_of_all _ fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have habi (s) : Integrable (fun ω => a s ω + b s ω) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable ((ham s).add (hbm s)) ?_).1
      (ne_of_lt ((ENNReal.le_tsum s).trans_lt hsum))
    filter_upwards [han s, hbn s] with ω ha hb
    exact add_nonneg ha hb
  have hai (s) : Integrable (a s) μ := (habi s).mono_nonneg (ham s) (han s)
    ((hbn s).mono fun _ hb => le_add_of_nonneg_right hb)
  have hbi (s) : Integrable (b s) μ := (habi s).mono_nonneg (hbm s) (hbn s)
    ((han s).mono fun _ ha => le_add_of_nonneg_left ha)
  let e : ℕ → Ω → ℝ := fun s ω => 2 * a s ω + b s ω
  have hei (s) : Integrable (e s) μ := ((hai s).const_mul 2).add (hbi s)
  have hen (s) : 0 ≤ᵐ[μ] e s := by
    filter_upwards [han s, hbn s] with ω ha hb
    exact add_nonneg (mul_nonneg (by norm_num) ha) hb
  have her (s) : sf_error μ x ξ ρ γ s = μ[e s | historySigma x s] := by
    unfold sf_error
    congr 1
    funext ω
    dsimp [e, a, b]
    ring
  have hrn (s) : 0 ≤ᵐ[μ] sf_error μ x ξ ρ γ s := by
    rw [her]; exact condExp_nonneg (hen s)
  have heint (s) : (∫ ω, sf_error μ x ξ ρ γ s ω ∂μ) = ∫ ω, e s ω ∂μ := by
    rw [her s]
    have hm : historySigma x s ≤ ‹MeasurableSpace Ω› := ℱ.le s
    letI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
    exact integral_condExp hm
  refine ⟨hai, hbi, fun s => ?_, hrn, ?_⟩
  · rw [her]
    exact (stronglyMeasurable_condExp.mono (ℱ.le s)).measurable
  · have hle (s) : (∫⁻ ω, ENNReal.ofReal (sf_error μ x ξ ρ γ s ω) ∂μ) ≤
        2 * ∫⁻ ω, ENNReal.ofReal (a s ω + b s ω) ∂μ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (by rw [her]; exact integrable_condExp) (hrn s),
        heint s, ofReal_integral_eq_lintegral_ofReal (hei s) (hen s)]
      calc
        _ ≤ ∫⁻ ω, ENNReal.ofReal (2 * (a s ω + b s ω)) ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [hbn s] with ω hb
          apply ENNReal.ofReal_le_ofReal
          change 0 ≤ b s ω at hb
          dsimp only [e]
          linarith
        _ = _ := by
          simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          rw [lintegral_const_mul' (ENNReal.ofReal 2)
            (fun ω => ENNReal.ofReal (a s ω + b s ω)) ENNReal.ofReal_ne_top]
          norm_num
    calc
      _ ≤ ∑' s, 2 * ∫⁻ ω, ENNReal.ofReal (a s ω + b s ω) ∂μ := ENNReal.tsum_le_tsum hle
      _ = 2 * ∑' s, ∫⁻ ω, ENNReal.ofReal (a s ω + b s ω) ∂μ := ENNReal.tsum_mul_left
      _ < ⊤ := ENNReal.mul_lt_top (by norm_num) hsum

end NumStochOpt.QuasiFejer


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NumStochOpt.QuasiFejer

lemma sf_descent {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ γ : ℕ → Ω → ℝ) (s : ℕ)
    (hc : Convex ℝ X) (hcl : IsClosed X) (hne : X.Nonempty)
    (hx : ∀ k, Measurable (x k)) (hxl : MemLp (x s) 2 μ) (hξ : Integrable (ξ s) μ)
    (ha : Integrable (fun ω => ρ s ω * |γ s ω|) μ)
    (hb : Integrable (fun ω => ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) μ)
    (hρ : StronglyMeasurable[historySigma x s] (ρ s))
    (hγ : StronglyMeasurable[historySigma x s] (γ s))
    (hρn : 0 ≤ᵐ[μ] ρ s)
    (hr : ∀ ω, x (s + 1) ω = projX X (x s ω - ρ s ω • ξ s ω))
    (w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ X)
    (hq : ∀ᵐ ω ∂μ, F w - F (x s ω) ≥
      ⟪μ[ξ s | historySigma x s] ω, w - x s ω⟫_ℝ + γ s ω) :
    μ[(fun ω => ‖w - x (s + 1) ω‖ ^ 2) | historySigma x s] ≤ᵐ[μ]
      fun ω => ‖w - x s ω‖ ^ 2 - 2 * ρ s ω * (F (x s ω) - F w) +
        sf_error μ x ξ ρ γ s ω := by
  let ℱ := sf_filtration x hx
  let a : Ω → ℝ := fun ω => 2 * (ρ s ω * |γ s ω|)
  have hai : Integrable a μ := ha.const_mul 2
  have haa : StronglyMeasurable[historySigma x s] a := by
    letI : MeasurableSpace Ω := historySigma x s
    convert (stronglyMeasurable_const (b := (2 : ℝ))).mul (hρ.mul hγ.norm) using 1
    funext ω
    simp [a, Real.norm_eq_abs]
  have heq : (fun ω => 2 * ρ s ω * |γ s ω| + ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) =
      a + (fun ω => ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) := by
    funext ω; dsimp [a]; ring
  have hm : historySigma x s ≤ ‹MeasurableSpace Ω› := ℱ.le s
  have hca : μ[a | historySigma x s] = a := condExp_of_stronglyMeasurable hm haa hai
  have herror : sf_error μ x ξ ρ γ s =ᵐ[μ] fun ω =>
      a ω + μ[(fun ω => ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) | historySigma x s] ω := by
    unfold sf_error
    rw [heq]
    exact (condExp_add hai hb (historySigma x s)).mono fun ω h => by
      rw [h, hca]
      rfl
  have hstep := sf_one_step_result μ X x ξ ρ s hc hcl hne hx hxl hξ hb hρ hr w hw
  filter_upwards [hstep, hq, hρn, herror] with ω h hq hρ herr
  rw [herr]
  have hn : 0 ≤ 2 * ρ s ω := mul_nonneg (by norm_num) hρ
  have h1 := mul_le_mul_of_nonneg_left hq hn
  have h2 := mul_le_mul_of_nonneg_left (neg_le_abs (γ s ω)) hn
  dsimp [a]
  nlinarith

lemma sf_optimalset_result {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ γ : ℕ → Ω → ℝ)
    (hc : Convex ℝ X) (hX : IsCompact X) (hne : X.Nonempty)
    (hx : ∀ s, Measurable (x s)) (hx0 : ∀ ω, x 0 ω ∈ X)
    (hξ : ∀ s, Integrable (ξ s) μ)
    (hρ : ∀ s, StronglyMeasurable[historySigma x s] (ρ s))
    (hγ : ∀ s, StronglyMeasurable[historySigma x s] (γ s))
    (hr : ∀ s ω, x (s + 1) ω = projX X (x s ω - ρ s ω • ξ s ω))
    (hq : ∀ w ∈ optimalSet F X, ∀ s, ∀ᵐ ω ∂μ, F w - F (x s ω) ≥
      ⟪μ[ξ s | historySigma x s] ω, w - x s ω⟫_ℝ + γ s ω)
    (hρn : ∀ᵐ ω ∂μ, ∀ s, 0 ≤ ρ s ω)
    (hsum : ∑' s, ∫⁻ ω, ENNReal.ofReal
      (ρ s ω * |γ s ω| + ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) ∂μ < ⊤) :
    IsStochQuasiFejer μ x (optimalSet F X) := by
  have hxm := sf_iterates_mem X hc hX.isClosed hne x ξ ρ hx0 hr
  have hxl (s) := sf_compact_memLp μ X hX (x s) (hx s) (hxm s)
  obtain ⟨hai, hbi, herm, hern, hers⟩ := sf_error_data μ x ξ ρ γ hx hξ hρ hγ hρn hsum
  refine ⟨hx, hxl, sf_error μ x ξ ρ γ, herm, hern, hers, ?_⟩
  intro w hw s
  have h := sf_descent μ F X x ξ ρ γ s hc hX.isClosed hne hx (hxl s) (hξ s)
    (hai s) (hbi s) (hρ s) (hγ s) (hρn.mono fun ω h => h s) (hr s) w hw.1 (hq w hw s)
  filter_upwards [h, hρn] with ω h hρ
  have hg : 0 ≤ F (x s ω) - F w := sub_nonneg.2 (hw.2 _ (hxm s ω))
  have ht : 0 ≤ 2 * ρ s ω * (F (x s ω) - F w) :=
    mul_nonneg (mul_nonneg (by norm_num) (hρ s)) hg
  linarith

end NumStochOpt.QuasiFejer


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NumStochOpt.QuasiFejer

lemma sf_continuous_comp_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hF : ContinuousOn F X) (x : Ω → EuclideanSpace ℝ (Fin n))
    (hx : Measurable x) (hxm : ∀ ω, x ω ∈ X) : Measurable (fun ω => F (x ω)) := by
  exact hF.domRestrict.measurable.comp (hx.subtype_mk (h := hxm))

lemma sf_continuous_comp_integrable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hF : ContinuousOn F X) (hX : IsCompact X) (x : Ω → EuclideanSpace ℝ (Fin n))
    (hx : Measurable x) (hxm : ∀ ω, x ω ∈ X) : Integrable (fun ω => F (x ω)) μ := by
  obtain ⟨B, hB⟩ := (hX.image_of_continuousOn hF).isBounded.exists_norm_le
  apply memLp_one_iff_integrable.1
  exact MemLp.of_bound (sf_continuous_comp_measurable F X hF x hx hxm).aestronglyMeasurable
    B (ae_of_all _ fun ω => hB _ (Set.mem_image_of_mem F (hxm ω)))

end NumStochOpt.QuasiFejer


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NumStochOpt.QuasiFejer

lemma sf_summable_decrements {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (v g r : ℕ → Ω → ℝ) (hvi : ∀ s, Integrable (v s) μ)
    (hvn : ∀ s, 0 ≤ᵐ[μ] v s)
    (hgm : ∀ s, AEStronglyMeasurable (g s) μ) (hgn : ∀ s, 0 ≤ᵐ[μ] g s)
    (hrm : ∀ s, Measurable (r s)) (hrn : ∀ s, 0 ≤ᵐ[μ] r s)
    (hrsum : ∑' s, ∫⁻ ω, ENNReal.ofReal (r s ω) ∂μ < ⊤)
    (hstep : ∀ s, μ[v (s + 1) | ℱ s] ≤ᵐ[μ]
      fun ω => v s ω - g s ω + r s ω) :
    ∀ᵐ ω ∂μ, Summable (fun s => g s ω) := by
  obtain ⟨hri, hris⟩ := sf_error_summable μ r hrm hrn hrsum
  have hgi (s) : Integrable (g s) μ := by
    apply ((hvi s).add (hri s)).mono_nonneg (hgm s) (hgn s)
    filter_upwards [hstep s, condExp_nonneg (m := ℱ s) (hvn (s + 1))] with ω h hn
    change 0 ≤ μ[v (s + 1) | ℱ s] ω at hn
    change g s ω ≤ v s ω + r s ω
    linarith
  have htel (N) : (∫ ω, v N ω ∂μ) + ∑ s ∈ Finset.range N, ∫ ω, g s ω ∂μ ≤
      (∫ ω, v 0 ω ∂μ) + ∑ s ∈ Finset.range N, ∫ ω, r s ω ∂μ := by
    induction N with
    | zero => simp
    | succ N ih =>
      have h := integral_mono_ae (integrable_condExp (μ := μ) (m := ℱ N))
        (((hvi N).sub (hgi N)).add (hri N)) (hstep N)
      rw [integral_condExp (ℱ.le N)] at h
      change (∫ ω, v (N + 1) ω ∂μ) ≤ (∫ ω, ((v N - g N) + r N) ω ∂μ) at h
      rw [integral_add' ((hvi N).sub (hgi N)) (hri N), integral_sub' (hvi N) (hgi N)] at h
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith
  have hgs : Summable (fun s => ∫ ω, g s ω ∂μ) := by
    apply summable_of_sum_range_le (c := (∫ ω, v 0 ω ∂μ) + ∑' s, ∫ ω, r s ω ∂μ)
      (fun s => integral_nonneg_of_ae (hgn s))
    intro N
    have ht := htel N
    have hn := integral_nonneg_of_ae (hvn N)
    have hr := hris.sum_le_tsum (Finset.range N) (fun _ _ => integral_nonneg_of_ae (hrn _))
    linarith
  have hsum : ∑' s, eLpNorm (g s) 1 μ ≠ ⊤ := by
    simp_rw [sf_nonneg_l1 μ (g _) (hgi _) (hgn _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun s => integral_nonneg_of_ae (hgn s)) hgs]
    exact ENNReal.ofReal_ne_top
  exact (summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl hgm hsum).mono
    fun _ h => h.of_norm

end NumStochOpt.QuasiFejer


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NumStochOpt.QuasiFejer

lemma sf_weighted_gap_cluster (a g : ℕ → ℝ) (han : ∀ s, 0 ≤ a s) (hgn : ∀ s, 0 ≤ g s)
    (had : Tendsto (fun N => ∑ s ∈ Finset.range N, a s) atTop atTop)
    (hgs : Summable (fun s => a s * g s)) : MapClusterPt 0 atTop g := by
  apply Metric.nhds_basis_ball.mapClusterPt_iff_frequently.2
  intro ε hε
  have hf : ∃ᶠ s in atTop, g s < ε := by
    by_contra hf
    have he : ∀ᶠ s in atTop, ε ≤ g s := by simpa only [not_lt] using not_frequently.1 hf
    obtain ⟨N, hN⟩ := eventually_atTop.1 he
    let T : ℝ := ∑' s, a s * g s
    obtain ⟨M, hNM, hM⟩ := exists_lt_of_tendsto_atTop had N
      ((T + ε * (∑ s ∈ Finset.range N, a s) + 1) / ε)
    have htail : ε * ((∑ s ∈ Finset.range M, a s) - ∑ s ∈ Finset.range N, a s) ≤ T := by
      calc
        _ = ε * ∑ s ∈ Finset.Ico N M, a s := by rw [Finset.sum_Ico_eq_sub _ hNM]
        _ = ∑ s ∈ Finset.Ico N M, ε * a s := Finset.mul_sum _ _ _
        _ ≤ ∑ s ∈ Finset.Ico N M, a s * g s := by
          apply Finset.sum_le_sum
          intro s hs
          have := mul_le_mul_of_nonneg_left (hN s (Finset.mem_Ico.1 hs).1) (han s)
          nlinarith
        _ ≤ ∑ s ∈ Finset.range M, a s * g s := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro s hs; exact Finset.mem_range.2 (Finset.mem_Ico.1 hs).2
          · intro s _ _; exact mul_nonneg (han s) (hgn s)
        _ ≤ T := hgs.sum_le_tsum _ (fun s _ => mul_nonneg (han s) (hgn s))
    have hMm := (div_lt_iff₀ hε).1 hM
    nlinarith
  exact hf.mono fun s hs => by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (hgn s)] using hs

lemma sf_optimal_cluster {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : IsCompact X) (hF : ContinuousOn F X)
    (u : ℕ → EuclideanSpace ℝ (Fin n)) (hu : ∀ s, u s ∈ X)
    (w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ optimalSet F X)
    (a : ℕ → ℝ) (han : ∀ s, 0 ≤ a s)
    (had : Tendsto (fun N => ∑ s ∈ Finset.range N, a s) atTop atTop)
    (hgs : Summable (fun s => a s * (F (u s) - F w))) :
    ∃ p ∈ optimalSet F X, MapClusterPt p atTop u := by
  have hgap := sf_weighted_gap_cluster a (fun s => F (u s) - F w) han
    (fun s => sub_nonneg.2 (hw.2 _ (hu s))) had hgs
  obtain ⟨φ, hφ, hφg⟩ := hgap.tendsto_subseq
  obtain ⟨p, hpX, ψ, hψ, hψu⟩ := hX.tendsto_subseq (fun s => hu (φ s))
  have hFpu : Tendsto (fun s => F (u (φ (ψ s)))) atTop (𝓝 (F p)) := by
    exact (hF p hpX).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hψu, Eventually.of_forall fun s => hu _⟩)
  have hFpeq : F p - F w = 0 := tendsto_nhds_unique
    (hFpu.sub_const (F w)) (hφg.comp hψ.tendsto_atTop)
  refine ⟨p, ⟨hpX, fun y hy => ?_⟩, ?_⟩
  · have := hw.2 y hy; linarith
  · exact hψu.mapClusterPt.of_comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop)

lemma sf_dense_unique {n : ℕ}
    (u : ℕ → EuclideanSpace ℝ (Fin n)) (Z D : Set (EuclideanSpace ℝ (Fin n)))
    (hZD : Z ⊆ closure D)
    (hD : ∀ w ∈ D, ∃ l : ℝ, Tendsto (fun s => ‖w - u s‖ ^ 2) atTop (𝓝 l))
    (p : EuclideanSpace ℝ (Fin n)) (hp : p ∈ Z) (hpc : MapClusterPt p atTop u)
    (q : EuclideanSpace ℝ (Fin n)) (hqc : MapClusterPt q atTop u) : q = p := by
  have hc : IsClosed {w : EuclideanSpace ℝ (Fin n) | ‖w - p‖ = ‖w - q‖} :=
    isClosed_eq (continuous_id.sub continuous_const).norm
      (continuous_id.sub continuous_const).norm
  have hd : D ⊆ {w : EuclideanSpace ℝ (Fin n) | ‖w - p‖ = ‖w - q‖} :=
    fun w hw => sf_cluster_equidistant u w p q (hD w hw) hpc hqc
  have hh : ‖p - p‖ = ‖p - q‖ := closure_minimal hd hc (hZD hp)
  have hz : p - q = 0 := norm_eq_zero.1 (by simpa using hh.symm)
  exact (sub_eq_zero.1 hz).symm

end NumStochOpt.QuasiFejer


open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NumStochOpt.QuasiFejer

lemma sf_root_result {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ γ : ℕ → Ω → ℝ)
    (hF : ContinuousOn F X) (hc : Convex ℝ X) (hX : IsCompact X) (hne : X.Nonempty)
    (hx : ∀ s, Measurable (x s)) (hx0 : ∀ ω, x 0 ω ∈ X)
    (hξ : ∀ s, Integrable (ξ s) μ)
    (hρ : ∀ s, StronglyMeasurable[historySigma x s] (ρ s))
    (hγ : ∀ s, StronglyMeasurable[historySigma x s] (γ s))
    (hr : ∀ s ω, x (s + 1) ω = projX X (x s ω - ρ s ω • ξ s ω))
    (hq : ∀ w ∈ optimalSet F X, ∀ s, ∀ᵐ ω ∂μ, F w - F (x s ω) ≥
      ⟪μ[ξ s | historySigma x s] ω, w - x s ω⟫_ℝ + γ s ω)
    (hρn : ∀ᵐ ω ∂μ, ∀ s, 0 ≤ ρ s ω)
    (hρd : ∀ᵐ ω ∂μ, Tendsto (fun N => ∑ s ∈ Finset.range N, ρ s ω) atTop atTop)
    (hsum : ∑' s, ∫⁻ ω, ENNReal.ofReal
      (ρ s ω * |γ s ω| + ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) ∂μ < ⊤) :
    ∀ᵐ ω ∂μ, ∃ w ∈ optimalSet F X, Tendsto (fun s => x s ω) atTop (𝓝 w) := by
  have hxm := sf_iterates_mem X hc hX.isClosed hne x ξ ρ hx0 hr
  have hxl (s) := sf_compact_memLp μ X hX (x s) (hx s) (hxm s)
  let ℱ := sf_filtration x hx
  obtain ⟨hai, hbi, herm, hern, hers⟩ := sf_error_data μ x ξ ρ γ hx hξ hρ hγ hρn hsum
  obtain ⟨w, hwX, hwF⟩ := hX.exists_isMinOn hne hF
  have hw : w ∈ optimalSet F X := ⟨hwX, hwF⟩
  let g : ℕ → Ω → ℝ := fun s ω => 2 * ρ s ω * (F (x s ω) - F w)
  have hgm (s) : AEStronglyMeasurable (g s) μ := by
    have hFm := sf_continuous_comp_measurable F X hF (x s) (hx s) (hxm s)
    exact ((stronglyMeasurable_const.mul ((hρ s).mono (ℱ.le s))).mul
      (hFm.stronglyMeasurable.sub stronglyMeasurable_const)).aestronglyMeasurable
  have hgn (s) : 0 ≤ᵐ[μ] g s := hρn.mono fun ω h =>
    mul_nonneg (mul_nonneg (by norm_num) (h s)) (sub_nonneg.2 (hw.2 _ (hxm s ω)))
  have hstep (s) := sf_descent μ F X x ξ ρ γ s hc hX.isClosed hne hx (hxl s) (hξ s)
    (hai s) (hbi s) (hρ s) (hγ s) (hρn.mono fun ω h => h s) (hr s) w hwX (hq w hw s)
  have hgs := sf_summable_decrements μ ℱ (fun s ω => ‖w - x s ω‖ ^ 2) g
    (sf_error μ x ξ ρ γ) (fun s => sf_distance_integrable μ (x s) (hxl s) w)
    (fun _ => ae_of_all _ fun _ => sq_nonneg _) hgm hgn herm hern hers hstep
  have hqf := sf_optimalset_result μ F X x ξ ρ γ hc hX hne hx hx0 hξ hρ hγ hr hq hρn hsum
  obtain ⟨D, _, _, hZD, hD⟩ := sf_dense_distances μ x (optimalSet F X) hqf
  filter_upwards [hgs, hρn, hρd, hD] with ω hgs hρn hρd hD
  have hs : Summable (fun s => ρ s ω * (F (x s ω) - F w)) := by
    have heq : (fun s => (1 / 2 : ℝ) * g s ω) =
        (fun s => ρ s ω * (F (x s ω) - F w)) := by
      funext s
      dsimp [g]
      ring
    simpa only [heq] using! hgs.mul_left (1 / 2 : ℝ)
  obtain ⟨p, hp, hpc⟩ := sf_optimal_cluster F X hX hF (fun s => x s ω) (fun s => hxm s ω)
    w hw (fun s => ρ s ω) hρn hρd hs
  refine ⟨p, hp, hX.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall fun s => hxm s ω) ?_⟩
  intro q _ hqc
  exact sf_dense_unique (fun s => x s ω) (optimalSet F X) D hZD hD p hp hpc q hqc

end NumStochOpt.QuasiFejer

open NumStochOpt.QuasiFejer

/-- **Theorem 6.2** (Ermoliev, Ch. 6 of Ermoliev & Wets (1988), p. 144): convergence with
probability 1 of the stochastic quasigradient projection method.
Minimize `F` over `X ⊆ ℝⁿ`, with optimal set `X*`. The random iterates satisfy (6.11)
`x^{s+1} = π_X[x^s - ρ_s ξ⁰(s)]`, `s = 0, 1, …`, and the random directions satisfy (6.12)
`F(x*) - F(x^s) ≥ ⟨E{ξ⁰(s) | x⁰, …, x^s}, x* - x^s⟩ + γ₀(s)` for every `x* ∈ X*`, where `ρ_s` and
`γ₀(s)` depend on `(x⁰, …, x^s)`. Assume
(a) `F` is convex and continuous on `X`,
(b) `X` is a (nonempty) convex compact set,
(c) with probability 1, `ρ_s ≥ 0` and `∑ ρ_s = ∞`, and `∑_s E{ρ_s|γ₀(s)| + ρ_s²‖ξ⁰(s)‖²} < ∞` (6.15).
Then with probability 1 the sequence `x^s` converges and its limit lies in `X*`. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (x ξ : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ γ₀ : ℕ → Ω → ℝ)
    (hFconv : ConvexOn ℝ X F) (hFcont : ContinuousOn F X)
    (hXconv : Convex ℝ X) (hXcpt : IsCompact X) (hXne : X.Nonempty)
    (hx_meas : ∀ s, Measurable (x s)) (hx0 : ∀ ω, x 0 ω ∈ X)
    (hξ_int : ∀ s, Integrable (ξ s) μ)
    (hρ_adapt : ∀ s, StronglyMeasurable[historySigma x s] (ρ s))
    (hγ_adapt : ∀ s, StronglyMeasurable[historySigma x s] (γ₀ s))
    (hrec : ∀ s ω, x (s + 1) ω = projX X (x s ω - ρ s ω • ξ s ω))
    (hqg : ∀ xstar ∈ optimalSet F X, ∀ s, ∀ᵐ ω ∂μ,
      F xstar - F (x s ω) ≥ ⟪(condExp (historySigma x s) μ (ξ s)) ω, xstar - x s ω⟫_ℝ + γ₀ s ω)
    (hρ_nonneg : ∀ᵐ ω ∂μ, ∀ s, 0 ≤ ρ s ω)
    (hρ_div : ∀ᵐ ω ∂μ, Tendsto (fun N => ∑ s ∈ Finset.range N, ρ s ω) atTop atTop)
    (hsum : ∑' s, ∫⁻ ω, ENNReal.ofReal (ρ s ω * |γ₀ s ω| + ρ s ω ^ 2 * ‖ξ s ω‖ ^ 2) ∂μ < ⊤) :
    ∀ᵐ ω ∂μ, ∃ xstar ∈ optimalSet F X, Tendsto (fun s => x s ω) atTop (𝓝 xstar) := by
  exact sf_root_result μ F X x ξ ρ γ₀ hFcont hXconv hXcpt hXne hx_meas hx0 hξ_int hρ_adapt hγ_adapt hrec hqg hρ_nonneg hρ_div hsum

#print axioms solution
