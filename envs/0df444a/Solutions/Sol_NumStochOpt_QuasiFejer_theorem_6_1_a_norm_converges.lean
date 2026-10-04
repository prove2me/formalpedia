-- Prove2me | solution 1 for NumStochOpt.QuasiFejer.theorem_6_1_a_norm_converges
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T00:19:18.857567+00:00
-- url     : https://prove2.me/submissions/6546afbb-775b-44a3-885c-2f31dafeb0a9

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

open NumStochOpt.QuasiFejer

/-- **Theorem 6.1 (a)** (Ermoliev, Ch. 6 of Ermoliev & Wets (1988), p. 144, citing [5, p. 98]).
If `{z^s}` is a stochastic quasi-Féjer sequence for `Z`, then for every `w ∈ Z` the sequence
`‖w - z^{s+1}‖²` converges with probability 1 (the null set may depend on `w`), and
`E‖w - z^s‖²` is bounded in `s` by a finite constant `C` (which may depend on `w`). -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (Z : Set (EuclideanSpace ℝ (Fin n)))
    (hz : IsStochQuasiFejer μ z Z) :
    ∀ w ∈ Z,
      (∀ᵐ ω ∂μ, ∃ l : ℝ, Tendsto (fun s => ‖w - z (s + 1) ω‖ ^ 2) atTop (𝓝 l)) ∧
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ s, ∫⁻ ω, ENNReal.ofReal (‖w - z s ω‖ ^ 2) ∂μ < C := by
  exact sf_norm_result μ z Z hz

#print axioms solution
