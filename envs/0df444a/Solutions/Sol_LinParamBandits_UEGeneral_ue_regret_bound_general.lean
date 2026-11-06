-- Prove2me | solution 1 for LinParamBandits.UEGeneral.ue_regret_bound_general
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:41:33.919496+00:00
-- url     : https://prove2.me/submissions/031abed7-3d16-4caa-8f2a-6c245b15e04b

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy
import Definitions.Def_LinParamBandits_UEGeneral_Vstar
import Theorems.Thm_LinParamBandits_UEGeneral_regret_decomposition
import Theorems.Thm_LinParamBandits_UEGeneral_potential_sum_le_Vstar
import Theorems.Thm_LinParamBandits_UEGeneral_Vstar_le

open MeasureTheory ProbabilityTheory

namespace UEGenGoalAux

open LinParamBandits.UEGeneral

variable {r : ℕ}

lemma measurable_stepZ (ψ : Policy r) (n : ℕ) :
    Measurable (fun q : LinParamBandits.LowerBound.Vec r × (LinParamBandits.LowerBound.History r n × ℝ) =>
      Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) q.2.1
        (ψ.act n q.2.1, inner ℝ (ψ.act n q.2.1) q.1 + q.2.2)) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    have ha : Measurable (fun q : LinParamBandits.LowerBound.Vec r ×
        (LinParamBandits.LowerBound.History r n × ℝ) => ψ.act n q.2.1) :=
      (ψ.measurable_act n).comp (measurable_fst.comp measurable_snd)
    refine ha.prodMk ?_
    exact (Measurable.inner ha measurable_fst).add (measurable_snd.comp measurable_snd)
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)

lemma measurable_step (ψ : Policy r) (z : LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    Measurable (fun p : LinParamBandits.LowerBound.History r n × ℝ =>
      Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) p.1
        (ψ.act n p.1, inner ℝ (ψ.act n p.1) z + p.2)) :=
  (measurable_stepZ ψ n).comp (measurable_const.prodMk measurable_id)

lemma isProb_histMeasure (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) [IsMarkovKernel ν]
    (z : LinParamBandits.LowerBound.Vec r) (ψ : Policy r) :
    ∀ n, IsProbabilityMeasure (histMeasure ν z ψ n)
  | 0 => by
      simp only [histMeasure]; infer_instance
  | n + 1 => by
      have := isProb_histMeasure ν z ψ n
      simp only [histMeasure]
      exact Measure.isProbabilityMeasure_map (measurable_step ψ z n).aemeasurable

lemma exists_kernel (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) [IsMarkovKernel ν]
    (ψ : Policy r) :
    ∀ n, ∃ K : Kernel (LinParamBandits.LowerBound.Vec r) (LinParamBandits.LowerBound.History r n),
      IsMarkovKernel K ∧ ∀ z, K z = histMeasure ν z ψ n
  | 0 => ⟨Kernel.const _ (Measure.dirac (Fin.elim0 : LinParamBandits.LowerBound.History r 0)),
      inferInstance, fun z => by simp [histMeasure]⟩
  | n + 1 => by
      obtain ⟨K, hK, hKz⟩ := exists_kernel ν ψ n
      let η : Kernel (LinParamBandits.LowerBound.Vec r × LinParamBandits.LowerBound.History r n) ℝ :=
        ν.comap (fun p => ψ.act n p.2) ((ψ.measurable_act n).comp measurable_snd)
      let C := K ⊗ₖ η
      let D := (Kernel.deterministic (fun z : LinParamBandits.LowerBound.Vec r => z) measurable_id) ×ₖ C
      refine ⟨D.map (fun q : LinParamBandits.LowerBound.Vec r × (LinParamBandits.LowerBound.History r n × ℝ) =>
          Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) q.2.1
            (ψ.act n q.2.1, inner ℝ (ψ.act n q.2.1) q.1 + q.2.2)),
        Kernel.IsMarkovKernel.map _ (measurable_stepZ ψ n), fun z => ?_⟩
      rw [Kernel.map_apply _ (measurable_stepZ ψ n), Kernel.prod_apply, Kernel.deterministic_apply,
        Measure.dirac_prod, Measure.map_map (measurable_stepZ ψ n) measurable_prodMk_left]
      have hC : C z = (histMeasure ν z ψ n) ⊗ₘ (ν.comap (ψ.act n) (ψ.measurable_act n)) := by
        simp only [C]
        rw [Kernel.compProd_apply_eq_compProd_sectR, hKz]
        congr 1
      rw [hC]
      simp only [histMeasure]
      rfl

/-- The admissible arm set of period `s + 1`: arms of `𝒰`, equal to `b_{s+1}` if `s < r`. -/
def admissible (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (b : Fin r → LinParamBandits.LowerBound.Vec r)
    (s : ℕ) : Set (LinParamBandits.LowerBound.Vec r) :=
  {v | v ∈ 𝒰 ∧ ∀ hs : s < r, v = b ⟨s, hs⟩}

lemma measurableSet_admissible (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰 : MeasurableSet 𝒰)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (s : ℕ) : MeasurableSet (admissible 𝒰 b s) := by
  by_cases hs : s < r
  · have : admissible 𝒰 b s = 𝒰 ∩ {b ⟨s, hs⟩} := by
      ext v; simp only [admissible, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨h.1, h.2 hs⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
    rw [this]; exact h𝒰.inter (measurableSet_singleton _)
  · have : admissible 𝒰 b s = 𝒰 := by
      ext v; simp only [admissible, Set.mem_setOf_eq]
      exact ⟨fun h => h.1, fun h => ⟨h, fun h' => absurd h' hs⟩⟩
    rw [this]; exact h𝒰

lemma measurableSet_good (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰 : MeasurableSet 𝒰)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    MeasurableSet {h : LinParamBandits.LowerBound.History r n | ∀ s : Fin n, (h s).1 ∈ admissible 𝒰 b s} := by
  have : {h : LinParamBandits.LowerBound.History r n | ∀ s : Fin n, (h s).1 ∈ admissible 𝒰 b s} =
      ⋂ s : Fin n, (fun h : LinParamBandits.LowerBound.History r n => (h s).1) ⁻¹' admissible 𝒰 b s := by
    ext h; simp
  rw [this]
  exact MeasurableSet.iInter fun s =>
    (measurable_fst.comp (measurable_pi_apply s)) (measurableSet_admissible 𝒰 h𝒰 b s)

lemma ae_good (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰 : MeasurableSet 𝒰)
    (b : Fin r → LinParamBandits.LowerBound.Vec r)
    (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ)
    (z : LinParamBandits.LowerBound.Vec r) (ψ : Policy r)
    (hact : ∀ t h, ψ.act t h ∈ 𝒰)
    (hinit : ∀ (t : ℕ) (h : LinParamBandits.LowerBound.History r t) (ht : t < r), ψ.act t h = b ⟨t, ht⟩) :
    ∀ n, ∀ᵐ h ∂(histMeasure ν z ψ n), ∀ s : Fin n, (h s).1 ∈ admissible 𝒰 b s
  | 0 => Filter.Eventually.of_forall (fun h s => Fin.elim0 s)
  | n + 1 => by
      have ih := ae_good 𝒰 h𝒰 b ν z ψ hact hinit n
      simp only [histMeasure]
      rw [ae_map_iff (measurable_step ψ z n).aemeasurable (measurableSet_good 𝒰 h𝒰 b (n + 1))]
      have hms : MeasurableSet {p : LinParamBandits.LowerBound.History r n × ℝ |
          ∀ s : Fin n, (p.1 s).1 ∈ admissible 𝒰 b s} :=
        measurable_fst (measurableSet_good 𝒰 h𝒰 b n)
      have h2 : ∀ᵐ p ∂((histMeasure ν z ψ n) ⊗ₘ (ν.comap (ψ.act n) (ψ.measurable_act n))),
          ∀ s : Fin n, (p.1 s).1 ∈ admissible 𝒰 b s := by
        apply Measure.ae_compProd_of_ae_ae hms
        filter_upwards [ih] with h hh
        exact Filter.Eventually.of_forall (fun _ => hh)
      filter_upwards [h2] with p hp
      intro s
      refine Fin.lastCases ?_ (fun j => ?_) s
      · simp only [Fin.snoc_last, Fin.val_last]
        exact ⟨hact n p.1, fun hs => hinit n p.1 hs⟩
      · simp only [Fin.snoc_castSucc, Fin.coe_castSucc]
        exact hp j

lemma bddAbove_image (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰c : IsCompact 𝒰)
    (z : LinParamBandits.LowerBound.Vec r) : BddAbove ((fun v => inner ℝ v z) '' 𝒰) :=
  (h𝒰c.image (by fun_prop : Continuous fun v : LinParamBandits.LowerBound.Vec r => inner ℝ v z)).bddAbove

lemma le_bestValue (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰c : IsCompact 𝒰)
    (u : LinParamBandits.LowerBound.Vec r) (hu : u ∈ 𝒰) (z : LinParamBandits.LowerBound.Vec r) :
    inner ℝ u z ≤ bestValue 𝒰 z :=
  le_csSup (bddAbove_image 𝒰 h𝒰c z) ⟨u, hu, rfl⟩

lemma bestValue_le_add (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰c : IsCompact 𝒰)
    (h𝒰ne : 𝒰.Nonempty) (ū : ℝ) (hnorm : ∀ u ∈ 𝒰, ‖u‖ ≤ ū) (z w : LinParamBandits.LowerBound.Vec r) :
    bestValue 𝒰 z ≤ bestValue 𝒰 w + ū * ‖z - w‖ := by
  unfold bestValue
  apply csSup_le (h𝒰ne.image _)
  rintro _ ⟨v, hv, rfl⟩
  have h1 : inner ℝ v z = inner ℝ v w + inner ℝ v (z - w) := by
    rw [inner_sub_right]; ring
  have h2 : inner ℝ v (z - w) ≤ ū * ‖z - w‖ :=
    (real_inner_le_norm v (z - w)).trans (by gcongr; exact hnorm v hv)
  have h3 : inner ℝ v w ≤ sSup ((fun v => inner ℝ v w) '' 𝒰) := le_bestValue 𝒰 h𝒰c v hv w
  linarith

lemma continuous_bestValue (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰c : IsCompact 𝒰)
    (h𝒰ne : 𝒰.Nonempty) (ū : ℝ) (hū : 0 ≤ ū) (hnorm : ∀ u ∈ 𝒰, ‖u‖ ≤ ū) :
    Continuous (fun z => bestValue 𝒰 z) := by
  have : LipschitzWith (Real.toNNReal ū) (fun z => bestValue 𝒰 z) := by
    apply LipschitzWith.of_le_add_mul
    intro z w
    rw [Real.coe_toNNReal _ hū, dist_eq_norm]
    exact bestValue_le_add 𝒰 h𝒰c h𝒰ne ū hnorm z w
  exact this.continuous

lemma abs_bestValue_le (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰c : IsCompact 𝒰)
    (h𝒰ne : 𝒰.Nonempty) (ū : ℝ) (hnorm : ∀ u ∈ 𝒰, ‖u‖ ≤ ū) (z : LinParamBandits.LowerBound.Vec r) :
    |bestValue 𝒰 z| ≤ ū * ‖z‖ := by
  rw [abs_le]
  obtain ⟨u, hu⟩ := h𝒰ne
  constructor
  · have h1 := le_bestValue 𝒰 h𝒰c u hu z
    have h2 : -inner ℝ u z ≤ ū * ‖z‖ :=
      (neg_le_abs _).trans ((abs_real_inner_le_norm u z).trans (by gcongr; exact hnorm u hu))
    linarith
  · have := bestValue_le_add 𝒰 h𝒰c ⟨u, hu⟩ ū hnorm z 0
    unfold bestValue at this ⊢
    simp only [inner_zero_right, sub_zero] at this
    have h0 : sSup ((fun v : LinParamBandits.LowerBound.Vec r => (0 : ℝ)) '' 𝒰) = 0 := by
      rw [Set.Nonempty.image_const ⟨u, hu⟩, csSup_singleton]
    linarith

/-- The pathwise numerical step: `√V* ≤ √K' √r √(log T)`-type estimate, packaged. -/
lemma numeric (r T : ℕ) (hr : 2 ≤ r) (hT : r + 1 ≤ T) (c₀ : ℝ) (hc₀ : 1 ≤ c₀) :
    2 * c₀ * ((r : ℝ) * Real.log c₀ + ((r : ℝ) + 1) * Real.log ((r : ℝ) + ((T - r : ℕ) : ℝ) + 1)) ≤
      (2 * c₀ * (Real.log c₀ + 4)) * ((r : ℝ) * Real.log T) := by
  have hrT : (r : ℝ) + ((T - r : ℕ) : ℝ) = T := by
    rw [Nat.cast_sub (by omega)]; ring
  rw [hrT]
  have hT3 : (3 : ℝ) ≤ T := by exact_mod_cast (show 3 ≤ T by omega)
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hL1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlc : 0 ≤ Real.log c₀ := Real.log_nonneg hc₀
  have hlog2 : Real.log ((T : ℝ) + 1) ≤ 2 * Real.log T := by
    rw [← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by linarith)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have hlogT1 : 0 ≤ Real.log ((T : ℝ) + 1) := Real.log_nonneg (by linarith)
  have key : (r : ℝ) * Real.log c₀ + ((r : ℝ) + 1) * Real.log ((T : ℝ) + 1) ≤
      (Real.log c₀ + 4) * ((r : ℝ) * Real.log T) := by
    have e1 : (r : ℝ) * Real.log c₀ ≤ (r : ℝ) * Real.log c₀ * Real.log T := by
      have : 0 ≤ (r : ℝ) * Real.log c₀ := by positivity
      nlinarith
    have e2 : ((r : ℝ) + 1) * Real.log ((T : ℝ) + 1) ≤ (2 * r) * (2 * Real.log T) := by
      apply mul_le_mul (by linarith) hlog2 hlogT1 (by positivity)
    nlinarith
  have hc : 0 ≤ 2 * c₀ := by linarith
  calc 2 * c₀ * ((r : ℝ) * Real.log c₀ + ((r : ℝ) + 1) * Real.log ((T : ℝ) + 1))
      ≤ 2 * c₀ * ((Real.log c₀ + 4) * ((r : ℝ) * Real.log T)) := mul_le_mul_of_nonneg_left key hc
    _ = _ := by ring

end UEGenGoalAux

open UEGenGoalAux LinParamBandits.UEGeneral in
theorem solution :
    ∀ σ₀ ubar lam0 : ℝ, 0 < σ₀ → 0 < ubar → 0 < lam0 →
    ∃ a₄ a₅ : ℝ, 0 < a₄ ∧ 0 < a₅ ∧
    ∀ (r : ℕ), 2 ≤ r →
    ∀ (𝒰 : Set (LinParamBandits.LowerBound.Vec r)), IsCompact 𝒰 → 𝒰.Nonempty →
    ∀ (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ), IsMarkovKernel ν →
    ∀ (b : Fin r → LinParamBandits.LowerBound.Vec r), Assumption1 𝒰 ν b σ₀ ubar lam0 →
    ∀ (ψ : Policy r), IsUE 𝒰 b σ₀ ubar lam0 ψ →
    ∀ (T : ℕ), r + 1 ≤ T →
      (∀ z : LinParamBandits.LowerBound.Vec r,
        regret ν 𝒰 ψ z T ≤
          a₄ * r * ‖z‖ + a₅ * r * Real.sqrt T * Real.log T ^ (3 / 2 : ℝ)) ∧
      (∀ μ : Measure (LinParamBandits.LowerBound.Vec r), IsProbabilityMeasure μ → Integrable (fun z => ‖z‖) μ →
        Integrable (fun z => regret ν 𝒰 ψ z T) μ ∧
        risk ν 𝒰 ψ μ T ≤
          a₄ * r * (∫ z, ‖z‖ ∂μ) + a₅ * r * Real.sqrt T * Real.log T ^ (3 / 2 : ℝ)) := by
  intro σ₀ ubar lam0 hσ₀ hubar hlam0
  set c₀ : ℝ := max 1 (ubar ^ 2 / lam0) with hc₀def
  have hc₀ : 1 ≤ c₀ := le_max_left _ _
  set K' : ℝ := 2 * c₀ * (Real.log c₀ + 4) with hK'def
  have hK' : 0 ≤ K' := by
    have := Real.log_nonneg hc₀
    positivity
  set α := alpha σ₀ ubar lam0 with hαdef
  have hα : 0 ≤ α := by simp only [hαdef, alpha]; positivity
  refine ⟨4 * ubar, 2 * α * Real.sqrt K' + 1, by positivity, by positivity, ?_⟩
  intro r hr 𝒰 h𝒰c h𝒰ne ν hν b hA ψ hψ T hT
  haveI := hν
  have h𝒰m : MeasurableSet 𝒰 := h𝒰c.isClosed.measurableSet
  have hprob := isProb_histMeasure ν
  have hT3 : (3 : ℝ) ≤ T := by exact_mod_cast (show 3 ≤ T by omega)
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hL1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  -- Part 1: the regret bound.
  have part1 : ∀ z : LinParamBandits.LowerBound.Vec r,
      regret ν 𝒰 ψ z T ≤
        (4 * ubar) * r * ‖z‖ + (2 * α * Real.sqrt K' + 1) * r * Real.sqrt T * Real.log T ^ (3 / 2 : ℝ) := by
    intro z
    haveI := hprob z ψ T
    have hdec := regret_decomposition hr h𝒰c h𝒰ne hA hψ T hT z
    set V := Vstar r (ubar ^ 2 / lam0) (T - r) with hVdef
    -- pathwise bound on the potential sum
    have hpath : ∀ᵐ h ∂(histMeasure ν z ψ T),
        Real.sqrt (∑ t ∈ Finset.Ico r T, potential (armSeq h) t) ≤ Real.sqrt V := by
      filter_upwards [ae_good 𝒰 h𝒰m b ν z ψ hψ.act_mem hψ.act_init T] with h hh
      apply Real.sqrt_le_sqrt
      apply potential_sum_le_Vstar hr hubar hlam0 hA.b_minEig (armSeq h) _ _ T hT
      · intro k hk
        have hkT : k < T := by omega
        simp only [armSeq, dif_pos hkT]
        exact (hh ⟨k, hkT⟩).2 hk
      · intro s
        simp only [armSeq]
        split_ifs with hs
        · exact hA.norm_le _ (hh ⟨s, hs⟩).1
        · simp [hubar.le]
    have hint : ∫ h, Real.sqrt (∑ t ∈ Finset.Ico r T, potential (armSeq h) t) ∂(histMeasure ν z ψ T)
        ≤ Real.sqrt V := by
      have := integral_mono_of_nonneg (μ := histMeasure ν z ψ T)
        (f := fun h => Real.sqrt (∑ t ∈ Finset.Ico r T, potential (armSeq h) t))
        (g := fun _ => Real.sqrt V) (Filter.Eventually.of_forall (fun h => Real.sqrt_nonneg _))
        (integrable_const _) hpath
      simpa using this
    have hV : V ≤ K' * ((r : ℝ) * Real.log T) := by
      have h1 := Vstar_le hr (ubar ^ 2 / lam0) (by positivity) (T - r) (by omega)
      have h2 := numeric r T hr hT c₀ hc₀
      rw [← hc₀def] at h1
      linarith
    have hsqV : Real.sqrt V ≤ Real.sqrt K' * Real.sqrt r * Real.sqrt (Real.log T) := by
      rw [← Real.sqrt_mul hK', ← Real.sqrt_mul (by positivity), mul_assoc]
      exact Real.sqrt_le_sqrt hV
    have hpow : Real.log T ^ (3 / 2 : ℝ) = Real.log T * Real.sqrt (Real.log T) := by
      rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add (by linarith), Real.rpow_one]
    have hcoef : 0 ≤ 2 * α * Real.sqrt r * Real.log T * Real.sqrt T := by positivity
    have hsr : Real.sqrt (r : ℝ) * Real.sqrt r = r := Real.mul_self_sqrt (by positivity)
    have hA1 : 2 * ubar * ((r : ℝ) + 2) * ‖z‖ ≤ (4 * ubar) * r * ‖z‖ := by
      have := norm_nonneg z
      have : 2 * ubar * ((r : ℝ) + 2) ≤ (4 * ubar) * r := by nlinarith
      exact mul_le_mul_of_nonneg_right this (norm_nonneg z)
    have hA2 : 2 * α * Real.sqrt r * Real.log T * Real.sqrt T *
        ∫ h, Real.sqrt (∑ t ∈ Finset.Ico r T, potential (armSeq h) t) ∂(histMeasure ν z ψ T) ≤
        (2 * α * Real.sqrt K' + 1) * r * Real.sqrt T * Real.log T ^ (3 / 2 : ℝ) := by
      calc _ ≤ 2 * α * Real.sqrt r * Real.log T * Real.sqrt T *
            (Real.sqrt K' * Real.sqrt r * Real.sqrt (Real.log T)) :=
            mul_le_mul_of_nonneg_left (hint.trans hsqV) hcoef
        _ = (2 * α * Real.sqrt K') * (Real.sqrt r * Real.sqrt r) * Real.sqrt T *
            (Real.log T * Real.sqrt (Real.log T)) := by ring
        _ = (2 * α * Real.sqrt K') * r * Real.sqrt T * Real.log T ^ (3 / 2 : ℝ) := by
            rw [hsr, hpow]
        _ ≤ _ := by
            have : 0 ≤ (r : ℝ) * Real.sqrt T * Real.log T ^ (3 / 2 : ℝ) := by positivity
            nlinarith
    linarith
  refine ⟨part1, ?_⟩
  intro μ hμ hnorm
  -- measurability of the regret in z
  obtain ⟨K, hK, hKz⟩ := exists_kernel ν ψ T
  haveI := hK
  have hRmeas : StronglyMeasurable (fun z => regret ν 𝒰 ψ z T) := by
    have heq : (fun z => regret ν 𝒰 ψ z T) = fun z =>
        (T : ℝ) * bestValue 𝒰 z -
          ∫ h, (fun p : LinParamBandits.LowerBound.Vec r × LinParamBandits.LowerBound.History r T =>
            ∑ s, inner ℝ (p.2 s).1 p.1) (z, h) ∂(K z) := by
      funext z
      unfold regret
      rw [hKz z]
    rw [heq]
    refine StronglyMeasurable.sub ?_ ?_
    · exact (continuous_const.mul (continuous_bestValue 𝒰 h𝒰c h𝒰ne ubar hubar.le hA.norm_le)).stronglyMeasurable
    · refine StronglyMeasurable.integral_kernel_prod_right' (κ := K)
        (f := fun p : LinParamBandits.LowerBound.Vec r × LinParamBandits.LowerBound.History r T =>
          ∑ s, inner ℝ (p.2 s).1 p.1) ?_
      apply Continuous.stronglyMeasurable
      fun_prop
  -- a linear bound on |regret|
  have hRabs : ∀ z, |regret ν 𝒰 ψ z T| ≤ (2 * T * ubar) * ‖z‖ := by
    intro z
    haveI := hprob z ψ T
    have h1 := abs_bestValue_le 𝒰 h𝒰c h𝒰ne ubar hA.norm_le z
    have h2 : ‖∫ h, ∑ s, inner ℝ (h s).1 z ∂(histMeasure ν z ψ T)‖ ≤ T * ubar * ‖z‖ := by
      have := norm_integral_le_of_norm_le_const (μ := histMeasure ν z ψ T) (C := T * ubar * ‖z‖)
        (f := fun h => ∑ s, inner ℝ (h s).1 z) (by
          filter_upwards [ae_good 𝒰 h𝒰m b ν z ψ hψ.act_mem hψ.act_init T] with h hh
          calc ‖∑ s, inner ℝ (h s).1 z‖ ≤ ∑ s : Fin T, ‖inner ℝ (h s).1 z‖ := norm_sum_le _ _
            _ ≤ ∑ s : Fin T, ubar * ‖z‖ := by
                apply Finset.sum_le_sum
                intro s _
                rw [Real.norm_eq_abs]
                exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact hA.norm_le _ (hh s).1)
            _ = T * ubar * ‖z‖ := by simp; ring)
      rwa [probReal_univ, mul_one] at this
    rw [Real.norm_eq_abs] at h2
    unfold regret
    have hTn : (0 : ℝ) ≤ T := by positivity
    calc |(T : ℝ) * bestValue 𝒰 z - ∫ h, ∑ s, inner ℝ (h s).1 z ∂(histMeasure ν z ψ T)|
        ≤ |(T : ℝ) * bestValue 𝒰 z| + |∫ h, ∑ s, inner ℝ (h s).1 z ∂(histMeasure ν z ψ T)| :=
          abs_sub _ _
      _ ≤ T * (ubar * ‖z‖) + T * ubar * ‖z‖ := by
          rw [abs_mul, abs_of_nonneg hTn]
          gcongr
      _ = (2 * T * ubar) * ‖z‖ := by ring
  have hRint : Integrable (fun z => regret ν 𝒰 ψ z T) μ := by
    refine Integrable.mono' (hnorm.const_mul (2 * T * ubar)) hRmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => ?_))
    rw [Real.norm_eq_abs]
    exact hRabs z
  refine ⟨hRint, ?_⟩
  set Cst : ℝ := (2 * α * Real.sqrt K' + 1) * r * Real.sqrt T * Real.log T ^ (3 / 2 : ℝ)
  have hBint : Integrable (fun z => (4 * ubar) * r * ‖z‖ + Cst) μ :=
    (hnorm.const_mul _).add (integrable_const _)
  unfold risk
  calc ∫ z, regret ν 𝒰 ψ z T ∂μ ≤ ∫ z, ((4 * ubar) * r * ‖z‖ + Cst) ∂μ :=
        integral_mono hRint hBint part1
    _ = (4 * ubar) * r * (∫ z, ‖z‖ ∂μ) + Cst := by
        rw [integral_add (hnorm.const_mul _) (integrable_const _), integral_const_mul,
          integral_const, probReal_univ, one_smul]
