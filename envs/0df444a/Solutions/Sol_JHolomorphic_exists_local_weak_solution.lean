-- Prove2me | solution 1 for JHolomorphic.exists_local_weak_solution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T09:50:07.387279+00:00
-- url     : https://prove2.me/submissions/846985cd-fe37-4c39-b07a-444ae5e69b0a

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_norm_integral_inv_sub_smul_le
import Theorems.Thm_JHolomorphic_exists_weakPartials_integral_inv_sub_smul
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_smul_sub
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_contDiffOn
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal BoundedContinuousFunction

set_option maxHeartbeats 4000000 in
/-- Wendl, Lemma 2.24. -/
theorem exists_local_weak_solution_aux (n : ℕ) (p : ℝ) (hp : 2 < p)
    (A : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n))
    (hA : MemLp A (ENNReal.ofReal p) (volume.restrict (ball 0 1)))
    (u₀ : EuclideanSpace ℂ (Fin n)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ u : ℂ → EuclideanSpace ℂ (Fin n), ContinuousOn u (ball 0 ε) ∧
      u 0 = u₀ ∧ ∃ us ut : ℂ → EuclideanSpace ℂ (Fin n), HasWeakPartialsOn (ball 0 ε) u us ut ∧
        MemLp u (ENNReal.ofReal p) (volume.restrict (ball 0 ε)) ∧
        MemLp us (ENNReal.ofReal p) (volume.restrict (ball 0 ε)) ∧
        MemLp ut (ENNReal.ofReal p) (volume.restrict (ball 0 ε)) ∧
        ∀ᵐ z ∂(volume.restrict (ball 0 ε)), us z + Complex.I • ut z + A z (u z) = 0 := by
  classical
  have hp1 : 1 < p := by linarith
  have hP1 : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le
  have hPtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨C1, hC1, hC1b⟩ :=
    norm_integral_inv_sub_smul_le (E := EuclideanSpace ℂ (Fin n)) p 1 hp one_pos
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = Real.pi / (2 * (C1 + 1)) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hAn : MemLp (fun z => ‖A z‖) (ENNReal.ofReal p) (volume.restrict (ball 0 1)) := hA.norm
  obtain ⟨δ, hδ, hδb⟩ := hAn.eLpNorm_indicator_le hP1 hPtop hη
  have hvol : Tendsto (fun r => volume (ball (0 : ℂ) r)) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_measure_biInter_gt (μ := volume) (s := fun r : ℝ => ball (0 : ℂ) r)
      (a := 0) (fun r _ => measurableSet_ball.nullMeasurableSet)
      (fun i j _ hij => ball_subset_ball hij) ⟨1, one_pos, measure_ball_lt_top.ne⟩
    rw [biInter_gt_ball, closedBall_zero, measure_singleton] at h
    exact h
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ε ∧ ε < 1 ∧ volume (ball (0 : ℂ) ε) ≤ ENNReal.ofReal δ := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT one_pos,
      (tendsto_order.1 hvol).2 _ (ENNReal.ofReal_pos.2 hδ)] with ε hε0 hε1 hεv
    exact ⟨hε0, hε1.2, hεv.le⟩
  filter_upwards [hev] with ε ⟨hε0, hε1, hεv⟩
  have hD1 : ball (0 : ℂ) ε ⊆ ball 0 1 := ball_subset_ball hε1.le
  have hAε : eLpNorm (fun z => ‖A z‖) (ENNReal.ofReal p) (volume.restrict (ball 0 ε)) ≤
      ENNReal.ofReal η := by
    have h := hδb (ball 0 ε) measurableSet_ball (by
      rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.2 hD1]; exact hεv)
    have hrr : (volume.restrict (ball (0 : ℂ) 1)).restrict (ball 0 ε) =
        volume.restrict (ball 0 ε) := by
      rw [Measure.restrict_restrict measurableSet_ball, inter_eq_left.2 hD1]
    rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball, hrr] at h
    exact h
  have hAεm : MemLp (fun z => ‖A z‖) (ENNReal.ofReal p) (volume.restrict (ball 0 ε)) :=
    hAn.mono_measure (Measure.restrict_mono hD1 le_rfl)
  have hAεs : AEStronglyMeasurable A (volume.restrict (ball 0 ε)) :=
    hA.1.mono_measure (Measure.restrict_mono hD1 le_rfl)
  have h0D : (0 : ℂ) ∈ ball (0 : ℂ) ε := mem_ball_self hε0
  -- extension by zero of bounded continuous functions on the disc
  obtain ⟨ext, hextdef⟩ : ∃ ext : (ball (0 : ℂ) ε →ᵇ EuclideanSpace ℂ (Fin n)) →
      ℂ → EuclideanSpace ℂ (Fin n),
      ext = fun v z => if hz : z ∈ ball (0 : ℂ) ε then v ⟨z, hz⟩ else 0 := ⟨_, rfl⟩
  have hext_mem : ∀ v z (hz : z ∈ ball (0 : ℂ) ε), ext v z = v ⟨z, hz⟩ := fun v z hz => by
    rw [hextdef]; exact dif_pos hz
  have hext_out : ∀ v z, z ∉ ball (0 : ℂ) ε → ext v z = 0 := fun v z hz => by
    rw [hextdef]; exact dif_neg hz
  have hext_norm : ∀ v z, ‖ext v z‖ ≤ ‖v‖ := by
    intro v z
    by_cases hz : z ∈ ball (0 : ℂ) ε
    · rw [hext_mem v z hz]; exact v.norm_coe_le_norm _
    · rw [hext_out v z hz, norm_zero]; exact norm_nonneg _
  have hext_sub : ∀ v w z, ext (v - w) z = ext v z - ext w z := by
    intro v w z
    by_cases hz : z ∈ ball (0 : ℂ) ε
    · rw [hext_mem _ z hz, hext_mem _ z hz, hext_mem _ z hz]; rfl
    · rw [hext_out _ z hz, hext_out _ z hz, hext_out _ z hz, sub_zero]
  have hext_cont : ∀ v, ContinuousOn (ext v) (ball 0 ε) := by
    intro v
    exact continuousOn_iff_continuous_restrict.2
      (v.continuous.congr fun x => (hext_mem v x.1 x.2).symm)
  -- the right-hand side `A u` on the disc
  obtain ⟨G, hGdef⟩ : ∃ G : (ball (0 : ℂ) ε →ᵇ EuclideanSpace ℂ (Fin n)) →
      ℂ → EuclideanSpace ℂ (Fin n),
      G = fun v => (ball (0 : ℂ) ε).indicator (fun z => A z (ext v z)) := ⟨_, rfl⟩
  have hAvm : ∀ v, AEStronglyMeasurable (fun z => A z (ext v z)) (volume.restrict (ball 0 ε)) :=
    fun v => (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := EuclideanSpace ℂ (Fin n))
      (F := EuclideanSpace ℂ (Fin n))).continuous.comp_aestronglyMeasurable
        (hAεs.prodMk ((hext_cont v).aestronglyMeasurable measurableSet_ball))
  have hGrest : ∀ v, MemLp (fun z => A z (ext v z)) (ENNReal.ofReal p)
      (volume.restrict (ball 0 ε)) ∧ eLpNorm (fun z => A z (ext v z)) (ENNReal.ofReal p)
        (volume.restrict (ball 0 ε)) ≤ ENNReal.ofReal (‖v‖ * η) := by
    intro v
    have hdom : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) ε)), ‖A z (ext v z)‖ ≤ ‖v‖ * ‖‖A z‖‖ :=
      Eventually.of_forall fun z => by
        rw [norm_norm]
        calc ‖A z (ext v z)‖ ≤ ‖A z‖ * ‖ext v z‖ := (A z).le_opNorm _
          _ ≤ ‖A z‖ * ‖v‖ := mul_le_mul_of_nonneg_left (hext_norm v z) (norm_nonneg _)
          _ = ‖v‖ * ‖A z‖ := mul_comm _ _
    refine ⟨hAεm.of_le_mul (hAvm v) hdom, ?_⟩
    calc _ ≤ ENNReal.ofReal ‖v‖ * eLpNorm (fun z => ‖A z‖) (ENNReal.ofReal p)
          (volume.restrict (ball 0 ε)) :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdom _
      _ ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal η := by gcongr
      _ = _ := (ENNReal.ofReal_mul (norm_nonneg _)).symm
  have hGm : ∀ v, MemLp (G v) (ENNReal.ofReal p) volume := fun v => by
    rw [hGdef]; exact (memLp_indicator_iff_restrict measurableSet_ball).2 (hGrest v).1
  have hGn : ∀ v, (eLpNorm (G v) (ENNReal.ofReal p) volume).toReal ≤ ‖v‖ * η := fun v => by
    rw [hGdef]
    show (eLpNorm ((ball (0 : ℂ) ε).indicator (fun z => A z (ext v z))) (ENNReal.ofReal p)
      volume).toReal ≤ _
    rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hGrest v).2
  have hGs : ∀ v, Function.support (G v) ⊆ ball 0 ε := fun v => by
    rw [hGdef]; exact Set.support_indicator_subset
  have hGsub : ∀ v w, G (v - w) = G v - G w := by
    intro v w
    rw [hGdef]
    funext z
    simp only [Pi.sub_apply]
    by_cases hz : z ∈ ball (0 : ℂ) ε
    · rw [indicator_of_mem hz, indicator_of_mem hz, indicator_of_mem hz, hext_sub, map_sub]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz, indicator_of_notMem hz, sub_zero]
  -- the Cauchy transform
  obtain ⟨S, hSdef⟩ : ∃ S : (ℂ → EuclideanSpace ℂ (Fin n)) → ℂ → EuclideanSpace ℂ (Fin n),
      S = fun f z => ∫ ζ, (z - ζ)⁻¹ • f ζ := ⟨_, rfl⟩
  have hSb : ∀ v, ∀ z ∈ ball (0 : ℂ) ε, Integrable (fun ζ => (z - ζ)⁻¹ • G v ζ) ∧
      ‖S (G v) z‖ ≤ C1 * (‖v‖ * η) := by
    intro v z hz
    obtain ⟨hi, hb⟩ := hC1b (G v) (hGm v) ((hGs v).trans hD1) z (hD1 hz)
    refine ⟨hi, ?_⟩
    rw [hSdef]
    exact hb.trans (mul_le_mul_of_nonneg_left (hGn v) hC1)
  have hSsub : ∀ v w, ∀ z ∈ ball (0 : ℂ) ε, S (G v) z - S (G w) z = S (G (v - w)) z := by
    intro v w z hz
    rw [hSdef, hGsub]
    simp only
    rw [← integral_sub (hSb v z hz).1 (hSb w z hz).1]
    congr 1
    funext ζ
    simp [smul_sub]
  have hC3 : ∀ v, ContinuousOn (S (G v)) (ball 0 ε) ∧
      ∃ ws wt : ℂ → EuclideanSpace ℂ (Fin n), HasWeakPartialsOn (ball 0 ε) (S (G v)) ws wt ∧
        MemLp ws (ENNReal.ofReal p) (volume.restrict (ball 0 ε)) ∧
        MemLp wt (ENNReal.ofReal p) (volume.restrict (ball 0 ε)) ∧
        ∀ᵐ z ∂(volume.restrict (ball 0 ε)),
          ws z + Complex.I • wt z = (2 * Real.pi : ℂ) • G v z := fun v => by
    rw [hSdef]
    exact exists_weakPartials_integral_inv_sub_smul p ε hp hε0 (G v) (hGm v) (hGs v)
  -- the contraction
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = -(2 * Real.pi)⁻¹ := ⟨_, rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ F : (ball (0 : ℂ) ε →ᵇ EuclideanSpace ℂ (Fin n)) →
      ℂ → EuclideanSpace ℂ (Fin n),
      F = fun v z => c • (S (G v) z - (S (G v) 0 + (2 * Real.pi) • u₀)) := ⟨_, rfl⟩
  have hFcOn : ∀ v, ContinuousOn (F v) (ball 0 ε) := fun v => by
    rw [hFdef]; exact ((hC3 v).1.sub continuousOn_const).const_smul c
  have hFc : ∀ v, Continuous (fun x : ball (0 : ℂ) ε => F v x) := fun v => by
    have := hFcOn v
    rw [continuousOn_iff_continuous_restrict] at this
    exact this
  have hFb : ∀ v (x : ball (0 : ℂ) ε),
      ‖F v x‖ ≤ |c| * (2 * (C1 * (‖v‖ * η)) + 2 * Real.pi * ‖u₀‖) := by
    intro v x
    rw [hFdef]
    simp only
    rw [norm_smul, Real.norm_eq_abs]
    gcongr
    calc ‖S (G v) x - (S (G v) 0 + (2 * Real.pi) • u₀)‖
        ≤ ‖S (G v) x‖ + (‖S (G v) 0‖ + ‖(2 * Real.pi) • u₀‖) :=
          (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ C1 * (‖v‖ * η) + (C1 * (‖v‖ * η) + 2 * Real.pi * ‖u₀‖) := by
          gcongr
          · exact (hSb v x x.2).2
          · exact (hSb v 0 h0D).2
          · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      _ = _ := by ring
  let Φ : (ball (0 : ℂ) ε →ᵇ EuclideanSpace ℂ (Fin n)) →
      (ball (0 : ℂ) ε →ᵇ EuclideanSpace ℂ (Fin n)) := fun v =>
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x : ball (0 : ℂ) ε => F v x) (hFc v) _
      (hFb v)
  have hΦapp : ∀ v (x : ball (0 : ℂ) ε), Φ v x = F v x := fun v x => rfl
  have hcontr : ∀ v w (x : ball (0 : ℂ) ε), ‖Φ v x - Φ w x‖ ≤ (1 / 2) * ‖v - w‖ := by
    intro v w x
    rw [hΦapp, hΦapp, hFdef]
    simp only
    rw [← smul_sub]
    have : S (G v) x - (S (G v) 0 + (2 * Real.pi) • u₀) -
        (S (G w) x - (S (G w) 0 + (2 * Real.pi) • u₀)) = S (G (v - w)) x - S (G (v - w)) 0 := by
      rw [← hSsub v w x x.2, ← hSsub v w 0 h0D]; abel
    rw [this, norm_smul, Real.norm_eq_abs, hcdef, abs_neg, abs_inv,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have hb1 := (hSb (v - w) x x.2).2
    have hb2 := (hSb (v - w) 0 h0D).2
    calc (2 * Real.pi)⁻¹ * ‖S (G (v - w)) x - S (G (v - w)) 0‖
        ≤ (2 * Real.pi)⁻¹ * (C1 * (‖v - w‖ * η) + C1 * (‖v - w‖ * η)) := by
          gcongr; exact (norm_sub_le _ _).trans (add_le_add hb1 hb2)
      _ = (C1 / (2 * (C1 + 1))) * ‖v - w‖ := by
          rw [hηdef]; field_simp; ring
      _ ≤ (1 / 2) * ‖v - w‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [div_le_iff₀ (by positivity)]; linarith
  have hΦ : ContractingWith (1 / 2 : ℝ≥0) Φ := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => ?_
    rw [BoundedContinuousFunction.sub_apply]
    have := hcontr v w x
    simpa using this
  haveI : Nonempty (ball (0 : ℂ) ε →ᵇ EuclideanSpace ℂ (Fin n)) := ⟨0⟩
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ = ContractingWith.fixedPoint Φ hΦ := ⟨_, rfl⟩
  have hfix : Φ v₀ = v₀ := by rw [hv₀]; exact ContractingWith.fixedPoint_isFixedPt hΦ
  have hu_eq : ∀ z (hz : z ∈ ball (0 : ℂ) ε), F v₀ z = ext v₀ z := by
    intro z hz
    rw [hext_mem v₀ z hz, ← hΦapp v₀ ⟨z, hz⟩, hfix]
  -- the solution
  obtain ⟨hwc, ws, wt, hW, hwsm, hwtm, heq⟩ := hC3 v₀
  have hKint : ∀ f : ℂ → EuclideanSpace ℂ (Fin n), MemLp f (ENNReal.ofReal p)
      (volume.restrict (ball 0 ε)) → ∀ K ⊆ ball (0 : ℂ) ε, IsCompact K → IntegrableOn f K := by
    intro f hf K hK hKc
    haveI : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
    exact (hf.mono_measure (Measure.restrict_mono hK le_rfl)).integrable hP1
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) ε)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  refine ⟨F v₀, hFcOn v₀, ?_, fun z => c • (ws z - 0), fun z => c • (wt z - 0), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFdef]
    simp only
    rw [sub_add_cancel_left, smul_neg, smul_smul, hcdef, neg_mul,
      inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), neg_smul, neg_neg, one_smul]
  · have hconst : HasWeakPartialsOn (ball 0 ε)
        (fun _ : ℂ => S (G v₀) 0 + (2 * Real.pi) • u₀) (fun _ => 0) (fun _ => 0) := by
      have := HasWeakPartialsOn.of_contDiffOn isOpen_ball
        (contDiffOn_const (c := S (G v₀) 0 + (2 * Real.pi) • u₀) (s := ball (0 : ℂ) ε))
      simpa using this
    have h6 := HasWeakPartialsOn.smul_sub hW hconst
      (fun K hK hKc => ⟨(hwc.mono hK).integrableOn_compact hKc, hKint ws hwsm K hK hKc,
        hKint wt hwtm K hK hKc⟩)
      (fun K hK hKc => ⟨integrableOn_const hKc.measure_lt_top.ne,
        integrableOn_const hKc.measure_lt_top.ne, integrableOn_const hKc.measure_lt_top.ne⟩) c
    rw [hFdef]
    exact h6
  · refine MemLp.of_bound ((hFcOn v₀).aestronglyMeasurable measurableSet_ball) ‖Φ v₀‖ ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    rw [← hΦapp v₀ ⟨z, hz⟩]
    exact (Φ v₀).norm_coe_le_norm _
  · simp only [sub_zero]; exact hwsm.const_smul c
  · simp only [sub_zero]; exact hwtm.const_smul c
  · filter_upwards [heq, ae_restrict_mem measurableSet_ball] with z hz hzD
    simp only [sub_zero]
    have hG : G v₀ z = A z (F v₀ z) := by
      rw [hGdef, hu_eq z hzD]; exact indicator_of_mem hzD _
    have hsm2 : ((2 * Real.pi : ℝ) : ℂ) • A z (F v₀ z) = (2 * Real.pi : ℝ) • A z (F v₀ z) := rfl
    rw [show c • ws z + Complex.I • (c • wt z) = c • (ws z + Complex.I • wt z) by
      rw [smul_add, smul_comm Complex.I c], hz, hG,
      show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      hsm2, smul_smul, hcdef, neg_mul,
      inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), neg_smul, one_smul, neg_add_cancel]

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

theorem solution (n : ℕ) (p : ℝ) (hp : 2 < p)
    (A : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n))
    (hA : MemLp A (ENNReal.ofReal p) (volume.restrict (ball 0 1)))
    (u₀ : EuclideanSpace ℂ (Fin n)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ u : ℂ → EuclideanSpace ℂ (Fin n), ContinuousOn u (ball 0 ε) ∧
      u 0 = u₀ ∧ ∃ us ut : ℂ → EuclideanSpace ℂ (Fin n), HasWeakPartialsOn (ball 0 ε) u us ut ∧
        MemLp u (ENNReal.ofReal p) (volume.restrict (ball 0 ε)) ∧
        MemLp us (ENNReal.ofReal p) (volume.restrict (ball 0 ε)) ∧
        MemLp ut (ENNReal.ofReal p) (volume.restrict (ball 0 ε)) ∧
        ∀ᵐ z ∂(volume.restrict (ball 0 ε)), us z + Complex.I • ut z + A z (u z) = 0 :=
  exists_local_weak_solution_aux n p hp A hA u₀
