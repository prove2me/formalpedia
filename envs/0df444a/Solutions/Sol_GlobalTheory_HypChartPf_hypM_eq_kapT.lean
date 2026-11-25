-- Prove2me | solution 1 for GlobalTheory.HypChartPf.hypM_eq_kapT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:35.266618+00:00
-- url     : https://prove2.me/submissions/b9f79480-04d4-47de-89cc-316cff1c1082

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushQ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidChartMeasureFormula
import Theorems.Thm_GlobalTheory_HypChartPf_hypM_eq
import Theorems.Thm_PI_RhsWLim_W_continuous_hypPar
import Theorems.Thm_PI_RhsWLim_W_normSq_sum_eq
import Theorems.Thm_PI_RhsWLim_W_qIso_measurePreserving

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
namespace GlobalTheory.HypChartPf
open PI.RhsWLim PI.RhsWLim.W
private lemma ofLp_qFw_kapT (k : ℕ) (v : (Fin k → ℂ) × ℂ) :
    WithLp.ofLp (qFw k (kapT k v)) = (WithLp.toLp 2 v.1, Complex.arg v.2) := by
  ext a
  · simp [qFw, kapT, Complex.re_add_im]
  · simp [qFw, kapT]
private lemma hypPar_toLp_arg_of_mem_hypS (k : ℕ) (T' : ℝ) (v : (Fin k → ℂ) × ℂ) (hv : v ∈ hypS k T') :
    hypPar k T' (WithLp.toLp 2 v.1, Complex.arg v.2) = v := by
  simp only [hypS, Set.mem_ofPred_eq] at hv
  have hn : ‖(WithLp.toLp 2 v.1 : EuclideanSpace ℂ (Fin k))‖ ^ 2 + T' = ‖v.2‖ ^ 2 := by
    rw [← normSq_sum_eq, ← Complex.normSq_eq_norm_sq]
    simp only []
    linarith
  simp only [hypPar, hn, Real.sqrt_sq (norm_nonneg _), Complex.norm_mul_exp_arg_mul_I, ]
private lemma kapT_hypPar_ofLp_qFw (k : ℕ) (T' : ℝ) (hT' : 0 < T') (x : TrE k)
    (hx : (WithLp.ofLp (qFw k x)).2 ∈ Set.Ioc (-Real.pi) Real.pi) :
    kapT k (hypPar k T' (WithLp.ofLp (qFw k x))) = x := by
  ext o
  rcases o with _ | ⟨a, b⟩
  · simp only [kapT, hypPar]
    simp only [qFw] at hx ⊢
    simp only [WithLp.equiv_symm_apply, WithLp.ofLp_toLp]
    rw [Complex.arg_real_mul _ (Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (sq_nonneg _) hT')),
      Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I hx]
  · cases b <;> simp [kapT, hypPar, qFw]
end GlobalTheory.HypChartPf
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.HypChartPf
open PI.RhsWLim PI.RhsWLim.W
namespace GlobalTheory.HypChartPf
theorem _root_.solution (k : ℕ) (T' : ℝ) (hT' : 0 < T') (E : Set ((Fin k → ℂ) × ℂ)) (hE : MeasurableSet E)
    (hS : E ⊆ hypS k T') : hypM k T' E = (1 / 2) * volume (kapT k '' E) := by
  rw [hypM_eq k T' E hE]
  congr 1
  have hFm : MeasurableSet (hypPar k T' ⁻¹' E ∩ Set.univ ×ˢ Set.Ioc (-Real.pi) Real.pi) :=
    ((continuous_hypPar k T').measurable hE).inter (MeasurableSet.univ.prod measurableSet_Ioc)
  have hset : kapT k '' E =
      (fun x : TrE k => WithLp.ofLp (qFw k x)) ⁻¹' (hypPar k T' ⁻¹' E ∩ Set.univ ×ˢ Set.Ioc (-Real.pi) Real.pi) := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [ofLp_qFw_kapT k v, hypPar_toLp_arg_of_mem_hypS k T' v (hS hv)]
      exact ⟨hv, Complex.arg_mem_Ioc _⟩
    · rintro ⟨h1, h2⟩
      exact ⟨_, h1, kapT_hypPar_ofLp_qFw k T' hT' x h2⟩
  rw [hset, (qIso_measurePreserving k).measure_preimage hFm.nullMeasurableSet]
end GlobalTheory.HypChartPf
