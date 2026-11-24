-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.gaussQ_continuous_rapidDecay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:29:54.308824+00:00
-- url     : https://prove2.me/submissions/5a0cf161-70e4-4cb6-a805-b444ce725e81

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianContinuousRapidDecay
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_GaussReg_exists_lower_family
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_GaussReg_exp_mul_pow_le
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_sizeTup_eq_sum_xw
import Theorems.Thm_GlobalTheory_T_infinite_adeles_local_ring_totally_real
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB
open GaussReg
namespace GlobalTheory.CompanionTheory.SW.BB
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ y w, |e y w| = ‖y w‖) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ), Continuous (gaussQ e b Pm) ∧ ((∀ w, (Pm w).PosDef) → RapidDecay b (fun X => (gaussQ e b Pm X : ℂ))) := by
  intro F E _ _ _ _ _ σ hCM M d b e hom he Pm
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, -, -, -, hco, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  have hxw : ∀ w p, Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => xw e b X w p := by
    intro w p
    have h := (hco d b).continuous
    exact (continuous_apply w).comp (hom.continuous.comp ((continuous_apply p.2).comp
      (h.comp ((continuous_apply p.1).comp (continuous_apply 0)))))
  have hxw' : ∀ w, Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => xw e b X w := fun w =>
    continuous_pi (hxw w)
  refine ⟨?_, fun hP N => ?_⟩
  · unfold gaussQ
    refine Real.continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun w _ => ?_))
    exact (hxw' w).dotProduct (Continuous.matrix_mulVec continuous_const (hxw' w))
  · obtain ⟨c, hc, hlow⟩ := exists_lower_family hP
    refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * (Real.pi * c))), fun X => ?_⟩
    have hs := sizeTup_eq_sum_xw b e he X
    have hs0 : 0 ≤ sizeTup b X := by
      rw [hs]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hq := hlow fun w => xw e b X w
    rw [← hs] at hq
    have hn : ‖((gaussQ e b Pm X : ℝ) : ℂ)‖ = gaussQ e b Pm X := by
      rw [Complex.norm_real, gaussQ, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [hn]
    have key := exp_mul_pow_le (a := Real.pi * c) (mul_pos Real.pi_pos hc) N hs0
      (q := Real.pi * ∑ w, xw e b X w ⬝ᵥ (Pm w *ᵥ xw e b X w))
      (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hq Real.pi_pos.le)
    simpa [gaussQ, neg_mul] using key
end GlobalTheory.CompanionTheory.SW.BB
