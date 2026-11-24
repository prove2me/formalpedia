-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimInf.exists_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:29:33.077627+00:00
-- url     : https://prove2.me/submissions/2b9b54df-3ba9-4a55-beef-a28c7d55d1c5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanPrimitiveVectorCompactRescale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimInf
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.PrimInf
theorem _root_.solution (ρ : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ) (hρc : ∀ w, Continuous (ρ w))
    (hρs : ∀ w, Continuous (ρ w).symm) (t : InfinitePlace F → ℂ) (htre : ∀ w, (t w).re = 0)
    (htim : ∀ w, (t w).im ≠ 0) :
    ∃ Ψ : (Fin 2 → Ainf F) ≃ₜ (InfinitePlace F → ℂ),
      ∀ p w, Ψ p w = ((ρ w (p 0 w) : ℝ) : ℂ) + ((ρ w (p 1 w) : ℝ) : ℂ) * t w := by
  let inv : (InfinitePlace F → ℂ) → Fin 2 → Ainf F := fun z k =>
    if k = 0 then fun w => (ρ w).symm (z w).re else fun w => (ρ w).symm ((z w).im / (t w).im)
  have hinv0 : ∀ z w, inv z 0 w = (ρ w).symm (z w).re := fun z w => rfl
  have hinv1 : ∀ z w, inv z 1 w = (ρ w).symm ((z w).im / (t w).im) := fun z w => rfl
  let fwd : (Fin 2 → Ainf F) → InfinitePlace F → ℂ :=
    fun p w => ((ρ w (p 0 w) : ℝ) : ℂ) + ((ρ w (p 1 w) : ℝ) : ℂ) * t w
  have hre : ∀ p w, (fwd p w).re = ρ w (p 0 w) := fun p w => by
    simp [fwd, htre w]
  have him : ∀ p w, (fwd p w).im = ρ w (p 1 w) * (t w).im := fun p w => by
    simp [fwd]
  have hl : Function.LeftInverse inv fwd := by
    intro p
    funext k
    revert k
    rw [Fin.forall_fin_two]
    constructor
    · funext w
      rw [hinv0, hre, RingEquiv.symm_apply_apply]
    · funext w
      rw [hinv1, him, mul_div_cancel_right₀ _ (htim w), RingEquiv.symm_apply_apply]
  have hr : Function.RightInverse inv fwd := by
    intro z
    funext w
    apply Complex.ext
    · rw [hre, hinv0, RingEquiv.apply_symm_apply]
    · rw [him, hinv1, RingEquiv.apply_symm_apply, div_mul_cancel₀ _ (htim w)]
  have hc1 : Continuous fwd := by
    refine continuous_pi fun w => ?_
    have hc : ∀ k : Fin 2, Continuous fun p : Fin 2 → Ainf F => ((ρ w (p k w) : ℝ) : ℂ) := fun k =>
      Complex.continuous_ofReal.comp
        ((hρc w).comp ((continuous_apply w).comp (continuous_apply k)))
    exact (hc 0).add ((hc 1).mul continuous_const)
  have hc2 : Continuous inv := by
    refine continuous_pi fun k => ?_
    revert k
    rw [Fin.forall_fin_two]
    constructor
    · refine continuous_pi fun w => ?_
      exact (hρs w).comp (Complex.continuous_re.comp (continuous_apply w))
    · refine continuous_pi fun w => ?_
      exact (hρs w).comp ((Complex.continuous_im.comp (continuous_apply w)).div_const _)
  exact ⟨⟨⟨fwd, inv, hl, hr⟩, hc1, hc2⟩, fun _ _ => rfl⟩
end GlobalTheory.CompanionTheory.SW.PrimInf
