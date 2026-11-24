-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittE.exists_mem_UJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:58:36.186156+00:00
-- url     : https://prove2.me/submissions/bea511b6-f6bd-4c73-83e2-eb61538d4aaf

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_formB_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_cT_mul_mul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.WittE
variable {E : Type} [Field E]
namespace GlobalTheory.CompanionTheory.SW.WittE
theorem _root_.solution (s : E →+* E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0)
    (γ : (Fin M → E) →ₗ[E] (Fin M → E)) (hγ : IsIsom (formB s J) γ) :
    ∃ g ∈ UJ s J, ∀ z, (g : Matrix (Fin M) (Fin M) E) *ᵥ z = γ z := by
  set m := LinearMap.toMatrix' γ with hm
  have hmv : ∀ z, m *ᵥ z = γ z := fun z => LinearMap.toMatrix'_mulVec γ z
  have hu : cT s m * J * m = J := by
    ext i j
    have hcol : ∀ i, (fun k => m k i) = γ (Pi.single i 1) := by
      intro i
      rw [← hmv]
      ext k
      simp
    rw [cT_mul_mul_apply, hcol, hcol, ← formB_apply, hγ, formB_apply]
    simp [hform, Pi.single_apply]
  have hdet : m.det ≠ 0 := by
    intro h0
    apply hJ
    have := congrArg Matrix.det hu
    rw [Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero m hdet, ?_, hmv⟩
  exact hu
end GlobalTheory.CompanionTheory.SW.WittE
