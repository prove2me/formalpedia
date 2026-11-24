-- Prove2me | solution 1 for GlobalTheory.UnramCocycle.conj_mem_ine_of_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:52.528817+00:00
-- url     : https://prove2.me/submissions/06320a1d-701a-4ca2-9048-66063ef2f79a

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleUnramifiedOutsideVanishOnKernel
import Theorems.Thm_ReciprocityTheory_Gal_mem_Ine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open Pointwise
open GlobalTheory GlobalTheory.UnramCocycle
namespace GlobalTheory.UnramCocycle
theorem _root_.solution {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (g σ : G F Ω) (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  rw [mem_Ine] at hσ ⊢
  obtain ⟨hdec, hval⟩ := hσ

  have hmem : ∀ y : Ω, y ∈ g • A ↔ g⁻¹ y ∈ A := fun y =>
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
  have hgg : ∀ y : Ω, g⁻¹ (g y) = y := fun y => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  refine ⟨?_, fun x hx => ?_⟩
  · have h' : σ • (g • A) = g • A := hdec
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h', inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, hmem, hgg]
      exact (ValuationSubring.valuation_le_one_iff A x).1 hx
    have hy := hval (g x) hx'
    have e : (g⁻¹ * σ * g) x - x = g⁻¹ (σ (g x) - g x) := by
      rw [map_sub, hgg, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    rw [e]
    rw [valuation_lt_one_iff'] at hy ⊢
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨(hmem _).1 hy1, ?_⟩
    rcases hy2 with h0 | h0
    · left
      rw [h0, map_zero]
    · right
      rwa [← map_inv₀, ← hmem]
end GlobalTheory.UnramCocycle
