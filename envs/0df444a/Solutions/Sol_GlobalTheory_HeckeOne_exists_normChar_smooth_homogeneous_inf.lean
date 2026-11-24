-- Prove2me | solution 1 for GlobalTheory.HeckeOne.exists_normChar_smooth_homogeneous_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:35:32.166472+00:00
-- url     : https://prove2.me/submissions/069ce5e0-c586-49cd-96ee-5593aa9fd78f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExtensionEmbeddingMixedSymmOfIsComplex
import Theorems.Thm_GlobalTheory_HeckeOne_continuous_mixedIdele
import Theorems.Thm_GlobalTheory_HeckeOne_mixedIdele_mixedEmbedding
import Theorems.Thm_GlobalTheory_HeckeOne_exists_trivial_on_expScalar
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_HeckeOne_isUnitary_normChar
import Theorems.Thm_GlobalTheory_exists_smooth_mul_extension_of_continuous_char
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (Ideles)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm)
open GlobalTheory GlobalTheory.HeckeOne
variable (K : Type) [Field K] [NumberField K]
variable {K}
namespace GlobalTheory.HeckeOne
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), χ.IsUnitary → ∃ (t : ℝ) (φ : mixedSpace K → ℂ), (∀ x y, φ (x * y) = φ x * φ y) ∧ (∀ (r : ℝ) x, 0 < r → φ (r • x) = φ x) ∧ ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) ∧ ∀ k : Kˣ, φ (mixedEmbedding K (k : K)) = ((((χ * GlobalTheory.HeckeOne.normChar K (-t)).inf k : ℂˣ) : ℂ))⁻¹ := by
  intro K _ _ χ hχ
  obtain ⟨t, ht⟩ := exists_trivial_on_expScalar χ hχ
  let ξ : HChar K := χ * normChar K (-t)
  have hξ : ξ.IsUnitary := fun x => by
    change ‖((χ.1 x : ℂˣ) : ℂ) * (((normChar K (-t)).1 x : ℂˣ) : ℂ)‖ = 1
    rw [norm_mul, hχ x, isUnitary_normChar (-t) x, mul_one]
  obtain ⟨φ, hmul, hsm, hu, hiff⟩ := GlobalTheory.exists_smooth_mul_extension_of_continuous_char K ((ξ⁻¹).1.comp (mixedIdele K))
    ((ξ⁻¹).2.1.comp (continuous_mixedIdele K))
  have hu' : ∀ u : (mixedSpace K)ˣ, φ u = ((ξ.1 (mixedIdele K u) : ℂˣ) : ℂ)⁻¹ := fun u => by
    rw [hu, ← Units.val_inv_eq_inv_val]
    rfl
  refine ⟨t, φ, hmul, fun r x hr => ?_, hsm, fun x hx => ?_, fun k => ?_⟩
  · have h1 : r • x = (expScalar K (Real.log r) : mixedSpace K) * x := by
      change _ = algebraMap ℝ (mixedSpace K) (Real.exp (Real.log r)) * x
      rw [Real.exp_log hr, Algebra.smul_def]
    rw [h1, hmul, hu', ht]
    simp
  · obtain ⟨u, rfl⟩ := (hiff x).1 hx
    rw [hu', norm_inv, hξ, inv_one]
  · have := hu' (Units.map (mixedEmbedding K).toMonoidHom k)
    rw [mixedIdele_mixedEmbedding] at this
    exact this
end GlobalTheory.HeckeOne
