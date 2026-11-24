-- Prove2me | solution 1 for GlobalTheory.LocalQuad.exists_norm_over_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:27:07.618902+00:00
-- url     : https://prove2.me/submissions/df7314f2-406d-48a5-920e-1216db65b6fa

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuaternaryOfCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuedTernaryLtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRingHomAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalQuad_exists_norm_of_quaternary
import Theorems.Thm_GlobalTheory_LocalQuad_exists_ringHom_adicCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
namespace GlobalTheory.LocalQuad
theorem _root_.solution (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F]
    (L : Type) [Field L] [NumberField L] [Algebra F L] {α β γ : F} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hγ : γ ≠ 0) {s : L} (hs : s ^ 2 = algebraMap F L (α * β * γ))
    (hr : ∀ σ : F →+* ℝ, ∃ x y z t : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
      x ^ 2 - σ α * y ^ 2 - σ β * z ^ 2 + σ γ * t ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x y z t : v.adicCompletion F,
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
      x ^ 2 - algebraMap F _ α * y ^ 2 - algebraMap F _ β * z ^ 2 + algebraMap F _ γ * t ^ 2 = 0) :
    ∃ X Y : L, algebraMap F L β = X ^ 2 - algebraMap F L α * Y ^ 2 := by
  refine H L _ _ (by simpa using hα) (by simpa using hβ) (fun σ => ?_) (fun w => ?_)
  · obtain ⟨x, y, z, t, h0, h⟩ := hr (σ.comp (algebraMap F L))
    exact exists_norm_of_quaternary (s := σ s) (γ := σ (algebraMap F L γ)) (by simpa using hα)
      (by simpa using hβ) (by simpa using hγ) (by rw [← map_pow, hs]; simp) h0 h
  · haveI : CharZero (w.adicCompletion L) :=
      charZero_of_injective_algebraMap (algebraMap L (w.adicCompletion L)).injective
    obtain ⟨v, φ, hφ⟩ := exists_ringHom_adicCompletion F L w
    obtain ⟨x, y, z, t, h0, h⟩ := hf v
    refine exists_norm_of_quaternary (s := algebraMap L _ s)
      (γ := algebraMap L _ (algebraMap F L γ)) (x := φ x) (y := φ y) (z := φ z) (t := φ t)
      (by simpa using hα) (by simpa using hβ) (by simpa using hγ)
      (by rw [← map_pow, hs]; simp only [map_mul]) (by simpa using h0) ?_
    have := congrArg φ h
    simpa only [map_add, map_sub, map_mul, map_pow, hφ, map_zero] using this
end GlobalTheory.LocalQuad
