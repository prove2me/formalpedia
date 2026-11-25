-- Prove2me | solution 1 for GlobalTheory.PDiv.primTangent_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:10.543887+00:00
-- url     : https://prove2.me/submissions/2e499b5f-a8cc-4245-9b54-61dc4863db77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionCartierDualTangentBijective
import Theorems.Thm_GlobalTheory_PDiv_mem_ker_cobOne_of_mul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_succ
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_zero
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_id
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_mk
import Theorems.Thm_GlobalTheory_PDivGroup_rigLevel_mk
import Theorems.Thm_GlobalTheory_PDiv_SemiBialgHom_levelRig_mk
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.PDiv.SemiBialgHom.levelRig_mk
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT
attribute [local simp] GlobalTheory.PDivGroup.resOne_succ
attribute [local simp] GlobalTheory.PDivGroup.resOne_zero
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_id
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_mk
attribute [local simp] GlobalTheory.PDivGroup.rigLevel_mk



set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.PDiv
namespace GlobalTheory.PDiv
theorem _root_.solution {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] :
    Function.Bijective (primTangent R A) := by
  constructor
  · intro b b' hbb
    refine Subtype.ext (CartierDual.eq_of_forall_apply (R := R) fun φ => ?_)
    rw [← primTangent_d b φ, ← primTangent_d b' φ, hbb]
  · intro l
    let δ : CartierDual R A →ₗ[R] R := l ∘ₗ AugCot.d (counitAlgHom R (CartierDual R A))
    obtain ⟨a, ha⟩ := (CartierDual.toBidual_bijective (R := R) (M := A)).2 (toConv δ)
    have hδ : ∀ φ : CartierDual R A, φ a = δ φ := fun φ => by
      have := congrArg (fun x => x φ) ha
      simpa using this
    have hmem : a ∈ LinearMap.ker (cobOne R A) := mem_ker_cobOne_of_mul fun φ ψ => by
      rw [hδ, hδ, hδ]
      simp only [δ, LinearMap.comp_apply, AugCot.d_mul, map_add, map_smul, smul_eq_mul]
      rfl
    refine ⟨⟨a, hmem⟩, AugCot.hom_ext fun φ => ?_⟩
    rw [primTangent_d]
    exact hδ φ
end GlobalTheory.PDiv
