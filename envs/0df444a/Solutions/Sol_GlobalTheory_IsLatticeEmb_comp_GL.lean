-- Prove2me | solution 1 for GlobalTheory.IsLatticeEmb.comp_GL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:55:43.405853+00:00
-- url     : https://prove2.me/submissions/de4b4401-1ae7-4ebd-b4eb-3f028c46c215

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open NumberField Matrix
open ReciprocityTheory.MultiplicativeHeights (IsLattice)
open scoped TensorProduct nonZeroDivisors
variable {r : ℕ}
variable {K : Type} [Field K] [NumberField K]
variable {M M' : Type} [AddCommGroup M] [Module (𝓞 K) M] [AddCommGroup M'] [Module (𝓞 K) M']
open GlobalTheory.IsLatticeEmb
variable {φ : M →ₗ[𝓞 K] (Fin r → K)}
namespace GlobalTheory.IsLatticeEmb
theorem _root_.solution (h : IsLatticeEmb φ) (γ : GL (Fin r) K) :
    IsLatticeEmb (((γ : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars (𝓞 K)) ∘ₗ φ) := by
  have hγ : Function.Bijective (γ : Matrix (Fin r) (Fin r) K).mulVecLin :=
    ⟨mulVec_injective_iff_isUnit.mpr γ.isUnit, mulVec_surjective_iff_isUnit.mpr γ.isUnit⟩
  refine ⟨hγ.1.comp h.1, ?_, ?_⟩
  · rw [LinearMap.range_comp]; exact h.2.1.map _
  · rw [LinearMap.range_comp, Submodule.map_coe, LinearMap.coe_restrictScalars,
      ← Submodule.map_span, h.2.2, Submodule.map_top, LinearMap.range_eq_top.mpr hγ.2]
end GlobalTheory.IsLatticeEmb
