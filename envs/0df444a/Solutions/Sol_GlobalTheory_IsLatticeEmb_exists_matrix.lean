-- Prove2me | solution 1 for GlobalTheory.IsLatticeEmb.exists_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:31:06.335588+00:00
-- url     : https://prove2.me/submissions/90c07790-d0c7-4a1a-9327-3acc98e54229

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice
import Theorems.Thm_GlobalTheory_IsLatticeEmb_isBaseChange

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
theorem _root_.solution {s : ℕ} (h : IsLatticeEmb φ) (g : M →ₗ[𝓞 K] (Fin s → K)) :
    ∃ A : Matrix (Fin s) (Fin r) K, ∀ x, A *ᵥ φ x = g x :=
  ⟨LinearMap.toMatrix' (h.isBaseChange.lift g), fun x => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix', IsBaseChange.lift_eq]⟩
end GlobalTheory.IsLatticeEmb
