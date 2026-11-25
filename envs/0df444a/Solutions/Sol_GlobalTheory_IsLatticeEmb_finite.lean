-- Prove2me | solution 1 for GlobalTheory.IsLatticeEmb.finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:54:09.726365+00:00
-- url     : https://prove2.me/submissions/13d84df9-914a-479c-812a-b60e8b4e34bf

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
theorem _root_.solution (h : IsLatticeEmb φ) : Module.Finite (𝓞 K) M := by
  have : Module.Finite (𝓞 K) (LinearMap.range φ) := Module.Finite.iff_fg.mpr h.2.1
  exact Module.Finite.equiv (LinearEquiv.ofInjective φ h.1).symm
end GlobalTheory.IsLatticeEmb
