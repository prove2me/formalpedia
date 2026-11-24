-- Prove2me | solution 1 for GlobalTheory.isLatticeEmb_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:55:49.184526+00:00
-- url     : https://prove2.me/submissions/68ab594b-4190-46b0-9a59-0c5b1b2319b5

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
namespace GlobalTheory
theorem _root_.solution {Λ : Submodule (𝓞 K) (Fin r → K)} (hΛ : IsLattice Λ) :
    IsLatticeEmb Λ.subtype :=
  ⟨Λ.injective_subtype, by rwa [Submodule.range_subtype]⟩
end GlobalTheory
