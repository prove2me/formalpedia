-- Prove2me | solution 1 for GlobalTheory.T.exists_pos_pow_galois_fixing_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:58:14.365614+00:00
-- url     : https://prove2.me/submissions/bdcf9b67-0a1e-4a96-9ad5-b76e8c32a22d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPosPowGaloisFixingFinset
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPosPowGaloisFixingFinsetStatement
import Theorems.Thm_GlobalTheory_PowFix_exists_pos_pow_fix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (σ : G E Ω) (s : Finset Ω), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ s, (σ ^ m) x = x := by
  first | exact @GlobalTheory.PowFix.exists_pos_pow_fix | exact GlobalTheory.PowFix.exists_pos_pow_fix | (intros; apply GlobalTheory.PowFix.exists_pos_pow_fix <;> assumption)
end _root_.GlobalTheory.T
