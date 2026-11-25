-- Prove2me | solution 1 for GroundTheory.Global.mem_maximalIdeal_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:57.021842+00:00
-- url     : https://prove2.me/submissions/b03bdce3-4fae-4905-98cf-68b2d0ae0a77

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Theorems.Thm_GroundTheory_Global_integers_valued
import Theorems.Thm_GroundTheory_Global_valued_of_irreducible_integer
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
namespace GroundTheory.Global
theorem _root_.solution (y : 𝒪[u.adicCompletion F]) (n : ℕ) :
    y ∈ 𝓂[u.adicCompletion F] ^ n ↔ Valued.v (y : u.adicCompletion F) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[u.adicCompletion F]
  have h := (integers_valued u).maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow hϖ n
  rw [← SetLike.mem_coe, h, Set.mem_ofPred_eq]
  change Valued.v (y : u.adicCompletion F) ≤ Valued.v (ϖ : u.adicCompletion F) ^ n ↔ _
  rw [valued_of_irreducible_integer u hϖ, ← WithZero.exp_nsmul]
  simp
end GroundTheory.Global
