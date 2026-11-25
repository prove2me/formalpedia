-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.localIdeal_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:27:33.382723+00:00
-- url     : https://prove2.me/submissions/35b565ae-b862-40de-a6ea-d9d300495e67

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
import Theorems.Thm_GroundTheory_Global_mem_localIdeal_iff
import Theorems.Thm_GroundTheory_Global_IdeleGroup_valued_eq_exp_neg_ord
import Theorems.Thm_GroundTheory_Global_IdeleGroup_component_ne_zero
import Theorems.Thm_GroundTheory_Global_IdeleGroup_count_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (s : IdeleGroup K) (I : 𝓘) (v : HeightOneSpectrum (𝓞 K)) :
    localIdeal ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v =
      (localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) v).map
        (LinearMap.mulLeft (v.adicCompletionIntegers K) ((s : 𝔸[K]).2 v)) := by
  ext y
  rw [mem_localIdeal_iff (Units.ne_zero _), Submodule.mem_map, count_smul]
  have ht := component_ne_zero v s
  constructor
  · intro hy
    refine ⟨((s : 𝔸[K]).2 v)⁻¹ * y, ?_, ?_⟩
    · rw [mem_localIdeal_iff (Units.ne_zero _), map_mul, map_inv₀, valued_eq_exp_neg_ord]
      calc (exp (-ord v s))⁻¹ * Valued.v y
          ≤ (exp (-ord v s))⁻¹ * exp (-(ord v s + count K v (I : FractionalIdeal (𝓞 K)⁰ K))) :=
            mul_le_mul_right hy _
        _ = exp (-count K v (I : FractionalIdeal (𝓞 K)⁰ K)) := by
            rw [← exp_neg, neg_neg, ← exp_add]
            congr 1
            ring
    · rw [LinearMap.mulLeft_apply, mul_inv_cancel_left₀ ht]
  · rintro ⟨z, hz, rfl⟩
    rw [mem_localIdeal_iff (Units.ne_zero _)] at hz
    rw [LinearMap.mulLeft_apply, map_mul, valued_eq_exp_neg_ord, neg_add, exp_add]
    exact mul_le_mul_right hz _
end GroundTheory.Global.IdeleGroup
