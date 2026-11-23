-- Prove2me | solution 1 for GroundTheory.Global.valued_of_irreducible_integer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:37.099814+00:00
-- url     : https://prove2.me/submissions/4dc4d9c6-7bcf-44d8-acf6-695adba81fa5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Theorems.Thm_GroundTheory_Global_integers_valued
import Theorems.Thm_GroundTheory_Global_mem_maximalIdeal_iff_valued_lt_one
import Theorems.Thm_GroundTheory_Global_mem_valuationInteger_iff
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
theorem _root_.solution {ϖ : 𝒪[u.adicCompletion F]} (hϖ : Irreducible ϖ) :
    Valued.v (ϖ : u.adicCompletion F) = WithZero.exp (-1) := by
  apply le_antisymm
  · have h := (mem_maximalIdeal_iff_valued_lt_one u ϖ).1 hϖ.not_isUnit
    have h' : Valued.v (ϖ : u.adicCompletion F) < WithZero.exp (-1) * WithZero.exp 1 := by
      rwa [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    exact (WithZero.lt_mul_exp_iff_le (by simp)).1 h'
  · have hlt : WithZero.exp (-1 : ℤ) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    obtain ⟨y, hy⟩ := valuedAdicCompletion_surjective F u (WithZero.exp (-1))
    have hy1 : Valued.v y ≤ 1 := by rw [hy]; exact hlt.le
    let y' : 𝒪[u.adicCompletion F] := ⟨y, (mem_valuationInteger_iff u y).2 hy1⟩
    have hy' : y' ∈ 𝓂[u.adicCompletion F] := by
      rw [mem_maximalIdeal_iff_valued_lt_one]
      change Valued.v y < 1
      rw [hy]; exact hlt
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hy'
    obtain ⟨c, hc⟩ := hy'
    rw [← hy, show y = ((c * ϖ : 𝒪[u.adicCompletion F]) : u.adicCompletion F) by rw [hc],
      Subring.coe_mul, map_mul]
    exact mul_le_of_le_one_left zero_le ((integers_valued u).map_le_one c)
end GroundTheory.Global
