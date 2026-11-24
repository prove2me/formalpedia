-- Prove2me | solution 1 for GlobalTheory.SplitWeil.nabs_lt_of_valuation_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:16.97921+00:00
-- url     : https://prove2.me/submissions/6d6d76fe-e038-4039-8e02-8f6c4ab82225

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Theorems.Thm_GlobalTheory_SplitWeil_one_lt_resCard
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_le_of_valuation_le
import Theorems.Thm_GlobalTheory_SplitWeil_mem_cball_uniformiser
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_uniformiser


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitWeil
theorem _root_.solution {x y : kˣ} (h : valuation k (x : k) < valuation k (y : k)) :
    nabs k x < nabs k y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  have hy0 : 0 < valuation k (y : k) := by simp [zero_lt_iff]
  have hlt : valuation k ((x : k) * (y : k)⁻¹) < 1 := by
    rw [map_mul, map_inv₀, mul_inv_lt_iff₀ hy0, one_mul]; exact h
  let z : 𝒪[k] := ⟨(x : k) * (y : k)⁻¹, (Valuation.mem_integer_iff _ _).mpr hlt.le⟩
  have hz : z ∈ 𝓂[k] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hlt
  have h1 : valuation k ((x : k) * (y : k)⁻¹) ≤ valuation k (ϖ : k) :=
    (mem_cball_uniformiser hϖ (x := Units.mk0 _ h0) rfl z).mpr hz
  have h2 : valuation k (x : k) ≤ valuation k ((Units.mk0 _ h0 * y : kˣ) : k) := by
    rw [map_mul, map_inv₀, mul_inv_le_iff₀ hy0] at h1
    rw [Units.val_mul, map_mul]
    exact h1
  have h3 := nabs_le_of_valuation_le h2
  rw [nabs_mul, nabs_uniformiser hϖ (x := Units.mk0 _ h0) rfl] at h3
  refine h3.trans_lt (mul_lt_of_lt_one_left (nabs_pos k y) (inv_lt_one_of_one_lt₀ ?_))
  exact_mod_cast one_lt_resCard k
end GlobalTheory.SplitWeil
