-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.measure_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:39:36.078679+00:00
-- url     : https://prove2.me/submissions/550b3815-5343-404f-bde3-799f7b109060

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_VolFreePerLatStdLat
import Theorems.Thm_GlobalTheory_SplitWeil_measure_cball
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_uniformiser


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution [MeasurableSpace k] [BorelSpace k] {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ)
    (ν : Measure k) (hν : IsUnitVol ν) (m : ℕ) :
    ν {x | (ϖ : k) ^ m * x ∈ 𝒪[k]} = (resCard k : ENNReal) ^ m := by
  have := hν.1
  have h0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  set u : kˣ := Units.mk0 (ϖ : k) h0 with hu
  have hset : {x | (ϖ : k) ^ m * x ∈ 𝒪[k]} = cball (u⁻¹ ^ m) := by
    ext x
    have hv : 0 < valuation k (ϖ : k) ^ m := pow_pos ((Valuation.pos_iff _).2 h0) m
    simp only [Set.mem_ofPred_eq, cball, Valuation.mem_integer_iff, map_mul, map_pow, hu,
      Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, inv_pow]
    rw [← one_div, le_div_iff₀ hv, mul_comm]
  have h1 : distribHaarChar k u⁻¹ = (resCard k : NNReal) := by
    have := nabs_uniformiser hϖ (x := u) rfl
    rw [map_inv]
    apply NNReal.coe_injective
    rw [NNReal.coe_inv]
    simp only [nabs] at this
    rw [this]
    simp
  rw [hset, measure_cball, hν.2, mul_one, map_pow, h1]
  simp
end GlobalTheory.RootEx.UnfoldShape
