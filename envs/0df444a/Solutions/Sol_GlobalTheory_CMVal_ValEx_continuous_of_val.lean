-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.continuous_of_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:33.080156+00:00
-- url     : https://prove2.me/submissions/fb683b52-4e87-4973-ac75-5a34f08656f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
open WithZeroTopology
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution {K L : Type} [Field K] [Field L] [Valued K ℤᵐ⁰] [Valued L ℤᵐ⁰]
    (hK : Function.Surjective (Valued.v : K → ℤᵐ⁰)) (f : K →+* L) (hf : ∀ x, Valued.v (f x) = Valued.v x) :
    Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have ho : IsOpen {x : K | Valued.v x < MonoidWithZeroHom.ValueGroup₀.embedding γ.1} :=
    WithZeroTopology.isOpen_Iio.preimage (Valued.continuous_valuation_of_surjective hK)
  filter_upwards [ho.mem_nhds (by simp [zero_lt_iff])] with x hx
  rw [Valuation.restrict_lt_iff_lt_embedding, hf]
  exact hx
end GlobalTheory.CMVal.ValEx
