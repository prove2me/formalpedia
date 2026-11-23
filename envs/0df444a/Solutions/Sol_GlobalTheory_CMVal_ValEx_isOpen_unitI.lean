-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.isOpen_unitI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:55.152394+00:00
-- url     : https://prove2.me/submissions/507c4c2c-b671-4832-85d4-42986ce3e54a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Theorems.Thm_GlobalTheory_CMVal_ValEx_continuous_val
import Theorems.Thm_GlobalTheory_CMVal_ValEx_continuous_finOf
import Theorems.Thm_GlobalTheory_CMVal_ValEx_mem_unitI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution : IsOpen (unitI (E := E) : Set (Ideles E)) := by
  have hO : IsOpen {a : Af E | ∀ v, a v ∈ v.adicCompletionIntegers E} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  convert (hO.preimage (Units.continuous_val.comp continuous_finOf)).inter
    (hO.preimage (Units.continuous_val.comp (continuous_finOf.comp continuous_inv))) using 1
  ext x
  constructor
  · intro h
    exact ⟨fun P => (mem_unitI.1 h P).le, fun P => (mem_unitI.1 (unitI.inv_mem h) P).le⟩
  · rintro ⟨h1, h2⟩
    refine mem_unitI.2 fun P => le_antisymm (h1 P) ?_
    have h3 : Valued.v (((locU P (finOf x⁻¹) : (P.adicCompletion E)ˣ)) : P.adicCompletion E) ≤ 1 := h2 P
    rw [map_inv, map_inv, Units.val_inv_eq_inv_val, map_inv₀] at h3
    exact (inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (locU P (finOf x)).ne_zero))).1 h3
end GlobalTheory.CMVal.ValEx
