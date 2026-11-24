-- Prove2me | solution 1 for GlobalTheory.CMVal.ValEx.isOpen_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:55.787885+00:00
-- url     : https://prove2.me/submissions/e253644b-2b43-4609-9545-46777bfcd426

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Theorems.Thm_GlobalTheory_CMVal_ValEx_continuous_val
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
variable {E : Type} [Field E] [NumberField E]
open WithZeroTopology
namespace GlobalTheory.CMVal.ValEx
theorem _root_.solution (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    IsOpen (cong (Valued.v : Valuation (w.adicCompletion E) ℤᵐ⁰) n : Set (w.adicCompletion E)ˣ) := by
  have h1 : IsOpen ({1} : Set ℤᵐ⁰) := WithZeroTopology.isOpen_iff.2 (Or.inl (by simp))
  have h2 : IsOpen (Set.Iic (WithZero.exp (-(n : ℤ)))) :=
    WithZeroTopology.isOpen_iff.2 (Or.inr ⟨_, WithZero.exp_ne_zero, Set.Iio_subset_Iic_self⟩)
  exact (h1.preimage ((continuous_val w).comp Units.continuous_val)).inter
    (h2.preimage ((continuous_val w).comp (Units.continuous_val.sub continuous_const)))
end GlobalTheory.CMVal.ValEx
