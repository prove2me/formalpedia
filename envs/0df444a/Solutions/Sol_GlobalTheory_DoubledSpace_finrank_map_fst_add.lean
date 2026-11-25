-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.finrank_map_fst_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:26:18.396318+00:00
-- url     : https://prove2.me/submissions/30b2fe94-ee9b-49cf-bcdd-18d4afc2f28a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply



set_option autoImplicit false
open GlobalTheory
open Module
open GlobalTheory.DoubledSpace
variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] {σ : E →+* E}
namespace GlobalTheory.DoubledSpace
theorem _root_.solution [FiniteDimensional E W] (I : Submodule E (W × W)) :
    finrank E (I.map (LinearMap.fst E W W)) + finrank E (right I) = finrank E I := by
  have h1 := LinearMap.finrank_range_add_finrank_ker ((LinearMap.fst E W W).domRestrict I)
  rw [LinearMap.range_domRestrict] at h1
  rw [← h1]
  congr 1
  refine LinearEquiv.finrank_eq
    { toFun := fun y => ⟨⟨(0, y.1), y.2⟩, rfl⟩
      invFun := fun p => ⟨p.1.1.2, ?_⟩
      map_add' := fun a b => by ext <;> simp
      map_smul' := fun a b => by ext <;> simp
      left_inv := fun a => rfl
      right_inv := fun p => ?_ }
  · have e : p.1.1.1 = 0 := p.2
    rw [mem_right, ← e]; exact p.1.2
  · have e : p.1.1.1 = 0 := p.2
    ext <;> simp [e]
end GlobalTheory.DoubledSpace
