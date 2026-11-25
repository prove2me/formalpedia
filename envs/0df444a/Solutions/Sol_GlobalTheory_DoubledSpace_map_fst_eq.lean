-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.map_fst_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:42:38.917633+00:00
-- url     : https://prove2.me/submissions/32f358a1-ac2d-4592-ad8e-957fa5481c35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_DoubledSpace_finrank_add_finrank_orthogonal
import Theorems.Thm_GlobalTheory_DoubledSpace_finrank_map_fst_add
import Theorems.Thm_GlobalTheory_DoubledSpace_map_fst_le
import Theorems.Thm_GlobalTheory_DoubledSpace_finrank_left_eq_finrank_right
import Theorems.Thm_GlobalTheory_IsSaturatedSubmodule_eq_of_le_of_finrank_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
open GlobalTheory.DoubledSpace
variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] {σ : E →+* E}
variable {h : W →ₗ[E] W →ₛₗ[σ] E} {I : Submodule E (W × W)}
variable [FiniteDimensional E W] (hσ : Function.Involutive σ) (hh : ∀ x y, σ (h x y) = h y x)
  (hn : ∀ x, (∀ y, h x y = 0) → x = 0) (hI : ∀ p ∈ I, ∀ q ∈ I, form h p q = 0)
  (hd : finrank E I = finrank E W)
include hσ hh hn hI hd
namespace GlobalTheory.DoubledSpace
theorem _root_.solution : I.map (LinearMap.fst E W W) = (left I).orthogonalBilin h := by
  refine Submodule.eq_of_le_of_finrank_eq (map_fst_le hI) ?_
  have a := finrank_map_fst_add I
  have e := finrank_add_finrank_orthogonal hσ hh hn (left I)
  have f := finrank_left_eq_finrank_right hσ hh hn hI hd
  omega
end GlobalTheory.DoubledSpace
