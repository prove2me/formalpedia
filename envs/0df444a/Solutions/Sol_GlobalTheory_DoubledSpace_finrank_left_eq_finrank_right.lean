-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.finrank_left_eq_finrank_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:34:13.611005+00:00
-- url     : https://prove2.me/submissions/7fb8f073-2eef-423b-8d19-65d119575911

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_DoubledSpace_finrank_add_finrank_orthogonal
import Theorems.Thm_GlobalTheory_DoubledSpace_finrank_map_fst_add
import Theorems.Thm_GlobalTheory_DoubledSpace_finrank_map_snd_add
import Theorems.Thm_GlobalTheory_DoubledSpace_map_fst_le
import Theorems.Thm_GlobalTheory_DoubledSpace_map_snd_le

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
theorem _root_.solution : finrank E (left I) = finrank E (right I) := by
  have a := finrank_map_fst_add I
  have b := finrank_map_snd_add I
  have c := Submodule.finrank_mono (map_fst_le hI)
  have d := Submodule.finrank_mono (map_snd_le hI)
  have e := finrank_add_finrank_orthogonal hσ hh hn (left I)
  have f := finrank_add_finrank_orthogonal hσ hh hn (right I)
  omega
end GlobalTheory.DoubledSpace
