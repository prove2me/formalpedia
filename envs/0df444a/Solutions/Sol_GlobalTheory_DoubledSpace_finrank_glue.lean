-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.finrank_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:58:33.205747+00:00
-- url     : https://prove2.me/submissions/8b847bd8-c9c6-4d25-9448-43560ad6c071

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_DoubledSpace_finrank_add_finrank_orthogonal
import Theorems.Thm_GlobalTheory_DoubledSpace_finrank_map_fst_add
import Theorems.Thm_GlobalTheory_DoubledSpace_right_glue
import Theorems.Thm_GlobalTheory_DoubledSpace_map_fst_glue
import Theorems.Thm_GlobalTheory_DoubledSpace_finrank_reduced

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
variable {h : W →ₗ[E] W →ₛₗ[σ] E} {X X' : Submodule E W}
variable [FiniteDimensional E W] (hσ : Function.Involutive σ) (hh : ∀ x y, σ (h x y) = h y x)
  (hn : ∀ x, (∀ y, h x y = 0) → x = 0)
include hσ hh hn
namespace GlobalTheory.DoubledSpace
theorem _root_.solution (hX : ∀ x ∈ X, ∀ x' ∈ X, h x x' = 0) (hX' : ∀ x ∈ X', ∀ x' ∈ X', h x x' = 0)
    (φ : Reduced h X ≃ₗ[E] Reduced h X') : finrank E (glue h X X' φ) = finrank E W := by
  have a := finrank_map_fst_add (glue h X X' φ)
  rw [map_fst_glue, right_glue hX'] at a
  have b := finrank_reduced hσ hh hn hX
  have c := finrank_reduced hσ hh hn hX'
  have d := φ.finrank_eq
  have e := finrank_add_finrank_orthogonal hσ hh hn X
  omega
end GlobalTheory.DoubledSpace
