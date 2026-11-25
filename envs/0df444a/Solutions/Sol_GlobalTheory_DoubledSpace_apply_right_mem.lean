-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.apply_right_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:54:29.248486+00:00
-- url     : https://prove2.me/submissions/6de1b3f9-de7c-48e0-9bd4-5aa08383f208

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_DoubledSpace_map_snd_le
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
variable {h : W →ₗ[E] W →ₛₗ[σ] E} {I : Submodule E (W × W)}
variable [FiniteDimensional E W] (hσ : Function.Involutive σ) (hh : ∀ x y, σ (h x y) = h y x)
  (hn : ∀ x, (∀ y, h x y = 0) → x = 0) (hI : ∀ p ∈ I, ∀ q ∈ I, form h p q = 0)
  (hd : finrank E I = finrank E W)
include hσ hh hn hI hd
omit hσ hh hn hd [FiniteDimensional E W]
namespace GlobalTheory.DoubledSpace
theorem _root_.solution {u : W → W}
    (hu : ∀ y ∈ (right I).orthogonalBilin h, u y - y ∈ right I) {x y : W} (hp : (x, y) ∈ I) :
    (x, u y) ∈ I := by
  have := I.add_mem hp (hu y (map_snd_le hI ⟨_, hp, rfl⟩))
  simpa using this
end GlobalTheory.DoubledSpace
