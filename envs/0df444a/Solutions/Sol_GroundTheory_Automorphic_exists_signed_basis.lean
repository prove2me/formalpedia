-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_signed_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:29:29.123149+00:00
-- url     : https://prove2.me/submissions/068878a1-8cb3-4efe-bada-862ee8123a99

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (L : LieSubalgebra ℝ (Matrix ι ι 𝕜))
variable {L}
namespace GroundTheory.Automorphic
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x) {s : ℝ} (hs : s * s = 1)
    (hpos : ∀ v : V, v ≠ 0 → 0 < s * B v v) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      ∀ i j, B (b i) (b j) = if i = j then s else 0 := by
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B)
    ⟨fun x y => by rw [RingHom.id_apply]; exact hB x y⟩
  have hpos' : ∀ i, 0 < s * B (v i) (v i) := fun i => hpos _ (v.ne_zero i)
  set w : Fin (Module.finrank ℝ V) → ℝ := fun i => (Real.sqrt (s * B (v i) (v i)))⁻¹
  have hw : ∀ i, IsUnit (w i) := fun i =>
    (inv_ne_zero (Real.sqrt_pos.2 (hpos' i)).ne').isUnit
  refine ⟨v.isUnitSMul hw, fun i j => ?_⟩
  rw [Module.Basis.isUnitSMul_apply, Module.Basis.isUnitSMul_apply, map_smul, map_smul,
    LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  split_ifs with hij
  · subst hij
    have hsq : Real.sqrt (s * B (v i) (v i)) ^ 2 = s * B (v i) (v i) := Real.sq_sqrt (hpos' i).le
    have hst : s * B (v i) (v i) ≠ 0 := (hpos' i).ne'
    have ht : B (v i) (v i) ≠ 0 := right_ne_zero_of_mul hst
    simp only [w]
    rw [← mul_assoc, ← sq, inv_pow, hsq, mul_inv, mul_assoc, inv_mul_cancel₀ ht, mul_one]
    exact inv_eq_of_mul_eq_one_right hs
  · rw [hv hij, mul_zero, mul_zero]
end GroundTheory.Automorphic
