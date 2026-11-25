-- Prove2me | solution 1 for GlobalTheory.CuspGL.sum_coef_mul_eq_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:56:41.750192+00:00
-- url     : https://prove2.me/submissions/d3357abf-c03d-4f20-9a19-799be5657036

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingSelfIrreducibleAlgClosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_StarVirtualCharacterEqApplyInvStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIntCoeffPrimitiveGLCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGLStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyOfIrreduciStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingEqZeroOfDistinctIrreduStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndomorphismInnerProductPrimitiveMobiuStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OrthogonalIntVectorsNotAgreeOnRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsTeichmullerMapAlgebraicClosureFiniteFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusCharacterOrthogonalityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqOfIsPrimitiveOfEqOnEllipticFiniteGL
import Theorems.Thm_GlobalTheory_CuspGL_generalLinearGroupCardComplex_finiteField_ne_zero
import Theorems.Thm_GlobalTheory_BI_isChar_mem_virt_complex
import Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_ipGL_psi_eq
import Theorems.Thm_GlobalTheory_CuspGL_expand_primitive
import Theorems.Thm_GlobalTheory_CuspGL_extZero_spec
import Theorems.Thm_GlobalTheory_CuspGL_rootSum_isAdditive_and_pow_X_sub_one
import Theorems.Thm_GlobalTheory_CuspGL_star_virt_eq_inv
import Theorems.Thm_GlobalTheory_isChar_restrict_conj_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
open Polynomial
namespace GlobalTheory.CuspGL
namespace _root_.GlobalTheory.CuspGL
theorem _root_.solution (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (d : ℕ) (hd : 0 < d)
    (χ χ' : GL (Fin d) F → ℂ) (h : _root_.GlobalTheory.BI.IsChar ℂ ℂ χ) (h' : _root_.GlobalTheory.BI.IsChar ℂ ℂ χ')
    (hp : _root_.GlobalTheory.CuspGL.IsPrimitive (_root_.GlobalTheory.CuspGL.extZero χ)) (hp' : _root_.GlobalTheory.CuspGL.IsPrimitive (_root_.GlobalTheory.CuspGL.extZero χ')) (a b : ℕ → ℤ)
    (ha : ∀ k : ℕ, _root_.GlobalTheory.CuspGL.ipGL (_root_.GlobalTheory.CuspGL.extZero χ) (fun g : Module.End F (Fin d → F) => _root_.GlobalTheory.CuspGL.rootSum θ k (LinearMap.charpoly g))
      = a k * _root_.GlobalTheory.CuspGL.glCard F d)
    (hb : ∀ k : ℕ, _root_.GlobalTheory.CuspGL.ipGL (_root_.GlobalTheory.CuspGL.extZero χ') (fun g : Module.End F (Fin d → F) => _root_.GlobalTheory.CuspGL.rootSum θ k (LinearMap.charpoly g))
      = b k * _root_.GlobalTheory.CuspGL.glCard F d) :
    ((∑ k ∈ Finset.range (Nat.card F ^ d - 1), a k * b k : ℤ) : ℂ) = d * _root_.GlobalTheory.BI.pair χ χ' := by
  classical
  letI : Fintype (GL (Fin d) F) := Fintype.ofFinite _
  have hN : _root_.GlobalTheory.CuspGL.glCard F d ≠ 0 := _root_.GlobalTheory.CuspGL.generalLinearGroupCardComplex_finiteField_ne_zero F d
  have hfr : Module.finrank F (Fin d → F) = d := Module.finrank_fin_fun F
  obtain ⟨h1, -, h3, h4⟩ := _root_.GlobalTheory.CuspGL.extZero_spec F d χ
  obtain ⟨h1', -, -, h4'⟩ := _root_.GlobalTheory.CuspGL.extZero_spec F d χ'
  have hinv' := h4' (_root_.GlobalTheory.isChar_restrict_conj_one ℂ ℂ _ χ' h').2.1
  set M : ℕ → Module.End F (Fin d → F) → ℂ := fun k =>
    _root_.GlobalTheory.CuspGL.psi (_root_.GlobalTheory.CuspGL.rootSum θ k) (Fin d → F) with hMdef

  have hexp : ∀ x : GL (Fin d) F, (d : ℂ) * χ' x =
      ∑ k ∈ Finset.range (Nat.card F ^ d - 1), (b k : ℂ) * M k (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) := by
    intro x
    have hu : IsUnit (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) :=
      x.isUnit.map (Matrix.toLinAlgEquiv' (R := F) (n := Fin d))
    have := _root_.GlobalTheory.CuspGL.expand_primitive F (Fin d → F) θ hθ _ hinv' hp'
      (by rw [hfr]; exact hd) _ hu
    rw [hfr, h1'] at this
    simp only [hb] at this
    apply mul_left_cancel₀ hN
    rw [Finset.mul_sum, ← mul_assoc, this]
    refine Finset.sum_congr rfl fun k _ => by simp only [M]; ring

  have hMk : ∀ k, ∑ x : GL (Fin d) F, χ x * star (M k (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) =
      a k * _root_.GlobalTheory.CuspGL.glCard F d := by
    intro k
    rw [← ha k, ← _root_.GlobalTheory.CuspGL.PrimOrth.ipGL_psi_eq F (Fin d → F) _
      (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one F θ k).1 _ hp, h3,
      finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun x _ => by rw [h1]
  have hpair : ∑ x : GL (Fin d) F, χ x * star (χ' x) =
      _root_.GlobalTheory.CuspGL.glCard F d * _root_.GlobalTheory.BI.pair χ χ' := by
    unfold _root_.GlobalTheory.BI.pair _root_.GlobalTheory.CuspGL.glCard
    have hN' : ((Nat.card (GL (Fin d) F) : ℂ)) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    rw [← mul_assoc, mul_inv_cancel₀ hN', one_mul, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [_root_.GlobalTheory.CuspGL.star_virt_eq_inv _ _ (_root_.GlobalTheory.BI.isChar_mem_virt_complex h') x]
  have hmain : (d : ℂ) * ∑ x : GL (Fin d) F, χ x * star (χ' x) =
      ∑ k ∈ Finset.range (Nat.card F ^ d - 1), (b k : ℂ) *
        ∑ x : GL (Fin d) F, χ x * star (M k (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    have := congrArg star (hexp x)
    rw [star_mul', star_natCast, star_sum] at this
    rw [mul_left_comm, this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [star_mul', star_intCast]
    ring
  rw [hpair] at hmain
  simp only [hMk] at hmain
  apply mul_left_cancel₀ hN
  push_cast
  have hre : ∑ k ∈ Finset.range (Nat.card F ^ d - 1), (b k : ℂ) * (a k * _root_.GlobalTheory.CuspGL.glCard F d) =
      _root_.GlobalTheory.CuspGL.glCard F d * ∑ k ∈ Finset.range (Nat.card F ^ d - 1), (a k : ℂ) * b k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hre] at hmain
  linear_combination -hmain
end _root_.GlobalTheory.CuspGL
end GlobalTheory.CuspGL
