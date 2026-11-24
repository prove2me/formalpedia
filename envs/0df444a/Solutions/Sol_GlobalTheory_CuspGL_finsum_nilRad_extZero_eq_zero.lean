-- Prove2me | solution 1 for GlobalTheory.CuspGL.finsum_nilRad_extZero_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:18:28.380717+00:00
-- url     : https://prove2.me/submissions/d982b3b4-7d59-48a6-9a4f-e2aad0795e92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterCosetSumEqZeroOfSubgroupSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsStandardUnipotentRadicalBijOnNilradicalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveExtendZeroOfSumUnipotentRadical
import Theorems.Thm_GlobalTheory_T_character_coset_sum_eq_zero_of_subgroup_sum
import Theorems.Thm_GlobalTheory_T_charpoly_block_and_invariant_under_stabilizerNilradical
import Theorems.Thm_GlobalTheory_T_generalLinearFunctionExtendZeroEnd_properties


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
namespace GlobalTheory.CuspGL
theorem _root_.solution (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ)
    (hχ : IsChar ℂ ℂ χ) (A : Submodule F (Fin d → F)) (H : Subgroup (GL (Fin d) F))
    (hb : Set.BijOn (fun u : GL (Fin d) F => Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1)
      (H : Set (GL (Fin d) F)) (nilRad A))
    (h0 : ∑ᶠ u ∈ (H : Set (GL (Fin d) F)), χ u = 0)
    (g : Module.End F (Fin d → F)) (hg : ∀ x ∈ A, g x ∈ A) :
    ∑ᶠ h ∈ nilRad A, extZero χ (g + h) = 0 := by
  obtain ⟨e1, e2, -, -⟩ := GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties F d χ
  by_cases hu : IsUnit g
  · have hm : IsUnit (LinearMap.toMatrix' g) := by
      have := hu.map (LinearMap.toMatrixAlgEquiv' (R := F) (n := Fin d))
      exact this
    obtain ⟨x, hx⟩ := hm
    have hgx : Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g := by
      rw [hx, Matrix.toLin'_toMatrix']
    have : Finite (Module.End F (Fin d → F)) := Module.finite_of_finite F
    have hb2 : Set.BijOn (fun h : Module.End F (Fin d → F) => g * h) (nilRad A) (nilRad A) := by
      refine ((Set.toFinite _).injOn_iff_bijOn_of_mapsTo ?_).1 ?_
      · intro h hh
        exact ⟨fun y => hg _ (hh.1 y), fun y hy => by simp [hh.2 y hy]⟩
      · intro a _ b _ hab
        exact hu.mul_left_cancel hab
    have h1 := GlobalTheory.T.character_coset_sum_eq_zero_of_subgroup_sum _ χ hχ H
      ((finsum_set_coe_eq_finsum_mem (f := χ) (H : Set (GL (Fin d) F))).trans h0) x
    have h2 := (finsum_set_coe_eq_finsum_mem (f := fun u => χ (x * u)) (H : Set (GL (Fin d) F))).symm.trans h1
    rw [← h2]
    symm
    refine finsum_mem_eq_of_bijOn _ (hb2.comp hb) fun u _ => ?_
    rw [← e1]
    congr 1
    simp only [Function.comp, Units.val_mul, Matrix.toLin'_mul, hgx, mul_sub, mul_one]
    rw [add_sub_cancel]
    rfl
  · refine finsum_mem_of_eqOn_zero fun h hh => ?_
    refine e2 _ fun hu' => hu ?_
    have hc := (GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F _ A g hg).2 h hh
    rw [LinearMap.isUnit_iff_isUnit_det, LinearMap.det_eq_sign_charpoly_coeff] at hu' ⊢
    rwa [hc] at hu'
end GlobalTheory.CuspGL
