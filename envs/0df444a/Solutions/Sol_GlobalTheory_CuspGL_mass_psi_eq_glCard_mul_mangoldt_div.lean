-- Prove2me | solution 1 for GlobalTheory.CuspGL.mass_psi_eq_glCard_mul_mangoldt_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:54:20.615883+00:00
-- url     : https://prove2.me/submissions/abf0dacd-8246-4ebd-be99-f691e5468977

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionCancelOfOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveMulEqVonMangoldtConvolutionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassEqOfLinearEquivInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMulParabolicInductionTrivialStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEndomorphismDensityGLRecursionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEqFinsumPsiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMobiusInverseMonicEq
import Theorems.Thm_GlobalTheory_CuspGL_mass_comp_charpoly_eq_mul
import Theorems.Thm_GlobalTheory_T_additive_mul_eq_vonMangoldt_convolution
import Theorems.Thm_GlobalTheory_T_apply_charpoly_eq_finsum_psi_invariant_submodules
import Theorems.Thm_GlobalTheory_T_charpolyEndomorphismDensityGL_recursion
import Theorems.Thm_GlobalTheory_T_endomorphismMass_eq_of_linearEquiv_invariant
import Theorems.Thm_GlobalTheory_T_endomorphismMass_mul_parabolic_induction_trivial
import Theorems.Thm_GlobalTheory_T_invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj
import Theorems.Thm_GlobalTheory_T_monicFactorizationConvolution_cancel_of_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution :
    ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (s : F[X] → ℂ), IsAdditive s → ∀ P : F[X], P.Monic → P.natDegree = Module.finrank F V →
      mass (psi s V) P = glCard F P.natDegree * mangoldt s P / ((Nat.card F : ℂ) ^ P.natDegree - 1) := by
  intro F _ _ V _ _ _ s hs P hP hdeg
  have hiso := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F s
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hmu1 : mu (1 : F[X]) = 1 := (GlobalTheory.T.charpolyEndomorphismDensityGL_recursion F 1 monic_one).2
  have hlog := GlobalTheory.T.additive_mul_eq_vonMangoldt_convolution F (Nat.card F) hq s mu hs hmu1 (fun Q hQ => (GlobalTheory.T.charpolyEndomorphismDensityGL_recursion F Q hQ).1)
  have hmul : ∀ Q : F[X], Q.Monic → s Q * mu Q =
      conv (fun D => mass (psi s (Fin D.natDegree → F)) D / glCard F D.natDegree) mu Q := by
    intro Q hQ
    have h := GlobalTheory.T.endomorphismMass_mul_parabolic_induction_trivial F (Fin Q.natDegree → F) (fun V _ _ _ => psi s V) hiso Q hQ (by simp)
    have h2 : (fun g : Module.End F (Fin Q.natDegree → F) =>
        ∑ᶠ W : {W : Submodule F (Fin Q.natDegree → F) // ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2)) =
        fun g => s (LinearMap.charpoly g) := by
      funext g
      exact (GlobalTheory.T.apply_charpoly_eq_finsum_psi_invariant_submodules F _ s g).symm
    rw [← h]
    rw [h2, mass_comp_charpoly_eq_mul, mu, mul_div_assoc]
  have hc := GlobalTheory.T.monicFactorizationConvolution_cancel_of_one F _ _ mu hmu1 (fun Q hQ => (hmul Q hQ).symm.trans (hlog Q hQ)) P hP
  have hV := GlobalTheory.T.endomorphismMass_eq_of_linearEquiv_invariant F V (fun V _ _ _ => psi s V) hiso P hdeg
  have hg : glCard F P.natDegree ≠ 0 := by
    unfold glCard
    exact_mod_cast (Nat.card_pos (α := GL (Fin P.natDegree) F)).ne'
  rw [hV, mul_div_assoc, ← hc, mul_div_cancel₀ _ hg]
end GlobalTheory.CuspGL
