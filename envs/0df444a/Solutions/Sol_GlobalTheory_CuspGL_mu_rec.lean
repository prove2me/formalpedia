-- Prove2me | solution 1 for GlobalTheory.CuspGL.mu_rec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:23:14.346251+00:00
-- url     : https://prove2.me/submissions/e403ce2a-f1c7-4d99-bf43-aa4542f1a8de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMulParabolicInductionTrivialStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumCardCyclicVectorsInvariantSubspacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassOfCharpolyCardCyclicVectorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEndomorphismDensityGLRecursion
import Theorems.Thm_GlobalTheory_CuspGL_cyclic_conj
import Theorems.Thm_GlobalTheory_CuspGL_glCard_ne_zero_of_finite
import Theorems.Thm_GlobalTheory_CuspGL_mass_const
import Theorems.Thm_GlobalTheory_CuspGL_mu_one
import Theorems.Thm_GlobalTheory_T_endomorphismMassOfCharpoly_card_cyclic_vectors
import Theorems.Thm_GlobalTheory_T_endomorphismMass_mul_parabolic_induction_trivial
import Theorems.Thm_GlobalTheory_T_finsum_card_cyclic_vectors_invariant_subspaces


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (P : F[X]), P.Monic →
    (Nat.card F : ℂ) ^ P.natDegree * mu P = conv (fun _ => 1) mu P ∧ mu (1 : F[X]) = 1 := by
  intro F _ _ P hP
  refine ⟨?_, mu_one F⟩
  have key := GlobalTheory.T.endomorphismMass_mul_parabolic_induction_trivial F (Fin P.natDegree → F)
    (fun V _ _ _ g => (Nat.card {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ))
    (by
      intro V V' _ _ _ _ _ _ e g
      congr 1
      exact (Nat.card_congr (e.toEquiv.subtypeEquiv fun v => cyclic_conj e g v)).symm)
    P hP (by simp)
  simp only [GlobalTheory.T.finsum_card_cyclic_vectors_invariant_subspaces] at key
  rw [mass_const] at key
  have hr : conv (fun D : F[X] => mass (fun g : Module.End F (Fin D.natDegree → F) =>
      (Nat.card {v : Fin D.natDegree → F // ∀ U : Submodule F (Fin D.natDegree → F),
        (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) D / glCard F D.natDegree) mu P
      = conv (fun _ => 1) mu P := by
    unfold conv
    refine finsum_mem_congr rfl fun x hx => ?_
    beta_reduce
    rw [GlobalTheory.T.endomorphismMassOfCharpoly_card_cyclic_vectors F x.1 hx.1, div_self (glCard_ne_zero_of_finite F _)]
  rw [← hr, ← key]
  unfold mu
  simp [mul_div_assoc]
end GlobalTheory.CuspGL
