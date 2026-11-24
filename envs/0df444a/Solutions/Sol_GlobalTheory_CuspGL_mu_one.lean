-- Prove2me | solution 1 for GlobalTheory.CuspGL.mu_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:05:40.329795+00:00
-- url     : https://prove2.me/submissions/4c0d6716-996d-44d5-a17d-6443f6e50712

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMulParabolicInductionTrivialStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumCardCyclicVectorsInvariantSubspacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassOfCharpolyCardCyclicVectorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEndomorphismDensityGLRecursion

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
theorem _root_.solution (F : Type) [Field F] : mu (1 : F[X]) = 1 := by
  unfold mu
  have h : ∀ n : ℕ, n = 0 →
      mass (fun _ : Module.End F (Fin n → F) => (1 : ℂ)) 1 / glCard F n = 1 := by
    rintro n rfl
    have h1 : glCard F 0 = 1 := by
      unfold glCard
      haveI : Subsingleton (GL (Fin 0) F) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
      rw [Nat.card_unique]
      simp
    have h2 : {g : Module.End F (Fin 0 → F) | LinearMap.charpoly g = 1} = {0} := by
      ext g
      have hg : g = 0 := Subsingleton.elim _ _
      have hc : LinearMap.charpoly g = 1 := by
        apply (LinearMap.charpoly_monic g).natDegree_eq_zero.1
        rw [LinearMap.charpoly_natDegree]
        simp
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun _ => hg, fun _ => hc⟩
    unfold mass
    rw [h1, h2, finsum_mem_singleton]
    simp
  exact h _ natDegree_one
end GlobalTheory.CuspGL
