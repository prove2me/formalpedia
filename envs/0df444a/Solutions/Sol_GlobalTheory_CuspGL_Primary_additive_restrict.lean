-- Prove2me | solution 1 for GlobalTheory.CuspGL.Primary.additive_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:25:04.038248+00:00
-- url     : https://prove2.me/submissions/11c77c6d-8759-40f5-aa30-17e534d872c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyInvariantLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusInversionAffineFinrankSubspacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjectivePiAdjoinRootKerEqRangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalApplyMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantSubspaceMobiusInverseCharpolyPrimaryEq
import Theorems.Thm_GlobalTheory_CuspGL_Primary_additive_pow
import Theorems.Thm_GlobalTheory_CuspGL_charpoly_eq_restrict_mul_mapQ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.Primary
namespace GlobalTheory.CuspGL.Primary
theorem _root_.solution {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {s : F[X] → ℂ} (hs : IsAdditive s) {g : Module.End F V} {f : F[X]} {m : ℕ} (hf : f.Monic)
    (hi : Irreducible f) (hc : LinearMap.charpoly g = f ^ m) (A : Submodule F V) (hA : ∀ x ∈ A, g x ∈ A) :
    (f.natDegree : ℂ) * s (LinearMap.charpoly (g.restrict hA)) = (Module.finrank F A : ℂ) * s f := by
  have h1 : LinearMap.charpoly (g.restrict hA) ∣ f ^ m :=
    hc ▸ ⟨_, charpoly_eq_restrict_mul_mapQ A g hA⟩
  obtain ⟨j, -, hj⟩ := (dvd_prime_pow hi.prime m).1 h1
  have h2 : LinearMap.charpoly (g.restrict hA) = f ^ j :=
    eq_of_monic_of_associated (LinearMap.charpoly_monic _) (hf.pow j) hj
  have h3 := LinearMap.charpoly_natDegree (g.restrict hA)
  rw [h2, hf.natDegree_pow] at h3
  rw [h2, additive_pow hs hf, ← h3]
  push_cast; ring
end GlobalTheory.CuspGL.Primary
