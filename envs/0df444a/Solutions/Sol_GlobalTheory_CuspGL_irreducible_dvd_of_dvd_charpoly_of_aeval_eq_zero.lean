-- Prove2me | solution 1 for GlobalTheory.CuspGL.irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:35.605923+00:00
-- url     : https://prove2.me/submissions/b820b55f-6f77-4be7-91f3-0f3ec0357a6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsConjEqAddOfIsCoprime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary

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
theorem _root_.solution {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (T : Module.End F V) (p q : F[X]) (hp : Irreducible p)
    (hd : p ∣ LinearMap.charpoly T) (hq : aeval T q = 0) : p ∣ q := by
  have : Fact (Irreducible p) := ⟨hp⟩
  have hroot : (LinearMap.charpoly (T.baseChange (AdjoinRoot p))).IsRoot (AdjoinRoot.root p) := by
    rw [LinearMap.charpoly_baseChange]
    obtain ⟨r, hr⟩ := hd
    rw [hr, Polynomial.map_mul, IsRoot, eval_mul, AdjoinRoot.algebraMap_eq,
      (AdjoinRoot.isRoot_root p).eq_zero, zero_mul]
  obtain ⟨v, hv⟩ :=
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot).exists_hasEigenvector
  have h0 : aeval (T.baseChange (AdjoinRoot p)) (q.map (algebraMap F (AdjoinRoot p))) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    change aeval (Module.End.baseChangeHom F (AdjoinRoot p) V T) q = 0
    rw [Polynomial.aeval_algHom_apply, hq, map_zero]
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q.map (algebraMap F (AdjoinRoot p))) hv
  rw [h0, LinearMap.zero_apply] at h1
  have hz : (q.map (algebraMap F (AdjoinRoot p))).eval (AdjoinRoot.root p) = 0 := by
    rcases smul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hv.2
  rw [Polynomial.eval_map_algebraMap, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at hz
  exact hz
end GlobalTheory.CuspGL
