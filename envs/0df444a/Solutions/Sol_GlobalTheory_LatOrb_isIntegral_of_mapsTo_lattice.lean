-- Prove2me | solution 1 for GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:37:34.519171+00:00
-- url     : https://prove2.me/submissions/e9d9d2c1-8105-4b47-ab53-78fa6c018e08

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralMatrixOfMapsToFullRankLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.LatOrb
namespace GlobalTheory.LatOrb
theorem _root_.solution : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (M : Submodule O (Fin n → K)),
    IsLatV O M → ∀ c : Matrix (Fin n) (Fin n) K, (∀ v ∈ M, c *ᵥ v ∈ M) → IsIntegral O c := by
  intro O K _ _ _ n M hM c hc
  classical
  haveI : Module.Finite O M := Module.Finite.iff_fg.mpr hM.1
  let f : Module.End O M :=
    { toFun := fun v => ⟨c *ᵥ (v : Fin n → K), hc v v.2⟩
      map_add' := fun x y => by ext1; simp [Matrix.mulVec_add]
      map_smul' := fun a x => by
        ext1
        simp only [Submodule.coe_smul, RingHom.id_apply, SetLike.val_smul]
        rw [Matrix.mulVec_smul] }
  have hpow : ∀ k : ℕ, ∀ v : M, (c ^ k) *ᵥ (v : Fin n → K) = (((f ^ k) v : M) : Fin n → K) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, ← Matrix.mulVec_mulVec, pow_succ, Module.End.mul_apply]
      have h1 : ((f v : M) : Fin n → K) = c *ᵥ (v : Fin n → K) := rfl
      rw [← h1, ih]
  have key : ∀ q : O[X], ∀ v : M, aeval c q *ᵥ (v : Fin n → K) = (((aeval f q) v : M) : Fin n → K) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => intro v; simp [Matrix.add_mulVec, hp, hq]
    | monomial k a =>
      intro v
      rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def,
        Matrix.smul_mulVec, LinearMap.smul_apply, Submodule.coe_smul, hpow]
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  refine ⟨p, hp, ?_⟩
  rw [← Polynomial.aeval_def]
  set A := aeval c p
  have hker : Submodule.span K (M : Set (Fin n → K)) ≤ LinearMap.ker (Matrix.mulVecLin A) := by
    rw [Submodule.span_le]
    intro v hv
    have := key p ⟨v, hv⟩
    rw [hpf] at this
    simpa using this
  rw [hM.2, top_le_iff, LinearMap.ker_eq_top] at hker
  have : Matrix.toLin' A = 0 := by rw [Matrix.toLin'_apply']; exact hker
  simpa using this
end GlobalTheory.LatOrb
