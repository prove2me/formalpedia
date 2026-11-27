-- Prove2me | solution 1 for GlobalTheory.EmbeddingMean.card_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:21:20.236058+00:00
-- url     : https://prove2.me/submissions/08382bd4-9d4a-4a0a-9e77-6122f34b8584

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAndMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EmbeddingMean
namespace GlobalTheory.EmbeddingMean
theorem _root_.solution {K A B C : Type} [Field K] [Field A] [Field B] [Field C] [CharZero K]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra A B] [IsScalarTower K A B]
    [FiniteDimensional K A] [FiniteDimensional K B] [IsAlgClosed C] [DecidableEq (A →ₐ[K] C)]
    (f : A →ₐ[K] C) :
    (Finset.univ.filter (fun g : B →ₐ[K] C => g.comp (IsScalarTower.toAlgHom K A B) = f)).card
      = Module.finrank A B := by
  letI : Algebra A C := f.toRingHom.toAlgebra
  haveI : IsScalarTower K A C := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  haveI : FiniteDimensional A B := Module.Finite.of_restrictScalars_finite K A B
  haveI : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  rw [← AlgHom.card A B C, ← Fintype.card_subtype]
  refine Fintype.card_congr
    { toFun := fun g => { g.1.toRingHom with
        commutes' := fun a => by
          have := DFunLike.congr_fun g.2 a
          exact this }
      invFun := fun h => ⟨h.restrictScalars K, AlgHom.ext fun a => h.commutes a⟩
      left_inv := fun g => Subtype.ext (AlgHom.ext fun _ => rfl)
      right_inv := fun h => AlgHom.ext fun _ => rfl }
end GlobalTheory.EmbeddingMean
