-- Prove2me | solution 1 for GlobalTheory.CNorm.IsKum.pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:56.925679+00:00
-- url     : https://prove2.me/submissions/f24b077a-cbab-44ba-b928-14dcd764f992

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_KummerGalois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
namespace IsKum
theorem _root_.solution {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E] {ζ δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) (k : ℕ) :
    (σ ^ k) θ = algebraMap F E (ζ ^ k) * θ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, AlgEquiv.commutes, h.conj, pow_succ', map_mul]
    ring
end IsKum
end GlobalTheory.CNorm
