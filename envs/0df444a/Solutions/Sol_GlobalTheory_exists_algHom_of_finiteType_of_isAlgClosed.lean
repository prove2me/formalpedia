-- Prove2me | solution 1 for GlobalTheory.exists_algHom_of_finiteType_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:37:18.616312+00:00
-- url     : https://prove2.me/submissions/046660e3-7558-4761-a3aa-3190bc6f3fdc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAlgHomOfFiniteTypeOfIsAlgClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K C F : Type) [Field K] [CommRing C]
    [Nontrivial C] [Algebra K C] [Algebra.FiniteType K C] [Field F] [IsAlgClosed F]
    [Algebra K F] : Nonempty (C →ₐ[K] F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  let := Ideal.Quotient.field m
  have := finite_of_finite_type_of_isJacobsonRing K (C ⧸ m)
  exact ⟨(IsAlgClosed.lift : (C ⧸ m) →ₐ[K] F).comp (Ideal.Quotient.mkₐ K m)⟩
end GlobalTheory
