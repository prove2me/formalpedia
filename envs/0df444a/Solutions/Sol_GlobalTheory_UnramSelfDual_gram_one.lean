-- Prove2me | solution 1 for GlobalTheory.UnramSelfDual.gram_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:51:02.29882+00:00
-- url     : https://prove2.me/submissions/4d183e0d-0b85-4cf7-bf66-f998a02cc28d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsSubConjNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticeProjectionMemOfUnitLength
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsOfFixedInt
import Theorems.Thm_GlobalTheory_UnramSelfDual_cT_mul_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal Formalism.UG
open GlobalTheory GlobalTheory.UnramSelfDual
variable {A : Type} [CommRing A] (c : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)
variable {c J}
namespace GlobalTheory.UnramSelfDual
theorem _root_.solution {e : Fin M → Fin M → A}
    (he : ∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0) :
    cT c (Matrix.of e)ᵀ * J * (Matrix.of e)ᵀ = 1 := by
  ext i j
  rw [Matrix.one_apply, ← he, ← cT_mul_of]
  rfl
end GlobalTheory.UnramSelfDual
