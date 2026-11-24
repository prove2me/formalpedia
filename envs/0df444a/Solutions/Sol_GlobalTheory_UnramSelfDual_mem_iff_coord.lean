-- Prove2me | solution 1 for GlobalTheory.UnramSelfDual.mem_iff_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:08:23.996905+00:00
-- url     : https://prove2.me/submissions/84cec05f-3114-4f39-8593-623f1ef62227

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
import Theorems.Thm_GlobalTheory_UnramSelfDual_expand
import Theorems.Thm_P2M_GlobalTheory_UnramSelfDual_smul_mem__cfd5fc8f3c8d

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
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {O : Subalgebra R A}
  {c : A →+* A} {M : ℕ} {J : Matrix (Fin M) (Fin M) A} {L : Submodule O (Fin M → A)}
namespace GlobalTheory.UnramSelfDual
theorem _root_.solution (hL : ∀ y, y ∈ L ↔ ∀ z ∈ L, hform c J z y ∈ O) {e : Fin M → Fin M → A}
    (heL : ∀ i, e i ∈ L) (he : ∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0)
    (y : Fin M → A) : y ∈ L ↔ ∀ i, hform c J (e i) y ∈ O := by
  refine ⟨fun hy i => (hL y).1 hy _ (heL i), fun h => ?_⟩
  rw [← expand he y]
  exact sum_mem fun i _ => smul_mem' (h i) (heL i)
end GlobalTheory.UnramSelfDual
