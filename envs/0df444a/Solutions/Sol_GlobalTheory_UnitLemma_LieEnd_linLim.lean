-- Prove2me | solution 1 for GlobalTheory.UnitLemma.LieEnd.linLim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:03:26.056556+00:00
-- url     : https://prove2.me/submissions/c5b1d1dc-d2d2-4c2d-97cd-72ba5aab4176

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetEqOneOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GramDetEqNormMulGramDetOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaSelfAdjointLieOfCountLimitDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.LieEnd
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ}
namespace GlobalTheory.UnitLemma.LieEnd
theorem _root_.solution (h1 : CountIdentity) (h2 : UnitaryLimit) (B : InvAlg K) (hB : B.LieReg) (a : K.O)
    (ha : K.Small a) (x : B.A) (hx : B.Plus x) : B.LinLim a x (B.N x : ℝ) := by
  have hw : ∀ k : ℕ, IsUnit (algebraMap K.O B.A a ^ k) := by
    intro k
    apply IsUnit.pow
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
    exact (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ha.1)).map _
  have hσ : B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A a := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ha.2.2]
  refine (h2 K B hB a ha x hx).congr fun k => ?_
  have e : x * algebraMap K.O B.A a ^ (2 * k) =
      x * (algebraMap K.O B.A a ^ k * B.σ (algebraMap K.O B.A a ^ k)) := by
    rw [map_pow, hσ, ← pow_add, two_mul]
  rw [e, h1 K B hB x _ hx (hw k), Rat.cast_natCast]
end GlobalTheory.UnitLemma.LieEnd
