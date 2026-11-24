-- Prove2me | solution 1 for GlobalTheory.UnitLemma.PairClass.exists_aeval_eq_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:40:48.619673+00:00
-- url     : https://prove2.me/submissions/46015df8-ff44-43df-bd8b-7687978b440a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ExistsNeZeroAevalEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfSeparable
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_base_change_cyclic_vector


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PairClass
namespace GlobalTheory.UnitLemma.PairClass
theorem _root_.solution {F A : Type} [Field F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (a : A) (hs : (LinearMap.mulLeft F a).charpoly.Separable) (y : A) :
    ∃ q : F[X], y = aeval a q := by
  obtain ⟨w, hw⟩ := Formalism.IrreducibleCountingLemmas.Z.base_change_cyclic_vector F A (LinearMap.mulLeft F a) hs
  have key : ∀ (p : F[X]) (z : A), aeval (LinearMap.mulLeft F a) p z = aeval a p * z := by
    intro p z
    have h1 : aeval (Algebra.lmul F A a) p = Algebra.lmul F A (aeval a p) :=
      aeval_algHom_apply (Algebra.lmul F A) a p
    have h2 : Algebra.lmul F A a = LinearMap.mulLeft F a := rfl
    rw [← h2, h1]
    rfl
  obtain ⟨p1, hp1⟩ := hw 1
  obtain ⟨p2, hp2⟩ := hw (w * w)
  obtain ⟨p3, hp3⟩ := hw y
  rw [key] at hp1 hp2 hp3
  have hw2 : w = aeval a p2 := by
    calc w = w * w * aeval a p1 := by rw [mul_assoc, mul_comm w (aeval a p1), hp1, mul_one]
      _ = aeval a p2 * (aeval a p1 * w) := by rw [← hp2]; ring
      _ = aeval a p2 := by rw [hp1, mul_one]
  exact ⟨p3 * p2, by rw [← hp3, map_mul, hw2]⟩
end GlobalTheory.UnitLemma.PairClass
