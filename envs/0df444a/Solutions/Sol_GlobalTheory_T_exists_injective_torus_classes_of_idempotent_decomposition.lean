-- Prove2me | solution 1 for GlobalTheory.T.exists_injective_torus_classes_of_idempotent_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:21:13.288477+00:00
-- url     : https://prove2.me/submissions/370ae95d-8546-47c4-ae84-ab8a36afe0dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInjectiveTorusClassesOfIdempotentDecomposi
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInjectiveTorusClassesOfIdempotentDecomposiStatement
import Theorems.Thm_GlobalTheory_UnitLemma_TorusPts_torus_points


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e : ι → B.A) (S : Finset ι) (a : K.O), K.Small a → IsPre B e S → ∀ k : ℕ, ∃ f : ({i // i ∉ S} → Fin (k + 1)) → B.T ⧸ (intUnits K.O B.A).subgroupOf B.T, Function.Injective f ∧ ∀ n, IsIntegral K.O ((((Quotient.out (f n) : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A) := by
  first | exact @GlobalTheory.UnitLemma.TorusPts.torus_points | exact GlobalTheory.UnitLemma.TorusPts.torus_points | (intros; apply GlobalTheory.UnitLemma.TorusPts.torus_points <;> assumption)
end _root_.GlobalTheory.T
