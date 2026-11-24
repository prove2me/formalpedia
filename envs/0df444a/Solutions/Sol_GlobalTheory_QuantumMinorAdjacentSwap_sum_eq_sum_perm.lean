-- Prove2me | solution 1 for GlobalTheory.QuantumMinorAdjacentSwap.sum_eq_sum_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:47:44.190879+00:00
-- url     : https://prove2.me/submissions/907b4cb1-fdb7-49d3-b8d6-f3daa76149bb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_QminorSwapAdjacent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.QuantumMinorAdjacentSwap
variable {A : Type} [Ring A] [Algebra ℂ A]
open Formalism.REAL
namespace GlobalTheory.QuantumMinorAdjacentSwap
theorem _root_.solution {n : ℕ} {V : Type} [AddCommMonoid V] (F : (Fin n → Fin n) → V)
    (hF : ∀ d, ¬ Function.Injective d → F d = 0) :
    ∑ d, F d = ∑ σ : Equiv.Perm (Fin n), F σ := by
  classical
  symm
  refine Finset.sum_of_injOn (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n))
    (fun _ _ _ _ h => DFunLike.coe_injective h) (fun _ _ => Finset.mem_univ _) ?_
    (fun _ _ => rfl)
  intro d _ hd
  apply hF
  intro hinj
  exact hd ⟨Equiv.ofBijective d (Finite.injective_iff_bijective.1 hinj), by simp, rfl⟩
end GlobalTheory.QuantumMinorAdjacentSwap
