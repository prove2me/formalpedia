-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliAdj.HasAdj.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:21:36.259285+00:00
-- url     : https://prove2.me/submissions/4ca5f38f-9c53-477b-a8ba-ba01fd52af6c

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetOppositeNegStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetAdjointForm
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAdj_HasAdj_add
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAdj_HasAdj_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliAdj
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.CapelliAdj
namespace HasAdj
theorem _root_.solution {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {ι : Type*} (s : Finset ι)
    (f g : ι → Module.End ℂ V) (h : ∀ i ∈ s, HasAdj B (f i) (g i)) :
    HasAdj B (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasAdj.zero B
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end HasAdj
end GlobalTheory.CompanionTheory.CapelliAdj
