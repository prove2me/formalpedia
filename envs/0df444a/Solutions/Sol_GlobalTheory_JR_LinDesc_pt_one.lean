-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.pt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:54:53.237523+00:00
-- url     : https://prove2.me/submissions/710ec9ef-059c-47ad-b841-0015ccd42d88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
namespace GlobalTheory.JR.LinDesc
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ a : A.K, LinDesc.pt A hG lam 1 a = sec (A.invK τ p lam a) := by
  intro F E _ _ _ _ _ A r τ p hG lam a
  unfold LinDesc.pt sec Et.invK
  congr 1
  refine Prod.ext ?_ rfl
  funext i
  have h1 : (1 : A.K) = LinDesc.bas A hG ⟨0, Fin.pos i⟩ := by
    simp [LinDesc.bas]
  simp only
  rw [h1, Module.Basis.equivFun_self]
  by_cases hi : (i : ℕ) = 0
  · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
  · rw [if_neg hi, if_neg]
    intro h; exact hi (by rw [← h])
end GlobalTheory.JR.LinDesc
