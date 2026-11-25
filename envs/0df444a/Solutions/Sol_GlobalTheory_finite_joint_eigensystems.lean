-- Prove2me | solution 1 for GlobalTheory.finite_joint_eigensystems
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:49.570801+00:00
-- url     : https://prove2.me/submissions/f2e5830d-de7b-4019-8a6c-9808b07bc38d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteJointEigensystems

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [Field K] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K), (∀ i j, Commute (A i) (A j)) → Set.Finite {χ : ι → K | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, A i *ᵥ c = χ i • c} := by
  intro K _ n ι A hc
  let f : ι → Module.End K (Fin n → K) := fun i => Matrix.toLin' (A i)
  have hcf : ∀ i j, Commute (f i) (f j) := by
    intro i j
    exact (hc i j).map Matrix.toLinAlgEquiv'
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcf j i) φ)
  refine (WellFoundedGT.finite_ne_bot_of_iSupIndep hind).subset ?_
  rintro χ ⟨c, hc0, hχ⟩
  show (⨅ i, (f i).maxGenEigenspace (χ i)) ≠ ⊥
  intro hbot
  apply hc0
  have hmem : c ∈ ⨅ i, (f i).maxGenEigenspace (χ i) := by
    rw [Submodule.mem_iInf]
    intro i
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff]
    simpa [f] using hχ i
  rw [hbot] at hmem
  exact (Submodule.mem_bot K).mp hmem
end GlobalTheory
