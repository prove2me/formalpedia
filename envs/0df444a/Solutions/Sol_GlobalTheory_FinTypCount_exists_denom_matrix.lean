-- Prove2me | solution 1 for GlobalTheory.FinTypCount.exists_denom_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:27:09.396127+00:00
-- url     : https://prove2.me/submissions/c46fde54-936b-43df-b30e-3c1c9d00e7e0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Theorems.Thm_GlobalTheory_FinTypCount_exists_denom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NG
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.FinTypCount
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
variable {n : ℕ}
namespace GlobalTheory.FinTypCount
theorem _root_.solution (G : Matrix (Fin n) (Fin n) (AL L)) :
    ∃ m : ℕ, 0 < m ∧ ∀ i j, (m : AL L) * G i j ∈ ALint L := by
  classical
  choose m hm h using fun p : Fin n × Fin n => exists_denom (G p.1 p.2)
  refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun i j => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ (i, j))
  rw [hk, Nat.cast_mul, mul_comm ((m (i, j) : ℕ) : AL L), mul_assoc]
  exact Subring.mul_mem _ (natCast_mem _ _) (h (i, j))
end GlobalTheory.FinTypCount
