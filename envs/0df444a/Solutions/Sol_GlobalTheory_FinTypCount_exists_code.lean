-- Prove2me | solution 1 for GlobalTheory.FinTypCount.exists_code
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:45:20.498644+00:00
-- url     : https://prove2.me/submissions/9d0b8c5d-5453-4a12-96d2-1cc274d72b54

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Theorems.Thm_GlobalTheory_FinTypCount_exists_approx
import Theorems.Thm_GlobalTheory_FinTypCount_exists_denom_matrix

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
theorem _root_.solution (N : ℕ) (hN : 0 < N) (g : GAf L n) :
    ∃ p : ℕ × (Fin n → Fin n → L), 0 < p.1 ∧
      (∀ i j, (p.1 : AL L) * (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L) ∧
      ∀ i j, ∃ y ∈ ALint L, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
        p.2 i j ⊗ₜ[L⁺] (1 : AFplus L) + (p.1 * N) • y := by
  obtain ⟨m, hm, h⟩ := exists_denom_matrix (g.1 : Matrix (Fin n) (Fin n) (AL L))
  choose c y hy e using fun i j =>
    exists_approx (m * N) (Nat.mul_pos hm hN) ((g.1 : Matrix (Fin n) (Fin n) (AL L)) i j)
  exact ⟨(m, c), hm, h, fun i j => ⟨y i j, hy i j, e i j⟩⟩
end GlobalTheory.FinTypCount
