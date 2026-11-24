-- Prove2me | solution 1 for GlobalTheory.CombMinor.cMat_supported
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:16:01.734835+00:00
-- url     : https://prove2.me/submissions/36674a89-77f6-458d-abbc-97ddd6715466

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdDetMemHaO
import Theorems.Thm_GlobalTheory_CombMinor_det_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MvPolynomial Formalism.L2.Pj Formalism.L2.Pj.Crude
open GlobalTheory GlobalTheory.CombMinor
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k]
namespace GlobalTheory.CombMinor
theorem _root_.solution (τ : Ty) (s : ℕ) (hs : s ≤ r τ) (B : Fin s → Fin n → k) (S : Set (Letter Ty r n))
    (h : ∀ ρ i b, B ρ b ≠ 0 → (⟨τ, i, b⟩ : Letter Ty r n) ∈ S) :
    (cMat τ s hs B).det ∈ supported k S := by
  refine det_mem (supported k S).toSubring _ fun ρ i => ?_
  change _ ∈ supported k S
  simp only [cMat, Matrix.of_apply]
  refine Subalgebra.sum_mem _ fun b _ => ?_
  by_cases hb : B ρ b = 0
  · rw [hb, C_0, zero_mul]; exact Subalgebra.zero_mem _
  · refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
    rw [supported_eq_adjoin_X]; exact Algebra.subset_adjoin ⟨_, h ρ _ b hb, rfl⟩
end GlobalTheory.CombMinor
