-- Prove2me | solution 1 for GlobalTheory.MinorNorm.fock_prod_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:01:05.733474+00:00
-- url     : https://prove2.me/submissions/1209b591-8935-4ba4-a5aa-04409e0f9dad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_iterD_zero
import Theorems.Thm_GlobalTheory_MinorNorm_iterD_succ
import Theorems.Thm_GlobalTheory_MinorNorm_fock_X_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
variable {σ : Type}
namespace GlobalTheory.MinorNorm
theorem _root_.solution {k : ℕ} (v : Fin k → Fin k → σ) :
    ∀ (m : ℕ) (ρ J : Fin m → Fin k) (P Q : MvPolynomial σ ℂ),
      Formalism.E.fock ((∏ t, X (v (ρ t) (J t))) * P) Q =
        Formalism.E.fock P (iterD (fun r c => pderiv (v r c)) m ρ J Q) := by
  intro m
  induction m with
  | zero => intro ρ J P Q; simp [iterD_zero]
  | succ m ih =>
    intro ρ J P Q
    rw [iterD_succ, ← fock_X_mul, ← ih, Fin.prod_univ_succ]
    congr 1
    simp only [Fin.tail]
    ring
end GlobalTheory.MinorNorm
