-- Prove2me | solution 1 for GlobalTheory.RowSpan.weight_lt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:15:39.601606+00:00
-- url     : https://prove2.me/submissions/e96b84ae-ae05-4c0a-ab15-42d4de7c9221

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf

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
open GlobalTheory GlobalTheory.RowSpan
open MvPolynomial Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
variable {σ : Type} (w : σ → ℕ)
namespace GlobalTheory.RowSpan
theorem _root_.solution {p q : MvPolynomial σ k} {a b : ℕ} (hp : ∀ m ∈ p.support, Finsupp.weight w m < a)
    (hq : ∀ m ∈ q.support, Finsupp.weight w m ≤ b) : ∀ m ∈ (p * q).support, Finsupp.weight w m < a + b := by
  classical
  intro m hm
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (support_mul p q hm)
  have := hp x hx
  have := hq y hy
  rw [map_add]
  omega
end GlobalTheory.RowSpan
