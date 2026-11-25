-- Prove2me | solution 1 for GlobalTheory.RowSpan.le_of_top_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:49:46.584335+00:00
-- url     : https://prove2.me/submissions/554d169e-22a2-48e9-b3fa-4fb794532105

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
import Theorems.Thm_GlobalTheory_RowSpan_rowStable_degree
import Theorems.Thm_GlobalTheory_RowSpan_eq_zero_of_fisch_self
import Theorems.Thm_GlobalTheory_RowSpan_fisch_rowAct
import Theorems.Thm_GlobalTheory_RowSpan_RowStable_exists_top
import Theorems.Thm_GlobalTheory_RowSpan_RowStable_inf

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
namespace GlobalTheory.RowSpan
theorem _root_.solution [Finite T] {U V : Submodule ℚ (MvPolynomial (Letter T r n) ℚ)} (hU : RowStable U)
    (hV : RowStable V) (h : ∀ P ∈ V, RowInv r n ℚ P → (∃ a : T → ℕ → ℕ, RowDeg r n ℚ a P) → P ∈ U) : V ≤ U := by
  intro P hP
  let W := V ⊓ restrictTotalDegree (Letter T r n) ℚ P.totalDegree
  have hW : RowStable W := hV.inf (rowStable_degree _)
  have hPW : P ∈ W := ⟨hP, (mem_restrictTotalDegree _ _ _).2 le_rfl⟩
  have : FiniteDimensional ℚ W := Submodule.finiteDimensional_of_le (inf_le_right : W ≤ _)
  have : FiniteDimensional ℚ (U ⊓ W : Submodule ℚ _) := Submodule.finiteDimensional_of_le inf_le_right
  by_contra hPU
  have hlt : U ⊓ W < W := lt_of_le_of_ne inf_le_right fun e => hPU (e.ge hPW).1
  let O : Submodule ℚ (MvPolynomial (Letter T r n) ℚ) :=
    W ⊓ LinearMap.ker ((U ⊓ W).subtype.dualMap ∘ₗ fisch)
  have hO : ∀ x, x ∈ O ↔ x ∈ W ∧ ∀ y ∈ U ⊓ W, fisch x y = 0 := fun x =>
    and_congr Iff.rfl ⟨fun h y hy => LinearMap.congr_fun h ⟨y, hy⟩, fun h => LinearMap.ext fun y => h y.1 y.2⟩
  have hOs : RowStable O := by
    intro g hg x hx
    rw [hO] at hx ⊢
    refine ⟨hW g hg x hx.1, fun y hy => ?_⟩
    rw [fisch_rowAct]
    exact hx.2 _ ((hU.inf hW) _ (fun σ => by rw [Matrix.det_transpose]; exact hg σ) y hy)
  have hO0 : O ≠ ⊥ := by
    have hk := LinearMap.ker_ne_bot_of_finrank_lt (f := ((U ⊓ W).subtype.dualMap ∘ₗ fisch) ∘ₗ W.subtype) (by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt_finrank_of_lt hlt)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
    exact (Submodule.ne_bot_iff _).2 ⟨x.1, ⟨x.2, hx⟩, fun e => hx0 (Subtype.ext e)⟩
  obtain ⟨Q, hQ, hQ0, h1, h2⟩ := hOs.exists_top hO0
  rw [hO] at hQ
  exact hQ0 (eq_zero_of_fisch_self (hQ.2 Q ⟨h Q hQ.1.1 h1 h2, hQ.1⟩))
end GlobalTheory.RowSpan
