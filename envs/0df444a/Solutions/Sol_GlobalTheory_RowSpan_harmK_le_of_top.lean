-- Prove2me | solution 1 for GlobalTheory.RowSpan.harmK_le_of_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:54.299347+00:00
-- url     : https://prove2.me/submissions/c7ca53bd-c270-49b1-864b-a07cc0a8eb44

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
import Theorems.Thm_GlobalTheory_RowSpan_mem_harmK_iff
import Theorems.Thm_GlobalTheory_RowSpan_rowStable_harmK
import Theorems.Thm_GlobalTheory_RowSpan_le_of_top_rat
import Theorems.Thm_GlobalTheory_RowSpan_map_rowAct
import Theorems.Thm_GlobalTheory_RowSpan_rowInv_map
import Theorems.Thm_GlobalTheory_RowSpan_harmK_le_span
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_map


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
theorem _root_.solution [CharZero k] [Finite T] (cc : T → T) (isX : T → Prop)
    {U : Submodule k (MvPolynomial (Letter T r n) k)} (hU : RowStable U)
    (h : ∀ P ∈ harmK r n k cc isX (fun _ => 1), RowInv r n k P → (∃ a : T → ℕ → ℕ, RowDeg r n k a P) → P ∈ U) :
    harmK r n k cc isX (fun _ => 1) ≤ U := by
  refine (harmK_le_span cc isX).trans (Submodule.span_le.2 ?_)
  rintro _ ⟨P, hP, rfl⟩
  let U₀ : Submodule ℚ (MvPolynomial (Letter T r n) ℚ) :=
    (U.restrictScalars ℚ).comap (mapAlgHom (Algebra.ofId ℚ k)).toLinearMap
  have hU₀ : ∀ Q, Q ∈ U₀ ↔ map (algebraMap ℚ k) Q ∈ U := fun _ => Iff.rfl
  refine (hU₀ P).1 (le_of_top_rat (U := U₀) (fun g hg Q hQ => ?_) (rowStable_harmK cc isX) ?_ hP)
  · rw [hU₀, map_rowAct]
    refine hU _ (fun σ => ?_) _ hQ
    rw [← RingHom.map_det]
    exact (hg σ).map _
  · rintro Q hQ h1 ⟨a, h2⟩
    rw [hU₀]
    refine h _ ?_ (rowInv_map _ h1) ⟨a, fun m hm => h2 m (support_map_subset _ _ hm)⟩
    rw [mem_harmK_iff] at hQ ⊢
    intro τ hτ j j'
    have := congrArg (map (algebraMap ℚ k)) (hQ τ hτ j j')
    rw [map_sum, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun b _ => by rw [MvPolynomial.pderiv_map, MvPolynomial.pderiv_map]
end GlobalTheory.RowSpan
