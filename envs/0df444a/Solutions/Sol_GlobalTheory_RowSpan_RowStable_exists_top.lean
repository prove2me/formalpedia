-- Prove2me | solution 1 for GlobalTheory.RowSpan.RowStable.exists_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:35:29.63313+00:00
-- url     : https://prove2.me/submissions/88d63bc3-6ef9-431e-948d-eafded0990ac

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
import Theorems.Thm_GlobalTheory_RowSpan_exists_weight_lt
import Theorems.Thm_GlobalTheory_RowSpan_RowStable_rowShift_mem
import Theorems.Thm_GlobalTheory_RowSpan_RowStable_component_mem
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Wick.dividedContraction_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowSpan
open MvPolynomial Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
namespace GlobalTheory.RowSpan
namespace RowStable
theorem _root_.solution [Infinite k] {U : Submodule k (MvPolynomial (Letter T r n) k)} (hU : RowStable U)
    (h0 : U ≠ ⊥) : ∃ P ∈ U, P ≠ 0 ∧ RowInv r n k P ∧ ∃ a : T → ℕ → ℕ, RowDeg r n k a P := by
  classical
  let h : Letter T r n → ℕ := fun ℓ => ℓ.2.1
  let w := fun ℓ : Letter T r n => Finsupp.single (rowOf ℓ) 1
  have hex : ∃ d, ∃ P ∈ U, P ≠ 0 ∧ ∀ m ∈ P.support, Finsupp.weight h m < d := by
    obtain ⟨P, hP, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    exact ⟨P.support.sup (Finsupp.weight h) + 1, P, hP, hP0, fun m hm => Nat.lt_succ_of_le (Finset.le_sup hm)⟩
  obtain ⟨P, hP, hP0, hd⟩ := Nat.find_spec hex
  obtain ⟨m₀, hm₀⟩ := support_nonempty.2 hP0
  let Q := weightedHomogeneousComponent w (Finsupp.weight w m₀) P
  have hQU : Q ∈ U := hU.component_mem hP _
  have hQs : ∀ m ∈ Q.support, m ∈ P.support ∧ Finsupp.weight w m = Finsupp.weight w m₀ := by
    intro m hm
    rw [mem_support_iff, coeff_weightedHomogeneousComponent] at hm
    split_ifs at hm with h1
    · exact ⟨mem_support_iff.2 hm, h1⟩
    · exact absurd rfl hm
  refine ⟨Q, hQU, fun hQ => ?_, fun σ i i' hi t => ?_,
    fun σ i => if hi : i < r σ then Finsupp.weight w m₀ ⟨σ, ⟨i, hi⟩⟩ else 0, fun m hm σ i => ?_⟩
  · have := congrArg (coeff m₀) hQ
    rw [coeff_weightedHomogeneousComponent, if_pos rfl] at this
    exact mem_support_iff.1 hm₀ this
  · by_contra hne
    have hlt := exists_weight_lt h (rowShift r n k σ i i' t) (fun ℓ m hm => by
      rw [rowShift, aeval_X] at hm
      split_ifs at hm with hc
      · obtain ⟨b, rfl⟩ := hc
        rw [add_sub_cancel_left, ← smul_eq_C_mul] at hm
        have := support_smul hm
        rw [support_X, Finset.mem_singleton] at this
        rw [this, Finsupp.weight_single, one_smul]
        exact hi
      · simp at hm) Q
    have hpos : 0 < Nat.find hex := lt_of_le_of_lt (Nat.zero_le _) (hd m₀ hm₀)
    refine Nat.find_min hex (m := Nat.find hex - 1) (by omega)
      ⟨_, U.sub_mem (hU.rowShift_mem σ i i' hi t hQU) hQU, sub_ne_zero.2 hne, fun m' hm' => ?_⟩
    obtain ⟨m, hm, h1⟩ := hlt m' hm'
    have := hd m (hQs m hm).1
    omega
  · simp only [i.2, dif_pos, Fin.eta]
    rw [← (hQs m hm).2, Finsupp.weight_apply, Finsupp.sum, Finsupp.finset_sum_apply]
    simp only [w, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    refine Finset.sum_bij_ne_zero (fun b _ _ => ⟨σ, i, b⟩) ?_ ?_ ?_ ?_
    · intro b _ hb
      exact Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 hb, rfl⟩
    · intro b _ _ b' _ _ hb
      cases hb
      rfl
    · rintro ⟨σ', i', b⟩ hl hb
      have := (Finset.mem_filter.1 hl).2
      cases this
      exact ⟨b, Finset.mem_univ _, hb, rfl⟩
    · intro b _ _
      rfl
end RowStable
end GlobalTheory.RowSpan
