-- Prove2me | solution 1 for GlobalTheory.RegSS.quad_exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:12:08.903806+00:00
-- url     : https://prove2.me/submissions/1d5d830d-0433-4574-97bf-896c28356511

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
open Matrix NumberField
open scoped TensorProduct
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
namespace GlobalTheory.RegSS
namespace _root_.GlobalTheory.RegSS
theorem _root_.solution [CharZero F]
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsQuadInvol F E σ) :
    ∃ (b : Module.Basis (Fin 2) F E) (d : F), b 0 = 1 ∧ σ (b 1) = - b 1 ∧ d ≠ 0 ∧
      b 1 * b 1 = algebraMap F E d := by
  have hfr := h.finrank_eq
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [hfr]; norm_num)
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hfr]; norm_num)
  haveI := h.etale
  haveI : IsReduced E := Algebra.FormallyUnramified.isReduced_of_field F E
  obtain ⟨e, he⟩ := h.ne_id
  set w := e - σ e with hw
  have hσw : σ w = -w := by simp [w, h.invol]
  have hw0 : w ≠ 0 := fun h0 => he (sub_eq_zero.mp h0).symm
  have two : (2 : F) ≠ 0 := two_ne_zero
  have hkill : ∀ t : F, t • w = -(t • w) → t = 0 := by
    intro t ht
    have h2 : (2 : F) • (t • w) = 0 := by rw [two_smul]; nth_rewrite 1 [ht]; exact neg_add_cancel _
    rcases smul_eq_zero.mp h2 with h2 | h2
    · exact absurd h2 two
    · exact (smul_eq_zero.mp h2).resolve_right hw0
  have hli : LinearIndependent F ![(1 : E), w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hσst := congrArg σ hst
    simp only [map_add, map_smul, map_one, hσw, map_zero, smul_neg] at hσst
    have ht : t • w = -(t • w) := by
      have := hst.trans hσst.symm
      exact add_left_cancel this
    have ht0 := hkill t ht
    subst ht0
    simp only [zero_smul, add_zero] at hst
    refine ⟨?_, rfl⟩
    rw [Algebra.smul_def, mul_one] at hst
    exact (algebraMap F E).injective (by rw [hst, map_zero])
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hfr])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = w := by simp [b]
  have hsum : w * w = b.repr (w * w) 0 • (1 : E) + b.repr (w * w) 1 • w := by
    have := b.sum_repr (w * w)
    rw [Fin.sum_univ_two, hb0, hb1] at this
    exact this.symm
  have hσ2 : σ (w * w) = w * w := by rw [map_mul, hσw, neg_mul_neg]
  have hc1 : b.repr (w * w) 1 = 0 := by
    apply hkill
    have := congrArg σ hsum
    rw [hσ2] at this
    simp only [map_add, map_smul, map_one, hσw, smul_neg] at this
    have := hsum.symm.trans this
    exact add_left_cancel this
  refine ⟨b, b.repr (w * w) 0, hb0, by rw [hb1, hσw], ?_, ?_⟩
  · intro hd
    rw [hc1, hd, zero_smul, zero_smul, add_zero] at hsum
    exact hw0 (IsReduced.eq_zero w ⟨2, by rw [pow_two, hsum]⟩)
  · rw [hb1]
    conv_lhs => rw [hsum, hc1, zero_smul, add_zero, Algebra.smul_def, mul_one]
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
