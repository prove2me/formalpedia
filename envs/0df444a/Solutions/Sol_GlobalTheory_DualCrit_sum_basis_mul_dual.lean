-- Prove2me | solution 1 for GlobalTheory.DualCrit.sum_basis_mul_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:09:39.239069+00:00
-- url     : https://prove2.me/submissions/73f565a0-e411-41a6-9fc1-9b4802e1fb43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentOfTraceDual
import Theorems.Thm_GlobalTheory_DualCrit_trace_eq_sum_ringHom
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.DualCrit
namespace GlobalTheory.DualCrit
theorem _root_.solution {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K]
    [Fintype (E →+* K)] (hcard : Fintype.card (E →+* K) = Module.finrank ℚ E)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (σ σ' : E →+* K) :
    ∑ j, σ' (b j) * σ ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b j) =
      if σ' = σ then 1 else 0 := by
  set bd := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b
  let A : Matrix ι (E →+* K) K := fun j τ => τ (b j)
  let B : Matrix (E →+* K) ι K := fun τ k => τ (bd k)
  have hAB : A * B = 1 := by
    ext j k
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [A, B]
    rw [show (∑ τ : E →+* K, τ (b j) * τ (bd k)) = ∑ τ : E →+* K, τ (bd k * b j) from
      Finset.sum_congr rfl fun τ _ => by rw [map_mul, mul_comm]]
    rw [← trace_eq_sum_ringHom hcard, ← Algebra.traceForm_apply,
      LinearMap.BilinForm.apply_dualBasis_left]
    split_ifs <;> simp
  have e : ι ≃ (E →+* K) := Fintype.equivOfCardEq (by rw [hcard, Module.finrank_eq_card_basis b])
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hAB
  have h := congrFun (congrFun hBA σ) σ'
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simp only [A, B] at h
  calc _ = ∑ k, σ (bd k) * σ' (b k) := Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ = _ := by rw [h]; exact if_congr eq_comm rfl rfl
end GlobalTheory.DualCrit
