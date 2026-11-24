-- Prove2me | solution 1 for GlobalTheory.Mem.PartialZeta.hasSum_cnt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:17:27.505133+00:00
-- url     : https://prove2.me/submissions/035259c5-77de-499b-9ffa-e4048207a666

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_ne_bot_of_coprime
import Theorems.Thm_GlobalTheory_Mem_RayData_finite_cnt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.PartialZeta
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.PartialZeta
theorem _root_.solution {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) (D : RayData K M) (c : D.G) (s a : ℂ)
    (h : HasSum (fun I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} =>
      (Ideal.absNorm I.1 : ℂ) ^ (-s)) a) : LSeriesHasSum (D.cnt c) s a := by
  classical
  let C := {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c}
  let Nm : C → ℕ := fun I => Ideal.absNorm I.1
  have h' : HasSum (fun x : (Σ n : ℕ, {I : C // Nm I = n}) =>
      (Ideal.absNorm x.2.1.1 : ℂ) ^ (-s)) a :=
    (Equiv.sigmaFiberEquiv Nm).hasSum_iff.2 h
  refine h'.sigma (fun n => ?_)
  let en : {I : C // Nm I = n} ≃
      {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧ D.cls I = c} :=
    { toFun := fun x => ⟨x.1.1, x.1.2.1, x.2, x.1.2.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1, y.2.2.2⟩, y.2.2.1⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  haveI : Finite {I : C // Nm I = n} := by
    haveI := D.finite_cnt c n
    exact Finite.of_equiv _ en.symm
  haveI : Fintype {I : C // Nm I = n} := Fintype.ofFinite _
  have hconst : (fun x : {I : C // Nm I = n} => (Ideal.absNorm x.1.1 : ℂ) ^ (-s)) =
      fun _ => (n : ℂ) ^ (-s) := by
    funext x
    rw [show Ideal.absNorm x.1.1 = n from x.2]
  show HasSum (fun x : {I : C // Nm I = n} => (Ideal.absNorm x.1.1 : ℂ) ^ (-s)) _
  rw [hconst]
  by_cases hn : n = 0
  · subst hn
    haveI : IsEmpty {I : C // Nm I = 0} := ⟨fun x => by
      have hx : x.1.1 = ⊥ := Ideal.absNorm_eq_zero_iff.1 x.2
      exact ne_bot_of_coprime hM x.1.2.1 hx⟩
    rw [LSeries.term_zero]
    exact hasSum_empty
  · rw [LSeries.term_of_ne_zero hn]
    have hs := hasSum_fintype (fun _ : {I : C // Nm I = n} => (n : ℂ) ^ (-s))
    convert hs using 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, RayData.cnt,
      ← Nat.card_congr en, Nat.card_eq_fintype_card, Complex.cpow_neg, div_eq_mul_inv]
end GlobalTheory.Mem.PartialZeta
