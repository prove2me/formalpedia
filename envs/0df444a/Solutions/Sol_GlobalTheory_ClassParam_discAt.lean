-- Prove2me | solution 1 for GlobalTheory.ClassParam.discAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:53:17.826787+00:00
-- url     : https://prove2.me/submissions/57f621d4-6c47-463d-9cad-73a5842f2dbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_det_gram
import Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_det_gram_change
import Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_isUnit_det_gram
import Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_det_gram_fixed
import Theorems.Thm_GlobalTheory_ClassParam_trLk_eq
import Theorems.Thm_GlobalTheory_ClassParam_exists_pow_basis
import Theorems.Thm_GlobalTheory_ClassParam_exists_setting
import Theorems.Thm_GlobalTheory_ClassParam_star_fixed_iff
import Theorems.Thm_GlobalTheory_ClassParam_sig_fixed
import Theorems.Thm_GlobalTheory_ClassParam_mk_eq_iff_normE
import Theorems.Thm_GlobalTheory_ClassParam_norm_inclPlus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
attribute [local instance] algLk
variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]
namespace GlobalTheory.ClassParam
theorem _root_.solution [CharZero E] [FiniteDimensional F E] (hP : IsPPol c r P)
    (hc : ∀ e, c (c e) = e) (hc1 : c ≠ 1) (hF : ∀ e, c e = e → ∃ a, algebraMap F E a = e) :
    DiscAt k hP := by
  obtain ⟨b, S, -⟩ := exists_setting k hP hc
  obtain ⟨b₀, -⟩ := exists_pow_basis hP
  have hg : ∀ (x : (Lplus hP ⊗[F] k)ˣ)
      (e : Module.Basis (Fin r) (E ⊗[F] k) (AdjoinRoot P ⊗[F] k)),
      (Matrix.of fun i j => hx k hP x (e i) (e j)) = gram (starLk k hP) (inclPlus k hP x) e := by
    intro x e
    simp only [gram, hx, tf, trLk_eq k b₀]
  have hmul : ∀ x δ δ₁, IsDisc hP x δ → IsDisc hP 1 δ₁ →
      δ = QuotientGroup.mk (normPlus (k := k) hP x) * δ₁ := by
    rintro x _ _ ⟨e, d, hd, rfl⟩ ⟨e₁, d₁, hd₁, rfl⟩
    rw [← QuotientGroup.mk_mul, eq_comm, mk_eq_iff_normE]
    obtain ⟨z, hz⟩ := S.det_gram_change 1 e₁ e
    refine ⟨z, ?_⟩
    rw [hg, Units.val_one, map_one] at hd₁
    rw [hd, hg, det_gram, hz, ← hd₁, norm_inclPlus k hP hc hc1 hF, ← mul_assoc,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, Units.val_mul]
  have hex : ∀ x : (Lplus hP ⊗[F] k)ˣ, ∃ δ, IsDisc hP x δ := by
    intro x
    obtain ⟨d, hd⟩ := sig_fixed k hF _
      (S.det_gram_fixed ((star_fixed_iff k hP _).2 ⟨(x : Lplus hP ⊗[F] k), rfl⟩) b)
    have hu := S.isUnit_det_gram (x.isUnit.map (inclPlus k hP))
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [← hd, tmul_zero] at hu
      exact not_isUnit_zero hu
    exact ⟨_, b, Units.mk0 d hd0, by rw [hg]; exact hd, rfl⟩
  intro x
  refine ⟨?_, hmul x⟩
  obtain ⟨δ, hδ⟩ := hex x
  obtain ⟨δ₁, hδ₁⟩ := hex 1
  exact ⟨δ, hδ, fun δ' hδ' => (hmul x δ' δ₁ hδ' hδ₁).trans (hmul x δ δ₁ hδ hδ₁).symm⟩
end GlobalTheory.ClassParam
