-- Prove2me | solution 1 for GlobalTheory.PDivGroup.exists_mulP_eq_of_transl_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:54:18.095591+00:00
-- url     : https://prove2.me/submissions/b9713c7e-4357-4592-8ba6-5dd0bfb57903

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulPEqOfTranslInvariant
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_map_comp
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_IsBicharacter_map
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_succ
import Theorems.Thm_GlobalTheory_PDivGroup_resOne_zero
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_id
import Theorems.Thm_GlobalTheory_PDivGroup_rigExtMap_mk
import Theorems.Thm_GlobalTheory_PDivGroup_rigLevel_mk
import Theorems.Thm_GlobalTheory_PDivGroup_transl_apply
import Theorems.Thm_GlobalTheory_PDiv_SemiBialgHom_levelRig_mk
import Theorems.Thm_GlobalTheory_PDiv_comp_mulBy_pts
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_dual_mulBy
import Theorems.Thm_GlobalTheory_PDiv_map_mulBy
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
import Theorems.Thm_GlobalTheory_PDiv_mulBy_comp
import Theorems.Thm_GlobalTheory_PDiv_mulBy_mulBy
import Theorems.Thm_GlobalTheory_PDiv_torsionIdeal_le_ker_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.PDiv.SemiBialgHom.levelRig_mk
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT
attribute [local simp] GlobalTheory.PDivGroup.resOne_succ
attribute [local simp] GlobalTheory.PDivGroup.resOne_zero
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_id
attribute [local simp] GlobalTheory.PDivGroup.rigExtMap_mk
attribute [local simp] GlobalTheory.PDivGroup.rigLevel_mk


section
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
namespace GlobalTheory.PDivGroup
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
private theorem exists_mulBy_pow_eq_comp_resOne' {p : ℕ} {R : Type} [CommRing R]
    (G : _root_.GlobalTheory.PDivGroup p R) (n : ℕ) :
    ∃ M : G.A 1 →ₐc[R] G.A (n + 1),
      ∀ a : G.A (n + 1),
        _root_.GlobalTheory.PDiv.mulBy R (G.A (n + 1)) (p ^ n) a = M (G.resOne n a) := by
  induction n with
  | zero =>
    refine ⟨BialgHom.id R (G.A 1), fun a => ?_⟩
    have h := _root_.GlobalTheory.PDiv.mulBy_comp (BialgHom.id R (G.A 1)) 1
    rw [pow_one, toConv_ofConv] at h
    rw [_root_.GlobalTheory.PDivGroup.resOne_zero]
    simpa using congrArg (fun f : G.A 1 →ₐc[R] G.A 1 => f a) h
  | succ n ih =>
    obtain ⟨M, hM⟩ := ih
    refine ⟨(G.mulP (n + 1)).comp M, fun a => ?_⟩
    rw [pow_succ, ← _root_.GlobalTheory.PDiv.mulBy_mulBy, ← _root_.GlobalTheory.PDivGroup.mulP_res,
      ← _root_.GlobalTheory.PDiv.map_mulBy, hM, _root_.GlobalTheory.PDivGroup.resOne_succ, BialgHom.comp_apply]
end GlobalTheory.PDivGroup
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory GlobalTheory.PDivGroup
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R)
namespace GlobalTheory.PDivGroup
namespace _root_.GlobalTheory.PDivGroup
theorem _root_.solution {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R)
    (n : ℕ) (a : G.A (n + 1))
    (ha : G.transl n a = a ⊗ₜ[R] 1) :
    ∃ e : G.A n, G.mulP n e = a := by
  obtain ⟨M, hM⟩ := exists_mulBy_pow_eq_comp_resOne' G n
  have key : ∀ χ φ : _root_.GlobalTheory.CartierDual R (G.A (n + 1)),
      (χ * _root_.GlobalTheory.CartierDual.map
        (_root_.GlobalTheory.PDiv.mulBy R (G.A (n + 1)) (p ^ n)) φ).ofConv a =
        χ.ofConv a * φ.ofConv 1 := by
    intro χ φ
    have h1 : (_root_.GlobalTheory.CartierDual.map
        (_root_.GlobalTheory.PDiv.mulBy R (G.A (n + 1)) (p ^ n)) φ).ofConv =
        (φ.ofConv ∘ₗ (M : G.A 1 →ₗ[R] G.A (n + 1))) ∘ₗ
          (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1) := by
      ext x
      simp [_root_.GlobalTheory.CartierDual.map_apply, hM]
    rw [_root_.GlobalTheory.CartierDual.mul_apply, _root_.GlobalTheory.CartierDual.pair_tmul, h1]
    have h2 : ∀ t, TensorProduct.map χ.ofConv
        ((φ.ofConv ∘ₗ (M : G.A 1 →ₗ[R] G.A (n + 1))) ∘ₗ
          (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1)) t =
        TensorProduct.map χ.ofConv
          (φ.ofConv ∘ₗ (M : G.A 1 →ₗ[R] G.A (n + 1)))
          (LinearMap.lTensor _
            (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1) t) := by
      intro t
      rw [LinearMap.lTensor, ← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id]
    rw [h2, ← _root_.GlobalTheory.PDivGroup.transl_apply, ha]
    simp
  let K : Ideal (_root_.GlobalTheory.CartierDual R (G.A (n + 1))) :=
    { carrier := {ψ | ∀ χ : _root_.GlobalTheory.CartierDual R (G.A (n + 1)), (χ * ψ).ofConv a = 0}
      add_mem' := by
        intro x y hx hy χ
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [mul_add, ofConv_add, LinearMap.add_apply, hx, hy, add_zero]
      zero_mem' := by
        intro χ
        simp
      smul_mem' := by
        intro c x hx χ
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
        rw [← mul_assoc]
        exact hx _ }
  have hK : _root_.GlobalTheory.PDiv.torsionIdeal R (_root_.GlobalTheory.CartierDual R (G.A (n + 1))) (p ^ n) ≤
      RingHom.ker (Ideal.Quotient.mkₐ R K) := by
    rw [_root_.GlobalTheory.PDiv.torsionIdeal_le_ker_iff,
      ← toConv_ofConv (toConv (Ideal.Quotient.mkₐ R K) ^ p ^ n),
      ← _root_.GlobalTheory.PDiv.comp_mulBy_pts]
    apply WithConv.ext
    rw [ofConv_toConv]
    ext φ
    show Ideal.Quotient.mkₐ R K (_root_.GlobalTheory.PDiv.mulBy R _ (p ^ n) φ) =
      algebraMap R _ (CoalgebraStruct.counit φ)
    rw [← _root_.GlobalTheory.PDiv.dual_mulBy, ← (Ideal.Quotient.mkₐ R K).commutes,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
    intro χ
    rw [mul_sub, ofConv_sub, LinearMap.sub_apply, key, Algebra.algebraMap_eq_smul_one, mul_smul_one,
      ofConv_smul, LinearMap.smul_apply, _root_.GlobalTheory.CartierDual.counit_apply, smul_eq_mul, mul_comm, sub_self]
  have hker : ∀ ψ, _root_.GlobalTheory.CartierDual.map (G.mulP n) ψ = 0 →
      ψ.ofConv a = 0 := by
    intro ψ hψ
    have h3 : ψ ∈ RingHom.ker (Ideal.Quotient.mkₐ R K) := by
      apply hK
      rw [← _root_.GlobalTheory.PDivGroup.ker_dual_mulP]
      exact hψ
    rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h3
    simpa using h3 1
  set πL : _root_.GlobalTheory.CartierDual R (G.A (n + 1)) →ₗ[R] _root_.GlobalTheory.CartierDual R (G.A n) :=
    (_root_.GlobalTheory.CartierDual.map (G.mulP n) :
      _root_.GlobalTheory.CartierDual R (G.A (n + 1)) →ₗ[R] _root_.GlobalTheory.CartierDual R (G.A n))
    with hπL
  have hs : Function.Surjective πL := _root_.GlobalTheory.PDivGroup.dual_mulP_surjective G n
  set evL : _root_.GlobalTheory.CartierDual R (G.A (n + 1)) →ₗ[R] R :=
    (_root_.GlobalTheory.CartierDual.cartierDualToBidual R (G.A (n + 1)) a).ofConv with hevL
  have hle : LinearMap.ker πL ≤ LinearMap.ker evL := by
    intro ψ hψ
    exact hker ψ hψ
  let L : _root_.GlobalTheory.CartierDual R (G.A n) →ₗ[R] R :=
    ((LinearMap.ker πL).liftQ evL hle).comp (πL.quotKerEquivOfSurjective hs).symm.toLinearMap
  have hL : ∀ ψ, L (πL ψ) = ψ.ofConv a := by
    intro ψ
    have h4 : (πL.quotKerEquivOfSurjective hs).symm (πL ψ) = Submodule.Quotient.mk ψ := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, h4, Submodule.liftQ_apply]
    rfl
  obtain ⟨e, he⟩ :=
    (_root_.GlobalTheory.CartierDual.toBidual_bijective (R := R) (M := G.A n)).2 (toConv L)
  refine ⟨e, (_root_.GlobalTheory.CartierDual.toBidual_bijective (R := R) (M := G.A (n + 1))).1 ?_⟩
  apply WithConv.ext
  ext ψ
  show ψ.ofConv (G.mulP n e) = ψ.ofConv a
  rw [← _root_.GlobalTheory.CartierDual.map_apply]
  have h5 := congrArg
    (fun x => x.ofConv (_root_.GlobalTheory.CartierDual.map (G.mulP n) ψ)) he
  simp only [ofConv_toConv] at h5
  rw [← hL ψ]
  exact h5
end _root_.GlobalTheory.PDivGroup
end GlobalTheory.PDivGroup
