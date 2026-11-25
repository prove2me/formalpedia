-- Prove2me | solution 1 for GlobalTheory.flat_of_basis_mod_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:10.977719+00:00
-- url     : https://prove2.me/submissions/1fa4e50c-7d5c-4f7e-949f-0c1ce8dbd6d8

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Theorems.Thm_GlobalTheory_sup_pow_smul_top_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open RingTheory.Sequence IsLocalRing TensorProduct
open GlobalTheory
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
theorem _root_.solution [IsNoetherianRing A] (B : Type*) [CommRing B] [IsNoetherianRing B]
    [Algebra A B] [Module B M] [IsScalarTower A B M] [Module.Finite B M] {I : Ideal A}
    (hI : I.map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson) {S : Type*} (m : S → M)
    (hsurj : Submodule.span A (Set.range m) ⊔ I • ⊤ = ⊤)
    (hinj : ∀ (n : ℕ) (z : S →₀ A),
      Finsupp.linearCombination A m z ∈ (I ^ n • ⊤ : Submodule A M) → ∀ s, z s ∈ I ^ n) :
    Module.Flat A M := by
  rw [Module.Flat.iff_lTensor_injective']
  intro J
  haveI : SMulCommClass A B M := IsScalarTower.to_smulCommClass
  haveI : Module.Finite B (M ⊗[A] J) := by
    exact Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange A B B M J)
  let φ : (S →₀ J) →ₗ[A] M ⊗[A] J := Finsupp.lsum A fun s => TensorProduct.mk A M J (m s)
  have hφ : LinearMap.range φ ⊔ I • ⊤ = ⊤ := by
    rw [eq_top_iff]
    rintro t -
    induction t with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul y j =>
      have hy : y ∈ Submodule.span A (Set.range m) ⊔ I • ⊤ := by rw [hsurj]; trivial
      have := Submodule.mem_map_of_mem (f := (TensorProduct.mk A M J).flip j) hy
      rw [Submodule.map_sup, Submodule.map_smul''] at this
      refine SetLike.le_def.mp (sup_le_sup ?_ (Submodule.smul_mono le_rfl le_top)) this
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨Finsupp.single s j, by simp [φ]⟩
  let μ : M ⊗[A] J →ₗ[A] M := (TensorProduct.rid A M).toLinearMap ∘ₗ J.subtype.lTensor M
  have hμφ : ∀ w, μ (φ w) =
      Finsupp.linearCombination A m (Finsupp.mapRange.linearMap J.subtype w) := by
    intro w
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single s j => simp [μ, φ]
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul (M := A) J
  rw [injective_iff_map_eq_zero]
  intro t ht
  have hμt : μ t = 0 := by simp [μ, ht]
  have key : ∀ n : ℕ, t ∈ (I ^ n • ⊤ : Submodule A (M ⊗[A] J)) := by
    intro n
    have h1 : t ∈ LinearMap.range φ ⊔ I ^ (n + c) • ⊤ := by
      rw [sup_pow_smul_top_eq_top hφ]; trivial
    obtain ⟨_, ⟨w, rfl⟩, v, hv, rfl⟩ := Submodule.mem_sup.mp h1
    refine add_mem ?_ (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) hv)
    have h2 : μ (φ w) ∈ (I ^ (n + c) • ⊤ : Submodule A M) := by
      rw [map_add, add_eq_zero_iff_eq_neg] at hμt
      rw [hμt, neg_mem_iff]
      have := Submodule.mem_map_of_mem (f := μ) hv
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    rw [hμφ] at h2
    have h3 : ∀ s, w s ∈ (I ^ n • ⊤ : Submodule A J) := by
      intro s
      have h4 : (w s : A) ∈ (I ^ (n + c) • ⊤ ⊓ J : Submodule A A) :=
        ⟨by simpa using hinj _ _ h2 s, (w s).2⟩
      rw [hc _ (by omega), Nat.add_sub_cancel] at h4
      rw [Submodule.mem_smul_top_iff]
      exact Submodule.smul_mono le_rfl inf_le_right h4
    rw [show φ w = w.sum fun s j => m s ⊗ₜ j from rfl]
    refine Submodule.sum_mem _ fun s _ => ?_
    have := Submodule.mem_map_of_mem (f := TensorProduct.mk A M J (m s)) (h3 s)
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  have h0 := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M ⊗[A] J) _ hI
  rw [← Submodule.mem_bot B, ← h0, Submodule.mem_iInf]
  intro n
  rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem A, Ideal.smul_restrictScalars]
  exact key n
end GlobalTheory
