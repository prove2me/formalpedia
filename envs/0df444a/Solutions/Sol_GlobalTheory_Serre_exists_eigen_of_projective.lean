-- Prove2me | solution 1 for GlobalTheory.Serre.exists_eigen_of_projective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:45:36.459265+00:00
-- url     : https://prove2.me/submissions/9c976b73-9a26-4b21-acea-7dc4ee0394df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedRingOfIntegers
import Theorems.Thm_GlobalTheory_Serre_mulChar_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Serre.mulChar_tmul

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.Serre
variable {R O O' : Type*} [CommRing R] [CommRing O] [CommRing O'] [Algebra O O'] [Algebra O R]
  [Algebra O' R] [IsScalarTower O O' R]
variable {M : Type*} [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M]
omit [Algebra O R]
namespace GlobalTheory.Serre
theorem _root_.solution (M : Type*) [AddCommGroup M] [Module O M] [Module.Finite O M]
    [Module.Projective O M] {N L : Type*} [AddCommGroup N] [Module R N] [Module O N]
    [SMulCommClass O R N] [AddCommGroup L] [Module R L] [Module O L] [SMulCommClass O R L]
    (τ : O → R) (i : N →ₗ[R] L) (hi : Function.Injective i)
    (hlin : ∀ (x : O) n, i (x • n) = x • i n)
    (hr : ∀ l, l ∈ LinearMap.range i ↔ ∀ x : O, x • l = τ x • l) :
    ∃ j : N ⊗[O] M →ₗ[R] L ⊗[O] M, (∀ n m, j (n ⊗ₜ m) = i n ⊗ₜ m) ∧ Function.Injective j ∧
      ∀ z, z ∈ LinearMap.range j ↔ ∀ x : O, x • z = τ x • z := by
  let i' : N →ₗ[O] L := { i.toAddHom with map_smul' := hlin }
  let j : N ⊗[O] M →ₗ[R] L ⊗[O] M :=
    { (i'.rTensor M).toAddHom with
      map_smul' := fun r z ↦ by
        change i'.rTensor M (r • z) = r • i'.rTensor M z
        induction z with
        | zero => simp
        | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']
        | tmul n m => simp [smul_tmul', i'] }
  refine ⟨j, fun _ _ ↦ rfl, Module.Flat.rTensor_preserves_injective_linearMap i' hi,
    fun z ↦ ⟨?_, fun hz ↦ ?_⟩⟩
  · rintro ⟨z, rfl⟩ x
    induction z with
    | zero => simp
    | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']
    | tmul n m =>
      change (x • i n) ⊗ₜ[O] m = (τ x • i n) ⊗ₜ[O] m
      rw [(hr _).mp ⟨n, rfl⟩]
  · obtain ⟨n, t, s, -, -, hst⟩ := Module.Finite.exists_comp_eq_id_of_projective O M
    let c (k : Fin n) : L ⊗[O] M →ₗ[O] L :=
      (TensorProduct.rid O L).toLinearMap ∘ₗ (LinearMap.proj k ∘ₗ s).lTensor L
    have hc : ∀ k (r : R) z, c k (r • z) = r • c k z := fun k r z ↦ by
      induction z with
      | zero => simp
      | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']
      | tmul l m => simpa [smul_tmul', c] using smul_comm _ r l
    have hsum : ∀ z, ∑ k, c k z ⊗ₜ[O] t (Pi.single k 1) = z := fun z ↦ by
      induction z with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, add_tmul, Finset.sum_add_distrib, hz, hz']
      | tmul l m =>
        have hm : t (s m) = m := congr($hst m)
        conv_rhs => rw [← hm, pi_eq_sum_univ' (s m)]
        simp [c, smul_tmul, tmul_sum]
    choose u hu using fun k ↦ (hr (c k z)).mpr fun x ↦ by rw [← map_smul, hz, hc]
    refine ⟨∑ k, u k ⊗ₜ t (Pi.single k 1), ?_⟩
    rw [map_sum, ← hsum z]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [← hu]; rfl
end GlobalTheory.Serre
