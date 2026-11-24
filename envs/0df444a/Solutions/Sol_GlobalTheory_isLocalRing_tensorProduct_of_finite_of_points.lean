-- Prove2me | solution 1 for GlobalTheory.isLocalRing_tensorProduct_of_finite_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:04:57.026274+00:00
-- url     : https://prove2.me/submissions/765e04ac-a301-4f2a-8825-e3830f5539bf

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_FormalChartAtZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsLocalRingTensorProductOfFiniteOfPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
namespace GlobalTheory
private theorem tenLocal_sub_mem {O A : Type} [CommRing O] [CommRing A] [IsLocalRing O]
    [IsLocalRing A] [Algebra O A] (φ : A →ₐ[O] O) (a : A) :
    a - algebraMap O A (φ a) ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro h
  have h2 := h.map φ
  simp at h2
end GlobalTheory
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  (∀ (O A A' : Type) [CommRing O] [CommRing A] [CommRing A'] [IsLocalRing O] [IsLocalRing A] [IsLocalRing A'] [Algebra O A] [Algebra O A']
    [Module.Finite O A] [Module.Finite O A'], (A →ₐ[O] O) → (A' →ₐ[O] O) → IsLocalRing (A ⊗[O] A')) := by
  intro O A A' _ _ _ _ _ _ _ _ _ _ φ φ'
  let Φ : A ⊗[O] A' →ₐ[O] O := Algebra.TensorProduct.productMap φ φ'
  have hsurj : Function.Surjective Φ := fun o => ⟨algebraMap _ _ o, Φ.commutes o⟩
  have hM0 : ((maximalIdeal O).comap Φ).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective Φ hsurj
  refine IsLocalRing.of_unique_max_ideal ⟨(maximalIdeal O).comap Φ, hM0, ?_⟩
  intro M hM
  have hint : Algebra.IsIntegral O (A ⊗[O] A') := Algebra.IsIntegral.of_finite _ _
  have key : ∀ {B : Type} [CommRing B] [IsLocalRing B] [Algebra O B] (f : B →ₐ[O] A ⊗[O] A'),
      M.comap f = maximalIdeal B := by
    intro B _ _ _ f
    have hf : (f : B →+* A ⊗[O] A').IsIntegral := by
      refine RingHom.IsIntegral.tower_top (algebraMap O B) _ ?_
      rw [f.comp_algebraMap]
      exact fun x => hint.isIntegral x
    have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (f : B →+* A ⊗[O] A') hf M
    exact IsLocalRing.eq_maximalIdeal this
  have hA := key (Algebra.TensorProduct.includeLeft : A →ₐ[O] A ⊗[O] A')
  have hA' := key (Algebra.TensorProduct.includeRight : A' →ₐ[O] A ⊗[O] A')
  have hO := key (Algebra.ofId O (A ⊗[O] A'))
  have hx : ∀ x : A ⊗[O] A', x - algebraMap O _ (Φ x) ∈ M := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      have := M.add_mem hx hy
      rw [map_add, map_add]
      convert this using 1
      ring
    | tmul a a' =>
      have h1 := tenLocal_sub_mem φ a
      have h2 := tenLocal_sub_mem φ' a'
      rw [← hA, Ideal.mem_comap, map_sub, AlgHom.commutes] at h1
      rw [← hA', Ideal.mem_comap, map_sub, AlgHom.commutes] at h2
      have h3 := M.add_mem
        (M.mul_mem_right ((Algebra.TensorProduct.includeRight : A' →ₐ[O] A ⊗[O] A') a') h1)
        (M.mul_mem_left (algebraMap O (A ⊗[O] A') (φ a)) h2)
      have e1 : a ⊗ₜ[O] a' = (Algebra.TensorProduct.includeLeft : A →ₐ[O] A ⊗[O] A') a *
          (Algebra.TensorProduct.includeRight : A' →ₐ[O] A ⊗[O] A') a' := by simp
      have e2 : Φ (a ⊗ₜ[O] a') = φ a * φ' a' := by simp [Φ]
      rw [e2, map_mul, e1]
      convert h3 using 1
      ring
  refine hM.eq_of_le hM0.ne_top ?_
  intro x hxM
  rw [Ideal.mem_comap, ← hO, Ideal.mem_comap]
  have := M.sub_mem hxM (hx x)
  simpa using this
end GlobalTheory
