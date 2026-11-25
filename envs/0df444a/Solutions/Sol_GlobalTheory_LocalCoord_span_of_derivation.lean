-- Prove2me | solution 1 for GlobalTheory.LocalCoord.span_of_derivation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:01.782931+00:00
-- url     : https://prove2.me/submissions/d0d0662e-d72e-4063-905a-0671dddf1918

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLocalCoordinates
import Theorems.Thm_GlobalTheory_ReducedAlg_isReduced_field_tensor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.LocalCoord
namespace GlobalTheory.LocalCoord
theorem _root_.solution {k A K B W : Type} [Field k] [PerfectField k] [CommRing A]
    [Algebra k A] [Field K] [Algebra k K] [CommRing B] [Algebra K B] [AddCommGroup W]
    [Module K W] [Module k W] [IsScalarTower k K W]
    (φ : K ⊗[k] A →ₐ[K] B) (χ : B →ₐ[K] K) {g : ℕ}
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ ≤ nilradical _)
    (t : Fin g → B) (s : B) (hs : χ s ≠ 0) (ht : ∀ i, χ (t i) = 0)
    (hb : ∀ b, χ b = 0 → s * b ∈ Ideal.span (Set.range t))
    (D : A →ₗ[k] W)
    (hD : ∀ a b, D (a * b) = χ (φ (1 ⊗ₜ a)) • D b + χ (φ (1 ⊗ₜ b)) • D a)
    (hN : ∀ a ∈ nilradical A, D a = 0) :
    ∃ w : Fin g → W, ∀ a, χ (φ (1 ⊗ₜ a)) = 0 → D a ∈ Submodule.span K (Set.range w) := by
  classical
  let E : K ⊗[k] A →ₗ[K] W := D.liftBaseChange K
  have hψ : ∀ (c : K) (a : A), χ (φ (c ⊗ₜ a)) = c * χ (φ (1 ⊗ₜ a)) := by
    intro c a
    rw [← smul_eq_mul, ← map_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hE : ∀ x y, E (x * y) = χ (φ x) • E y + χ (φ y) • E x := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' h h' => simp only [add_mul, map_add, h, h', add_smul, smul_add]; abel
    | tmul c a =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [mul_add, map_add, h, h', add_smul, smul_add]; abel
      | tmul d b =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hψ c, hψ d]
        simp only [E, LinearMap.liftBaseChange_tmul, hD, smul_add, smul_smul]
        congr 2 <;> ring
  have hEN : ∀ x ∈ nilradical (K ⊗[k] A), E x = 0 := by
    intro x hx
    haveI : IsReduced (A ⧸ nilradical A) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
    haveI := GlobalTheory.ReducedAlg.isReduced_field_tensor (k := k) K (A ⧸ nilradical A)
    let π := Algebra.TensorProduct.map (AlgHom.id k K) (Ideal.Quotient.mkₐ k (nilradical A))
    have h0 : π x = 0 := ((mem_nilradical.mp hx).map π).eq_zero
    let D' : (A ⧸ nilradical A) →ₗ[k] W :=
      (((nilradical A).restrictScalars k).liftQ D (fun a ha => hN a ha)).comp
        (Submodule.Quotient.restrictScalarsEquiv k (nilradical A)).symm.toLinearMap
    have key : ∀ y, E y = D'.liftBaseChange K (π y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [map_add, h, h']
      | tmul d b => rfl
    rw [key, h0, map_zero]
  choose l hl using hφ
  refine ⟨fun i => E (l (t i)), fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hb _ ha)
  have h1 : E (l s * 1 ⊗ₜ a - ∑ i, l (c i) * l (t i)) = 0 := by
    refine hEN _ (hker ?_)
    rw [RingHom.mem_ker, map_sub, map_mul, map_sum]
    simp only [map_mul, hl, hc, sub_self]
  rw [map_sub, map_sum, sub_eq_zero] at h1
  simp only [hE, hl, ha, ht, zero_smul, add_zero] at h1
  have h2 : E (1 ⊗ₜ a) = D a := by simp [E]
  rw [h2] at h1
  rw [← Submodule.smul_mem_iff _ hs, h1]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end GlobalTheory.LocalCoord
