-- Prove2me | solution 1 for GlobalTheory.PicPi.eq_one_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:42:32.700719+00:00
-- url     : https://prove2.me/submissions/a7915122-46cd-4c19-9bcd-b9784441398e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicPiIsOfFinOrder
import Theorems.Thm_GlobalTheory_PicPi_exists_one_tmul
import Theorems.Thm_GlobalTheory_PicPi_single_smul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
open GlobalTheory.PicPi
variable {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] [DecidableEq ι]
variable [Fintype ι]
namespace GlobalTheory.PicPi
theorem _root_.solution (M : CommRing.Pic ((j : ι) → R j))
    (h : ∀ i, CommRing.Pic.mapRingHom (Pi.evalRingHom R i) M = 1) : M = 1 := by
  letI inst : ∀ i, Algebra ((j : ι) → R j) (R i) := fun i => (Pi.evalRingHom R i).toAlgebra
  have hA : ∀ i, algebraMap ((j : ι) → R j) (R i) = Pi.evalRingHom R i := fun i => rfl
  have e : ∀ i, (R i ⊗[(j : ι) → R j] M) ≃ₗ[R i] R i := by
    intro i
    have hi := h i
    rw [← hA i, CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapAlgebra_apply,
      CommRing.Pic.mk_eq_one_iff] at hi
    exact hi.some
  choose m hm using fun i => exists_one_tmul i M (hA i) ((e i).symm 1)
  let m₀ : M := ∑ i, (Pi.single i 1 : (j : ι) → R j) • m i
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton ((j : ι) → R j) M m₀) := by
    intro x
    refine ⟨fun i => e i ((1 : R i) ⊗ₜ x), ?_⟩
    have key : ∀ i, (Pi.single i 1 : (j : ι) → R j) • x =
        (Pi.single i (e i ((1 : R i) ⊗ₜ x)) : (j : ι) → R j) • m i := by
      intro i
      set r := e i ((1 : R i) ⊗ₜ x) with hr
      have h1 : (1 : R i) ⊗ₜ[(j : ι) → R j] x =
          (1 : R i) ⊗ₜ ((Pi.single i r : (j : ι) → R j) • m i) := by
        apply (e i).injective
        rw [← TensorProduct.smul_tmul]
        have h0 : (Pi.single i r : (j : ι) → R j) • (1 : R i) = r := by
          rw [Algebra.smul_def, hA i]; simp
        rw [h0]
        have h5 : (r ⊗ₜ[(j : ι) → R j] m i : R i ⊗[(j : ι) → R j] M) = r • ((1 : R i) ⊗ₜ m i) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [h5, map_smul, hm i, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
      have h2 : (1 : R i) ⊗ₜ[(j : ι) → R j] (x - (Pi.single i r : (j : ι) → R j) • m i) = 0 := by
        rw [TensorProduct.tmul_sub, h1, sub_self]
      have h3 := single_smul_eq_zero i M (hA i) _ h2
      rw [smul_sub, sub_eq_zero, smul_smul] at h3
      rw [h3, ← Pi.single_mul, one_mul]
    rw [LinearMap.toSpanSingleton_apply, Finset.smul_sum]
    have hs : ∀ i, (fun i => e i ((1 : R i) ⊗ₜ x) : (j : ι) → R j) •
        (Pi.single i 1 : (j : ι) → R j) • m i = (Pi.single i 1 : (j : ι) → R j) • x := by
      intro i
      rw [key i, smul_smul]
      congr 1
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [Finset.sum_congr rfl (fun i _ => hs i), ← Finset.sum_smul]
    have h1 : ∑ i, (Pi.single i 1 : (j : ι) → R j) = 1 := by
      simpa using Finset.univ_sum_single (1 : (j : ι) → R j)
    rw [h1, one_smul]
  have hbij := Module.Invertible.bijective_of_surjective hsurj
  exact CommRing.Pic.mk_eq_self.symm.trans
    (CommRing.Pic.mk_eq_one_iff.mpr ⟨(LinearEquiv.ofBijective _ hbij).symm⟩)
end GlobalTheory.PicPi
