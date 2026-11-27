-- Prove2me | solution 1 for GlobalTheory.TwistTie.exists_det_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:34:30.157974+00:00
-- url     : https://prove2.me/submissions/e7ed7c0d-3aab-4b79-97ce-705c5c6629da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_DetSubMemOfConj
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TwistTie
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix
namespace GlobalTheory.TwistTie
theorem _root_.solution {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (I : Ideal R)
    {r : ℕ} (hr : 1 ≤ r) (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) :
    ∃ δ : (Q ≃ₗ[R] Q) →* (R ⧸ I)ˣ, Function.Surjective δ ∧ ∀ (k : Q ≃ₗ[R] Q) (a : Matrix (Fin r) (Fin r) R),
      (∀ j, k (e.symm (Pi.single j 1)) = ∑ i, a i j • e.symm (Pi.single i 1)) →
        (δ k : R ⧸ I) = Ideal.Quotient.mk I a.det := by
  classical
  have hs : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  let cj : (Q ≃ₗ[R] Q) →* ((Fin r → R ⧸ I) ≃ₗ[R ⧸ I] (Fin r → R ⧸ I)) :=
    MonoidHom.mk' (fun k => (e.symm ≪≫ₗ k ≪≫ₗ e).extendScalarsOfSurjective hs) (fun a b => by
      ext x i
      simp [LinearEquiv.mul_apply])
  refine ⟨LinearEquiv.det.comp cj, fun u => ?_, fun k a ha => ?_⟩
  · let i₀ : Fin r := ⟨0, hr⟩
    let δ : (R ⧸ I)ˣ → Fin r → R ⧸ I := fun w => Function.update 1 i₀ w
    have hδ : ∀ w w' : (R ⧸ I)ˣ, w * w' = 1 → Matrix.diagonal (δ w) * Matrix.diagonal (δ w') = 1 := by
      intro w w' hw
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      by_cases h : i = i₀
      · subst h
        simp only [δ, Function.update_self]
        rw [← Units.val_mul, hw, Units.val_one]
      · simp [δ, h]
    let g : (Fin r → R ⧸ I) ≃ₗ[R ⧸ I] (Fin r → R ⧸ I) :=
      Matrix.toLin'OfInv (hδ u⁻¹ u (inv_mul_cancel u)) (hδ u u⁻¹ (mul_inv_cancel u))
    have hg : LinearEquiv.det g = u := by
      apply Units.ext
      rw [LinearEquiv.coe_det]
      have : (g : (Fin r → R ⧸ I) →ₗ[R ⧸ I] (Fin r → R ⧸ I)) = Matrix.toLin' (Matrix.diagonal (δ u)) := rfl
      rw [this, LinearMap.det_toLin', Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp
    have hk : cj (e ≪≫ₗ g.restrictScalars R ≪≫ₗ e.symm) = g := by
      ext x i
      simp [cj]
    exact ⟨e ≪≫ₗ g.restrictScalars R ≪≫ₗ e.symm, by rw [MonoidHom.comp_apply, hk, hg]⟩
  · rw [MonoidHom.comp_apply, LinearEquiv.coe_det, RingHom.map_det, ← LinearMap.det_toMatrix']
    congr 1
    ext i j
    rw [LinearMap.toMatrix'_apply]
    change e (k (e.symm (Pi.single j 1))) i = Ideal.Quotient.mk I (a i j)
    rw [ha, map_sum, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [map_smul, e.apply_symm_apply, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one]
      rfl
    · intro b _ hb
      rw [map_smul, e.apply_symm_apply, Pi.smul_apply, Pi.single_eq_of_ne hb.symm, smul_zero]
    · simp
end GlobalTheory.TwistTie
