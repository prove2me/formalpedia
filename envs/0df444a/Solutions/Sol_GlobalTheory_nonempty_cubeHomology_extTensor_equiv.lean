-- Prove2me | solution 1 for GlobalTheory.nonempty_cubeHomology_extTensor_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:41:58.149672+00:00
-- url     : https://prove2.me/submissions/50970bbe-47e1-4978-8bb6-576c1589c3e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_Cube_degProj_mul_degProj
import Theorems.Thm_GlobalTheory_Cube_degSign_mul_degSign
import Theorems.Thm_GlobalTheory_Cube_totalD_mul_degSign
import Theorems.Thm_GlobalTheory_nonempty_cubeHomology_equiv_of_homotopy
import Theorems.Thm_GlobalTheory_Cube_exists_contraction
import Theorems.Thm_GlobalTheory_tensor_homotopy
import Theorems.Thm_GlobalTheory_rangeRestrict_comp_subtype_of_orthogonal
import Theorems.Thm_GlobalTheory_exists_retraction_tensor_ranges
import Theorems.Thm_GlobalTheory_Cube_totalD_totalTensorEquiv
import Theorems.Thm_GlobalTheory_Cube_degProj_totalTensorEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube Finset.HasAntidiagonal Module
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] [Finite ι] [Finite κ] {K : Type u} [Field K]
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι K) (B : Cube.{v} κ K) (n : ℕ) :
    Nonempty ((cubeComplex (extTensor A B)).homology n ≃ₗ[K] ∀ x : antidiagonal n,
      (cubeComplex A).homology x.1.1 ⊗[K] (cubeComplex B).homology x.1.2) := by
  obtain ⟨e, h, hh, hDe, heD, hee, hPe, hεe, hεh⟩ := A.exists_contraction
  obtain ⟨e', h', hh', hDe', heD', hee', hPe', -, -⟩ := B.exists_contraction
  have orth : ∀ {ι : Type} (A : Cube.{v} ι K) (e : Module.End K (∀ s, A.obj s)), e * e = e →
      (∀ p, degProj A p * e = e * degProj A p) → ∀ p q, (e * degProj A p) * (e * degProj A q) =
        if p = q then e * degProj A p else 0 := fun A e hee hPe p q => by
    rw [mul_assoc, ← mul_assoc (degProj A p), hPe, ← mul_assoc, ← mul_assoc, hee, mul_assoc,
      degProj_mul_degProj]
    split_ifs <;> simp
  have hA := fun p => nonempty_cubeHomology_equiv_of_homotopy A p (LinearEquiv.refl K _) _ _ e h
    (fun _ => rfl) (fun _ => rfl) hh hDe heD (hPe p) (LinearMap.range (e * degProj A p)).subtype
    (e * degProj A p).rangeRestrict (fun _ => rfl)
    (fun w => congr($(rangeRestrict_comp_subtype_of_orthogonal (orth A e hee hPe) p) w))
  have hB := fun p => nonempty_cubeHomology_equiv_of_homotopy B p (LinearEquiv.refl K _) _ _ e' h'
    (fun _ => rfl) (fun _ => rfl) hh' hDe' heD' (hPe' p)
    (LinearMap.range (e' * degProj B p)).subtype (e' * degProj B p).rangeRestrict (fun _ => rfl)
    (fun w => congr($(rangeRestrict_comp_subtype_of_orthogonal (orth B e' hee' hPe') p) w))
  obtain ⟨I, Q, hIQ, hQI⟩ := exists_retraction_tensor_ranges (orth A e hee hPe)
    (orth B e' hee' hPe') (antidiagonal n)
  obtain ⟨E⟩ := nonempty_cubeHomology_equiv_of_homotopy (extTensor A B) n (totalTensorEquiv A B)
    _ _ (TensorProduct.map e e') _ (totalD_totalTensorEquiv A B) (degProj_totalTensorEquiv A B n)
    (tensor_homotopy hh hDe heD (totalD_mul_degSign A) hεe hεh (degSign_mul_degSign A) hh')
    (by simp [add_mul, ← TensorProduct.map_mul, hDe, hDe'])
    (by simp [mul_add, ← TensorProduct.map_mul, heD, heD'])
    (by simp only [Finset.sum_mul, Finset.mul_sum, ← TensorProduct.map_mul, hPe, hPe']) I Q
    (fun z => by
      rw [hIQ, ← Module.End.mul_apply, Finset.mul_sum, LinearMap.sum_apply]
      simp only [TensorProduct.map_mul]) hQI
  exact ⟨E ≪≫ₗ LinearEquiv.piCongrRight fun x =>
    TensorProduct.congr (hA x.1.1).some.symm (hB x.1.2).some.symm⟩
end GlobalTheory
