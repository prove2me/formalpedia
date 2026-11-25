-- Prove2me | solution 1 for GlobalTheory.Cube.exists_contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:19:23.861455+00:00
-- url     : https://prove2.me/submissions/d2527346-53cc-455b-8a08-eba087b807c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_Cube_ext_restrictDeg
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_degProj
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_degSign
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_totalD_succ
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_totalD_zero
import Theorems.Thm_GlobalTheory_Cube_totalD_mul_degSign
import Theorems.Thm_GlobalTheory_exists_comp_comp_eq_of_field

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
variable {ι : Type} [LinearOrder ι] {K : Type u} [Field K]
open GlobalTheory.Cube
namespace GlobalTheory
namespace Cube
theorem _root_.solution (A : Cube.{v} ι K) : ∃ e h : Module.End K (∀ s, A.obj s),
    1 - e = (totalD A : Module.End K _) * h + h * totalD A ∧
    (totalD A : Module.End K _) * e = 0 ∧ e * totalD A = 0 ∧ e * e = e ∧
    (∀ p, degProj A p * e = e * degProj A p) ∧ degSign A * e = e * degSign A ∧
    degSign A * h = -(h * degSign A) := by
  choose g hg using fun p => exists_comp_comp_eq_of_field (d A p)
  set D : Module.End K (∀ s, A.obj s) := totalD A with hD
  let h : Module.End K (∀ s, A.obj s) := LinearMap.pi fun s =>
    LinearMap.proj (φ := fun t : {t : Finset ι // t.card = s.card} => A.obj t.1) ⟨s, rfl⟩ ∘ₗ
      g s.card ∘ₗ restrictDeg A (s.card + 1)
  have hr : ∀ p x, restrictDeg A p (h x) = g p (restrictDeg A (p + 1) x) := fun p x => by
    funext ⟨s, hs⟩
    subst hs
    rfl
  have hDD : D * D = 0 := LinearMap.ext (totalD_totalD A)
  have hDhD : D * h * D = D := LinearMap.ext fun x => ext_restrictDeg fun p => by
    simp only [Module.End.mul_apply, hD]
    cases p with
    | zero => rw [restrictDeg_totalD_zero, restrictDeg_totalD_zero]
    | succ p => rw [restrictDeg_totalD_succ, hr, restrictDeg_totalD_succ, hg]
  have hεh : degSign A * h = -(h * degSign A) := LinearMap.ext fun x => ext_restrictDeg fun p => by
    simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, restrictDeg_degSign, hr,
      map_zsmul, pow_succ]
    simp
  have hDε : D * degSign A = -(degSign A * D) := totalD_mul_degSign A
  have hP : ∀ q, degProj A q * (D * h + h * D) = (D * h + h * D) * degProj A q := fun q =>
    LinearMap.ext fun x => ext_restrictDeg fun p => by
      simp only [Module.End.mul_apply, LinearMap.add_apply, map_add, restrictDeg_degProj, hD, hr,
        restrictDeg_totalD_succ]
      cases p with
      | zero => split_ifs <;> simp [restrictDeg_totalD_zero]
      | succ p =>
        simp only [restrictDeg_totalD_succ, hr, restrictDeg_degProj]
        split_ifs <;> simp
  obtain ⟨e, he⟩ : ∃ e : Module.End K (∀ s, A.obj s), e = 1 - (D * h + h * D) := ⟨_, rfl⟩
  have h1 : D * e = 0 := by
    rw [he, mul_sub, mul_add, ← mul_assoc, ← mul_assoc, hDD, hDhD]; simp
  have h2 : e * D = 0 := by
    rw [he, sub_mul, add_mul, mul_assoc h, hDD, hDhD]; simp
  have h3 : e * e * e = e * e := by
    have : e * e * e = e * (1 - (D * h + h * D)) * e := by rw [← he]
    rw [this, mul_sub, mul_add, ← mul_assoc, h2, sub_mul, add_mul, mul_assoc e (h * D),
      mul_assoc h, h1]
    simp
  have h4 : ∀ q, degProj A q * e = e * degProj A q := fun q => by
    rw [he, mul_sub, sub_mul, hP]; simp
  have h5 : degSign A * e = e * degSign A := by
    have a1 : degSign A * (D * h) = D * h * degSign A := by
      rw [mul_assoc, ← neg_neg (h * _), ← hεh, mul_neg, ← mul_assoc D, hDε]; simp [mul_assoc]
    have a2 : degSign A * (h * D) = h * D * degSign A := by
      rw [mul_assoc, hDε, ← mul_assoc, hεh]; simp [mul_assoc]
    rw [he, mul_sub, sub_mul, mul_add, add_mul, a1, a2]; simp
  refine ⟨e * e, h + e * h, ?_, ?_, ?_, ?_, fun q => ?_, ?_, ?_⟩
  · have : e * e = e * (1 - (D * h + h * D)) := by rw [← he]
    rw [this, mul_sub, mul_add e, ← mul_assoc e D, h2, mul_add D, ← mul_assoc D e, h1, add_mul,
      ← mul_assoc]
    simp only [mul_one, zero_mul, zero_add, add_zero]
    nth_rewrite 1 [he]
    abel
  · rw [← mul_assoc, h1, zero_mul]
  · rw [mul_assoc, h2, mul_zero]
  · rw [← mul_assoc, h3, h3]
  · rw [← mul_assoc, h4, mul_assoc, h4, mul_assoc]
  · rw [← mul_assoc, h5, mul_assoc, h5, mul_assoc]
  · rw [mul_add, ← mul_assoc, h5, mul_assoc, hεh, add_mul, mul_neg, mul_assoc, neg_add]
end Cube
end GlobalTheory
