-- Prove2me | solution 1 for GlobalTheory.nonempty_cubeHomology_equiv_of_homotopy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:28:15.134705+00:00
-- url     : https://prove2.me/submissions/26b34646-7628-4073-aa6d-24f4b03358ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_Cube_degProj_mul_degProj
import Theorems.Thm_GlobalTheory_nonempty_cubeHomology_equiv_of_retract

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
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
open GlobalTheory.Cube
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι R) (n : ℕ)
    {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (Φ : V ≃ₗ[R] ∀ s, A.obj s) (T P e h : Module.End R V)
    (hT : ∀ x, totalD A (Φ x) = Φ (T x)) (hP : ∀ x, degProj A n (Φ x) = Φ (P x))
    (hh : 1 - e = T * h + h * T) (hTe : T * e = 0) (heT : e * T = 0) (heP : P * e = e * P)
    (I : W →ₗ[R] V) (Q : V →ₗ[R] W) (hIQ : ∀ x, I (Q x) = e (P x)) (hQI : ∀ w, Q (I w) = w) :
    Nonempty ((cubeComplex A).homology n ≃ₗ[R] W) := by
  have hPe : ∀ x, P (e x) = e (P x) := fun x => congr($heP x)
  have hPP : ∀ x, P (P x) = P x := fun x => Φ.injective (by
    rw [← hP, ← hP]
    have := degProj_mul_degProj A n n
    rw [if_pos rfl] at this
    exact congr($this (Φ x)))
  have hI : ∀ w, e (P (I w)) = I w := fun w => by rw [← hIQ, hQI]
  refine nonempty_cubeHomology_equiv_of_retract A n (Φ.toLinearMap ∘ₗ I) (Q ∘ₗ Φ.symm.toLinearMap)
    (fun w => ?_) (fun w => ?_) (fun y => ?_) (fun w => by simp [hQI]) fun x hx hx' hx'' => ?_
  · change totalD A (Φ (I w)) = 0
    have : T (e (P (I w))) = 0 := congr($hTe (P (I w)))
    rw [hT, ← hI, this, map_zero]
  · change degProj A n (Φ (I w)) = Φ (I w)
    rw [hP, ← hI, hPe, hPP]
  · obtain ⟨y, rfl⟩ := Φ.surjective y
    have : e (T y) = 0 := congr($heT y)
    rw [hT]
    change Q (Φ.symm (Φ (T y))) = 0
    rw [Φ.symm_apply_apply, ← hQI (Q _), hIQ, ← hPe, this, map_zero, map_zero]
  · obtain ⟨x, rfl⟩ := Φ.surjective x
    rw [hT, map_eq_zero_iff _ Φ.injective] at hx
    rw [hP, Φ.injective.eq_iff] at hx'
    change Q (Φ.symm (Φ x)) = 0 at hx''
    rw [Φ.symm_apply_apply] at hx''
    have h1 : e x = 0 := by rw [← hx', ← hIQ, hx'', map_zero]
    have h2 : x - e x = T (h x) + h (T x) := congr($hh x)
    rw [h1, hx, map_zero, add_zero, sub_zero] at h2
    exact ⟨Φ (h x), by rw [hT, ← h2]⟩
end GlobalTheory
