-- Prove2me | solution 1 for GlobalTheory.nonempty_cubeHomology_equiv_of_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:19:27.435776+00:00
-- url     : https://prove2.me/submissions/4fbb006e-b63c-4d34-92cd-7da066666c33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_nonempty_homology_equiv_of_retract
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_extend
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_totalD_succ
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_totalD_zero
import Theorems.Thm_GlobalTheory_Cube_totalD_extend

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
    {W : Type*} [AddCommGroup W] [Module R W] (I : W →ₗ[R] ∀ s, A.obj s)
    (Q : (∀ s, A.obj s) →ₗ[R] W) (hI : ∀ w, totalD A (I w) = 0)
    (hPI : ∀ w, degProj A n (I w) = I w) (hQ : ∀ y, Q (totalD A y) = 0) (hQI : ∀ w, Q (I w) = w)
    (hex : ∀ x, totalD A x = 0 → degProj A n x = x → Q x = 0 → ∃ y, totalD A y = x) :
    Nonempty ((cubeComplex A).homology n ≃ₗ[R] W) := by
  have h1 : ∀ w, d A n (restrictDeg A n (I w)) = 0 := fun w => by
    rw [← restrictDeg_totalD_succ, hI, map_zero]
  have h2 : ∀ w, Q (extend A n (restrictDeg A n (I w))) = w := fun w =>
    (congrArg Q (hPI w)).trans (hQI w)
  have h3 : ∀ x : Term A n, d A n x = 0 → Q (extend A n x) = 0 →
      ∃ y, restrictDeg A n (totalD A y) = x := fun x hx hx' => by
    obtain ⟨y, hy⟩ := hex (extend A n x) (by rw [totalD_extend, hx, map_zero])
      (congrArg (extend A n) (restrictDeg_extend A n x)) hx'
    exact ⟨y, by rw [hy, restrictDeg_extend]⟩
  have hd : ∀ (p : ℕ) (x : Term A p), ((cubeComplex A).d p (p + 1)).hom x = d A p x :=
    fun p x => by rw [cubeComplex_d]; rfl
  cases n with
  | zero =>
    have h0 : (cubeComplex A).d 0 0 = 0 := (cubeComplex A).shape 0 0 (by simp)
    obtain ⟨e⟩ := nonempty_homology_equiv_of_retract ((cubeComplex A).sc' 0 0 1)
      (restrictDeg A 0 ∘ₗ I) (Q ∘ₗ extend A 0) (fun w => (hd 0 _).trans (h1 w))
      (fun y => by
        change Q (extend A 0 (((cubeComplex A).d 0 0).hom y)) = 0
        rw [h0]
        exact (congrArg Q (map_zero _)).trans (map_zero _)) h2
      (fun x hx hx' => by
        obtain ⟨y, hy⟩ := h3 x ((hd 0 _).symm.trans hx) hx'
        rw [restrictDeg_totalD_zero] at hy
        exact ⟨0, (map_zero _).trans hy⟩)
    exact ⟨((cubeComplex A).homologyIsoSc' 0 0 1 (by simp) (by simp)).toLinearEquiv ≪≫ₗ e⟩
  | succ n =>
    obtain ⟨e⟩ := nonempty_homology_equiv_of_retract ((cubeComplex A).sc' n (n + 1) (n + 1 + 1))
      (restrictDeg A (n + 1) ∘ₗ I) (Q ∘ₗ extend A (n + 1)) (fun w => (hd (n + 1) _).trans (h1 w))
      (fun y => by
        change Q (extend A (n + 1) (((cubeComplex A).d n (n + 1)).hom y)) = 0
        exact (congrArg (fun z => Q (extend A (n + 1) z)) (hd n y)).trans
          ((congrArg Q (totalD_extend A n y).symm).trans (hQ _))) h2
      (fun x hx hx' => by
        obtain ⟨y, hy⟩ := h3 x ((hd (n + 1) _).symm.trans hx) hx'
        rw [restrictDeg_totalD_succ] at hy
        exact ⟨_, (hd n _).trans hy⟩)
    exact ⟨((cubeComplex A).homologyIsoSc' n (n + 1) (n + 1 + 1) (by simp)
      (by simp)).toLinearEquiv ≪≫ₗ e⟩
end GlobalTheory
