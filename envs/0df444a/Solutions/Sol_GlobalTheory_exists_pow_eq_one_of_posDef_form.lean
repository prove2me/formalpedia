-- Prove2me | solution 1 for GlobalTheory.exists_pow_eq_one_of_posDef_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:45:46.460869+00:00
-- url     : https://prove2.me/submissions/e1fa75f0-1272-4b2a-9549-228dcc7f95f2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsPowEqOneOfPosDefForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (b : LinearMap.BilinForm ℤ Y) (hs : ∀ y z, b y z = b z y) (hp : ∀ y, y ≠ 0 → 0 < b y y)
    (σ : Y ≃ₗ[ℤ] Y) (hσ : ∀ y z, b (σ y) (σ z) = b y z) : ∃ n : ℕ, 0 < n ∧ σ ^ n = 1 := by
  classical
  rw [← isOfFinOrder_iff_pow_eq_one]
  by_contra hfin
  have hinj := injective_pow_iff_not_isOfFinOrder.mpr hfin
  let e := Module.Free.chooseBasis ℤ Y
  have h0 : ∀ y, 0 ≤ b y y := fun y => by
    by_cases h : y = 0
    · simp [h]
    · exact (hp y h).le
  have hpow : ∀ (n : ℕ) y, b ((σ ^ n) y) ((σ ^ n) y) = b y y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih => intro y; rw [pow_succ', LinearEquiv.mul_apply, hσ, ih]
  have hnd : ∀ y, (∀ j, b y (e j) = 0) → y = 0 := by
    intro y hy
    by_contra h
    have : b y = 0 := e.ext fun j => by simpa using hy j
    have h2 := hp y h
    simp [this] at h2
  let f : ℕ → (_ → _ → ℤ) := fun n i j => b ((σ ^ n) (e i)) (e j)
  have hf : Function.Injective f := by
    intro m n h
    apply hinj
    apply LinearEquiv.toLinearMap_injective
    refine e.ext fun i => ?_
    rw [← sub_eq_zero]
    apply hnd
    intro j
    have := congrFun (congrFun h i) j
    simp only [f] at this
    simp [this]
  let C : _ → _ → ℤ := fun i j => b (e i) (e i) * b (e j) (e j)
  have hS : (Set.univ.pi fun i => Set.univ.pi fun j => Set.Icc (-C i j) (C i j)).Finite :=
    Set.Finite.pi fun i => Set.Finite.pi fun j => Set.finite_Icc _ _
  refine Set.infinite_of_injective_forall_mem hf (fun n => ?_) hS
  intro i _ j _
  have h1 := LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le b h0 ((σ ^ n) (e i)) (e j)
  rw [hpow, hs (e j), hs (e j)] at h1
  have h2 : f n i j ^ 2 ≤ C i j := by
    simp only [f, C]; nlinarith [h1]
  constructor <;> nlinarith [h2, sq_nonneg (f n i j - 1), sq_nonneg (f n i j + 1), Int.le_self_sq (f n i j), Int.le_self_sq (-f n i j)]
end GlobalTheory
