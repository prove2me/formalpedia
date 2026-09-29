-- Prove2me | solution 1 for Module.Basis.exists_not_exists_eq_smul_and_forall_exists_sub_smul_eq_smul_of_mulVec_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/593199c0-3e9a-56f3-8f16-59b7636abe94

import Mathlib
import Theorems.Thm_Matrix_exists_ne_zero_forall_mulVec_eq_zero_of_forall_map_mulVec_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Basis_exists_not_exists_eq_smul_and_forall_exists_sub_smul_eq_smul_of_mulVec_eq_smul

set_option autoImplicit false

set_option maxHeartbeats 1600000

namespace Ws23
namespace LatticeLift

theorem main {Λ : Type*} [AddCommGroup Λ] {t : ℕ} (b : Module.Basis (Fin t) ℤ Λ)
    {I : Type*} (T : I → Λ →ₗ[ℤ] Λ) (n : I → ℤ)
    (p : ℕ) [Fact p.Prime] (κ : Type*) [Field κ] [CharP κ p]
    (m : Fin t → κ) (hm : m ≠ 0)
    (heig : ∀ i, ((LinearMap.toMatrix b b (T i)).map (Int.cast : ℤ → κ)).mulVec m = (n i : κ) • m) :
    ∃ v : Λ, (¬ ∃ w : Λ, v = (p : ℤ) • w) ∧ ∀ i, ∃ w : Λ, T i v - n i • v = (p : ℤ) • w := by
  classical
  letI : Algebra (ZMod p) κ := ZMod.algebra κ p

  set M : I → Matrix (Fin t) (Fin t) ℤ := fun i => LinearMap.toMatrix b b (T i) - (n i : ℤ) • 1 with hM
  set A : I → Matrix (Fin t) (Fin t) (ZMod p) := fun i => (M i).map (Int.castRingHom (ZMod p)) with hA

  have hcastκ : ∀ i, (A i).map (algebraMap (ZMod p) κ) = (M i).map (Int.castRingHom κ) := by
    intro i
    ext j k
    simp only [hA, Matrix.map_apply, eq_intCast, map_intCast]
  have hMκ : ∀ i, (M i).map (Int.castRingHom κ) = (LinearMap.toMatrix b b (T i)).map (Int.cast : ℤ → κ) - (n i : κ) • 1 := by
    intro i
    ext j k
    simp only [hM, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, eq_intCast, Int.cast_sub,
      smul_eq_mul, Int.cast_mul, mul_ite, mul_one, mul_zero]
    split_ifs <;> simp
  have hAv : ∀ i, ((A i).map (algebraMap (ZMod p) κ)).mulVec m = 0 := by
    intro i
    rw [hcastκ, hMκ, Matrix.sub_mulVec, heig i, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]

  obtain ⟨w, hw0, hw⟩ := Matrix.exists_ne_zero_forall_mulVec_eq_zero_of_forall_map_mulVec_eq_zero A m hm hAv

  set c : Fin t → ℤ := fun j => ((w j).val : ℤ) with hc
  have hcw : ∀ j, ((c j : ℤ) : ZMod p) = w j := fun j => by simp [hc]
  set v : Λ := b.equivFun.symm c with hv
  have hvc : b.equivFun v = c := by rw [hv, LinearEquiv.apply_symm_apply]
  refine ⟨v, ?_, fun i => ?_⟩
  ·
    rintro ⟨u, hu⟩
    apply hw0
    funext j
    have h1 : c j = (p : ℤ) * b.equivFun u j := by
      have := congrArg (fun x => b.equivFun x j) hu
      simpa [hvc, map_smul] using this
    rw [Pi.zero_apply, ← hcw j, h1]
    simp
  ·
    have hcoord : b.equivFun (T i v - n i • v) = (M i).mulVec c := by
      funext j
      rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, hvc, hM]
      dsimp only
      rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply]
      congr 1
      have h := LinearMap.toMatrix_mulVec_repr b b (T i) v

      have hv' : ⇑(b.repr v) = c := by
        funext k; rw [← hvc]; rfl
      rw [hv'] at h
      rw [h]
      rfl

    have hdvd : ∀ j, (p : ℤ) ∣ (M i).mulVec c j := by
      intro j
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hj := congrFun (hw i) j
      rw [Pi.zero_apply] at hj
      rw [← hj]
      have hmv := RingHom.map_mulVec (Int.castRingHom (ZMod p)) (M i) c j
      rw [eq_intCast] at hmv
      rw [hmv, hA]
      dsimp only
      congr 1
      funext k
      exact hcw k
    choose d hd using hdvd
    refine ⟨b.equivFun.symm d, ?_⟩
    apply b.equivFun.injective
    rw [hcoord, map_smul, LinearEquiv.apply_symm_apply]
    funext j
    rw [hd j, Pi.smul_apply, smul_eq_mul]

end Ws23.LatticeLift

theorem solution
    {Λ : Type*} [AddCommGroup Λ] {t : ℕ} (b : Module.Basis (Fin t) ℤ Λ)
    {I : Type*} (T : I → Λ →ₗ[ℤ] Λ) (n : I → ℤ)
    (p : ℕ) [Fact p.Prime] (κ : Type*) [Field κ] [CharP κ p]
    (m : Fin t → κ) (hm : m ≠ 0)
    (heig : ∀ i, ((LinearMap.toMatrix b b (T i)).map (Int.cast : ℤ → κ)).mulVec m = (n i : κ) • m) :
    ∃ v : Λ, (¬ ∃ w : Λ, v = (p : ℤ) • w) ∧ ∀ i, ∃ w : Λ, T i v - n i • v = (p : ℤ) • w :=
  Ws23.LatticeLift.main b T n p κ m hm heig

end S_Module_Basis_exists_not_exists_eq_smul_and_forall_exists_sub_smul_eq_smul_of_mulVec_eq_smul
end P2MW
export P2MW.S_Module_Basis_exists_not_exists_eq_smul_and_forall_exists_sub_smul_eq_smul_of_mulVec_eq_smul (solution)
