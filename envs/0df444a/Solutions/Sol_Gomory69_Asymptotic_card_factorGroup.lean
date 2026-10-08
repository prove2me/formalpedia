-- Prove2me | solution 1 for Gomory69.Asymptotic.card_factorGroup
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:55:19.591409+00:00
-- url     : https://prove2.me/submissions/90f82ebc-a6e1-40e3-ae71-a6e341f3da9d

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_IntegerProgram



namespace Gomory69.Asymptotic

open Matrix

theorem lattice_eq_range {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) :
    basisLattice B = (LinearMap.range (Matrix.mulVecLin B)).toAddSubgroup := by
  apply le_antisymm
  · unfold basisLattice
    rw [AddSubgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    funext i
    simp [Matrix.mulVec_single_one]
  · rintro _ ⟨x, rfl⟩
    have : Matrix.mulVecLin B x = ∑ j, x j • (fun i => B i j) := by
      funext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    show Matrix.mulVecLin B x ∈ basisLattice B
    rw [this]
    refine AddSubgroup.sum_mem _ (fun j _ => ?_)
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self j)) _

theorem card_factor_core {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0) :
    Finite (FactorGroup B) ∧ Nat.card (FactorGroup B) = detAbs B := by
  have hinj : Function.Injective (Matrix.mulVecLin B) := by
    intro x y hxy
    have : B.mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hxy
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet this
    exact sub_eq_zero.mp h2
  let e : (Fin m → ℤ) ≃ₗ[ℤ] LinearMap.range (Matrix.mulVecLin B) :=
    LinearEquiv.ofInjective (Matrix.mulVecLin B) hinj
  have h := Submodule.natAbs_det_equiv (LinearMap.range (Matrix.mulVecLin B)) e
  have hcomp : (LinearMap.range (Matrix.mulVecLin B)).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap ((e : (Fin m → ℤ) →+ _)) = Matrix.mulVecLin B := by
    ext x : 1
    rfl
  have hd : LinearMap.det (Matrix.mulVecLin B) = B.det := by
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
  have hcard : Nat.card ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) = detAbs B := by
    rw [← h]
    unfold detAbs
    rw [hcomp, hd]
  have hfin : Finite ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    unfold detAbs
    exact Int.natAbs_ne_zero.mpr hdet
  have eq : FactorGroup B ≃ ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) :=
    (QuotientAddGroup.quotientAddEquivOfEq (lattice_eq_range B)).toEquiv
  exact ⟨Finite.of_equiv _ eq.symm, by rw [Nat.card_congr eq]; exact hcard⟩

end Gomory69.Asymptotic

open Gomory69.Asymptotic


theorem solution {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0) :
    Finite (FactorGroup B) ∧ Nat.card (FactorGroup B) = detAbs B := by
  exact card_factor_core B hdet
