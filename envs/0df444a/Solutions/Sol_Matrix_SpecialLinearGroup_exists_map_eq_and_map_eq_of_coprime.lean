-- Prove2me | solution 1 for Matrix.SpecialLinearGroup.exists_map_eq_and_map_eq_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/60c7d28b-a4e7-599e-af4c-adcc76e54a76

import Mathlib
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_SpecialLinearGroup_exists_map_eq_and_map_eq_of_coprime

open scoped MatrixGroups

namespace SL2CRTLift

noncomputable section

variable {m M : ℕ}

abbrev crt (h : m.Coprime M) : ZMod (m * M) ≃+* ZMod m × ZMod M := ZMod.chineseRemainder h

def π₁ (h : m.Coprime M) : ZMod (m * M) →+* ZMod m := (RingHom.fst _ _).comp (crt h).toRingHom

def π₂ (h : m.Coprime M) : ZMod (m * M) →+* ZMod M := (RingHom.snd _ _).comp (crt h).toRingHom

theorem π₁_apply (h : m.Coprime M) (x : ZMod (m * M)) : π₁ h x = (crt h x).1 := rfl

theorem π₂_apply (h : m.Coprime M) (x : ZMod (m * M)) : π₂ h x = (crt h x).2 := rfl

theorem crt_apply_eq (h : m.Coprime M) (x : ZMod (m * M)) : crt h x = (π₁ h x, π₂ h x) := rfl

def crtMat (h : m.Coprime M) (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) :
    Matrix (Fin 2) (Fin 2) (ZMod (m * M)) :=
  Matrix.of fun i j => (crt h).symm (A i j, B i j)

theorem π₁_crtMat (h : m.Coprime M) (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) (i j : Fin 2) :
    π₁ h (crtMat h A B i j) = A i j := by
  simp [π₁_apply, crtMat]

theorem π₂_crtMat (h : m.Coprime M) (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) (i j : Fin 2) :
    π₂ h (crtMat h A B i j) = B i j := by
  simp [π₂_apply, crtMat]

theorem mapMatrix_π₁_crtMat (h : m.Coprime M) (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) :
    (π₁ h).mapMatrix (crtMat h A B) = (A : Matrix (Fin 2) (Fin 2) (ZMod m)) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  exact π₁_crtMat h A B i j

theorem mapMatrix_π₂_crtMat (h : m.Coprime M) (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) :
    (π₂ h).mapMatrix (crtMat h A B) = (B : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  exact π₂_crtMat h A B i j

theorem det_crtMat (h : m.Coprime M) (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) :
    (crtMat h A B).det = 1 := by
  apply (crt h).injective
  rw [map_one, crt_apply_eq, RingHom.map_det, RingHom.map_det, mapMatrix_π₁_crtMat,
    mapMatrix_π₂_crtMat, Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe]
  rfl

def crtSL (h : m.Coprime M) (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) : SL(2, ZMod (m * M)) :=
  ⟨crtMat h A B, det_crtMat h A B⟩

theorem crtSL_apply (h : m.Coprime M) (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) (i j : Fin 2) :
    (crtSL h A B) i j = crtMat h A B i j := rfl

theorem π₁_intCast (h : m.Coprime M) (k : ℤ) : π₁ h (k : ZMod (m * M)) = (k : ZMod m) :=
  map_intCast (π₁ h) k

theorem π₂_intCast (h : m.Coprime M) (k : ℤ) : π₂ h (k : ZMod (m * M)) = (k : ZMod M) :=
  map_intCast (π₂ h) k

theorem main (m M : ℕ) [NeZero m] [NeZero M] (hmM : Nat.Coprime m M)
    (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) :
    ∃ γ : SL(2, ℤ), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m)) γ = A ∧
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = B := by
  haveI : NeZero (m * M) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne M)⟩
  obtain ⟨γ, hγ⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod (m * M) (crtSL hmM A B)

  have hent : ∀ i j : Fin 2, ((γ i j : ℤ) : ZMod (m * M)) = crtMat hmM A B i j := by
    intro i j
    have := congrArg (fun Y : SL(2, ZMod (m * M)) => Y i j) hγ
    simp at this
    exact this
  refine ⟨γ, ?_, ?_⟩
  · ext i j
    have h1 : (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m)) γ) i j = ((γ i j : ℤ) : ZMod m) := by
      simp
    rw [h1, ← π₁_intCast hmM, hent, π₁_crtMat]
  · ext i j
    have h1 : (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ) i j = ((γ i j : ℤ) : ZMod M) := by
      simp
    rw [h1, ← π₂_intCast hmM, hent, π₂_crtMat]

end

end SL2CRTLift

theorem solution
    (m M : ℕ) [NeZero m] [NeZero M] (hmM : Nat.Coprime m M)
    (A : SL(2, ZMod m)) (B : SL(2, ZMod M)) :
    ∃ γ : SL(2, ℤ), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m)) γ = A ∧
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = B :=
  SL2CRTLift.main m M hmM A B

end S_Matrix_SpecialLinearGroup_exists_map_eq_and_map_eq_of_coprime
end P2MW
export P2MW.S_Matrix_SpecialLinearGroup_exists_map_eq_and_map_eq_of_coprime (solution)
