-- Prove2me | solution 1 for GlobalTheory.IwahoriFactor.factor_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:57:34.845872+00:00
-- url     : https://prove2.me/submissions/f36c9fec-8f0f-450d-b4df-adc5b98ccb3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdInvOfBlockTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.IwahoriFactor
variable {O : Type} [CommRing O] {n : ℕ}
namespace GlobalTheory.IwahoriFactor
theorem _root_.solution {α β α' β' : O} {u u' l l' : Matrix (Fin n) (Fin n) O} {d d' : Fin n → Oˣ}
    (hu : UpperUnip α u) (hu' : UpperUnip α' u') (hl : LowerUnip β l) (hl' : LowerUnip β' l')
    (h : u * Matrix.diagonal (fun i => (d i : O)) * l =
      u' * Matrix.diagonal (fun i => (d' i : O)) * l') :
    u = u' ∧ d = d' ∧ l = l' := by
  have iu' : IsUnit u'.det := by rw [hu'.det]; exact isUnit_one
  have il : IsUnit l.det := by rw [hl.det]; exact isUnit_one
  letI := u'.invertibleOfIsUnitDet iu'
  letI := l.invertibleOfIsUnitDet il
  have tu : u.BlockTriangular id := fun i j h => (hu i j).1 h
  have tu' : u'.BlockTriangular id := fun i j h => (hu' i j).1 h
  have tl : l.BlockTriangular OrderDual.toDual := fun i j h => (hl i j).1 h
  have tl' : l'.BlockTriangular OrderDual.toDual := fun i j h => (hl' i j).1 h
  set X := u'⁻¹ * (u * Matrix.diagonal (fun i => (d i : O))) with hX
  have e1 : u' * X = u * Matrix.diagonal (fun i => (d i : O)) := by
    rw [hX, Matrix.mul_nonsing_inv_cancel_left _ _ iu']
  have e2 : X * l = Matrix.diagonal (fun i => (d' i : O)) * l' := by
    rw [hX, Matrix.mul_assoc, h, Matrix.mul_assoc u', Matrix.nonsing_inv_mul_cancel_left _ _ iu']
  have e3 : X = Matrix.diagonal (fun i => (d' i : O)) * l' * l⁻¹ := by
    rw [← e2, Matrix.mul_nonsing_inv_cancel_right _ _ il]
  have tX : X.BlockTriangular id :=
    (Matrix.blockTriangular_inv_of_blockTriangular tu').mul
      (tu.mul (Matrix.blockTriangular_diagonal _))
  have tX' : X.BlockTriangular OrderDual.toDual := by
    rw [e3]
    exact ((Matrix.blockTriangular_diagonal _).mul tl').mul
      (Matrix.blockTriangular_inv_of_blockTriangular tl)
  have hd : X = Matrix.diagonal (fun i => X i i) := by
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [Matrix.diagonal_apply_ne _ h.ne]; exact tX' h
    · rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h.ne']; exact tX h
  rw [hd] at e1 e2
  have f1 : ∀ i j, u' i j * X j j = u i j * d j := fun i j => by
    simpa [Matrix.mul_diagonal] using congrFun (congrFun e1 i) j
  have f2 : ∀ i j, X i i * l i j = d' i * l' i j := fun i j => by
    simpa [Matrix.diagonal_mul] using congrFun (congrFun e2 i) j
  have g1 : ∀ i, X i i = d i := fun i => by
    simpa [(hu i i).2.1 rfl, (hu' i i).2.1 rfl] using f1 i i
  have g2 : ∀ i, X i i = d' i := fun i => by
    simpa [(hl i i).2.1 rfl, (hl' i i).2.1 rfl] using f2 i i
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have := f1 i j
    rw [g1] at this
    exact ((Units.mul_left_inj _).1 this).symm
  · funext i
    exact Units.ext ((g1 i).symm.trans (g2 i))
  · ext i j
    have := f2 i j
    rw [g2] at this
    exact (Units.mul_right_inj _).1 this
end GlobalTheory.IwahoriFactor
