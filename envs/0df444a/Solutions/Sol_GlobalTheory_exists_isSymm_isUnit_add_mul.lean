-- Prove2me | solution 1 for GlobalTheory.exists_isSymm_isUnit_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:42:37.010682+00:00
-- url     : https://prove2.me/submissions/31d1a616-6070-475b-bd68-74231ceba446

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_isUnit_of_forall_maximalSpectrum_mk_ne_zero
import Theorems.Thm_GlobalTheory_exists_lift_maximalSpectrum_pi
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.coe_symplecticGroupMap

set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
variable {S R : Type*} [CommRing S] [CommRing R] {f : S →+* R}
  {l : Type*} [Fintype l] [DecidableEq l]
namespace GlobalTheory
theorem _root_.solution [Finite (MaximalSpectrum R)] {A B C D : Matrix l l R}
    (h : fromBlocks A B C D ∈ symplecticGroup l R) :
    ∃ X : Matrix l l R, X.IsSymm ∧ IsUnit (A + X * C).det := by
  have key : ∀ p : MaximalSpectrum R, ∃ Y : Matrix l l (R ⧸ p.asIdeal), Y.IsSymm ∧
      IsUnit (A.map (Ideal.Quotient.mk p.asIdeal) + Y * C.map (Ideal.Quotient.mk p.asIdeal)) := by
    intro p
    have := p.isMaximal
    let _ := Ideal.Quotient.field p.asIdeal
    have h' := SymplecticGroup.map_mem h (Ideal.Quotient.mk p.asIdeal)
    rw [fromBlocks_map] at h'
    refine exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot (fun x h₁ h₂ => ?_)
      (SymplecticGroup.fromBlocks_mem_iff.1 h').1
    have hu := (isUnit_iff_isUnit_det _).2 (SymplecticGroup.symplectic_det h')
    have := mulVec_injective_iff_isUnit.2 hu (a₁ := Sum.elim x 0) (a₂ := Sum.elim 0 0) (by
      rw [smul_eq_mulVec] at h₁ h₂
      simp [fromBlocks_mulVec, h₁, h₂])
    exact (Sum.elim_eq_iff.1 this).1
  choose Y hY hu using key
  obtain ⟨s, hs⟩ := exists_lift_maximalSpectrum_pi (R := R)
  refine ⟨Matrix.of fun i j => s fun p => Y p i j, ?_,
    isUnit_of_forall_maximalSpectrum_mk_ne_zero fun p => ?_⟩
  · ext i j
    simp only [transpose_apply, of_apply]
    exact congrArg s (funext fun p => (hY p).apply i j)
  · have := p.isMaximal
    have hX : (Matrix.of fun i j => s fun p => Y p i j).map (Ideal.Quotient.mk p.asIdeal) = Y p :=
      Matrix.ext fun i j => by simp [hs]
    rw [RingHom.map_det, map_add, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      RingHom.mapMatrix_apply, hX]
    exact ((isUnit_iff_isUnit_det _).1 (hu p)).ne_zero
end GlobalTheory
