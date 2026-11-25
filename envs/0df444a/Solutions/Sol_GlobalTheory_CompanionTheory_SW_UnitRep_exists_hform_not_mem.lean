-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.UnitRep.exists_hform_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:38:04.499729+00:00
-- url     : https://prove2.me/submissions/8fc60838-7d7e-42e9-af7c-e84e405aa6e7

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormRepresentsUnit
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitRep_hform_add_left
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitRep_hform_add_right
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_UnitRep_hform_smul_left__f3e0ebeac993
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_UnitRep_hform_smul_right__dc8b27524d6b
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitRep_hform_single_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix HeckeCharacterZeroLocus.SiegelWeilU
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.UnitRep
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CompanionTheory.SW.UnitRep
theorem _root_.solution (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A))
    (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ) (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A)
    (hdet : IsUnit J.det) (P : Ideal A) (hP : P.IsMaximal) :
    ∃ y, hform σ J y y ∉ P := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨δ, hδu, hδσ⟩ := hδ
  have hpol : ∀ x y, hform σ J x y + hform σ J y x ∈ P := fun x y => by
    have h := hcon (x + y)
    rw [hform_add_left, hform_add_right, hform_add_right] at h
    have h' := P.sub_mem (P.sub_mem h (hcon x)) (hcon y)
    convert h' using 1
    ring
  have hpol' : ∀ x y, δ * (hform σ J x y - hform σ J y x) ∈ P := fun x y => by
    have h := hpol x (δ • y)
    rw [hform_smul_right', hform_smul_left', hδσ] at h
    convert h using 1
    ring
  have hall : ∀ x y, hform σ J x y ∈ P := fun x y => by
    have h₁ : hform σ J x y - hform σ J y x ∈ P :=
      (Ideal.unit_mul_mem_iff_mem P hδu).1 (hpol' x y)
    have h₂ : 2 * hform σ J x y ∈ P := by
      convert P.add_mem (hpol x y) h₁ using 1
      ring
    exact (Ideal.unit_mul_mem_iff_mem P h2).1 h₂
  have hJ0 : (Ideal.Quotient.mk P).mapMatrix J = 0 := by
    ext i j
    have h := hall (Pi.single i 1) (Pi.single j 1)
    rw [hform_single_single] at h
    simpa using Ideal.Quotient.eq_zero_iff_mem.2 h
  have hd : J.det ∈ P := by
    refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [RingHom.map_det, hJ0, Matrix.det_zero]
  exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P hd hdet)
end GlobalTheory.CompanionTheory.SW.UnitRep
