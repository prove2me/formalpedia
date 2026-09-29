-- Prove2me | solution 1 for ModularCurve.heckeBetaModLHDefined
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/dce00987-740a-5b49-a9ac-37860df0d251

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_qExpand_image_intFormRatiosC_subset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeBetaModLHDefined

set_option autoImplicit false

namespace BetaModLH

open ModularCurve CongruenceSubgroup IntermediateField

open scoped MatrixGroups

variable (N : ℕ) (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ)

scoped instance finiteIndex_GammaH [NeZero N] : (CohCarrier.GammaH N H').FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH N H')

theorem mem_GammaH_of_entries_eq {A B : SL(2, ℤ)} (hB : B ∈ CohCarrier.GammaH N H')
    (h10 : ((A 1 0 : ℤ) : ZMod N) = B 1 0)
    (h11 : ((A 1 1 : ℤ) : ZMod N) = B 1 1) : A ∈ CohCarrier.GammaH N H' := by
  obtain ⟨hB0, hBH⟩ := CohCarrier.mem_GammaH_iff.mp hB
  have hA0 : A ∈ Gamma0 N := by
    rw [Gamma0_mem] at hB0 ⊢
    rw [h10]; exact hB0
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have heq : CohCarrier.gamma0Units N ⟨A, hA0⟩ = CohCarrier.gamma0Units N ⟨B, hB0⟩ := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod N) = ((B 1 1 : ℤ) : ZMod N)
    exact h11
  rw [heq]; exact hBH

theorem cocycleH [NeZero ℓ] : ∀ γ ∈ CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ), ∃ γ₁ ∈ CohCarrier.GammaH N H',
    γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  obtain ⟨hγH, hγ0⟩ := Subgroup.mem_inf.mp hγ
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hMℓc : ((N * ℓ : ℕ) : ℤ) ∣ γ 1 0 := by
    have := Gamma0_mem.mp hγ0; rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨c', hc'⟩ := hMℓc
  rw [Nat.cast_mul] at hc'
  have hdet' : Matrix.det !![(γ 0 0 : ℤ), (ℓ : ℤ) * γ 0 1; (N : ℤ) * c', γ 1 1] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + (γ 0 1 : ℤ) * hc'
  refine ⟨⟨_, hdet'⟩, ?_, rfl, rfl, ?_, rfl⟩
  · refine mem_GammaH_of_entries_eq N H' hγH ?_ rfl
    show (((N : ℤ) * c' : ℤ) : ZMod N) = ((γ 1 0 : ℤ) : ZMod N)
    have h0 : ((γ 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp (CohCarrier.GammaH_le_Gamma0 H' hγH)
    rw [h0]; push_cast; rw [ZMod.natCast_self, zero_mul]
  · show (ℓ : ℤ) * ((N : ℤ) * c') = γ 1 0
    linear_combination -hc'

theorem qExpand_mem (K : Type*) [Field K] [NeZero N] [NeZero ℓ]
    (y : LaurentSeries K) (hy : y ∈ qExpFunctionFieldC K (CohCarrier.GammaH N H')) :
    qExpand K ℓ y ∈ qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ)) := by
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset K
    (Γ := CohCarrier.GammaH N H') (translation_mem_GammaH N H') ℓ (cocycleH N H' ℓ)

  let φ : LaurentSeries K →ₐ[K] LaurentSeries K :=
    { qExpand K ℓ with
      commutes' := fun a => by
        show qExpand K ℓ (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) a
        rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }
  have hφ : ∀ z, φ z = qExpand K ℓ z := fun _ => rfl
  have hy' : y ∈ IntermediateField.adjoin K (intFormRatiosC K (CohCarrier.GammaH N H')) := hy
  have hmap : (IntermediateField.adjoin K (intFormRatiosC K (CohCarrier.GammaH N H'))).map φ
      ≤ IntermediateField.adjoin K (intFormRatiosC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ))) := by
    rw [IntermediateField.adjoin_map]
    refine IntermediateField.adjoin.mono K _ _ ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hsub ⟨z, hz, (hφ z).symm⟩
  exact hmap ⟨y, hy', rfl⟩

end BetaModLH
p2m_reactivate "P2MW.S_ModularCurve_heckeBetaModLHDefined.BetaModLH"

theorem solution (K : Type*) [Field K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [NeZero ℓ] :
    ModularCurve.HeckeBetaModLHDefined K N H' ℓ :=
  fun y hy => BetaModLH.qExpand_mem N H' ℓ K y hy

end S_ModularCurve_heckeBetaModLHDefined
end P2MW
export P2MW.S_ModularCurve_heckeBetaModLHDefined (solution)
