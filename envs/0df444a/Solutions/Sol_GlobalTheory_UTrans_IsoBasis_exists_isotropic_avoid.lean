-- Prove2me | solution 1 for GlobalTheory.UTrans.IsoBasis.exists_isotropic_avoid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:07:25.018518+00:00
-- url     : https://prove2.me/submissions/ded6a9f9-5431-4676-a7c6-dd942fc65182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicBasisNonorthogonalTwoVectors
import Theorems.Thm_GlobalTheory_UTrans_IsoBasis_hf_symm
import Theorems.Thm_GlobalTheory_UTrans_IsoBasis_hfL_ne
import Theorems.Thm_GlobalTheory_UTrans_IsoBasis_hf_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.IsoBasis
variable {E : Type} [Field E] {n : ℕ}
namespace GlobalTheory.UTrans.IsoBasis
theorem _root_.solution [CharZero E] {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}
    (hG : IsHerm σ G) (hz : ∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0)
    {ι : Type} [Finite ι] (f : ι → (Fin n → E) →ₗ[E] E) (hf0 : ∀ i, ∃ x, f i x ≠ 0) :
    ∃ z, hf σ G z z = 0 ∧ ∀ i, f i z ≠ 0 := by
  obtain ⟨w, hw0, hw⟩ := hz
  obtain ⟨c, hc⟩ := hG.ne_id
  set δ := c - σ c with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 hc.symm
  have hδσ : σ δ = -δ := by simp [hδ, hG.invol]
  obtain ⟨u, hu⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun o : Option ι => o.elim (hfL σ G w) f) (by
      rintro (_ | i)
      · exact hfL_ne hG hw0
      · exact hf0 i)
  have huw : hf σ G u w ≠ 0 := hu none
  have hui : ∀ i, f i u ≠ 0 := fun i => hu (some i)
  set a := hf σ G w u with ha
  have hσa : σ a = hf σ G u w := hf_symm hG _ _
  have ha0 : a ≠ 0 := by
    intro h; apply huw; rw [← hσa, h, map_zero]
  have huu : σ (hf σ G u u) = hf σ G u u := hf_symm hG _ _
  let bad : ι → E := fun i => (hf σ G u u / 2 - a * f i u / f i w) / δ
  have hfin : (Set.range bad).Finite := Set.finite_range bad
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : E) ∉ Set.range bad := by
    by_contra h
    push_neg at h
    exact (Set.infinite_of_injective_forall_mem (f := fun t : ℕ => (t : E)) Nat.cast_injective h) hfin
  refine ⟨a • u + (-(hf σ G u u) / 2 + δ * t) • w, ?_, fun i => ?_⟩
  · rw [hf_comb, hw, ← ha, ← hσa]
    simp only [map_add, map_mul, map_div₀, map_neg, huu, hδσ, map_natCast, map_ofNat]
    ring
  · rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    by_cases h : f i w = 0
    · simp [h, ha0, hui i]
    · intro h'
      apply ht
      refine ⟨i, ?_⟩
      simp only [bad]
      field_simp
      linear_combination (-2 : E) * h'
end GlobalTheory.UTrans.IsoBasis
