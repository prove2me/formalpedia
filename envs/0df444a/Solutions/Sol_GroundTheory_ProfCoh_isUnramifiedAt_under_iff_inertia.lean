-- Prove2me | solution 1 for GroundTheory.ProfCoh.isUnramifiedAt_under_iff_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:15.403485+00:00
-- url     : https://prove2.me/submissions/39658e1d-48d8-4c8e-b026-305fbf51bbe9

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
import Theorems.Thm_GroundTheory_ProfCoh_restrictScalars_mem_inertia_iff
import Theorems.Thm_GroundTheory_ProfCoh_mem_range_restrictScalarsHom_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
variable {F E M : Type*} [Field F] [Field E] [Field M] [Algebra F E] [Algebra E M] [Algebra F M]
  [IsScalarTower F E M]
variable [NumberField F] [NumberField E] [NumberField M] [IsGalois F M]
namespace GroundTheory.ProfCoh
theorem _root_.solution (Q : Ideal (𝓞 M)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 F) (Q.under (𝓞 E)) ↔
      ∀ σ ∈ Q.inertia Gal(M/F), ∀ x : E, σ (algebraMap E M x) = algebraMap E M x := by
  have : IsGaloisGroup Gal(M/F) (𝓞 F) (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ F M
  have : IsGalois E M := IsGalois.tower_top_of_isGalois F E M
  have : IsGaloisGroup Gal(M/E) (𝓞 E) (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ E M
  have cF : Nat.card (Q.inertia Gal(M/F)) = Q.ramificationIdx (𝓞 F) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (Q.under (𝓞 F)) Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 F)) Q Gal(M/F)]
  have cE : Nat.card (Q.inertia Gal(M/E)) = Q.ramificationIdx (𝓞 E) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (Q.under (𝓞 E)) Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 E)) Q Gal(M/E)]
  have htow : Q.ramificationIdx (𝓞 F) =
      (Q.under (𝓞 E)).ramificationIdx (𝓞 F) * Q.ramificationIdx (𝓞 E) :=
    Ideal.ramificationIdx_tower (q := Q.under (𝓞 E)) (r := Q)
  set φ : Gal(M/E) →* Gal(M/F) := AlgEquiv.restrictScalarsHom F with hφ
  have hinj : Function.Injective φ := AlgEquiv.restrictScalarsHom_injective F
  have hmap : (Q.inertia Gal(M/E)).map φ = Q.inertia Gal(M/F) ⊓ φ.range := by
    ext σ
    simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range]
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨(restrictScalars_mem_inertia_iff Q τ).2 hτ, τ, rfl⟩
    · rintro ⟨hσ, τ, rfl⟩
      exact ⟨τ, (restrictScalars_mem_inertia_iff Q τ).1 hσ, rfl⟩
  have hcardmap : Nat.card ((Q.inertia Gal(M/E)).map φ) = Nat.card (Q.inertia Gal(M/E)) :=
    Subgroup.card_map_of_injective hinj
  have hpos : 0 < Nat.card (Q.inertia Gal(M/E)) := Nat.card_pos
  rw [← Ideal.ramificationIdx_eq_one_iff]
  constructor
  · intro h1 σ hσ
    have hc : Nat.card (Q.inertia Gal(M/F) ⊓ φ.range : Subgroup Gal(M/F)) ≥
        Nat.card (Q.inertia Gal(M/F)) := by
      rw [← hmap, hcardmap, cF, cE, htow, h1, one_mul]
    have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : Q.inertia Gal(M/F) ⊓ φ.range ≤ _) hc
    have hσ' : σ ∈ Q.inertia Gal(M/F) ⊓ φ.range := by rw [heq]; exact hσ
    exact (mem_range_restrictScalarsHom_iff σ).1 hσ'.2
  · intro h
    have hle : Q.inertia Gal(M/F) ≤ φ.range := fun σ hσ =>
      (mem_range_restrictScalarsHom_iff σ).2 (h σ hσ)
    have hmap' : (Q.inertia Gal(M/E)).map φ = Q.inertia Gal(M/F) := by
      rw [hmap, inf_eq_left.2 hle]
    have hc : (Q.under (𝓞 E)).ramificationIdx (𝓞 F) * Q.ramificationIdx (𝓞 E) =
        1 * Q.ramificationIdx (𝓞 E) := by
      rw [← htow, ← cF, ← cE, ← hmap', hcardmap, one_mul]
    exact Nat.eq_of_mul_eq_mul_right (cE ▸ hpos) hc
end GroundTheory.ProfCoh
