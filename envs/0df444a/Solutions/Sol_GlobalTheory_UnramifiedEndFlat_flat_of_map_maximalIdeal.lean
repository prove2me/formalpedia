-- Prove2me | solution 1 for GlobalTheory.UnramifiedEndFlat.flat_of_map_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:58:37.314691+00:00
-- url     : https://prove2.me/submissions/bdf104ac-b06d-4ca4-a268-37678644301f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Theorems.Thm_GlobalTheory_UnramifiedEndFlat_flat_of_map_maximalIdeal_self
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.UnramifiedEndFlat
open IsLocalRing
namespace GlobalTheory.UnramifiedEndFlat
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [IsNoetherianRing A] (e : B ≃+* A)
    (φ : A →+* B) (hm : (maximalIdeal A).map φ = maximalIdeal B)
    (h₀ : ∀ b, ∃ a, φ a - b ∈ maximalIdeal B) : φ.Flat := by
  have he : (maximalIdeal B).map (e : B →+* A) = maximalIdeal A :=
    map_maximalIdeal_of_surjective _ e.surjective
  have h : ((e : B →+* A).comp φ).Flat := by
    refine flat_of_map_maximalIdeal_self _ (by rw [← Ideal.map_map, hm, he]) fun b => ?_
    obtain ⟨a, ha⟩ := h₀ (e.symm b)
    refine ⟨a, ?_⟩
    have := Ideal.mem_map_of_mem (e : B →+* A) ha
    rw [he] at this
    simpa using this
  have := h.comp (RingHom.Flat.of_bijective (f := (e.symm : A →+* B)) e.symm.bijective)
  convert this
  ext x
  simp
end GlobalTheory.UnramifiedEndFlat
