-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.IsIso.N_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:10:36.539804+00:00
-- url     : https://prove2.me/submissions/b5bceba3-811a-4239-a463-f8ab97a71757

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_orbSum_equiv
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_IsIso_herm_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
open GlobalTheory.UnitLemma.Orbit.IsIso
variable {B C : InvAlg K} {φ : B.A ≃ₐ[K.E] C.A}
namespace GlobalTheory.UnitLemma.Orbit.IsIso
theorem _root_.solution (h : IsIso φ) (x : B.A) : C.N (φ x) = B.N x := by
  have hm : ∀ (L : Submodule K.O B.A) (y : B.A),
      φ y ∈ L.map (φ.restrictScalars K.O).toLinearEquiv.toLinearMap ↔ y ∈ L := by
    intro L y
    rw [Submodule.mem_map_equiv]
    simp
  refine orbSum_equiv (φ.restrictScalars K.O) _ _ (fun t => ?_) _ _ (fun L => ?_)
  · change (t : B.A) * B.σ t = 1 ↔ φ t * C.σ (φ t) = 1
    rw [← h.1, ← map_mul, map_eq_one_iff _ φ.injective]
  · refine and_congr (and_congr ?_ ?_) (and_congr ?_ ?_)
    · exact (Submodule.fg_map_iff _ φ.injective).symm
    · rw [Submodule.map_coe]
      change _ ↔ Submodule.span K.E (φ.toLinearEquiv.toLinearMap '' (L : Set B.A)) = ⊤
      rw [← Submodule.map_span, Submodule.map_eq_top_iff]
    · rw [φ.surjective.forall]
      simp only [← h.2, ← map_mul, hm]
    · rw [φ.surjective.forall]
      refine forall_congr' fun y => ?_
      rw [φ.surjective.forall]
      simp only [hm, h.herm_eq]
end GlobalTheory.UnitLemma.Orbit.IsIso
