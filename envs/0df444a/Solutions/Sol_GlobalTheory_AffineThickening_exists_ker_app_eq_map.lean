-- Prove2me | solution 1 for GlobalTheory.AffineThickening.exists_ker_app_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:05:57.298297+00:00
-- url     : https://prove2.me/submissions/22245faf-686d-48b3-a164-6eb94b7534e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Theorems.Thm_GlobalTheory_PrimeSection_ker_eq_map_of_isPushout


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)
variable {i}
namespace GlobalTheory.AffineThickening
theorem _root_.solution {A C : CommRingCat.{u}} {β : A ⟶ C}
    (hβ : Function.Surjective β) {f : Y ⟶ Spec A} {i : Z ⟶ Y} {f' : Z ⟶ Spec C}
    (h : IsPullback i f' f (Spec.map β)) {U : Y.Opens} (hU : IsAffineOpen U) :
    ∃ α : A →+* Γ(Y, U), RingHom.ker (i.app U).hom = (RingHom.ker β.hom).map α := by
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := i ⁻¹ᵁ U) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top) β (i.app U)
      ((Scheme.ΓSpecIso C).inv ≫ f'.appLE ⊤ (i ⁻¹ᵁ U) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  exact ⟨_, PrimeSection.ker_eq_map_of_isPushout hpo' hβ⟩
end GlobalTheory.AffineThickening
