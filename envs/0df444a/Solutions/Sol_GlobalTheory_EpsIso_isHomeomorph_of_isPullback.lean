-- Prove2me | solution 1 for GlobalTheory.EpsIso.isHomeomorph_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:08:54.922362+00:00
-- url     : https://prove2.me/submissions/a1059d29-572f-49d6-ac40-2e2b69c3bae1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoOfIdModEpsThickening
import Theorems.Thm_GlobalTheory_EpsIso_ker_fst_eq_span
import Theorems.Thm_GlobalTheory_EpsIso_fst_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.EpsIso
namespace GlobalTheory.EpsIso
theorem _root_.solution {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K}
    {π : Y' ⟶ Sp (DualNumber K)} {j : Y ⟶ Y'}
    (h : IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)) :
    IsClosedImmersion j ∧ IsHomeomorph j := by
  have hsp : spMap (TrivSqZeroExt.fstHom K K K).toRingHom =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) := rfl
  have hsurj := fst_surjective K
  have hci : IsClosedImmersion (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    rw [hsp]
    exact IsClosedImmersion.spec_of_surjective _ hsurj
  have hsu : Surjective (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    have hr : Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom K K K).toRingHom) = Set.univ := by
      rw [range_comap_of_surjective (f := (TrivSqZeroExt.fstHom K K K).toRingHom)
        (hf := hsurj), PrimeSpectrum.zeroLocus_eq_univ_iff]
      intro x hx
      rw [SetLike.mem_coe, ker_fst_eq_span, Ideal.mem_span_singleton] at hx
      obtain ⟨y, rfl⟩ := hx
      show _ ∈ nilradical _
      rw [mem_nilradical]
      exact ⟨2, by rw [pow_two, _root_.mul_mul_mul_comm, DualNumber.eps_mul_eps, zero_mul]⟩
    rw [hsp]
    exact ⟨fun p => Set.range_eq_univ.1 hr p⟩
  have hcj : IsClosedImmersion j := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hci
  have hsj : Surjective j := MorphismProperty.of_isPullback (P := @Surjective) h.flip hsu
  refine ⟨hcj, ?_⟩
  rw [isHomeomorph_iff_isEmbedding_surjective]
  exact ⟨j.isClosedEmbedding.isEmbedding, hsj.surj⟩
end GlobalTheory.EpsIso
