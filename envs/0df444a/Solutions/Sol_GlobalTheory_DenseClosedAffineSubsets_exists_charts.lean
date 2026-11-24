-- Prove2me | solution 1 for GlobalTheory.DenseClosedAffineSubsets.exists_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:51:21.169793+00:00
-- url     : https://prove2.me/submissions/59ca7fcc-1bf6-4f8d-bfd9-32993e97fa38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint
import Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_basicOpen_sec
import Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_sec_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.DenseClosedAffineSubsets
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.DenseClosedAffineSubsets
theorem _root_.solution (R : Type) [CommRing R] (N : ℕ) :
    ∃ (D : Fin (N + 1) → (PSpace R N).Opens) (r : ∀ _ K, Γ((D K).toScheme, ⊤)),
      ⨆ K, D K = ⊤ ∧ (∀ J K, (D K).toScheme.basicOpen (r J K) ≤ (D K).ι ⁻¹ᵁ D J) ∧
      ∀ (U : Scheme.{0}) (u : U ⟶ Sp R) (m : Fin (N + 1) → Γ(U, ⊤)) (K₀ : Fin (N + 1)),
        IsUnit (m K₀) → ∃ φ : U ⟶ PSpace R N, φ ≫ PSpace.str R N = u ∧
          ∀ (K : Fin (N + 1)) (V : Scheme.{0}) (a : V ⟶ U) (b : V ⟶ D K), a ≫ φ = b ≫ (D K).ι →
            IsUnit (a.appTop (m K)) ∧
              ∀ J, b.appTop (r J K) * a.appTop (m K) = a.appTop (m J) := by
  have hX (K : Fin (N + 1)) : (MvPolynomial.X K : MvPolynomial (Fin (N + 1)) R) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 1 := MvPolynomial.isHomogeneous_X R K
  refine ⟨fun K ↦ Proj.basicOpen _ (MvPolynomial.X K),
    fun J K ↦ sec _ _ (HomogeneousLocalization.Away.isLocalizationElem (hX K) (hX J)),
    Proj.iSup_basicOpen_eq_top' _ _ (fun K ↦ ⟨1, hX K⟩) (adjoin_X R N),
    fun J K ↦ (basicOpen_sec _ (hX K) (hX J)).le, ?_⟩
  intro U u m K₀ hm
  let F : MvPolynomial (Fin (N + 1)) R →+* Γ(U, ⊤) :=
    MvPolynomial.eval₂Hom ((Scheme.ΓSpecIso (.of R)).inv ≫ u.appTop).hom m
  have hF (K) : F (MvPolynomial.X K) = m K := MvPolynomial.eval₂Hom_X' _ _ _
  have hirr : (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).toIdeal.map F = ⊤ := by
    refine Ideal.eq_top_of_isUnit_mem _ ?_ hm
    rw [← hF]
    refine Ideal.mem_map_of_mem _ ?_
    refine (HomogeneousIdeal.mem_irrelevant_iff _ _).mpr ?_
    rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne _ (hX K₀) one_ne_zero]
  refine ⟨Proj.fromOfGlobalSections _ F hirr, ?_, ?_⟩
  · rw [PSpace.str, Proj.fromOfGlobalSections_toSpecZero_assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    have : (F.comp (algebraMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) _)).comp
        (algebraMap R _) = ((Scheme.ΓSpecIso (.of R)).inv ≫ u.appTop).hom := by
      ext x
      exact MvPolynomial.eval₂Hom_C _ _ x
    rw [this, CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
    simp
  · intro K V a b hab
    have hpre := Proj.fromOfGlobalSections_preimage_basicOpen _ F hirr one_pos (hX K)
    have hr : Set.range a ⊆ Set.range (U.basicOpen (F (MvPolynomial.X K))).ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι, ← hpre]
      change Proj.fromOfGlobalSections _ F hirr (a z) ∈ Proj.basicOpen _ (MvPolynomial.X K)
      rw [← Scheme.Hom.comp_apply, hab, Scheme.Hom.comp_apply]
      exact (b z).2
    obtain ⟨a', rfl⟩ : ∃ a' : V ⟶ (U.basicOpen (F (MvPolynomial.X K))).toScheme,
        a' ≫ (U.basicOpen (F (MvPolynomial.X K))).ι = a :=
      ⟨_, IsOpenImmersion.lift_fac _ a hr⟩
    obtain rfl : b = a' ≫ Proj.toBasicOpenOfGlobalSections _ F rfl one_pos (hX K) := by
      rw [← cancel_mono (Scheme.Opens.ι _), ← hab,
        ← Proj.fromOfGlobalSections_resLE _ F hirr one_pos (hX K), Category.assoc, Category.assoc,
        Scheme.Hom.resLE_comp_ι]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← hF]
    refine ⟨IsUnit.map _ ?_, fun J ↦ ?_⟩
    · apply RingedSpace.isUnit_of_isUnit_germ
      intro x hx
      rw [← Scheme.mem_basicOpen, ← Scheme.preimage_basicOpen_top]
      exact x.2
    · rw [← map_mul, sec_mul _ (hX K) (hX J)]
end GlobalTheory.DenseClosedAffineSubsets
