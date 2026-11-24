-- Prove2me | solution 1 for GlobalTheory.TangentCriterion.formallyUnramified_of_tangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:26:58.052702+00:00
-- url     : https://prove2.me/submissions/837e10ef-b6ba-4c73-9bc1-c93173707fdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UnramifiedQuasiFiniteOfTangent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.TangentCriterion
namespace GlobalTheory.TangentCriterion
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B]
    (h : ∀ (K : Type) [Field K] (g : B →+* DualNumber K),
      g.comp (algebraMap A B) = (((algebraMap K (DualNumber K)).comp
        (TrivSqZeroExt.fstHom K K K).toRingHom).comp g).comp (algebraMap A B) →
      g = ((algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K K).toRingHom).comp g) :
    Algebra.FormallyUnramified A B := by
  refine ⟨?_⟩
  by_contra hn
  rw [not_subsingleton_iff_nontrivial] at hn
  obtain ⟨N, hN, -⟩ : ∃ N : Submodule B Ω[B⁄A], IsCoatom N ∧ ⊥ ≤ N :=
    (eq_top_or_exists_le_coatom (⊥ : Submodule B Ω[B⁄A])).resolve_left bot_ne_top
  have hs : IsSimpleModule B (Ω[B⁄A] ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
  letI := Ideal.Quotient.field m
  let φ : Ω[B⁄A] →ₗ[B] (B ⧸ m) := e.toLinearMap ∘ₗ N.mkQ
  let D : Derivation A B (B ⧸ m) := φ.compDer (KaehlerDifferential.D A B)
  have hD := h (B ⧸ m) (dualOfDerivation D) (by
    ext a <;> simp [dualOfDerivation, TrivSqZeroExt.algebraMap_eq_inl])
  have h0 : ∀ b, φ (KaehlerDifferential.D A B b) = 0 := fun b => by
    have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hD b)
    simpa [dualOfDerivation, TrivSqZeroExt.algebraMap_eq_inl, D] using this
  have hφ : φ = 0 := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation A B)
    rintro _ ⟨b, rfl⟩
    exact h0 b
  have hsurj : Function.Surjective φ := e.surjective.comp N.mkQ_surjective
  obtain ⟨w, hw⟩ := hsurj 1
  rw [hφ] at hw
  exact zero_ne_one hw
end GlobalTheory.TangentCriterion
