-- Prove2me | solution 1 for GlobalTheory.SplitFinitePart.exists_section_of_isIntegralHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:49.624013+00:00
-- url     : https://prove2.me/submissions/2c90d623-21a2-415d-920a-58e588bf300c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSectionOfIsIntegralHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SplitFinitePart
namespace GlobalTheory.SplitFinitePart
theorem _root_.solution {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] {N : Scheme.{0}} (g : N ⟶ Sp R) [IsIntegralHom g] (γ : Sp K ⟶ N)
    (hγ : γ ≫ g = spMap (algebraMap R K)) : ∃ s : Sp R ⟶ N, s ≫ g = 𝟙 _ ∧ spMap (algebraMap R K) ≫ s = γ := by
  have : IsAffine N := isAffine_of_isAffineHom g
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (N.isoSpec.inv ≫ g)
  obtain ⟨c, hc⟩ := Spec.map_surjective (γ ≫ N.isoSpec.hom)
  have h1 : IsIntegralHom (Spec.map ψ) := by rw [hψ]; infer_instance
  have hint : ψ.hom.IsIntegral := IsIntegralHom.SpecMap_iff.mp h1
  have h2 : ψ ≫ c = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hc, hψ, Category.assoc, Iso.hom_inv_id_assoc, hγ]
  have h3 : c.hom.comp ψ.hom = algebraMap R K := congrArg CommRingCat.Hom.hom h2
  have h4 : ∀ b, ∃ a : R, algebraMap R K a = c.hom b := fun b => by
    refine IsIntegrallyClosed.isIntegral_iff.mp ?_
    have := (hint b).map c.hom
    rwa [h3] at this
  choose σ hσ using h4
  have hi := IsFractionRing.injective R K
  let σ' : Γ(N, ⊤) →+* R :=
    { toFun := σ
      map_one' := hi (by simp [hσ])
      map_mul' := fun a b => hi (by simp [hσ])
      map_zero' := hi (by simp [hσ])
      map_add' := fun a b => hi (by simp [hσ]) }
  refine ⟨spMap σ' ≫ N.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact hi ((hσ _).trans (congrArg (fun φ : R →+* K => φ a) h3))
  · rw [← Category.assoc, Iso.comp_inv_eq, ← hc, ← Spec.map_comp]
    congr 1
    ext a
    exact hσ a
end GlobalTheory.SplitFinitePart
