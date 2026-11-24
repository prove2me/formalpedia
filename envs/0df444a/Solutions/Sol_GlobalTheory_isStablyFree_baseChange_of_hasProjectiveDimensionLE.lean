-- Prove2me | solution 1 for GlobalTheory.isStablyFree_baseChange_of_hasProjectiveDimensionLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:31:27.233793+00:00
-- url     : https://prove2.me/submissions/7ab5f9ca-c74f-47d0-8b4a-146bdcbf14b1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsPrincipalMapAwayOfHasProjectiveDimensionLE
import Theorems.Thm_GlobalTheory_nonempty_equiv_prod_of_exact_of_projective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open scoped TensorProduct
namespace GlobalTheory
theorem _root_.solution (R : Type) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A] [Module.Flat R A]
    (n : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M],
      HasProjectiveDimensionLE (ModuleCat.of R M) n → Module.Projective A (A ⊗[R] M) →
        Module.IsStablyFree A (A ⊗[R] M) := by
  induction n with
  | zero =>
    intro M _ _ _ h _
    have h1 : Projective (ModuleCat.of R M) :=
      (projective_iff_hasProjectiveDimensionLE_zero _).2 h
    have h2 : Module.Projective R M := (IsProjective.iff_projective M).2 h1
    have h3 : Module.Free R M := Module.free_of_flat_of_isLocalRing
    infer_instance
  | succ n ih =>
    intro M _ _ _ h hp
    obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' R M
    have hS := LinearMap.shortExact_shortComplexKer hf
    have hK : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n := by
      have hP : Projective (ModuleCat.of R (Fin m → R)) := inferInstance
      exact (hS.hasProjectiveDimensionLT_X₃_iff n hP).1 h
    have hex : Function.Exact ((LinearMap.ker f).subtype.baseChange A) (f.baseChange A) :=
      lTensor_exact A f.exact_subtype_ker_map hf
    have hinj : Function.Injective ((LinearMap.ker f).subtype.baseChange A) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (LinearMap.ker f).injective_subtype
    have hsurj : Function.Surjective (f.baseChange A) := LinearMap.lTensor_surjective A hf
    obtain ⟨e⟩ := nonempty_equiv_prod_of_exact_of_projective _ _ hinj hsurj hex
    have hfree : Module.Free A ((A ⊗[R] LinearMap.ker f) × (A ⊗[R] M)) := Module.Free.of_equiv e
    have hKp : Module.Projective A (A ⊗[R] LinearMap.ker f) :=
      Module.Projective.of_split (LinearMap.inl A _ (A ⊗[R] M)) (LinearMap.fst A _ _)
        (LinearMap.ext fun _ ↦ rfl)
    have hKs := ih (LinearMap.ker f) hK hKp
    obtain ⟨N, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod A (A ⊗[R] LinearMap.ker f)
    have : Module.Free A ((A ⊗[R] M) × ((A ⊗[R] LinearMap.ker f) × N)) :=
      Module.Free.of_equiv (M := ((A ⊗[R] LinearMap.ker f) × (A ⊗[R] M)) × N)
        (((LinearEquiv.prodComm A _ _).prodCongr (LinearEquiv.refl A N)).trans
          (LinearEquiv.prodAssoc A _ _ _))
    exact Module.IsStablyFree.of_free_prod A _ ((A ⊗[R] LinearMap.ker f) × N)
end GlobalTheory
