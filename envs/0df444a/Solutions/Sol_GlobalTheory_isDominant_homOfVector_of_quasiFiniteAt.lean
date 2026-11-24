-- Prove2me | solution 1 for GlobalTheory.isDominant_homOfVector_of_quasiFiniteAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:18:35.656268+00:00
-- url     : https://prove2.me/submissions/05684303-5721-48fe-a23c-27d4ce1d4270

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsDominantHomOfVectorOfQuasiFiniteAt
import Theorems.Thm_GlobalTheory_isDominant_of_locallyQuasiFinite_affineSpace

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X Z : Scheme.{0}) [IsIntegral X] [IsIntegral Z] (t : X ⟶ Z) [LocallyOfFiniteType t] (g : ℕ) (U : X.Opens), (U : Set X).Nonempty → SmoothOfRelativeDimension g (U.ι ≫ t) → ∀ (u : Fin g → Γ(X, ⊤)) (w : X), (AffineSpace.homOfVector t u).QuasiFiniteAt w → IsDominant (AffineSpace.homOfVector t u) := by
  intro X Z _ _ t _ g U hU hs u w hw
  have hf := AffineSpace.homOfVector_over t u
  generalize AffineSpace.homOfVector t u = f at hf hw
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ 𝔸(Fin g; Z) ↘ Z) := by rw [hf]; infer_instance
    exact locallyOfFiniteType_of_comp f (𝔸(Fin g; Z) ↘ Z)
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.isOpen f.quasiFiniteLocus.isOpen hU
    ⟨w, hw⟩
  let W : X.Opens := U ⊓ f.quasiFiniteLocus
  have h1 : SmoothOfRelativeDimension (0 + g) (X.homOfLE (inf_le_left : W ≤ U) ≫ U.ι ≫ t) :=
    inferInstance
  have h2 : LocallyQuasiFinite (X.homOfLE (inf_le_right : W ≤ f.quasiFiniteLocus) ≫
    f.quasiFiniteLocus.ι ≫ f) := inferInstance
  rw [Scheme.homOfLE_ι_assoc] at h1 h2
  rw [zero_add] at h1
  obtain ⟨Z', hZ', V, hV, hx, e, hsm⟩ := h1.exists_isStandardSmoothOfRelativeDimension ⟨x, hxU, hxV⟩
  have : Nonempty W := ⟨⟨x, hxU, hxV⟩⟩
  have : Nonempty V := ⟨⟨_, hx⟩⟩
  have : Nonempty Z' := ⟨⟨_, e hx⟩⟩
  have : IsDominant (hV.fromSpec ≫ W.ι ≫ f) :=
    isDominant_of_locallyQuasiFinite_affineSpace _ hsm hZ'.fromSpec _ (by
      rw [IsAffineOpen.SpecMap_appLE_fromSpec _ hZ' hV e]; simp [hf, W])
  have : IsDominant (W.ι ≫ f) := .of_comp hV.fromSpec _
  exact .of_comp W.ι _
end GlobalTheory
