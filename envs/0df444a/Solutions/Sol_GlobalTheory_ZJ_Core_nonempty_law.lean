-- Prove2me | solution 1 for GlobalTheory.ZJ.Core.nonempty_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:41:04.411097+00:00
-- url     : https://prove2.me/submissions/c282679c-1c35-40ea-8b7e-d87c983c818f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NonemptyLawAbelianSchemeProperClosure
import Theorems.Thm_GlobalTheory_ZJ_isGrpPullback_of_dominant
import Theorems.Thm_GlobalTheory_ExtUnique_spec_fractionRing
import Theorems.Thm_GlobalTheory_grpObj_of_dense_open
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ
namespace GlobalTheory.ZJ
namespace Core
theorem _root_.solution : ∀ C : Core, SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart → (∃ m : C.GG ⊗ C.GG ⟶ C.GG, ∀ φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left, IsSquare C.a φ₂ → φ₂ ≫ m.left = (μ[C.A]).left ≫ C.a) → (∃ i : C.GG ⟶ C.GG, C.a ≫ i.left = (ι[C.A]).left ≫ C.a) → Nonempty C.Law := by
  rintro C hsm hcart ⟨m, hm⟩ ⟨i, hi⟩
  have := C.proper
  have hsep : IsSeparated C.GG.hom := by
    change IsSeparated (C.G.ι ≫ C.P.hom)
    infer_instance
  have hsmooth : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have hne : Nonempty C.U.toScheme := C.ne.to_subtype
  have hpb : IsPullback C.a C.A.hom C.GG.hom C.U.ι := by
    have w : C.a ≫ C.GG.hom = C.A.hom ≫ C.U.ι := by
      rw [← C.cart.w, Category.assoc]; rfl
    refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
      (fun s => C.cart.lift (s.fst ≫ C.G.ι) s.snd (by rw [Category.assoc]; exact s.condition))
      (fun s => ?_) (fun s => C.cart.lift_snd _ _ _) (fun s t h₁ h₂ => ?_)⟩⟩
    · rw [← cancel_mono C.G.ι, Category.assoc]
      exact C.cart.lift_fst _ _ _
    · apply C.cart.hom_ext
      · rw [C.cart.lift_fst, ← h₁, Category.assoc]
      · rw [C.cart.lift_snd, h₂]
  let e : 𝟙_ (Over C.Z) ⟶ C.GG := Over.homMk C.e C.e_sec
  obtain ⟨grp, -, hη, -, comm, pull⟩ :=
    grpObj_of_dense_open C.Z C.U.toScheme C.U.ι C.GG C.A C.a hpb m i e hm hi C.e_zero
  refine ⟨{ smooth := hsm, zero := congrArg (fun z => z.left) hη, pull := pull, test := fun p _ y τ => ?_ }⟩
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing τ.V (FractionRing τ.V)
  have := τ.smooth
  have : Smooth τ.H.hom := SmoothOfRelativeDimension.smooth C.g _
  exact isGrpPullback_of_dominant (Out.jK τ.V) (hcart p y τ) ((τ.φ_cart.comp pull).congr τ.yK_fac τ.φ_f)
end Core
end GlobalTheory.ZJ
