-- Prove2me | solution 1 for GlobalTheory.ExtDescent.isPullback_of_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:49:21.161522+00:00
-- url     : https://prove2.me/submissions/5a6b2d19-92f0-4bb1-983b-f04240f4e0a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusExtensionDescends
import Theorems.Thm_GlobalTheory_ExtDescent_fpqc_of_isPullback

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
open GlobalTheory GlobalTheory.ExtDescent
variable {S S₀ : Scheme.{0}} {f : S ⟶ S₀}
namespace GlobalTheory.ExtDescent
theorem _root_.solution [Flat f] [Surjective f] [QuasiCompact f] {T G B T₀ G₀ B₀ : Scheme.{0}}
    {i : T ⟶ G} {t : T ⟶ S} {q : G ⟶ B} {e : S ⟶ B} (H : IsPullback i t q e)
    {i₀ : T₀ ⟶ G₀} {t₀ : T₀ ⟶ S₀} {q₀ : G₀ ⟶ B₀} {e₀ : S₀ ⟶ B₀}
    {τ : T ⟶ T₀} {g : G ⟶ G₀} {φ : B ⟶ B₀} (hτ : IsPullback τ t t₀ f) (hγ : IsPullback g q q₀ φ)
    (hi : τ ≫ i₀ = i ≫ g) (he : f ≫ e₀ = e ≫ φ) : IsPullback i₀ t₀ q₀ e₀ := by
  haveI : Flat τ := (fpqc_of_isPullback hτ).1.2
  haveI : Surjective τ := (fpqc_of_isPullback hτ).1.1
  haveI := Flat.epi_of_flat_of_surjective τ
  have w : i₀ ≫ q₀ = t₀ ≫ e₀ := by
    rw [← cancel_epi τ, reassoc_of% hi, hγ.w, reassoc_of% H.w, reassoc_of% hτ.w, he]
  let c : T₀ ⟶ pullback q₀ e₀ := pullback.lift i₀ t₀ w
  have c₁ : c ≫ pullback.fst q₀ e₀ = i₀ := pullback.lift_fst _ _ _
  have c₂ : c ≫ pullback.snd q₀ e₀ = t₀ := pullback.lift_snd _ _ _
  have hp : IsPullback (τ ≫ c) t (pullback.snd q₀ e₀) f := by
    refine IsPullback.of_right ?_ (by rw [Category.assoc, c₂, hτ.w]) (IsPullback.of_hasPullback q₀ e₀)
    rw [Category.assoc, c₁, hi, he]
    exact H.paste_horiz hγ
  have hc : IsPullback τ (𝟙 T) c (τ ≫ c) := by
    refine IsPullback.of_bot ?_ (by simp) hp
    rw [c₂, Category.id_comp]
    exact hτ
  haveI : IsIso c := MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{0})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hc.flip
    (fpqc_of_isPullback hp) (inferInstanceAs (IsIso (𝟙 T)))
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) c₁ c₂
end GlobalTheory.ExtDescent
