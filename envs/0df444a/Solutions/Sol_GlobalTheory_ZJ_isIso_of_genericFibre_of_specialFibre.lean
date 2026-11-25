-- Prove2me | solution 1 for GlobalTheory.ZJ.isIso_of_genericFibre_of_specialFibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:37.746087+00:00
-- url     : https://prove2.me/submissions/1ec97888-7828-4659-83bf-6a819913ad3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TestCartOfSpecialFibreSurjective
import Theorems.Thm_GlobalTheory_ZJ_eq_of_injective_baseChange
import Theorems.Thm_GlobalTheory_ZJ_mem_range_of_surjective_baseChange
import Theorems.Thm_GlobalTheory_ZJ_eq_closedPoint_or_mem_range
import Theorems.Thm_GlobalTheory_isIntegral_and_isNormalScheme_of_smooth
import Theorems.Thm_GlobalTheory_isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict
import Theorems.Thm_GlobalTheory_isOpenImmersion_spMap_of_isDiscreteValuationRing


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
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ
namespace GlobalTheory.ZJ
theorem _root_.solution (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K]
    {H X S' H' X' : Scheme.{0}} (h : H ⟶ X) (s : X ⟶ Sp T) (u : H ⟶ Sp T) (hu : h ≫ s = u)
    [Smooth s] [IsSeparated s] [Smooth u] [IsSeparated u] [QuasiCompact u]
    [ConnectedSpace ↥(pullback u (spMap (algebraMap T K)))]
    (hK : IsPullback (pullback.fst u (spMap (algebraMap T K)) ≫ h) (pullback.snd u (spMap (algebraMap T K)))
      s (spMap (algebraMap T K)))
    {q : S' ⟶ Sp T} (hq : IsLocalRing.closedPoint T ∈ Set.range q)
    {b : X' ⟶ X} {s' : X' ⟶ S'} {a : H' ⟶ H} {h' : H' ⟶ X'}
    (hX : IsPullback b s' s q) (hH : IsPullback a (h' ≫ s') u q) (w : a ≫ h = h' ≫ b)
    (hbij : Function.Bijective h') : IsIso h := by
  subst hu
  let t := spMap (algebraMap T K)
  have : IsOpenImmersion t := isOpenImmersion_spMap_of_isDiscreteValuationRing T K
  have : ConnectedSpace ↥(pullback s t) :=
    hK.isoPullback.hom.surjective.connectedSpace hK.isoPullback.hom.continuous
  obtain ⟨hXi, hN⟩ := isIntegral_and_isNormalScheme_of_smooth T K s
  obtain ⟨hHi, -⟩ := isIntegral_and_isNormalScheme_of_smooth T K (h ≫ s)
  have : IsSeparated h := IsSeparated.of_comp h s
  have : QuasiCompact h := QuasiCompact.of_comp h s
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h s
  let j := pullback.fst (h ≫ s) t
  have hj : IsPullback j (𝟙 _ ≫ pullback.snd (h ≫ s) t) (h ≫ s) t := by
    rw [Category.id_comp]; exact .of_hasPullback _ _
  have hinj : Function.Injective h := fun x y hxy ↦ by
    rcases eq_closedPoint_or_mem_range T K (s (h x)) with hx | hx
    · exact eq_of_injective_baseChange hX hH w hbij.1 hxy (hx ▸ hq)
    · exact eq_of_injective_baseChange hK hj (Category.id_comp _).symm
        (fun _ _ e ↦ e) hxy hx
  have hsurj : Function.Surjective h := fun z ↦ by
    rcases eq_closedPoint_or_mem_range T K (s z) with hx | hx
    · exact mem_range_of_surjective_baseChange hX w hbij.2 (hx ▸ hq)
    · exact mem_range_of_surjective_baseChange (h' := 𝟙 _) hK (Category.id_comp _).symm
        (fun e ↦ ⟨e, rfl⟩) hx
  have : LocallyQuasiFinite h := LocallyQuasiFinite.of_injective hinj
  have : IsOpenImmersion (j ≫ h) := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hK.flip ‹_›
  have : IsOpenImmersion (j.opensRange.ι ≫ h) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc]
    infer_instance
  have : IsOpenImmersion h :=
    isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict h (fun y ↦ (hN y).2)
      j.opensRange ⟨⟨j (Classical.arbitrary _), _, rfl⟩⟩
  exact (isIso_iff_isOpenImmersion_and_surjective h).mpr ⟨this, ⟨hsurj⟩⟩
end GlobalTheory.ZJ
