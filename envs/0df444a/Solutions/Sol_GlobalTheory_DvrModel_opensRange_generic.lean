-- Prove2me | solution 1 for GlobalTheory.DvrModel.opensRange_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:23:16.186238+00:00
-- url     : https://prove2.me/submissions/0a7fa7b8-c76a-4b0d-93e6-02052ff0081e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Theorems.Thm_GlobalTheory_DvrModel_isLocalization_away

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.DvrModel
open PrimeSection
variable {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {K : Type u} [Field K] [Algebra V K] [IsFractionRing V K] {ϖ : V}
  {H : Scheme.{u}} {f : H ⟶ Spec (.of V)}
  {HK : Scheme.{u}} {j : HK ⟶ H} {fK : HK ⟶ Spec (.of K)}
  {Hs : Scheme.{u}} {i : Hs ⟶ H} {fs : Hs ⟶ Spec (.of (ResidueField V))}
local notation "cst[" f ", " R ", " c "]" =>
  ConcreteCategory.hom (Scheme.Hom.appTop f)
    (ConcreteCategory.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of R))) c)
namespace GlobalTheory.DvrModel
theorem _root_.solution (hϖ : Irreducible ϖ) [IsOpenImmersion j]
    (hK : IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K)))) :
    j.opensRange = H.basicOpen cst[f, V, ϖ] := by
  have := isLocalization_away K hϖ
  have hr := PrimeSpectrum.localization_away_comap_range K ϖ
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨y, rfl⟩
    change f (j y) ∈ (PrimeSpectrum.basicOpen ϖ : Set (PrimeSpectrum V))
    rw [← hr, ← Scheme.Hom.comp_apply, hK.w]
    exact ⟨fK y, rfl⟩
  · obtain ⟨z, hz⟩ : f x ∈ Set.range (PrimeSpectrum.comap (algebraMap V K)) := hr.ge hx
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback hK x z hz.symm
    exact ⟨y, hy⟩
end GlobalTheory.DvrModel
