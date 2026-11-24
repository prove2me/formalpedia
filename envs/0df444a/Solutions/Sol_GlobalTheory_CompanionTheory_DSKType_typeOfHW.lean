-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSKType.typeOfHW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:43:18.017478+00:00
-- url     : https://prove2.me/submissions/c14adad6-e484-49e3-b675-d5b149f2de16

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KsetSubsetUjset
import Theorems.Thm_GlobalTheory_CompanionTheory_DSKType_kset_subset_ujset
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSKType
open CompanionTheory.D.DSIC PI.UpqRep
namespace GlobalTheory.CompanionTheory.DSKType
theorem _root_.solution (hL : LowSpan) (hS : StabLink) (hW : WtLink) : TypeOfHW := by
  intro n ε H _ _ σ S E hσ hM μ x hx0 hfin hhw
  obtain ⟨S₀, hfd, hxS, hst⟩ := hfin
  have hinj : Function.Injective S.subtype := S.injective_subtype
  have := hfd
  have hU : FiniteDimensional ℂ (S₀.comap S.subtype) := by
    refine FiniteDimensional.of_injective
      (LinearMap.codRestrict S₀ (S.subtype ∘ₗ (S₀.comap S.subtype).subtype) (fun y => y.2)) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : S₀ => (y : H)) hab
  have hUst : KStab ε E (S₀.comap S.subtype) := by
    refine (hS n ε H σ S E hσ hM _ hU).2 ?_
    rintro g hg _ ⟨v, hv, rfl⟩
    exact ⟨⟨σ g v, hM.stab g (kset_subset_ujset hg) v v.2⟩, hst g hg v hv, rfl⟩
  have hrel : KRel ε E := fun a b c d _ _ => hM.gl a b c d
  have hun : KUnit ε E := by
    intro a b hab y z
    have := hM.unit a b y z
    simpa [Formalism.REAL.sgn, hab] using this
  obtain ⟨L, hLU, hxL, hLst, hirr, hdom, -⟩ := hL n ε S E μ x _ hrel hun hx0 hhw hU hUst hxS
  have hLfd : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLU
  refine ⟨L.map S.subtype, inferInstance, (hS n ε H σ S E hσ hM L hLfd).1 hLst, ?_, ?_, ?_⟩
  · intro S' hle hS'
    have hle' : S'.comap S.subtype ≤ L := by
      intro y hy
      obtain ⟨z, hz, hzy⟩ := hle hy
      rwa [← hinj hzy]
    have hmap : (S'.comap S.subtype).map S.subtype = S' := by
      apply Submodule.map_comap_eq_of_le
      exact hle.trans LinearMap.map_le_range
    have hst' : KStab ε E (S'.comap S.subtype) := by
      refine (hS n ε H σ S E hσ hM _ (Submodule.finiteDimensional_of_le hle')).2 ?_
      rwa [hmap]
    rcases hirr _ hle' hst' with h | h
    · left; rw [← hmap, h, Submodule.map_bot]
    · right; rw [← hmap, h]
  · exact ⟨x, ⟨x, hxL, rfl⟩, fun h => hx0 (Subtype.ext h), (hW n ε H σ S E hσ hM μ x).1 hhw.1⟩
  · rintro ν _ ⟨v, hv, rfl⟩ hv0 hwt
    exact hdom ν v hv (fun h => hv0 (by rw [h]; rfl)) ((hW n ε H σ S E hσ hM ν v).2 hwt)
end GlobalTheory.CompanionTheory.DSKType
