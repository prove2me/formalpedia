-- Prove2me | solution 1 for GlobalTheory.isIso_of_isClosedImmersion_of_thickenings_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:18:12.354423+00:00
-- url     : https://prove2.me/submissions/e92d370a-ba40-45eb-8940-2263a0584535

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIsoOfIsClosedImmersionOfThickeningsOfIsProper
import Theorems.Thm_GlobalTheory_ThickeningClosed_exists_mul_eq_zero_of_mem
import Theorems.Thm_GlobalTheory_ThickeningClosed_isOpen_zeroLocusOpen
import Theorems.Thm_GlobalTheory_ThickeningClosed_mem_of_thickenings


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ThickeningClosed
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    (Y : Over (Spec (CommRingCat.of R))) [IsProper Y.hom] {Z : Scheme.{0}} (j : Z ⟶ Y.left)
    [IsClosedImmersion j]
    (h : ∀ n : ℕ, ∃ l : (thickObj R I n Y).left ⟶ Z, l ≫ j = (fstG I n Y).left) : IsIso j := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have h' : ∀ n : ℕ, ∃ l : pullback Y.hom (thick R I n) ⟶ Z, l ≫ j = pullback.fst Y.hom (thick R I n) :=
    fun n => h n
  have hnear : ∀ x : Y.left, x ∈ zeroLocusOpen j.ker := by
    by_contra hne
    simp only [not_forall] at hne
    obtain ⟨x₀, hx₀⟩ := hne
    have hSc : IsClosed (zeroLocusOpen j.ker)ᶜ := (isOpen_zeroLocusOpen j.ker).isClosed_compl
    have hT : IsClosed (Y.hom '' (zeroLocusOpen j.ker)ᶜ) := Y.hom.isClosedMap _ hSc
    obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal (Y.hom x₀).asIdeal (Y.hom x₀).isPrime.ne_top
    have hcl : (⟨m, hm.isPrime⟩ : PrimeSpectrum (CommRingCat.of R)) ∈ closure {Y.hom x₀} :=
      (PrimeSpectrum.le_iff_mem_closure _ _).mp hpm
    obtain ⟨x, hxS, hx⟩ :=
      closure_minimal (Set.singleton_subset_iff.mpr
        (Set.mem_image_of_mem _ hx₀ : Y.hom x₀ ∈ Y.hom '' (zeroLocusOpen j.ker)ᶜ)) hT hcl
    apply hxS
    refine ThickeningClosed.mem_of_thickenings I Y.hom j h' x ?_
    rw [hx]
    exact hI.trans (sInf_le ⟨bot_le, hm⟩)
  have hker : j.ker = ⊥ := by
    ext U a
    simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, Submodule.mem_bot]
    constructor
    · intro ha
      have hJ : LinearMap.ker (LinearMap.toSpanSingleton Γ(Y.left, U) Γ(Y.left, U) a) = ⊤ := by
        by_contra hJ
        obtain ⟨q, hq, hJq⟩ := Ideal.exists_le_maximal _ hJ
        obtain ⟨s, hs, hsa⟩ :=
          ThickeningClosed.exists_mul_eq_zero_of_mem j.ker U ⟨q, hq.isPrime⟩ (hnear _) ha
        exact hs (hJq (by simp [LinearMap.mem_ker, hsa]))
      have h1 : (1 : Γ(Y.left, U)) ∈ LinearMap.ker (LinearMap.toSpanSingleton Γ(Y.left, U) Γ(Y.left, U) a) :=
        hJ ▸ Submodule.mem_top
      simpa using h1
    · rintro rfl
      exact zero_mem _
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
end GlobalTheory
