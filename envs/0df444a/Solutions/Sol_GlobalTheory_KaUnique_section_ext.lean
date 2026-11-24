-- Prove2me | solution 1 for GlobalTheory.KaUnique.section_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:29:50.16296+00:00
-- url     : https://prove2.me/submissions/d671cf7b-dbf4-4330-bd97-93927e7003df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignSwap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TopLeTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KaUnique
variable {T T' : Type} [CommRing T] [CommRing T'] {X : Scheme.{0}}
namespace GlobalTheory.KaUnique
theorem _root_.solution {K : Type} [Field K] (π : X ⟶ Sp K) (w w' : Sp K ⟶ X) (hw : w ≫ π = 𝟙 _) (hw' : w' ≫ π = 𝟙 _)
    (p p' : Sp K) (e : w p = w' p') : w = w' := by
  have hs : ∀ q q' : Sp K, q = q' := fun q q' => Subsingleton.elim (α := PrimeSpectrum K) q q'
  obtain rfl := hs p p'
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (w p)) isOpen_univ
  have h : ⊤ ≤ w ⁻¹ᵁ U := fun q _ => by rw [hs q p]; exact hxU
  have h' : ⊤ ≤ w' ⁻¹ᵁ U := fun q _ => by rw [hs q p]; change w' p ∈ U; rw [← e]; exact hxU
  have key : ∀ (v : Sp K ⟶ X) (hv : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), IsUnit (evalHom v U hv f) ↔ v p ∈ X.basicOpen f := by
    intro v hv f
    have e1 : IsUnit (evalHom v U hv f) ↔ IsUnit ((v.appLE U ⊤ hv).hom f) :=
      isUnit_map_iff (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv _
    rw [e1]
    have e2 := Scheme.basicOpen_appLE v ⊤ U hv f
    constructor
    · intro hu
      have : p ∈ (Sp K).basicOpen ((v.appLE U ⊤ hv).hom f) := by
        rw [Scheme.basicOpen_of_isUnit _ hu]; trivial
      erw [e2] at this
      exact this.2
    · intro hp
      apply RingedSpace.isUnit_of_isUnit_germ
      intro q hq
      have : q ∈ (Sp K).basicOpen ((v.appLE U ⊤ hv).hom f) := by
        erw [e2]; rw [hs q p]; exact ⟨trivial, hp⟩
      exact ((Sp K).mem_basicOpen _ q hq).1 this
  have hev : evalHom w U h = evalHom w' U h' := by
    ext f
    have h1 : evalHom w U h (f - cst π U (evalHom w U h f)) = 0 := by
      rw [map_sub, ← valT_eq w U h (cst _ _ _), valT_cst w π hw U h, sub_self]
    have h2 : ¬ IsUnit (evalHom w' U h' (f - cst π U (evalHom w U h f))) := by
      rw [key, ← e, ← key w h, h1]; exact not_isUnit_zero
    rw [isUnit_iff_ne_zero, not_not, map_sub, ← valT_eq w' U h' (cst _ _ _), valT_cst w' π hw' U h', sub_eq_zero] at h2
    exact h2.symm
  have happ : w.appLE U ⊤ h = w'.appLE U ⊤ h' := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of K)).hom]
    exact CommRingCat.hom_ext hev
  have a1 := IsAffineOpen.SpecMap_appLE_fromSpec w hU (isAffineOpen_top (Sp K)) h
  have a2 := IsAffineOpen.SpecMap_appLE_fromSpec w' hU (isAffineOpen_top (Sp K)) h'
  rw [happ, a2, IsAffineOpen.fromSpec_top] at a1
  exact ((cancel_epi _).1 a1).symm
end GlobalTheory.KaUnique
