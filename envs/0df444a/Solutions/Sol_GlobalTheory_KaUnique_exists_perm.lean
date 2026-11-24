-- Prove2me | solution 1 for GlobalTheory.KaUnique.exists_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:22:37.088838+00:00
-- url     : https://prove2.me/submissions/6d473a0f-4407-4aff-adc9-a1b158e11082

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TopLeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KosBlockMulKosD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsSquareDetComparisonEqMulDetPowOfBasisChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KaFormHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfVanish
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KeyInvariantFromIntersectionUnique
import Theorems.Thm_GlobalTheory_KaUnique_section_ext
import Theorems.Thm_GlobalTheory_KaUnique_valT_sec


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
namespace GlobalTheory.KaUnique
theorem _root_.solution {K : Type} [Field K] {x : KeyIn K} {n d : ℕ} {s : Fin x.P.g → RR x n} {z z' : Fin d → Pt x}
    {ch ch' : Fin d → x.P.L.ι} (hz : EtZ x s z ch) (hz' : EtZ x s z' ch') :
    ∃ σ : Equiv.Perm (Fin d), ∀ a, z' (σ a) = z a := by
  let p : Sp K := IsLocalRing.closedPoint K
  have hs : ∀ q q' : Sp K, q = q' := fun q q' => Subsingleton.elim (α := PrimeSpectrum K) q q'
  have h1 : ∀ a, ∃ a', z' a' = z a := by
    intro a
    obtain ⟨a', q, hq⟩ := hz'.2.2.2.2 ((z a).left p) (fun i hi => by
      obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
      have hcU : ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U c := fun q _ => by
        rw [hs q p]; exact x.P.A.left.basicOpen_le _ hc
      have e := valT_sec (T := K) (z a).left x.P.L c (ch a) hcU (hz.1 a) n (s i)
      erw [hz.2.1 a i, mul_zero, valT_eq _ _ hcU] at e
      have e1 : IsUnit (evalHom (T := K) (z a).left (x.P.L.U c) hcU ((s i).f c)) ↔
          IsUnit (((show Sp K ⟶ x.P.A.left from (z a).left).appLE (x.P.L.U c) ⊤ hcU).hom ((s i).f c)) :=
        isUnit_map_iff (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv _
      have e2 := Scheme.basicOpen_appLE (show Sp K ⟶ x.P.A.left from (z a).left) ⊤ (x.P.L.U c) hcU ((s i).f c)
      have e3 : IsUnit (((show Sp K ⟶ x.P.A.left from (z a).left).appLE (x.P.L.U c) ⊤ hcU).hom ((s i).f c)) := by
        apply RingedSpace.isUnit_of_isUnit_germ
        intro q hq
        have : q ∈ (Sp K).basicOpen
            (((show Sp K ⟶ x.P.A.left from (z a).left).appLE (x.P.L.U c) ⊤ hcU).hom ((s i).f c)) := by
          erw [e2]; rw [hs q p]; exact ⟨trivial, hc⟩
        exact ((Sp K).mem_basicOpen _ q hq).1 this
      exact (e1.2 e3).ne_zero e)
    exact ⟨a', Over.OverMorphism.ext (section_ext x.P.A.hom _ _ (Over.w (z' a')) (Over.w (z a)) q p hq)⟩
  choose f hf using h1
  have hinj : Function.Injective f := fun a a' e => by
    by_contra hne
    exact hz.2.2.2.1 a a' hne p (by rw [← hf a, ← hf a', e])
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩
end GlobalTheory.KaUnique
