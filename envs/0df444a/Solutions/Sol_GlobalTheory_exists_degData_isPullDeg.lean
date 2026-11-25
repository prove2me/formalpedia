-- Prove2me | solution 1 for GlobalTheory.exists_degData_isPullDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:25:53.51712+00:00
-- url     : https://prove2.me/submissions/507f7e9b-0656-4a67-9b45-fa661fd0d15d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValEqOfAppInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDegDataIsPullDeg
import Theorems.Thm_GlobalTheory_DegPull_exists_isPullDeg
import Theorems.Thm_GlobalTheory_PsiEvenPull_psiEven_pull
import Theorems.Thm_GlobalTheory_psiIn_of_isPullDeg
import Theorems.Thm_GlobalTheory_tauBimult_of_isPullDeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolBaseChangeSt → _root_.ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R'), I.map φ ≤ I' → ∀ (D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegData R I) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Out.PsiOn D.toPre W) → (_root_.ReciprocityTheory.ChartRestriction.G.Out.specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W → ∃ (D' : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegData R' I') (hD : _root_.ReciprocityTheory.ChartRestriction.G.Out.IsPullDeg φ D.toPre D'.toPre), hD.W = W ∧ D'.toPre.P.g = D.toPre.P.g := by
  intro hP hG R R' _ _ _ _ I I' φ hle D W hψ hgen
  obtain ⟨D₀, hE, hT, hI, hF⟩ := D
  obtain ⟨D', hD, hW, hg⟩ :=
    _root_.GlobalTheory.DegPull.exists_isPullDeg hP R R' φ D₀ W hψ hgen
  refine ⟨⟨D', _root_.GlobalTheory.PsiEvenPull.psiEven_pull hG R R' φ D₀ D' hD hE,
    _root_.GlobalTheory.tauBimult_of_isPullDeg hG R R' φ D₀ D' hD hT, ?_, ?_⟩, hD, hW, hg⟩
  · intro χ hχ
    exact _root_.GlobalTheory.psiIn_of_isPullDeg R R' φ D₀ D' hD χ I I' hle
      (hI _ fun h => hχ (hD.xe.map_eq_zero_iff.mp h))
  · intro n
    refine ((hF n).preimage hD.xe.injective.injOn).subset ?_
    intro χ hχ h
    exact hχ (_root_.GlobalTheory.psiIn_of_isPullDeg R R' φ D₀ D' hD χ (I ^ n) (I' ^ n)
      (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono hle n) h)
end _root_.GlobalTheory
end GlobalTheory
