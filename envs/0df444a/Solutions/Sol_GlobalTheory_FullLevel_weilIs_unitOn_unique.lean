-- Prove2me | solution 1 for GlobalTheory.FullLevel.weilIs_unitOn_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:44:20.391149+00:00
-- url     : https://prove2.me/submissions/b6fcbc00-13d2-43b0-9976-fbe0f435a087

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_WeilIsUniqueOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFullSymplecticLevelStructureUniqueOfLevelsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFullSymplecticLevelStructureOfTateIsoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueFullLevel
import Theorems.Thm_GlobalTheory_ThetaGroupTest_weilIs_unique_of_local


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FullLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.FullLevel
theorem _root_.solution {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    {k : Type} [Field k] (x : Sp k ⟶ S) (n : ℤ) (g g' : Over.mk x ⟶ G) (c c' : kˣ)
    (h : Out.WeilIs G L n g g' (unitOn c)) (h' : Out.WeilIs G L n g g' (unitOn c')) : c = c' := by
  have hU : Subsingleton (Sp k) := by
    show Subsingleton (PrimeSpectrum k); infer_instance
  obtain ⟨p⟩ : Nonempty (Sp k) := by
    show Nonempty (PrimeSpectrum k); infer_instance
  have hp : ∀ V : (Over.mk x).left.Opens, p ∈ V → V = ⊤ := by
    intro V hV
    apply TopologicalSpace.Opens.ext
    ext y
    exact ⟨fun _ => trivial, fun _ => (Subsingleton.elim (α := Sp k) p y) ▸ hV⟩
  have H := GlobalTheory.ThetaGroupTest.weilIs_unique_of_local p hp hL h h'
  have hinj : Function.Injective (Units.map ((⊤ : (Over.mk x).left.Opens).ι.appTop.hom.toMonoidHom)) := by
    apply Units.map_injective
    haveI : IsIso ((⊤ : (Over.mk x).left.Opens).ι.app ⊤) := Scheme.Hom.isIso_app _ _ (by simp)
    exact (ConcreteCategory.bijective_of_isIso ((⊤ : (Over.mk x).left.Opens).ι.app ⊤)).1
  have H2 : unitOn c = unitOn c' := hinj H
  unfold unitOn at H2
  have hinj2 : Function.Injective (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) := by
    apply Units.map_injective
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1
  exact hinj2 H2
end GlobalTheory.FullLevel
