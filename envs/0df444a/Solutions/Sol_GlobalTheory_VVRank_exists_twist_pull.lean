-- Prove2me | solution 1 for GlobalTheory.VVRank.exists_twist_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:44:27.059801+00:00
-- url     : https://prove2.me/submissions/546e10e5-5133-4e95-8edb-e9f6d8d4b341

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Theorems.Thm_GlobalTheory_VVRank_exists_gen_pullTo
import Theorems.Thm_GlobalTheory_VVRank_sv_pullS
import Theorems.Thm_GlobalTheory_VVRank_sv_of_isTwistPull
import Theorems.Thm_GlobalTheory_VVRank_isTwistPull_of_sv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VVRank
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
variable {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
  {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
namespace GlobalTheory.VVRank
theorem _root_.solution (hL : L.IsLB) (hα : α.IsGen) {T' : Over S} (h : T' ⟶ T)
    {ψ' : T' ⊗ A ⟶ T' ⊗ A} {m' : T' ⊗ A ⟶ A} (hm' : ψ' ≫ snd T' A = m')
    (e : ψ' ≫ h ▷ A = h ▷ A ≫ ψ) :
    ∃ α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T' A).left, m'.left] ![a, -b]), α'.IsGen ∧
      ∀ s s', IsTwistPull A L ψ m hm a b α s s' →
        IsTwistPull A L ψ' m' hm' a b α' (pullS A b h s) (pullS A a h s') := by
  obtain ⟨α', h₁, h₂⟩ := exists_gen_pullTo (φ' := ![(snd T' A).left, m'.left]) α hα (h ▷ A).left
    (fun k => by
      fin_cases k
      · exact whisker_snd_left A h
      · change (h ▷ A).left ≫ m.left = m'.left
        rw [← Over.comp_left, ← hm, ← hm', ← Category.assoc, ← e, Category.assoc, whiskerRight_snd])
  refine ⟨α', h₁, fun s s' H => isTwistPull_of_sv A hL h₁ fun y J hJ => ?_⟩
  rw [sv_pullS A a h s' _ y hJ, sv_pullS A b h s _ y hJ, h₂ _ _ y J hJ, sv_of_isTwistPull A H _ y hJ,
    Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, e]
end GlobalTheory.VVRank
