-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.isPull_famPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:02:33.264811+00:00
-- url     : https://prove2.me/submissions/c3789d4a-4034-4752-b48e-c9577b731b3c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsFOfIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfInjective
import Theorems.Thm_GlobalTheory_ThetaSpecialise_isPull_pullOver
import Theorems.Thm_GlobalTheory_ThetaSpecialise_IsPull_comp
import Theorems.Thm_GlobalTheory_ThetaSpecialise_eq_pullOver_of_secScal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.ThetaSpecialise
theorem _root_.solution (hG : GlobalFnsSt) {k : ℕ} (F₀ : Fam D (FractionRing R) k) (α : D.X) (f : D.SecB k α)
    (h : GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F₀.s α) (D.famφB α) (DegPre.famε k) f
      (DegPre.prB D (FractionRing R)).left 1) :
    IsPull (DegPre.prB D F).left ((famPull D (FractionRing R) F hG k F₀).s α) f := by
  have hL : D.P.L.IsLB := D.P.isLB
  have hpZ : (DegPre.prB D (FractionRing R)).left ≫ specZIsTerminal.from _ =
      specZIsTerminal.from _ ≫ Spec.map (CommRingCat.ofHom (RingHom.id ℤ)) :=
    specZIsTerminal.hom_ext _ _
  have hφE : ∀ i, DegPre.famφ D (FractionRing R) α i = (DegPre.prB D (FractionRing R)).left ≫ D.famφB α i :=
    famφ_prB D (FractionRing R) α
  have h₁ : IsPull (DegPre.prB D (FractionRing R)).left (F₀.s α) f := by
    have key := isPull_pullOver (L := D.P.L) (ε := DegPre.famε k) hpZ hφE f
    rwa [eq_pullOver_of_secScal hL hpZ hφE h] at key
  have h₂ := isPull_pullOver (L := D.P.L) (ε := DegPre.famε k) (isPullback_famMap D (FractionRing R) F).w
    (famφ_famMap D (FractionRing R) F α) (F₀.s α)
  have hc : (famMap D (FractionRing R) F).left ≫ (DegPre.prB D (FractionRing R)).left = (DegPre.prB D F).left := by
    rw [← Over.comp_left, famMap_snd]
  exact IsPull.comp h₂ h₁ hc
end GlobalTheory.ThetaSpecialise
