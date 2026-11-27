-- Prove2me | solution 1 for GlobalTheory.AnValJetEx.appLE_spMap_jetPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:15:13.719349+00:00
-- url     : https://prove2.me/submissions/de9cb803-637e-4b46-b478-e90b45ecb78f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsGeneratorJetReading
import Theorems.Thm_GlobalTheory_AnValJetEx_jet_point_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_appLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_closedPoint


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
open GlobalTheory GlobalTheory.AnValJetEx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnValJetEx
theorem _root_.solution {d : ℕ} {Y : Scheme.{0}} (e : (Fin d → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (m : ℕ)
    {R : Type} [CommRing R] (r : Jet ℂ (Fin 1 × Fin d) m →+* R) (U : Y.Opens) (hU : e 0 cpt ∈ U)
    (h : ⊤ ≤ (spMap r ≫ jetPt e hol m) ⁻¹ᵁ U) (a : Γ(Y, U)) :
    ((spMap r ≫ jetPt e hol m).appLE U ⊤ h).hom a = toΓ R (r (jetOf m fun z => valAt' (e z) U a)) := by
  have h1 : ⊤ ≤ jetPt e hol m ⁻¹ᵁ U := fun p _ => by
    rw [jet_point_eq (K := ℂ) (I := Fin 1 × Fin d) (m := m) p]
    show jetPt e hol m (IsLocalRing.closedPoint _) ∈ U
    rwa [jetPt_closedPoint]
  have e1 : (spMap r ≫ jetPt e hol m).appLE U ⊤ h = (jetPt e hol m).appLE U ⊤ h1 ≫ (spMap r).appTop :=
    (Scheme.Hom.appLE_comp_appLE (spMap r) (jetPt e hol m) U ⊤ ⊤ h1 le_rfl).symm
  rw [e1, jetPt_appLE e hol m U hU h1, Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl
end GlobalTheory.AnValJetEx
