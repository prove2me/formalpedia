-- Prove2me | solution 1 for GlobalTheory.RawChartBC.rIsChart_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:10:12.373085+00:00
-- url     : https://prove2.me/submissions/ed6b25bd-b070-4711-b944-b2534367d79f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsRawChartBaseChangeJetPoints
import Theorems.Thm_GlobalTheory_RawChartBC_psTrunc_map
import Theorems.Thm_GlobalTheory_RawChartBC_basis_map
import Theorems.Thm_GlobalTheory_RawChartBC_sq_aug
import Theorems.Thm_GlobalTheory_RawChartBC_sq_trunc
import Theorems.Thm_GlobalTheory_RawChartBC_sq_subst
import Theorems.Thm_GlobalTheory_RawChartBC_sq_tan
import Theorems.Thm_GlobalTheory_RawChartBC_sq_copy
import Theorems.Thm_GlobalTheory_RawChartBC_isCombAt_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.RawChartBC
open ReciprocityTheory.ChartRestriction.G.PullbackSections
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}
namespace GlobalTheory.RawChartBC
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (uvec : Lt1 Dw → Fin d → S), RIsChart x0 u d F act uvec x → RIsChart (spMap ψ ≫ x0) (fun τ i => spMap (dualMap ψ) ≫ u τ i) d (fun i => MvPowerSeries.map ψ (F i)) (fun a i => MvPowerSeries.map ψ (act a i)) (fun ℓ j => ψ (uvec ℓ j)) x' := by
  intro E _ _ _ H Dw l Xo S S' _ _ ψ x0 d F act x x' hx' u uvec hX
  obtain rfl : x' = fun m => rjBC ψ x0 d m 1 ≫ x m := funext hx'
  refine ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m a => ?_, fun ℓ => ?_, basis_map ψ uvec hX.basis⟩
  · rw [← Category.assoc, sq_aug, Category.assoc, hX.zero m]
    simp [Hom.one_def]
  · rw [← Category.assoc, sq_trunc, Category.assoc, hX.trunc m]
  · simp only [psTrunc_map]
    rw [← Category.assoc, sq_subst, Category.assoc, hX.law m]
    simp only [rjpt, Hom.mul_def, comp_lift_assoc]
    rw [← Category.assoc (homAt _ _) (rjBC _ _ _ _ _), ← Category.assoc (homAt _ _) (rjBC _ _ _ _ _), sq_copy,
      sq_copy, Category.assoc, Category.assoc]
  · simp only [psTrunc_map]
    rw [← Category.assoc (homAt _ _), sq_subst, Category.assoc, Category.assoc, hX.act m a]
  · have hv : (fun j : Fin d => (homAt (spMap ψ ≫ x0) (jetTan ((0 : Fin 1), j) :
        Jet S' (Fin 1 × Fin d) (0 + 1) →ₐ[S'] DualNumber S') ≫ (rjBC ψ x0 d 1 1 ≫ x 1)).left) =
        fun j => spMap (dualMap ψ) ≫ (homAt x0 (jetTan ((0 : Fin 1), j) :
          Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left := by
      funext j
      rw [← Category.assoc, sq_tan, Category.assoc]
      rfl
    have := isCombAt_map ψ x0 (hX.tan ℓ)
    rw [← hv] at this
    exact this
end GlobalTheory.RawChartBC
