-- Prove2me | solution 1 for GlobalTheory.RawFrameBC.exists_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:43:08.49382+00:00
-- url     : https://prove2.me/submissions/2df62130-6cf4-4249-8047-6c91e7b6d80a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsRawChartFramesBaseChange
import Theorems.Thm_GlobalTheory_RawFrameBC_exists_reindexed_pull
import Theorems.Thm_GlobalTheory_RawFrameBC_sq_subst
import Theorems.Thm_GlobalTheory_RawFrameBC_rjpt_bc
import Theorems.Thm_P2M_GlobalTheory_RawFrameBC_c__comp_985ef5b88959

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
open GlobalTheory GlobalTheory.RawFrameBC
namespace GlobalTheory.RawFrameBC
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (e : ∀ m, RFrTy x0 d x m), (∀ m, (e m).IsGen) → ∃ e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m, (∀ m, (e' m).IsGen) ∧ (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left)) ∧ ∀ (m n' : ℕ) (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S), LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (rpe (spMap ψ ≫ x0) d x' e' m (fun i j => MvPolynomial.map ψ (φ i j))) (LB.pullGen Xo.univ.t.PP.L _ _ (rpe x0 d x e m φ) (rjBC ψ x0 d m n').left) := by
  intro E _ _ _ H Dw l Xo S S' _ _ ψ x0 d F act x x' hx e he
  have hφ : ∀ m, cφ ![rjpt (spMap ψ ≫ x0) d x' m (0 : Fin 2), rjpt (spMap ψ ≫ x0) d x' m (1 : Fin 2)] =
      fun k => (rjBC ψ x0 d m 2).left ≫ cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)] k := by
    intro m
    rw [rjpt_bc ψ x0 d x x' hx m 0, rjpt_bc ψ x0 d x x' hx m 1, cφ_comp]
  choose e' he' hcorr hnat using fun m =>
    exists_reindexed_pull Xo.univ.t.PP.isLB (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2)
      (e m) (he m) (rjBC ψ x0 d m 2).left _ (hφ m)
  refine ⟨e', he', fun m => hcorr m, fun m n' φ => ?_⟩
  have hab := congrArg Over.Hom.left (sq_subst ψ x0 d m (fun p : Fin 2 × Fin d => φ p.1 p.2))
  simp only [Over.comp_left] at hab
  unfold rpe
  exact hnat m _ _ _ _ _ hab
end GlobalTheory.RawFrameBC
