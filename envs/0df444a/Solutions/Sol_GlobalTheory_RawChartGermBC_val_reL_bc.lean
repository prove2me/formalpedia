-- Prove2me | solution 1 for GlobalTheory.RawChartGermBC.val_reL_bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:05:36.101907+00:00
-- url     : https://prove2.me/submissions/0377b3b6-9af1-4ec5-b73e-f9fbc2032590

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LBPull
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_RawChartBaseChangeRigGerm
import Theorems.Thm_GlobalTheory_RawChartGermBC_map_psIn
import Theorems.Thm_GlobalTheory_RawChartGermBC_subst_rjBC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RawChartGermBC
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ)
namespace GlobalTheory.RawChartGermBC
theorem _root_.solution (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G)
    (hx : ∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m)
    (e : ∀ m, RFrTy x0 d x m) (e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m)
    (he : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L
      (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left))
    (wP : PrimTy H Xo) (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (rjO (spMap ψ ≫ x0) d m 1).left) (z : Z) {J}
    (hJ : Good Xo.univ.t.PP.L z J) :
    val (reL (spMap ψ ≫ x0) d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP m) r z J =
      val (reL x0 d x act e wP m) (r ≫ (rjBC ψ x0 d m 1).left) z J := by
  have hφ : ∀ p : Fin 2 × Fin d,
      (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (MvPowerSeries.map ψ (act H.w0 j))] :
        Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S') p.1 p.2 =
      MvPolynomial.map ψ ((![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (act H.w0 j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2) := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [map_psIn]
  have hxl : (x' m).left = (rjBC ψ x0 d m 1).left ≫ (x m).left := by
    rw [hx m]
    rfl
  unfold reL rpe
  simp only [val_mul hJ, val_pull hJ]
  congr 1
  · rw [hxl, Category.assoc]
  · refine (val_pull hJ _ _ r).trans ?_
    refine (val_corr hJ (he m) _).trans ?_
    refine (val_pull hJ _ _ _).trans ?_
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    simp only [Category.assoc]
    rw [subst_rjBC ψ x0 d m 2 1 _ _ hφ]
end GlobalTheory.RawChartGermBC
