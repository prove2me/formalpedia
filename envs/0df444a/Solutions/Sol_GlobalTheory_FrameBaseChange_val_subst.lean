-- Prove2me | solution 1 for GlobalTheory.FrameBaseChange.val_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:29:42.892572+00:00
-- url     : https://prove2.me/submissions/fa6bb294-5e5e-48a4-95ad-16581c4cc863

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsFrameRawChartBaseChange
import Theorems.Thm_GlobalTheory_FrameBaseChange_subst_square
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
open GlobalTheory GlobalTheory.FrameBaseChange
open MvPolynomial (X C)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X)
variable {ψ x0} {d : ℕ} {x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G} {x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G}
variable {e : ∀ m, RFrTy x0 d x m} {e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m} {m : ℕ}
  (hc : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L
    (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left))
  {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι} (hJ : Good Xo.univ.t.PP.L z J)
include hc hJ
namespace GlobalTheory.FrameBaseChange
theorem _root_.solution {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S)
    (φ' : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S') (hφ : ∀ i j, φ' i j = MvPolynomial.map ψ (φ i j))
    (r : Z ⟶ (rjO (spMap ψ ≫ x0) d m n).left) :
    val (rpe (spMap ψ ≫ x0) d x' e' m φ') r z J = val (rpe x0 d x e m φ) (r ≫ (rjBC ψ x0 d m n).left) z J := by
  unfold rpe
  refine ((val_pull hJ _ _ r).trans ((val_corr hJ hc _).trans (val_pull hJ _ _ _))).trans
    (Eq.trans (congrArg (fun q => val (e m) q z J) ?_) (val_pull hJ _ _ _).symm)
  have e2 : (fun p : Fin 2 × Fin d => φ' p.1 p.2) = fun p => MvPolynomial.map ψ (φ p.1 p.2) :=
    funext fun p => hφ p.1 p.2
  have hsq := subst_square ψ x0 m (fun p : Fin 2 × Fin d => φ p.1 p.2)
  simp only [Category.assoc, ← Over.comp_left, e2, hsq]
end GlobalTheory.FrameBaseChange
