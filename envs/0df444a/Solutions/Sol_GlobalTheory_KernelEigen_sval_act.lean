-- Prove2me | solution 1 for GlobalTheory.KernelEigen.sval_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:29:53.350502+00:00
-- url     : https://prove2.me/submissions/5f71111c-d31e-4e72-a83d-4e3252440ce3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TranslatePullbackEigensection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.KernelEigen
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}
namespace GlobalTheory.KernelEigen
theorem _root_.solution {n : ℤ} {θ : ThetaGrp A L n T} {s s' : LB.Sec (LPow A L n T)} (H : IsActOf A L n θ s s')
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J) (hJ : Good L z J) :
    sval s' r z J = (tval θ r z J).val * sval s (r ≫ (translT A θ.pt).left) z J := by
  have l₁ := chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _)
  let j : Fin 2 → L.ι := fun i => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i)
  have hz : r z ∈ LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j := hJ.mem _ r
  have e : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left, translT, lift_snd]
  rw [sval_of s _ z J (fun _ => j 1) (fun _ => by rw [Category.assoc, e]; rfl)]
  exact (gs_res r z (chart_le_zero A L _ j) hz _).symm.trans ((congrArg (gs r z _) (H j)).trans
    ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hz _)
      ((gs_res r z (l₁ j) hz _).trans (gs_pull r (translT A θ.pt).left z
        (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1)) (l₁ j hz) _)))))
end GlobalTheory.KernelEigen
