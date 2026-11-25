-- Prove2me | solution 1 for GlobalTheory.LinkSec.linkSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:04:33.359616+00:00
-- url     : https://prove2.me/submissions/f133c645-a601-480c-a4f1-90d4bdf7f09f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsLawOfOfMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ValSerGermFnVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GsSpMapGermAt
import Theorems.Thm_GlobalTheory_LinkSec_change_index
import Theorems.Thm_P2M_GlobalTheory_LinkSec_gs_to__eq_9fe3707169ce
import Theorems.Thm_GlobalTheory_LinkSec_gs_spMap_germAt
import Theorems.Thm_GlobalTheory_LinkSec_psJet_pow
import Theorems.Thm_GlobalTheory_LinkSec_gs_of_isSer1
import Theorems.Thm_GlobalTheory_LinkSec_diagSub_zero
import Theorems.Thm_GlobalTheory_LinkSec_diagSub_one
import Theorems.Thm_GlobalTheory_LinkSec_diagSub_psJet
import Theorems.Thm_P2M_GlobalTheory_LinkSec_homAt_comp__47a5a5bde5a3
import Theorems.Thm_GlobalTheory_LinkSec_val_prim_eq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_stalkMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LinkSec
variable {V : Type} [CommRing V]
namespace GlobalTheory.LinkSec
theorem _root_.solution : LinkSecSt := by
  intro E _ _ _ H V _ _ t hp d BT tg xT eT wPT hC hF hW x _ hM j _ ρ hρ hc ε hε q σ r S g hr hS hg m y J hJ
  letI := H.starRing
  obtain ⟨hj, vr⟩ := gs_of_isSer1 xT x hM _ _ r hr m y
  obtain ⟨-, vS⟩ := gs_of_isSer1 xT x hM _ _ S hS m y
  let s := Formalism.L2.Pj.homAt (𝟙 (Sp V)) (diagSub m (BT.A.act H.w0))
  have h₀ : s ≫ jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2) = xT m := by
    rw [jptG, ← Category.assoc, homAt_comp', diagSub_zero]
    refine Eq.trans (congrArg (· ≫ xT m) ?_) (Category.id_comp _)
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  have h₁ : s ≫ jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2) = xT m ≫ t.act.act H.w0 := by
    rw [jptG, ← Category.assoc, homAt_comp', diagSub_one]
    exact (hC.act m H.w0).symm
  obtain ⟨hs, c, c₁, c₂⟩ := change_index (t.act.act H.w0) (xT m) s _ _ h₀ h₁ (eT m) (hF.gen m) ρ hρ q σ j y hj J hJ
  obtain ⟨J₂, hJ₂, e₂⟩ := exists_good t.PP.L t.PP.isLB (s.left y)
    (cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)]) (fun _ => j)
    (fun _ _ _ => rfl) (fun I => Set.mem_iInter.1 hs I)
  have e₂' : ∀ I, J₂ (𝟙 _ ≫ cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)] I) = j :=
    fun I => (congrArg J₂ (Category.id_comp _)).trans (e₂ I)
  have v₂ := hε m (s.left y) J₂ hJ₂ e₂'
  have v₃ := (gs_unit (𝟙 _) (s.left y) _ hs _).trans
    ((congrArg Units.val (val_of (L := t.PP.L) (ε := cε 2) (eT m) (𝟙 _) (s.left y) J₂ (fun _ => j) e₂')).symm.trans v₂)
  have vε : (gm s.left y _ ((eT m).s fun _ => j)).val = germAt _ y (psJet m (diagSer BT H.w0 ε)) :=
    (gs_unit s.left y _ hs _).symm.trans ((gs_stalkMap s.left y _ hs _).trans
      ((congrArg (s.left.stalkMap y).hom v₃).trans ((gs_stalkMap s.left y ⊤ trivial _).symm.trans
        ((gs_spMap_germAt _ y _).trans (congrArg (germAt _ y) (diagSub_psJet m _ (BT.A.const H.w0) ε))))))
  have vρ : (gm (xT m).left y _ (ρ.s fun _ => j)).val = germAt _ y (psJet m r) :=
    (gs_unit (xT m).left y _ hj _).symm.trans vr
  have vL : val (eLG t (𝟙 (Sp V)) d xT BT.A.act eT wPT m) (𝟙 (Sp (Jet V (Fin 1 × Fin d) m))) y J =
      c * (gm (xT m).left y _ (ρ.s fun _ => j) * gm s.left y _ ((eT m).s fun _ => j)) := by
    refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) c₂)
    · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_prim_eq t hp wPT hW ρ hρ hc (xT m).left y J hJ))
      exact congrArg (fun p => val wPT p y J) (Category.id_comp _)
    · refine (val_pull hJ _ _ _).trans ?_
      exact congrArg (fun p => val (L := t.PP.L) (ε := cε 2) (eT m) p y J) (Category.id_comp _)
  rw [vL, gs_toΓ_eq]
  refine c₁.trans ((congrArg (_ * ·) vS).trans ?_)
  rw [← hg, FBIdJet.psJet_mul, psJet_pow, FBIdJet.psJet_mul, map_mul, map_pow, map_mul, ← vε, ← vρ]
  simp only [Units.val_pow_eq_pow_val, Units.val_mul]
  ring
end GlobalTheory.LinkSec
