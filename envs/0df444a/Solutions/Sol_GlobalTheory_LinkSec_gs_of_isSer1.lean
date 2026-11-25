-- Prove2me | solution 1 for GlobalTheory.LinkSec.gs_of_isSer1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:39:07.190835+00:00
-- url     : https://prove2.me/submissions/5ede5004-1530-4865-97a5-557fa91021db

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
import Theorems.Thm_GlobalTheory_LinkSec_toJet_eq
import Theorems.Thm_GlobalTheory_LinkSec_ev_pt_one
import Theorems.Thm_GlobalTheory_JetSer_toJet_X
import Theorems.Thm_GlobalTheory_JetSer_valSer_germ_fnVal


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
theorem _root_.solution {G : Over (Sp V)} {d : ℕ} (xT : JetPts G (Fin 1 × Fin d)) (x : JetSer.Fam G (Fin d))
    (hM : Match (oneCol d) xT x) (U : G.left.Opens) (f : Γ(G.left, U)) (g : PS V 1 d) (h : JetSer.IsSer1 x U f g)
    (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) :
    (xT m).left y ∈ U ∧ gs (xT m).left y U f = germAt _ y (psJet m g) := by
  have R : JetSer.Rep x (pt V (n := 1) d 0) (fun m => LinkLaw.toAt (V := V) (Jet V (Fin 1 × Fin d) m) ≫ xT m) := by
    refine ⟨fun j => by simp [pt], fun m => ?_⟩
    obtain ⟨e, he1, he2⟩ := hM m
    refine ⟨(e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m), fun j => ?_, ?_⟩
    · exact (he1 j).trans (JetSer.toJet_X m ((0 : Fin 1), j)).symm
    · apply Over.OverMorphism.ext
      exact (Category.id_comp _).trans he2
  obtain ⟨h1, h2⟩ := h 1 _ _ R m
  have e : (LinkLaw.toAt (V := V) (Jet V (Fin 1 × Fin d) m) ≫ xT m).left = (xT m).left := Category.id_comp _
  have h1' : ⊤ ≤ (xT m).left ⁻¹ᵁ U := e ▸ h1
  have h2' : JetSer.fnVal (A := Jet V (Fin 1 × Fin d) m) (xT m).left U f = psJet m g :=
    (congrArg (fun p => JetSer.fnVal (A := Jet V (Fin 1 × Fin d) m) p U f) e).symm.trans
      (h2.trans (by rw [ev_pt_one]; exact toJet_eq m g))
  refine ⟨h1' (show y ∈ (⊤ : (Sp (Jet V (Fin 1 × Fin d) m)).Opens) from trivial), ?_⟩
  rw [← h2']
  exact (JetSer.valSer_germ_fnVal (A := Jet V (Fin 1 × Fin d) m) (xT m).left U h1' y f).symm
end GlobalTheory.LinkSec
