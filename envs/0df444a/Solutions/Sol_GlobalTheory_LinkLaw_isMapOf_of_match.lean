-- Prove2me | solution 1 for GlobalTheory.LinkLaw.isMapOf_of_match
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:22:59.536274+00:00
-- url     : https://prove2.me/submissions/72c129ae-6716-4c1a-abac-fa57cb20a125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsLawOfOfMatch
import Theorems.Thm_GlobalTheory_LinkLaw_jetSubstP_coord
import Theorems.Thm_GlobalTheory_LinkLaw_read_match
import Theorems.Thm_GlobalTheory_LinkLaw_constantCoeff_ev
import Theorems.Thm_GlobalTheory_LinkLaw_exists_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open GlobalTheory GlobalTheory.LinkLaw
variable {V : Type} [CommRing V]
namespace GlobalTheory.LinkLaw
theorem _root_.solution {G : Over (Sp V)} {d : ℕ} (φ : Pt V 1 d)
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (xT : JetPts G (Fin 1 × Fin d)) (f : G ⟶ G)
    (hf : ∀ m, xT m ≫ f =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)) ≫ xT m)
    (x : JetSer.Fam G (Fin d)) (hM : Match (oneCol d) xT x) : JetSer.IsMapOf x x f φ := by
  refine ⟨hφ, fun n a y hy => ?_⟩
  have hab : ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![a] : Fin 1 → Pt V n d) i j) = 0 := by
    intro i j
    fin_cases i
    exact hy.1 j
  refine ⟨fun j => constantCoeff_ev _ hab _ (hφ j), fun m => ?_⟩
  obtain ⟨e, he1, he2⟩ := hM m
  obtain ⟨ψa, ha1, ha2⟩ := hy.2 m
  obtain ⟨Φ, hΦ, hsub⟩ := exists_subst
    (fun p : Fin 1 × Fin d => (![a] : Fin 1 → Pt V n d) p.1 p.2) (fun p => hab p.1 p.2) m
  have key : ∀ j, (Φ.comp ((AlgHom.id V _).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m))) (Chart.zR m j) = JetSer.toJet m (a j) := by
    intro j
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1, AlgHom.id_apply]
    exact hΦ (0, j)
  have ea : ψa = Φ.comp ((AlgHom.id V _).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)) :=
    Chart.jet_ext fun j => (ha1 j).trans (key j).symm
  have hid : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (AlgHom.id V (Jet V (Fin 1 × Fin d) m)) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  refine ⟨Φ.comp ((jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)).comp
    (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)), fun j => ?_, ?_⟩
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1,
      jetSubstP_coord m (fun p : Fin 1 × Fin d => φ p.2) _ (hφ _)]
    exact hsub _
  · show y m ≫ f = _
    rw [← read_match (xT m) (x m) e he2, ← hf m, ha2, ea, ← read_match (xT m) (x m) e he2, hid,
      Category.id_comp]
    simp only [Category.assoc]
end GlobalTheory.LinkLaw
