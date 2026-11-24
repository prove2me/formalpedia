-- Prove2me | solution 1 for GlobalTheory.LinkLaw.isLawOf_of_match
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:22:57.935489+00:00
-- url     : https://prove2.me/submissions/987bda2d-7bc6-4458-80ed-450c0601d1bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsLawOfOfMatch
import Theorems.Thm_GlobalTheory_LinkLaw_jetMap_coord
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
theorem _root_.solution {G : Over (Sp V)} [GrpObj G] {d : ℕ} (F : Fin d → PS V 2 d)
    (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0) (xT : JetPts G (Fin 1 × Fin d))
    (law : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ xT m =
      (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m (0 : Fin 2)) ≫ xT m) *
        (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m (1 : Fin 2)) ≫ xT m))
    (x : JetSer.Fam G (Fin d)) (hM : Match (oneCol d) xT x) : JetSer.IsLawOf x F := by
  refine ⟨hF, fun n a b y z hy hz => ?_⟩
  have hab : ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → Pt V n d) i j) = 0 := by
    intro i j
    fin_cases i
    · exact hy.1 j
    · exact hz.1 j
  refine ⟨fun j => constantCoeff_ev _ hab _ (hF j), fun m => ?_⟩
  obtain ⟨e, he1, he2⟩ := hM m
  obtain ⟨ψa, ha1, ha2⟩ := hy.2 m
  obtain ⟨ψb, hb1, hb2⟩ := hz.2 m
  obtain ⟨Φ, hΦ, hsub⟩ := exists_subst
    (fun p : Fin 2 × Fin d => (![a, b] : Fin 2 → Pt V n d) p.1 p.2) (fun p => hab p.1 p.2) m
  have key : ∀ i : Fin 2, ∀ j, (Φ.comp ((jetCopy d m i).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m))) (Chart.zR m j) =
      JetSer.toJet m ((![a, b] : Fin 2 → Pt V n d) i j) := by
    intro i j
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1, jetCopy, jetMap_coord]
    exact hΦ (i, j)
  have ea : ψa = Φ.comp ((jetCopy d m 0).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)) :=
    Chart.jet_ext fun j => (ha1 j).trans (key 0 j).symm
  have eb : ψb = Φ.comp ((jetCopy d m 1).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)) :=
    Chart.jet_ext fun j => (hb1 j).trans (key 1 j).symm
  refine ⟨Φ.comp ((jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)).comp
    (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)), fun j => ?_, ?_⟩
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1,
      jetSubstP_coord m (fun p : Fin 1 × Fin d => F p.2) _ (hF _)]
    exact hsub _
  · show y m * z m = _
    rw [← read_match (xT m) (x m) e he2, law m, MonObj.comp_mul,
      read_match (xT m) (x m) e he2, read_match (xT m) (x m) e he2, ← ea, ← eb, ← ha2, ← hb2]
end GlobalTheory.LinkLaw
