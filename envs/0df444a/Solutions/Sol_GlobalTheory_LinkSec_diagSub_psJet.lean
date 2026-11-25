-- Prove2me | solution 1 for GlobalTheory.LinkSec.diagSub_psJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:39:05.308773+00:00
-- url     : https://prove2.me/submissions/e3db6e62-8927-440b-b653-ac6840f8ece1

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
import Theorems.Thm_GlobalTheory_LinkSec_diagSub_zero
import Theorems.Thm_GlobalTheory_LinkSec_diagSub_one
import Theorems.Thm_GlobalTheory_JetSer_toJet_X
import Theorems.Thm_GlobalTheory_LinkLaw_exists_subst
import Theorems.Thm_GlobalTheory_LinkLaw_jetMap_coord
import Theorems.Thm_GlobalTheory_LinkLaw_jetSubstP_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext


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
theorem _root_.solution {d : ℕ} (m : ℕ) (φ : Pt V 1 d) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (ε : PS V 2 d) :
    diagSub m φ (psJet m ε) = psJet m (ev (n := 1) ![pt V (n := 1) d 0, comp1 φ (pt V (n := 1) d 0)] ε) := by
  have c : comp1 φ (pt V (n := 1) d 0) = φ := funext fun i => ev_pt_one _
  rw [c]
  have h0 : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff
      ((![pt V (n := 1) d 0, φ] : Fin 2 → Pt V 1 d) p.1 p.2) = 0 := by
    rintro ⟨a, i⟩
    fin_cases a
    · simp [pt]
    · exact hφ i
  obtain ⟨Φ, hΦ, hsub⟩ := LinkLaw.exists_subst
    (fun p : Fin 2 × Fin d => (![pt V (n := 1) d 0, φ] : Fin 2 → Pt V 1 d) p.1 p.2) h0 m
  have e : diagSub m φ = Φ := by
    refine Chart.jet_ext (R := V) fun p => Eq.trans ?_ (hΦ p).symm
    obtain ⟨a, i⟩ := p
    fin_cases a
    · refine Eq.trans ?_ (JetSer.toJet_X m ((0 : Fin 1), i)).symm
      have := AlgHom.congr_fun (diagSub_zero m φ) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
      rw [AlgHom.comp_apply, jetCopy, LinkLaw.jetMap_coord] at this
      exact this
    · have := AlgHom.congr_fun (diagSub_one m φ) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
      rw [AlgHom.comp_apply, jetCopy, LinkLaw.jetMap_coord,
        LinkLaw.jetSubstP_coord m (fun p : Fin 1 × Fin d => φ p.2) _ (hφ _)] at this
      exact this
  rw [e, ← toJet_eq, ← toJet_eq]
  exact hsub ε
end GlobalTheory.LinkSec
