-- Prove2me | solution 1 for GlobalTheory.EigenDer.subst_tanPair_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:10:58.474807+00:00
-- url     : https://prove2.me/submissions/3e403831-ab3b-4917-88a2-3e93478354ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HasSubstAddSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsNilpotentOfMemKerJetTruncR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SubstMapAlgebraMap
import Theorems.Thm_GlobalTheory_EigenDer_subst_map_algebraMap
import Theorems.Thm_GlobalTheory_EigenDer_hasSubst_tanPair
import Theorems.Thm_GlobalTheory_EigenDer_ev_pt_pt
import Theorems.Thm_GlobalTheory_Jets_ev_addOf_eps
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.EigenDer
variable {R : Type} [CommRing R]
namespace GlobalTheory.EigenDer
theorem _root_.solution {d : ℕ} (Gl : FGLaw R d) (v : Fin d → R) (f : PS R 1 d) :
    subst (tanPair d v) (ev (n := 2) ![addOf Gl.F (pt R d 0) (pt R d 1)] f) =
      MvPowerSeries.map (algebraMap R (DualNumber R)) f +
        C (DualNumber.eps : DualNumber R) *
          MvPowerSeries.map (algebraMap R (DualNumber R)) (Dof Gl.F v f) := by
  have hF : addOf (n := 2) Gl.F (pt R d 0) (pt R d 1) = Gl.F := funext fun i => ev_pt_pt _
  have ha : HasSubst (fun p : Fin 1 × Fin d => (![Gl.F] : Fin 1 → Pt R 2 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero (by
      rintro ⟨j, i⟩
      fin_cases j
      exact Gl.const i)
  have e : (fun p : Fin 1 × Fin d => subst (tanPair d v) ((![Gl.F] : Fin 1 → Pt R 2 d) p.1 p.2)) =
      fun p : Fin 1 × Fin d => (![addOf (Gl.mapF (algebraMap R (DualNumber R))) (pt (DualNumber R) d 0)
          (fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R))] : Fin 1 → Pt (DualNumber R) 1 d) p.1 p.2 := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j
    exact (subst_map_algebraMap (hasSubst_tanPair d v) (Gl.F i)).symm
  have hc := ha.comp (hasSubst_tanPair d v)
  simp only [substAlgHom_apply] at hc
  rw [← GlobalTheory.Jets.ev_addOf_eps, hF]
  unfold ev
  rw [subst_comp_subst_apply ha (hasSubst_tanPair d v), ← e, subst_map_algebraMap hc]
end GlobalTheory.EigenDer
