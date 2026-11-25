-- Prove2me | solution 1 for GlobalTheory.LeadJets.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:04:25.633391+00:00
-- url     : https://prove2.me/submissions/57df45e0-a11e-42dc-a30a-3eb101c045ab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_TaylorExpansionLocalCoordinates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NmatZeroMemBor
import Theorems.Thm_GlobalTheory_LeadJets_jets
import Theorems.Thm_GlobalTheory_LeadJets_cpt_zero
import Theorems.Thm_GlobalTheory_LeadJets_rmul_nmat_zero
import Theorems.Thm_GlobalTheory_LeadJets_nmat_zero_mem_Bor
import Theorems.Thm_GlobalTheory_LeadJets_lact_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_hol_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_isOpen_OmF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open Filter Asymptotics
open GlobalTheory GlobalTheory.LeadJets
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LeadJets
theorem _root_.solution : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (T a δ : ℕ), a ≤ T + 1 →
    ∀ (t : Fin δ → Frame X.Ψ r → ℂ), (∀ k, X.IsSec G (t k)) → IsValBasisM X Fl.xs t →
    ∀ f, X.IsSec (G + T • Xa.L) f →
    ∃ cc : (Fin (nd X) → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z : V (nd X) => f (cpt X (Fl.xs j) z) - leadM X Fl.s Fl.w0 t T a cc (cpt X (Fl.xs j) z))
        =O[𝓝 0] fun z => ‖z‖ ^ a := by
  intro r X Xa Fl G T a δ ha t ht hb f hf
  have hs0 : ∀ j k, Fl.s k (Fl.xs j) = 0 := fun j =>
    (Fl.S_eq _ (Fl.xs_mem j)).2 ⟨j, 1, one_mem _, nmat X 0, nmat_zero_mem_Bor X, by
      rw [rmul_nmat_zero, lact_one]⟩
  exact jets (U := fun j => OmF X (Fl.xs j)) (f := fun j z => f (cpt X (Fl.xs j) z))
    (w := fun j z => Fl.w0 (cpt X (Fl.xs j) z)) (s := fun j z k => Fl.s k (cpt X (Fl.xs j) z))
    (t := fun j z k => t k (cpt X (Fl.xs j) z)) ha
    (fun j => OntoB.isOpen_OmF X _)
    (fun j => by
      show cpt X (Fl.xs j) 0 ∈ X.dom
      rw [cpt_zero]; exact Fl.xs_mem j)
    (fun j => OntoB.hol_comp X _ hf.1)
    (fun j => OntoB.hol_comp X _ Fl.weightForm_vanishes.1.1.1.1)
    (fun j k => OntoB.hol_comp X _ (Fl.s_van k).1.1.1.1)
    (fun j k => OntoB.hol_comp X _ (ht k).1)
    (fun j => by simpa only [cpt_zero] using Fl.w0_ne j)
    (fun j k => by simpa only [cpt_zero] using hs0 j k)
    Fl.coord
    (fun v => by simpa only [cpt_zero] using hb.1 v)
end GlobalTheory.LeadJets
