-- Prove2me | solution 1 for GlobalTheory.Reg.combined_bound_at_trivial_valuations_of_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:49:45.15764+00:00
-- url     : https://prove2.me/submissions/1b0fb204-8ace-47bf-aeec-9e6a28929368

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_CombinedBoundAtTrivialValuationsOfCharts
import Theorems.Thm_GlobalTheory_Reg_TrivBound_nonneg_triv
import Theorems.Thm_GlobalTheory_Reg_TrivBound_comb_triv
import Theorems.Thm_GlobalTheory_Reg_TrivBound_ordQ_mem_trivSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.Reg
namespace GlobalTheory.Reg
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ la : HeightOneSpectrum (𝓞 c.F), (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ) → (∀ (la : HeightOneSpectrum (𝓞 c.F)) (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → (∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, ∃ i, v (ws i) ≠ ⊤) → Formalism.L2.PjFree.NoCommonZero Xo c ws) → ∀ C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c), (∀ a n, C a n ≤ sec Xo c a n) → Formalism.L2.PjFree.RegularityR2Quotient Xo c C := by
  intro E _ _ _ H Dw l Xo c hS hN C hC aL nL aE nE k ws et c' hc' hws het ⟨la, nu, hyp⟩ q
  have hws' : ∀ i, ws i ∈ sec Xo c aL nL := fun i => hC _ _ (hws i)
  have het' : et ∈ sec Xo c aE nE := hC _ _ het
  obtain ⟨S, hF, hQ⟩ := (hS la).2 aL nL k ws hws' (hN la aL nL k ws hws' fun v hv => (hyp v hv).2.1)
  exact ⟨TrivBound.nonneg_triv S hQ het' (fun v hv => (hyp v hv).1) _ (TrivBound.ordQ_mem_trivSet q),
    TrivBound.comb_triv S hQ ws hF hws' het' nu c' hc' (fun v hv => ⟨(hyp v hv).1, (hyp v hv).2.2⟩) _
      (TrivBound.ordQ_mem_trivSet q)⟩
end GlobalTheory.Reg
