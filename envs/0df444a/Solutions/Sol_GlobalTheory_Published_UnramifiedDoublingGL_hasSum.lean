-- Prove2me | solution 1 for GlobalTheory.Published.UnramifiedDoublingGL.hasSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:36:38.988883+00:00
-- url     : https://prove2.me/submissions/53733b9c-2bd3-45a2-88bf-e34309aed6ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Theorems.Thm_GlobalTheory_GLDoubling_sphSection_io_biinv
import Theorems.Thm_GlobalTheory_GLDoubling_sphSection_torusElt
import Theorems.Thm_GlobalTheory_GLDoubling_hasSum_cell
import Theorems.Thm_GlobalTheory_GLDoubling_zonal_biinv
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG
open scoped NNReal Pointwise
open GlobalTheory GlobalTheory.Published
open GlobalTheory.GLDoubling
namespace GlobalTheory.Published
namespace UnramifiedDoublingGL
theorem _root_.solution (H : UnramifiedDoublingGL)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
    (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure] (hμ : μ (KO k (Fin n)) = 1)
    {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k)
    {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V} {α : Fin n → ℂˣ}
    (hπ : HasSatake π α) {ω : GL (Fin n) k → ℂ} (hω : IsZonal π (KO k (Fin n)) ω) :
    ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
      HasSum (fun e : {e : Fin n → ℤ // Antitone e} => (μ.real (cell k (Fin n) ϖ e) : ℂ) *
          ((resCard k : ℂ) ^ (-((n : ℂ) / 2 + s) * ((∑ i, |e.1 i| : ℤ) : ℂ)) * ω (torusElt k (Fin n) ϖ e)))
        (lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) *
          invNormFactor (resCard k) n s) := by
  obtain ⟨s₀, h⟩ := H k n μ hμ V π α hπ ω hω
  refine ⟨s₀, fun s hs => ?_⟩
  have := hasSum_cell μ hϖ (h s hs).1 fun g x hx y hy => by
    rw [sphSection_io_biinv s g hx hy, zonal_biinv hω g hx hy]
  simp only [sphSection_torusElt hϖ, Fintype.card_fin] at this
  rwa [(h s hs).2] at this
end UnramifiedDoublingGL
end GlobalTheory.Published
