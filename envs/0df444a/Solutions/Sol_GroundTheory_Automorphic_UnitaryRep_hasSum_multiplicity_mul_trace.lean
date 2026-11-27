-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.hasSum_multiplicity_mul_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:44:11.944646+00:00
-- url     : https://prove2.me/submissions/089ca07b-bf13-42dc-b158-4777d27a2285

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_Equiv_trace_integrated
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isTraceClass_integrated_restrict
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_hasSum_trace_integrated_restrict
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace InnerProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (π : UnitaryRep G H) (μ : Measure G) (f : G →₁[μ] ℂ)
variable {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))
variable {π μ f}
variable (hsum : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ)
include hsum
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution (hT : IsTraceClass (π.integrated μ f))
    (hfin : ∀ j, {k : J | (π.restrict (V k) (hinv k)).IsEquivalent
      (π.restrict (V j) (hinv j))}.Finite) :
    HasSum (fun c : Quotient (restrictSetoid π hinv) => (multiplicity π hinv c : ℂ) *
        trace ((π.restrict (V c.out) (hinv c.out)).integrated μ f))
      (trace (π.integrated μ f)) := by
  set S := restrictSetoid π hinv
  have h0 := hasSum_trace_integrated_restrict hinv hsum hT
  let e := Equiv.sigmaFiberEquiv (Quotient.mk S)
  have h1 : HasSum (fun a : Σ c : Quotient S, {j : J // Quotient.mk S j = c} =>
      trace ((π.restrict (V (e a)) (hinv (e a))).integrated μ f)) (trace (π.integrated μ f)) :=
    (e.hasSum_iff).2 h0
  refine h1.sigma fun c => ?_
  have hfc : Set.Finite {j : J | Quotient.mk S j = c} := by
    refine (hfin c.out).subset fun j hj => ?_
    have : Quotient.mk S j = Quotient.mk S c.out := by rw [show Quotient.mk S j = c from hj]; exact c.out_eq.symm
    exact Quotient.exact this
  have : Finite {j : J // Quotient.mk S j = c} := hfc.to_subtype
  have : Fintype {j : J // Quotient.mk S j = c} := Fintype.ofFinite _
  have hconst : ∀ a : {j : J // Quotient.mk S j = c},
      trace ((π.restrict (V (e ⟨c, a⟩)) (hinv (e ⟨c, a⟩))).integrated μ f) =
        trace ((π.restrict (V c.out) (hinv c.out)).integrated μ f) := by
    intro a
    have hja : Quotient.mk S a.1 = Quotient.mk S c.out := by rw [a.2]; exact c.out_eq.symm
    obtain ⟨eq⟩ := (Quotient.exact hja : S a.1 c.out)
    exact (eq.trace_integrated f (isTraceClass_integrated_restrict hinv hT a.1)).symm
  have h2 := hasSum_fintype (fun a : {j : J // Quotient.mk S j = c} =>
    trace ((π.restrict (V (e ⟨c, a⟩)) (hinv (e ⟨c, a⟩))).integrated μ f))
  convert h2 using 1
  rw [Finset.sum_congr rfl fun a _ => hconst a, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    multiplicity, Nat.card_eq_fintype_card]
end GroundTheory.Automorphic.UnitaryRep
