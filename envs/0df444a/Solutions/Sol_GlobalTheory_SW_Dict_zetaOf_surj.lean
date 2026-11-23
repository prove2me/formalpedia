-- Prove2me | solution 1 for GlobalTheory.SW.Dict.zetaOf_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:41.643047+00:00
-- url     : https://prove2.me/submissions/92265ffb-7d4e-4793-a2c8-c7b1a719a1a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Theorems.Thm_GlobalTheory_SW_Dict_exists_emb_comb
import Theorems.Thm_GlobalTheory_SW_Dict_sum_type

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Dict
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable (Ψ : Finset (E →+* ℂ))
variable {Ψ}
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable (Ψ : Finset (E →+* ℂ))
variable {Ψ}
namespace GlobalTheory.SW.Dict
namespace _root_.GlobalTheory.SW.Dict
theorem _root_.solution (hΨ : _root_.GlobalTheory.SW.IsType Ψ)
    (ζ : Fin n → _root_.GlobalTheory.SW.QI E N → ℂ) :
    ∃ z z' : _root_.GlobalTheory.SW.CM Ψ n N, _root_.GlobalTheory.SW.zetaOf Ψ z z' = ζ := by
  choose w hw using fun (k : Fin n) (a : Fin N) =>
    _root_.GlobalTheory.SW.Dict.exists_emb_comb (E := E) (fun j => ζ k (a, j))
  refine ⟨fun τ => Matrix.of fun k a => w k a τ,
    fun τ => Matrix.of fun k a => w k a (ComplexEmbedding.conjugate τ.1), ?_⟩
  funext k p
  obtain ⟨a, j⟩ := p
  rw [← hw k a j, _root_.GlobalTheory.SW.Dict.sum_type hΨ]
  simp only [_root_.GlobalTheory.SW.zetaOf, Matrix.of_apply, ComplexEmbedding.conjugate_coe_eq]
  exact Finset.sum_congr rfl fun _ _ => by ring
end _root_.GlobalTheory.SW.Dict
end GlobalTheory.SW.Dict
