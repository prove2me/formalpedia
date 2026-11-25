-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.KAK.irreducible_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:55:13.673584+00:00
-- url     : https://prove2.me/submissions/f6fa67fc-96ce-4bda-bad7-d3594cd334f6

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartanDecompositionGeneralLinear
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.KAK
variable {F : Type} [Field F]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.CompanionTheory.QL.KAK
theorem _root_.solution {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ} (h : LF 𝒪[F] ϖ nrm q)
    (hϖ : ϖ ∈ 𝒪[F]) : Irreducible (⟨ϖ, hϖ⟩ : 𝒪[F]) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  ext x
  have hu : IsUnit x ↔ ValuativeRel.valuation F (x : F) = 1 :=
    (Valuation.integer.integers (ValuativeRel.valuation F)).isUnit_iff_valuation_eq_one
  have hle : ValuativeRel.valuation F (x : F) ≤ 1 := x.2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu, Ideal.mem_span_singleton']
  constructor
  · intro hx
    obtain ⟨o, ho, e⟩ := (h.lt_one (x : F)).1 (lt_of_le_of_ne hle hx)
    exact ⟨⟨o, ho⟩, Subtype.ext (by simp [e, mul_comm])⟩
  · rintro ⟨a, rfl⟩
    exact ((h.lt_one _).2 ⟨a, a.2, by simp [mul_comm]⟩).ne
end GlobalTheory.CompanionTheory.QL.KAK
