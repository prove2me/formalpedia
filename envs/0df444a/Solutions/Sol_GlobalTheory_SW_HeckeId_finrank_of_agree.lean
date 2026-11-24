-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.finrank_of_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:27:15.121507+00:00
-- url     : https://prove2.me/submissions/43703107-7961-49e8-baa4-c10999bc5971

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_Hyp_smul_mem
import Theorems.Thm_GlobalTheory_SW_Nbr_finrank_eq


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
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Nbr
omit [IsCMField E]
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution {m : ℕ} {X : Lt E N} (h : Agree m X (stdL E N)) :
    Module.finrank (𝓞 E) X = N := by
  have : IsLocalizedModule (𝓞 E)⁰ X.subtype := by
    obtain ⟨s, hs, -, -, h2⟩ := h
    have := isLocalizedModule_id (𝓞 E)⁰ (Fin N → E) E
    refine ⟨IsLocalizedModule.map_units (LinearMap.id (R := 𝓞 E) (M := Fin N → E)), fun y => ?_,
      fun {x₁ x₂} h => ⟨1, by rw [Subtype.ext h]⟩⟩
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (𝓞 E)⁰ y
    choose c hc using hd
    have h1 : (d : 𝓞 E) • y ∈ stdL E N := by
      have : (d : 𝓞 E) • y = ∑ i, c i • (Pi.single i 1 : Fin N → E) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply, ← hc j, Algebra.smul_def]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hs' : (s : 𝓞 E) ∈ (𝓞 E)⁰ := mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hs.ne')
    exact ⟨(⟨_, h2 _ h1⟩, ⟨s, hs'⟩ * d), mul_smul _ _ _⟩
  rw [← IsLocalizedModule.finrank_eq (𝓞 E)⁰ X.subtype le_rfl,
    ← IsLocalization.finrank_eq E (𝓞 E)⁰ le_rfl]
  simp
end GlobalTheory.SW.HeckeId
