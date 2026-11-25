-- Prove2me | solution 1 for GlobalTheory.SplitPlaceExt.algHom_eq_or_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:11:23.921996+00:00
-- url     : https://prove2.me/submissions/127f3e2c-cf71-44cc-8624-964bec2836f5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgHomEqOrConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
noncomputable section
open GlobalTheory GlobalTheory.SplitPlaceExt
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
local notation3 "cc" => IsCMField.complexConj L
namespace GlobalTheory.SplitPlaceExt
theorem _root_.solution {K : Type} [Field K] [Algebra L⁺ K] (i j : L →ₐ[L⁺] K) :
    j = i ∨ ∀ x, j x = i (cc x) := by
  obtain ⟨θ, hθ⟩ : ∃ θ : L, cc θ ≠ θ := by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one L (AlgEquiv.ext h)
  obtain ⟨δ, hδ⟩ : ∃ δ : L, δ = θ - cc θ := ⟨_, rfl⟩
  have hcδ : cc δ = -δ := by rw [hδ, map_sub, IsCMField.complexConj_apply_apply, neg_sub]
  have hδ0 : δ ≠ 0 := by rw [hδ]; exact sub_ne_zero.mpr (Ne.symm hθ)
  have hfix : ∀ y : L, cc y = y → j y = i y := by
    intro y hy
    have e : y = algebraMap L⁺ L ⟨y, (IsCMField.complexConj_eq_self_iff (K := L) _).mp hy⟩ := rfl
    rw [e, AlgHom.commutes, AlgHom.commutes]
  have hdec : ∀ x : L, ∃ a b : L, cc a = a ∧ cc b = b ∧ x = a + b * δ := by
    intro x
    refine ⟨(x + cc x) / 2, (x - cc x) / (2 * δ), ?_, ?_, ?_⟩
    · rw [map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat, add_comm]
    · rw [map_div₀, map_sub, IsCMField.complexConj_apply_apply, map_mul, map_ofNat, hcδ]
      field_simp
      ring
    · field_simp
      ring
  have hsq : j δ * j δ = i δ * i δ := by
    rw [← map_mul, ← map_mul]
    apply hfix
    rw [map_mul, hcδ, neg_mul_neg]
  rcases mul_self_eq_mul_self_iff.mp hsq with h | h
  · left
    ext x
    obtain ⟨a, b, ha, hb, rfl⟩ := hdec x
    rw [map_add, map_add, map_mul, map_mul, hfix a ha, hfix b hb, h]
  · right
    intro x
    obtain ⟨a, b, ha, hb, rfl⟩ := hdec x
    rw [map_add, map_add, map_mul, map_mul, hfix a ha, hfix b hb, h, ha, hb, hcδ, map_add, map_mul,
      map_neg]
end GlobalTheory.SplitPlaceExt
