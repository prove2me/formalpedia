-- Prove2me | solution 1 for GlobalTheory.orbit_stab_cut_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:37:18.181024+00:00
-- url     : https://prove2.me/submissions/fbb95f52-3c08-45b9-adf3-f20e928f055d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetFixingIffPreservesSubgroupOrbit
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (H : Subgroup (G E Ω)) (y : Ω) :
    ∃ s : Finset Ω, ∀ σ : G E Ω, (∀ x ∈ s, σ x = x) ↔ ∀ τ ∈ H, ∃ τ' ∈ H, σ (τ y) = τ' y := by
  classical
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  set S : Set Ω := {t | ∃ τ ∈ H, τ y = t} with hSdef
  have hS : S.Finite := by
    refine ((minpoly E y).rootSet_finite Ω).subset ?_
    rintro t ⟨τ, -, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [Polynomial.aeval_algEquiv]
    simp [minpoly.aeval]
  set O := hS.toFinset with hOdef
  have hmemO : ∀ t, t ∈ O ↔ ∃ τ ∈ H, τ y = t := fun t => by simp [O, S]
  set P : Polynomial Ω := ∏ t ∈ O, (X - C t) with hP
  refine ⟨(Finset.range (P.natDegree + 1)).image P.coeff, fun σ => ?_⟩
  have key : (∀ x ∈ (Finset.range (P.natDegree + 1)).image P.coeff, σ x = x) ↔
      P.map (σ : Ω →+* Ω) = P := by
    constructor
    · intro h
      ext n
      rw [coeff_map]
      by_cases hn : n ≤ P.natDegree
      · exact h _ (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (Nat.lt_succ_of_le hn), rfl⟩)
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hn)]; simp
    · intro h x hx
      obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hx
      have := congrArg (fun p => p.coeff n) h
      simpa [coeff_map] using this
  have hmap : P.map (σ : Ω →+* Ω) = ∏ t ∈ O, (X - C (σ t)) := by
    simp [hP, Polynomial.map_prod]
  rw [key, hmap]
  constructor
  · intro h τ hτ
    have h0 : (∏ t ∈ O, (X - C (σ t))).eval (σ (τ y)) = 0 := by
      rw [eval_prod]
      exact Finset.prod_eq_zero ((hmemO _).2 ⟨τ, hτ, rfl⟩) (by simp)
    rw [h, hP, eval_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨t, ht, ht0⟩ := h0
    obtain ⟨τ', hτ', rfl⟩ := (hmemO t).1 ht
    refine ⟨τ', hτ', ?_⟩
    simpa [sub_eq_zero] using ht0
  · intro h
    have hinj : Function.Injective (σ : Ω → Ω) := σ.injective
    have hsub : O.image σ ⊆ O := by
      intro u hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨τ, hτ, rfl⟩ := (hmemO t).1 ht
      obtain ⟨τ', hτ', he⟩ := h τ hτ
      exact (hmemO _).2 ⟨τ', hτ', he.symm⟩
    have heq : O.image σ = O :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ hinj])
    calc ∏ t ∈ O, (X - C (σ t)) = ∏ u ∈ O.image σ, (X - C u) :=
          by
          rw [Finset.prod_image (fun a _ b _ hab => hinj hab)]
      _ = P := by rw [heq]
end GlobalTheory
