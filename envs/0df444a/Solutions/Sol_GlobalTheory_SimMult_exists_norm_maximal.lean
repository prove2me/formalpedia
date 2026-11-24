-- Prove2me | solution 1 for GlobalTheory.SimMult.exists_norm_maximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:14:51.783853+00:00
-- url     : https://prove2.me/submissions/9eb287db-9e37-480a-bdfe-4dbccd103c83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSimTrivialOfMult
import Theorems.Thm_GlobalTheory_SimMult_exists_norm_finiteField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimMult
variable {O : Type*} [CommRing O] (σ : O →+* O)
namespace GlobalTheory.SimMult
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (P : Ideal O) [hP : P.IsMaximal]
    [Finite (O ⧸ P)] (hne : ∃ t, σ t - t ∉ P) (ν : ℤ) (hν : (ν : O) ∉ P) :
    ∃ c, c * σ c - ν ∈ P := by
  by_cases h : P ≤ P.comap σ
  · let := Ideal.Quotient.field P
    let τ : O ⧸ P →+* O ⧸ P := Ideal.quotientMap P σ h
    have hτ : ∀ x, τ (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (σ x) := fun x => rfl
    obtain ⟨c, hc⟩ := exists_norm_finiteField τ (by
        intro x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [hτ, hτ, hσ]) (by
        obtain ⟨t, ht⟩ := hne
        refine ⟨Ideal.Quotient.mk P t, fun h => ht ?_⟩
        rw [hτ] at h
        exact Ideal.Quotient.eq.1 h) ν (by
        intro h
        apply hν
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast]
        exact h)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨c, Ideal.Quotient.eq.1 ?_⟩
    rw [map_mul, map_intCast, ← hτ]
    exact hc
  · obtain ⟨x, hx, hx'⟩ := SetLike.not_le_iff_exists.1 h
    obtain ⟨y, e, he, hy⟩ := hP.exists_inv (x := σ x) hx'
    refine ⟨e + ν * (y * σ x), ?_⟩
    have hy' := congrArg σ hy
    rw [map_add, map_mul, hσ, map_one] at hy'
    have : (e + ν * (y * σ x)) * σ (e + ν * (y * σ x)) - ν
        = ((1 - ν) * σ (e + ν * (y * σ x))) * e + (ν * (ν - 1) * σ y) * x := by
      simp only [map_add, map_mul, map_intCast, hσ]
      linear_combination (ν * (σ e + ν * (σ y * x))) * hy + ν * hy'
    rw [this]
    exact P.add_mem (P.mul_mem_left _ he) (P.mul_mem_left _ hx)
end GlobalTheory.SimMult
