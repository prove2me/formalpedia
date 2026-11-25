-- Prove2me | solution 1 for GlobalTheory.WachFree.free_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:00.773347+00:00
-- url     : https://prove2.me/submissions/0e1d07ea-a8aa-4044-b3af-0b55f2c745e1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemXSmulOfProjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
open GlobalTheory GlobalTheory.WachFree
namespace GlobalTheory.WachFree
theorem _root_.solution {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (c : O) (hc : c ≠ 0) (hc' : ¬ IsUnit c)
    (hX : IsSMulRegular M (X : O⟦X⟧))
    (h : ∀ x y : M, (C c : O⟦X⟧) • x = (X : O⟦X⟧) • y → ∃ z : M, x = (X : O⟦X⟧) • z) :
    Module.Free O⟦X⟧ M := by
  haveI : Module.FinitePresentation O⟦X⟧ M := Module.finitePresentation_of_finite _ _
  have hker : Ideal.span {(X : O⟦X⟧)} = RingHom.ker (constantCoeff (R := O)) := by
    ext f
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, X_dvd_iff]
  let e : (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) ≃+* O :=
    (Ideal.quotEquivOfEq hker).trans
      (RingHom.quotientKerEquivOfSurjective (f := constantCoeff (R := O))
        fun a => ⟨C a, by simp⟩)
  haveI : IsDomain (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) := e.toMulEquiv.isDomain
  haveI : IsPrincipalIdealRing (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) :=
    IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective
  have hpow : ∀ (k : ℕ) (x y : M), (C (c ^ k) : O⟦X⟧) • x = (X : O⟦X⟧) • y →
      ∃ z : M, x = (X : O⟦X⟧) • z := by
    intro k
    induction k with
    | zero => intro x y hxy; exact ⟨y, by simpa using hxy⟩
    | succ k ih =>
      intro x y hxy
      rw [pow_succ, map_mul, mul_smul] at hxy
      obtain ⟨z, hz⟩ := ih _ _ hxy
      exact h _ _ hz
  have hdvd : ∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ c ^ k := by
    intro a ha
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    obtain ⟨j, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    have hj : j ≠ 0 := by
      rintro rfl
      exact hc' (by simp)
    refine ⟨k, ?_⟩
    rw [Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd (Dvd.dvd.mul_left (dvd_pow_self _ hj) _) _
  haveI := Module.Finite.of_restrictScalars_finite O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)})
    (QuotSMulTop (X : O⟦X⟧) M)
  haveI : Module.IsTorsionFree (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) (QuotSMulTop (X : O⟦X⟧) M) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    by_cases hr : constantCoeff r = 0
    · left
      rw [Ideal.Quotient.eq_zero_iff_mem, hker]
      exact hr
    right
    have h1 : (Submodule.Quotient.mk (r • m) : QuotSMulTop (X : O⟦X⟧) M) = 0 := hrm
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at h1 ⊢
    obtain ⟨y, -, hy⟩ := h1
    obtain ⟨k, b, hb⟩ := hdvd _ hr
    obtain ⟨d, hd⟩ : (X : O⟦X⟧) ∣ C (c ^ k) - C b * r := by
      rw [X_dvd_iff]
      simp [hb, mul_comm]
    obtain ⟨z, hz⟩ := hpow k m (d • m + (C b : O⟦X⟧) • y) (by
      rw [smul_add, smul_comm (X : O⟦X⟧) (C b : O⟦X⟧) y, hy, smul_smul, smul_smul, ← hd, ← add_smul,
        sub_add_cancel])
    exact ⟨z, trivial, hz.symm⟩
  refine (Module.free_quotSMulTop_iff_free O⟦X⟧ M ?_ hX).mp inferInstance
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, isUnit_iff_constantCoeff]
  simp
end GlobalTheory.WachFree
