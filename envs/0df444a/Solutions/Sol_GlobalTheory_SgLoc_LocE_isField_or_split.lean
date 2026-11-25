-- Prove2me | solution 1 for GlobalTheory.SgLoc.LocE_isField_or_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:34:38.376175+00:00
-- url     : https://prove2.me/submissions/36dde640-fc44-4aec-9d7c-7ffa7ab4fa4d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralValIntegerIff
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
open GlobalTheory GlobalTheory.SgLoc
namespace GlobalTheory.SgLoc
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) :
    IsField E ∨ ∃ e : E ≃ₐ[F] F × F, ∀ x, e (L.cj x) = (e x).swap := by
  by_cases hE : IsField E
  · exact Or.inl hE
  right
  haveI := L.reduced
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  obtain ⟨x, hx0, hxu⟩ : ∃ x : E, x ≠ 0 ∧ ¬ IsUnit x := by
    by_contra hcon
    push Not at hcon
    exact hE ⟨exists_pair_ne E, mul_comm, fun {a} ha => (hcon a ha).exists_right_inv⟩
  obtain ⟨n, hn⟩ := (L.cj_fix (x * L.cj x)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  obtain ⟨t, ht⟩ := (L.cj_fix (x + L.cj x)).1 (by rw [map_add, L.cj_cj, add_comm])
  have hn0 : n = 0 := by
    by_contra h
    apply hxu
    have : IsUnit (x * L.cj x) := hn ▸ (IsUnit.mk0 n h).map (algebraMap F E)
    exact isUnit_of_mul_isUnit_left this
  have hN : x * L.cj x = 0 := by rw [← hn, hn0, map_zero]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, map_zero] at ht
    apply hx0
    apply IsNilpotent.eq_zero
    exact ⟨2, by linear_combination (-x) * ht - hN⟩
  set p : E := t⁻¹ • x with hp
  have hq : L.cj p = t⁻¹ • L.cj x := by rw [hp, map_smul]
  have h1 : p + L.cj p = 1 := by
    rw [hq, hp, ← smul_add, ← ht, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ ht0, map_one]
  have h0 : p * L.cj p = 0 := by
    rw [hq, hp, smul_mul_smul_comm, hN, smul_zero]
  have hp0 : p ≠ 0 := smul_ne_zero (inv_ne_zero ht0) hx0
  have hq0 : L.cj p ≠ 0 := by simpa using hp0
  have hpp : p * p = p := by linear_combination p * h1 - h0
  have hqq : L.cj p * L.cj p = L.cj p := by linear_combination L.cj p * h1 - h0
  clear_value p
  let φ : F × F →ₐ[F] E := idemPairHom p (L.cj p) h1 h0
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    change a • p + b • L.cj p = 0 at hab
    have ha : a • p = 0 := by
      have := congrArg (p * ·) hab
      simpa [mul_add, hpp, h0] using this
    have hb : b • L.cj p = 0 := by rwa [ha, zero_add] at hab
    have ha' : a = 0 := (smul_eq_zero.1 ha).resolve_right hp0
    have hb' : b = 0 := (smul_eq_zero.1 hb).resolve_right hq0
    simp [ha', hb']
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap)
      (by rw [L.rank]; simp)).1 hinj
  refine ⟨(AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm, fun z => ?_⟩
  obtain ⟨y, rfl⟩ := (AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).surjective z
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_eq]
  change L.cj (y.1 • p + y.2 • L.cj p) = y.2 • p + y.1 • L.cj p
  rw [map_add, map_smul, map_smul, L.cj_cj, add_comm]
end GlobalTheory.SgLoc
