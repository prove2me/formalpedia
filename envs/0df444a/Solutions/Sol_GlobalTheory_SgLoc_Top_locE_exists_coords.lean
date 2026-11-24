-- Prove2me | solution 1 for GlobalTheory.SgLoc.Top.locE_exists_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:01:18.951806+00:00
-- url     : https://prove2.me/submissions/7fd7a49e-7e62-48fc-aa6a-96c82932b814

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Theorems.Thm_GlobalTheory_SgLoc_Top_mem_integer_of_isIntegral
import Theorems.Thm_GlobalTheory_SgLoc_Top_locE_nontrivial
import Theorems.Thm_GlobalTheory_SgLoc_Top_locE_exists_pure
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
open ValuativeRel MeasureTheory Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.Top
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.SgLoc.Top
theorem _root_.solution [CharZero F] (L : LocE F E) :
    ∃ (ψ : (F × F) ≃ₗ[F] E) (D : F), D ≠ 0 ∧
      (∀ p : F × F, p.1 ∈ 𝒪[F] → p.2 ∈ 𝒪[F] → ψ p ∈ L.O) ∧
      (∀ p : F × F, ψ p ∈ L.O → 2 * p.1 ∈ 𝒪[F] ∧ 2 * D * p.2 ∈ 𝒪[F]) := by
  obtain ⟨d, D, hD0, hDO, hcj, hdd⟩ := locE_exists_pure L
  have := L.free
  have hnt := locE_nontrivial L
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  let φ : (F × F) →ₗ[F] E := (LinearMap.fst F F F).smulRight (1 : E) + (LinearMap.snd F F F).smulRight d
  have hφ : ∀ p : F × F, φ p = algebraMap F E p.1 + algebraMap F E p.2 * d := by
    intro p
    simp [φ, Algebra.smul_def]
  have hinjA := (algebraMap F E).injective
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hφ] at hp
    have hc : algebraMap F E p.1 - algebraMap F E p.2 * d = 0 := by
      have h' := congrArg L.cj hp
      rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hcj, map_zero] at h'
      rw [← h']; ring
    have hb : algebraMap F E (2 * p.2 * D) = 0 := by
      rw [map_mul, map_mul, ← hdd, map_ofNat]
      linear_combination d * hp - d * hc
    have hb' : p.2 = 0 := by
      have h2 := (map_eq_zero_iff _ hinjA).mp hb
      simpa [hD0] using h2
    have ha : p.1 = 0 := by
      rw [hb', map_zero, zero_mul, add_zero] at hp
      exact (map_eq_zero_iff _ hinjA).mp hp
    exact Prod.ext ha hb'
  have hdim : Module.finrank F (F × F) = Module.finrank F E := by
    rw [Module.finrank_prod, Module.finrank_self, L.rank]
  have hA : ∀ a ∈ 𝒪[F], IsIntegral 𝒪[F] (algebraMap F E a) := by
    intro a ha
    rw [isIntegral_algebraMap_iff hinjA]
    exact (show IsIntegral 𝒪[F] (algebraMap 𝒪[F] F ⟨a, ha⟩) from isIntegral_algebraMap)
  have hdI : IsIntegral 𝒪[F] d := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C ⟨D, hDO⟩, Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
      IsScalarTower.algebraMap_apply 𝒪[F] F E, pow_two, hdd]
    exact sub_self _
  refine ⟨LinearMap.linearEquivOfInjective φ hinj hdim, D, hD0, ?_, ?_⟩
  · intro p h1 h2
    rw [LinearMap.linearEquivOfInjective_apply, hφ, L.O_def]
    exact (hA _ h1).add ((hA _ h2).mul hdI)
  · intro p hp
    rw [LinearMap.linearEquivOfInjective_apply, hφ, L.O_def] at hp
    have hq := hp.map (L.cj.toAlgHom.restrictScalars 𝒪[F])
    have hcx : (L.cj.toAlgHom.restrictScalars 𝒪[F]) (algebraMap F E p.1 + algebraMap F E p.2 * d) =
        algebraMap F E p.1 - algebraMap F E p.2 * d := by
      change L.cj _ = _
      rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hcj]; ring
    rw [hcx] at hq
    constructor
    · have h' := hp.add hq
      rw [show algebraMap F E p.1 + algebraMap F E p.2 * d + (algebraMap F E p.1 - algebraMap F E p.2 * d) =
        algebraMap F E (2 * p.1) by rw [map_mul, map_ofNat]; ring, isIntegral_algebraMap_iff hinjA] at h'
      exact mem_integer_of_isIntegral h'
    · have h' := (hp.sub hq).mul hdI
      rw [show (algebraMap F E p.1 + algebraMap F E p.2 * d - (algebraMap F E p.1 - algebraMap F E p.2 * d)) * d =
        algebraMap F E (2 * D * p.2) by rw [map_mul, map_mul, map_ofNat, ← hdd]; ring, isIntegral_algebraMap_iff hinjA] at h'
      exact mem_integer_of_isIntegral h'
end GlobalTheory.SgLoc.Top
