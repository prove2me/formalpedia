-- Prove2me | solution 1 for GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:16.285154+00:00
-- url     : https://prove2.me/submissions/1ebbccbc-693a-4c39-ae7c-eb69c0d2e449

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Theorems.Thm_GlobalTheory_UnramOrder_exists_double_root
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_exists_trace
import Theorems.Thm_GlobalTheory_UnramOrder_exists_norm
import Theorems.Thm_GlobalTheory_UnramOrder_exists_generator
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnramOrder
open IsLocalRing Polynomial
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F]
namespace GlobalTheory.UnramOrder
theorem _root_.solution [CharZero F] (L : LocE F E) :
    ∃ ω ∈ L.O, ∃ e ∈ L.O, (ω - L.cj ω) * e = 1 := by
  obtain ⟨ω, hω, hω0, hgen⟩ := exists_generator L
  obtain ⟨t, ht⟩ := exists_trace L hω
  obtain ⟨n, hn⟩ := exists_norm L hω
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (algebraMap_mem_iff L a).2 a.2
  have hD : (ω - L.cj ω) ^ 2 = algebraMap F E (t ^ 2 - 4 * n : 𝒪[F]) := by
    push_cast
    have h4 : ((4 : 𝒪[F]) : F) = 4 := rfl
    simp only [h4, map_ofNat, ← ht, ← hn]
    ring
  by_cases hu : IsUnit (t ^ 2 - 4 * n)
  · obtain ⟨v, hv⟩ := hu.exists_right_inv
    refine ⟨ω, hω, (ω - L.cj ω) * algebraMap F E v,
      L.O.mul_mem (L.O.sub_mem hω (cj_mem L hω)) (hint v), ?_⟩
    rw [← mul_assoc, ← sq, hD, ← map_mul, ← Subring.coe_mul, hv]
    simp
  exfalso
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hm := hϖ.maximalIdeal_eq
  obtain ⟨a, ha1, ha2⟩ := exists_double_root (t := residue 𝒪[F] t) (n := residue 𝒪[F] n) (by
    have := (residue_eq_zero_iff _).2 (show t ^ 2 - 4 * n ∈ maximalIdeal 𝒪[F] from hu)
    simpa only [map_sub, map_mul, map_pow, map_ofNat] using this)
  obtain ⟨a, rfl⟩ := residue_surjective a
  have h1 : ϖ ∣ t - 2 * a := by
    rw [← Ideal.mem_span_singleton, ← hm, ← residue_eq_zero_iff]
    simp only [map_sub, map_mul, map_ofNat, ha1, sub_self]
  have h2 : ϖ ∣ n - a ^ 2 := by
    rw [← Ideal.mem_span_singleton, ← hm, ← residue_eq_zero_iff]
    simp only [map_sub, map_pow, ha2, sub_self]
  obtain ⟨u, hu1⟩ := h1
  obtain ⟨v, hv1⟩ := h2
  have hu2 := congrArg (algebraMap 𝒪[F] E) hu1
  have hv2 := congrArg (algebraMap 𝒪[F] E) hv1
  simp only [map_sub, map_mul, map_pow, map_ofNat] at hu2 hv2
  have hal : ∀ a : 𝒪[F], algebraMap 𝒪[F] E a = algebraMap F E a := fun _ => rfl
  simp only [hal, ← ht, ← hn] at hu2 hv2
  have hmem := L.unram ϖ hϖ (ω - algebraMap F E a) (L.O.sub_mem hω (hint a)) (by
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨algebraMap F E u * ω - algebraMap F E v,
      L.O.sub_mem (L.O.mul_mem (hint u) hω) (hint v)⟩, ?_⟩
    show (algebraMap F E u * ω - algebraMap F E v) * algebraMap F E ϖ = _
    linear_combination (-ω) * hu2 + hv2)
  obtain ⟨⟨y, hy⟩, hy'⟩ := Submodule.mem_span_singleton.1 hmem
  have hy1 : y * algebraMap F E ϖ = ω - algebraMap F E a := hy'
  have hy2 := congrArg L.cj hy1
  simp only [map_mul, map_sub, AlgEquiv.commutes] at hy2
  obtain ⟨b, hb⟩ := hgen y hy
  have h3 : algebraMap F E (1 - ϖ * b : 𝒪[F]) * (ω - L.cj ω) = 0 := by
    push_cast
    linear_combination -hy1 + hy2 + algebraMap F E ϖ * hb
  have h4 : ((1 - ϖ * b : 𝒪[F]) : F) ≠ 0 := by
    intro h
    have h5 : 1 - ϖ * b = 0 := Subtype.ext h
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one b (sub_eq_zero.1 h5).symm)
  exact hω0 (((IsUnit.mk0 _ h4).map (algebraMap F E)).mul_right_eq_zero.1 h3)
end GlobalTheory.UnramOrder
