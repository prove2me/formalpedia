-- Prove2me | solution 1 for GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:43:54.137537+00:00
-- url     : https://prove2.me/submissions/35b0583d-6e6e-47cb-a25e-9699b340de24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsEqAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EventuallyExistsQuaternionNormOneReEq
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_SelfDualGenus_finite_residueField_adicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_isAdicComplete_adicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_isUnit_algebraMap_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
namespace GlobalTheory.QSA.IntRep
open NumberField IsDedekindDomain in
open scoped Quaternion Topology in
private lemma coe_adicCompletionIntegers_inv {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {x y : v.adicCompletionIntegers F} (h : x * y = 1) :
    (y : v.adicCompletion F) = (x : v.adicCompletion F)⁻¹ := by
  refine (eq_inv_of_mul_eq_one_right ?_)
  exact_mod_cast h
open IsDedekindDomain NumberField IsLocalRing in
open Polynomial in
private lemma exists_root_monic_quadratic_henselian {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (IsLocalRing.maximalIdeal R)] (p q a₀ : R)
    (h : a₀ ^ 2 + p * a₀ + q ∈ IsLocalRing.maximalIdeal R) (hu : IsUnit (2 * a₀ + p)) :
    ∃ a : R, a ^ 2 + p * a + q = 0 ∧ a - a₀ ∈ IsLocalRing.maximalIdeal R := by
  obtain ⟨a, ha, haa⟩ := HenselianRing.is_henselian (X ^ 2 + (C p * X + C q))
    (monic_X_pow_add degree_linear_lt) a₀
    (by simpa only [eval_add, eval_pow, eval_X, eval_mul, eval_C, add_assoc] using h)
    (by
      have : eval a₀ (derivative (X ^ 2 + (C p * X + C q))) = 2 * a₀ + p := by
        simp [derivative_X_pow]; ring
      rw [this]; exact hu.map _)
  exact ⟨a, by simpa only [IsRoot, eval_add, eval_pow, eval_X, eval_mul, eval_C, add_assoc] using ha,
    haa⟩
open IsDedekindDomain NumberField IsLocalRing in
open Polynomial in
private lemma exists_binary_form_eq_unit {O : Type*} [CommRing O] [IsLocalRing O]
    [HenselianRing O (maximalIdeal O)] [Finite (ResidueField O)] (t n u : O)
    (hD : IsUnit (t ^ 2 - 4 * n)) (hu : IsUnit u) :
    ∃ r s : O, r ^ 2 + t * r * s + n * s ^ 2 = u := by
  have hu' := (residue_ne_zero_iff_isUnit u).2 hu
  by_cases h2 : IsUnit (2 : O)
  · have h2k : (2 : ResidueField O) ≠ 0 := by
      have := (residue_ne_zero_iff_isUnit (2 : O)).2 h2
      rwa [map_ofNat] at this
    set i : O := ↑h2.unit⁻¹ with hi_def
    have hi : 2 * i = 1 := h2.mul_val_inv
    set e : O := (t ^ 2 - 4 * n) * i ^ 2 with he_def
    have he : IsUnit e := hD.mul ((h2.unit⁻¹).isUnit.pow 2)
    have hek := (residue_ne_zero_iff_isUnit e).2 he
    haveI := Fintype.ofFinite (ResidueField O)
    have hchar : ringChar (ResidueField O) ≠ 2 := by
      intro h
      haveI := ringChar.eq_iff.mp h
      exact h2k (by simpa using CharP.cast_eq_zero (ResidueField O) 2)
    obtain ⟨α, σ, hασ⟩ := FiniteField.exists_root_sum_quadratic
      (f := X ^ 2 - C (residue O u)) (g := C (-(residue O e)) * X ^ 2)
      (degree_X_pow_sub_C (by norm_num) _) (degree_C_mul_X_pow 2 (neg_ne_zero.2 hek))
      (FiniteField.odd_card_of_char_ne_two hchar)
    obtain ⟨x₀, rfl⟩ := residue_surjective α
    obtain ⟨s₀, rfl⟩ := residue_surjective σ
    simp only [eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hασ
    have hm : x₀ ^ 2 - e * s₀ ^ 2 - u ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff]
      simp only [map_sub, map_mul, map_pow]
      linear_combination hασ
    have key : ∃ X s : O, X ^ 2 - e * s ^ 2 = u := by
      by_cases hx : IsUnit x₀
      · obtain ⟨X, hX, -⟩ := exists_root_monic_quadratic_henselian 0 (-(e * s₀ ^ 2 + u)) x₀
          (by convert hm using 1; ring) (by simpa using h2.mul hx)
        exact ⟨X, s₀, by linear_combination hX⟩
      · have hs : IsUnit s₀ := by
          by_contra hs
          rw [← residue_ne_zero_iff_isUnit, not_not] at hx hs
          apply hu'
          rw [hx, hs] at hασ
          linear_combination -hασ
        set E : O := ↑he.unit⁻¹ with hE_def
        have hE : e * E = 1 := he.mul_val_inv
        obtain ⟨s, hs', -⟩ := exists_root_monic_quadratic_henselian 0 (-(x₀ ^ 2 - u) * E) s₀
          (by
            have : s₀ ^ 2 + 0 * s₀ + -(x₀ ^ 2 - u) * E = -E * (x₀ ^ 2 - e * s₀ ^ 2 - u) := by
              linear_combination (-s₀ ^ 2) * hE
            rw [this]; exact Ideal.mul_mem_left _ _ hm)
          (by simpa using h2.mul hs)
        exact ⟨x₀, s, by linear_combination (-e) * hs' - (x₀ ^ 2 - u) * hE⟩
    obtain ⟨X, s, hXs⟩ := key
    exact ⟨X - t * s * i, s, by
      linear_combination hXs + (t ^ 2 * s ^ 2 * i - n * s ^ 2 * (1 + 2 * i) - t * X * s) * hi⟩
  · have h2k : (2 : ResidueField O) = 0 := by
      by_contra h
      exact h2 ((residue_ne_zero_iff_isUnit _).1 (by rwa [map_ofNat]))
    have h4 : (4 : ResidueField O) = 0 := by
      rw [show (4 : ResidueField O) = 2 * 2 by norm_num, h2k, zero_mul]
    have ht : IsUnit t := by
      rw [← residue_ne_zero_iff_isUnit] at hD ⊢
      intro h
      apply hD
      rw [map_sub, map_mul, map_pow, h, map_ofNat, h4]
      ring
    have hchar : ringChar (ResidueField O) = 2 :=
      CharP.ringChar_of_prime_eq_zero Nat.prime_two (by simpa using h2k)
    obtain ⟨ρ, hρ⟩ := FiniteField.isSquare_of_char_two hchar (residue O u)
    obtain ⟨r₀, rfl⟩ := residue_surjective ρ
    have hr₀ : IsUnit r₀ := by
      rw [← residue_ne_zero_iff_isUnit]
      rintro h
      rw [h, mul_zero] at hρ
      exact hu' hρ
    set c : O := r₀ ^ 2 - u with hc_def
    have hc : c ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff, hc_def, map_sub, map_pow, hρ]
      ring
    have hb : IsUnit (t * r₀) := ht.mul hr₀
    set β : O := ↑hb.unit⁻¹ with hβ_def
    have hβ : t * r₀ * β = 1 := hb.mul_val_inv
    obtain ⟨w, hw, hw1⟩ := exists_root_monic_quadratic_henselian (-1) (n * β ^ 2 * c) 1
      (by
        have : (1 : O) ^ 2 + -1 * 1 + n * β ^ 2 * c = (n * β ^ 2) * c := by ring
        rw [this]; exact Ideal.mul_mem_left _ _ hc)
      (by norm_num)
    have hwu : IsUnit w := by
      rw [← residue_ne_zero_iff_isUnit]
      have := (residue_eq_zero_iff _).2 hw1
      rw [map_sub, map_one, sub_eq_zero] at this
      rw [this]; exact one_ne_zero
    set ω : O := ↑hwu.unit⁻¹ with hω_def
    have hω : w * ω = 1 := hwu.mul_val_inv
    exact ⟨r₀, -c * β * ω, by
      linear_combination (-c * ω) * hβ + (c * ω ^ 2) * hw + (-c * (w * ω + 1) + c * ω) * hω⟩
end GlobalTheory.QSA.IntRep
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open GlobalTheory GlobalTheory.QSA GlobalTheory.QSA.IntRep
open NumberField IsDedekindDomain
open scoped Quaternion Topology
namespace GlobalTheory.QSA.IntRep
namespace _root_.GlobalTheory.QSA.IntRep
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 →
    ∀ᶠ v in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))), ∀ t ∈ v.adicCompletionIntegers F,
      ∃ u : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b],
        _root_.GlobalTheory.QSA.nrm u = 1 ∧ u.re = t ∧ u.imI ∈ v.adicCompletionIntegers F ∧ u.imJ ∈ v.adicCompletionIntegers F ∧
          u.imK ∈ v.adicCompletionIntegers F := by
  intro F _ _ a b ha hb
  obtain ⟨α, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
  obtain ⟨β, e, he, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) b
  have hα : α ≠ 0 := by rintro rfl; simp at ha
  have hβ : β ≠ 0 := by rintro rfl; simp at hb
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have he0 : e ≠ 0 := nonZeroDivisors.ne_zero he
  have hx0 : α * d * β * e * 2 ≠ 0 := by
    have : (2 : 𝓞 F) ≠ 0 := two_ne_zero
    positivity
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors (I := Ideal.span {α * d * β * e * 2})
    (by simpa using hx0)).subset fun v hv => ?_)
  rw [Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  by_contra hx
  apply hv
  haveI := _root_.GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  haveI := _root_.GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hunit := (_root_.GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v _).2 hx
  simp only [map_mul, IsUnit.mul_iff] at hunit
  obtain ⟨⟨⟨⟨hA, hD⟩, hB⟩, hE⟩, h2⟩ := hunit
  rw [map_ofNat] at h2
  set a' : v.adicCompletionIntegers F :=
    algebraMap (𝓞 F) (v.adicCompletionIntegers F) α * ↑hD.unit⁻¹ with ha'_def
  set b' : v.adicCompletionIntegers F :=
    algebraMap (𝓞 F) (v.adicCompletionIntegers F) β * ↑hE.unit⁻¹ with hb'_def
  have ha'K : (a' : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F α / algebraMap (𝓞 F) F d) := by
    rw [map_div₀, ha'_def, MulMemClass.coe_mul,
      coe_adicCompletionIntegers_inv v hD.mul_val_inv]
    rfl
  have hb'K : (b' : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F β / algebraMap (𝓞 F) F e) := by
    rw [map_div₀, hb'_def, MulMemClass.coe_mul,
      coe_adicCompletionIntegers_inv v hE.mul_val_inv]
    rfl
  have ha'u : IsUnit a' := hA.mul (hD.unit⁻¹).isUnit
  have hb'u : IsUnit b' := hB.mul (hE.unit⁻¹).isUnit
  set ai : v.adicCompletionIntegers F := ↑ha'u.unit⁻¹ with hai_def
  have hai : a' * ai = 1 := ha'u.mul_val_inv
  intro t ht
  set T : v.adicCompletionIntegers F := ⟨t, ht⟩ with hT
  obtain ⟨z, hz⟩ : ∃ z : v.adicCompletionIntegers F, IsUnit (T ^ 2 - 1 + a' * b' * z ^ 2) := by
    by_cases hc : IsUnit (T ^ 2 - 1)
    · exact ⟨0, by simpa using hc⟩
    · refine ⟨1, ?_⟩
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, not_not] at hc
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_add, hc, zero_add, one_pow, mul_one]
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 (ha'u.mul hb'u)
  obtain ⟨r, s, hrs⟩ := exists_binary_form_eq_unit 0 (b' * ai) ((T ^ 2 - 1 + a' * b' * z ^ 2) * ai)
    (by
      rw [show (0 : v.adicCompletionIntegers F) ^ 2 - 4 * (b' * ai) = -(2 * 2 * (b' * ai)) by ring]
      exact ((h2.mul h2).mul (hb'u.mul (ha'u.unit⁻¹).isUnit)).neg)
    (hz.mul (ha'u.unit⁻¹).isUnit)
  have hO : T ^ 2 - a' * r ^ 2 - b' * s ^ 2 + a' * b' * z ^ 2 = 1 := by
    linear_combination (-a') * hrs + (b' * s ^ 2 - (T ^ 2 - 1) - a' * b' * z ^ 2) * hai
  refine ⟨⟨t, r, s, z⟩, ?_, rfl, r.2, s.2, z.2⟩
  unfold _root_.GlobalTheory.QSA.nrm
  rw [← ha'K, ← hb'K]
  have := congrArg (fun x : v.adicCompletionIntegers F => (x : v.adicCompletion F)) hO
  push_cast at this
  exact this
end _root_.GlobalTheory.QSA.IntRep
end GlobalTheory.QSA.IntRep
