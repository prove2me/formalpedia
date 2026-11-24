-- Prove2me | solution 1 for GlobalTheory.UnramOrder.isPrincipalIdealRing_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:08:25.161336+00:00
-- url     : https://prove2.me/submissions/15a61f4f-c742-4721-b9f4-326ea474fa50

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Theorems.Thm_GlobalTheory_UnramOrder_exists_eq_add_mul
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
variable {R₀ R : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R]
namespace GlobalTheory.UnramOrder
theorem _root_.solution [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [HenselianRing R₀ (maximalIdeal R₀)] (c : R →+* R) (hc : ∀ x, c (c x) = x)
    (hbase : ∀ r, c (algebraMap R₀ R r) = algebraMap R₀ R r)
    (hfix : ∀ x, c x = x → x ∈ (algebraMap R₀ R).range) {ω : R} (hω : IsUnit (ω - c ω))
    (hD : ∀ r : R₀, IsUnit (algebraMap R₀ R r) → IsUnit r) :
    IsPrincipalIdealRing R := by
  obtain ⟨t, ht⟩ := hfix (ω + c ω) (by rw [map_add, hc, add_comm])
  obtain ⟨n, hn⟩ := hfix (ω * c ω) (by rw [map_mul, hc, mul_comm])
  have hDu : IsUnit (t ^ 2 - 4 * n) := by
    refine hD _ ?_
    convert hω.pow 2 using 1
    simp only [map_sub, map_mul, map_pow, map_ofNat, ht, hn]
    ring
  by_cases hroot : ∃ r : R₀, r ^ 2 - t * r + n ∈ maximalIdeal R₀
  · obtain ⟨r₀, hr₀⟩ := hroot
    have hder : IsUnit (2 * r₀ - t) := by
      by_contra h
      have h1 : 2 * r₀ - t ∈ maximalIdeal R₀ := h
      have h2 : t ^ 2 - 4 * n ∈ maximalIdeal R₀ := by
        have : t ^ 2 - 4 * n = (2 * r₀ - t) * (2 * r₀ - t) - 4 * (r₀ ^ 2 - t * r₀ + n) := by ring
        rw [this]
        exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hr₀)
      exact h2 hDu
    obtain ⟨r, hr, -⟩ := HenselianRing.is_henselian (I := maximalIdeal R₀)
      (X ^ 2 - C t * X + C n) (by monicity!) r₀ (by simpa using hr₀) (by
        have := hder.map (Ideal.Quotient.mk (maximalIdeal R₀))
        convert this using 2
        simp [one_add_one_eq_two])
    simp only [IsRoot.def, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hr
    obtain ⟨d, hd⟩ := hDu.exists_right_inv

    have hg : (2 * r - t) * ((2 * r - t) * d) = 1 := by linear_combination hd + 4 * d * hr
    set g := (2 * r - t) * d
    have hr' := congrArg (algebraMap R₀ R) hr
    have hg' := congrArg (algebraMap R₀ R) hg
    simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_one, map_ofNat] at hr' hg'
    have hωω : ω * ω = algebraMap R₀ R t * ω - algebraMap R₀ R n := by rw [ht, hn]; ring
    set T := algebraMap R₀ R t
    set N := algebraMap R₀ R n
    set ρ := algebraMap R₀ R r with hρ
    set G := algebraMap R₀ R g
    obtain ⟨e, he⟩ : ∃ e, e = (ω - (T - ρ)) * G := ⟨_, rfl⟩
    have hee : e * e = e := by
      rw [he]
      linear_combination G ^ 2 * hωω - G ^ 2 * hr' + (ω - (T - ρ)) * G * hg'
    let ψ : R₀ × R₀ →+* R :=
      { toFun := fun z => algebraMap R₀ R z.1 * e + algebraMap R₀ R z.2 * (1 - e)
        map_zero' := by simp
        map_one' := by simp
        map_add' := fun x y => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring
        map_mul' := fun x y => by
          simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
          linear_combination (-(algebraMap R₀ R x.1 - algebraMap R₀ R x.2)
            * (algebraMap R₀ R y.1 - algebraMap R₀ R y.2)) * hee }
    refine IsPrincipalIdealRing.of_surjective ψ fun x => ?_
    obtain ⟨a, b, rfl⟩ := exists_eq_add_mul c hc hbase hfix hω x
    refine ⟨(a + b * r, a + b * (t - r)), ?_⟩
    show algebraMap R₀ R _ * e + algebraMap R₀ R _ * (1 - e) = _
    simp only [map_add, map_mul, map_sub]
    rw [he]
    linear_combination algebraMap R₀ R b * (ω - (T - ρ)) * hg'
  · push Not at hroot
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R₀
    have hm := hϖ.maximalIdeal_eq
    have hunit : ∀ a b : R₀, ¬ (ϖ ∣ a ∧ ϖ ∣ b) →
        IsUnit (algebraMap R₀ R a + algebraMap R₀ R b * ω) := by
      intro a b hab
      have hN : IsUnit (a ^ 2 + t * a * b + n * b ^ 2) := by
        by_contra h
        have h1 : a ^ 2 + t * a * b + n * b ^ 2 ∈ maximalIdeal R₀ := h
        by_cases hb : IsUnit b
        · obtain ⟨v, hv⟩ := hb.exists_right_inv
          refine hroot (-(a * v)) ?_
          have : (-(a * v)) ^ 2 - t * (-(a * v)) + n
              = v ^ 2 * (a ^ 2 + t * a * b + n * b ^ 2) := by
            linear_combination (-(t * a * v) - n * (b * v + 1)) * hv
          rw [this]
          exact Ideal.mul_mem_left _ _ h1
        · have hb' : b ∈ maximalIdeal R₀ := hb
          have ha2 : a ^ 2 ∈ maximalIdeal R₀ := by
            have : a ^ 2 = (a ^ 2 + t * a * b + n * b ^ 2) - (t * a + n * b) * b := by ring
            rw [this]
            exact Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ _ hb')
          have ha : a ∈ maximalIdeal R₀ := Ideal.IsPrime.mem_of_pow_mem inferInstance 2 ha2
          rw [hm, Ideal.mem_span_singleton] at ha hb'
          exact hab ⟨ha, hb'⟩
      have h2 := hN.map (algebraMap R₀ R)
      have : algebraMap R₀ R (a ^ 2 + t * a * b + n * b ^ 2)
          = (algebraMap R₀ R a + algebraMap R₀ R b * ω)
            * (algebraMap R₀ R a + algebraMap R₀ R b * c ω) := by
        simp only [map_add, map_mul, map_pow, ht, hn]; ring
      rw [this] at h2
      exact isUnit_of_mul_isUnit_left h2
    have hfac : ∀ x : R, x ≠ 0 → ∃ k : ℕ, ∃ u : R, IsUnit u ∧ x = algebraMap R₀ R ϖ ^ k * u := by
      intro x hx
      obtain ⟨a, b, rfl⟩ := exists_eq_add_mul c hc hbase hfix hω x
      obtain ⟨d, a', b', rfl, rfl, hcop⟩ : ∃ d a' b' : R₀, a = d * a' ∧ b = d * b' ∧
          ¬ (ϖ ∣ a' ∧ ϖ ∣ b') := by
        rcases ValuationRing.dvd_total a b with ⟨z, hz⟩ | ⟨z, hz⟩
        · exact ⟨a, 1, z, by simp, hz, fun h => hϖ.not_dvd_one h.1⟩
        · exact ⟨b, z, 1, hz, by simp, fun h => hϖ.not_dvd_one h.2⟩
      have hd : d ≠ 0 := by rintro rfl; simp at hx
      obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
      refine ⟨k, _, (u.isUnit.map (algebraMap R₀ R)).mul (hunit a' b' hcop), ?_⟩
      simp only [map_mul, map_pow]; ring
    refine ⟨fun I => ?_⟩
    by_cases hI : I = ⊥
    · rw [hI]; infer_instance
    have hpow : ∀ x ∈ I, x ≠ 0 → ∃ k : ℕ, algebraMap R₀ R ϖ ^ k ∈ I ∧ algebraMap R₀ R ϖ ^ k ∣ x := by
      intro x hx hx0
      obtain ⟨k, u, hu, rfl⟩ := hfac x hx0
      exact ⟨k, (I.mul_unit_mem_iff_mem hu).1 hx, dvd_mul_right _ _⟩
    have hex : ∃ k : ℕ, algebraMap R₀ R ϖ ^ k ∈ I := by
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      obtain ⟨k, hk, -⟩ := hpow x hx hx0
      exact ⟨k, hk⟩
    refine ⟨algebraMap R₀ R ϖ ^ Nat.find hex, le_antisymm (fun x hx => ?_) ?_⟩
    · by_cases hx0 : x = 0
      · rw [hx0]; exact zero_mem _
      obtain ⟨k, hk, hkx⟩ := hpow x hx hx0
      exact Ideal.mem_span_singleton.2 ((pow_dvd_pow _ (Nat.find_min' hex hk)).trans hkx)
    · exact (Submodule.span_singleton_le_iff_mem _ _).2 (Nat.find_spec hex)
end GlobalTheory.UnramOrder
