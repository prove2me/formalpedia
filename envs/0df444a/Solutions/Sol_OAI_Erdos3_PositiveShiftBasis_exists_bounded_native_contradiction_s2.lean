-- Prove2me | solution 1 for OAI.Erdos3.PositiveShiftBasis.exists_bounded_native_contradiction_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:27:47.890716+00:00
-- url     : https://prove2.me/submissions/626ca45c-b4d1-448b-b97d-bb72b30216d9

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B277
import Theorems.Thm_OAI_Erdos3_PositiveShiftBasis_exists_native_detector_contradiction_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem expect_pair_sub_real (F : G → ℝ) :
    (𝔼 h, 𝔼 k, F (h - k)) = 𝔼 d, F d := by
  rw [Finset.expect_comm]
  have hinner (k : G) : (𝔼 h, F (h - k)) = 𝔼 d, F d := by
    apply Fintype.expect_equiv (Equiv.addRight (-k))
    intro h
    simp only [Equiv.coe_addRight, sub_eq_add_neg]
  simp_rw [hinner]
  exact Fintype.expect_const _

theorem gowersNorm_pow_lower_of_pair_detector (j : ℕ) (v : G → ℂ)
    (C : G → G → ℝ) {alpha delta gamma : ℝ}
    (hdelta : 0 ≤ delta) (hgamma : 0 ≤ gamma)
    (hC : ∀ h k, C h k ≤ 1) (hmean : alpha ≤ 𝔼 h, 𝔼 k, C h k)
    (hdetect : ∀ h k, delta ≤ C h k →
      gamma ≤ gowersNorm (j + 1) (multiplicativeDerivative v (h - k))) :
    gamma ^ (2 ^ (j + 1)) * (alpha - delta) ≤
      gowersNorm (j + 2) v ^ (2 ^ (j + 2)) := by
  have hpoint (h k : G) :
      gamma ^ (2 ^ (j + 1)) * (C h k - delta) ≤
        gowersNorm (j + 1) (multiplicativeDerivative v (h - k)) ^ (2 ^ (j + 1)) := by
    by_cases hlarge : delta ≤ C h k
    · have hpow := pow_le_pow_left₀ hgamma (hdetect h k hlarge) (2 ^ (j + 1))
      have hsmall : C h k - delta ≤ 1 := by linarith [hC h k]
      exact (mul_le_of_le_one_right (pow_nonneg hgamma _) hsmall).trans hpow
    · have hleft : gamma ^ (2 ^ (j + 1)) * (C h k - delta) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hgamma _) (by linarith)
      exact hleft.trans (pow_nonneg (gowersNorm_nonneg j _) _)
  have h := Finset.expect_le_expect (fun h (_ : h ∈ (Finset.univ : Finset G)) =>
    Finset.expect_le_expect (fun k (_ : k ∈ (Finset.univ : Finset G)) => hpoint h k))
  simp_rw [← Finset.mul_expect, Finset.expect_sub_distrib,
    Finset.expect_const Finset.univ_nonempty] at h
  rw [expect_pair_sub_real (fun a =>
    gowersNorm (j + 1) (multiplicativeDerivative v a) ^ (2 ^ (j + 1))),
    ← gowersNorm_derivative] at h
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hmean delta) (pow_nonneg hgamma _)).trans h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedPartnerPower
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem functionCorrelationSeminorm_apply (w v : Ω → ℂ) :
    functionCorrelationSeminorm w v = ‖𝔼 x, v x * w x‖ := rfl

theorem functionCorrelationSeminorm_le (w v : Ω → ℂ) {M : ℝ}
    (hw : ∀ x, ‖w x‖ ≤ M) :
    functionCorrelationSeminorm w v ≤ M * (𝔼 x, ‖v x‖) := by
  rw [functionCorrelationSeminorm_apply, Finset.mul_expect]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le_expect
  intro x _
  rw [norm_mul, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hw x) (norm_nonneg _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G] [Fintype G]

theorem shiftTestSeminormAt_bddAbove (B : G → ℂ) (T : ι → G → ℂ) {M : ℝ}
    (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (h : G) :
    BddAbove (Set.range fun i => functionCorrelationSeminorm (fun x => B (x + h) * T i x)) := by
  apply Seminorm.bddAbove_range_iff.mpr
  intro v
  refine ⟨M * (𝔼 x, ‖v x‖), ?_⟩
  rintro _ ⟨i, rfl⟩
  apply functionCorrelationSeminorm_le
  intro x
  rw [norm_mul]
  exact ((mul_le_mul_of_nonneg_left (hT i x) (norm_nonneg _)).trans_eq
    (mul_one _)).trans (hB _)

theorem shiftTestSeminormAt_apply (B : G → ℂ) (T : ι → G → ℂ) {M : ℝ}
    (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (h : G) (v : G → ℂ) :
    shiftTestSeminormAt B T h v = ⨆ i, ‖𝔼 x, v x * (B (x + h) * T i x)‖ := by
  simp only [shiftTestSeminormAt,
    Seminorm.iSup_apply (shiftTestSeminormAt_bddAbove B T hB hT h),
    functionCorrelationSeminorm_apply]

theorem exists_nearly_maximizing_shift_tests [Nonempty ι]
    (B : G → ℂ) (T : ι → G → ℂ) {M : ℝ}
    (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1)
    (v : G → ℂ) {eta : ℝ} (heta : 0 < eta) :
    ∃ t : G → ι, shiftTestingSeminorm B T v - eta <
      𝔼 h, ‖𝔼 x, v x * (B (x + h) * T (t h) x)‖ := by
  have hchoice (h : G) : ∃ i, shiftTestSeminormAt B T h v - eta <
      ‖𝔼 x, v x * (B (x + h) * T i x)‖ := by
    rw [shiftTestSeminormAt_apply B T hB hT]
    exact exists_lt_of_lt_ciSup (sub_lt_self _ heta)
  choose t ht using hchoice
  refine ⟨t, ?_⟩
  change (𝔼 h, shiftTestSeminormAt B T h v) - eta < _
  rw [← Fintype.expect_const (ι := G) eta, ← Finset.expect_sub_distrib]
  exact Finset.expect_lt_expect (fun h _ => (ht h).le)
    ⟨0, Finset.mem_univ _, ht 0⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G]

theorem translatedTestFamily_norm_le_one (T : ι → G → ℂ)
    (hT : ∀ i x, ‖T i x‖ ≤ 1) (p : G × ι) (x : G) :
    ‖translatedTestFamily T p x‖ ≤ 1 := hT _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftTestingGowers
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G] [Fintype G] [Nonempty ι]

theorem exists_shift_tests_of_lt_seminorm (v B : G → ℂ) (T : ι → G → ℂ)
    {M a : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1)
    (ha : 0 ≤ a) (hlt : a < shiftTestingSeminorm B T v) :
    ∃ t : G → ι, a ^ 2 ≤ M ^ 2 * (𝔼 h, 𝔼 k,
      ‖𝔼 x, v x * star (v (x + h - k)) * T (t h) x * star (T (t k) (x + h - k))‖) := by
  let eta := (shiftTestingSeminorm B T v - a) / 2
  have heta : 0 < eta := by dsimp only [eta]; linarith
  obtain ⟨t, ht⟩ := exists_nearly_maximizing_shift_tests B T hB hT v heta
  have havg : a ≤ 𝔼 h, ‖𝔼 x, v x * (B (x + h) * T (t h) x)‖ := by
    dsimp only [eta] at ht
    linarith
  exact ⟨t, (pow_le_pow_left₀ ha havg 2).trans
    (shifted_test_cauchy_schwarz v B (fun h => T (t h)) hB)⟩

theorem exists_shift_tests_of_seminorm_large (v B : G → ℂ) (T : ι → G → ℂ)
    {M tau : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1)
    (htau : 0 < tau) (hlarge : tau ≤ shiftTestingSeminorm B T v) :
    ∃ t : G → ι, tau ^ 2 / 4 ≤ M ^ 2 * (𝔼 h, 𝔼 k,
      ‖𝔼 x, v x * star (v (x + h - k)) * T (t h) x * star (T (t k) (x + h - k))‖) := by
  obtain ⟨t, ht⟩ := exists_shift_tests_of_lt_seminorm v B T hB hT
    (a := tau / 2) (by positivity) (by linarith)
  exact ⟨t, (by convert ht using 1; ring)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G] [Fintype G]

theorem shift_derivative_correlation_le_one (v : G → ℂ) (T : ι → G → ℂ)
    (hv : ∀ x, ‖v x‖ ≤ 1) (hT : ∀ i x, ‖T i x‖ ≤ 1) (i j : ι) (h k : G) :
    ‖𝔼 x, v x * star (v (x + h - k)) * T i x * star (T j (x + h - k))‖ ≤ 1 := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  simp only [norm_mul, norm_star]
  have hpair := (mul_le_of_le_one_left (norm_nonneg _) (hv x)).trans (hv (x + h - k))
  have htriple := (mul_le_of_le_one_left (norm_nonneg _) hpair).trans (hT i x)
  exact (mul_le_of_le_one_left (norm_nonneg _) htriple).trans (hT j _)

theorem shiftTestingSeminorm_gowers_lower [Nonempty ι] (s : ℕ)
    (v B : G → ℂ) (T : ι → G → ℂ) {M tau delta gamma : ℝ}
    (hM : 0 < M) (htau : 0 < tau) (hdelta : 0 ≤ delta) (hgamma : 0 ≤ gamma)
    (hv : ∀ x, ‖v x‖ ≤ 1) (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1)
    (hlarge : tau ≤ shiftTestingSeminorm B T v)
    (hdet : ∀ (i j : ι) (a : G) (f : G → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      delta ≤ ‖𝔼 x, f x * T i x * star (T j (x + a))‖ → gamma ≤ gowersNorm (s + 1) f) :
    gamma ^ (2 ^ (s + 1)) * (tau ^ 2 / (4 * M ^ 2) - delta) ≤
      gowersNorm (s + 2) v ^ (2 ^ (s + 2)) := by
  obtain ⟨t, ht⟩ := exists_shift_tests_of_seminorm_large v B T hB hT htau hlarge
  let C : G → G → ℝ := fun h k =>
    ‖𝔼 x, v x * star (v (x + h - k)) * T (t h) x * star (T (t k) (x + h - k))‖
  have hmean : tau ^ 2 / (4 * M ^ 2) ≤ 𝔼 h, 𝔼 k, C h k := by
    apply (div_le_iff₀ (show 0 < 4 * M ^ 2 by positivity)).mpr
    change tau ^ 2 / 4 ≤ M ^ 2 * (𝔼 h, 𝔼 k, C h k) at ht
    nlinarith only [ht]
  apply gowersNorm_pow_lower_of_pair_detector s v C hdelta hgamma
    (fun h k => shift_derivative_correlation_le_one v T hv hT (t h) (t k) h k) hmean
  intro h k hc
  apply hdet (t h) (t k) (h - k) (multiplicativeDerivative v (h - k))
  · intro x
    simp only [multiplicativeDerivative, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hv x)).trans (hv _)
  · simpa only [C, multiplicativeDerivative, ← add_sub_assoc] using hc

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeProduct
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H]

variable [Fintype H]

theorem mixedGowersMoment_sum {j : ℕ} {κ : (Fin j → Bool) → Type*}
    [∀ ω, Fintype (κ ω)] (F : ∀ ω, κ ω → H → ℂ) :
    mixedGowersMoment j (fun ω x ↦ ∑ k, F ω k x) =
      ∑ q : ∀ ω, κ ω, mixedGowersMoment j (fun ω ↦ F ω (q ω)) := by
  classical
  simp only [mixedGowersMoment_eq_expect_cube, mixedCubeProduct, map_sum,
    Fintype.prod_sum, Finset.expect_sum_comm]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem gowersNorm_sum {ι : Type*} [Fintype ι] (j : ℕ) (f : ι → H → ℂ) :
    gowersNorm (j + 1) (fun x ↦ ∑ i, f i x) ≤ ∑ i, gowersNorm (j + 1) (f i) := by
  classical
  apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
    (Finset.sum_nonneg (fun i _ ↦ gowersNorm_nonneg j _))
  calc
    gowersNorm (j + 1) (fun x ↦ ∑ i, f i x) ^ (2 ^ (j + 1)) =
        ‖mixedGowersMoment (j + 1) (fun _ x ↦ ∑ i, f i x)‖ := by
      rw [mixedGowersMoment_const, norm_gowersMoment, gowersNorm_pow]
    _ = ‖∑ q : (Fin (j + 1) → Bool) → ι,
        mixedGowersMoment (j + 1) (fun ω ↦ f (q ω))‖ := by
      rw [mixedGowersMoment_sum (fun _ i ↦ f i)]
    _ ≤ ∑ q : (Fin (j + 1) → Bool) → ι,
        ‖mixedGowersMoment (j + 1) (fun ω ↦ f (q ω))‖ := norm_sum_le _ _
    _ ≤ ∑ q : (Fin (j + 1) → Bool) → ι,
        ∏ ω, gowersNorm (j + 1) (f (q ω)) :=
      Finset.sum_le_sum (fun q _ ↦ norm_mixedGowersMoment_le j _)
    _ = ∏ _ω : Fin (j + 1) → Bool, ∑ i, gowersNorm (j + 1) (f i) :=
      (Fintype.prod_sum (fun (_ω : Fin (j + 1) → Bool) i ↦
        gowersNorm (j + 1) (f i))).symm
    _ = (∑ i, gowersNorm (j + 1) (f i)) ^ (2 ^ (j + 1)) := by simp

theorem gowersNorm_add (j : ℕ) (f g : H → ℂ) :
    gowersNorm (j + 1) (fun x ↦ f x + g x) ≤
      gowersNorm (j + 1) f + gowersNorm (j + 1) g := by
  simpa [add_comm] using
    (gowersNorm_sum j (fun b : Bool ↦ if b then f else g))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

omit [Fintype H] in
theorem multiplicativeDerivative_const_mul (c : ℂ) (f : H → ℂ) (h : H) :
    multiplicativeDerivative (fun x ↦ c * f x) h =
      (fun x ↦ (c * star c) * multiplicativeDerivative f h x) := by
  funext x
  simp only [multiplicativeDerivative, star_mul]
  ring

theorem gowersNorm_const_mul (j : ℕ) (c : ℂ) (f : H → ℂ) :
    gowersNorm (j + 1) (fun x ↦ c * f x) = ‖c‖ * gowersNorm (j + 1) f := by
  induction j generalizing c f with
  | zero =>
    simp only [Nat.zero_add, gowersNorm_one, ← Finset.mul_expect, norm_mul]
  | succ j ih =>
    apply (pow_left_inj₀ (gowersNorm_nonneg (j + 1) _)
      (mul_nonneg (norm_nonneg _) (gowersNorm_nonneg (j + 1) _))
      (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))).mp
    rw [gowersNorm_derivative, mul_pow, gowersNorm_derivative]
    simp only [multiplicativeDerivative_const_mul, ih, norm_mul, norm_star, mul_pow]
    rw [← Finset.mul_expect]
    congr 1
    rw [← pow_add]
    congr 1
    simp [pow_succ, Nat.mul_two]

theorem gowersNorm_mul_character (j : ℕ) (χ f : H → ℂ)
    (hχ : ∀ x y, χ (x + y) = χ x * χ y) (hunit : ∀ x, ‖χ x‖ = 1) :
    gowersNorm (j + 2) (fun x ↦ χ x * f x) = gowersNorm (j + 2) f := by
  have hcancel (x : H) : χ x * star (χ x) = 1 := by
    change χ x * (starRingEnd ℂ) (χ x) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hunit]
    norm_num
  have hd (h : H) : multiplicativeDerivative (fun x ↦ χ x * f x) h =
      (fun x ↦ star (χ h) * multiplicativeDerivative f h x) := by
    funext x
    simp only [multiplicativeDerivative, hχ, star_mul]
    calc
      _ =
          (χ x * star (χ x)) * (star (χ h) * (f x * star (f (x + h)))) := by ring
      _ = _ := by rw [hcancel, one_mul]
  apply (pow_left_inj₀ (gowersNorm_nonneg (j + 1) _)
    (gowersNorm_nonneg (j + 1) _)
    (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))).mp
  rw [gowersNorm_derivative, gowersNorm_derivative]
  simp only [hd, gowersNorm_const_mul, norm_star, hunit, one_mul]

theorem gowersNorm_const (j : ℕ) (c : ℂ) :
    gowersNorm (j + 1) (fun _ : H ↦ c) = ‖c‖ := by
  simpa only [mul_one, gowersNorm_const_one] using
    (gowersNorm_const_mul j c (fun _ : H ↦ 1))

@[simp] theorem gowersNorm_zero (j : ℕ) :
    gowersNorm (j + 1) (fun _ : H ↦ 0) = 0 := by
  rw [gowersNorm_const, norm_zero]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem gowersNorm_restrict_one_pos (j : ℕ) {Q : Finset H} (hQ : Q.Nonempty) :
    0 < gowersNorm (j + 1) (restrictTo Q (fun _ ↦ 1)) := by
  have hmean : 0 < ‖𝔼 x, restrictTo Q (fun _ ↦ 1) x‖ := by
    rw [norm_expect_restrict_one]
    exact div_pos (by exact_mod_cast hQ.card_pos)
      (by exact_mod_cast Fintype.card_pos)
  exact hmean.trans_le (norm_expect_le_gowersNorm j _)

theorem gowersNorm_restrict_pow (j : ℕ) (Q : Finset H) (f : H → ℂ) :
    gowersNorm (j + 1) (restrictTo Q f) ^ (2 ^ (j + 1)) =
      (gowersMoment (j + 1) (restrictTo Q (fun _ ↦ 1))).re *
        restrictedGowersNorm (j + 1) Q f ^ (2 ^ (j + 1)) := by
  by_cases hQ : Q.Nonempty
  · rw [restrictedGowersNorm, div_pow, ← gowersNorm_pow]
    field_simp [(gowersNorm_restrict_one_pos j hQ).ne']
  · have he : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
    simp [he, restrictedGowersNorm, gowersNorm_zero]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem gowersNorm_restrict_cubeCount (j : ℕ) (Q : Finset H) (f : H → ℂ) :
    gowersNorm (j + 1) (restrictTo Q f) ^ (2 ^ (j + 1)) =
      ((groupCubeCount (j + 1) Q : ℝ) / (Fintype.card H : ℝ) ^ (j + 2)) *
        restrictedGowersNorm (j + 1) Q f ^ (2 ^ (j + 1)) := by
  rw [gowersNorm_restrict_pow, gowersMoment_indicator_re]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

variable [Fintype B] [DecidableEq B]

theorem finiteSupportGowersNorm_ambient_comparison {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f : A → ℂ) :
    gowersNorm (j + 1) (imageExtension φ Q f) ^ (2 ^ (j + 1)) =
      ((Nat.card (SupportedCube (j + 1) (Q : Set A)) : ℝ) /
        (Fintype.card B : ℝ) ^ (j + 2)) * finiteSupportGowersNorm (j + 1) Q f ^ (2 ^ (j + 1)) := by
  have h := gowersNorm_restrict_cubeCount j (Q.image φ) (imageExtension φ Q f)
  simpa only [restrictTo_imageExtension, ← card_supportedCube_image hφ,
    ← finiteSupportGowersNorm_eq_restricted hφ] using h

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem supportedCubeSum_congr_on (j : ℕ) (Q : Finset A)
    (F G : (Fin j → Bool) → A → ℂ) (h : ∀ ω x, x ∈ Q → F ω x = G ω x) :
    supportedCubeSum j (Q : Set A) F = supportedCubeSum j (Q : Set A) G := by
  unfold supportedCubeSum
  apply Finset.sum_congr rfl
  intro p _
  unfold mixedCubeProduct
  apply Finset.prod_congr rfl
  intro ω _
  rw [h ω _ (p.property ω)]

theorem finiteSupportGowersNorm_congr_on (j : ℕ) (Q : Finset A) (f g : A → ℂ)
    (h : ∀ x ∈ Q, f x = g x) : finiteSupportGowersNorm j Q f = finiteSupportGowersNorm j Q g := by
  unfold finiteSupportGowersNorm
  rw [supportedCubeSum_congr_on j Q (fun _ => f) (fun _ => g) (fun _ => h)]

theorem reflectsPairSums_of_addEquiv (e : A ≃+ B) (Q : Set A) :
    ReflectsPairSums e.toAddMonoidHom Q := by
  intro a ha b hb c hc d hd he
  change e a + e b = e c + e d at he
  apply e.injective
  exact (map_add e a b).trans (he.trans (map_add e c d).symm)

theorem card_supportedCube_image_eq [DecidableEq B] {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) :
    Nat.card (SupportedCube j (Q.image φ : Set B)) = Nat.card (SupportedCube j (Q : Set A)) := by
  simpa only [Finset.coe_image] using (Nat.card_congr (supportedCubeEquiv hφ j)).symm

theorem finiteSupportGowersNorm_imageExtension [DecidableEq B] {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f : A → ℂ) :
    finiteSupportGowersNorm j (Q.image φ) (imageExtension φ Q f) = finiteSupportGowersNorm j Q f := by
  unfold finiteSupportGowersNorm
  rw [card_supportedCube_image_eq hφ]
  simp only [Finset.coe_image, supportedCubeSum_imageExtension hφ]

theorem finiteSupportGowersNorm_addEquiv [DecidableEq B] (e : A ≃+ B)
    (j : ℕ) (Q : Finset A) (f : B → ℂ) :
    finiteSupportGowersNorm j (Q.image e) f = finiteSupportGowersNorm j Q (fun x => f (e x)) := by
  have hφ := reflectsPairSums_of_addEquiv e (Q : Set A)
  calc
    _ = finiteSupportGowersNorm j (Q.image e) (imageExtension e.toAddMonoidHom Q (fun x => f (e x))) := by
      apply finiteSupportGowersNorm_congr_on
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (imageExtension_apply hφ.injOn (fun x => f (e x)) hx).symm
    _ = _ := finiteSupportGowersNorm_imageExtension hφ j _

theorem finiteCorrelation_addEquiv [DecidableEq B] (e : A ≃+ B)
    (Q : Finset A) (f g : B → ℂ) :
    finiteCorrelation (Q.image e) f g = finiteCorrelation Q (fun x => f (e x)) (fun x => g (e x)) := by
  unfold finiteCorrelation
  exact Finset.expect_image e.injective.injOn

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteConvolution
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem finiteConvolution_fourier (f g : H → ℂ) (x : H) :
    finiteConvolution f g x =
      ∑ χ : AddChar H ℂ, (finiteFourierCoeff f χ * finiteFourierCoeff g χ) * χ x := by
  symm
  have hχ (χ : AddChar H ℂ) :
      (finiteFourierCoeff f χ * finiteFourierCoeff g χ) * χ x =
        𝔼 y, f y * (finiteFourierCoeff g χ * χ (x - y)) := by
    rw [mul_assoc, finiteFourierCoeff, Finset.expect_mul]
    apply Finset.expect_congr rfl
    intro y _
    rw [addChar_sub_star]
    ring
  simp_rw [hχ]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro y _
  rw [← Finset.mul_sum, finiteFourier_inversion]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.GowersFourierMultiplier
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem gowersNorm_mul_fourier (j : ℕ) (f : H → ℂ) (a : AddChar H ℂ → ℂ) :
    gowersNorm (j + 2) (fun x => f x * (∑ χ : AddChar H ℂ, a χ * χ x)) ≤
      (∑ χ : AddChar H ℂ, ‖a χ‖) * gowersNorm (j + 2) f := by
  simp only [Finset.mul_sum]
  apply (gowersNorm_sum (j + 1) _).trans_eq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro χ _
  have he : (fun x => f x * (a χ * χ x)) = (fun x => a χ * (χ x * f x)) := by
    funext x
    ring
  rw [he, gowersNorm_const_mul, gowersNorm_mul_character j χ f χ.map_add_eq_mul χ.norm_apply]

theorem gowersNorm_mul_convolution (j : ℕ) (f u v : H → ℂ) :
    gowersNorm (j + 2) (fun x => f x * finiteConvolution u v x) ≤
      (∑ χ : AddChar H ℂ, ‖finiteFourierCoeff u χ * finiteFourierCoeff v χ‖) *
        gowersNorm (j + 2) f := by
  simp only [finiteConvolution_fourier]
  exact gowersNorm_mul_fourier j f _

theorem gowersNorm_mul_approximation (j : ℕ) (f u v : H → ℂ) {M ε : ℝ}
    (hε : 0 ≤ ε) (hf : ∀ x, ‖f x‖ ≤ 1) (huv : ∀ x, ‖u x - v x‖ ≤ 1)
    (herror : (𝔼 x, ‖u x - v x‖) ≤ ε ^ (2 ^ (j + 2)))
    (hmult : gowersNorm (j + 2) (fun x => f x * v x) ≤ M * gowersNorm (j + 2) f) :
    gowersNorm (j + 2) (fun x => f x * u x) ≤ M * gowersNorm (j + 2) f + ε := by
  let e := fun x => f x * (u x - v x)
  have heunit (x : H) : ‖e x‖ ≤ 1 := by
    simpa only [e, norm_mul, one_mul] using mul_le_mul (hf x) (huv x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hepoint (x : H) : ‖e x‖ ≤ ‖u x - v x‖ := by
    simpa only [e, norm_mul, one_mul] using mul_le_mul_of_nonneg_right (hf x) (norm_nonneg (u x - v x))
  have he : gowersNorm (j + 2) e ≤ ε :=
    gowersNorm_le_of_mean_norm_le_pow (j + 1) e heunit hε
      ((Finset.expect_le_expect (fun x _ => hepoint x)).trans herror)
  have hsplit : (fun x => f x * u x) = (fun x => f x * v x + e x) := by
    funext x
    dsimp [e]
    ring
  rw [hsplit]
  exact (gowersNorm_add (j + 1) _ _).trans (add_le_add hmult he)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [AddCommGroup H] [Fintype H] in
theorem finiteIndicator_sub_norm_le_one (I : Finset H) (x y : H) :
    ‖finiteIndicator I x - finiteIndicator I y‖ ≤ 1 := by
  simp only [finiteIndicator]
  split_ifs <;> norm_num

omit [Fintype H] in
theorem finiteIndicator_sub_smoothed_norm_le_one (I : Finset H) {B : Finset H}
    (hB : B.Nonempty) (x : H) : ‖finiteIndicator I x - smoothedIndicator I B x‖ ≤ 1 := by
  have he : finiteIndicator I x - smoothedIndicator I B x =
      𝔼 h ∈ B, (finiteIndicator I x - finiteIndicator I (x - h)) := by
    rw [Finset.expect_sub_distrib, Finset.expect_const hB]
    rfl
  rw [he]
  exact (RCLike.norm_expect_le (K := ℂ)).trans
    ((Finset.expect_le_expect (fun h _ => finiteIndicator_sub_norm_le_one I x (x - h))).trans_eq
      (Finset.expect_const hB 1))

theorem gowersNorm_mul_smoothedIndicator (j : ℕ) (f : H → ℂ) (I : Finset H)
    {B : Finset H} (hB : B.Nonempty) :
    gowersNorm (j + 2) (fun x => f x * smoothedIndicator I B x) ≤
      ((Fintype.card H : ℝ) / B.card) * gowersNorm (j + 2) f := by
  simp only [smoothedIndicator_eq_convolution]
  exact (gowersNorm_mul_convolution j f _ _).trans
    (mul_le_mul_of_nonneg_right (smoothedIndicator_fourier_mass hB I) (gowersNorm_nonneg (j + 1) f))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {N : ℕ} [NeZero N]

theorem exists_cyclic_interval_smoothing (a : ZMod N) (L : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ v : ZMod N → ℂ,
      (∀ x, ‖finiteIndicator (cyclicInterval a L) x - v x‖ ≤ 1) ∧
      (𝔼 x, ‖finiteIndicator (cyclicInterval a L) x - v x‖) ≤ 2 * δ ∧
      ∀ (j : ℕ) (f : ZMod N → ℂ),
        gowersNorm (j + 2) (fun x => f x * v x) ≤ (2 / δ) * gowersNorm (j + 2) f := by
  obtain ⟨K, hK, hKN, hsmall, hratio⟩ := exists_smoothing_scale (NeZero.pos N) hδ hδ1
  let I := cyclicInterval a L
  let B := cyclicInterval (0 : ZMod N) K
  have hB : B.Nonempty := cyclicInterval_nonempty 0 hK
  have hcard : B.card = K := cyclicInterval_card 0 hKN
  refine ⟨smoothedIndicator I B, finiteIndicator_sub_smoothed_norm_le_one I hB, ?_, ?_⟩
  · apply mean_indicator_smoothing_error I hB
    intro h hh
    obtain ⟨m, hm, he⟩ := Finset.mem_image.mp hh
    have hmK : m ≤ K - 1 := by have := Finset.mem_range.mp hm; omega
    have hmreal : (m : ℝ) ≤ δ * N := (Nat.cast_le.mpr hmK).trans hsmall
    have hmean := cyclicInterval_nat_shift_error a L m
    have hhcast : (m : ZMod N) = h := by simpa using he
    rw [hhcast] at hmean
    apply hmean.trans
    apply (div_le_iff₀ (by exact_mod_cast NeZero.pos N : (0 : ℝ) < N)).mpr
    nlinarith
  · intro j f
    have hm := gowersNorm_mul_smoothedIndicator j f I hB
    rw [ZMod.card, hcard] at hm
    exact hm.trans (mul_le_mul_of_nonneg_right hratio (gowersNorm_nonneg (j + 1) f))

theorem gowersNorm_cyclicInterval_cutoff (j : ℕ) (f : ZMod N → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (a : ZMod N) (L : ℕ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    gowersNorm (j + 2) (fun x => f x * finiteIndicator (cyclicInterval a L) x) ≤
      (4 / ε ^ (2 ^ (j + 2))) * gowersNorm (j + 2) f + ε := by
  let δ := ε ^ (2 ^ (j + 2)) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hpower : ε ^ (2 ^ (j + 2)) ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hε.le hε1 (2 ^ (j + 2))
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  obtain ⟨v, hv, herr, hmult⟩ := exists_cyclic_interval_smoothing a L hδ hδ1
  apply gowersNorm_mul_approximation j f (finiteIndicator (cyclicInterval a L)) v hε.le hf hv
  · convert herr using 1
    dsimp [δ]
    ring
  · have he : 2 / δ = 4 / ε ^ (2 ^ (j + 2)) := by dsimp [δ]; ring
    simpa only [he] using hmult j f

end Erdos3

end

section

namespace Erdos3

variable {N : ℕ} [NeZero N]

theorem gowersNorm_lower_bound_of_cyclicInterval (j : ℕ) (f : ZMod N → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (a : ZMod N) (L : ℕ)
    {η ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcut : η ≤ gowersNorm (j + 2) (fun x => f x * finiteIndicator (cyclicInterval a L) x)) :
    (η - ε) * ε ^ (2 ^ (j + 2)) / 4 ≤ gowersNorm (j + 2) f := by
  have hb := hcut.trans (gowersNorm_cyclicInterval_cutoff j f hf a L hε hε1)
  have he : ε ^ (2 ^ (j + 2)) ≠ 0 := pow_ne_zero _ hε.ne'
  have hd : η - ε ≤ 4 / ε ^ (2 ^ (j + 2)) * gowersNorm (j + 2) f := by linarith
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  calc
    _ ≤ (4 / ε ^ (2 ^ (j + 2)) * gowersNorm (j + 2) f) * ε ^ (2 ^ (j + 2)) :=
      mul_le_mul_of_nonneg_right hd (pow_nonneg hε.le _)
    _ = _ := by field_simp

theorem gowersNorm_transfer_cyclicInterval (j : ℕ) (f : ZMod N → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (a : ZMod N) (L : ℕ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hcut : η ≤ gowersNorm (j + 2) (fun x => f x * finiteIndicator (cyclicInterval a L) x)) :
    (η / 2) ^ (2 ^ (j + 2) + 1) / 4 ≤ gowersNorm (j + 2) f := by
  have hb := gowersNorm_lower_bound_of_cyclicInterval j f hf a L
    (ε := η / 2) (by linarith) (by linarith) hcut
  have he : η - η / 2 = η / 2 := by ring
  rw [he, ← pow_succ'] at hb
  exact hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3.NativeModelingNumerics

theorem mul_exp_le_exp {a b c d : ℝ} (hc : c ≤ Real.exp d) (hab : a + d ≤ b) :
    c * Real.exp a ≤ Real.exp b := by
  calc
    _ ≤ Real.exp d * Real.exp a := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _ = Real.exp (d + a) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem exp_ratio_le {a b c d u : ℝ} (hc : c ≤ Real.exp d) (hu : a + b + d ≤ u) :
    Real.exp a / (Real.exp (-b) / c) ≤ Real.exp u := by
  have he : Real.exp a / (Real.exp (-b) / c) = c * Real.exp (a + b) := by
    rw [div_div_eq_mul_div]
    calc
      _ = c * (Real.exp a / Real.exp (-b)) := by ring
      _ = _ := by rw [← Real.exp_sub]; congr 2; ring
  rw [he]
  exact mul_exp_le_exp hc hu

theorem exp_threshold_le {a b c d u : ℝ} (hc : 0 < c) (hcd : c ≤ Real.exp d)
    (hu : b + 2 * a + d ≤ u) :
    Real.exp (-u) ≤ (Real.exp (-b) / c) / Real.exp a ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos (Real.exp_pos a))).mpr
  apply (le_div_iff₀ hc).mpr
  have hsquare : Real.exp a ^ 2 = Real.exp (2 * a) := by
    simpa using (Real.exp_nat_mul a 2).symm
  rw [hsquare, ← Real.exp_add, mul_comm _ c]
  exact mul_exp_le_exp hcd (by linarith)

theorem sequential_thresholds {p q r : ℝ} (hp : 2 ≤ p) (hqp : q ≤ p) :
    Real.exp p / (Real.exp (-(2 * q + 2)) / 4) ≤ Real.exp (8 * p + 8) ∧
    Real.exp (-(8 * p + 8)) ≤
      (Real.exp (-(2 * q + 2)) / 4) / Real.exp (p + 2) ^ 2 ∧
    1 / (Real.exp (-(2 * q + 2)) * Real.exp (-r) / 8) ≤ Real.exp (8 * p + 8 + r) ∧
    Real.exp (-(8 * p + 8 + r)) ≤
      (Real.exp (-(2 * q + 2)) * Real.exp (-r) / 8) / Real.exp p ^ 2 := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have he : Real.exp (-(2 * q + 2)) * Real.exp (-r) = Real.exp (-(2 * q + 2 + r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨exp_ratio_le h4 (by linarith), exp_threshold_le (by norm_num) h4 (by linarith), ?_, ?_⟩
  · rw [he]
    simpa only [Real.exp_zero] using
      (exp_ratio_le (a := 0) (b := 2 * q + 2 + r) h8 (by linarith : 0 + (2 * q + 2 + r) + 8 ≤ 8 * p + 8 + r))
  · rw [he]
    exact exp_threshold_le (by norm_num) h8 (by linarith)

theorem coefficient_bound (r : ℝ) : 2 / Real.exp (-r) ≤ Real.exp (r + 2) := by
  rw [div_eq_mul_inv, Real.exp_neg, inv_inv]
  exact mul_exp_le_exp (by linarith [Real.add_one_le_exp (2 : ℝ)]) le_rfl

theorem one_add_mul_exp_bound {a : ℝ} (ha : 0 ≤ a) (c : ℝ) :
    1 + c * Real.exp a ≤ Real.exp (a + c) := by
  have h1 : 1 ≤ Real.exp a := Real.one_le_exp_iff.mpr ha
  calc
    _ ≤ (1 + c) * Real.exp a := by linarith
    _ ≤ Real.exp c * Real.exp a := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp c]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

theorem first_length_bound {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    1 + 4 * Real.exp p ^ 2 /
      (Real.exp (-r) ^ 2 * (Real.exp (-(2 * q + 2)) / 4) ^ 2) ≤
        Real.exp (2 * p + 2 * r + 4 * q + 4 + 64) := by
  have he : 4 * Real.exp p ^ 2 /
      (Real.exp (-r) ^ 2 * (Real.exp (-(2 * q + 2)) / 4) ^ 2) =
        64 * Real.exp (2 * p + 2 * r + 4 * q + 4) := by
    have hs : 2 * p + 2 * r + 4 * q + 4 = 2 * p + 2 * r + 2 * (2 * q + 2) := by ring
    rw [hs, Real.exp_add, Real.exp_add]
    have ht (x : ℝ) : Real.exp (2 * x) = Real.exp x ^ 2 := by simpa using Real.exp_nat_mul x 2
    rw [ht, ht, ht, Real.exp_neg, Real.exp_neg]
    field_simp
    ring
  rw [he]
  exact one_add_mul_exp_bound (by positivity) 64

theorem second_length_bound {q r t : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    1 + 4 / (Real.exp (-t) ^ 2 *
      (Real.exp (-(2 * q + 2)) * Real.exp (-r) / 8) ^ 2) ≤
        Real.exp (2 * t + 2 * r + 4 * q + 4 + 256) := by
  have he : 4 / (Real.exp (-t) ^ 2 *
      (Real.exp (-(2 * q + 2)) * Real.exp (-r) / 8) ^ 2) =
        256 * Real.exp (2 * t + 2 * r + 4 * q + 4) := by
    have hs : 2 * t + 2 * r + 4 * q + 4 = 2 * t + 2 * r + 2 * (2 * q + 2) := by ring
    rw [hs, Real.exp_add, Real.exp_add]
    have he (x : ℝ) : Real.exp (2 * x) = Real.exp x ^ 2 := by simpa using Real.exp_nat_mul x 2
    rw [he, he, he, Real.exp_neg, Real.exp_neg, Real.exp_neg]
    field_simp
    ring
  rw [he]
  exact one_add_mul_exp_bound (by positivity) 256

theorem length_product_bound {p q r t : ℝ} (hp : 2 ≤ p) (hq : 0 ≤ q)
    (hqp : q ≤ p) (hr : 0 ≤ r) (hrt : r ≤ t) :
    (1 + 4 * Real.exp p ^ 2 /
      (Real.exp (-r) ^ 2 * (Real.exp (-(2 * q + 2)) / 4) ^ 2)) *
    (1 + 4 / (Real.exp (-t) ^ 2 *
      (Real.exp (-(2 * q + 2)) * Real.exp (-r) / 8) ^ 2)) ≤
        Real.exp (1000 * (p + t + 2)) := by
  calc
    _ ≤ Real.exp (2 * p + 2 * r + 4 * q + 4 + 64) *
        Real.exp (2 * t + 2 * r + 4 * q + 4 + 256) :=
      mul_le_mul (first_length_bound (by linarith) hq hr)
        (second_length_bound hq hr (hr.trans hrt)) (by positivity) (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3.NativeModelingNumerics

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

theorem exists_product_niltest {ι σ : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}
    (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p) :
    letI : FiniteDimensional ℚ (∀ i, L i) := (productFinBasis D).finiteDimensional_of_finite
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i)) := IsModuleTopology.topologicalAddGroup ℝ _
    letI : T2Space (ℝ ⊗[ℚ] (∀ i, L i)) := realification_moduleTopology_t2 (productFinBasis D)
    ∃ S : (pi D).Niltest w, S.ComplexityLE (productNiltestBudget p) ∧
      ∀ x, S.eval x = ∏ i, (T i).eval x := by
  let : FiniteDimensional ℚ (∀ i, L i) := (productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, L i)) := realification_moduleTopology_t2 (productFinBasis D)
  exact ⟨piNiltest D T hp hι hT, piNiltest_complexity D T hp hι hT, piNiltest_eval D T hp hι hT⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CyclicProductBudget
namespace OAI

section

namespace Erdos3

theorem cyclicProductInputBudget_bounds {p : ℝ} (hp : 0 ≤ p) :
    1 ≤ cyclicProductInputBudget p ∧ productNiltestBudget p ≤ cyclicProductInputBudget p ∧
      3 * p + 16 ≤ cyclicProductInputBudget p := by
  have hn : 0 ≤ productNiltestBudget p := (sq_nonneg (p + 2)).trans (productNiltestBudget_geometry hp)
  unfold cyclicProductInputBudget
  constructor
  · linarith
  constructor <;> linarith

theorem cyclicProductCutoffBudget_nonneg (s c : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ cyclicProductCutoffBudget s c p := by
  have hq := (cyclicProductInputBudget_bounds hp).1
  unfold cyclicProductCutoffBudget cyclicProductVolumeBudget
  positivity

theorem cyclic_product_retained_correlation (m : ℕ) {p : ℝ} (hm : (m : ℝ) ≤ p) :
    Real.exp (-(3 * p + 16)) ≤ Real.exp (-p) / (2 * ((m : ℝ) + 8)) := by
  have hd : 2 * ((m : ℝ) + 8) ≤ Real.exp (2 * p + 16) := by
    linarith [Real.add_one_le_exp (2 * p + 16)]
  calc
    _ = Real.exp (-p) / Real.exp (2 * p + 16) := by rw [← Real.exp_sub]; congr 1; ring
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_nonneg _) (by positivity) hd

theorem cyclic_product_retained_volume (m : ℕ) {p : ℝ} (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) :
    Real.exp (-cyclicProductVolumeBudget p) ≤
      Real.exp (-p) / (2 * ((m : ℝ) + 8) * Real.exp ((m : ℝ) * p)) := by
  have hd : 2 * ((m : ℝ) + 8) ≤ Real.exp (2 * p + 16) := by
    linarith [Real.add_one_le_exp (2 * p + 16)]
  have he : Real.exp ((m : ℝ) * p) ≤ Real.exp (p ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hden : 2 * ((m : ℝ) + 8) * Real.exp ((m : ℝ) * p) ≤
      Real.exp (2 * p + 16 + p ^ 2) := by
    rw [Real.exp_add]
    exact mul_le_mul hd he (Real.exp_nonneg _) (Real.exp_nonneg _)
  calc
    _ = Real.exp (-p) / Real.exp (2 * p + 16 + p ^ 2) := by
      rw [← Real.exp_sub]
      congr 1
      unfold cyclicProductVolumeBudget
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_nonneg _) (by positivity) hden

theorem cyclic_product_cutoff_exponential (s c : ℕ) (p : ℝ) :
    Real.exp (-cyclicProductCutoffBudget s c p) ≤
      ((1 : ℝ) / ((s : ℝ) + 3) ^ (s + 3)) *
        Real.exp (-cyclicProductVolumeBudget p) ^ (s + 3) *
        Real.exp (-((cyclicProductInputBudget p + c) ^ c)) ^ (2 ^ (s + 2)) := by
  have hc : Real.exp (-(((s + 3) ^ (s + 3) : ℕ) : ℝ)) ≤
      (1 : ℝ) / ((s : ℝ) + 3) ^ (s + 3) := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, mul_one, pow_one] using
      exp_neg_nat_mul_le_inverse_pow ((s + 3) ^ (s + 3)) 1 (by positivity) (p := 1) (by norm_num)
  calc
    _ = Real.exp (-(((s + 3) ^ (s + 3) : ℕ) : ℝ)) *
        Real.exp (-cyclicProductVolumeBudget p) ^ (s + 3) *
        Real.exp (-((cyclicProductInputBudget p + c) ^ c)) ^ (2 ^ (s + 2)) := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      unfold cyclicProductCutoffBudget
      ring
    _ ≤ _ := by gcongr

theorem cyclic_product_transfer_exponential (s c : ℕ) (p : ℝ) :
    Real.exp (-cyclicProductDetectionBudget s c p) ≤
      (Real.exp (-cyclicProductCutoffBudget s c p) / 2) ^ (2 ^ (s + 2) + 1) / 4 := by
  have h4 : Real.exp (-(4 : ℝ)) ≤ 1 / 4 := by
    simpa only [Nat.cast_ofNat, mul_one, pow_one] using
      exp_neg_nat_mul_le_inverse_pow 4 1 (by norm_num) (p := 1) (by norm_num)
  calc
    _ = Real.exp (-cyclicProductCutoffBudget s c p - 1) ^ (2 ^ (s + 2) + 1) * Real.exp (-4) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      unfold cyclicProductDetectionBudget
      push_cast
      ring
    _ ≤ (Real.exp (-cyclicProductCutoffBudget s c p) / 2) ^ (2 ^ (s + 2) + 1) * (1 / 4) := by
      gcongr
      exact exp_sub_one_le_half_exp _
    _ = _ := by ring

theorem exists_cyclicProductDetectionBudget_bound (s c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → cyclicProductDetectionBudget s c p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let B := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4
  let Q := B + 3 * X + 17
  let V := X ^ 2 + 3 * X + 16
  let R := Polynomial.C ((s + 3) ^ (s + 3)) + Polynomial.C (s + 3) * V +
    Polynomial.C (2 ^ (s + 2)) * (Q + Polynomial.C c) ^ c
  let P := Polynomial.C (2 ^ (s + 2) + 1) * (R + 1) + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, R, V, Q, B, X, Polynomial.eval₂_pow, cyclicProductDetectionBudget,
    cyclicProductCutoffBudget, cyclicProductInputBudget, cyclicProductVolumeBudget,
    productNiltestBudget, productObservableLipBudget] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveCyclicCorrelation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem translatedCyclicProduct_norm_bound (h : ι → ZMod N) (u : ι → ℤ → ℂ)
    {p : ℝ} (hu : ∀ i x, ‖u i x‖ ≤ Real.exp p) (x : ZMod N) :
    ‖translatedCyclicProduct h u x‖ ≤ Real.exp ((Fintype.card ι : ℝ) * p) := by
  unfold translatedCyclicProduct
  rw [norm_prod]
  calc
    _ ≤ ∏ _i : ι, Real.exp p := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hu i _)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3

theorem exists_correlating_niltest_product_piece {ι : Type*} [Fintype ι]
    {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
    {s : ℕ} {d : ι → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (w : Fin 1 → ℕ) (hw : ∀ j, 0 < w j) (T : ∀ i, (D i).Niltest w)
    {p : ℝ} (hT : ∀ i, (T i).ComplexityLE p) {N : ℕ} [NeZero N]
    (h : ι → ZMod N) (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hc : Real.exp (-p) ≤ ‖finiteCorrelation Finset.univ f
      (translatedCyclicProduct h (fun i n => (T i).eval (fun _ => n)))‖) :
    ∃ a : commonCyclicCuts h,
      let len := intervalCutUpper (commonCyclicCuts h) N a - a
      let S := fun i => (T i).translate hw (fun _ => cyclicTranslationOffset (h i) a)
      0 < len ∧ a.val + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      (∀ i, (S i).ComplexityLE p) ∧
      Real.exp (-p) / (2 * ((Fintype.card ι : ℝ) + 8)) ≤
        ‖finiteCorrelation (Finset.Ico (a.val : ℤ) (a.val + len)) (fun x => f (x : ZMod N))
          (fun x => ∏ i, (S i).eval (fun _ => x))‖ ∧
      Real.exp (-p) / (2 * ((Fintype.card ι : ℝ) + 8) * Real.exp ((Fintype.card ι : ℝ) * p)) ≤
        (len : ℝ) / N := by
  have hu (x : ZMod N) :
      ‖translatedCyclicProduct h (fun i n => (T i).eval (fun _ => n)) x‖ ≤
        Real.exp ((Fintype.card ι : ℝ) * p) :=
    translatedCyclicProduct_norm_bound h _ (fun i n => (T i).eval_budget (hT i) _) x
  obtain ⟨a, hpos, hbound, hshort, hcorr, hvol⟩ := exists_correlating_integer_product_interval
    h (fun i n => (T i).eval (fun _ => n)) f (Real.exp_pos (-p))
      (Real.exp_pos ((Fintype.card ι : ℝ) * p)) hf hu hc
  refine ⟨a, hpos, hbound, hshort, ?_, ?_, hvol⟩
  · intro i
    exact hT i
  · have he (x : ℤ) :
        (∏ i, ((T i).translate hw (fun _ => cyclicTranslationOffset (h i) a)).eval (fun _ => x)) =
          ∏ i, (T i).eval (fun _ => x + cyclicTranslationOffset (h i) a) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [RationalFilteredNilmanifold.Niltest.eval_translate]
      rfl
    simpa only [he] using hcorr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ShiftFailurePositiveBasis
namespace OAI

section

namespace Erdos3.PositiveShiftBasis

open scoped BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}

theorem testingFamily_norm_le (B : PositiveShiftBasis s N q a J)
    (hk : ZMod N × Fin B.count) (n : ZMod N) : ‖B.testingFamily hk n‖ ≤ 1 := by
  classical
  by_cases hh : hk.1 ∈ B.shifts
  · rw [testingFamily, if_pos hh]
    exact ((B.mode hk.1 hk.2).norm_evalCyclic_le N _).trans (B.mode_norm hk.1 hh hk.2)
  · simp only [testingFamily, if_neg hh, norm_zero, zero_le_one]

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCommonModelQuadruples
namespace OAI

section

namespace Erdos3

open scoped TensorProduct Pointwise

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem nativeCyclicFunctions_norm {degree N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (hf : f ∈ nativeCyclicFunctions degree N p) (x : ZMod N) : ‖f x‖ ≤ 1 := by
  obtain ⟨F⟩ := hf
  rw [F.eval x]
  exact (F.test.norm_evalCyclic_le N (fun _ => x)).trans F.norm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.OneDimensionalBox
namespace OAI

section

namespace Erdos3

theorem oneDimensionalBox_eq_image (a : ℤ) (L : ℕ) :
    translatedIntegerBox (fun _ : Fin 1 => a) (fun _ => L) =
      (Finset.Ico a (a + L)).image (scalarPiOneEquiv ℤ) := by
  ext x
  rw [mem_translatedIntegerBox, Finset.mem_image]
  constructor
  · intro hx
    refine ⟨x 0, Finset.mem_Ico.mpr (hx 0), ?_⟩
    exact (scalarPiOneEquiv ℤ).apply_symm_apply x
  · rintro ⟨y, hy, rfl⟩ i
    exact Finset.mem_Ico.mp hy

theorem oneDimensionalBox_norm (j : ℕ) (a : ℤ) (L : ℕ) (f : (Fin 1 → ℤ) → ℂ) :
    finiteSupportGowersNorm j (translatedIntegerBox (fun _ : Fin 1 => a) (fun _ => L)) f =
      finiteSupportGowersNorm j (Finset.Ico a (a + L)) (fun x => f (fun _ => x)) := by
  rw [oneDimensionalBox_eq_image]
  exact finiteSupportGowersNorm_addEquiv (scalarPiOneEquiv ℤ) j _ f

theorem oneDimensionalBox_correlation (a : ℤ) (L : ℕ) (f g : (Fin 1 → ℤ) → ℂ) :
    finiteCorrelation (translatedIntegerBox (fun _ : Fin 1 => a) (fun _ => L)) f g =
      finiteCorrelation (Finset.Ico a (a + L)) (fun x => f (fun _ => x)) (fun x => g (fun _ => x)) := by
  rw [oneDimensionalBox_eq_image]
  exact finiteCorrelation_addEquiv (scalarPiOneEquiv ℤ) _ f g

theorem integerInterval_cubeCount_bounds (a : ℤ) (L : ℕ) [NeZero L] (j : ℕ) :
    ((1 : ℝ) / ((j : ℝ) + 1) ^ (j + 1)) * (L : ℝ) ^ (j + 1) ≤
      Nat.card (SupportedCube j (Finset.Ico a (a + L) : Set ℤ)) ∧
    (Nat.card (SupportedCube j (Finset.Ico a (a + L) : Set ℤ)) : ℝ) ≤ (L : ℝ) ^ (j + 1) := by
  have h := translatedIntegerBox_cubeCount_bounds (fun _ : Fin 1 => L) (fun _ => a) j
  rw [oneDimensionalBox_eq_image] at h
  have he := reflectsPairSums_of_addEquiv (scalarPiOneEquiv ℤ) (Finset.Ico a (a + L) : Set ℤ)
  have hcount : Nat.card (SupportedCube j
      (((Finset.Ico a (a + L)).image (scalarPiOneEquiv ℤ)) : Set (Fin 1 → ℤ))) =
      Nat.card (SupportedCube j (Finset.Ico a (a + L) : Set ℤ)) :=
    card_supportedCube_image_eq he j
  rw [hcount, Finset.card_image_of_injective _ (scalarPiOneEquiv ℤ).injective] at h
  simpa only [Fintype.card_fin, pow_one, Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicIntervalCubeComparison
namespace OAI

section

namespace Erdos3

theorem imageExtension_comap_eq_indicator {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [DecidableEq B] (φ : A →+ B) (Q : Finset A)
    (hφ : Set.InjOn φ (Q : Set A)) (f : B → ℂ) :
    imageExtension φ Q (fun x => f (φ x)) =
      fun y => f y * finiteIndicator (Q.image φ) y := by
  classical
  funext y
  by_cases hy : y ∈ Q.image φ
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [imageExtension_apply hφ _ hx]
    simp [finiteIndicator, Finset.mem_image_of_mem φ hx]
  · rw [imageExtension_eq_zero]
    · simp [finiteIndicator, hy]
    · rintro ⟨x, hx, hxy⟩
      exact hy (Finset.mem_image.mpr ⟨x, hx, hxy⟩)

theorem cyclicInterval_gowersNorm_pow {N : ℕ} [NeZero N] (a : ℤ) (len j : ℕ)
    (hshort : 2 * ((len : ℤ) - 1) < N) (f : ZMod N → ℂ) :
    gowersNorm (j + 1) (fun x => f x * finiteIndicator (cyclicInterval (a : ZMod N) len) x)
        ^ (2 ^ (j + 1)) =
      ((Nat.card (SupportedCube (j + 1) (Finset.Ico a (a + len) : Set ℤ)) : ℝ) /
        (N : ℝ) ^ (j + 2)) * finiteSupportGowersNorm (j + 1)
          (Finset.Ico a (a + len)) (fun x => f (x : ZMod N)) ^ (2 ^ (j + 1)) := by
  have he := integerInterval_reflectsPairSums N a (a + len) (by omega)
  have hh := finiteSupportGowersNorm_ambient_comparison he j
    (fun x => f ((integerCyclicMap N) x))
  rw [imageExtension_comap_eq_indicator _ _ he.injOn,
    integerInterval_image_cyclicInterval, ZMod.card] at hh
  exact hh

theorem cyclicInterval_gowersNorm_lower_pow {N : ℕ} [NeZero N]
    (a : ℤ) (len j : ℕ) [NeZero len]
    (hshort : 2 * ((len : ℤ) - 1) < N) (f : ZMod N → ℂ)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hvol : δ ≤ (len : ℝ) / N)
    (hloc : η ≤ finiteSupportGowersNorm (j + 1) (Finset.Ico a (a + len))
      (fun x => f (x : ZMod N))) :
    ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) * δ ^ (j + 2) * η ^ (2 ^ (j + 1)) ≤
      gowersNorm (j + 1) (fun x => f x * finiteIndicator (cyclicInterval (a : ZMod N) len) x)
        ^ (2 ^ (j + 1)) := by
  rw [cyclicInterval_gowersNorm_pow a len j hshort]
  have hcount := (integerInterval_cubeCount_bounds a len (j + 1)).1
  have hn : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hc : 0 ≤ (1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2) := by positivity
  have hratio : ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) * δ ^ (j + 2) ≤
      (Nat.card (SupportedCube (j + 1) (Finset.Ico a (a + len) : Set ℤ)) : ℝ) /
        (N : ℝ) ^ (j + 2) := by
    calc
      _ ≤ ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) * ((len : ℝ) / N) ^ (j + 2) := by
        gcongr
      _ = (((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) * (len : ℝ) ^ (j + 2)) /
          (N : ℝ) ^ (j + 2) := by rw [div_pow, mul_div_assoc]
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hn.le _)
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hcount
  exact mul_le_mul hratio (pow_le_pow_left₀ hη hloc _) (pow_nonneg hη _)
    (div_nonneg (Nat.cast_nonneg _) (pow_nonneg hn.le _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestDetection
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem exists_intervalNiltestDetection.{u} (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L : Type u} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      1 ≤ p → ∀ (w : Fin 1 → ℕ), (∀ i, 0 < w i) →
      ∀ (T : D.Niltest w), T.ComplexityLE p →
      ∀ (a : ℤ) (len : ℕ) [NeZero len] (f : ℤ → ℂ),
      (∀ x ∈ Finset.Ico a (a + len), ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖finiteCorrelation (Finset.Ico a (a + len)) f
        (fun x => T.eval (fun _ => x))‖ →
      Real.exp (-((p + C) ^ C)) ≤ finiteSupportGowersNorm (s + 1)
        (Finset.Ico a (a + len)) f := by
  obtain ⟨C, hC, hdet⟩ := exists_boxNiltestDetection s
  refine ⟨C, hC, ?_⟩
  intro L _ _ d _ _ _ _ D p hp w hw T hT a len hlen f hf hc
  have hunit : ∀ x ∈ translatedIntegerBox (fun _ : Fin 1 => a) (fun _ => len),
      ‖f (x 0)‖ ≤ 1 := by
    intro x hx
    exact hf (x 0) (Finset.mem_Ico.mpr ((mem_translatedIntegerBox _ _ x).mp hx 0))
  have hcorr : Real.exp (-p) ≤ ‖finiteCorrelation
      (translatedIntegerBox (fun _ : Fin 1 => a) (fun _ => len)) (fun x => f (x 0)) T.eval‖ := by
    rwa [oneDimensionalBox_correlation]
  have hp0 : 0 ≤ p := by linarith
  have hdim : (Fintype.card (Fin 1) : ℝ) ≤ p := by simpa using hp
  have hh := @hdet (Fin 1) inferInstance inferInstance L inferInstance inferInstance d
    inferInstance inferInstance inferInstance inferInstance D p hp0 hdim w hw T hT
    (fun _ => a) (fun _ => len) (fun _ => hlen) (fun x => f (x 0)) hunit hcorr
  simpa only [oneDimensionalBox_norm] using hh

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicProductDetection
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3

theorem cyclicProductNiltestDetection_zero.{u,v} :
    CyclicProductNiltestDetection.{u,v} 0 (fun p => p + p ^ 2) := by
  intro ι _ L _ _ d _ _ _ _ D p hp hι w hw T hT N _ h f hf hc
  let c : ℂ := ∏ i, (T i).eval (fun _ => 0)
  have he (x : ZMod N) : translatedCyclicProduct h (fun i n => (T i).eval (fun _ => n)) x = c := by
    unfold translatedCyclicProduct c
    apply Finset.prod_congr rfl
    intro i _
    simp only [RationalFilteredNilmanifold.Niltest.eval_step_zero (D i)]
  have hcnorm : ‖c‖ ≤ Real.exp (p ^ 2) := by
    unfold c
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : ι, Real.exp p :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => (T i).eval_budget (hT i) _)
      _ = Real.exp ((Fintype.card ι : ℝ) * p) := by
        rw [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have heq : finiteCorrelation Finset.univ f
      (translatedCyclicProduct h (fun i n => (T i).eval (fun _ => n))) =
      (𝔼 x, f x) * star c := by
    simp only [finiteCorrelation, he, ← Finset.expect_mul]
  rw [heq, norm_mul, norm_star] at hc
  have hg : Real.exp (-p) / Real.exp (p ^ 2) ≤ ‖𝔼 x, f x‖ := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    exact hc.trans (mul_le_mul_of_nonneg_left hcnorm (norm_nonneg _))
  have he' : Real.exp (-p) / Real.exp (p ^ 2) = Real.exp (-(p + p ^ 2)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rwa [he', ← gowersNorm_one] at hg

end Erdos3

end

section

open scoped TensorProduct BigOperators

namespace Erdos3

theorem exists_cyclicProductNiltestDetection_succ.{u,v} (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicProductNiltestDetection.{u,v} (s + 1) (fun p => (p + C) ^ C) := by
  obtain ⟨c, _, hdet⟩ := exists_intervalNiltestDetection (s + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_cyclicProductDetectionBudget_bound s c
  refine ⟨C, hC, ?_⟩
  intro ι _ L _ _ d _ _ _ _ D p hp hι w hw T hT N _ h f hf hc
  obtain ⟨a, hlen, hbound, hshort, hS, hcorr, hvol⟩ :=
    exists_correlating_niltest_product_piece D w hw T hT h f hf hc
  let len := intervalCutUpper (commonCyclicCuts h) N a - a.val
  let S := fun i => (T i).translate hw (fun _ => cyclicTranslationOffset (h i) a)
  change 0 < len at hlen
  let : NeZero len := ⟨hlen.ne'⟩
  let : FiniteDimensional ℚ (∀ i, L i) :=
    (RationalFilteredNilmanifold.productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, L i)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis D)
  obtain ⟨U, hU, hUeval⟩ := RationalFilteredNilmanifold.exists_product_niltest D S hp hι hS
  have hq := cyclicProductInputBudget_bounds hp
  have heval : (fun n : ℤ => U.eval (fun _ => n)) =
      (fun n => ∏ i, (S i).eval (fun _ => n)) := funext (fun n => hUeval (fun _ => n))
  have hcU : Real.exp (-cyclicProductInputBudget p) ≤
      ‖finiteCorrelation (Finset.Ico (a.val : ℤ) (a.val + len)) (fun x => f (x : ZMod N))
        (fun n => U.eval (fun _ => n))‖ := by
    rw [heval]
    exact (Real.exp_le_exp.mpr (neg_le_neg hq.2.2)).trans
      ((cyclic_product_retained_correlation (Fintype.card ι) hι).trans hcorr)
  have hlocal := hdet (RationalFilteredNilmanifold.pi D) (cyclicProductInputBudget p)
    hq.1 w hw U (hU.mono hq.2.1) (a.val : ℤ) len (fun x => f (x : ZMod N))
    (fun x _ => hf _) hcU
  have hvolume : Real.exp (-cyclicProductVolumeBudget p) ≤ (len : ℝ) / N :=
    (cyclic_product_retained_volume (Fintype.card ι) hp hι).trans hvol
  have hpow := cyclicInterval_gowersNorm_lower_pow (a.val : ℤ) len (s + 1) hshort f
    (Real.exp_nonneg (-cyclicProductVolumeBudget p))
    (Real.exp_nonneg (-((cyclicProductInputBudget p + c) ^ c))) hvolume hlocal
  have hpower : Real.exp (-cyclicProductCutoffBudget s c p) ≤
      gowersNorm (s + 2) (fun x => f x * finiteIndicator (cyclicInterval (a.val : ZMod N) len) x)
        ^ (2 ^ (s + 2)) := by
    apply (cyclic_product_cutoff_exponential s c p).trans
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc, Int.cast_natCast] at hpow ⊢
    exact hpow
  have hcut := exp_neg_le_of_pow (gowersNorm_nonneg (s + 1) _)
    (cyclicProductCutoffBudget_nonneg s c hp) (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hpower
  have htransfer := gowersNorm_transfer_cyclicInterval s f hf (a.val : ZMod N) len
    (Real.exp_pos (-cyclicProductCutoffBudget s c p))
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (cyclicProductCutoffBudget_nonneg s c hp))) hcut
  exact (Real.exp_le_exp.mpr (neg_le_neg (hbudget p hp))).trans
    ((cyclic_product_transfer_exponential s c p).trans htransfer)

theorem exists_cyclicProductNiltestDetection.{u,v} (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicProductNiltestDetection.{u,v} s (fun p => (p + C) ^ C) := by
  cases s with
  | zero =>
    refine ⟨2, le_rfl, ?_⟩
    intro ι _ L _ _ d _ _ _ _ D p hp hι w hw T hT N _ h f hf hc
    have hb : p + p ^ 2 ≤ (p + (2 : ℕ)) ^ 2 := by
      norm_num only [Nat.cast_ofNat]
      nlinarith
    exact (Real.exp_le_exp.mpr (neg_le_neg hb)).trans
      (cyclicProductNiltestDetection_zero D p hp hι w hw T hT N h f hf hc)
  | succ s => exact exists_cyclicProductNiltestDetection_succ s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicPairNiltestDetection
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem cyclic_pair_niltest_detection.{u,v}
    {s : ℕ} {F : ℝ → ℝ} (hdet : CyclicProductNiltestDetection.{u,0} s F)
    {ι : Type v} {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
    {d : ι → ℕ} [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
    [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    {p : ℝ} (hp : 2 ≤ p) (w : Fin 1 → ℕ) (hw : ∀ j, 0 < w j)
    (T : ∀ i, (D i).Niltest w) (hT : ∀ i, (T i).ComplexityLE p)
    (N : ℕ) [NeZero N] (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (i j : ι) (a : ZMod N)
    (hc : Real.exp (-p) ≤ ‖𝔼 x, f x * (T i).eval (fun _ => (x.val : ℤ)) *
      star ((T j).eval (fun _ => ((x + a).val : ℤ)))‖) :
    Real.exp (-F p) ≤ gowersNorm (s + 1) f := by
  let index : Fin 2 → ι := ![i, j]
  let D' := fun k : Fin 2 => D (index k)
  let U : ∀ k : Fin 2, (D' k).Niltest w := fun k =>
    if k = 0 then (T (index k)).conjugate else T (index k)
  have hU : ∀ k, (U k).ComplexityLE p := by
    intro k
    dsimp only [U]
    split_ifs <;> exact hT (index k)
  let shifts : Fin 2 → ZMod N := ![0, a]
  have heval (x : ZMod N) :
      translatedCyclicProduct shifts (fun k n => (U k).eval (fun _ => n)) x =
        star ((T i).eval (fun _ => (x.val : ℤ))) *
          (T j).eval (fun _ => ((x + a).val : ℤ)) := by
    simp [translatedCyclicProduct, Fin.prod_univ_two, shifts, U, D', index, add_comm]
    rfl
  have hcorr : Real.exp (-p) ≤ ‖finiteCorrelation Finset.univ f
      (translatedCyclicProduct shifts (fun k n => (U k).eval (fun _ => n)))‖ := by
    convert hc using 1
    congr 1
    unfold finiteCorrelation
    apply Finset.expect_congr rfl
    intro x _
    rw [heval]
    simp only [star_mul, star_star]
    ring
  exact hdet D' p (by linarith) (by simpa using hp) w hw U hU N shifts f hf hcorr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PositiveShiftTestingNiltests
namespace OAI

section

namespace Erdos3.PositiveShiftBasis

open scoped TensorProduct NNReal

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}

theorem testingNiltest_eval (B : PositiveShiftBasis s N q a J)
    (hk : ZMod N × Fin B.count) (x : ZMod N) :
    (B.testingNiltest hk).eval (fun _ => (x.val : ℤ)) = B.testingFamily hk x := by
  classical
  by_cases hh : hk.1 ∈ B.shifts
  · simp only [testingNiltest, testingFamily, if_pos hh,
      RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom,
      RationalFilteredNilmanifold.Niltest.evalCyclic,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  · simp only [testingNiltest, testingFamily, if_neg hh,
      RationalFilteredNilmanifold.Niltest.eval_const]

theorem testingNiltest_complexity (B : PositiveShiftBasis s N q a J)
    (hk : ZMod N × Fin B.count) : (B.testingNiltest hk).ComplexityLE (q + 2) := by
  classical
  by_cases hh : hk.1 ∈ B.shifts
  · simp only [testingNiltest, if_pos hh,
      RationalFilteredNilmanifold.Niltest.linearPullbackHom_complexityLE]
    exact (B.mode_complexity hk.1 hh hk.2).mono (by linarith)
  · simp only [testingNiltest, if_neg hh]
    refine ⟨RationalFilteredNilmanifold.GeometryComplexityLE.mono B.model B.geometry
      (by linarith), ?_⟩
    change Real.log (2 + (‖(0 : ℂ)‖₊ : ℝ) + (0 : ℝ)) ≤ q + 2
    simp only [nnnorm_zero, NNReal.coe_zero, add_zero]
    have hq : 0 ≤ q := (Nat.cast_nonneg B.dim).trans B.geometry.1
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftTestingGowers
namespace OAI

section

namespace Erdos3

theorem shift_detection_exponential_gap {p : ℝ} (hp : 2 ≤ p) :
    Real.exp (-6 * p) ≤
      Real.exp (-p) ^ 2 / (4 * Real.exp p ^ 2) - Real.exp (-6 * p) := by
  have hthree : 3 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have htwo : 8 ≤ Real.exp (2 * p) := by
    have he : Real.exp (2 * p) = Real.exp p ^ 2 := by
      simpa using Real.exp_nat_mul p 2
    rw [he]
    nlinarith
  have hratio : Real.exp (-p) ^ 2 / (4 * Real.exp p ^ 2) = Real.exp (-4 * p) / 4 := by
    calc
      _ = (Real.exp (-p) / Real.exp p) ^ 2 / 4 := by field_simp
      _ = _ := by
        rw [← Real.exp_sub, ← Real.exp_nat_mul]
        congr 2
        ring
  have hprod : Real.exp (-4 * p) = Real.exp (-6 * p) * Real.exp (2 * p) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hratio, hprod]
  nlinarith [Real.exp_pos (-6 * p)]

theorem shiftDetectionLoss_nonneg (s C : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ shiftDetectionLoss s C p := by unfold shiftDetectionLoss; positivity

theorem shift_detection_exponential_product (s C : ℕ) (p : ℝ) :
    Real.exp (-shiftDetectionLoss s C p) =
      Real.exp (-((6 * p + C) ^ C)) ^ (2 ^ (s + 1)) * Real.exp (-6 * p) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  unfold shiftDetectionLoss
  ring

theorem shiftDetectionPolynomial_eval (s C : ℕ) (p : ℝ) :
    (shiftDetectionPolynomial s C).eval₂ (Nat.castRingHom ℝ) p = shiftDetectionLoss s C p := by
  simp [shiftDetectionPolynomial, shiftDetectionLoss, Polynomial.eval₂_pow]

theorem exists_shiftDetectionLoss_fixed_power (s C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 2 ≤ p → shiftDetectionLoss s C p ≤ (p + 2) ^ D := by
  obtain ⟨D, hD, hbound⟩ := exists_natPolynomial_fixed_power_budget (shiftDetectionPolynomial s C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  simpa only [shiftDetectionPolynomial_eval] using hbound p (by linarith)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem cyclicShiftTestingDetection_of_product.{u,v} {s C : ℕ}
    (hdet : CyclicProductNiltestDetection.{u,0} s (fun p => (p + C) ^ C)) :
    CyclicShiftTestingDetection.{u,v} s (shiftDetectionLoss s C) := by
  intro ι _ L _ _ d _ _ _ _ D p hp w hw T hT N _ hunit v B hv hB hlarge
  have hp0 : 0 ≤ p := by linarith
  have hG : Real.exp (-((6 * p + C) ^ C)) ^ (2 ^ (s + 1)) *
      (Real.exp (-p) ^ 2 / (4 * Real.exp p ^ 2) - Real.exp (-6 * p)) ≤
        gowersNorm (s + 2) v ^ (2 ^ (s + 2)) := by
    apply shiftTestingSeminorm_gowers_lower s v B
      (fun i x => (T i).eval (fun _ => (x.val : ℤ)))
      (Real.exp_pos _) (Real.exp_pos _) (Real.exp_nonneg _) (Real.exp_nonneg _)
      hv hB hunit hlarge
    intro i j a f hf hc
    apply cyclic_pair_niltest_detection hdet D (p := 6 * p) (by linarith) w hw T
      (fun i => (hT i).mono (by linarith)) N f hf i j a
    simpa only [neg_mul] using hc
  apply exp_neg_le_of_pow (gowersNorm_nonneg (s + 1) v)
    (shiftDetectionLoss_nonneg s C hp0) (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
  rw [shift_detection_exponential_product]
  exact (mul_le_mul_of_nonneg_left (shift_detection_exponential_gap hp)
    (pow_nonneg (Real.exp_nonneg _) _)).trans hG

theorem exists_cyclicShiftTestingDetection.{u,v} (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicShiftTestingDetection.{u,v} s (fun p => (p + 2) ^ C) := by
  obtain ⟨c, _, hdet⟩ : ∃ c : ℕ, 2 ≤ c ∧
      CyclicProductNiltestDetection.{u,0} s (fun p => (p + c) ^ c) :=
    exists_cyclicProductNiltestDetection s
  obtain ⟨C, hC, hbudget⟩ := exists_shiftDetectionLoss_fixed_power s c
  have hraw : CyclicShiftTestingDetection.{u,v} s (shiftDetectionLoss s c) :=
    cyclicShiftTestingDetection_of_product (s := s) (C := c) (hdet := @hdet)
  refine ⟨C, hC, ?_⟩
  intro ι _ L _ _ d _ _ _ _ D p hp w hw T hT N _ hunit v B hv hB hlarge
  exact (Real.exp_le_exp.mpr (neg_le_neg (hbudget p hp))).trans
    (hraw D p hp w hw T hT N hunit v B hv hB hlarge)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem cyclic_translated_pair_niltest_detection.{u,v}
    {s : ℕ} {F : ℝ → ℝ} (hdet : CyclicProductNiltestDetection.{u,0} s F)
    {ι : Type v} {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
    {d : ι → ℕ} [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
    [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    {p : ℝ} (hp : 2 ≤ p) (w : Fin 1 → ℕ) (hw : ∀ j, 0 < w j)
    (T : ∀ i, (D i).Niltest w) (hT : ∀ i, (T i).ComplexityLE p)
    (N : ℕ) [NeZero N] (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (i j : ι) (b c : ZMod N)
    (hc : Real.exp (-p) ≤ ‖𝔼 x, f x * (T i).eval (fun _ => ((x + b).val : ℤ)) *
      star ((T j).eval (fun _ => ((x + c).val : ℤ)))‖) :
    Real.exp (-F p) ≤ gowersNorm (s + 1) f := by
  let index : Fin 2 → ι := ![i, j]
  let D' := fun k : Fin 2 => D (index k)
  let U : ∀ k : Fin 2, (D' k).Niltest w := fun k =>
    if k = 0 then (T (index k)).conjugate else T (index k)
  have hU : ∀ k, (U k).ComplexityLE p := by
    intro k
    dsimp only [U]
    split_ifs <;> exact hT (index k)
  let shifts : Fin 2 → ZMod N := ![b, c]
  have heval (x : ZMod N) :
      translatedCyclicProduct shifts (fun k n => (U k).eval (fun _ => n)) x =
        star ((T i).eval (fun _ => ((x + b).val : ℤ))) *
          (T j).eval (fun _ => ((x + c).val : ℤ)) := by
    simp [translatedCyclicProduct, Fin.prod_univ_two, shifts, U, D', index, add_comm]
    rfl
  have hcorr : Real.exp (-p) ≤ ‖finiteCorrelation Finset.univ f
      (translatedCyclicProduct shifts (fun k n => (U k).eval (fun _ => n)))‖ := by
    convert hc using 1
    congr 1
    unfold finiteCorrelation
    apply Finset.expect_congr rfl
    intro x _
    rw [heval]
    simp only [star_mul, star_star]
    ring
  exact hdet D' p (by linarith) (by simpa using hp) w hw U hU N shifts f hf hcorr

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem cyclicTranslatedShiftTestingDetection_of_product.{u,v} {s C : ℕ}
    (hdet : CyclicProductNiltestDetection.{u,0} s (fun p => (p + C) ^ C)) :
    CyclicTranslatedShiftTestingDetection.{u,v} s (shiftDetectionLoss s C) := by
  intro ι _ L _ _ d _ _ _ _ D p hp w hw T hT N _ hunit v B hv hB hlarge
  have hp0 : 0 ≤ p := by linarith
  have hG : Real.exp (-((6 * p + C) ^ C)) ^ (2 ^ (s + 1)) *
      (Real.exp (-p) ^ 2 / (4 * Real.exp p ^ 2) - Real.exp (-6 * p)) ≤
        gowersNorm (s + 2) v ^ (2 ^ (s + 2)) := by
    apply shiftTestingSeminorm_gowers_lower s v B
      (translatedTestFamily (fun i x => (T i).eval (fun _ => (x.val : ℤ))))
      (Real.exp_pos _) (Real.exp_pos _) (Real.exp_nonneg _) (Real.exp_nonneg _)
      hv hB (translatedTestFamily_norm_le_one _ hunit) hlarge
    intro i j a f hf hc
    apply cyclic_translated_pair_niltest_detection hdet D (p := 6 * p) (by linarith) w hw T
      (fun i => (hT i).mono (by linarith)) N f hf i.2 j.2 i.1 (a + j.1)
    simpa only [neg_mul, translatedTestFamily, add_assoc] using hc
  apply exp_neg_le_of_pow (gowersNorm_nonneg (s + 1) v)
    (shiftDetectionLoss_nonneg s C hp0) (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
  rw [shift_detection_exponential_product]
  exact (mul_le_mul_of_nonneg_left (shift_detection_exponential_gap hp)
    (pow_nonneg (Real.exp_nonneg _) _)).trans hG

theorem exists_cyclicTranslatedShiftTestingDetection.{u,v} (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicTranslatedShiftTestingDetection.{u,v} s (fun p => (p + 2) ^ C) := by
  obtain ⟨c, _, hdet⟩ : ∃ c : ℕ, 2 ≤ c ∧
      CyclicProductNiltestDetection.{u,0} s (fun p => (p + c) ^ c) :=
    exists_cyclicProductNiltestDetection s
  obtain ⟨C, hC, hbudget⟩ := exists_shiftDetectionLoss_fixed_power s c
  have hraw : CyclicTranslatedShiftTestingDetection.{u,v} s (shiftDetectionLoss s c) :=
    cyclicTranslatedShiftTestingDetection_of_product (s := s) (C := c) (hdet := @hdet)
  refine ⟨C, hC, ?_⟩
  intro ι _ L _ _ d _ _ _ _ D p hp w hw T hT N _ hunit v B hv hB hlarge
  exact (Real.exp_le_exp.mpr (neg_le_neg (hbudget p hp))).trans
    (hraw D p hp w hw T hT N hunit v B hv hB hlarge)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u

theorem shiftTestingSeminorm_eq_zero_of_isEmpty {G ι : Type*}
    [AddCommGroup G] [Fintype G] [IsEmpty ι] (B : G → ℂ) (T : ι → G → ℂ) (v : G → ℂ) :
    shiftTestingSeminorm B T v = 0 := by
  have h0 : ∀ h : G, shiftTestSeminormAt B T h = 0 := fun h => by
    rw [shiftTestSeminormAt, iSup_of_empty', Seminorm.sSup_empty, Seminorm.bot_eq_zero]
  change Finset.univ.expect (fun h => shiftTestSeminormAt B T h v) = 0
  simp [h0]

namespace PositiveShiftBasis

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_testingFamily_gowers_detection (s : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{u} s N q a J) {p : ℝ}, 2 ≤ p → q + 2 ≤ p →
      ∀ v W : ZMod N → ℂ, (∀ x, ‖v x‖ ≤ 1) → (∀ x, ‖W x‖ ≤ Real.exp p) →
      (Real.exp (-p) ≤ shiftTestingSeminorm W B.testingFamily v →
        Real.exp (-((p + 2) ^ A)) ≤ gowersNorm (s + 2) v) ∧
      (Real.exp (-p) ≤ shiftTestingSeminorm W (translatedTestFamily B.testingFamily) v →
        Real.exp (-((p + 2) ^ A)) ≤ gowersNorm (s + 2) v) := by
  obtain ⟨A₁, hA₁, h₁⟩ : ∃ A : ℕ, 2 ≤ A ∧
      CyclicShiftTestingDetection.{u,0} s (fun p => (p + 2) ^ A) :=
    exists_cyclicShiftTestingDetection s
  obtain ⟨A₂, _, h₂⟩ : ∃ A : ℕ, 2 ≤ A ∧
      CyclicTranslatedShiftTestingDetection.{u,0} s (fun p => (p + 2) ^ A) :=
    exists_cyclicTranslatedShiftTestingDetection s
  refine ⟨max A₁ A₂, hA₁.trans (le_max_left _ _), ?_⟩
  intro N _ q a J B p hp hqp v W hv hW
  cases isEmpty_or_nonempty (ZMod N × Fin B.count) with
  | inl he =>
    let := he
    constructor <;> intro hlarge
    · rw [shiftTestingSeminorm_eq_zero_of_isEmpty] at hlarge
      exact False.elim ((not_le_of_gt (Real.exp_pos _)) hlarge)
    · rw [shiftTestingSeminorm_eq_zero_of_isEmpty] at hlarge
      exact False.elim ((not_le_of_gt (Real.exp_pos _)) hlarge)
  | inr he =>
    let := he
    have hT (i : ZMod N × Fin B.count) : (B.testingNiltest i).ComplexityLE p :=
      (B.testingNiltest_complexity i).mono hqp
    have hunit (i : ZMod N × Fin B.count) (x : ZMod N) :
        ‖(B.testingNiltest i).eval (fun _ => (x.val : ℤ))‖ ≤ 1 := by
      rw [B.testingNiltest_eval]
      exact B.testingFamily_norm_le i x
    have hbase : 1 ≤ p + 2 := by linarith
    constructor
    · intro hlarge
      apply (Real.exp_le_exp.mpr (neg_le_neg
        (pow_le_pow_right₀ hbase (le_max_left A₁ A₂)))).trans
      exact h₁ (ι := ZMod N × Fin B.count) (L := fun _ => B.L)
        (d := fun _ => B.dim) (fun _ => B.model) p hp (fun _ => 1)
        (fun _ => Nat.zero_lt_one) B.testingNiltest hT N hunit v W hv hW
        (by simpa only [B.testingNiltest_eval] using hlarge)
    · intro hlarge
      apply (Real.exp_le_exp.mpr (neg_le_neg
        (pow_le_pow_right₀ hbase (le_max_right A₁ A₂)))).trans
      exact h₂ (ι := ZMod N × Fin B.count) (L := fun _ => B.L)
        (d := fun _ => B.dim) (fun _ => B.model) p hp (fun _ => 1)
        (fun _ => Nat.zero_lt_one) B.testingNiltest hT N hunit v W hv hW
        (by simpa only [B.testingNiltest_eval] using hlarge)

end PositiveShiftBasis
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AxisCompression
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_native_detector_of_gowers (s : ℕ) (hs : 1 ≤ s) (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {u : ℝ}, 2 ≤ u →
      ∀ (X : Seminorm ℂ (ZMod N → ℂ)) (K M tau : ℝ),
      K / tau ≤ Real.exp u → Real.exp (-u) ≤ tau / M ^ 2 →
      (∀ v : ZMod N → ℂ, (∀ x, ‖v x‖ ≤ 1) →
        Real.exp (-(2 * u)) ≤ X v →
        Real.exp (-((2 * u + 2) ^ A)) ≤ gowersNorm (s + 1) v) →
      NativeModelDetector s N ((u + C) ^ C) X K M
        (Real.exp (-((u + C) ^ C))) tau := by
  obtain ⟨B, _, hinverse⟩ := exists_cyclicNativeInverse_positive s hs
  let Y : Polynomial ℕ := Polynomial.X
  let P := (2 * Y + 2) ^ A + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ u hu X K M tau hcap hthreshold hdetect psi hpsi hlarge
  let v : ZMod N → ℂ := fun x => (Real.exp (-u) : ℂ) * psi x
  have hu0 : 0 ≤ u := by linarith
  have hv : ∀ x, ‖v x‖ ≤ 1 := by
    intro x
    calc
      _ = Real.exp (-u) * ‖psi x‖ := by
        simp only [v, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-u) * (K / tau) := mul_le_mul_of_nonneg_left (hpsi x) (Real.exp_nonneg _)
      _ ≤ Real.exp (-u) * Real.exp u := mul_le_mul_of_nonneg_left hcap (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hXv : X v = Real.exp (-u) * X psi := by
    change X ((Real.exp (-u) : ℂ) • psi) = _
    rw [map_smul_eq_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hnorm : Real.exp (-(2 * u)) ≤ X v := by
    rw [hXv]
    calc
      _ = Real.exp (-u) * Real.exp (-u) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-u) * (tau / M ^ 2) := mul_le_mul_of_nonneg_left hthreshold (Real.exp_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hlarge (Real.exp_nonneg _)
  let q := (2 * u + 2) ^ A + 2
  have hq : 2 ≤ q := by
    dsimp [q]
    have hp := pow_nonneg (by linarith : 0 ≤ 2 * u + 2) A
    linarith
  have hG : Real.exp (-q) ≤ gowersNorm (s + 1) v :=
    (Real.exp_le_exp.mpr (by dsimp [q]; linarith)).trans (hdetect v hv hnorm)
  obtain ⟨g, ⟨G⟩, hg⟩ := hinverse hq v hv hG
  have hcost : (q + B) ^ B ≤ (u + C) ^ C := by
    simpa [Y, P, q, Polynomial.eval₂_pow] using hbudget u hu0
  have hmean : ‖𝔼 x, v x * star (g x)‖ = Real.exp (-u) * ‖𝔼 x, psi x * star (g x)‖ := by
    have heq : (𝔼 x, v x * star (g x)) = (Real.exp (-u) : ℂ) * (𝔼 x, psi x * star (g x)) := by
      simp only [v, Finset.mul_expect, mul_assoc]
    rw [heq, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hc : Real.exp (-u) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  refine ⟨g, ⟨{ G with complexity := G.complexity.mono hcost }⟩, ?_⟩
  apply (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans
  apply hg.trans
  rw [hmean]
  exact mul_le_of_le_one_left (norm_nonneg _) hc

end Erdos3

end

section

namespace Erdos3.PositiveShiftBasis

universe u

theorem exists_testingFamily_native_detectors (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{u} s N q a J) {u : ℝ}, 2 ≤ u → q + 2 ≤ u →
      ∀ (W : ZMod N → ℂ), (∀ x, ‖W x‖ ≤ Real.exp u) →
      ∀ K M tau : ℝ, K / tau ≤ Real.exp u → Real.exp (-u) ≤ tau / M ^ 2 →
      NativeModelDetector (s + 1) N ((u + C) ^ C)
        (shiftTestingSeminorm W B.testingFamily) K M (Real.exp (-((u + C) ^ C))) tau ∧
      NativeModelDetector (s + 1) N ((u + C) ^ C)
        (shiftTestingSeminorm W (translatedTestFamily B.testingFamily))
        K M (Real.exp (-((u + C) ^ C))) tau := by
  obtain ⟨A, _, hGowers⟩ := exists_testingFamily_gowers_detection.{u} s
  obtain ⟨C, hC, hnative⟩ := exists_native_detector_of_gowers (s + 1) (by omega) A
  refine ⟨C, hC, ?_⟩
  intro N _ q a J B u hu hqu W hW K M tau hcap hthreshold
  have hW₂ (x) : ‖W x‖ ≤ Real.exp (2 * u) :=
    (hW x).trans (Real.exp_le_exp.mpr (by linarith))
  constructor
  · apply hnative hu (shiftTestingSeminorm W B.testingFamily) K M tau hcap hthreshold
    intro v hv hlarge
    exact (hGowers B (by linarith) (by linarith) v W hv hW₂).1 hlarge
  · apply hnative hu (shiftTestingSeminorm W (translatedTestFamily B.testingFamily))
      K M tau hcap hthreshold
    intro v hv hlarge
    exact (hGowers B (by linarith) (by linarith) v W hv hW₂).2 hlarge

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open NativeModelingNumerics

universe u

theorem exists_bounded_testingFamily_native_detectors (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{u} s N q a J) {p : ℝ}, 2 ≤ p → q ≤ p →
      ∀ b : ZMod N → ℂ, (∀ x, ‖b x‖ ≤ Real.exp p) →
      ∃ p₁ p₂ beta₁ beta₂ : ℝ,
        p ≤ (p + C) ^ C ∧ 2 ≤ p₁ ∧ 2 ≤ p₂ ∧ p₁ ≤ (p + C) ^ C ∧ p₂ ≤ (p + C) ^ C ∧
        0 < beta₁ ∧ 0 < beta₂ ∧
        2 / beta₁ ≤ Real.exp ((p + C) ^ C) ∧ 2 / beta₂ ≤ Real.exp ((p + C) ^ C) ∧
        (1 + 4 * Real.exp p ^ 2 /
          (beta₁ ^ 2 * (Real.exp (-(2 * q + 2)) / 4) ^ 2)) *
        (1 + 4 / (beta₂ ^ 2 *
          (Real.exp (-(2 * q + 2)) * beta₁ / 8) ^ 2)) ≤ Real.exp ((p + C) ^ C) ∧
        NativeModelDetector (s + 1) N p₁ (shiftTestingSeminorm b B.testingFamily)
          (Real.exp p) (Real.exp (p + 2)) beta₁ (Real.exp (-(2 * q + 2)) / 4) ∧
        (∀ f ∈ nativeCyclicFunctions (s + 1) N p₁,
          NativeModelDetector (s + 1) N p₂
            (shiftTestingSeminorm f (translatedTestFamily B.testingFamily))
            1 (Real.exp p) beta₂ (Real.exp (-(2 * q + 2)) * beta₁ / 8)) := by
  obtain ⟨D, hD, hdetector⟩ := exists_testingFamily_native_detectors.{u} s
  let Y : Polynomial ℕ := Polynomial.X
  let R := (8 * Y + 8 + Polynomial.C D) ^ D
  let S := (8 * Y + 8 + R + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (1000 * (Y + S + 2))
  refine ⟨C, hC, ?_⟩
  intro N _ q a J B p hp hqp b hb
  let u₁ := 8 * p + 8
  let p₁ := (u₁ + D) ^ D
  let p₂ := (u₁ + p₁ + D) ^ D
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hu₁ : 2 ≤ u₁ := by dsimp [u₁]; linarith
  have hbase : 1 ≤ u₁ + D := by linarith
  have hp₁base : u₁ + D ≤ p₁ := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by omega : 1 ≤ D)
  have hp₁ : 2 ≤ p₁ := by linarith
  have hp₁₂ : p₁ ≤ p₂ := by
    change (u₁ + (D : ℝ)) ^ D ≤ (u₁ + p₁ + D) ^ D
    exact pow_le_pow_left₀ (by linarith) (by linarith) D
  have hp₂ : 2 ≤ p₂ := hp₁.trans hp₁₂
  have hq : 0 ≤ q := (Nat.cast_nonneg B.dim).trans B.geometry.1
  have hcost : 1000 * (p + p₂ + 2) ≤ (p + C) ^ C := by
    simpa [Y, R, S, p₁, p₂, u₁, Polynomial.eval₂_pow] using hbudget p hp0
  have hpcost : p ≤ (p + C) ^ C := by linarith
  have hp₁cost : p₁ + 2 ≤ (p + C) ^ C := by linarith
  have hp₂cost : p₂ + 2 ≤ (p + C) ^ C := by linarith
  obtain ⟨hcap₁, hthreshold₁, hcap₂, hthreshold₂⟩ :=
    sequential_thresholds (r := p₁) hp hqp
  refine ⟨p₁, p₂, Real.exp (-p₁), Real.exp (-p₂), hpcost, hp₁, hp₂,
    by linarith, by linarith, Real.exp_pos _, Real.exp_pos _, ?_, ?_, ?_, ?_, ?_⟩
  · exact (coefficient_bound p₁).trans (Real.exp_le_exp.mpr hp₁cost)
  · exact (coefficient_bound p₂).trans (Real.exp_le_exp.mpr hp₂cost)
  · exact (length_product_bound hp hq hqp (by linarith) hp₁₂).trans (Real.exp_le_exp.mpr hcost)
  · exact (hdetector B hu₁ (by dsimp [u₁]; linarith) b
      (fun x => (hb x).trans (Real.exp_le_exp.mpr (by dsimp [u₁]; linarith)))
      (Real.exp p) (Real.exp (p + 2)) (Real.exp (-(2 * q + 2)) / 4)
      hcap₁ hthreshold₁).1
  · intro f hf
    have hu₂ : 2 ≤ u₁ + p₁ := by linarith
    have hfunit (x) : ‖f x‖ ≤ Real.exp (u₁ + p₁) :=
      (nativeCyclicFunctions_norm hf x).trans (Real.one_le_exp_iff.mpr (by linarith))
    exact (hdetector B hu₂ (by dsimp [u₁]; linarith) f hfunit
      1 (Real.exp p) (Real.exp (-(2 * q + 2)) * Real.exp (-p₁) / 8)
      hcap₂ hthreshold₂).2

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u

theorem CyclicNiltestUpperComparison.mono_budget
    {degree N : ℕ} [NeZero N] {P Q epsilon delta : ℝ} {f g : ZMod N → ℝ}
    (h : CyclicNiltestUpperComparison.{u} degree N Q epsilon f g)
    (hPQ : P ≤ Q) (hdelta : epsilon ≤ delta) :
    CyclicNiltestUpperComparison.{u} degree N P delta f g := by
  intro L _ _ s dim _ _ _ _ D hs T hT hcomp
  exact (h D hs T hT (hcomp.mono hPQ)).trans hdelta

theorem cyclic_difference_norm_bound {N : ℕ} [NeZero N] {p epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) (f g : ZMod N → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ Real.exp p) (x : ZMod N) :
    ‖((f x - (1 + epsilon) * g x : ℝ) : ℂ)‖ ≤ Real.exp (p + 2) := by
  have hm0 : 0 ≤ (1 + epsilon) * g x := mul_nonneg (by linarith) (hg x).1
  have hm : (1 + epsilon) * g x ≤ 2 * Real.exp p :=
    (mul_le_mul_of_nonneg_right (by linarith : 1 + epsilon ≤ 2) (hg x).1).trans
      (mul_le_mul_of_nonneg_left (hg x).2 (by norm_num))
  have hnorm : |f x - (1 + epsilon) * g x| ≤ 2 * Real.exp p := by
    rw [abs_le]
    constructor <;> linarith [(hf x).1, (hf x).2, Real.exp_pos p]
  rw [Complex.norm_real, Real.norm_eq_abs]
  apply hnorm.trans
  exact NativeModelingNumerics.mul_exp_le_exp
    (by linarith [Real.add_one_le_exp (2 : ℝ)]) le_rfl

namespace PositiveShiftBasis

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_bounded_native_contradiction_s2_oai (s c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {q : ℝ} {f g J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f n - (1 + epsilon) * g n) J)
      (w : Fin B.dim → ℕ),
      (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
      ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Odd N → Real.exp ((p + C) ^ C) ≤ N →
      (∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p) →
      (∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p) →
      (∀ n, 0 ≤ J n ∧ J n ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} (s + 2) N ((p + C) ^ C)
        (Real.exp (-((p + C) ^ C))) f g → False := by
  obtain ⟨D, _, hdetectors⟩ := exists_bounded_testingFamily_native_detectors (s + 1)
  obtain ⟨E, _, hcontra⟩ := exists_native_detector_contradiction_s2 s c hc hepsilon hepsilon1 hshift
  let Y : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Y + Polynomial.C D) ^ D + Polynomial.C E) ^ E)
  refine ⟨C, hC, ?_⟩
  intro N _ q f g J B w hw p hp hqp hodd hN hf hg hJ hcompare
  have hJnorm (x) : ‖(J x : ℂ)‖ ≤ Real.exp p := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hJ x).1] using (hJ x).2
  obtain ⟨p₁, p₂, beta₁, beta₂, hpwide, hp₁, hp₂, hp₁wide, hp₂wide,
    hbeta₁, hbeta₂, hcoeff₁, hcoeff₂, hlength, hdet₁, hdet₂⟩ :=
    hdetectors B hp hqp (fun x => (J x : ℂ)) hJnorm
  have hcost : ((p + D) ^ D + E) ^ E ≤ (p + C) ^ C := by
    simpa [Y, Polynomial.eval₂_pow] using hbudget p (by linarith)
  have hcap (v : ZMod N → ℝ) (hv : ∀ x, 0 ≤ v x ∧ v x ≤ Real.exp p) :
      ∀ x, 0 ≤ v x ∧ v x ≤ Real.exp ((p + D) ^ D) :=
    fun x => ⟨(hv x).1, (hv x).2.trans (Real.exp_le_exp.mpr hpwide)⟩
  exact hcontra B w hw (hp.trans hpwide) hp₁ hp₂ (hqp.trans hpwide) hp₁wide hp₂wide
    (Real.exp_pos _) (Real.exp_pos _) hbeta₁ hbeta₂
    (cyclic_difference_norm_bound hepsilon hepsilon1 f g hf hg) hJnorm
    hcoeff₁ hcoeff₂ hlength hdet₁ hdet₂ hodd
    ((Real.exp_le_exp.mpr hcost).trans hN) (hcap f hf) (hcap g hg) (hcap J hJ)
    (hcompare.mono_budget hcost (Real.exp_le_exp.mpr (neg_le_neg hcost)))

end PositiveShiftBasis
end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.PositiveShiftBasis.exists_bounded_native_contradiction_s2_oai := @OAI.Erdos3.PositiveShiftBasis.exists_bounded_native_contradiction_s2_oai
