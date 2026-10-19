-- Prove2me | solution 1 for OAI.Erdos3.PositiveShiftBasis.exists_native_detector_contradiction_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:17:59.588991+00:00
-- url     : https://prove2.me/submissions/ed414856-dd77-47af-96a6-c64b6fc0b6c8

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B207
import Definitions.Def_OAIE3v2B230
import Theorems.Thm_OAI_Erdos3_PositiveShiftBasis_exists_factored_positive_shift_contradiction_s2
import Theorems.Thm_OAI_Erdos3_PositiveShiftBasis_exists_prescribed_lower_inputs_s2
import Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_anchored_option_mode_factorization_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitExpansionCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem two_site_model_identity {G I : Type*} {J : I → Type*}
    [AddCommGroup G] [Fintype G] [Fintype I] [∀ i, Fintype (J i)]
    (a b ea U : G → ℂ) (Q : I → G → ℂ) (R : ∀ i, J i → G → ℂ)
    (eb : I → G → ℂ) (c : I → ℂ) (d : ∀ i, J i → ℂ)
    (ha : ∀ n, a n = (∑ i, c i * Q i n) + ea n)
    (hb : ∀ i n, b n = (∑ j, d i j * R i j n) + eb i n) (h : G) :
    (𝔼 n, U n * a n * b (n + h)) =
      (∑ i, ∑ j, (c i * d i j) * (𝔼 n, U n * Q i n * R i j (n + h))) +
      (𝔼 n, U n * ea n * b (n + h)) +
      (∑ i, c i * (𝔼 n, U n * Q i n * eb i (n + h))) := by
  have hpoint (n : G) : U n * a n * b (n + h) =
      (∑ i, ∑ j, (c i * d i j) * (U n * Q i n * R i j (n + h))) +
      U n * ea n * b (n + h) + (∑ i, c i * (U n * Q i n * eb i (n + h))) := by
    rw [ha n]
    calc
      _ = (∑ i, c i * (U n * Q i n * b (n + h))) + U n * ea n * b (n + h) := by
        simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, ((∑ j, (c i * d i j) * (U n * Q i n * R i j (n + h))) +
          c i * (U n * Q i n * eb i (n + h)))) + U n * ea n * b (n + h) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [hb i (n + h)]
        simp only [mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [Finset.sum_add_distrib]; ring
  simp_rw [hpoint, Finset.expect_add_distrib, Finset.expect_sum_comm, ← Finset.mul_expect]

theorem two_site_model_error_bound {G I : Type*} {J : I → Type*}
    [AddCommGroup G] [Fintype G] [Fintype I] [∀ i, Fintype (J i)]
    (a b ea U : G → ℂ) (Q : I → G → ℂ) (R : ∀ i, J i → G → ℂ)
    (eb : I → G → ℂ) (c : I → ℂ) (d : ∀ i, J i → ℂ)
    (ha : ∀ n, a n = (∑ i, c i * Q i n) + ea n)
    (hb : ∀ i n, b n = (∑ j, d i j * R i j n) + eb i n)
    (h : G) {A : ℝ} {B : I → ℝ}
    (hfirst : ‖𝔼 n, U n * ea n * b (n + h)‖ ≤ A)
    (hsecond : ∀ i, ‖𝔼 n, U n * Q i n * eb i (n + h)‖ ≤ B i) :
    ‖(𝔼 n, U n * a n * b (n + h)) -
      (∑ i, ∑ j, (c i * d i j) * (𝔼 n, U n * Q i n * R i j (n + h)))‖ ≤
        A + ∑ i, ‖c i‖ * B i := by
  rw [two_site_model_identity a b ea U Q R eb c d ha hb h]
  rw [show ∀ x y z : ℂ, x + y + z - x = y + z by intros; ring]
  apply (norm_add_le _ _).trans
  apply add_le_add hfirst
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hsecond i) (norm_nonneg _)

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

theorem weightedModelError_nonneg {G I : Type*} [Fintype I]
    (c : I → ℂ) (ea : G → ℝ) (eb : I → G → ℝ)
    (ha : ∀ h, 0 ≤ ea h) (hb : ∀ i h, 0 ≤ eb i h) (h : G) :
    0 ≤ weightedModelError c ea eb h := by
  exact add_nonneg (ha h) (Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hb i h)))

theorem weightedModelError_mean_le {G I : Type*} [Fintype G] [Fintype I]
    (c : I → ℂ) (ea : G → ℝ) (eb : I → G → ℝ) {A : ℝ} {B : I → ℝ}
    (ha : (𝔼 h, ea h) ≤ A) (hb : ∀ i, (𝔼 h, eb i h) ≤ B i) :
    (𝔼 h, weightedModelError c ea eb h) ≤ A + ∑ i, ‖c i‖ * B i := by
  simp only [weightedModelError, Finset.expect_add_distrib, Finset.expect_sum_comm,
    ← Finset.mul_expect]
  exact add_le_add ha (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _)))

theorem exists_large_good_error_set {G : Type*} [Fintype G] [Nonempty G]
    (H : Finset G) (err : G → ℝ) {sigma delta : ℝ} (hsigma : 0 < sigma) (hdelta : 0 < delta)
    (herr : ∀ h, 0 ≤ err h) (hH : sigma * Fintype.card G ≤ (H.card : ℝ))
    (hmean : (𝔼 h, err h) ≤ sigma * delta / 4) :
    ∃ S : Finset G, S ⊆ H ∧ S.Nonempty ∧
      sigma / 2 * Fintype.card G ≤ (S.card : ℝ) ∧ ∀ h ∈ S, err h ≤ delta / 2 := by
  classical
  let bad := H.filter (fun h => delta / 2 < err h)
  have hbadH : bad ⊆ H := Finset.filter_subset _ _
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ h, err h) ≤ sigma * delta / 4 * Fintype.card G := by
    exact (div_le_iff₀ hcard).mp (by simpa only [Fintype.expect_eq_sum_div_card] using hmean)
  have hbad : (bad.card : ℝ) * (delta / 2) ≤ sigma * delta / 4 * Fintype.card G := by
    calc
      _ = ∑ _h ∈ bad, delta / 2 := by simp
      _ ≤ ∑ h ∈ bad, err h := Finset.sum_le_sum (fun h hh => (Finset.mem_filter.mp hh).2.le)
      _ ≤ ∑ h, err h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun h _ _ => herr h)
      _ ≤ _ := hsum
  have hbadCard : (bad.card : ℝ) ≤ sigma / 2 * Fintype.card G := by
    apply (mul_le_mul_iff_left₀ (show 0 < delta / 2 by positivity)).mp
    exact hbad.trans_eq (by ring)
  have hgood : sigma / 2 * Fintype.card G ≤ ((H \ bad).card : ℝ) := by
    rw [Finset.cast_card_sdiff hbadH]
    linarith
  have hgoodPos : (0 : ℝ) < (H \ bad).card :=
    (mul_pos (by positivity) hcard).trans_le hgood
  refine ⟨H \ bad, Finset.sdiff_subset, Finset.card_pos.mp (by exact_mod_cast hgoodPos), hgood, ?_⟩
  intro h hh
  by_contra hlarge
  exact (Finset.mem_sdiff.mp hh).2 (Finset.mem_filter.mpr
    ⟨(Finset.mem_sdiff.mp hh).1, lt_of_not_ge hlarge⟩)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_fixed_dependent_choices {G K : Type*} {P : K → Type*}
    [Fintype K] [∀ k, Fintype (P k)]
    (H : Finset G) (hH : H.Nonempty) (rel : ∀ (_ : G) (k : K), P k → Prop)
    (hchoice : ∀ h ∈ H, ∀ k, ∃ p, rel h k p) {R : ℝ}
    (hcount : ∀ k, (Fintype.card (P k) : ℝ) ≤ Real.exp R) :
    ∃ (q : ∀ k, P k) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-R * Fintype.card K) * H.card ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, rel h k (q k) := by
  classical
  choose choices hchoices using hchoice
  obtain ⟨h0, hh0⟩ := hH
  have hH : H.Nonempty := ⟨h0, hh0⟩
  let code : G → (∀ k, P k) := fun h => if hh : h ∈ H then choices h hh else choices h0 hh0
  have hcode (h : G) (hh : h ∈ H) (k : K) : rel h k (code h k) := by
    simpa [code, hh] using hchoices h hh k
  have hcodeCount : (((Set.univ : Set (∀ k, P k)).ncard : ℕ) : ℝ) ≤
      Real.exp (R * Fintype.card K) := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_pi, Nat.cast_prod]
    calc
      _ ≤ ∏ _k : K, Real.exp R :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun k _ => hcount k)
      _ = (Real.exp R) ^ Fintype.card K := by simp
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨q, _, S, hsub, hSn, hconst, hsize⟩ := exists_exponential_constant_fiber
    H hH code Set.univ Set.finite_univ (fun _ _ => Set.mem_univ _) hcodeCount
  refine ⟨q, S, hsub, hSn, ?_, ?_⟩
  · simpa only [neg_mul] using hsize
  · intro h hh k
    rw [← hconst h hh]
    exact hcode h (hsub hh) k

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

theorem shiftTestingSeminorm_apply (B : G → ℂ) (T : ι → G → ℂ) {M : ℝ}
    (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (v : G → ℂ) :
    shiftTestingSeminorm B T v =
      𝔼 h, ⨆ i, ‖𝔼 x, v x * (B (x + h) * T i x)‖ := by
  change (𝔼 h, shiftTestSeminormAt B T h v) = _
  simp_rw [shiftTestSeminormAt_apply B T hB hT]

theorem shiftTestingSeminorm_le [Nonempty ι]
    (B : G → ℂ) (T : ι → G → ℂ) {M : ℝ}
    (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (v : G → ℂ) :
    shiftTestingSeminorm B T v ≤ M * (𝔼 x, ‖v x‖) := by
  rw [shiftTestingSeminorm_apply B T hB hT]
  apply Finset.expect_le Finset.univ_nonempty
  intro h _
  apply ciSup_le
  intro i
  apply functionCorrelationSeminorm_le
  intro x
  rw [norm_mul]
  exact ((mul_le_mul_of_nonneg_left (hT i x) (norm_nonneg _)).trans_eq
    (mul_one _)).trans (hB _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem shiftTestingSeminorm_le_of_nonneg {G ι : Type*} [AddCommGroup G] [Fintype G]
    (B : G → ℂ) (T : ι → G → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (v : G → ℂ) :
    shiftTestingSeminorm B T v ≤ M * (𝔼 x, ‖v x‖) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    let := h
    have hz : shiftTestingSeminorm B T v = 0 := by
      have h0 : ∀ h : G, shiftTestSeminormAt B T h = 0 := fun h => by
        rw [shiftTestSeminormAt, iSup_of_empty', Seminorm.sSup_empty, Seminorm.bot_eq_zero]
      change Finset.univ.expect (fun h => shiftTestSeminormAt B T h v) = 0
      simp [h0]
    rw [hz]
    exact mul_nonneg hM (Finset.expect_nonneg (fun x _ => norm_nonneg (v x)))
  | inr h =>
    let := h
    exact shiftTestingSeminorm_le B T hB hT v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G ι : Type*} [AddCommGroup G]

theorem translatedTestFamily_norm_le_one (T : ι → G → ℂ)
    (hT : ∀ i x, ‖T i x‖ ≤ 1) (p : G × ι) (x : G) :
    ‖translatedTestFamily T p x‖ ≤ 1 := hT _ _

variable [Fintype G]

theorem correlation_le_shiftTestSeminormAt (B v : G → ℂ) (T : ι → G → ℂ)
    {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (h : G) (i : ι) :
    ‖𝔼 x, v x * (B (x + h) * T i x)‖ ≤ shiftTestSeminormAt B T h v := by
  rw [shiftTestSeminormAt_apply B T hB hT]
  exact le_ciSup (Seminorm.bddAbove_range_iff.mp
    (shiftTestSeminormAt_bddAbove B T hB hT h) v) i

theorem first_model_error_le_shiftTest (B v : G → ℂ) (T : ι → G → ℂ)
    {M : ℝ} (hB : ∀ x, ‖B x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (h : G) (i : ι) :
    ‖𝔼 x, T i x * v x * B (x + h)‖ ≤ shiftTestSeminormAt B T h v := by
  have heq : (𝔼 x, T i x * v x * B (x + h)) = 𝔼 x, v x * (B (x + h) * T i x) := by
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [heq]
  exact correlation_le_shiftTestSeminormAt B v T hB hT h i

theorem second_model_error_le_shiftTest (Q v : G → ℂ) (T : ι → G → ℂ)
    {M : ℝ} (hQ : ∀ x, ‖Q x‖ ≤ M) (hT : ∀ i x, ‖T i x‖ ≤ 1) (h : G) (i : ι) :
    ‖𝔼 x, T i x * Q x * v (x + h)‖ ≤
      shiftTestSeminormAt Q (translatedTestFamily T) (-h) v := by
  have heq : (𝔼 x, T i x * Q x * v (x + h)) =
      𝔼 y, v y * (Q (y + -h) * translatedTestFamily T (-h, i) y) := by
    apply Fintype.expect_equiv (Equiv.addRight h)
    intro x
    simp only [Equiv.coe_addRight, translatedTestFamily, add_neg_cancel_right]
    ring
  rw [heq]
  exact correlation_le_shiftTestSeminormAt Q v (translatedTestFamily T) hQ
    (translatedTestFamily_norm_le_one T hT) (-h) (-h, i)

theorem mean_negated_shiftTest (B v : G → ℂ) (T : ι → G → ℂ) :
    (𝔼 h, shiftTestSeminormAt B T (-h) v) = shiftTestingSeminorm B T v := by
  change (𝔼 h, shiftTestSeminormAt B T (-h) v) = 𝔼 h, shiftTestSeminormAt B T h v
  apply Fintype.expect_equiv (Equiv.neg G)
  intro h
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_model_partner {G I : Type*} {J : I → Type*}
    [AddCommGroup G] [Fintype G] [Fintype I] [∀ i, Fintype (J i)]
    (a b ea U : G → ℂ) (Q : I → G → ℂ) (R : ∀ i, J i → G → ℂ)
    (eb : I → G → ℂ) (c : I → ℂ) (d : ∀ i, J i → ℂ)
    (ha : ∀ n, a n = (∑ i, c i * Q i n) + ea n)
    (hb : ∀ i n, b n = (∑ j, d i j * R i j n) + eb i n)
    (h : G) {A C D delta : ℝ} {B : I → ℝ}
    (hdelta : 0 < delta) (hC : 0 < C) (hD : 0 < D)
    (hc : (∑ i, ‖c i‖) ≤ C) (hd : ∀ i, (∑ j, ‖d i j‖) ≤ D)
    (hfirst : ‖𝔼 n, U n * ea n * b (n + h)‖ ≤ A)
    (hsecond : ∀ i, ‖𝔼 n, U n * Q i n * eb i (n + h)‖ ≤ B i)
    (herror : A + ∑ i, ‖c i‖ * B i ≤ delta / 2)
    (hcorr : delta ≤ ‖𝔼 n, U n * a n * b (n + h)‖) :
    ∃ i j, (delta / 2) / (C * D) ≤ ‖𝔼 n, U n * Q i n * R i j (n + h)‖ := by
  apply exists_large_weighted_pair c d
    (fun i j => 𝔼 n, U n * Q i n * R i j (n + h)) (by positivity) hC hD hc hd
  have herr := (two_site_model_error_bound a b ea U Q R eb c d ha hb h hfirst hsecond).trans herror
  have htri := norm_add_le
    ((𝔼 n, U n * a n * b (n + h)) -
      (∑ i, ∑ j, (c i * d i j) * (𝔼 n, U n * Q i n * R i j (n + h))))
    (∑ i, ∑ j, (c i * d i j) * (𝔼 n, U n * Q i n * R i j (n + h)))
  rw [sub_add_cancel] at htri
  linarith

theorem exists_fixed_model_partners {G I K : Type*} {J : I → Type*}
    [AddCommGroup G] [Fintype G] [Fintype I] [∀ i, Fintype (J i)] [Fintype K]
    (H : Finset G) (a b ea : G → ℂ) (U : G → K → G → ℂ)
    (Q : I → G → ℂ) (R : ∀ i, J i → G → ℂ)
    (eb : I → G → ℂ) (c : I → ℂ) (d : ∀ i, J i → ℂ)
    (ha : ∀ n, a n = (∑ i, c i * Q i n) + ea n)
    (hb : ∀ i n, b n = (∑ j, d i j * R i j n) + eb i n)
    (A : G → ℝ) (B : I → G → ℝ) {C D delta sigma budget : ℝ}
    (hdelta : 0 < delta) (hsigma : 0 < sigma) (hC : 0 < C) (hD : 0 < D)
    (hc : (∑ i, ‖c i‖) ≤ C) (hd : ∀ i, (∑ j, ‖d i j‖) ≤ D)
    (hA : ∀ h, 0 ≤ A h) (hB : ∀ i h, 0 ≤ B i h)
    (hfirst : ∀ h ∈ H, ∀ k, ‖𝔼 n, U h k n * ea n * b (n + h)‖ ≤ A h)
    (hsecond : ∀ h ∈ H, ∀ k i, ‖𝔼 n, U h k n * Q i n * eb i (n + h)‖ ≤ B i h)
    (hmean : (𝔼 h, A h) + ∑ i, ‖c i‖ * (𝔼 h, B i h) ≤ sigma * delta / 4)
    (hH : sigma * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, ∀ k, delta ≤ ‖𝔼 n, U h k n * a n * b (n + h)‖)
    (hcount : (Fintype.card (Sigma J) : ℝ) ≤ Real.exp budget) :
    ∃ (q : K → Sigma J) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-budget * Fintype.card K) * (sigma / 2 * Fintype.card G) ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k,
        (delta / 2) / (C * D) ≤ ‖𝔼 n, U h k n * Q (q k).1 n * R (q k).1 (q k).2 (n + h)‖ := by
  have herrMean : (𝔼 h, weightedModelError c A B h) ≤ sigma * delta / 4 :=
    (weightedModelError_mean_le c A B le_rfl (fun _ => le_rfl)).trans hmean
  obtain ⟨H', hsub, hH'n, hH'size, hgood⟩ := exists_large_good_error_set H
    (weightedModelError c A B) hsigma hdelta (weightedModelError_nonneg c A B hA hB) hH herrMean
  let rel : G → K → Sigma J → Prop := fun h k p =>
    (delta / 2) / (C * D) ≤ ‖𝔼 n, U h k n * Q p.1 n * R p.1 p.2 (n + h)‖
  have hchoice : ∀ h ∈ H', ∀ k, ∃ p, rel h k p := by
    intro h hh k
    obtain ⟨i, j, hij⟩ := exists_model_partner a b ea (U h k) Q R eb c d ha hb h
      hdelta hC hD hc hd (hfirst h (hsub hh) k) (hsecond h (hsub hh) k)
      (hgood h hh) (hcorr h (hsub hh) k)
    exact ⟨⟨i, j⟩, hij⟩
  obtain ⟨q, S, hSH', hSn, hsize, hfixed⟩ :=
    exists_large_fixed_choices H' hH'n rel hchoice hcount
  refine ⟨q, S, fun h hh => hsub (hSH' hh), hSn, ?_, hfixed⟩
  exact (mul_le_mul_of_nonneg_left hH'size (Real.exp_pos _).le).trans hsize

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_fixed_partners_of_shift_models {G I K ι : Type*} {J : I → Type*}
    [AddCommGroup G] [Fintype G] [Fintype I] [∀ i, Fintype (J i)] [Fintype K]
    (H : Finset G) (a b ea : G → ℂ) (T : ι → G → ℂ) (u : G → K → ι)
    (Q : I → G → ℂ) (R : ∀ i, J i → G → ℂ)
    (eb : I → G → ℂ) (c : I → ℂ) (d : ∀ i, J i → ℂ)
    (ha : ∀ n, a n = (∑ i, c i * Q i n) + ea n)
    (hb : ∀ i n, b n = (∑ j, d i j * R i j n) + eb i n)
    {C D delta sigma budget M : ℝ}
    (hdelta : 0 < delta) (hsigma : 0 < sigma) (hC : 0 < C) (hD : 0 < D)
    (hc : (∑ i, ‖c i‖) ≤ C) (hd : ∀ i, (∑ j, ‖d i j‖) ≤ D)
    (hT : ∀ t n, ‖T t n‖ ≤ 1) (hbcap : ∀ n, ‖b n‖ ≤ M)
    (hQ : ∀ i n, ‖Q i n‖ ≤ 1)
    (herror : shiftTestingSeminorm b T ea +
      ∑ i, ‖c i‖ * shiftTestingSeminorm (Q i) (translatedTestFamily T) (eb i) ≤ sigma * delta / 4)
    (hH : sigma * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, ∀ k, delta ≤ ‖𝔼 n, T (u h k) n * a n * b (n + h)‖)
    (hcount : (Fintype.card (Sigma J) : ℝ) ≤ Real.exp budget) :
    ∃ (q : K → Sigma J) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-budget * Fintype.card K) * (sigma / 2 * Fintype.card G) ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k,
        (delta / 2) / (C * D) ≤
          ‖𝔼 n, T (u h k) n * Q (q k).1 n * R (q k).1 (q k).2 (n + h)‖ := by
  apply exists_fixed_model_partners H a b ea (fun h k => T (u h k)) Q R eb c d ha hb
    (fun h => shiftTestSeminormAt b T h ea)
    (fun i h => shiftTestSeminormAt (Q i) (translatedTestFamily T) (-h) (eb i))
    hdelta hsigma hC hD hc hd
  · intro h
    exact apply_nonneg _ _
  · intro i h
    exact apply_nonneg _ _
  · intro h _ k
    exact first_model_error_le_shiftTest b ea T hbcap hT h (u h k)
  · intro h _ k i
    exact second_model_error_le_shiftTest (Q i) (eb i) T (hQ i) hT h (u h k)
  · change shiftTestingSeminorm b T ea +
      ∑ i, ‖c i‖ * (𝔼 h, shiftTestSeminormAt (Q i) (translatedTestFamily T) (-h) (eb i)) ≤ _
    simpa only [mean_negated_shiftTest] using herror
  · exact hH
  · exact hcorr
  · exact hcount

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exp_sub_two_le_quarter_exp (x : ℝ) : Real.exp (x - 2) ≤ Real.exp x / 4 := by
  have hfirst := exp_sub_one_le_half_exp (x - 1)
  have hsecond := exp_sub_one_le_half_exp x
  rw [show x - 1 - 1 = x - 2 by ring] at hfirst
  linarith

theorem exists_fixed_partners_power {G I K ι : Type*} {J : I → Type*}
    [AddCommGroup G] [Fintype G] [Fintype I] [∀ i, Fintype (J i)] [Fintype K]
    (H : Finset G) (a b ea : G → ℂ) (T : ι → G → ℂ) (u : G → K → ι)
    (Q : I → G → ℂ) (R : ∀ i, J i → G → ℂ)
    (eb : I → G → ℂ) (c : I → ℂ) (d : ∀ i, J i → ℂ)
    (ha : ∀ n, a n = (∑ i, c i * Q i n) + ea n)
    (hb : ∀ i n, b n = (∑ j, d i j * R i j n) + eb i n)
    {p q M : ℝ} (hp : 0 ≤ p) (hqp : q ≤ p) (hK : (Fintype.card K : ℝ) ≤ p)
    (hc : (∑ i, ‖c i‖) ≤ Real.exp p) (hd : ∀ i, (∑ j, ‖d i j‖) ≤ Real.exp p)
    (hT : ∀ t n, ‖T t n‖ ≤ 1) (hbcap : ∀ n, ‖b n‖ ≤ M)
    (hQ : ∀ i n, ‖Q i n‖ ≤ 1)
    (herror : shiftTestingSeminorm b T ea +
      ∑ i, ‖c i‖ * shiftTestingSeminorm (Q i) (translatedTestFamily T) (eb i) ≤ Real.exp (-(2 * q + 2)))
    (hH : Real.exp (-q) * Fintype.card G ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, ∀ k, Real.exp (-q) ≤ ‖𝔼 n, T (u h k) n * a n * b (n + h)‖)
    (hcount : (Fintype.card (Sigma J) : ℝ) ≤ Real.exp p) :
    ∃ (q : K → Sigma J) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-((p + 2) ^ 2)) * Fintype.card G ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, Real.exp (-((p + 2) ^ 2)) ≤
        ‖𝔼 n, T (u h k) n * Q (q k).1 n * R (q k).1 (q k).2 (n + h)‖ := by
  have hquarter : Real.exp (-(2 * q + 2)) ≤ Real.exp (-q) * Real.exp (-q) / 4 := by
    rw [← Real.exp_add]
    convert exp_sub_two_le_quarter_exp (-q + -q) using 1
    congr 1
    ring
  obtain ⟨choice, S, hsub, hSn, hsize, hbias⟩ := exists_fixed_partners_of_shift_models
    H a b ea T u Q R eb c d ha hb (Real.exp_pos _) (Real.exp_pos _)
    (Real.exp_pos _) (Real.exp_pos _) hc hd hT hbcap hQ (herror.trans hquarter) hH hcorr hcount
  have hsize' : Real.exp (-((p + 2) ^ 2)) ≤
      Real.exp (-p * Fintype.card K) * (Real.exp (-q) / 2) := by
    calc
      _ ≤ Real.exp ((-p * Fintype.card K + -q) - 1) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hK hp, sq_nonneg p]
      _ ≤ Real.exp (-p * Fintype.card K + -q) / 2 := exp_sub_one_le_half_exp _
      _ = _ := by rw [Real.exp_add]; ring
  have hbias' : Real.exp (-((p + 2) ^ 2)) ≤
      (Real.exp (-q) / 2) / (Real.exp p * Real.exp p) := by
    apply (le_div_iff₀ (mul_pos (Real.exp_pos _) (Real.exp_pos _))).mpr
    calc
      _ = Real.exp (-((p + 2) ^ 2) + (p + p)) := by rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (-q - 1) := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
      _ ≤ Real.exp (-q) / 2 := exp_sub_one_le_half_exp _
  refine ⟨choice, S, hsub, hSn, ?_, fun h hh k => hbias'.trans (hbias h hh k)⟩
  exact (mul_le_mul_of_nonneg_right hsize' (Nat.cast_nonneg _)).trans
    (by simpa only [mul_assoc] using hsize)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedDualVector
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

theorem functional_eq_uniform_inner (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (v : Ω → ℂ) :
    f v = 𝔼 x, v x * star (uniformDualVector f x) := by
  have hcard : (Fintype.card Ω : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Fintype.expect_eq_sum_div_card, functional_eq_sum_coordinates]
  simp only [uniformDualVector, star_mul, star_natCast, star_star]
  have hsum : (∑ x, v x * (f (Pi.single x 1) * (Fintype.card Ω : ℂ))) =
      (Fintype.card Ω : ℂ) * ∑ x, v x * f (Pi.single x 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  field_simp

omit [Nonempty Ω] in
theorem uniformDualVector_norm (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (x : Ω) :
    ‖uniformDualVector f x‖ = (Fintype.card Ω : ℝ) * ‖f (Pi.single x 1)‖ := by
  simp [uniformDualVector]

omit [Nonempty Ω] in
theorem uniform_single_norm_mean (x : Ω) :
    (𝔼 y, ‖(Pi.single x (1 : ℂ) : Ω → ℂ) y‖) = 1 / (Fintype.card Ω : ℝ) := by
  rw [Fintype.expect_eq_sum_div_card]
  have hpoint : (fun y => ‖(Pi.single x (1 : ℂ) : Ω → ℂ) y‖) = Pi.single x (1 : ℝ) := by
    ext y
    by_cases hy : y = x <;> simp [hy]
  rw [hpoint]
  simp

theorem uniformDualVector_self (f : (Ω → ℂ) →ₗ[ℂ] ℂ) :
    f (uniformDualVector f) = ((𝔼 x, ‖uniformDualVector f x‖ ^ 2) : ℝ) := by
  rw [functional_eq_uniform_inner]
  have hpoint (x : Ω) : uniformDualVector f x * star (uniformDualVector f x) =
      ((‖uniformDualVector f x‖ ^ 2 : ℝ) : ℂ) := by
    change uniformDualVector f x * (starRingEnd ℂ) (uniformDualVector f x) = _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hpoint]
  simp [Fintype.expect_eq_sum_div_card]

theorem uniformDualVector_cap (X : Seminorm ℂ (Ω → ℂ))
    (f : (Ω → ℂ) →ₗ[ℂ] ℂ) {K tau : ℝ} (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * (𝔼 x, ‖v x‖))
    (hdual : ∀ v, tau * ‖f v‖ ≤ X v) :
    ∀ x, ‖uniformDualVector f x‖ ≤ K / tau := by
  intro x
  have hcard : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hbound := (hdual (Pi.single x 1)).trans (hX (Pi.single x 1))
  rw [uniform_single_norm_mean] at hbound
  have hscaled := mul_le_mul_of_nonneg_left hbound hcard.le
  have hcancel : (Fintype.card Ω : ℝ) * (K * (1 / (Fintype.card Ω : ℝ))) = K := by
    field_simp
  rw [hcancel] at hscaled
  apply (le_div_iff₀ htau).mpr
  rw [uniformDualVector_norm]
  nlinarith only [hscaled]

theorem uniformDualVector_detectable (X : Seminorm ℂ (Ω → ℂ))
    (f : (Ω → ℂ) →ₗ[ℂ] ℂ) (b : Ω → ℂ) {M tau : ℝ}
    (hM : 0 < M) (htau : 0 < tau) (hb : ∀ x, ‖b x‖ ≤ M)
    (hfb : 1 < (f b).re) (hdual : ∀ v, tau * ‖f v‖ ≤ X v) :
    tau / M ^ 2 < X (uniformDualVector f) := by
  have hbMean : (𝔼 x, ‖b x‖ ^ 2) ≤ M ^ 2 :=
    (Finset.expect_le_expect (fun x (_ : x ∈ Finset.univ) =>
      pow_le_pow_left₀ (norm_nonneg _) (hb x) 2)).trans_eq
        (Finset.expect_const Finset.univ_nonempty (M ^ 2))
  have hself : ‖f (uniformDualVector f)‖ = 𝔼 x, ‖uniformDualVector f x‖ ^ 2 := by
    rw [uniformDualVector_self, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.expect_nonneg (fun x _ => sq_nonneg _))]
  have hcs := norm_expect_mul_star_sq_le b (uniformDualVector f)
  rw [← functional_eq_uniform_inner, ← hself] at hcs
  have hupper := mul_le_mul_of_nonneg_right hbMean (norm_nonneg (f (uniformDualVector f)))
  have hnorm : 1 < ‖f b‖ := hfb.trans_le (Complex.re_le_norm _)
  have hlarge : 1 < M ^ 2 * ‖f (uniformDualVector f)‖ := by
    nlinarith only [hcs, hupper, hnorm]
  have hscaled := mul_lt_mul_of_pos_left hlarge htau
  have hdom := mul_le_mul_of_nonneg_left (hdual (uniformDualVector f)) (sq_nonneg M)
  apply (div_lt_iff₀ (pow_pos hM 2)).mpr
  nlinarith only [hscaled, hdom]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarginalTailModeling
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

theorem exists_uniform_convex_approximation {S : Set (Ω → ℂ)} {z : Ω → ℂ}
    (hz : z ∈ convexHull ℝ S) (hS : ∀ q ∈ S, ∀ x, ‖q x‖ ≤ 1)
    (n : ℕ) (hn : 0 < n) :
    ∃ q : Fin n → (Ω → ℂ), (∀ i, q i ∈ S) ∧
      (𝔼 x, ‖((n : ℝ)⁻¹ • (∑ i, q i) - z) x‖ ^ 2) ≤ 1 / (n : ℝ) := by
  let e : (Ω → ℂ) ≃ₗ[ℝ] EuclideanSpace ℂ Ω :=
    (WithLp.linearEquiv 2 ℝ (Ω → ℂ)).symm
  have hz' : e z ∈ convexHull ℝ (e '' S) := by
    change e.toLinearMap z ∈ convexHull ℝ (e.toLinearMap '' S)
    rw [← e.toLinearMap.image_convexHull S]
    exact ⟨z, hz, rfl⟩
  have hS' : ∀ v ∈ e '' S, ‖v‖ ≤ Real.sqrt (Fintype.card Ω : ℝ) := by
    rintro v ⟨q, hq, rfl⟩
    rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),
      Real.sq_sqrt (Nat.cast_nonneg _)]
    change ‖(WithLp.toLp 2 q : EuclideanSpace ℂ Ω)‖ ^ 2 ≤ (Fintype.card Ω : ℝ)
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _x : Ω, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg (q x)) (hS q hq x) 2
      _ = _ := by simp
  obtain ⟨v, hv, hsq⟩ := exists_convex_empirical_average hz' hS' n hn
  let q : Fin n → (Ω → ℂ) := fun i => e.symm (v i)
  have hq : ∀ i, q i ∈ S := by
    intro i
    obtain ⟨w, hw, hew⟩ := hv i
    change e.symm (v i) ∈ S
    rw [← hew, e.symm_apply_apply]
    exact hw
  have hid : e ((n : ℝ)⁻¹ • (∑ i, q i) - z) =
      (n : ℝ)⁻¹ • (∑ i, v i) - e z := by
    simp only [map_sub, map_smul, map_sum, q, LinearEquiv.apply_symm_apply]
  rw [← hid, Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
  change ‖(WithLp.toLp 2 ((n : ℝ)⁻¹ • (∑ i, q i) - z) : EuclideanSpace ℂ Ω)‖ ^ 2 ≤
    (Fintype.card Ω : ℝ) / n at hsq
  rw [EuclideanSpace.norm_sq_eq] at hsq
  refine ⟨q, hq, ?_⟩
  rw [Fintype.expect_eq_sum_div_card]
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply (div_le_div_of_nonneg_right hsq (Nat.cast_nonneg _)).trans_eq
  field_simp

theorem seminorm_sq_le_square_mean (X : Seminorm ℂ (Ω → ℂ)) {K : ℝ}
    (hX : ∀ v, X v ≤ K * (𝔼 x, ‖v x‖)) (v : Ω → ℂ) :
    (X v) ^ 2 ≤ K ^ 2 * (𝔼 x, ‖v x‖ ^ 2) := by
  have h := pow_le_pow_left₀ (apply_nonneg X v) (hX v) 2
  rw [mul_pow] at h
  exact h.trans (mul_le_mul_of_nonneg_left (expect_square_le (fun x => ‖v x‖)) (sq_nonneg K))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

omit [DecidableEq Ω] [Nonempty Ω] in
theorem norm_uniform_inner_symm (v w : Ω → ℂ) :
    ‖𝔼 x, v x * star (w x)‖ = ‖𝔼 x, w x * star (v x)‖ := by
  have h : star (𝔼 x, v x * star (w x)) = 𝔼 x, w x * star (v x) := by
    simp [Fintype.expect_eq_sum_div_card, mul_comm]
  rw [← h, norm_star]

theorem mem_closure_model_of_uniform_detector
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)} (hS : Balanced ℂ S) (hSn : S.Nonempty)
    {K M beta tau : ℝ} (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * (𝔼 x, ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ Q ∈ S, beta ≤ ‖𝔼 x, psi x * star (Q x)‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    b ∈ closure ((2 / beta : ℝ) • convexHull ℝ S + X.closedBall 0 tau) := by
  apply mem_closure_model_set_of_dual_detector X hS hSn (by positivity) htau b
  intro f hfb hdual
  have hcap := uniformDualVector_cap X f.toLinearMap htau hX hdual
  have hlarge := uniformDualVector_detectable X f.toLinearMap b hM htau hb hfb hdual
  obtain ⟨Q, hQ, hcor⟩ := hdetect (uniformDualVector f.toLinearMap) hcap hlarge.le
  rw [norm_uniform_inner_symm, ← functional_eq_uniform_inner] at hcor
  refine ⟨Q, hQ, ?_⟩
  have h := mul_le_mul_of_nonneg_left hcor (show 0 ≤ 2 / beta by positivity)
  rw [div_mul_cancel₀ 2 hbeta.ne'] at h
  exact (by norm_num : (1 : ℝ) ≤ 2).trans h

theorem exists_convex_model_of_uniform_detector
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)} (hS : Balanced ℂ S) (hSn : S.Nonempty)
    {K M beta tau eta : ℝ} (hK : 0 ≤ K) (hM : 0 < M) (hbeta : 0 < beta)
    (htau : 0 < tau) (heta : 0 < eta)
    (hX : ∀ v, X v ≤ K * (𝔼 x, ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ Q ∈ S, beta ≤ ‖𝔼 x, psi x * star (Q x)‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ z ∈ convexHull ℝ S, X (b - (2 / beta : ℝ) • z) ≤ tau + eta := by
  have hc := mem_closure_model_of_uniform_detector X hS hSn hM hbeta htau hX hdetect b hb
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hc (eta / (K + 1)) (by positivity)
  obtain ⟨v, hv, e, he, hve⟩ := Set.mem_add.mp hy
  obtain ⟨z, hz, hzv⟩ := Set.mem_smul_set.mp hv
  have hxe : X e ≤ tau := X.mem_closedBall_zero.mp he
  have hnorm : ‖b - y‖ < eta / (K + 1) := by
    simpa only [dist_eq_norm] using hdist
  have hsmall : K * ‖b - y‖ ≤ eta := by
    have h := (lt_div_iff₀ (show 0 < K + 1 by linarith)).mp hnorm
    nlinarith [norm_nonneg (b - y)]
  have hmean : (𝔼 x, ‖(b - y) x‖) ≤ ‖b - y‖ :=
    (Finset.expect_le_expect (fun x (_ : x ∈ Finset.univ) => norm_le_pi_norm (b - y) x)).trans_eq
      (Finset.expect_const Finset.univ_nonempty ‖b - y‖)
  have hxy : X (b - y) ≤ eta := (hX (b - y)).trans
    ((mul_le_mul_of_nonneg_left hmean hK).trans hsmall)
  refine ⟨z, hz, ?_⟩
  have hid : b - (2 / beta : ℝ) • z = (b - y) + e := by
    rw [← hve, ← hzv]
    abel
  rw [hid]
  exact (map_add_le_add X _ _).trans (by linarith)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

theorem scaled_empirical_seminorm_bound (X : Seminorm ℂ (Ω → ℂ)) {K R : ℝ}
    (hR : 0 ≤ R) (hX : ∀ v, X v ≤ K * (𝔼 x, ‖v x‖))
    (v : Ω → ℂ) (n : ℕ) (hn : 0 < n) (hv : (𝔼 x, ‖v x‖ ^ 2) ≤ 1 / (n : ℝ)) :
    X (R • v) ≤ Real.sqrt (R ^ 2 * K ^ 2 / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq := (seminorm_sq_le_square_mean X hX v).trans
    (mul_le_mul_of_nonneg_left hv (sq_nonneg K))
  have hsmul : X (R • v) = R * X v := by
    change (X.restrictScalars ℝ) (R • v) = _
    rw [map_smul_eq_mul, Real.norm_of_nonneg hR]
    rfl
  have hscaled : (X (R • v)) ^ 2 ≤ R ^ 2 * K ^ 2 / n := by
    rw [hsmul, mul_pow]
    have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg R)
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_assoc] using h
  have hroot := Real.sq_sqrt (show 0 ≤ R ^ 2 * K ^ 2 / n by positivity)
  exact (sq_le_sq₀ (apply_nonneg X _) (Real.sqrt_nonneg _)).mp (hscaled.trans_eq hroot.symm)

variable [DecidableEq Ω]

theorem exists_uniform_model_of_detector
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) (hSbound : ∀ Q ∈ S, ∀ x, ‖Q x‖ ≤ 1)
    {K M beta tau : ℝ} (hK : 0 ≤ K) (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * (𝔼 x, ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ Q ∈ S, beta ≤ ‖𝔼 x, psi x * star (Q x)‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (Ω → ℂ)) (c : Fin n → ℝ) (e : Ω → ℂ),
      (∀ i, Q i ∈ S) ∧ b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2 / beta ∧ X e ≤ 2 * tau ∧
      (n : ℝ) ≤ 1 + 4 * K ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let R := 2 / beta
  have hR : 0 < R := by dsimp only [R]; positivity
  obtain ⟨n, hn, hlen, hsmall⟩ := exists_empirical_length (R := R) (K := K) htau
  let s := Real.sqrt (R ^ 2 * K ^ 2 / n)
  have hs : s < tau := hsmall
  let eta := (tau - s) / 2
  have heta : 0 < eta := by dsimp only [eta]; linarith
  obtain ⟨z, hz, hmodel⟩ := exists_convex_model_of_uniform_detector X hS hSn hK hM hbeta htau
    heta hX hdetect b hb
  obtain ⟨Q, hQ, happrox⟩ := exists_uniform_convex_approximation hz hSbound n hn
  let avg := (n : ℝ)⁻¹ • (∑ i, Q i)
  have hnoise : X (R • (avg - z)) ≤ s :=
    scaled_empirical_seminorm_bound X hR.le hX (avg - z) n hn happrox
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let c : Fin n → ℝ := fun _ => R / n
  have hstruct : (∑ i, c i • Q i) = R • avg := by
    calc
      _ = (R / (n : ℝ)) • (∑ i, Q i) := by rw [Finset.smul_sum]
      _ = _ := by dsimp only [avg]; rw [smul_smul]; congr 1
  have hcost : (∑ i, |c i|) = R := by
    simp only [c, abs_of_nonneg (div_nonneg hR.le hnR.le), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨n, hn, Q, c, b - ∑ i, c i • Q i, hQ, ?_, hcost.le, ?_, ?_⟩
  · abel
  · rw [hstruct]
    have hid : b - R • avg = (b - R • z) - R • (avg - z) := by
      rw [smul_sub]
      abel
    rw [hid]
    have h := map_sub_le_add X (b - R • z) (R • (avg - z))
    change X (b - R • z) ≤ tau + eta at hmodel
    dsimp only [eta] at hmodel
    linarith
  · have heq : R ^ 2 * K ^ 2 / tau ^ 2 = 4 * K ^ 2 / (beta ^ 2 * tau ^ 2) := by
      dsimp only [R]
      field_simp
      ring
    simpa only [heq] using hlen

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFixedVerticalPower
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_expect_three_le {G : Type*} [Fintype G] [Nonempty G]
    (u v w : G → ℂ) {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : ∀ x, ‖u x‖ ≤ A) (hv : ∀ x, ‖v x‖ ≤ B) (hw : ∀ x, ‖w x‖ ≤ C) :
    ‖𝔼 x, u x * v x * w x‖ ≤ A * B * C := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  simp only [norm_mul]
  exact mul_le_mul (mul_le_mul (hu x) (hv x) (norm_nonneg _) hA) (hw x)
    (norm_nonneg _) (mul_nonneg hA hB)

theorem exists_correlating_partner_components {G I J : Type*}
    [AddCommGroup G] [Fintype G] [Fintype I] [Fintype J]
    (U Q R : G → ℂ) (V : I → G → ℂ) (W : J → G → ℂ) (h : G)
    {delta C D rho eta : ℝ} (hdelta : 0 < delta) (hC : 0 < C) (hD : 0 < D)
    (heta : 0 ≤ eta) (hI : (Fintype.card I : ℝ) ≤ C) (hJ : (Fintype.card J : ℝ) ≤ D)
    (hU : ∀ x, ‖U x‖ ≤ 1) (hR : ∀ x, ‖R x‖ ≤ 1)
    (hV : ∀ i x, ‖V i x‖ ≤ 1)
    (hQapprox : ∀ x, ‖Q x - ∑ i, V i x‖ ≤ rho)
    (hRapprox : ∀ x, ‖R x - ∑ j, W j x‖ ≤ eta)
    (hsmall : rho + C * eta ≤ delta / 2)
    (hcorr : delta ≤ ‖𝔼 x, U x * Q x * R (x + h)‖) :
    ∃ i j, (delta / 2) / (C * D) ≤ ‖𝔼 x, U x * V i x * W j (x + h)‖ := by
  have hrho : 0 ≤ rho := (norm_nonneg _).trans (hQapprox 0)
  let ea : G → ℂ := fun x => Q x - ∑ i, V i x
  let eb : I → G → ℂ := fun _ x => R x - ∑ j, W j x
  have hfirst : ‖𝔼 x, U x * ea x * R (x + h)‖ ≤ rho := by
    have h := norm_expect_three_le U ea (fun x => R (x + h)) (by norm_num : (0 : ℝ) ≤ 1)
      hrho hU hQapprox (fun x => hR (x + h))
    simpa only [one_mul, mul_one] using h
  have hsecond (i : I) : ‖𝔼 x, U x * V i x * eb i (x + h)‖ ≤ eta := by
    have h := norm_expect_three_le U (V i) (fun x => eb i (x + h))
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
      hU (hV i) (fun x => hRapprox (x + h))
    simpa only [one_mul] using h
  apply exists_model_partner Q R ea U V (fun _ j => W j) eb (fun _ => 1) (fun _ _ => 1)
    (fun x => by dsimp only [ea]; simp only [one_mul]; ring)
    (fun _ x => by dsimp only [eb]; simp only [one_mul]; ring)
    h hdelta hC hD
  · simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hI
  · intro _
    simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hJ
  · exact hfirst
  · exact hsecond
  · simp only [norm_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact (add_le_add le_rfl (mul_le_mul_of_nonneg_right hI heta)).trans hsmall
  · exact hcorr

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_fixed_partner_components {G K : Type*} {I J : K → Type*}
    [AddCommGroup G] [Fintype G] [Fintype K]
    [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]
    (H : Finset G) (hH : H.Nonempty) (U : G → K → G → ℂ) (Q R : K → G → ℂ)
    (V : ∀ k, I k → G → ℂ) (W : ∀ k, J k → G → ℂ)
    {delta C D rho eta budget : ℝ} (hdelta : 0 < delta) (hC : 0 < C) (hD : 0 < D)
    (heta : 0 ≤ eta) (hI : ∀ k, (Fintype.card (I k) : ℝ) ≤ C)
    (hJ : ∀ k, (Fintype.card (J k) : ℝ) ≤ D) (hCD : C * D ≤ Real.exp budget)
    (hU : ∀ h ∈ H, ∀ k x, ‖U h k x‖ ≤ 1) (hR : ∀ k x, ‖R k x‖ ≤ 1)
    (hV : ∀ k i x, ‖V k i x‖ ≤ 1)
    (hQapprox : ∀ k x, ‖Q k x - ∑ i, V k i x‖ ≤ rho)
    (hRapprox : ∀ k x, ‖R k x - ∑ j, W k j x‖ ≤ eta)
    (hsmall : rho + C * eta ≤ delta / 2)
    (hcorr : ∀ h ∈ H, ∀ k, delta ≤ ‖𝔼 x, U h k x * Q k x * R k (x + h)‖) :
    ∃ (q : ∀ k, I k × J k) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-budget * Fintype.card K) * H.card ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k,
        (delta / 2) / (C * D) ≤ ‖𝔼 x, U h k x * V k (q k).1 x * W k (q k).2 (x + h)‖ := by
  let rel : ∀ (_ : G) (k : K), I k × J k → Prop := fun h k p =>
    (delta / 2) / (C * D) ≤ ‖𝔼 x, U h k x * V k p.1 x * W k p.2 (x + h)‖
  apply exists_large_fixed_dependent_choices H hH rel
  · intro h hh k
    obtain ⟨i, j, hij⟩ := exists_correlating_partner_components (U h k) (Q k) (R k) (V k) (W k) h
      hdelta hC hD heta (hI k) (hJ k) (hU h hh k) (hR k) (hV k)
      (hQapprox k) (hRapprox k) hsmall (hcorr h hh k)
    exact ⟨(i, j), hij⟩
  · intro k
    rw [Fintype.card_prod, Nat.cast_mul]
    exact (mul_le_mul (hI k) (hJ k) (Nat.cast_nonneg _) hC.le).trans hCD

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_fixed_native_vertical_partners
    {K σ : Type*} [Fintype K] {L L' : K → Type*}
    [∀ k, LieRing (L k)] [∀ k, LieAlgebra ℚ (L k)]
    [∀ k, LieRing (L' k)] [∀ k, LieAlgebra ℚ (L' k)] {s : ℕ} {d d' : K → ℕ}
    [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L k)] [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L k)]
    [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L k)] [∀ k, T2Space (ℝ ⊗[ℚ] L k)]
    [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L' k)] [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L' k)]
    [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L' k)] [∀ k, T2Space (ℝ ⊗[ℚ] L' k)]
    (D : ∀ k, RationalFilteredNilmanifold (L k) s (d k))
    (D' : ∀ k, RationalFilteredNilmanifold (L' k) s (d' k)) {w : σ → ℕ}
    (Q : ∀ k, (D k).Niltest w) (R : ∀ k, (D' k).Niltest w)
    {p q delta rho eta : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hdelta : 0 < delta)
    (hrho : 0 < rho) (heta : 0 < eta) (hrhop : rho⁻¹ ≤ Real.exp p) (hetaq : eta⁻¹ ≤ Real.exp q)
    (hQc : ∀ k, (Q k).ComplexityLE p) (hRc : ∀ k, (R k).ComplexityLE q)
    (hQcap : ∀ k, ((Q k).normBound : ℝ) ≤ 1) (hRcap : ∀ k, ((R k).normBound : ℝ) ≤ 1)
    (hsmall : rho + Real.exp (verticalDecompositionBudget p) * eta ≤ delta / 2)
    (N : ℕ) [NeZero N] (H : Finset (ZMod N)) (hH : H.Nonempty)
    (U : ZMod N → K → ZMod N → ℂ) (hU : ∀ h ∈ H, ∀ k n, ‖U h k n‖ ≤ 1)
    (hcorr : ∀ h ∈ H, ∀ k, delta ≤ ‖𝔼 n,
      U h k n * (Q k).evalCyclic N (fun _ => n) * (R k).evalCyclic N (fun _ => n + h)‖) :
    ∃ (freq : ∀ k, L k →ₗ[ℚ] ℚ) (freq' : ∀ k, L' k →ₗ[ℚ] ℚ)
      (V : ∀ k, (D k).Niltest w) (W : ∀ k, (D' k).Niltest w) (S : Finset (ZMod N)),
      S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-(verticalDecompositionBudget p + verticalDecompositionBudget q) * Fintype.card K) *
        H.card ≤ (S.card : ℝ) ∧
      (∀ k, (V k).ComplexityLE p ∧ (V k).orbit = (Q k).orbit ∧ ((V k).normBound : ℝ) ≤ 1) ∧
      (∀ k, (W k).ComplexityLE q ∧ (W k).orbit = (R k).orbit ∧ ((W k).normBound : ℝ) ≤ 1) ∧
      (∀ k i, rationalLogHeight (freq k ((D k).basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ k i, rationalLogHeight (freq' k ((D' k).basis i)) ≤ verticalDecompositionBudget q) ∧
      (∀ k (z : (D k).RealGroup), z ∈ (D k).filtration.realification.subgroup s → ∀ x,
        (V k).observable (z • x) =
          character ((realifyFunctional (freq k) z.coord : ℝ) : CircleFourier.Circle) * (V k).observable x) ∧
      (∀ k (z : (D' k).RealGroup), z ∈ (D' k).filtration.realification.subgroup s → ∀ x,
        (W k).observable (z • x) =
          character ((realifyFunctional (freq' k) z.coord : ℝ) : CircleFourier.Circle) * (W k).observable x) ∧
      ∀ h ∈ S, ∀ k, (delta / 2) /
        (Real.exp (verticalDecompositionBudget p) * Real.exp (verticalDecompositionBudget q)) ≤
        ‖𝔼 n, U h k n * (V k).evalCyclic N (fun _ => n) * (W k).evalCyclic N (fun _ => n + h)‖ := by
  classical
  choose I instI freqV V hI hheightV hcertV hvertV hintV hobsV happroxV using
    fun k => (Q k).exists_vertical_decomposition_preserving_bounds hp (hQc k) hrho hrhop
  let : ∀ k, Fintype (I k) := instI
  choose J instJ freqW W hJ hheightW hcertW hvertW hintW hobsW happroxW using
    fun k => (R k).exists_vertical_decomposition_preserving_bounds hq (hRc k) heta hetaq
  let : ∀ k, Fintype (J k) := instJ
  have hVcap (k : K) (i : I k) (n : ZMod N) : ‖(V k i).evalCyclic N (fun _ => n)‖ ≤ 1 := by
    apply ((V k i).norm_evalCyclic_le N _).trans
    rw [(hcertV k i).2.2.1]
    exact hQcap k
  have hRcap' (k : K) (n : ZMod N) : ‖(R k).evalCyclic N (fun _ => n)‖ ≤ 1 :=
    ((R k).norm_evalCyclic_le N _).trans (hRcap k)
  have hQa (k : K) (n : ZMod N) :
      ‖(Q k).evalCyclic N (fun _ => n) - ∑ i, (V k i).evalCyclic N (fun _ => n)‖ ≤ rho := by
    simpa only [RationalFilteredNilmanifold.Niltest.evalCyclic, norm_sub_rev] using
      happroxV k (fun _ => (n.val : ℤ))
  have hRa (k : K) (n : ZMod N) :
      ‖(R k).evalCyclic N (fun _ => n) - ∑ j, (W k j).evalCyclic N (fun _ => n)‖ ≤ eta := by
    simpa only [RationalFilteredNilmanifold.Niltest.evalCyclic, norm_sub_rev] using
      happroxW k (fun _ => (n.val : ℤ))
  have hcount : Real.exp (verticalDecompositionBudget p) * Real.exp (verticalDecompositionBudget q) ≤
      Real.exp (verticalDecompositionBudget p + verticalDecompositionBudget q) :=
    (Real.exp_add _ _).symm.le
  obtain ⟨choices, S, hsub, hSn, hsize, hbias⟩ := exists_fixed_partner_components H hH U
    (fun k n => (Q k).evalCyclic N (fun _ => n)) (fun k n => (R k).evalCyclic N (fun _ => n))
    (fun k i n => (V k i).evalCyclic N (fun _ => n)) (fun k j n => (W k j).evalCyclic N (fun _ => n))
    hdelta (Real.exp_pos _) (Real.exp_pos _) heta.le hI hJ hcount hU hRcap' hVcap hQa hRa hsmall hcorr
  refine ⟨(fun k => freqV k (choices k).1), (fun k => freqW k (choices k).2),
    (fun k => V k (choices k).1), (fun k => W k (choices k).2), S, hsub, hSn, hsize, ?_, ?_,
    (fun k => hheightV k (choices k).1), (fun k => hheightW k (choices k).2),
    (fun k => hvertV k (choices k).1), (fun k => hvertW k (choices k).2), hbias⟩
  · intro k
    refine ⟨(hcertV k (choices k).1).1, (hcertV k (choices k).1).2.1, ?_⟩
    rw [(hcertV k (choices k).1).2.2.1]
    exact hQcap k
  · intro k
    refine ⟨(hcertW k (choices k).2).1, (hcertW k (choices k).2).2.1, ?_⟩
    rw [(hcertW k (choices k).2).2.2.1]
    exact hRcap k

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_fixed_native_vertical_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {K σ : Type*} [Fintype K] {L L' : K → Type*}
      [∀ k, LieRing (L k)] [∀ k, LieAlgebra ℚ (L k)]
      [∀ k, LieRing (L' k)] [∀ k, LieAlgebra ℚ (L' k)] {s : ℕ} {d d' : K → ℕ}
      [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L k)] [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L k)]
      [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L k)] [∀ k, T2Space (ℝ ⊗[ℚ] L k)]
      [∀ k, TopologicalSpace (ℝ ⊗[ℚ] L' k)] [∀ k, IsTopologicalAddGroup (ℝ ⊗[ℚ] L' k)]
      [∀ k, ContinuousSMul ℝ (ℝ ⊗[ℚ] L' k)] [∀ k, T2Space (ℝ ⊗[ℚ] L' k)]
      (D : ∀ k, RationalFilteredNilmanifold (L k) s (d k))
      (D' : ∀ k, RationalFilteredNilmanifold (L' k) s (d' k)) {w : σ → ℕ}
      (Q : ∀ k, (D k).Niltest w) (R : ∀ k, (D' k).Niltest w)
      {p : ℝ}, 0 ≤ p → (Fintype.card K : ℝ) ≤ p →
      (∀ k, (Q k).ComplexityLE p) → (∀ k, (R k).ComplexityLE p) →
      (∀ k, (Q k).normBound ≤ 1) → (∀ k, (R k).normBound ≤ 1) →
      ∀ (N : ℕ) [NeZero N] (H : Finset (ZMod N)), H.Nonempty →
      ∀ U : ZMod N → K → ZMod N → ℂ,
      (∀ h ∈ H, ∀ k n, ‖U h k n‖ ≤ 1) →
      (∀ h ∈ H, ∀ k, Real.exp (-p) ≤ ‖𝔼 n,
        U h k n * (Q k).evalCyclic N (fun _ => n) * (R k).evalCyclic N (fun _ => n + h)‖) →
      ∃ (freq : ∀ k, L k →ₗ[ℚ] ℚ) (freq' : ∀ k, L' k →ₗ[ℚ] ℚ)
        (V : ∀ k, (D k).Niltest w) (W : ∀ k, (D' k).Niltest w) (S : Finset (ZMod N)),
        S ⊆ H ∧ S.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (S.card : ℝ) ∧
        (∀ k, (V k).ComplexityLE ((p + C) ^ C) ∧ (V k).orbit = (Q k).orbit ∧ (V k).normBound ≤ 1) ∧
        (∀ k, (W k).ComplexityLE ((p + C) ^ C) ∧ (W k).orbit = (R k).orbit ∧ (W k).normBound ≤ 1) ∧
        (∀ k i, rationalLogHeight (freq k ((D k).basis i)) ≤ (p + C) ^ C) ∧
        (∀ k i, rationalLogHeight (freq' k ((D' k).basis i)) ≤ (p + C) ^ C) ∧
        (∀ k z, z ∈ (D k).filtration.realification.subgroup s → ∀ x,
          (V k).observable (z • x) = character
            ((realifyFunctional (freq k) z.coord : ℝ) : CircleFourier.Circle) * (V k).observable x) ∧
        (∀ k z, z ∈ (D' k).filtration.realification.subgroup s → ∀ x,
          (W k).observable (z • x) = character
            ((realifyFunctional (freq' k) z.coord : ℝ) : CircleFourier.Circle) * (W k).observable x) ∧
        ∀ h ∈ S, ∀ k, Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n,
          U h k n * (V k).evalCyclic N (fun _ => n) * (W k).evalCyclic N (fun _ => n + h)‖ := by
  obtain ⟨c, _, hprecision⟩ := exists_vertical_pair_precision
  let X : Polynomial ℕ := Polynomial.X
  let B := (X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * B * X + B)
  refine ⟨C, hC, ?_⟩
  intro K σ _ L L' _ _ _ _ s d d' _ _ _ _ _ _ _ _ D D' w Q R p hp hK hQc hRc hQcap hRcap
    N _ H hH U hU hcorr
  obtain ⟨q, r, rho, eta, hpq, hpr, hqC, hrC, hVq, hVr, hrho, heta, hrhoq, hetar, hsmall, hloss⟩ :=
    hprecision p hp
  have hB0 : 0 ≤ (p + c) ^ c := by positivity
  have hbud : 2 * (p + c) ^ c * p + (p + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, B, Polynomial.eval₂_pow] using hbudget p hp
  have hBC : (p + c) ^ c ≤ (p + C) ^ C := by nlinarith
  have hsizeBudget : (verticalDecompositionBudget q + verticalDecompositionBudget r) *
      Fintype.card K ≤ (p + C) ^ C := by
    calc
      _ ≤ (2 * (p + c) ^ c) * Fintype.card K :=
        mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      _ ≤ (2 * (p + c) ^ c) * p := mul_le_mul_of_nonneg_left hK (by positivity)
      _ ≤ (p + C) ^ C := by linarith
  obtain ⟨freq, freq', V, W, S, hsub, hSn, hsize, hV, hW, hheightV, hheightW, hvertV, hvertW, hbias⟩ :=
    exists_fixed_native_vertical_partners D D' Q R (hp.trans hpq) (hp.trans hpr)
      (Real.exp_pos _) hrho heta hrhoq hetar
      (fun k => (hQc k).mono hpq) (fun k => (hRc k).mono hpr)
      hQcap hRcap hsmall N H hH U hU hcorr
  refine ⟨freq, freq', V, W, S, hsub, hSn, ?_, ?_, ?_, ?_, ?_, hvertV, hvertW, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hsizeBudget))
      (Nat.cast_nonneg _)).trans (by simpa only [neg_mul] using hsize)
  · exact fun k => ⟨(hV k).1.mono (hqC.trans hBC), (hV k).2⟩
  · exact fun k => ⟨(hW k).1.mono (hrC.trans hBC), (hW k).2⟩
  · exact fun k i => (hheightV k i).trans (hVq.trans hBC)
  · exact fun k i => (hheightW k i).trans (hVr.trans hBC)
  · exact fun h hh k => (Real.exp_le_exp.mpr (neg_le_neg hBC)).trans (hloss.trans (hbias h hh k))

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

theorem testingFamily_of_mem (B : PositiveShiftBasis s N q a J) {h : ZMod N}
    (hh : h ∈ B.shifts) (j : Fin B.count) (n : ZMod N) :
    B.testingFamily (h, j) n = (B.mode h j).evalCyclic N (fun _ => n) := by
  simp only [testingFamily, if_pos hh]

theorem testingFamily_norm_le (B : PositiveShiftBasis s N q a J)
    (hk : ZMod N × Fin B.count) (n : ZMod N) : ‖B.testingFamily hk n‖ ≤ 1 := by
  classical
  by_cases hh : hk.1 ∈ B.shifts
  · rw [testingFamily, if_pos hh]
    exact ((B.mode hk.1 hk.2).norm_evalCyclic_le N _).trans (B.mode_norm hk.1 hh hk.2)
  · simp only [testingFamily, if_neg hh, norm_zero, zero_le_one]

theorem exists_fixed_partners (B : PositiveShiftBasis s N q a J)
    {I : Type*} {K : I → Type*} [Fintype I] [∀ i, Fintype (K i)]
    (Q : I → ZMod N → ℂ) (R : ∀ i, K i → ZMod N → ℂ)
    (ea : ZMod N → ℂ) (eb : I → ZMod N → ℂ) (c : I → ℂ) (d : ∀ i, K i → ℂ)
    (ha : ∀ n, (a n : ℂ) = (∑ i, c i * Q i n) + ea n)
    (hb : ∀ i n, (J n : ℂ) = (∑ j, d i j * R i j n) + eb i n)
    {p M : ℝ} (hqp : q ≤ p)
    (hc : (∑ i, ‖c i‖) ≤ Real.exp p) (hd : ∀ i, (∑ j, ‖d i j‖) ≤ Real.exp p)
    (hJ : ∀ n, |J n| ≤ M) (hQ : ∀ i n, ‖Q i n‖ ≤ 1)
    (herror : shiftTestingSeminorm (fun n => (J n : ℂ)) B.testingFamily ea +
      ∑ i, ‖c i‖ * shiftTestingSeminorm (Q i) (translatedTestFamily B.testingFamily) (eb i) ≤
        Real.exp (-(2 * q + 2)))
    (hcount : (Fintype.card (Sigma K) : ℝ) ≤ Real.exp p) :
    ∃ (choice : Fin B.count → Sigma K) (S : Finset (ZMod N)), S ⊆ B.shifts ∧ S.Nonempty ∧
      Real.exp (-((p + 2) ^ 2)) * N ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ j, Real.exp (-((p + 2) ^ 2)) ≤
        ‖𝔼 n, (B.mode h j).evalCyclic N (fun _ => n) * Q (choice j).1 n *
          R (choice j).1 (choice j).2 (n + h)‖ := by
  have hq : 0 ≤ q := (Nat.cast_nonneg B.dim).trans B.geometry.1
  have hK : (Fintype.card (Fin B.count) : ℝ) ≤ p := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr B.count_le_dim).trans (B.geometry.1.trans hqp)
  have hH : Real.exp (-q) * Fintype.card (ZMod N) ≤ (B.shifts.card : ℝ) := by
    simpa only [ZMod.card] using B.shifts_large
  have hbcap (n) : ‖(J n : ℂ)‖ ≤ M := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hJ n
  have hcorr (h) (hh : h ∈ B.shifts) (j : Fin B.count) :
      Real.exp (-q) ≤ ‖𝔼 n, B.testingFamily (h, j) n * (a n : ℂ) * (J (n + h) : ℂ)‖ := by
    simp only [testingFamily_of_mem B hh]
    exact (B.mode_bias h hh j).le
  obtain ⟨choice, S, hsub, hSn, hlarge, hbias⟩ := exists_fixed_partners_power B.shifts
    (fun n => (a n : ℂ)) (fun n => (J n : ℂ)) ea B.testingFamily (fun h j => (h, j))
    Q R eb c d ha hb (hq.trans hqp) hqp hK hc hd B.testingFamily_norm_le hbcap hQ herror hH hcorr hcount
  refine ⟨choice, S, hsub, hSn, ?_, ?_⟩
  · simpa only [ZMod.card] using hlarge
  · intro h hh j
    simpa only [testingFamily_of_mem B (hsub hh)] using hbias h hh j

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftProductData
namespace OAI

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
  (B : PositiveShiftBasis.{u} s N q a J)

variable {L M : Fin B.count → Type u}
  [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
  (D : ∀ j, RationalFilteredNilmanifold (L j) s (d j))
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (e j))

theorem anchoredFactors_geometry {p : ℝ} (hqp : q ≤ p)
    (hD : ∀ j, (D j).GeometryComplexityLE p) (hE : ∀ j, (E j).GeometryComplexityLE p) :
    ∀ i, (B.anchoredFactors D E i).GeometryComplexityLE p := by
  intro i
  rcases i with _ | ((_ | j) | j)
  · exact B.geometry.mono B.model hqp
  · exact B.geometry.mono B.model hqp
  · exact hD j
  · exact hE j

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredMappedOrbitFactors
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

variable {G ι J σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (a : ι)

theorem exists_common_product_orbit_factors
    (weight : ∀ i, Fin (d i) → ℕ)
    (hFlayers : ∀ i j, (D i).filtration.layer j =
      Submodule.span ℚ ((D i).basis '' {k | j ≤ weight i k}))
    (H : Finset G) (hH : H.Nonempty)
    (g : G → ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (eta : G → J → L a →ₗ[ℚ] ℚ) (side : σ → ℝ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (Fintype.card (Σ i, Fin (d i)) : ℝ) ≤ p)
    (hdata : ∀ h ∈ H,
      ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
        (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded) (m : ℕ),
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis
          (productBasisWeight weight) (pi_layer_span D weight hFlayers))
          (productBasisWeight weight) W.toSubmodule ∧
        (∀ i j, rationalLogHeight
          (((pi D).filtration.associatedGradedBasis (pi D).basis
            (productBasisWeight weight) (pi_layer_span D weight hFlayers)).repr (v i) j) ≤ p) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp p ∧
        HasFixedProductOrbitFactors D a (g h) (eta h) side p m W) :
    ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded)
      (m : ℕ) (H' : Finset G),
      H' ⊆ H ∧ H'.Nonempty ∧
      Real.exp (-((p + 2) ^ 5 + p)) * H.card ≤ (H'.card : ℝ) ∧
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight weight) (pi_layer_span D weight hFlayers))
        (productBasisWeight weight) W.toSubmodule ∧
      (∀ i j, rationalLogHeight
        (((pi D).filtration.associatedGradedBasis (pi D).basis
          (productBasisWeight weight) (pi_layer_span D weight hFlayers)).repr (v i) j) ≤ p) ∧
      0 < m ∧ (m : ℝ) ≤ Real.exp p ∧
      ∀ h ∈ H', HasFixedProductOrbitFactors D a (g h) (eta h) side p m W := by
  classical
  obtain ⟨h₀, hh₀⟩ := hH
  let pick (h : G) := if h ∈ H then h else h₀
  have hpick (h) : pick h ∈ H := by
    dsimp only [pick]
    split_ifs with hh
    · exact hh
    · exact hh₀
  choose W v m hv hW hheight hm hmp hfactor using fun h => hdata (pick h) (hpick h)
  let e := (pi D).filtration.associatedGradedBasis (pi D).basis
    (productBasisWeight weight) (pi_layer_span D weight hFlayers)
  obtain ⟨h₁, _, H', hsub, hh₁, hsame, hlarge⟩ :=
    exists_common_fast_subalgebra_and_denominator e H ⟨h₀, hh₀⟩ W m
      (Fintype.card (Σ i, Fin (d i))) hp hd (by simpa only [Fintype.card_fin] using hd)
      (fun h _ => ⟨v h, hv h, hheight h⟩) (fun h _ => ⟨hm h, hmp h⟩)
  refine ⟨W h₁, v h₁, m h₁, H', hsub, ⟨h₁, hh₁⟩, hlarge,
    hv h₁, hW h₁, hheight h₁, hm h₁, hmp h₁, ?_⟩
  intro h hh
  have hpickh : pick h = h := if_pos (hsub hh)
  simpa only [hpickh, (hsame h hh).1, (hsame h hh).2] using hfactor h

theorem exists_common_product_frequency_family
    (H : Finset G)
    (g : G → ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (eta : G → J → L a →ₗ[ℚ] ℚ) (side : σ → ℝ) (p : ℝ) (m : ℕ)
    (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
    (hdata : ∀ h ∈ H, HasFixedProductOrbitFactors D a (g h) (eta h) side p m W)
    (S : G → (D a).Space → ℂ)
    (hinvariant : ∀ h ∈ H, ∀ z, z ∈ (D a).filtration.realification.subgroup s →
      (∀ j, realifyFunctional (eta h j) z.coord = 0) → ∀ x, S h (z • x) = S h x) :
    ∃ freq : ({h // h ∈ H} × J) → ∀ i, L i →ₗ[ℚ] ℚ,
      (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s →
        realifyFunctional (piFrequency (freq j)) x = 0) ∧
      (∀ h ∈ H, ∀ z, z ∈ (D a).filtration.realification.subgroup s →
        (∀ j, realifyFunctional (freq j a) z.coord = 0) → ∀ x, S h (z • x) = S h x) := by
  classical
  let freq₀ := fun h : {h // h ∈ H} => Classical.choose (hdata h.val h.property)
  have hfreq₀ (h : {h // h ∈ H}) := Classical.choose_spec (hdata h.val h.property)
  refine ⟨fun j => freq₀ j.1 j.2, ?_, ?_⟩
  · intro j x hx
    exact (hfreq₀ j.1).2.1 j.2 x hx
  · intro h hh z hz hf x
    apply hinvariant h hh z hz _ x
    intro j
    have hj := hf (⟨h, hh⟩, j)
    change realifyFunctional (freq₀ ⟨h, hh⟩ j a) z.coord = 0 at hj
    have hident : freq₀ ⟨h, hh⟩ j a = eta h j := (hfreq₀ ⟨h, hh⟩).1 j
    rwa [hident] at hj

end Erdos3.RationalFilteredNilmanifold

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

theorem nativeCyclicFunctions_balanced (degree N : ℕ) [NeZero N] (p : ℝ) :
    Balanced ℂ (nativeCyclicFunctions degree N p) := by
  rintro c hc _ ⟨f, ⟨F⟩, rfl⟩
  exact ⟨F.smul c hc⟩

theorem nativeCyclicFunctions_norm {degree N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (hf : f ∈ nativeCyclicFunctions degree N p) (x : ZMod N) : ‖f x‖ ≤ 1 := by
  obtain ⟨F⟩ := hf
  rw [F.eval x]
  exact (F.test.norm_evalCyclic_le N (fun _ => x)).trans F.norm

theorem nativeCyclicFunctions_zero {degree N : ℕ} [NeZero N] (hdegree : 1 ≤ degree)
    {p : ℝ} (hp : 2 ≤ p) : (0 : ZMod N → ℂ) ∈ nativeCyclicFunctions degree N p := by
  let D := (RationalTorus.nilmanifold 0).raiseStep hdegree
  have hgeom : D.GeometryComplexityLE p :=
    (RationalTorus.nilmanifold 0).raiseStep_geometry hdegree
      (RationalTorus.nilmanifold_geometry 0 (by linarith) (by norm_num; linarith))
  refine ⟨{
    L := RationalTorus.Algebra 0
    dim := 0
    model := D
    test := RationalFilteredNilmanifold.Niltest.const D (fun _ : Unit => 1) 0
    norm := by simp [RationalFilteredNilmanifold.Niltest.const]
    complexity := ⟨hgeom, ?_⟩
    eval := fun _ => rfl }⟩
  change Real.log (2 + (‖(0 : ℂ)‖₊ : ℝ) + (0 : ℝ)) ≤ p
  simp only [nnnorm_zero, NNReal.coe_zero, add_zero]
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_native_cyclic_model_of_detector {degree N : ℕ} [NeZero N]
    (hdegree : 1 ≤ degree) {p : ℝ} (hp : 2 ≤ p)
    (X : Seminorm ℂ (ZMod N → ℂ)) {K M beta tau : ℝ}
    (hK : 0 ≤ K) (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * (𝔼 x, ‖v x‖))
    (hdetect : ∀ psi : ZMod N → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ f ∈ nativeCyclicFunctions degree N p, beta ≤ ‖𝔼 x, psi x * star (f x)‖)
    (b : ZMod N → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ (n : ℕ) (_ : 0 < n) (f : Fin n → ZMod N → ℂ)
      (F : ∀ i, NativeCyclicModel degree N p (f i))
      (c : Fin n → ℂ) (e : ZMod N → ℂ),
      (∀ x, b x = (∑ i, c i * (F i).test.evalCyclic N (fun _ => x)) + e x) ∧
      (∑ i, ‖c i‖) ≤ 2 / beta ∧ X e ≤ 2 * tau ∧
      (n : ℝ) ≤ 1 + 4 * K ^ 2 / (beta ^ 2 * tau ^ 2) := by
  classical
  obtain ⟨n, hn, f, c, e, hf, heq, hcost, herr, hcount⟩ :=
    exists_uniform_model_of_detector X (nativeCyclicFunctions_balanced degree N p)
      ⟨0, nativeCyclicFunctions_zero hdegree hp⟩
      (fun _ hf x => nativeCyclicFunctions_norm hf x) hK hM hbeta htau hX hdetect b hb
  let F (i : Fin n) : NativeCyclicModel degree N p (f i) := Classical.choice (hf i)
  refine ⟨n, hn, f, F, (fun i => (c i : ℂ)), e, ?_, ?_, herr, hcount⟩
  · intro x
    have hx := congrFun heq x
    simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Complex.real_smul,
      fun i => (F i).eval x] using hx
  · simpa only [Complex.norm_real, Real.norm_eq_abs] using hcost

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_native_two_site_models {degree N : ℕ} [NeZero N]
    (hdegree : 1 ≤ degree) {p₁ p₂ : ℝ} (hp₁ : 2 ≤ p₁) (hp₂ : 2 ≤ p₂)
    (X₁ : Seminorm ℂ (ZMod N → ℂ))
    (X₂ : (ZMod N → ℂ) → Seminorm ℂ (ZMod N → ℂ))
    {K₁ K₂ M₁ M₂ beta₁ beta₂ eta : ℝ}
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hbeta₁ : 0 < beta₁) (hbeta₂ : 0 < beta₂) (heta : 0 < eta)
    (hX₁ : ∀ v, X₁ v ≤ K₁ * (𝔼 x, ‖v x‖))
    (hX₂ : ∀ f ∈ nativeCyclicFunctions degree N p₁, ∀ v, X₂ f v ≤ K₂ * (𝔼 x, ‖v x‖))
    (hdetect₁ : NativeModelDetector degree N p₁ X₁ K₁ M₁ beta₁ (eta / 4))
    (hdetect₂ : ∀ f ∈ nativeCyclicFunctions degree N p₁,
      NativeModelDetector degree N p₂ (X₂ f) K₂ M₂ beta₂ (eta * beta₁ / 8))
    (a b : ZMod N → ℂ) (ha : ∀ x, ‖a x‖ ≤ M₁) (hb : ∀ x, ‖b x‖ ≤ M₂) :
    NativeTwoSiteModelingData degree N p₁ p₂ K₁ K₂ beta₁ beta₂ eta X₁ X₂ a b := by
  classical
  let tau₁ := eta / 4
  let tau₂ := eta * beta₁ / 8
  have htau₁ : 0 < tau₁ := by dsimp [tau₁]; positivity
  have htau₂ : 0 < tau₂ := by dsimp [tau₂]; positivity
  obtain ⟨n, hn, f, F, c, ea, hfirst, hc, hea, hnBound⟩ :=
    exists_native_cyclic_model_of_detector hdegree hp₁ X₁ hK₁ hM₁ hbeta₁ htau₁ hX₁ hdetect₁ a ha
  have hf (i) : f i ∈ nativeCyclicFunctions degree N p₁ := ⟨F i⟩
  have hsecond (i) := exists_native_cyclic_model_of_detector hdegree hp₂ (X₂ (f i))
    hK₂ hM₂ hbeta₂ htau₂ (hX₂ (f i) (hf i)) (hdetect₂ (f i) (hf i)) b hb
  choose m hm g G d eb hsecond hd heb hmBound using hsecond
  have herr₂ : (∑ i, ‖c i‖ * X₂ (f i) (eb i)) ≤ (2 / beta₁) * (2 * tau₂) := by
    calc
      _ ≤ ∑ i, ‖c i‖ * (2 * tau₂) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (heb i) (norm_nonneg _))
      _ = (∑ i, ‖c i‖) * (2 * tau₂) := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  have hprecision : 2 * tau₁ + (2 / beta₁) * (2 * tau₂) = eta := by
    dsimp [tau₁, tau₂]
    field_simp
    ring
  have herr : X₁ ea + ∑ i, ‖c i‖ * X₂ (f i) (eb i) ≤ eta := by
    rw [← hprecision]
    exact add_le_add hea herr₂
  let length₁ := 1 + 4 * K₁ ^ 2 / (beta₁ ^ 2 * tau₁ ^ 2)
  let length₂ := 1 + 4 * K₂ ^ 2 / (beta₂ ^ 2 * tau₂ ^ 2)
  have hlength₂ : 0 ≤ length₂ := by dsimp [length₂]; positivity
  have htotal : (Fintype.card (Σ i, Fin (m i)) : ℝ) ≤ length₁ * length₂ := by
    simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    calc
      _ ≤ ∑ _i : Fin n, length₂ := Finset.sum_le_sum (fun i _ => hmBound i)
      _ = (n : ℝ) * length₂ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hnBound hlength₂
  exact ⟨n, hn, f, F, c, ea, m, hm, g, G, d, eb, hfirst, hsecond, hc, hd, herr, hnBound, hmBound, htotal⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_shift_native_two_site_models {degree N : ℕ} [NeZero N] {ι : Type*}
    (hdegree : 1 ≤ degree) {p₁ p₂ : ℝ} (hp₁ : 2 ≤ p₁) (hp₂ : 2 ≤ p₂)
    (T : ι → ZMod N → ℂ) (hT : ∀ i x, ‖T i x‖ ≤ 1)
    (a b : ZMod N → ℂ) {K M beta₁ beta₂ eta : ℝ}
    (hK : 0 < K) (hM : 0 < M) (hbeta₁ : 0 < beta₁) (hbeta₂ : 0 < beta₂) (heta : 0 < eta)
    (ha : ∀ x, ‖a x‖ ≤ M) (hb : ∀ x, ‖b x‖ ≤ K)
    (hdetect₁ : NativeModelDetector degree N p₁ (shiftTestingSeminorm b T) K M beta₁ (eta / 4))
    (hdetect₂ : ∀ f ∈ nativeCyclicFunctions degree N p₁,
      NativeModelDetector degree N p₂ (shiftTestingSeminorm f (translatedTestFamily T))
        1 K beta₂ (eta * beta₁ / 8)) :
    NativeTwoSiteModelingData degree N p₁ p₂ K 1 beta₁ beta₂ eta
      (shiftTestingSeminorm b T) (fun f => shiftTestingSeminorm f (translatedTestFamily T)) a b := by
  apply exists_native_two_site_models hdegree hp₁ hp₂
    (shiftTestingSeminorm b T) (fun f => shiftTestingSeminorm f (translatedTestFamily T))
    hK.le (by norm_num) hM hK hbeta₁ hbeta₂ heta
  · exact shiftTestingSeminorm_le_of_nonneg b T hK.le hb hT
  · intro f hf v
    exact shiftTestingSeminorm_le_of_nonneg f (translatedTestFamily T) (by norm_num)
      (nativeCyclicFunctions_norm hf) (translatedTestFamily_norm_le_one T hT) v
  · exact hdetect₁
  · exact hdetect₂
  · exact ha
  · exact hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftNativePartners
namespace OAI

section

namespace Erdos3.PositiveShiftBasis

open CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_fixed_native_partners :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis s N q a J)
      {I : Type*} {K : I → Type*} [Fintype I] [∀ i, Fintype (K i)]
      {L : I → Type*} {M : ∀ i, K i → Type*}
      [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i k, LieRing (M i k)] [∀ i k, LieAlgebra ℚ (M i k)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [∀ i k, TopologicalSpace (ℝ ⊗[ℚ] M i k)] [∀ i k, IsTopologicalAddGroup (ℝ ⊗[ℚ] M i k)]
      [∀ i k, ContinuousSMul ℝ (ℝ ⊗[ℚ] M i k)] [∀ i k, T2Space (ℝ ⊗[ℚ] M i k)]
      {d : I → ℕ} {e : ∀ i, K i → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      (E : ∀ i k, RationalFilteredNilmanifold (M i k) (s + 1) (e i k))
      (Q : ∀ i, (D i).Niltest (fun _ : Unit => 1))
      (R : ∀ i k, (E i k).Niltest (fun _ : Unit => 1))
      (ea : ZMod N → ℂ) (eb : I → ZMod N → ℂ) (c : I → ℂ) (b : ∀ i, K i → ℂ),
      (∀ n, (a n : ℂ) = (∑ i, c i * (Q i).evalCyclic N (fun _ => n)) + ea n) →
      (∀ i n, (J n : ℂ) = (∑ k, b i k * (R i k).evalCyclic N (fun _ => n)) + eb i n) →
      ∀ {p cap : ℝ}, q ≤ p →
      (∑ i, ‖c i‖) ≤ Real.exp p → (∀ i, (∑ k, ‖b i k‖) ≤ Real.exp p) →
      (∀ n, |J n| ≤ cap) →
      (∀ i, (Q i).ComplexityLE p) → (∀ i k, (R i k).ComplexityLE p) →
      (∀ i, (Q i).normBound ≤ 1) → (∀ i k, (R i k).normBound ≤ 1) →
      (shiftTestingSeminorm (fun n => (J n : ℂ)) B.testingFamily ea +
        ∑ i, ‖c i‖ * shiftTestingSeminorm (fun n => (Q i).evalCyclic N (fun _ => n))
          (translatedTestFamily B.testingFamily) (eb i) ≤ Real.exp (-(2 * q + 2))) →
      (Fintype.card (Sigma K) : ℝ) ≤ Real.exp p →
      ∃ (choice : Fin B.count → Sigma K)
        (freq : ∀ j, L (choice j).1 →ₗ[ℚ] ℚ)
        (freq' : ∀ j, M (choice j).1 (choice j).2 →ₗ[ℚ] ℚ)
        (V : ∀ j, (D (choice j).1).Niltest (fun _ : Unit => 1))
        (W : ∀ j, (E (choice j).1 (choice j).2).Niltest (fun _ : Unit => 1))
        (S : Finset (ZMod N)), S ⊆ B.shifts ∧ S.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (S.card : ℝ) ∧
        (∀ j, (V j).ComplexityLE ((p + C) ^ C) ∧ (V j).orbit = (Q (choice j).1).orbit ∧
          (V j).normBound ≤ 1) ∧
        (∀ j, (W j).ComplexityLE ((p + C) ^ C) ∧
          (W j).orbit = (R (choice j).1 (choice j).2).orbit ∧ (W j).normBound ≤ 1) ∧
        (∀ j i, rationalLogHeight (freq j ((D (choice j).1).basis i)) ≤ (p + C) ^ C) ∧
        (∀ j i, rationalLogHeight (freq' j ((E (choice j).1 (choice j).2).basis i)) ≤ (p + C) ^ C) ∧
        (∀ j z, z ∈ (D (choice j).1).filtration.realification.subgroup (s + 1) → ∀ x,
          (V j).observable (z • x) = character
            ((realifyFunctional (freq j) z.coord : ℝ) : CircleFourier.Circle) * (V j).observable x) ∧
        (∀ j z, z ∈ (E (choice j).1 (choice j).2).filtration.realification.subgroup (s + 1) → ∀ x,
          (W j).observable (z • x) = character
            ((realifyFunctional (freq' j) z.coord : ℝ) : CircleFourier.Circle) * (W j).observable x) ∧
        ∀ h ∈ S, ∀ j, Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n,
          (B.mode h j).evalCyclic N (fun _ => n) * (V j).evalCyclic N (fun _ => n) *
            (W j).evalCyclic N (fun _ => n + h)‖ := by
  classical
  obtain ⟨k, _, hvertical⟩ := exists_fixed_native_vertical_power
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C k) ^ k)
  refine ⟨C, hC, ?_⟩
  intro s N _ q a J B I K _ _ L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E Q R ea eb c b
    ha hb p cap hqp hc hbcoeff hJ hQc hRc hQcap hRcap herror hcount
  have hq : 0 ≤ q := (Nat.cast_nonneg B.dim).trans B.geometry.1
  have hp : 0 ≤ p := hq.trans hqp
  let t := (p + 2) ^ 2
  have hpt : p ≤ t := by dsimp [t]; nlinarith [sq_nonneg p]
  have ht : 0 ≤ t := hp.trans hpt
  have hbud : t + (t + k) ^ k ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hVC : (t + k) ^ k ≤ (p + C) ^ C := by linarith
  obtain ⟨choice, H, hHsub, hHn, hHsize, hHbias⟩ := B.exists_fixed_partners
    (fun i n => (Q i).evalCyclic N (fun _ => n))
    (fun i j n => (R i j).evalCyclic N (fun _ => n)) ea eb c b ha hb hqp hc hbcoeff hJ
    (fun i n => ((Q i).norm_evalCyclic_le N _).trans (hQcap i)) herror hcount
  have hK : (Fintype.card (Fin B.count) : ℝ) ≤ t := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr B.count_le_dim).trans (B.geometry.1.trans (hqp.trans hpt))
  obtain ⟨freq, freq', V, W, S, hsub, hSn, hsize, hV, hW, hheightV, hheightW, hvertV, hvertW, hbias⟩ :=
    hvertical (fun j => D (choice j).1) (fun j => E (choice j).1 (choice j).2)
      (fun j => Q (choice j).1) (fun j => R (choice j).1 (choice j).2) ht hK
      (fun j => (hQc (choice j).1).mono hpt) (fun j => (hRc (choice j).1 (choice j).2).mono hpt)
      (fun j => hQcap (choice j).1) (fun j => hRcap (choice j).1 (choice j).2)
      N H hHn (fun h j n => (B.mode h j).evalCyclic N (fun _ => n))
      (fun h hh j n => ((B.mode h j).norm_evalCyclic_le N _).trans (B.mode_norm h (hHsub hh) j)) hHbias
  refine ⟨choice, freq, freq', V, W, S, hsub.trans hHsub, hSn, ?_, ?_, ?_, ?_, ?_, hvertV, hvertW, ?_⟩
  · calc
      _ ≤ Real.exp (-(t + (t + k) ^ k)) * N :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbud)) (Nat.cast_nonneg N)
      _ = Real.exp (-((t + k) ^ k)) * (Real.exp (-t) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((t + k) ^ k)) * H.card :=
        mul_le_mul_of_nonneg_left hHsize (Real.exp_pos _).le
      _ ≤ S.card := hsize
  · exact fun j => ⟨(hV j).1.mono hVC, (hV j).2⟩
  · exact fun j => ⟨(hW j).1.mono hVC, (hW j).2⟩
  · exact fun j i => (hheightV j i).trans hVC
  · exact fun j i => (hheightW j i).trans hVC
  · exact fun h hh j => (Real.exp_le_exp.mpr (neg_le_neg hVC)).trans (hbias h hh j)

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftRefilteredExpansionSpec
namespace OAI

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

theorem productExpansionBudget_bounds {p : ℝ} (hp : 0 ≤ p) :
    2 ≤ productExpansionBudget p ∧ p ≤ productExpansionBudget p ∧
      (2 * p + 4) ^ 2 ≤ productExpansionBudget p := by
  dsimp [productExpansionBudget]
  constructor
  · nlinarith [sq_nonneg (2 * p + 4)]
  constructor
  · nlinarith [sq_nonneg (2 * p + 4)]
  · linarith

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDetectorContradictionSpec
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

namespace SquareModelData

variable {D : RationalFilteredNilmanifold L (s + 1) d}

theorem quotientModel_adapted (F : D.SquareModelData) :
    ∃ w : _ → ℕ, ∀ j, F.quotientModel.filtration.layer j =
      Submodule.span ℚ (F.quotientModel.basis '' {i | j ≤ w i}) := by
  classical
  refine ⟨quotientFinWeight (squareFinWeight F.weight)
    {i | s + 1 ≤ squareFinWeight F.weight i}, ?_⟩
  exact D.filtration.squareFiltration.topQuotientModel_basis_layers
    (D.filtration.squareFinBasis F.basis F.weight (F.layers 2)) (squareFinWeight F.weight)
    (D.filtration.squareFinBasis_layers F.basis F.weight F.layers)
    (D.filtration.squareLattice D.lattice) F.grid F.grid_pos F.inner F.outer

end SquareModelData
end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDetectorContradiction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_common_anchored_option_factors (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G J σ : Type*} [Fintype J] [Fintype σ] [DecidableEq σ] {L : (Option (Option J ⊕ J)) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Option (Option J ⊕ J)) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (H : Finset G) (_hH : H.Nonempty)
    (P : G → (D none).Niltest (fun _ : σ => 1)) (P₀ : (D (some (.inl none))).Niltest (fun _ : σ => 1))
    (U : G → J → (D none).Niltest (fun _ : σ => 1)) (V : J → (D (some (.inl none))).Niltest (fun _ : σ => 1))
    (A : ∀ j, (D (some (.inl (some j)))).Niltest (fun _ : σ => 1)) (B : G → ∀ j, (D (some (.inr j))).Niltest (fun _ : σ => 1))
    (eta : G → J → L none →ₗ[ℚ] ℚ) (theta : J → L (some (.inl none)) →ₗ[ℚ] ℚ)
    {p : ℝ} (_hp : 2 ≤ p) (_hcard : (Fintype.card (Option (Option J ⊕ J)) : ℝ) ≤ p)
    (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hD : ∀ i, (D i).GeometryComplexityLE p)
    (_hU : ∀ h ∈ H, ∀ j, (U h j).ComplexityLE p ∧ (U h j).orbit = (P h).orbit ∧ (U h j).normBound ≤ 1)
    (_hV : ∀ j, (V j).ComplexityLE p ∧ (V j).orbit = P₀.orbit ∧ (V j).normBound ≤ 1)
    (_hA : ∀ j, (A j).ComplexityLE p ∧ (A j).normBound ≤ 1)
    (_hB : ∀ h ∈ H, ∀ j, (B h j).ComplexityLE p ∧ (B h j).normBound ≤ 1)
    (_heta : ∀ h ∈ H, ∀ j k, rationalLogHeight (eta h j ((D none).basis k)) ≤ p)
    (_htheta : ∀ j k, rationalLogHeight (theta j ((D (some (.inl none))).basis k)) ≤ p)
    (_hvertU : ∀ h ∈ H, ∀ j z, z ∈ (D none).filtration.realification.subgroup s → ∀ x,
      (U h j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (eta h j) z.coord : ℝ) : CircleFourier.Circle) * (U h j).observable x)
    (_hvertV : ∀ j z, z ∈ (D (some (.inl none))).filtration.realification.subgroup s → ∀ x,
      (V j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (theta j) z.coord : ℝ) : CircleFourier.Circle) * (V j).observable x)
    (_hinvariant : ∀ h ∈ H, ∀ z, z ∈ (D none).filtration.realification.subgroup s →
      (∀ j, realifyFunctional (eta h j) z.coord = 0) → ∀ x,
        (P h).observable (z • x) = (P h).observable x)
    (weight : ∀ i, Fin (d i) → ℕ)
    (hFlayers : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ ((D i).basis '' {k | j ≤ weight i k}))
    (origin : G → J → σ → ℤ) (lengths : G → J → σ → ℕ) (_hlengths : ∀ h ∈ H, ∀ j i, 0 < lengths h j i)
    (_hbias : ∀ h ∈ H, ∀ j, Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin h j) (lengths h j),
      (U h j).eval x * star ((V j).eval x) * (A j).eval x * (B h j).eval x‖)
    (side : σ → ℝ) (_hside : ∀ i, Real.exp ((p + C) ^ C) ≤ side i)
    (_hrelative : ∀ h ∈ H, ∀ j i, Real.exp (-p) * side i ≤ lengths h j i),
    let omega := productBasisWeight weight
    let hTotal := pi_layer_span D weight hFlayers
    ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded)
      (m : ℕ) (H' : Finset G),
      H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal)
        omega W.toSubmodule ∧
      (∀ i k, rationalLogHeight
        (((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal).repr (v i) k) ≤
          (p + C) ^ C) ∧
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ h ∈ H', HasFixedProductOrbitFactors D none
        (fun i => (anchoredOptionReferenceData (P h) P₀ A (B h) i).orbit)
        (eta h) side ((p + C) ^ C) m W) ∧
      ∃ freq : ({h // h ∈ H'} × J) → ∀ i, L i →ₗ[ℚ] ℚ,
        (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s →
          realifyFunctional (piFrequency (freq j)) x = 0) ∧
        (∀ h ∈ H', ∀ z, z ∈ (D none).filtration.realification.subgroup s →
          (∀ j, realifyFunctional (freq j none) z.coord = 0) → ∀ x,
            (P h).observable (z • x) = (P h).observable x) := by
  classical
  obtain ⟨c, _, hfactor⟩ := exists_anchored_option_mode_factorization_s2 s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C c) ^ c + (X + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + ((Q + 2) ^ 5 + Q))
  refine ⟨C, hC, ?_⟩
  intro G J σ _ _ _ L _ _ d _ _ _ _ _ _ _ _ D H hH P P₀ U V A B eta theta p
    hp hcard hσ hD hU hV hA hB heta htheta hvertU hvertV hinvariant
    weight hFlayers origin lengths hlengths hbias side hside hrelative
  have hp0 : 0 ≤ p := by linarith
  let q := (p + c) ^ c + (p + 2) ^ 2
  have hpow : 0 ≤ (p + c) ^ c := pow_nonneg (by positivity) _
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hfactorq : (p + c) ^ c ≤ q := le_add_of_nonneg_right (sq_nonneg _)
  have hdimq : (p + 2) ^ 2 ≤ q := le_add_of_nonneg_left hpow
  have hbud : q + ((q + 2) ^ 5 + q) ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp0
  have hqC : q ≤ (p + C) ^ C := by
    have hn : 0 ≤ (q + 2) ^ 5 := by positivity
    linarith
  have hloss : (q + 2) ^ 5 + q ≤ (p + C) ^ C := by linarith
  have hsidepos (i) : 0 < side i := (Real.exp_pos _).trans_le (hside i)
  let g := fun h i => (anchoredOptionReferenceData (P h) P₀ A (B h) i).orbit
  have hdata (h : G) (hh : h ∈ H) :
      ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
        (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded) (m : ℕ),
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis
          (productBasisWeight weight) (pi_layer_span D weight hFlayers))
          (productBasisWeight weight) W.toSubmodule ∧
        (∀ i j, rationalLogHeight
          (((pi D).filtration.associatedGradedBasis (pi D).basis
            (productBasisWeight weight) (pi_layer_span D weight hFlayers)).repr (v i) j) ≤ q) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp q ∧
        HasFixedProductOrbitFactors D none (g h) (eta h) side q m W := by
    obtain ⟨W, v, m, hv, hW, hheight, hm, hmp, hf⟩ :=
      hfactor D (P h) P₀ (U h) V A (B h) (eta h) theta hp hcard hσ hD
        (hU h hh) hV hA (hB h hh) (heta h hh) htheta (hvertU h hh) hvertV
        weight hFlayers (origin h) (lengths h) (hlengths h hh) (hbias h hh) side
        (fun i => (Real.exp_le_exp.mpr (hfactorq.trans hqC)).trans (hside i)) (hrelative h hh)
    exact ⟨W, v, m, hv, hW, (fun i j => (hheight i j).trans hfactorq), hm,
      hmp.trans (Real.exp_le_exp.mpr hfactorq), hf.mono D none hfactorq hsidepos⟩
  have hdim : (Fintype.card (Σ i, Fin (d i)) : ℝ) ≤ q :=
    ((pi_geometry D hp0 hcard hD).1).trans hdimq
  obtain ⟨W, v, m, H', hsub, hnonempty, hlarge, hv, hW, hheight, hm, hmp, hf⟩ :=
    exists_common_product_orbit_factors D none weight hFlayers H hH g eta side hq0 hdim hdata
  have hf' (h : G) (hh : h ∈ H') :
      HasFixedProductOrbitFactors D none (g h) (eta h) side ((p + C) ^ C) m W :=
    (hf h hh).mono D none hqC hsidepos
  obtain ⟨freq, hfreq, hinv⟩ := exists_common_product_frequency_family D none H'
    g eta side ((p + C) ^ C) m W hf' (fun h => (P h).observable)
    (fun h hh => hinvariant h (hsub hh))
  refine ⟨W, v, m, H', hsub, hnonempty, ?_, hv, hW,
    (fun i j => (hheight i j).trans hqC), hm, hmp.trans (Real.exp_le_exp.mpr hqC),
    hf', freq, hfreq, hinv⟩
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hloss))
    (Nat.cast_nonneg _)).trans hlarge

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

theorem exists_common_product_factors (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{u} s N q a J) {L M : Fin B.count → Type u}
      [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
      [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
      (D : ∀ j, RationalFilteredNilmanifold (L j) s (d j))
      (E : ∀ j, RationalFilteredNilmanifold (M j) s (e j))
      (w : Fin B.dim → ℕ) (v : ∀ j, Fin (d j) → ℕ) (v' : ∀ j, Fin (e j) → ℕ)
      (hw : ∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i}))
      (hv : ∀ j k, (D j).filtration.layer k = Submodule.span ℚ ((D j).basis '' {i | k ≤ v j i}))
      (hv' : ∀ j k, (E j).filtration.layer k = Submodule.span ℚ ((E j).basis '' {i | k ≤ v' j i}))
      (A : ∀ j, (D j).Niltest (fun _ : Unit => 1))
      (R : ZMod N → ∀ j, (E j).Niltest (fun _ : Unit => 1))
      (H : Finset (ZMod N)) (h₀ : ZMod N), H ⊆ B.shifts → h₀ ∈ B.shifts →
      ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ j, (D j).GeometryComplexityLE p) → (∀ j, (E j).GeometryComplexityLE p) →
      (∀ j, (A j).ComplexityLE p ∧ (A j).normBound ≤ 1) →
      (∀ h ∈ H, ∀ j, (R h j).ComplexityLE p ∧ (R h j).normBound ≤ 1) →
      ∀ (origin : ZMod N → Fin B.count → Unit → ℤ) (lengths : ZMod N → Fin B.count → Unit → ℕ),
      (∀ h ∈ H, ∀ j i, 0 < lengths h j i) →
      (∀ h ∈ H, ∀ j, Real.exp (-p) ≤
        ‖𝔼 x ∈ translatedIntegerBox (origin h j) (lengths h j),
          (B.mode h j).eval x * star ((B.mode h₀ j).eval x) * (A j).eval x * (R h j).eval x‖) →
      (∀ h ∈ H, ∀ j i, Real.exp (-p) * N ≤ (lengths h j i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ N →
      let T := B.anchoredFactors D E
      let weight := B.anchoredWeights w v v'
      let hT := B.anchoredFactors_layers D E w v v' hw hv hv'
      ∃ (W : LieSubalgebra ℚ (pi T).filtration.AssociatedGraded)
        (b : Fin (Fintype.card (Σ i, Fin (B.anchoredDimension d e i))) → (pi T).filtration.AssociatedGraded)
        (m : ℕ) (H' : Finset (ZMod N)),
        H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H'.card : ℝ) ∧
        Submodule.span ℚ (Set.range b) = W.toSubmodule ∧
        BasisGradedSubmodule ((pi T).filtration.associatedGradedBasis (pi T).basis
          (productBasisWeight weight) (pi_layer_span T weight hT))
          (productBasisWeight weight) W.toSubmodule ∧
        (∀ i k, rationalLogHeight (((pi T).filtration.associatedGradedBasis (pi T).basis
          (productBasisWeight weight) (pi_layer_span T weight hT)).repr (b i) k) ≤ (p + C) ^ C) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ h ∈ H', HasFixedProductOrbitFactors T none
          (fun i => (anchoredOptionReferenceData (B.test h) (B.test h₀) A (R h) i).orbit)
          (B.frequency h) (fun _ : Unit => (N : ℝ)) ((p + C) ^ C) m W) ∧
        ∃ freq : ({h // h ∈ H'} × Fin B.count) → ∀ i, B.anchoredLieSpace L M i →ₗ[ℚ] ℚ,
          (∀ j x, x ∈ (pi T).filtration.realGradedRefiltrationLayer W s →
            realifyFunctional (piFrequency (freq j)) x = 0) ∧
          (∀ h ∈ H', ∀ z : B.model.RealGroup, z ∈ B.model.filtration.realification.subgroup s →
            (∀ j, realifyFunctional (freq j none) z.coord = 0) → ∀ x,
              (B.test h).observable (z • x) = (B.test h).observable x) := by
  classical
  obtain ⟨c, _, hfactor⟩ := exists_common_anchored_option_factors s hs
  let X : Polynomial ℕ := Polynomial.X
  let P := 2 * X + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C c) ^ c + X + P)
  refine ⟨C, hC, ?_⟩
  intro N _ q a J B L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E w v v' hw hv hv' A R H h₀
    hsub hh₀ p hp hqp hH hD hE hA hR origin lengths hlengths hbias hrelative hN
  let T := B.anchoredFactors D E
  let weight := B.anchoredWeights w v v'
  have hT := B.anchoredFactors_layers D E w v v' hw hv hv'
  let : FiniteDimensional ℚ (∀ i, B.anchoredLieSpace L M i) :=
    (productFinBasis T).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, B.anchoredLieSpace L M i))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, B.anchoredLieSpace L M i))
  let := realification_moduleTopology_t2 (pi T).basis
  let t := 2 * p + 4
  have hp0 : 0 ≤ p := by linarith
  have ht : 2 ≤ t := by dsimp [t]; linarith
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hqt : q ≤ t := hqp.trans hpt
  have hbud : (t + c) ^ c + p + t ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp0
  have hfC : (t + c) ^ c ≤ (p + C) ^ C := by linarith
  have hloss : (t + c) ^ c + p ≤ (p + C) ^ C := by linarith
  have hNm : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hHn : H.Nonempty := Finset.card_pos.mp (by
    exact_mod_cast ((mul_pos (Real.exp_pos (-p)) hNm).trans_le hH))
  have hm : (B.count : ℝ) ≤ p := (Nat.cast_le.mpr B.count_le_dim).trans (B.geometry.1.trans hqp)
  have hcard : (Fintype.card (Option (Option (Fin B.count) ⊕ Fin B.count)) : ℝ) ≤ t := by
    simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    dsimp [t]
    linarith
  have hgeometry (i) : (T i).GeometryComplexityLE t :=
    (B.anchoredFactors_geometry D E hqp hD hE i).mono (T i) hpt
  obtain ⟨W, b, m, H', hHH, hH'n, hlarge, hspan, hgraded, hheight, hmpos, hmbound, hfactors, freq, hfreq, hinv⟩ :=
    hfactor T H hHn B.test (B.test h₀) B.mode (B.mode h₀) A R B.frequency (B.frequency h₀)
      ht hcard (by simpa only [Fintype.card_unit, Nat.cast_one] using (by linarith : (1 : ℝ) ≤ t))
      hgeometry
      (fun h hh j => ⟨(B.mode_complexity h (hsub hh) j).mono hqt, B.mode_orbit h (hsub hh) j, B.mode_norm h (hsub hh) j⟩)
      (fun j => ⟨(B.mode_complexity h₀ hh₀ j).mono hqt, B.mode_orbit h₀ hh₀ j, B.mode_norm h₀ hh₀ j⟩)
      (fun j => ⟨(hA j).1.mono hpt, (hA j).2⟩)
      (fun h hh j => ⟨(hR h hh j).1.mono hpt, (hR h hh j).2⟩)
      (fun h hh j i => (B.frequency_height h (hsub hh) j i).trans hqt)
      (fun j i => (B.frequency_height h₀ hh₀ j i).trans hqt)
      (fun h hh => B.mode_vertical h (hsub hh)) (B.mode_vertical h₀ hh₀)
      (fun h hh => B.test_invariant h (hsub hh)) weight hT origin lengths hlengths
      (fun h hh j => (Real.exp_le_exp.mpr (neg_le_neg hpt)).trans (hbias h hh j))
      (fun _ : Unit => (N : ℝ)) (fun _ => (Real.exp_le_exp.mpr hfC).trans hN)
      (fun h hh j i => (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpt)) hNm.le).trans
        (hrelative h hh j i))
  refine ⟨W, b, m, H', hHH, hH'n, ?_, hspan, hgraded,
    (fun i k => (hheight i k).trans hfC), hmpos, hmbound.trans (Real.exp_le_exp.mpr hfC),
    (fun h hh => (hfactors h hh).mono T none hfC (fun _ => hNm)), freq, hfreq, hinv⟩
  calc
    _ ≤ Real.exp (-((t + c) ^ c + p)) * N :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hloss)) hNm.le
    _ = Real.exp (-((t + c) ^ c)) * (Real.exp (-p) * N) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-((t + c) ^ c)) * H.card := mul_le_mul_of_nonneg_left hH (Real.exp_pos _).le
    _ ≤ H'.card := hlarge

end Erdos3.PositiveShiftBasis

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_prescribed_common_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ PrescribedCommonFactorizationSpec.{u} s C := by
  classical
  obtain ⟨c, _, hlower⟩ := exists_prescribed_lower_inputs_s2 s
  obtain ⟨k, _, hcommon⟩ := exists_common_product_factors s hs
  let X : Polynomial ℕ := Polynomial.X
  let V := (X + Polynomial.C c) ^ c
  let P := X + 2 + V
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (V + (P + Polynomial.C k) ^ k + P)
  refine ⟨C, hC, ?_⟩
  dsimp only [PrescribedCommonFactorizationSpec]
  intro N _ q a J B w hw L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ T H hH p hp hqp hsize hTc hTn χ hvert hcorr hN
  have hp0 : 0 ≤ p := by linarith
  let r := p + 2 + (p + c) ^ c
  have hV0 : 0 ≤ (p + c) ^ c := by positivity
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hVr : (p + c) ^ c ≤ r := by dsimp [r]; linarith
  have hr : 2 ≤ r := by dsimp [r]; linarith
  have hr0 : 0 ≤ r := by linarith
  have hbud : (p + c) ^ c + (r + k) ^ k + r ≤ (p + C) ^ C := by
    simpa [V, P, X, r, Polynomial.eval₂_pow] using hbudget p hp0
  have hk0 : 0 ≤ (r + k) ^ k := by positivity
  have hVC : (p + c) ^ c ≤ (p + C) ^ C := by linarith
  have hkC : (r + k) ^ k ≤ (p + C) ^ C := by linarith
  obtain ⟨F, hFfull, hFquot, hFheight, h₀, hh₀, branches, S₀, hS₀H, hS₀n, hS₀large,
      A, R, η, γ, rSq, hA, hR, hinterval⟩ := hlower B D T H hH hp hqp hsize hTc hTn χ hvert hcorr
  let E := fun j => (F (j, true)).quotientModel
  let Q := fun j => (F (j, false)).quotientModel
  choose v hv using fun j => (F (j, true)).quotientModel_adapted
  choose v' hv' using fun j => (F (j, false)).quotientModel_adapted
  choose start len hlen hbound hshort hvol hbias using hinterval
  let origin (h : ZMod N) (j : Fin B.count) : Unit → ℤ :=
    if hh : h ∈ S₀ then fun _ => (start h hh j : ℤ) else 0
  let lengths (h : ZMod N) (j : Fin B.count) : Unit → ℕ :=
    if hh : h ∈ S₀ then fun _ => len h hh j else fun _ => 1
  have hlengths (h) (hh : h ∈ S₀) (j i) : 0 < lengths h j i := by
    simpa only [lengths, dif_pos hh] using hlen h hh j
  have hcorr' (h) (hh : h ∈ S₀) (j) : Real.exp (-r) ≤
      ‖𝔼 x ∈ translatedIntegerBox (origin h j) (lengths h j),
        (B.mode h j).eval x * star ((B.mode h₀ j).eval x) * (A j).eval x * (R h j).eval x‖ := by
    simpa only [origin, lengths, dif_pos hh] using
      (Real.exp_le_exp.mpr (neg_le_neg hVr)).trans (hbias h hh j)
  have hrelative (h) (hh : h ∈ S₀) (j i) : Real.exp (-r) * N ≤ (lengths h j i : ℝ) := by
    simpa only [lengths, dif_pos hh] using
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hVr)) (Nat.cast_nonneg N)).trans (hvol h hh j)
  have hsize' : Real.exp (-r) * N ≤ (S₀.card : ℝ) :=
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hVr)) (Nat.cast_nonneg N)).trans hS₀large
  have hRsmall (h j) : (R h j).ComplexityLE r ∧ (R h j).normBound ≤ 1 := by
    obtain ⟨_, _, _, _, hn, hc, _⟩ := hR h j
    exact ⟨hc.mono hVr, hn⟩
  obtain ⟨W, b, m, S, hSS₀, hSn, hSlarge, hspan, hgraded, hheight, hm, hmb, hfactors, freq, hfreq, hinv⟩ :=
    hcommon B E Q w v v' hw hv hv' A R S₀ h₀ (hS₀H.trans hH) (hH hh₀)
      hr (hqp.trans hpr) hsize'
      (fun j => (hFquot (j, true)).mono (E j) hVr)
      (fun j => (hFquot (j, false)).mono (Q j) hVr)
      (fun j => ⟨(hA j).2.1.mono hVr, (hA j).1⟩) (fun h _ j => hRsmall h j)
      origin lengths hlengths hcorr' hrelative ((Real.exp_le_exp.mpr hkC).trans hN)
  let G : B.CommonFactorization E Q A R h₀ H ((r + k) ^ k) := {
    weight := B.anchoredWeights w v v'
    adapted := B.anchoredFactors_layers E Q w v v' hw hv hv'
    subalgebra := W
    spanning := b
    span_eq := hspan
    graded := hgraded
    height := hheight
    denominator := m
    denominator_pos := hm
    denominator_bound := hmb
    shifts := S
    shifts_sub := hSS₀.trans hS₀H
    shifts_nonempty := hSn
    shifts_large := hSlarge
    factors := hfactors
    frequency := freq
    frequency_zero := hfreq
    invariant := hinv }
  refine ⟨F, (fun i => (hFfull i).mono (F i).fullModel hVC),
    (fun i => (hFquot i).mono (F i).quotientModel hVC),
    (fun i j l => (hFheight i j l).trans hVC), h₀, hh₀, branches, A, R, η, γ, rSq, ?_, ?_, ⟨G.mono hkC⟩⟩
  · exact fun j => ⟨(hA j).1, (hA j).2.1.mono hVC, (hA j).2.2⟩
  · intro h j
    obtain ⟨hγ, hη, hnorm, hOrbit, hn, hc, hval⟩ := hR h j
    exact ⟨hγ, (fun i => (hη i).trans (Real.exp_le_exp.mpr hVC)), hnorm, hOrbit, hn, hc.mono hVC, hval⟩

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_native_partner_contradiction (s c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ C : ℕ, 2 ≤ C ∧ NativePartnerContradictionSpec s C epsilon := by
  classical
  obtain ⟨k, _, hfactor⟩ := exists_prescribed_common_factorization (s + 1) (by omega)
  obtain ⟨d, _, hcontra⟩ := exists_factored_positive_shift_contradiction_s2 s c hc hepsilon hepsilon1 hshift
  let X : Polynomial ℕ := Polynomial.X
  let V := (X + Polynomial.C k) ^ k
  let P := X + 2 + V
  let Z := (2 * P + 4) ^ 2 + P + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Z ^ d + V + P)
  refine ⟨C, hC, ?_⟩
  dsimp only [NativePartnerContradictionSpec]
  intro N _ q f₁ f₂ weight B w hw L _ _ dims _ _ _ _ D _ _ _ _ _ _ _ _ T H
    hH p hp hqp hsize hTc hTn χ hvertical hcorrelation hodd hN hf₁ hf₂ hweight hcompare
  have hp0 : 0 ≤ p := by linarith
  let v := (p + k) ^ k
  let r := p + 2 + v
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hr : 2 ≤ r := by dsimp [r]; linarith
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hvr : v ≤ r := by dsimp [r]; linarith
  have hbud : (productExpansionBudget r + 2) ^ d + v + r ≤ (p + C) ^ C := by
    have heq : productExpansionBudget r + 2 = (2 * r + 4) ^ 2 + r + 4 := by
      dsimp [productExpansionBudget]
      ring
    rw [heq]
    simpa [Z, P, V, X, r, v, Polynomial.eval₂_pow] using hbudget p hp0
  have hcut0 : 0 ≤ (productExpansionBudget r + 2) ^ d := by
    have := (productExpansionBudget_bounds (by linarith : 0 ≤ r)).1
    positivity
  have hvC : v ≤ (p + C) ^ C := by linarith
  have hcutC : (productExpansionBudget r + 2) ^ d ≤ (p + C) ^ C := by linarith
  obtain ⟨Y, hYfull, hYquot, hYheight, anchor, _, branches, A, R, η, γ, rSq, _, hR, ⟨F⟩⟩ :=
    hfactor B w hw D T H hH hp hqp hsize hTc hTn χ hvertical hcorrelation
      ((Real.exp_le_exp.mpr hvC).trans hN)
  let G := F.mono hvr
  have hcomparison : CyclicNiltestUpperComparison.{0} (s + 2) N ((productExpansionBudget r + 2) ^ d)
      (Real.exp (-((productExpansionBudget r + 2) ^ d))) f₁ f₂ := by
    intro K _ _ degree dim _ _ _ _ E hdegree S hS hSc
    exact (hcompare E hdegree S hS (hSc.mono hcutC)).trans
      (Real.exp_le_exp.mpr (neg_le_neg hcutC))
  exact hcontra B (fun j => (Y (j, true)).quotientModel) (fun j => D (j, false))
    (fun j => Y (j, false)) A R anchor H G hH hr (hqp.trans hpr)
    (fun j => (hYquot (j, true)).mono (Y (j, true)).quotientModel hvr)
    (fun j => (hTc (j, false)).1.mono (D (j, false)) hpr)
    (fun j => (hYfull (j, false)).mono (Y (j, false)).fullModel hvr)
    (fun j => (hYquot (j, false)).mono (Y (j, false)).quotientModel hvr)
    (fun j i l => (hYheight (j, false) i l).trans hvr)
    (fun j => (T (j, false)).orbit) branches η γ rSq
    (fun h _ j => (hR h j).1)
    (fun h _ j i => ((hR h j).2.1 i).trans (Real.exp_le_exp.mpr hvr))
    (fun h _ j => (hR h j).2.2.1) (fun h _ j => (hR h j).2.2.2.1)
    hodd ((Real.exp_le_exp.mpr hcutC).trans hN)
    (fun n => ⟨(hf₁ n).1, (hf₁ n).2.trans (Real.exp_le_exp.mpr hpr)⟩)
    (fun n => ⟨(hf₂ n).1, (hf₂ n).2.trans (Real.exp_le_exp.mpr hpr)⟩)
    (fun n => ⟨(hweight n).1, (hweight n).2.trans (Real.exp_le_exp.mpr hpr)⟩)
    hcomparison

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_native_partner_pair_contradiction (s c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ C : ℕ, 2 ≤ C ∧ NativePartnerPairContradictionSpec s C epsilon := by
  classical
  obtain ⟨C, hC, hcontra⟩ := exists_native_partner_contradiction s c hc hepsilon hepsilon1 hshift
  refine ⟨C, hC, ?_⟩
  dsimp only [NativePartnerPairContradictionSpec]
  intro N _ q f₁ f₂ weight B w hw L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E V W H
    hH p hp hqp hsize hV hW hVn hWn χ χ' hχ hχ' hbias hodd hN hf₁ hf₂ hweight hcompare
  let K : Fin B.count × Bool → Type := fun j => BoolLieFamily (L j.1) (M j.1) j.2
  let dims : Fin B.count × Bool → ℕ := fun j => Bool.rec (e j.1) (d j.1) j.2
  let T : ∀ j, RationalFilteredNilmanifold (K j) (s + 1 + 1) (dims j) := fun j => by
    rcases j with ⟨j, b⟩
    cases b
    · exact E j
    · exact D j
  let U : ∀ j, (T j).Niltest (fun _ : Unit => 1) := fun j => by
    rcases j with ⟨j, b⟩
    cases b
    · exact W j
    · exact V j
  let char : ∀ j, (T j).RealGroup → CircleFourier.Circle := fun j => by
    rcases j with ⟨j, b⟩
    cases b
    · exact χ' j
    · exact χ j
  let : ∀ j, FiniteDimensional ℚ (K j) := by
    intro j
    exact (T j).basis.finiteDimensional_of_finite
  let Sq := fun j => (T j).filtration.squareLieSubalgebra
  let Qu := fun j => Sq j ⧸ (T j).filtration.squareFiltration.layerIdeal (s + 1 + 1)
  let : ∀ j, FiniteDimensional ℚ (Sq j) := fun _ => inferInstance
  let : ∀ j, FiniteDimensional ℚ (Qu j) := fun _ => inferInstance
  let : ∀ j, TopologicalSpace (ℝ ⊗[ℚ] Sq j) := fun j => moduleTopology ℝ (ℝ ⊗[ℚ] Sq j)
  let : ∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Sq j) := fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Sq j) := fun _ => inferInstance
  let : ∀ j, T2Space (ℝ ⊗[ℚ] Sq j) := fun j => realification_moduleTopology_t2 (Module.finBasis ℚ (Sq j))
  let : ∀ j, TopologicalSpace (ℝ ⊗[ℚ] Qu j) := fun j => moduleTopology ℝ (ℝ ⊗[ℚ] Qu j)
  let : ∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Qu j) := fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Qu j) := fun _ => inferInstance
  let : ∀ j, T2Space (ℝ ⊗[ℚ] Qu j) := fun j => realification_moduleTopology_t2 (Module.finBasis ℚ (Qu j))
  have hU (j) : (U j).ComplexityLE p := by
    rcases j with ⟨j, b⟩
    cases b
    · exact hW j
    · exact hV j
  have hUn (j) : (U j).normBound ≤ 1 := by
    rcases j with ⟨j, b⟩
    cases b
    · exact hWn j
    · exact hVn j
  have hchar (j z) (hz : z ∈ (T j).filtration.realification.subgroup (s + 1 + 1)) (x) :
      (U j).observable (z • x) = character (char j z) * (U j).observable x := by
    rcases j with ⟨j, b⟩
    cases b
    · exact hχ' j z hz x
    · exact hχ j z hz x
  exact hcontra B w hw T U H hH hp hqp hsize hU hUn char hchar hbias
    hodd hN hf₁ hf₂ hweight hcompare

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_two_site_model_contradiction (s c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ C : ℕ, 2 ≤ C ∧ TwoSiteModelContradictionSpec s C epsilon := by
  classical
  obtain ⟨a, _, hpartners⟩ := exists_fixed_native_partners
  obtain ⟨k, _, hcontra⟩ := exists_native_partner_pair_contradiction s c hc hepsilon hepsilon1 hshift
  let X : Polynomial ℕ := Polynomial.X
  let V := (X + Polynomial.C a) ^ a
  let P := X + 2 + V
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C k) ^ k + P)
  refine ⟨C, hC, ?_⟩
  dsimp only [TwoSiteModelContradictionSpec]
  intro N _ q f₁ f₂ weight B w hw I K _ _ L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E Q R
    ea eb coeff coeff' ha hb p hp hqp hcoeff hcoeff' hQ hR hQn hRn herror hcount
    hodd hN hf₁ hf₂ hweight hcompare
  have hp0 : 0 ≤ p := by linarith
  let v := (p + a) ^ a
  let r := p + 2 + v
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hr : 2 ≤ r := by dsimp [r]; linarith
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hvr : v ≤ r := by dsimp [r]; linarith
  have hbud : (r + k) ^ k + r ≤ (p + C) ^ C := by
    simpa [P, V, X, r, v, Polynomial.eval₂_pow] using hbudget p hp0
  have hcut : (r + k) ^ k ≤ (p + C) ^ C := by linarith
  have hweight' (n) : |weight n| ≤ Real.exp p := by
    rw [abs_of_nonneg (hweight n).1]
    exact (hweight n).2
  obtain ⟨choice, freq, freq', V₀, W₀, H, hH, _, hsize, hV, hW, _, _, hvertV, hvertW, hbias⟩ :=
    hpartners B D E Q R ea eb coeff coeff' ha hb hqp hcoeff hcoeff' hweight' hQ hR hQn hRn herror hcount
  have hcomparison : CyclicNiltestUpperComparison.{0} (s + 2) N ((r + k) ^ k)
      (Real.exp (-((r + k) ^ k))) f₁ f₂ := by
    intro J _ _ degree dim _ _ _ _ F hdegree S hS hSc
    exact (hcompare F hdegree S hS (hSc.mono hcut)).trans
      (Real.exp_le_exp.mpr (neg_le_neg hcut))
  exact hcontra B w hw (fun j => D (choice j).1) (fun j => E (choice j).1 (choice j).2)
    V₀ W₀ H hH hr (hqp.trans hpr)
    ((mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hvr)) (Nat.cast_nonneg N)).trans hsize)
    (fun j => (hV j).1.mono hvr) (fun j => (hW j).1.mono hvr)
    (fun j => (hV j).2.2) (fun j => (hW j).2.2)
    (fun j z => ((realifyFunctional (freq j) z.coord : ℝ) : CircleFourier.Circle))
    (fun j z => ((realifyFunctional (freq' j) z.coord : ℝ) : CircleFourier.Circle))
    hvertV hvertW (fun h hh j => (Real.exp_le_exp.mpr (neg_le_neg hvr)).trans (hbias h hh j))
    hodd ((Real.exp_le_exp.mpr hcut).trans hN)
    (fun n => ⟨(hf₁ n).1, (hf₁ n).2.trans (Real.exp_le_exp.mpr hpr)⟩)
    (fun n => ⟨(hf₂ n).1, (hf₂ n).2.trans (Real.exp_le_exp.mpr hpr)⟩)
    (fun n => ⟨(hweight n).1, (hweight n).2.trans (Real.exp_le_exp.mpr hpr)⟩)
    hcomparison

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_native_detector_contradiction_s2_oai (s c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeDetectorContradictionSpec s C epsilon := by
  classical
  obtain ⟨C, hC, hcontra⟩ := exists_two_site_model_contradiction s c hc hepsilon hepsilon1 hshift
  refine ⟨C, hC, ?_⟩
  dsimp only [NativeDetectorContradictionSpec]
  intro N _ q f₁ f₂ weight B w hw p p₁ p₂ K M beta₁ beta₂ hp hp₁ hp₂ hqp hp₁p hp₂p
    hK hM hbeta₁ hbeta₂ ha hb hcoeff₁ hcoeff₂ hlength hdetect₁ hdetect₂
    hodd hN hf₁ hf₂ hweight hcompare
  have hdata := exists_shift_native_two_site_models (by omega : 1 ≤ s + 1 + 1) hp₁ hp₂
    B.testingFamily B.testingFamily_norm_le
    (fun n => ((f₁ n - (1 + epsilon) * f₂ n : ℝ) : ℂ)) (fun n => (weight n : ℂ))
    hK hM hbeta₁ hbeta₂ (Real.exp_pos _) ha hb hdetect₁ hdetect₂
  obtain ⟨n, _, f, F, coeff, ea, m, _, g, G, coeff', eb,
    hfirst, hsecond, hcoeff, hcoeff', herr, _, _, htotal⟩ := hdata
  have hvalues (i : Fin n) : (fun x => (F i).test.evalCyclic N (fun _ => x)) = f i :=
    funext (fun x => ((F i).eval x).symm)
  have herr' : shiftTestingSeminorm (fun n => (weight n : ℂ)) B.testingFamily ea +
      ∑ i, ‖coeff i‖ * shiftTestingSeminorm
        (fun x => (F i).test.evalCyclic N (fun _ => x))
        (translatedTestFamily B.testingFamily) (eb i) ≤ Real.exp (-(2 * q + 2)) := by
    simpa only [hvalues] using herr
  have htotal' : (Fintype.card (Σ i, Fin (m i)) : ℝ) ≤ Real.exp p := by
    apply htotal.trans
    simpa only [one_pow, mul_one] using hlength
  exact hcontra B w hw (fun i => (F i).model) (fun i j => (G i j).model)
    (fun i => (F i).test) (fun i j => (G i j).test) ea eb coeff coeff'
    hfirst hsecond hp hqp (hcoeff.trans hcoeff₁) (fun i => (hcoeff' i).trans hcoeff₂)
    (fun i => (F i).complexity.mono hp₁p) (fun i j => (G i j).complexity.mono hp₂p)
    (fun i => (F i).norm) (fun i j => (G i j).norm) herr' htotal'
    hodd hN hf₁ hf₂ hweight hcompare

end Erdos3.PositiveShiftBasis

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.PositiveShiftBasis.exists_native_detector_contradiction_s2_oai := @OAI.Erdos3.PositiveShiftBasis.exists_native_detector_contradiction_s2_oai
