-- Prove2me | solution 1 for OAI.Erdos3.PositiveShiftBasis.exists_prescribed_lower_inputs_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:59:46.79099+00:00
-- url     : https://prove2.me/submissions/e2cfa4f7-c07a-4ec1-b3b0-f0cc88307c44

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B210

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AnchorLossBudget
namespace OAI

section

namespace Erdos3

theorem anchor_power_lower {p delta : ℝ} {m : ℕ} (hp : 0 ≤ p)
    (hm : (m : ℝ) ≤ p) (hdelta : Real.exp (-p) ≤ delta) :
    Real.exp (-(2 * p ^ 2)) ≤ delta ^ (2 * m) := by
  have hm' : ((2 * m : ℕ) : ℝ) ≤ 2 * p := by push_cast; linarith
  calc
    _ ≤ Real.exp (((2 * m : ℕ) : ℝ) * (-p)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp (-p) ^ (2 * m) := Real.exp_nat_mul _ _
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) hdelta _

theorem anchor_halved_power_lower {p delta : ℝ} {m : ℕ} (hp : 0 ≤ p)
    (hm : (m : ℝ) ≤ p) (hdelta : Real.exp (-p) ≤ delta) :
    Real.exp (-(2 * p ^ 2) - 1) ≤ delta ^ (2 * m) / 2 := by
  have hd0 : 0 ≤ delta := (Real.exp_nonneg _).trans hdelta
  rw [Real.exp_sub]
  apply div_le_div₀ (pow_nonneg hd0 _) (anchor_power_lower hp hm hdelta) (by norm_num)
  have h := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem anchor_branch_lower {p : ℝ} {m : ℕ} (hm : (m : ℝ) ≤ p) :
    Real.exp (-(4 * p)) ≤ Real.exp (-Real.log 4 * m) := by
  apply Real.exp_le_exp.mpr
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

theorem anchored_interval_budget {p delta : ℝ} {m : ℕ} (hp : 2 ≤ p)
    (hm : (m : ℝ) ≤ p) (hdelta : Real.exp (-p) ≤ delta) :
    Real.exp (-((p + 2) ^ 3)) ≤ delta ^ (2 * m) / 40 := by
  have hp0 : 0 ≤ p := by linarith
  have hd0 : 0 ≤ delta := (Real.exp_nonneg _).trans hdelta
  have h40 : (40 : ℝ) ≤ Real.exp 6 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 6
    rw [← Real.exp_nat_mul] at hpow
    norm_num at hpow
    linarith
  calc
    _ ≤ Real.exp (-(2 * p ^ 2) - 6) := by
      apply Real.exp_le_exp.mpr
      nlinarith [pow_nonneg hp0 3, sq_nonneg p]
    _ = Real.exp (-(2 * p ^ 2)) / Real.exp 6 := Real.exp_sub _ _
    _ ≤ _ := div_le_div₀ (pow_nonneg hd0 _) (anchor_power_lower hp0 hm hdelta) (by norm_num) h40

theorem anchored_density_budget {p delta sigma : ℝ} {m : ℕ} (hp : 2 ≤ p)
    (hm : (m : ℝ) ≤ p) (hdelta : Real.exp (-p) ≤ delta) (hsigma : Real.exp (-p) ≤ sigma) :
    Real.exp (-((p + 2) ^ 3)) ≤
      Real.exp (-Real.log 4 * m) * (delta ^ (2 * m) / 2) * sigma := by
  have hp0 : 0 ≤ p := by linarith
  have hd0 : 0 ≤ delta := (Real.exp_nonneg _).trans hdelta
  have hmul := mul_le_mul (anchor_branch_lower hm) (anchor_halved_power_lower hp0 hm hdelta)
    (Real.exp_nonneg _) (Real.exp_nonneg _)
  have htotal := mul_le_mul hmul hsigma (Real.exp_nonneg _)
    (mul_nonneg (Real.exp_nonneg _) (by positivity))
  apply le_trans _ htotal
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [pow_nonneg hp0 3, sq_nonneg p]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω H : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

theorem complexMean_eq_correlation_one (v : Ω → ℂ) :
    p.complexMean v = p.correlation v (fun _ => 1) := by
  simp only [correlation, complexMean, star_one, mul_one]

theorem norm_complexMean_sq_le (v : Ω → ℂ) :
    ‖p.complexMean v‖ ^ 2 ≤ p.mean (fun x => ‖v x‖ ^ 2) := by
  rw [p.complexMean_eq_correlation_one]
  have h := p.norm_correlation_sq_le v (fun _ => 1)
  simpa only [norm_one, one_pow, p.mean_const, mul_one] using h

theorem mean_norm_sq_le_one (v : Ω → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1) :
    p.mean (fun x => ‖v x‖ ^ 2) ≤ 1 := by
  apply (p.mean_mono (fun x => ?_)).trans_eq (p.mean_const 1)
  nlinarith [hv x, norm_nonneg (v x)]

theorem norm_correlation_le_one (v w : Ω → ℂ)
    (hv : ∀ x, ‖v x‖ ≤ 1) (hw : ∀ x, ‖w x‖ ≤ 1) : ‖p.correlation v w‖ ≤ 1 := by
  have hcs := p.norm_correlation_sq_le v w
  have hprod := (mul_le_of_le_one_left (p.mean_nonneg (fun x => sq_nonneg ‖w x‖))
    (p.mean_norm_sq_le_one v hv)).trans (p.mean_norm_sq_le_one w hw)
  nlinarith [norm_nonneg (p.correlation v w)]

theorem correlation_mul_phases (v w : Ω → ℂ) (a b : ℂ) :
    p.correlation (fun x => a * v x) (fun x => b * w x) =
      (a * star b) * p.correlation v w := by
  unfold correlation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [star_mul]
  ring

theorem norm_correlation_mul_phases (v w : Ω → ℂ) {a b : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖p.correlation (fun x => a * v x) (fun x => b * w x)‖ = ‖p.correlation v w‖ := by
  rw [p.correlation_mul_phases, norm_mul, norm_mul, norm_star, ha, hb, one_mul, one_mul]

variable [Fintype H]

theorem complexMean_average (v : H → Ω → ℂ) :
    p.complexMean (fun x => 𝔼 h, v h x) = 𝔼 h, p.complexMean (v h) := by
  unfold complexMean
  simp_rw [Finset.mul_expect]
  exact (Finset.expect_sum_comm _ _ _).symm

theorem correlation_average_left (v : H → Ω → ℂ) (w : Ω → ℂ) :
    p.correlation (fun x => 𝔼 h, v h x) w = 𝔼 h, p.correlation (v h) w := by
  unfold correlation
  simp_rw [Finset.expect_mul, Finset.mul_expect]
  exact (Finset.expect_sum_comm _ _ _).symm

theorem correlation_average_right (v : Ω → ℂ) (w : H → Ω → ℂ) :
    p.correlation v (fun x => 𝔼 h, w h x) = 𝔼 h, p.correlation v (w h) := by
  unfold correlation
  simp_rw [← expect_star, Finset.mul_expect]
  exact (Finset.expect_sum_comm _ _ _).symm

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {Ω : J → Type*} [∀ j, Fintype (Ω j)]

theorem complexMean_pi_product (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (v : ∀ j, Ω j → ℂ) :
    (pi p).complexMean (fun x => ∏ j, v j (x j)) = ∏ j, (p j).complexMean (v j) := by
  classical
  change (∑ x : ∀ j, Ω j, ((∏ j, (p j).weight (x j) : ℝ) : ℂ) * (∏ j, v j (x j))) =
    ∏ j, ∑ x, ((p j).weight x : ℂ) * v j x
  simp_rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j (x : Ω j) => ((p j).weight x : ℂ) * v j x)).symm

theorem correlation_pi_product (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (v w : ∀ j, Ω j → ℂ) :
    (pi p).correlation (fun x => ∏ j, v j (x j)) (fun x => ∏ j, w j (x j)) =
      ∏ j, (p j).correlation (v j) (w j) := by
  classical
  change (pi p).complexMean (fun x => (∏ j, v j (x j)) * star (∏ j, w j (x j))) =
    ∏ j, (p j).complexMean (fun x => v j x * star (w j x))
  simp_rw [star_prod, ← Finset.prod_mul_distrib]
  exact complexMean_pi_product p (fun j x => v j x * star (w j x))

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem uniform_correlation {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f g : Ω → ℂ) :
    (uniform Ω).correlation f g = 𝔼 x, f x * star (g x) :=
  uniform_complexMean _

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseCorrelationPairs
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {H Ω : Type*} [Fintype H] [Fintype Ω]

theorem weighted_mean_square_eq_pair_correlation
    (p : FiniteProbabilityWeights Ω) (v : H → Ω → ℂ) :
    p.mean (fun x => ‖𝔼 h, v h x‖ ^ 2) =
      𝔼 h, 𝔼 k, (p.correlation (v h) (v k)).re := by
  have h := congrArg Complex.re (p.correlation_average_left v (fun x => 𝔼 k, v k x))
  rw [p.correlation_self, Complex.ofReal_re] at h
  simpa only [p.correlation_average_right, expect_re] using h

theorem exists_weighted_common_anchor [Nonempty H]
    (p : FiniteProbabilityWeights Ω) (v : H → Ω → ℂ) {a : ℝ}
    (ha : 0 ≤ a) (hv : ∀ h x, ‖v h x‖ ≤ 1)
    (hmean : ∀ h, a ≤ (p.complexMean (v h)).re) :
    ∃ (h₀ : H) (S : Finset H), a ^ 2 / 2 * Fintype.card H ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, a ^ 2 / 2 ≤ ‖p.correlation (v h) (v h₀)‖ := by
  have hmean' : a ≤ (p.complexMean (fun x => 𝔼 h, v h x)).re := by
    rw [p.complexMean_average, expect_re]
    exact (Fintype.expect_const a).symm.trans_le (Finset.expect_le_expect (fun h _ => hmean h))
  have hnorm := hmean'.trans (Complex.re_le_norm _)
  have henergy := (pow_le_pow_left₀ ha hnorm 2).trans
    (p.norm_complexMean_sq_le (fun x => 𝔼 h, v h x))
  rw [weighted_mean_square_eq_pair_correlation] at henergy
  rw [Finset.expect_comm] at henergy
  obtain ⟨h₀, _, hslice⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty henergy
  have hcap (h : H) : (p.correlation (v h) (v h₀)).re ≤ 1 :=
    (Complex.re_le_norm _).trans (p.norm_correlation_le_one _ _ (hv h) (hv h₀))
  obtain ⟨S, hcard, hS⟩ := exists_dense_level_set
    (fun h => (p.correlation (v h) (v h₀)).re) (sq_nonneg a) hcap hslice
  exact ⟨h₀, S, hcard, fun h hh => (hS h hh).trans (Complex.re_le_norm _)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_common_anchor {H J : Type*} [Fintype H] [Nonempty H] [Fintype J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (v : H → ∀ j, Ω j → ℂ)
    {delta : ℝ} (hdelta : 0 < delta) (hv : ∀ h j x, ‖v h j x‖ ≤ 1)
    (hbias : ∀ h j, delta ≤ ‖(p j).complexMean (v h j)‖) :
    ∃ (h₀ : H) (S : Finset H),
      delta ^ (2 * Fintype.card J) / 2 * Fintype.card H ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ j, delta ^ (2 * Fintype.card J) / 2 ≤
        ‖(p j).correlation (v h j) (v h₀ j)‖ := by
  classical
  have hphase (h : H) (j : J) := exists_complex_unit_phase ((p j).complexMean (v h j))
  choose a ha hamean using hphase
  let V : H → (∀ j, Ω j) → ℂ := fun h x => ∏ j, a h j * v h j (x j)
  let q := FiniteProbabilityWeights.pi p
  have hV : ∀ h x, ‖V h x‖ ≤ 1 := by
    intro h x
    change ‖∏ j, a h j * v h j (x j)‖ ≤ 1
    rw [norm_prod]
    apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
    intro j _
    rw [norm_mul, ha, one_mul]
    exact hv h j (x j)
  have hmean (h : H) : delta ^ Fintype.card J ≤ (q.complexMean (V h)).re := by
    calc
      _ = ∏ _j : J, delta := by simp
      _ ≤ ∏ j, ‖(p j).complexMean (v h j)‖ :=
        Finset.prod_le_prod (fun _ _ => hdelta.le) (fun coordinate _ => hbias h coordinate)
      _ = _ := by
        dsimp only [q, V]
        rw [FiniteProbabilityWeights.complexMean_pi_product p (fun j x => a h j * v h j x)]
        simp_rw [FiniteProbabilityWeights.complexMean_mul_left, hamean]
        rw [← Complex.ofReal_prod, Complex.ofReal_re]
  have hcorr (h k : H) : ‖q.correlation (V h) (V k)‖ =
      ∏ j, ‖(p j).correlation (v h j) (v k j)‖ := by
    dsimp only [q, V]
    rw [FiniteProbabilityWeights.correlation_pi_product p
      (fun j x => a h j * v h j x) (fun j x => a k j * v k j x), norm_prod]
    apply Finset.prod_congr rfl
    intro j _
    exact (p j).norm_correlation_mul_phases (v h j) (v k j) (ha h j) (ha k j)
  obtain ⟨h₀, S, hcard, hS⟩ := exists_weighted_common_anchor q V
    (pow_nonneg hdelta.le _) hV hmean
  have hpow : (delta ^ Fintype.card J) ^ 2 = delta ^ (2 * Fintype.card J) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [hpow] at hcard hS
  refine ⟨h₀, S, hcard, ?_⟩
  intro h hh j
  have hprod : (∏ k, ‖(p k).correlation (v h k) (v h₀ k)‖) ≤
      ‖(p j).correlation (v h j) (v h₀ j)‖ := by
    have h := Finset.prod_le_prod_of_subset_of_le_one (s := {j}) (t := Finset.univ)
      (f := fun k => ‖(p k).correlation (v h k) (v h₀ k)‖) (by simp)
      (fun k _ => norm_nonneg _) (fun k _ _ =>
        (p k).norm_correlation_le_one (v h k) (v h₀ k) (hv h k) (hv h₀ k))
    simpa only [Finset.prod_singleton] using h
  exact ((hS h hh).trans_eq (hcorr h h₀)).trans hprod

theorem exists_common_anchor_on_finset {I J : Type*} [Fintype J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (H : Finset I) (hH : H.Nonempty)
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (v : I → ∀ j, Ω j → ℂ)
    {delta : ℝ} (hdelta : 0 < delta) (hv : ∀ h ∈ H, ∀ j x, ‖v h j x‖ ≤ 1)
    (hbias : ∀ h ∈ H, ∀ j, delta ≤ ‖(p j).complexMean (v h j)‖) :
    ∃ h₀ ∈ H, ∃ S ⊆ H,
      delta ^ (2 * Fintype.card J) / 2 * H.card ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ j, delta ^ (2 * Fintype.card J) / 2 ≤
        ‖(p j).correlation (v h j) (v h₀ j)‖ := by
  classical
  let : Nonempty H := ⟨⟨hH.choose, hH.choose_spec⟩⟩
  obtain ⟨h₀, S, hcard, hS⟩ := exists_common_anchor p (fun h : H => v h) hdelta
    (fun h => hv h h.property) (fun h => hbias h h.property)
  let S' := S.image (fun h : H => (h : I))
  have hcard' : S'.card = S.card := Finset.card_image_of_injective _ Subtype.val_injective
  refine ⟨h₀, h₀.property, S', ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hh
    exact k.property
  · simpa only [hcard', Fintype.card_coe] using hcard
  · intro h hh j
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hh
    exact hS k hk j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem partnerAnchorWeight_norm_le_one {G : Type*} (U V Q : G → ℂ)
    (hU : ∀ x, ‖U x‖ ≤ 1) (hV : ∀ x, ‖V x‖ ≤ 1) (hQ : ∀ x, ‖Q x‖ ≤ 1) (x : G) :
    ‖partnerAnchorWeight U V Q x‖ ≤ 1 := by
  simp only [partnerAnchorWeight, norm_mul, norm_star]
  have hleft := (mul_le_of_le_one_left (norm_nonneg _) (hU x)).trans (hV x)
  have hright := (mul_le_of_le_one_left (norm_nonneg _) (hQ x)).trans (hQ x)
  exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hleft).trans
    hright

theorem exists_fixed_partner_anchor {G K : Type*} [AddCommGroup G] [Fintype G] [Fintype K]
    (H : Finset G) (hH : H.Nonempty) (U : G → K → G → ℂ) (Q R : K → G → ℂ)
    {delta : ℝ} (hdelta : 0 < delta)
    (hU : ∀ h ∈ H, ∀ k x, ‖U h k x‖ ≤ 1)
    (hQ : ∀ k x, ‖Q k x‖ ≤ 1) (hR : ∀ k x, ‖R k x‖ ≤ 1)
    (hcorr : ∀ h ∈ H, ∀ k, delta ≤ ‖𝔼 x, U h k x * Q k x * R k (x + h)‖) :
    ∃ h0 ∈ H, ∃ S ⊆ H, S.Nonempty ∧
      delta ^ (2 * Fintype.card K) / 2 * H.card ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, delta ^ (2 * Fintype.card K) / 2 ≤
        ‖𝔼 x, partnerAnchorWeight (U h k) (U h0 k) (Q k) x * R k (x + h) * star (R k (x + h0))‖ := by
  let v : G → K → G → ℂ := fun h k x => U h k x * Q k x * R k (x + h)
  have hv : ∀ h ∈ H, ∀ k x, ‖v h k x‖ ≤ 1 := by
    intro h hh k x
    simp only [v, norm_mul]
    have hpair := (mul_le_of_le_one_left (norm_nonneg _) (hU h hh k x)).trans (hQ k x)
    exact (mul_le_of_le_one_left (norm_nonneg _) hpair).trans (hR k (x + h))
  obtain ⟨h0, hh0, S, hsub, hsize, hanchor⟩ := exists_common_anchor_on_finset H hH
    (fun _ : K => FiniteProbabilityWeights.uniform G) v hdelta hv
    (fun h hh k => by simpa only [FiniteProbabilityWeights.uniform_complexMean] using hcorr h hh k)
  have hpos : (0 : ℝ) < S.card := by
    have hHpos : (0 : ℝ) < H.card := by exact_mod_cast hH.card_pos
    exact (mul_pos (by positivity) hHpos).trans_le hsize
  refine ⟨h0, hh0, S, hsub, Finset.card_pos.mp (by exact_mod_cast hpos), hsize, ?_⟩
  intro h hh k
  have heq : (FiniteProbabilityWeights.uniform G).correlation (v h k) (v h0 k) =
      𝔼 x, partnerAnchorWeight (U h k) (U h0 k) (Q k) x * R k (x + h) * star (R k (x + h0)) := by
    rw [FiniteProbabilityWeights.uniform_correlation]
    apply Finset.expect_congr rfl
    intro x _
    simp only [v, partnerAnchorWeight, star_mul]
    ring
  rw [← heq]
  exact hanchor h hh k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration

theorem squareGeometryBudget_polynomial :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → squareGeometryBudget p ≤ (p + C) ^ C := by
  refine ⟨132, by decide, ?_⟩
  intro p hp
  have ht : 1 ≤ p + 5 := by linarith
  have hsmall : 2 * p + 5 ≤ (p + 5) ^ 2 := by nlinarith [sq_nonneg p]
  have htwo : (p + 5) ^ 2 ≤ (p + 5) ^ 11 := pow_le_pow_right₀ ht (by decide)
  have hbig : (p + 3) ^ 11 ≤ (p + 5) ^ 11 :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hinner : (p + 3) ^ 11 + 2 * p + 5 ≤ (p + 5) ^ 12 := by
    calc
      _ ≤ 2 * (p + 5) ^ 11 := by linarith
      _ ≤ (p + 5) * (p + 5) ^ 11 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  calc
    squareGeometryBudget p ≤ ((p + 5) ^ 12) ^ 11 :=
      pow_le_pow_left₀ (by positivity) hinner _
    _ = (p + 5) ^ 132 := by rw [← pow_mul]
    _ ≤ (p + (132 : ℕ)) ^ (132 : ℕ) :=
      pow_le_pow_left₀ (by linarith) (by norm_num) _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProjectedNativeCoefficient
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem exists_native_two_shift_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (a b : σ → ℤ) (g : D.filtration.realification.PolynomialOrbit w),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
        ∃ q : D.filtration.squareFiltration.realification.PolynomialOrbit w,
          ∀ x : σ → ℤ,
            D.filtration.realSquareFstHom
              (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) =
                ε⁻¹ * D.filtration.realification.polynomialOrbitEval w (x + a) g * γ⁻¹ ∧
            D.filtration.realSquareSndHom
              (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) =
                D.filtration.realification.polynomialOrbitEval w (x + b) g := by
  obtain ⟨C, hC, hnorm⟩ := exists_bounded_realified_square_orbit s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D p hp hD w hw a b g
  obtain ⟨ε, γ, hγ, hε, q, hq⟩ := hnorm D p hp hD w hw (a - b) g
  refine ⟨ε, γ, hγ, hε, q.translate hw b, ?_⟩
  intro x
  rw [NilpotentLieFiltration.polynomialOrbitEval_translate]
  have hx : (fun i => (x + b) i + (a - b) i) = x + a := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  simpa only [hx] using hq (x + b)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SpecifiedSquareObservable
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_specified_square_observable_lipschitz (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d m : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      (b : Basis (Fin m) ℚ L) (v : Fin m → ℕ)
      (h2 : D.filtration.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ v i}))
      (N : ℕ) (hN : 0 < N)
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b v h2)
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)
      {ω : σ → ℕ} (T : D.Niltest ω) {p : ℝ},
      0 ≤ p → T.ComplexityLE p →
      (Fintype.card (Fin m ⊕ {i // 2 ≤ v i}) : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      ∀ η : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr η.coord i| ≤ Real.exp p) →
        ∃ ℓ : ℝ≥0, (ℓ : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          letI := realificationQuotientMetricSpace (D.filtration.squareFinBasis b v h2)
            (D.filtration.squareLattice D.lattice) N hN hout
          LipschitzWith ℓ (D.filtration.realSquareObservable D.lattice η T.observable) := by
  obtain ⟨B, _, hleft⟩ := exists_bounded_normalization_left_lipschitz (s + 1) 1
  let X : Polynomial ℕ := Polynomial.X
  let P := 2 * X + (X + 3) ^ 2 + (X + 3 + Polynomial.C B) ^ B + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d m _ _ _ _ D _ _ _ _ b v h2 N hN hout ω T p hp hT hdim hb η hη
  obtain ⟨A, _, hA, hALip⟩ := hleft D p hp hT.1
  have hηLip := hALip η (fun i => (hη i).trans (Real.exp_le_exp.mpr (by norm_num; linarith)))
  let H := ⌈Real.exp p⌉₊
  let n := Fintype.card (Fin m ⊕ {i // 2 ≤ v i})
  let J := coordinateLipschitzBound (Fintype.card (Fin d)) (Fintype.card (Fin n)) H
  have hJ : (J : ℝ) ≤ Real.exp ((p + 3) ^ 2) := by
    change (coordinateLipschitzBound (Fintype.card (Fin d)) (Fintype.card (Fin n)) H : ℝ) ≤ _
    have h := coordinateLipschitzBound_le_exp (Fintype.card (Fin d)) (Fintype.card (Fin n)) H
      (show 0 ≤ p + 1 by linarith)
      (by simpa only [Fintype.card_fin] using hT.1.1.trans (by linarith : p ≤ p + 1))
      (by simpa only [Fintype.card_fin] using hdim.trans (by linarith : p ≤ p + 1))
      (ceil_exp_le_exp_add_one hp)
    simpa only [show p + 1 + 2 = p + 3 by ring] using h
  have hproj := D.filtration.squareFinBasis_projection_height D.basis b v h2
    (one_le_ceil_exp p) (fun i j => rationalHeightLE_ceil_exp (hb j i))
  let ℓ := T.normBound * (T.lipBound * J) + T.normBound * (T.lipBound * (A * J))
  have hnorm : (T.normBound : ℝ) ≤ Real.exp p := by
    have h := T.observable_budget hT
    linarith [T.lipBound.coe_nonneg]
  have hlip : (T.lipBound : ℝ) ≤ Real.exp p := by
    have h := T.observable_budget hT
    linarith [T.normBound.coe_nonneg]
  have hℓ := squareObservableLipschitz_le_exp A T.normBound T.lipBound J
    (normalizedSquareLeftBudget_nonneg 1 B hp) hA hnorm hlip hJ
  have hcost : 2 * p + (p + 3) ^ 2 + normalizedSquareLeftBudget 1 B p + 1 ≤ (p + C) ^ C := by
    have hleft : normalizedSquareLeftBudget 1 B p = (p + 3 + B) ^ B := by
      unfold normalizedSquareLeftBudget
      congr 1
      ring
    rw [hleft]
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨ℓ, hℓ.trans (Real.exp_le_exp.mpr hcost), ?_⟩
  exact D.filtration.realSquareObservable_lipschitz D.basis
    (D.filtration.squareFinBasis b v h2) D.lattice D.grid N H D.grid_pos hN D.outer_grid hout
    (fun k i => (hproj i k).1) (fun k i => (hproj i k).2)
    η T.observable A T.lipBound T.normBound hηLip T.lipschitz T.norm_le

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeSquareNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

theorem exists_specified_square_niltest (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d m : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      (b : Basis (Fin m) ℚ L) (v : Fin m → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ v i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis b v (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b v (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)
      {ω : σ → ℕ} (T : D.Niltest ω) {p : ℝ},
      0 ≤ p → T.ComplexityLE p →
      (D.filtration.squareFiltration.ofAdaptedBasis
        (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
        (D.filtration.squareFinBasis_layers b v hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      ∀ η : D.RealGroup, (∀ i, |(D.basis.baseChange ℝ).repr η.coord i| ≤ Real.exp p) →
      ∀ (q : D.filtration.squareFiltration.realification.PolynomialOrbit ω)
        (χ : D.RealGroup → CircleFourier.Circle),
      (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
        T.observable (z • x) = character (χ z) * T.observable x) →
      let Q := D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
        (D.filtration.squareFinBasis_layers b v hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout
      ∃ S : Q.Niltest ω,
        S.orbit = D.filtration.squareFiltration.realQuotientPolynomialOrbit
          (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q ∧
        (∀ z : D.filtration.squareFiltration.realification.Group,
          S.observable (QuotientGroup.mk (D.filtration.squareFiltration.realQuotientStepHom
            (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
            D.filtration.realSquareObservable D.lattice η T.observable (QuotientGroup.mk z)) ∧
        S.normBound = T.normBound ^ 2 ∧ S.ComplexityLE ((p + C) ^ C) ∧
        ∀ x : σ → ℤ, S.eval x = D.filtration.realSquareObservable D.lattice η T.observable
          (QuotientGroup.mk (D.filtration.squareFiltration.realification.polynomialOrbitEval ω x q)) := by
  obtain ⟨A, _, hobs⟩ := exists_specified_square_observable_lipschitz s
  obtain ⟨B, _, hrec⟩ := exists_rationalReconstructionLipschitzBound_exp s
  let X : Polynomial ℕ := Polynomial.X
  let U := X + 1 + (X + Polynomial.C A) ^ A + 2 * X
  let P := X + 2 * X + (U + Polynomial.C B) ^ B + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d m _ _ _ _ D _ _ _ _ _ _ _ _ b v hF N hN hin hout ω T p hp hT hV hb η hη q χ hvert
  let bs := D.filtration.squareFinBasis b v (hF 2)
  let vs := squareFinWeight v
  let hls := D.filtration.squareFinBasis_layers b v hF
  let Q := D.filtration.squareFiltration.topQuotientModel bs vs hls
    (D.filtration.squareLattice D.lattice) N hN hin hout
  have hQ : Q.GeometryComplexityLE p :=
    D.filtration.squareFiltration.topQuotientModel_geometry bs vs hls
      (D.filtration.squareLattice D.lattice) N hN hin hout hp hV
  obtain ⟨ℓ, hℓ, hℓLip⟩ := hobs D b v (hF 2) N hN hout T hp hT hV.1 hb η hη
  let H := ⌈Real.exp p⌉₊
  have he (i j) : RationalHeightLE (Q.basis.repr
      (lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1)) (bs j)) i) H := by
    exact (quotientFinBasis_projection_height bs
      (D.filtration.squareFiltration.layerIdeal (s + 1)) {i | s + 1 ≤ vs i}
      (hls (s + 1)) j i).mono (one_le_ceil_exp p)
  obtain ⟨S, horbit, hobservable, hnorm, hlip, hval⟩ :=
    D.filtration.exists_square_quotient_niltest_with_orbit D.lattice bs vs hls N hN hin hout
      ω q η T.observable χ hvert ℓ T.normBound hℓLip T.norm_le H (one_le_ceil_exp p) he
      (fun i j k => rationalHeightLE_ceil_exp (hQ.2.2.1 i j k))
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    have h := T.observable_budget hT
    linarith [T.lipBound.coe_nonneg]
  have hB2 : ((T.normBound ^ 2 : ℝ≥0) : ℝ) ≤ Real.exp (2 * p) := by
    rw [NNReal.coe_pow]
    calc
      _ ≤ (Real.exp p) ^ 2 := pow_le_pow_left₀ T.normBound.coe_nonneg hB 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  let r := p + 1 + (p + A) ^ A + 2 * p
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hp1r : p + 1 ≤ r := by dsimp [r]; linarith [pow_nonneg (by positivity : 0 ≤ p + A) A]
  have hAr : (p + A) ^ A ≤ r := by dsimp [r]; linarith
  have h2pr : 2 * p ≤ r := by dsimp [r]; linarith [pow_nonneg (by positivity : 0 ≤ p + A) A]
  have hlipBound : (S.lipBound : ℝ) ≤ Real.exp ((r + B) ^ B) := by
    rw [hlip]
    apply hrec _ _ H ℓ (T.normBound ^ 2) r hr
    · simpa only [Fintype.card_fin] using hV.1.trans (by linarith : p ≤ r)
    · exact hQ.1.trans (by linarith)
    · exact (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1r)
    · exact hℓ.trans (Real.exp_le_exp.mpr hAr)
    · exact hB2.trans (Real.exp_le_exp.mpr h2pr)
  have hnormBound : (S.normBound : ℝ) ≤ Real.exp (2 * p) := by rw [hnorm]; exact hB2
  have hlog := niltest_log_bound_of_exp S.normBound S.lipBound
    (by linarith : 0 ≤ 2 * p) (by positivity : 0 ≤ (r + B) ^ B) hnormBound hlipBound
  have hcost : p + 2 * p + (r + B) ^ B + 4 ≤ (p + C) ^ C := by
    simpa [X, U, P, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨S, horbit, hobservable, hnorm, ?_, hval⟩
  refine ⟨hQ.mono Q (by linarith [pow_nonneg (by positivity : 0 ≤ r + B) B]), ?_⟩
  exact hlog.trans (by linarith)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeRetainedIntegerMultilinearQuadruples
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_two_shift_integer_interval {N : ℕ} [NeZero N]
    (f R : ℤ → ℂ) (h h0 : ZMod N) {rho : ℝ} (hrho : 0 < rho)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hR : ∀ n, ‖R n‖ ≤ 1)
    (hcorr : rho ≤ ‖𝔼 x : ZMod N,
      f x.val * R ((x + h).val : ℤ) * star (R ((x + h0).val : ℤ))‖) :
    ∃ (branch branch0 : Bool) (a len : ℕ), 0 < len ∧ a + len ≤ N ∧
      2 * ((len : ℤ) - 1) < N ∧
      rho / 20 ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
        f n * R (n + cyclicBranchOffset h branch) * star (R (n + cyclicBranchOffset h0 branch0))‖ ∧
      rho / 20 ≤ (len : ℝ) / N := by
  let shifts : Fin 2 → ZMod N := ![h, h0]
  let u : Fin 2 → ℤ → ℂ := ![(fun n => star (R n)), R]
  have heval (x : ZMod N) : translatedCyclicProduct shifts u x =
      star (R ((x + h).val : ℤ)) * R ((x + h0).val : ℤ) := by
    simp [translatedCyclicProduct, shifts, u, Fin.prod_univ_two, add_comm]
  have hucap (x : ZMod N) : ‖translatedCyclicProduct shifts u x‖ ≤ 1 := by
    rw [heval, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hR _)).trans (hR _)
  have hc : rho ≤ ‖finiteCorrelation Finset.univ (fun x : ZMod N => f x.val)
      (translatedCyclicProduct shifts u)‖ := by
    convert hcorr using 1
    congr 1
    unfold finiteCorrelation
    apply Finset.expect_congr rfl
    intro x _
    rw [heval]
    simp only [star_mul, star_star]
    ring
  obtain ⟨a, hlen, hbound, hshort, hcor, hvol⟩ := exists_correlating_integer_product_interval
    shifts u (fun x : ZMod N => f x.val) hrho (by norm_num : (0 : ℝ) < 1)
    (fun x => hf x.val) hucap hc
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at hcor hvol
  let branch := decide (N - h.val ≤ a.val)
  let branch0 := decide (N - h0.val ≤ a.val)
  let len := intervalCutUpper (commonCyclicCuts shifts) N a.val - a.val
  have hprod (n : ℤ) : (∏ i, u i (n + cyclicTranslationOffset (shifts i) a.val)) =
      star (R (n + cyclicBranchOffset h branch)) * R (n + cyclicBranchOffset h0 branch0) := by
    simp only [Fin.prod_univ_two, shifts, u, Matrix.cons_val_zero, Matrix.cons_val_one,
      cyclicTranslationOffset_eq_branch, branch, branch0]
    rfl
  have heq : finiteCorrelation (Finset.Ico (a.val : ℤ) (a.val + len))
      (fun n => f ((n : ZMod N).val : ℤ))
      (fun n => ∏ i, u i (n + cyclicTranslationOffset (shifts i) a.val)) =
      𝔼 n ∈ Finset.Ico (a.val : ℤ) (a.val + len),
        f n * R (n + cyclicBranchOffset h branch) * star (R (n + cyclicBranchOffset h0 branch0)) := by
    unfold finiteCorrelation
    apply Finset.expect_congr rfl
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    have hrep : (((n : ZMod N).val : ℕ) : ℤ) = n := by
      rw [ZMod.val_intCast, Int.emod_eq_of_lt (by omega) (by omega)]
    change f (((n : ZMod N).val : ℕ) : ℤ) *
      star (∏ i, u i (n + cyclicTranslationOffset (shifts i) a.val)) = _
    rw [hrep, hprod, star_mul, star_star]
    ring
  refine ⟨branch, branch0, a.val, len, hlen, hbound, hshort, ?_, ?_⟩
  · rw [← heq]
    exact hcor
  · exact hvol

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedTwoShiftBranches
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_fixed_two_shift_branches {K : Type*} [Fintype K] {N : ℕ} [NeZero N]
    (H : Finset (ZMod N)) (hH : H.Nonempty) (h0 : ZMod N)
    (f : ZMod N → K → ℤ → ℂ) (R : K → ℤ → ℂ) {rho : ℝ} (hrho : 0 < rho)
    (hf : ∀ h ∈ H, ∀ k n, ‖f h k n‖ ≤ 1) (hR : ∀ k n, ‖R k n‖ ≤ 1)
    (hcorr : ∀ h ∈ H, ∀ k, rho ≤ ‖𝔼 x : ZMod N,
      f h k x.val * R k ((x + h).val : ℤ) * star (R k ((x + h0).val : ℤ))‖) :
    ∃ (branches : K → Bool × Bool) (S : Finset (ZMod N)), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-Real.log 4 * Fintype.card K) * H.card ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧
        2 * ((len : ℤ) - 1) < N ∧
        rho / 20 ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
          f h k n * R k (n + cyclicBranchOffset h (branches k).1) *
            star (R k (n + cyclicBranchOffset h0 (branches k).2))‖ ∧
        rho / 20 ≤ (len : ℝ) / N := by
  let rel : ZMod N → K → Bool × Bool → Prop := fun h k b =>
    ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      rho / 20 ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
        f h k n * R k (n + cyclicBranchOffset h b.1) * star (R k (n + cyclicBranchOffset h0 b.2))‖ ∧
      rho / 20 ≤ (len : ℝ) / N
  apply exists_large_fixed_choices H hH rel
  · intro h hh k
    obtain ⟨b, b0, a, len, hlen, hbound, hshort, hbias, hvol⟩ :=
      exists_two_shift_integer_interval (f h k) (R k) h h0 hrho (hf h hh k) (hR k) (hcorr h hh k)
    exact ⟨(b, b0), a, len, hlen, hbound, hshort, hbias, hvol⟩
  · rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num [Fintype.card_prod]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AnchoredIntegerIntervalsPower
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_anchored_integer_intervals {K : Type*} [Fintype K] {N : ℕ} [NeZero N]
    (H : Finset (ZMod N)) (hH : H.Nonempty)
    (U : ZMod N → K → ℤ → ℂ) (Q R : K → ℤ → ℂ) {delta : ℝ} (hdelta : 0 < delta)
    (hU : ∀ h ∈ H, ∀ k n, ‖U h k n‖ ≤ 1)
    (hQ : ∀ k n, ‖Q k n‖ ≤ 1) (hR : ∀ k n, ‖R k n‖ ≤ 1)
    (hcorr : ∀ h ∈ H, ∀ k, delta ≤ ‖𝔼 x : ZMod N,
      U h k x.val * Q k x.val * R k ((x + h).val : ℤ)‖) :
    ∃ h0 ∈ H, ∃ (branches : K → Bool × Bool) (S : Finset (ZMod N)),
      S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-Real.log 4 * Fintype.card K) * (delta ^ (2 * Fintype.card K) / 2) * H.card ≤
        (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧
        2 * ((len : ℤ) - 1) < N ∧
        delta ^ (2 * Fintype.card K) / 40 ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            partnerAnchorWeight (U h k) (U h0 k) (Q k) n *
              R k (n + cyclicBranchOffset h (branches k).1) *
              star (R k (n + cyclicBranchOffset h0 (branches k).2))‖ ∧
        delta ^ (2 * Fintype.card K) / 40 ≤ (len : ℝ) / N := by
  obtain ⟨h0, hh0, H', hsub, hH'n, hsize, hanchor⟩ := exists_fixed_partner_anchor H hH
    (fun h k x => U h k x.val) (fun k x => Q k x.val) (fun k x => R k x.val) hdelta
    (fun h hh k x => hU h hh k x.val) (fun k x => hQ k x.val) (fun k x => hR k x.val) hcorr
  let f : ZMod N → K → ℤ → ℂ := fun h k => partnerAnchorWeight (U h k) (U h0 k) (Q k)
  have hf : ∀ h ∈ H', ∀ k n, ‖f h k n‖ ≤ 1 := by
    intro h hh k n
    exact partnerAnchorWeight_norm_le_one (U h k) (U h0 k) (Q k)
      (hU h (hsub hh) k) (hU h0 hh0 k) (hQ k) n
  have hcorr' : ∀ h ∈ H', ∀ k, delta ^ (2 * Fintype.card K) / 2 ≤
      ‖𝔼 x : ZMod N, f h k x.val * R k ((x + h).val : ℤ) * star (R k ((x + h0).val : ℤ))‖ :=
    hanchor
  obtain ⟨branches, S, hSH', hSn, hcard, hinterval⟩ := exists_fixed_two_shift_branches
    H' hH'n h0 f R (by positivity) hf hR hcorr'
  refine ⟨h0, hh0, branches, S, fun h hh => hsub (hSH' hh), hSn, ?_, ?_⟩
  · calc
      _ = Real.exp (-Real.log 4 * Fintype.card K) *
          ((delta ^ (2 * Fintype.card K) / 2) * H.card) := mul_assoc _ _ _
      _ ≤ Real.exp (-Real.log 4 * Fintype.card K) * H'.card :=
        mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le
      _ ≤ _ := hcard
  · intro h hh k
    obtain ⟨a, len, hlen, hbound, hshort, hbias, hvol⟩ := hinterval h hh k
    refine ⟨a, len, hlen, hbound, hshort, ?_, ?_⟩
    · simpa only [div_div, show (2 : ℝ) * 20 = 40 by norm_num] using hbias
    · simpa only [div_div, show (2 : ℝ) * 20 = 40 by norm_num] using hvol

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_anchored_integer_intervals_power {K : Type*} [Fintype K] {N : ℕ} [NeZero N]
    (H : Finset (ZMod N)) (U : ZMod N → K → ℤ → ℂ) (Q R : K → ℤ → ℂ)
    {p delta : ℝ} (hp : 2 ≤ p) (hm : (Fintype.card K : ℝ) ≤ p)
    (hdelta : Real.exp (-p) ≤ delta) (hH : Real.exp (-p) * N ≤ (H.card : ℝ))
    (hU : ∀ h ∈ H, ∀ k n, ‖U h k n‖ ≤ 1)
    (hQ : ∀ k n, ‖Q k n‖ ≤ 1) (hR : ∀ k n, ‖R k n‖ ≤ 1)
    (hcorr : ∀ h ∈ H, ∀ k, delta ≤ ‖𝔼 x : ZMod N,
      U h k x.val * Q k x.val * R k ((x + h).val : ℤ)‖) :
    ∃ h0 ∈ H, ∃ (branches : K → Bool × Bool) (S : Finset (ZMod N)),
      S ⊆ H ∧ S.Nonempty ∧ Real.exp (-((p + 2) ^ 3)) * N ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧
        2 * ((len : ℤ) - 1) < N ∧
        Real.exp (-((p + 2) ^ 3)) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            partnerAnchorWeight (U h k) (U h0 k) (Q k) n *
              R k (n + cyclicBranchOffset h (branches k).1) *
              star (R k (n + cyclicBranchOffset h0 (branches k).2))‖ ∧
        Real.exp (-((p + 2) ^ 3)) ≤ (len : ℝ) / N := by
  have hdelta0 : 0 < delta := (Real.exp_pos _).trans_le hdelta
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hHpos : (0 : ℝ) < H.card := (mul_pos (Real.exp_pos _) hN).trans_le hH
  have hHn : H.Nonempty := Finset.card_pos.mp (by exact_mod_cast hHpos)
  obtain ⟨h0, hh0, branches, S, hsub, hSn, hsize, hinterval⟩ :=
    exists_anchored_integer_intervals H hHn U Q R hdelta0 hU hQ hR hcorr
  have hB : 0 ≤ Real.exp (-Real.log 4 * Fintype.card K) * (delta ^ (2 * Fintype.card K) / 2) :=
    mul_nonneg (Real.exp_nonneg _) (by positivity)
  refine ⟨h0, hh0, branches, S, hsub, hSn, ?_, ?_⟩
  · calc
      _ ≤ (Real.exp (-Real.log 4 * Fintype.card K) *
          (delta ^ (2 * Fintype.card K) / 2) * Real.exp (-p)) * N :=
        mul_le_mul_of_nonneg_right (anchored_density_budget hp hm hdelta le_rfl) hN.le
      _ = (Real.exp (-Real.log 4 * Fintype.card K) *
          (delta ^ (2 * Fintype.card K) / 2)) * (Real.exp (-p) * N) := by ring
      _ ≤ (Real.exp (-Real.log 4 * Fintype.card K) *
          (delta ^ (2 * Fintype.card K) / 2)) * H.card := mul_le_mul_of_nonneg_left hH hB
      _ ≤ _ := hsize
  · intro h hh k
    obtain ⟨a, len, hlen, hbound, hshort, hbias, hvol⟩ := hinterval h hh k
    exact ⟨a, len, hlen, hbound, hshort, (anchored_interval_budget hp hm hdelta).trans hbias,
      (anchored_interval_budget hp hm hdelta).trans hvol⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDetectorContradictionSpec
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct NNReal

theorem exists_controlled_prescribed_square_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (v : Fin (finrank ℚ L) → ℕ)
        (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ v i}))
        (M : ℕ) (hM : 0 < M)
        (hin : scaledIntegerGrid M ⊆ bchSubgroupCoordinates
          (D.filtration.squareFinBasis b v (hF 2)) (D.filtration.squareLattice D.lattice))
        (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b v (hF 2))
          (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid M),
        (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        (D.filtration.squareFiltration.ofAdaptedBasis
          (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
          (D.filtration.squareFinBasis_layers b v hF)
          (D.filtration.squareLattice D.lattice) M hM hin hout).GeometryComplexityLE ((p + C) ^ C) ∧
        let Q := D.filtration.squareFiltration.topQuotientModel
          (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
          (D.filtration.squareFinBasis_layers b v hF)
          (D.filtration.squareLattice D.lattice) M hM hin hout
        Q.GeometryComplexityLE ((p + C) ^ C) ∧
        ∀ (w : σ → ℕ), (∀ i, 0 < w i) → ∀ T : D.Niltest w, T.ComplexityLE p →
        ∀ χ : D.RealGroup → CircleFourier.Circle,
          (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
            T.observable (z • x) = character (χ z) * T.observable x) →
        ∀ a b₀ : σ → ℤ, ∃ η γ : D.RealGroup, γ ∈ D.realLattice ∧
          (∀ i, |(D.basis.baseChange ℝ).repr η.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ (rSq : D.filtration.squareFiltration.realification.PolynomialOrbit w) (S : Q.Niltest w),
            (∀ x : σ → ℤ,
              D.filtration.realSquareFstHom
                (D.filtration.squareFiltration.realification.polynomialOrbitEval w x rSq) =
                  η⁻¹ * D.filtration.realification.polynomialOrbitEval w (x + a) T.orbit * γ⁻¹ ∧
              D.filtration.realSquareSndHom
                (D.filtration.squareFiltration.realification.polynomialOrbitEval w x rSq) =
                  D.filtration.realification.polynomialOrbitEval w (x + b₀) T.orbit) ∧
            S.orbit = D.filtration.squareFiltration.realQuotientPolynomialOrbit
              (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl rSq ∧
            S.normBound = T.normBound ^ 2 ∧ S.ComplexityLE ((p + C) ^ C) ∧
            ∀ x : σ → ℤ, S.eval x = T.eval (x + a) * star (T.eval (x + b₀)) := by
  obtain ⟨a, _, hnormalize⟩ := exists_native_two_shift_normalization (s + 1)
  obtain ⟨g, _, hgeometry⟩ := squareGeometryBudget_polynomial
  obtain ⟨k, _, htest⟩ := exists_specified_square_niltest s
  let X : Polynomial ℕ := Polynomial.X
  let P := X + 1 + (X + Polynomial.C g) ^ g + (X + 1 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Polynomial.C k) ^ k)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp hD
  let q := p + 1 + (p + g) ^ g + (p + 1 + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hgp : 0 ≤ (p + g) ^ g := by positivity
  have hap : 0 ≤ (p + 1 + a) ^ a := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hp1q : p + 1 ≤ q := by dsimp [q]; linarith
  have hgeomq : squareGeometryBudget p ≤ q := by
    have hg := hgeometry p hp
    dsimp [q]
    linarith
  have hnormq : (p + 1 + a) ^ a ≤ q := by dsimp [q]; linarith
  have hbud : q + (q + k) ^ k ≤ (p + C) ^ C := by
    simpa [P, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by
    have hnonneg : 0 ≤ (q + k) ^ k := by positivity
    linarith
  have htestC : (q + k) ^ k ≤ (p + C) ^ C := by linarith
  obtain ⟨b, v, hF, M, hM, hin, hout, hb, hV⟩ := D.exists_controlled_square_geometry hp hD
  let V := D.filtration.squareFiltration.ofAdaptedBasis
    (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
    (D.filtration.squareFinBasis_layers b v hF) (D.filtration.squareLattice D.lattice) M hM hin hout
  let Q := D.filtration.squareFiltration.topQuotientModel
    (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
    (D.filtration.squareFinBasis_layers b v hF) (D.filtration.squareLattice D.lattice) M hM hin hout
  have hVq : V.GeometryComplexityLE q := hV.mono V hgeomq
  have hQq : Q.GeometryComplexityLE q :=
    D.filtration.squareFiltration.topQuotientModel_geometry
      (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
      (D.filtration.squareFinBasis_layers b v hF) (D.filtration.squareLattice D.lattice)
      M hM hin hout hq hVq
  refine ⟨b, v, hF, M, hM, hin, hout, (fun i j => (hb i j).trans (hp1q.trans hqC)),
    hVq.mono V hqC, hQq.mono Q hqC, ?_⟩
  intro w hw T hT χ hvert left right
  obtain ⟨η, γ, hγ, hη, rSq, hnorm⟩ := hnormalize D hp hD w hw left right T.orbit
  have hηq (i) : |(D.basis.baseChange ℝ).repr η.coord i| ≤ Real.exp q :=
    (hη i).trans (Real.exp_le_exp.mpr hnormq)
  obtain ⟨S, hSo, _, hSn, hSc, hSeval⟩ := htest D b v hF M hM hin hout T hq
    (hT.mono hpq) hVq (fun i j => (hb i j).trans hp1q) η hηq rSq χ hvert
  refine ⟨η, γ, hγ, (fun i => (hηq i).trans (Real.exp_le_exp.mpr hqC)), rSq, S,
    hnorm, hSo, hSn, hSc.mono htestC, ?_⟩
  intro x
  exact (hSeval x).trans (D.filtration.realSquareObservable_recovers_product D.lattice η γ
    (D.filtration.realification.polynomialOrbitEval w (x + left) T.orbit)
    (D.filtration.realification.polynomialOrbitEval w (x + right) T.orbit) hγ T.observable
    (D.filtration.squareFiltration.realification.polynomialOrbitEval w x rSq)
    (hnorm x).1 (hnorm x).2)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct NNReal

theorem exists_controlled_prescribed_square_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G J σ : Type*} {L : J → Type*}
      [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)] {d : J → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
      (D : ∀ j, RationalFilteredNilmanifold (L j) (s + 1) (d j))
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] (D j).filtration.squareLieSubalgebra)]
      [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D j).filtration.squareLieSubalgebra)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D j).filtration.squareLieSubalgebra)]
      [∀ j, T2Space (ℝ ⊗[ℚ] (D j).filtration.squareLieSubalgebra)]
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] ((D j).filtration.squareLieSubalgebra ⧸
        (D j).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D j).filtration.squareLieSubalgebra ⧸
        (D j).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D j).filtration.squareLieSubalgebra ⧸
        (D j).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ j, T2Space (ℝ ⊗[ℚ] ((D j).filtration.squareLieSubalgebra ⧸
        (D j).filtration.squareFiltration.layerIdeal (s + 1)))]
      {p : ℝ}, 0 ≤ p → (∀ j, (D j).GeometryComplexityLE p) →
      ∃ (b : ∀ j, Basis (Fin (finrank ℚ (L j))) ℚ (L j))
        (v : ∀ j, Fin (finrank ℚ (L j)) → ℕ)
        (hF : ∀ j i, (D j).filtration.layer i = Submodule.span ℚ (b j '' {k | i ≤ v j k}))
        (M : J → ℕ) (hM : ∀ j, 0 < M j)
        (hin : ∀ j, scaledIntegerGrid (M j) ⊆ bchSubgroupCoordinates
          ((D j).filtration.squareFinBasis (b j) (v j) (hF j 2)) ((D j).filtration.squareLattice (D j).lattice))
        (hout : ∀ j, bchSubgroupCoordinates ((D j).filtration.squareFinBasis (b j) (v j) (hF j 2))
          ((D j).filtration.squareLattice (D j).lattice) ⊆ denominatorGrid (M j)),
        (∀ j i k, rationalLogHeight ((D j).basis.repr (b j i) k) ≤ (p + C) ^ C) ∧
        (∀ j, ((D j).filtration.squareFiltration.ofAdaptedBasis
          ((D j).filtration.squareFinBasis (b j) (v j) (hF j 2)) (squareFinWeight (v j))
          ((D j).filtration.squareFinBasis_layers (b j) (v j) (hF j))
          ((D j).filtration.squareLattice (D j).lattice) (M j) (hM j) (hin j) (hout j)).GeometryComplexityLE ((p + C) ^ C)) ∧
        let Q := fun j => (D j).filtration.squareFiltration.topQuotientModel
          ((D j).filtration.squareFinBasis (b j) (v j) (hF j 2)) (squareFinWeight (v j))
          ((D j).filtration.squareFinBasis_layers (b j) (v j) (hF j))
          ((D j).filtration.squareLattice (D j).lattice) (M j) (hM j) (hin j) (hout j)
        (∀ j, (Q j).GeometryComplexityLE ((p + C) ^ C)) ∧
        ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
        ∀ T : ∀ j, (D j).Niltest w, (∀ j, (T j).ComplexityLE p) →
        ∀ χ : ∀ j, (D j).RealGroup → CircleFourier.Circle,
          (∀ j z, z ∈ (D j).filtration.realification.subgroup (s + 1) → ∀ x,
            (T j).observable (z • x) = character (χ j z) * (T j).observable x) →
        ∀ left right : G → J → σ → ℤ,
        ∃ (η γ : G → ∀ j, (D j).RealGroup)
          (rSq : G → ∀ j, (D j).filtration.squareFiltration.realification.PolynomialOrbit w)
          (S : G → ∀ j, (Q j).Niltest w),
          ∀ h j, γ h j ∈ (D j).realLattice ∧
            (∀ i, |((D j).basis.baseChange ℝ).repr (η h j).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (∀ x : σ → ℤ,
              (D j).filtration.realSquareFstHom
                ((D j).filtration.squareFiltration.realification.polynomialOrbitEval w x (rSq h j)) =
                  (η h j)⁻¹ * (D j).filtration.realification.polynomialOrbitEval w (x + left h j) (T j).orbit * (γ h j)⁻¹ ∧
              (D j).filtration.realSquareSndHom
                ((D j).filtration.squareFiltration.realification.polynomialOrbitEval w x (rSq h j)) =
                  (D j).filtration.realification.polynomialOrbitEval w (x + right h j) (T j).orbit) ∧
            (S h j).orbit = (D j).filtration.squareFiltration.realQuotientPolynomialOrbit
              ((D j).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq h j) ∧
            (S h j).normBound = (T j).normBound ^ 2 ∧ (S h j).ComplexityLE ((p + C) ^ C) ∧
            ∀ x : σ → ℤ, (S h j).eval x = (T j).eval (x + left h j) * star ((T j).eval (x + right h j)) := by
  classical
  obtain ⟨C, hC, hmodel⟩ := exists_controlled_prescribed_square_model s
  refine ⟨C, hC, ?_⟩
  intro G J σ L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp hD
  have hmodels (j : J) := hmodel (σ := σ) (D j) hp (hD j)
  choose b v hF M hM hin hout hb hV hQ hbuild using hmodels
  refine ⟨b, v, hF, M, hM, hin, hout, hb, hV, hQ, ?_⟩
  intro w hw T hT χ hvert left right
  have hchoices (h : G) (j : J) := hbuild j w hw (T j) (hT j) (χ j) (hvert j) (left h j) (right h j)
  choose η γ hγ hη rSq S hnorm hSo hSn hSc hSval using hchoices
  exact ⟨η, γ, rSq, S, fun h j => ⟨hγ h j, hη h j, hnorm h j, hSo h j, hSn h j, hSc h j, hSval h j⟩⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.PositiveShiftBasis

open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_native_partner_intervals {s N : ℕ} [NeZero N] {q : ℝ}
    {a J : ZMod N → ℝ} (B : PositiveShiftBasis s N q a J)
    {L M : Fin B.count → Type*}
    [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
    [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
    {d e : Fin B.count → ℕ}
    (D : ∀ j, RationalFilteredNilmanifold (L j) (s + 1) (d j))
    (E : ∀ j, RationalFilteredNilmanifold (M j) (s + 1) (e j))
    (Q : ∀ j, (D j).Niltest (fun _ : Unit => 1))
    (R : ∀ j, (E j).Niltest (fun _ : Unit => 1))
    (H : Finset (ZMod N)) (hsub : H ⊆ B.shifts) {p : ℝ} (hp : 2 ≤ p) (hqp : q ≤ p)
    (hsize : Real.exp (-p) * N ≤ (H.card : ℝ))
    (hQ : ∀ j, (Q j).normBound ≤ 1) (hR : ∀ j, (R j).normBound ≤ 1)
    (hcorr : ∀ h ∈ H, ∀ j, Real.exp (-p) ≤ ‖𝔼 n,
      (B.mode h j).evalCyclic N (fun _ => n) * (Q j).evalCyclic N (fun _ => n) *
        (R j).evalCyclic N (fun _ => n + h)‖) :
    ∃ h₀ ∈ H, ∃ (branches : Fin B.count → Bool × Bool) (S : Finset (ZMod N)),
      S ⊆ H ∧ S.Nonempty ∧ Real.exp (-((p + 2) ^ 3)) * N ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ j, ∃ start len : ℕ, 0 < len ∧ start + len ≤ N ∧
        2 * ((len : ℤ) - 1) < N ∧ Real.exp (-((p + 2) ^ 3)) * N ≤ (len : ℝ) ∧
        Real.exp (-((p + 2) ^ 3)) ≤
          ‖𝔼 x ∈ translatedIntegerBox (fun _ : Unit => (start : ℤ)) (fun _ => len),
            (B.mode h j).eval x * star ((B.mode h₀ j).eval x) *
              ((Q j).eval x * star ((Q j).eval x)) *
              ((R j).eval (x + fun _ => cyclicBranchOffset h (branches j).1) *
                star ((R j).eval (x + fun _ => cyclicBranchOffset h₀ (branches j).2)))‖ := by
  have hm : (Fintype.card (Fin B.count) : ℝ) ≤ p := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr B.count_le_dim).trans (B.geometry.1.trans hqp)
  obtain ⟨h₀, hh₀, branches, S, hSH, hSn, hlarge, hinterval⟩ :=
    exists_anchored_integer_intervals_power H
      (fun h j n => (B.mode h j).eval (fun _ => n))
      (fun j n => (Q j).eval (fun _ => n)) (fun j n => (R j).eval (fun _ => n))
      hp hm le_rfl hsize
      (fun h hh j n => ((B.mode h j).norm_eval_le _).trans (B.mode_norm h (hsub hh) j))
      (fun j n => ((Q j).norm_eval_le _).trans (hQ j))
      (fun j n => ((R j).norm_eval_le _).trans (hR j)) hcorr
  refine ⟨h₀, hh₀, branches, S, hSH, hSn, hlarge, ?_⟩
  intro h hh j
  obtain ⟨start, len, hlen, hbound, hshort, hbias, hvol⟩ := hinterval h hh j
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  refine ⟨start, len, hlen, hbound, hshort, (le_div_iff₀ hN).mp hvol, ?_⟩
  rw [unitIntervalBox_expect]
  have hshift (n c : ℤ) : ((fun _ : Unit => n) + fun _ => c) = (fun _ => n + c) := rfl
  simpa only [hshift, partnerAnchorWeight, mul_assoc] using hbias

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators NNReal

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_prescribed_lower_inputs_s2_oai (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis s N q a J) {L : (Fin B.count × Bool) → Type*}
      [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Fin B.count × Bool) → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      (T : ∀ i, (D i).Niltest (fun _ : Unit => 1))
      (H : Finset (ZMod N)), H ⊆ B.shifts →
      ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ i, (T i).ComplexityLE p) → (∀ i, (T i).normBound ≤ 1) →
      ∀ χ : ∀ i, (D i).RealGroup → CircleFourier.Circle,
      (∀ i z, z ∈ (D i).filtration.realification.subgroup (s + 1) → ∀ x,
        (T i).observable (z • x) = character (χ i z) * (T i).observable x) →
      (∀ h ∈ H, ∀ j, Real.exp (-p) ≤ ‖𝔼 n,
        (B.mode h j).evalCyclic N (fun _ => n) * (T (j, true)).evalCyclic N (fun _ => n) *
          (T (j, false)).evalCyclic N (fun _ => n + h)‖) →
      ∃ F : ∀ i, (D i).SquareModelData,
        (∀ i, (F i).fullModel.GeometryComplexityLE ((p + C) ^ C)) ∧
        (∀ i, (F i).quotientModel.GeometryComplexityLE ((p + C) ^ C)) ∧
        (∀ i j k, rationalLogHeight ((D i).basis.repr ((F i).basis j) k) ≤ (p + C) ^ C) ∧
        ∃ h₀ ∈ H, ∃ (branches : Fin B.count → Bool × Bool) (S : Finset (ZMod N)),
          S ⊆ H ∧ S.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (S.card : ℝ) ∧
          ∃ (A : ∀ j, (F (j, true)).quotientModel.Niltest (fun _ : Unit => 1))
            (R : ZMod N → ∀ j, (F (j, false)).quotientModel.Niltest (fun _ : Unit => 1))
            (η γ : ZMod N → ∀ j, (D (j, false)).RealGroup)
            (rSq : ZMod N → ∀ j,
              (D (j, false)).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ j, (A j).normBound ≤ 1 ∧ (A j).ComplexityLE ((p + C) ^ C) ∧
              ∀ x, (A j).eval x = (T (j, true)).eval x * star ((T (j, true)).eval x)) ∧
            (∀ h j, γ h j ∈ (D (j, false)).realLattice ∧
              (∀ i, |((D (j, false)).basis.baseChange ℝ).repr (η h j).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (∀ x : Unit → ℤ,
                (D (j, false)).filtration.realSquareFstHom
                  ((D (j, false)).filtration.squareFiltration.realification.polynomialOrbitEval
                    (fun _ => 1) x (rSq h j)) =
                    (η h j)⁻¹ * (D (j, false)).filtration.realification.polynomialOrbitEval (fun _ => 1)
                      (x + fun _ => cyclicBranchOffset h (branches j).1) (T (j, false)).orbit * (γ h j)⁻¹ ∧
                (D (j, false)).filtration.realSquareSndHom
                  ((D (j, false)).filtration.squareFiltration.realification.polynomialOrbitEval
                    (fun _ => 1) x (rSq h j)) =
                    (D (j, false)).filtration.realification.polynomialOrbitEval (fun _ => 1)
                      (x + fun _ => cyclicBranchOffset h₀ (branches j).2) (T (j, false)).orbit) ∧
              (R h j).orbit = (D (j, false)).filtration.squareFiltration.realQuotientPolynomialOrbit
                ((D (j, false)).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq h j) ∧
              (R h j).normBound ≤ 1 ∧ (R h j).ComplexityLE ((p + C) ^ C) ∧
              ∀ x, (R h j).eval x =
                (T (j, false)).eval (x + fun _ => cyclicBranchOffset h (branches j).1) *
                  star ((T (j, false)).eval (x + fun _ => cyclicBranchOffset h₀ (branches j).2))) ∧
            ∀ h ∈ S, ∀ j, ∃ start len : ℕ, 0 < len ∧ start + len ≤ N ∧
              2 * ((len : ℤ) - 1) < N ∧ Real.exp (-((p + C) ^ C)) * N ≤ (len : ℝ) ∧
              Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 x ∈ translatedIntegerBox (fun _ : Unit => (start : ℤ)) (fun _ => len),
                  (B.mode h j).eval x * star ((B.mode h₀ j).eval x) * (A j).eval x * (R h j).eval x‖ := by
  classical
  obtain ⟨c, _, hfamily⟩ := RationalFilteredNilmanifold.exists_controlled_prescribed_square_family s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((X + Polynomial.C c) ^ c + (X + 2) ^ 3 + X + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ q a J B L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ T H hH p hp hqp hsize hTc hTn χ hvert hcorr
  have hp0 : 0 ≤ p := by linarith
  have hbud : (p + c) ^ c + (p + 2) ^ 3 + p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp0
  have hc0 : 0 ≤ (p + c) ^ c := by positivity
  have hi0 : 0 ≤ (p + 2) ^ 3 := by positivity
  have hcC : (p + c) ^ c ≤ (p + C) ^ C := by linarith
  have hiC : (p + 2) ^ 3 ≤ (p + C) ^ C := by linarith
  obtain ⟨b, v, hF, M, hM, hin, hout, hb, hV, hQ, hbuild⟩ :=
    hfamily (G := Option (ZMod N)) (σ := Unit) D hp0 (fun i => (hTc i).1)
  let F : ∀ i, (D i).SquareModelData := fun i =>
    { basis := b i, weight := v i, layers := hF i, grid := M i,
      grid_pos := hM i, inner := hin i, outer := hout i }
  obtain ⟨h₀, hh₀, branches, S, hSH, hSn, hlarge, hinterval⟩ := B.exists_native_partner_intervals
    (fun j => D (j, true)) (fun j => D (j, false))
    (fun j => T (j, true)) (fun j => T (j, false)) H hH hp hqp hsize
    (fun j => hTn (j, true)) (fun j => hTn (j, false)) hcorr
  let left : Option (ZMod N) → (Fin B.count × Bool) → Unit → ℤ := fun h i =>
    match h with
    | none => 0
    | some h => if i.2 then 0 else fun _ => cyclicBranchOffset h (branches i.1).1
  let right : Option (ZMod N) → (Fin B.count × Bool) → Unit → ℤ := fun h i =>
    match h with
    | none => 0
    | some _ => if i.2 then 0 else fun _ => cyclicBranchOffset h₀ (branches i.1).2
  obtain ⟨η, γ, rSq, U, hdata⟩ := hbuild (fun _ => 1) (fun _ => by norm_num) T hTc χ hvert left right
  let A : ∀ j, (F (j, true)).quotientModel.Niltest (fun _ : Unit => 1) := fun j => U none (j, true)
  let R : ZMod N → ∀ j, (F (j, false)).quotientModel.Niltest (fun _ : Unit => 1) :=
    fun h j => U (some h) (j, false)
  have hAval (j) (x) : (A j).eval x = (T (j, true)).eval x * star ((T (j, true)).eval x) := by
    change (U none (j, true)).eval x = _
    simpa only [left, right, add_zero] using (hdata none (j, true)).2.2.2.2.2.2 x
  have hRval (h j) (x) : (R h j).eval x =
      (T (j, false)).eval (x + fun _ => cyclicBranchOffset h (branches j).1) *
        star ((T (j, false)).eval (x + fun _ => cyclicBranchOffset h₀ (branches j).2)) := by
    change (U (some h) (j, false)).eval x = _
    simpa only [left, right, Bool.false_eq_true, ↓reduceIte] using
      (hdata (some h) (j, false)).2.2.2.2.2.2 x
  refine ⟨F, ?_, ?_, (fun i j k => (hb i j k).trans hcC), h₀, hh₀, branches, S, hSH, hSn, ?_,
    A, R, (fun h j => η (some h) (j, false)), (fun h j => γ (some h) (j, false)),
    (fun h j => rSq (some h) (j, false)), ?_, ?_, ?_⟩
  · exact fun i => (hV i).mono (F i).fullModel hcC
  · exact fun i => (hQ i).mono (F i).quotientModel hcC
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hiC))
      (Nat.cast_nonneg N)).trans hlarge
  · intro j
    obtain ⟨_, _, _, _, hn, hc, _⟩ := hdata none (j, true)
    refine ⟨?_, hc.mono hcC, hAval j⟩
    change (U none (j, true)).normBound ≤ 1
    rw [hn]
    exact pow_le_one₀ (by positivity) (hTn (j, true))
  · intro h j
    obtain ⟨hγ, hη, hnorm, hOrbit, hn, hc, _⟩ := hdata (some h) (j, false)
    refine ⟨hγ, (fun i => (hη i).trans (Real.exp_le_exp.mpr hcC)), ?_, hOrbit, ?_, hc.mono hcC, hRval h j⟩
    · simpa only [left, right, Bool.false_eq_true, ↓reduceIte] using hnorm
    · change (U (some h) (j, false)).normBound ≤ 1
      rw [hn]
      exact pow_le_one₀ (by positivity) (hTn (j, false))
  · intro h hh j
    obtain ⟨start, len, hlen, hbound, hshort, hvol, hbias⟩ := hinterval h hh j
    refine ⟨start, len, hlen, hbound, hshort, ?_, ?_⟩
    · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hiC))
        (Nat.cast_nonneg N)).trans hvol
    · simp only [hAval, hRval]
      exact (Real.exp_le_exp.mpr (neg_le_neg hiC)).trans hbias

end Erdos3.PositiveShiftBasis

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.PositiveShiftBasis.exists_prescribed_lower_inputs_s2_oai.{u_1, u_2} := @OAI.Erdos3.PositiveShiftBasis.exists_prescribed_lower_inputs_s2_oai.{u_1, u_2}
