-- Prove2me | solution 2 for NonExclEncroach.Channels.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T14:22:21.144985+00:00
-- url     : https://prove2.me/submissions/3f666fdf-c063-4c30-9c60-292ddaa7a854


import Definitions.Def_NonExclEncroach_Channels_Model
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.GCongr
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false




/- Inlined helper: Solutions.P087Threshold -/

namespace NonExclEncroach.Channels

theorem P087_threshold_den_pos (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < 128-16*t^2-13*t^4 := by
  have h2 : t^2 ≤ 1 := pow_le_one₀ ht0 ht1.le
  have h4 : t^4 ≤ 1 := pow_le_one₀ ht0 ht1.le
  nlinarith


theorem P087_num1_strictAnti : StrictAntiOn num1 (Set.Icc (0:ℝ) 1) := by
  intro a ha b hb hab
  have ha0 := ha.1
  have hb0 := hb.1
  have ha2 : a^2 ≤ 1 := pow_le_one₀ ha.1 ha.2
  have ha3 : a^3 ≤ 1 := pow_le_one₀ ha.1 ha.2
  have ha4 : a^4 ≤ 1 := pow_le_one₀ ha.1 ha.2
  have hb2 : b^2 ≤ 1 := pow_le_one₀ hb.1 hb.2
  have hb3 : b^3 ≤ 1 := pow_le_one₀ hb.1 hb.2
  have hb4 : b^4 ≤ 1 := pow_le_one₀ hb.1 hb.2
  have h31 : a^3*b ≤ 1 := by
    have h := mul_le_mul ha3 hb.2 hb.1 (by norm_num : (0:ℝ) ≤ 1)
    simpa using h
  have h22 : a^2*b^2 ≤ 1 := by
    have h := mul_le_mul ha2 hb2 (sq_nonneg b) (by norm_num : (0:ℝ) ≤ 1)
    simpa using h
  have h13 : a*b^3 ≤ 1 := by
    have h := mul_le_mul ha.2 hb3 (pow_nonneg hb.1 3) (by norm_num : (0:ℝ) ≤ 1)
    simpa using h
  let Q := a^4+a^3*b+a^2*b^2+a*b^3+b^4
  let S := 32*(a+b)+14*(a^2+a*b+b^2)+8*(a^3+a^2*b+a*b^2+b^3)+
    (a^5+a^4*b+a^3*b^2+a^2*b^3+a*b^4+b^5)
  have hQ : Q ≤ 5 := by dsimp [Q]; linarith
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hpos : 0 < 80-4*Q+S := by linarith
  have hid : num1 a-num1 b=(b-a)*(80-4*Q+S) := by
    dsimp [num1,Q,S]
    ring
  have hp : 0 < num1 a-num1 b := by rw [hid]; exact mul_pos (sub_pos.mpr hab) hpos
  linarith

theorem P087_num1_pos_theta_lt_seven_twentieths (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hn : 0 < num1 t) : t < 7/20 := by
  by_contra h
  have ht : (7/20:ℝ) ≤ t := le_of_not_gt h
  have hmon := P087_num1_strictAnti.antitoneOn
    (show (7/20:ℝ) ∈ Set.Icc (0:ℝ) 1 by norm_num) ⟨ht0,ht1.le⟩ ht
  have hval : num1 (7/20:ℝ) < 0 := by norm_num [num1]
  linarith

theorem P087_c2_factor (t : ℝ) :
    c2 t=t*num1 t/(2*(1+t)*(128-16*t^2-13*t^4)) := by
  unfold c2
  congr 1
  unfold num1
  ring

theorem P087_c2_pos_of_num1_pos (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hn : 0 < num1 t) : 0 < c2 t := by
  rw [P087_c2_factor]
  exact div_pos (mul_pos ht0 hn) (mul_pos (mul_pos (by norm_num) (by linarith))
    (P087_threshold_den_pos t ht0.le ht1))

theorem P087_c2_neg_of_num1_neg (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hn : num1 t < 0) : c2 t < 0 := by
  rw [P087_c2_factor]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ht0 hn)
    (mul_pos (mul_pos (by norm_num) (by linarith)) (P087_threshold_den_pos t ht0.le ht1))

theorem P087_threshold_exists :
    ∃ θhat : ℝ, 0 < θhat ∧ θhat < 1 ∧ num1 θhat=0 ∧
      (∀ t, 0 < t → t < θhat → 0 < c2 t) ∧
      (∀ t, θhat < t → t < 1 → c2 t < 0) := by
  have hc : Continuous num1 := by unfold num1; fun_prop
  obtain ⟨θhat,hθ,heq⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1)
    hc.continuousOn (show (0:ℝ) ∈ Set.Icc (num1 1) (num1 0) by norm_num [num1])
  have h0 : 0 < θhat := by
    by_contra h
    have he : θhat=0 := by have := hθ.1; linarith
    subst θhat
    norm_num [num1] at heq
  have h1 : θhat < 1 := by
    by_contra h
    have he : θhat=1 := by have := hθ.2; linarith
    subst θhat
    norm_num [num1] at heq
  refine ⟨θhat,h0,h1,heq,?_,?_⟩
  · intro t ht0 htθ
    have ht1 : t < 1 := lt_trans htθ h1
    have hn := P087_num1_strictAnti ⟨ht0.le,ht1.le⟩ hθ htθ
    rw [heq] at hn
    exact P087_c2_pos_of_num1_pos t ht0 ht1 hn
  · intro t hθt ht1
    have ht0 : 0 < t := lt_trans h0 hθt
    have hn := P087_num1_strictAnti hθ ⟨ht0.le,ht1.le⟩ hθt
    rw [heq] at hn
    exact P087_c2_neg_of_num1_neg t ht0 ht1 hn

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087StageIII -/

namespace NonExclEncroach.Channels

/-- Complementarity is sufficient for maximizing a concave quadratic on the half-line. -/
theorem P087_quadratic_le (A x z : ℝ) (hz : 0 ≤ z)
    (hs : A ≤ 2 * x) (hc : x * (2 * x - A) = 0) :
    z * (A - z) ≤ x * (A - x) := by
  nlinarith [sq_nonneg (z - x), mul_nonneg hz (sub_nonneg.mpr hs)]

/-- A complete active-set certificate for the two stage-III best responses. -/
theorem P087_stageIII_of_complementarity (θ c b q1 y z : ℝ)
    (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hys : 1 - c - q1 ≤ 2 * y + θ * z)
    (hzs : 1 - b - 2 * θ * q1 ≤ 2 * z + θ * y)
    (hyc : y * (2 * y + θ * z - (1 - c - q1)) = 0)
    (hzc : z * (2 * z + θ * y - (1 - b - 2 * θ * q1)) = 0) :
    IsStageIII θ c b q1 y z := by
  constructor
  · refine ⟨hy, ?_⟩
    intro r hr
    have h := P087_quadratic_le (1 - c - q1 - θ * z) y r hr
      (by linarith) (by nlinarith [hyc])
    dsimp only [pd]
    nlinarith only [h]
  · refine ⟨hz, ?_⟩
    intro r hr
    have h := P087_quadratic_le (1 - b - 2 * θ * q1 - θ * y) z r hr
      (by linarith) (by nlinarith [hzc])
    dsimp only [resellerProfit, p1, p2]
    nlinarith only [h]

/-- Global stage-III existence, including every zero-quantity boundary.

No positivity hypothesis on the paper's interior formula is required, and `q1`,
`b`, and `c` are arbitrary. The four cases are both inactive, only supplier 1's
direct channel active, only the conjectured reseller order active, and both active.
-/
theorem P087_stageIII_exists (θ c b q1 : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ y z, IsStageIII θ c b q1 y z := by
  let A := 1 - c - q1
  let B := 1 - b - 2 * θ * q1
  have close : ∀ y z : ℝ, 0 ≤ y → 0 ≤ z → A ≤ 2*y + θ*z →
      B ≤ 2*z + θ*y → y*(2*y + θ*z - A) = 0 →
      z*(2*z + θ*y - B) = 0 → IsStageIII θ c b q1 y z := by
    intro y z hy hz hys hzs hyc hzc
    exact P087_stageIII_of_complementarity θ c b q1 y z hy hz hys hzs hyc hzc
  by_cases hA : A ≤ 0
  · by_cases hB : B ≤ 0
    · refine ⟨0, 0, close 0 0 ?_ ?_ ?_ ?_ ?_ ?_⟩ <;> simp_all
    · have hBpos : 0 < B := lt_of_not_ge hB
      refine ⟨0, B/2, close 0 (B/2) ?_ ?_ ?_ ?_ ?_ ?_⟩
      · norm_num
      · positivity
      · nlinarith [mul_nonneg hθ0 (le_of_lt hBpos)]
      · linarith
      · ring
      · ring
  · have hApos : 0 < A := lt_of_not_ge hA
    by_cases hBA : 2 * B ≤ θ * A
    · refine ⟨A/2, 0, close (A/2) 0 ?_ ?_ ?_ ?_ ?_ ?_⟩
      · positivity
      · norm_num
      · linarith
      · linarith
      · ring
      · ring
    · have hBpos : 0 < B := by
        have := mul_nonneg hθ0 (le_of_lt hApos)
        linarith
      by_cases hAB : 2 * A ≤ θ * B
      · refine ⟨0, B/2, close 0 (B/2) ?_ ?_ ?_ ?_ ?_ ?_⟩
        · norm_num
        · positivity
        · linarith
        · linarith
        · ring
        · ring
      · have hden : 0 < 4 - θ^2 := by nlinarith [sq_nonneg θ, sq_nonneg (θ-1)]
        have hy : 0 ≤ (2*A - θ*B)/(4-θ^2) := div_nonneg (by linarith) (le_of_lt hden)
        have hz : 0 ≤ (2*B - θ*A)/(4-θ^2) := div_nonneg (by linarith) (le_of_lt hden)
        have heqY : 2*((2*A-θ*B)/(4-θ^2)) + θ*((2*B-θ*A)/(4-θ^2)) = A := by
          field_simp
          <;> ring
        have heqZ : 2*((2*B-θ*A)/(4-θ^2)) + θ*((2*A-θ*B)/(4-θ^2)) = B := by
          field_simp
          <;> ring
        refine ⟨(2*A-θ*B)/(4-θ^2), (2*B-θ*A)/(4-θ^2),
          close _ _ hy hz heqY.ge heqZ.ge ?_ ?_⟩
        · rw [heqY]
          ring
        · rw [heqZ]
          ring

/-- The unique best response to a scalar concave quadratic. -/
theorem P087_quadratic_optimizer (A x : ℝ)
    (h : IsBestResponse (fun z ↦ z*(A-z)) x) : x = max (A/2) 0 := by
  by_cases hA : A ≤ 0
  · have hzero := h.2 0 (le_refl 0)
    have hsq : x^2 = 0 := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos h.1 hA, sq_nonneg x]
    have hx : x = 0 := sq_eq_zero_iff.mp hsq
    rw [hx, max_eq_right (by linarith)]
  · have hbest := h.2 (A/2) (by linarith)
    have hsq : (x-A/2)^2 = 0 := by nlinarith [sq_nonneg (x-A/2)]
    have hx : x = A/2 := sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    rw [hx, max_eq_left (by linarith)]

theorem P087_quadratic_necessary (A x : ℝ)
    (h : IsBestResponse (fun z ↦ z*(A-z)) x) :
    A ≤ 2*x ∧ x*(2*x-A) = 0 := by
  rw [P087_quadratic_optimizer A x h]
  by_cases hA : 0 ≤ A
  · rw [max_eq_left (by linarith)]
    constructor
    · linarith
    · ring
  · rw [max_eq_right (by linarith)]
    constructor
    · linarith
    · ring

/-- Every stage-III response satisfies the same complementarity certificate. -/
theorem P087_stageIII_complementarity (θ c b q1 y z : ℝ)
    (h : IsStageIII θ c b q1 y z) :
    0 ≤ y ∧ 0 ≤ z ∧
      1-c-q1 ≤ 2*y+θ*z ∧ 1-b-2*θ*q1 ≤ 2*z+θ*y ∧
      y*(2*y+θ*z-(1-c-q1)) = 0 ∧ z*(2*z+θ*y-(1-b-2*θ*q1)) = 0 := by
  have hyb : IsBestResponse (fun r ↦ r*((1-c-q1-θ*z)-r)) y := by
    refine ⟨h.1.1, ?_⟩
    intro r hr
    have hh := h.1.2 r hr
    dsimp only [pd] at hh
    nlinarith only [hh]
  have hzb : IsBestResponse (fun r ↦ r*((1-b-2*θ*q1-θ*y)-r)) z := by
    refine ⟨h.2.1, ?_⟩
    intro r hr
    have hh := h.2.2 r hr
    dsimp only [resellerProfit, p1, p2] at hh
    nlinarith only [hh]
  obtain ⟨hys, hyc⟩ := P087_quadratic_necessary _ _ hyb
  obtain ⟨hzs, hzc⟩ := P087_quadratic_necessary _ _ hzb
  refine ⟨h.1.1, h.2.1, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- Closed global coordinates, retaining both possible zero-quantity boundaries. -/
theorem P087_stageIII_coordinates (θ c b q1 y z : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (h : IsStageIII θ c b q1 y z) :
    y = max 0 (min ((1-c-q1)/2)
      ((2*(1-c-q1)-θ*(1-b-2*θ*q1))/(4-θ^2))) ∧
    z = max 0 ((1-b-2*θ*q1-θ*y)/2) := by
  obtain ⟨hy, hz, hys, hzs, hyc, hzc⟩ := P087_stageIII_complementarity θ c b q1 y z h
  let A := 1-c-q1
  let B := 1-b-2*θ*q1
  have hden : 0 < 4-θ^2 := by nlinarith [sq_nonneg θ, sq_nonneg (θ-1)]
  have hY : y = max 0 (min (A/2) ((2*A-θ*B)/(4-θ^2))) := by
    by_cases hy0 : y = 0
    · rw [hy0] at hys hzs hzc ⊢
      apply (max_eq_left ?_).symm
      by_cases hz0 : z = 0
      · rw [hz0] at hys
        exact (min_le_left _ _).trans (by dsimp [A]; linarith)
      · have hzEq : 2*z = B := by
          have : 2*z + θ*0 - (1-b-2*θ*q1) = 0 := (mul_eq_zero.mp hzc).resolve_left hz0
          dsimp [B]
          linarith
        apply (min_le_right _ _).trans
        apply div_nonpos_of_nonpos_of_nonneg
        · dsimp [A]
          nlinarith
        · exact le_of_lt hden
    · have hyEq : 2*y+θ*z = A := by
        have := (mul_eq_zero.mp hyc).resolve_left hy0
        exact (sub_eq_zero.mp this)
      by_cases hz0 : z = 0
      · have hyA : y = A/2 := by rw [hz0] at hyEq; linarith
        have hle : y ≤ (2*A-θ*B)/(4-θ^2) := by
          apply (le_div_iff₀ hden).2
          have hslack : 0 ≤ θ*(θ*y-B) := by
            apply mul_nonneg hθ0
            dsimp [B]
            rw [hz0] at hzs
            linarith
          rw [hz0] at hyEq
          nlinarith
        rw [← hyA, min_eq_left hle, max_eq_right hy]
      · have hzEq : 2*z+θ*y = B := by
          have := (mul_eq_zero.mp hzc).resolve_left hz0
          exact sub_eq_zero.mp this
        have hyI : y = (2*A-θ*B)/(4-θ^2) := by
          apply (eq_div_iff (ne_of_gt hden)).2
          nlinarith
        have hle : y ≤ A/2 := by nlinarith [mul_nonneg hθ0 hz]
        rw [← hyI, min_eq_right hle, max_eq_right hy]
  refine ⟨hY, ?_⟩
  have hzb : IsBestResponse (fun r ↦ r*((1-b-2*θ*q1-θ*y)-r)) z := by
    refine ⟨h.2.1, ?_⟩
    intro r hr
    have hh := h.2.2 r hr
    dsimp only [resellerProfit, p1, p2] at hh
    nlinarith only [hh]
  simpa only [max_comm] using P087_quadratic_optimizer _ _ hzb

/-- The global pair is unique at every observed first-product order. -/
theorem P087_stageIII_unique (θ c b q1 y z y' z' : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (h : IsStageIII θ c b q1 y z) (h' : IsStageIII θ c b q1 y' z') :
    y = y' ∧ z = z' := by
  obtain ⟨hy, hz⟩ := P087_stageIII_coordinates θ c b q1 y z hθ0 hθ1 h
  obtain ⟨hy', hz'⟩ := P087_stageIII_coordinates θ c b q1 y' z' hθ0 hθ1 h'
  have heq : y = y' := hy.trans hy'.symm
  exact ⟨heq, hz.trans (by rw [heq, ← hz'])⟩

/-- The explicit global response actually satisfies stage III. -/
theorem P087_stageIII_explicit (θ c b q1 : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    let y := max 0 (min ((1-c-q1)/2)
      ((2*(1-c-q1)-θ*(1-b-2*θ*q1))/(4-θ^2)))
    IsStageIII θ c b q1 y (max 0 ((1-b-2*θ*q1-θ*y)/2)) := by
  obtain ⟨y, z, h⟩ := P087_stageIII_exists θ c b q1 hθ0 hθ1
  obtain ⟨hy, hz⟩ := P087_stageIII_coordinates θ c b q1 y z hθ0 hθ1 h
  simpa only [← hy, ← hz] using h

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087ResellerExistence -/

namespace NonExclEncroach.Channels

/-- Nonnegative prices, direct sales, and substitution only decrease the separable
quadratic upper bound on reseller profit. -/
theorem P087_reseller_profit_upper (θ x z w1 w2 y : ℝ)
    (hθ : 0 ≤ θ) (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hy : 0 ≤ y) :
    resellerProfit θ x z w1 w2 y ≤ x - x^2 + z - z^2 := by
  have hcross : 0 ≤ θ * x * z := by positivity
  have hxy : 0 ≤ x * y := mul_nonneg hx hy
  have hzy : 0 ≤ θ * z * y := by positivity
  have hwx : 0 ≤ x * w1 := mul_nonneg hx hw1
  have hwz : 0 ≤ z * w2 := mul_nonneg hz hw2
  dsimp only [resellerProfit, p1, p2]
  nlinarith

/-- The reseller has a global optimum for every continuous nonnegative direct
quantity rule and every nonnegative price pair. No interior-quantity assumption
is imposed. -/
theorem P087_reseller_exists (θ w1 w2 : ℝ) (hθ : 0 ≤ θ)
    (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2)
    (Y : ℝ → ℝ) (hY : Continuous Y) (hY0 : ∀ x, 0 ≤ Y x) :
    ∃ x z : ℝ, 0 ≤ x ∧ 0 ≤ z ∧
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
        resellerProfit θ a b w1 w2 (Y a) ≤ resellerProfit θ x z w1 w2 (Y x) := by
  let f : ℝ × ℝ → ℝ := fun q => resellerProfit θ q.1 q.2 w1 w2 (Y q.1)
  have hf : Continuous f := by
    dsimp only [f, resellerProfit, p1, p2]
    fun_prop
  let K : Set (ℝ × ℝ) := Set.Icc (0, 0) (2, 2)
  have hzero : (0, 0) ∈ K := by norm_num [K, Set.mem_Icc, Prod.le_def]
  obtain ⟨q, hq, hmax⟩ := (isCompact_Icc : IsCompact K).exists_isMaxOn
    ⟨(0, 0), hzero⟩ hf.continuousOn
  have hq0 : 0 ≤ f q := by
    have h := hmax hzero
    simpa [f, resellerProfit] using h
  refine ⟨q.1, q.2, hq.1.1, hq.1.2, ?_⟩
  intro a b ha hb
  by_cases ha2 : a ≤ 2
  · by_cases hb2 : b ≤ 2
    · exact hmax (show (a, b) ∈ K from ⟨⟨ha, hb⟩, ⟨ha2, hb2⟩⟩)
    · have hb2' : 2 < b := lt_of_not_ge hb2
      have hup := P087_reseller_profit_upper θ a b w1 w2 (Y a) hθ ha hb hw1 hw2 (hY0 a)
      have hneg : resellerProfit θ a b w1 w2 (Y a) ≤ 0 := by
        nlinarith [sq_nonneg (a - 1/2), mul_nonneg (by linarith : 0 ≤ b - 2) hb]
      exact hneg.trans hq0
  · have ha2' : 2 < a := lt_of_not_ge ha2
    have hup := P087_reseller_profit_upper θ a b w1 w2 (Y a) hθ ha hb hw1 hw2 (hY0 a)
    have hneg : resellerProfit θ a b w1 w2 (Y a) ≤ 0 := by
      nlinarith [sq_nonneg (b - 1/2), mul_nonneg (by linarith : 0 ≤ a - 2) ha]
    exact hneg.trans hq0

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087Continuation -/

namespace NonExclEncroach.Channels

noncomputable section

/-- The direct quantity rule with both zero-quantity boundaries retained. -/
def P087_globalY (θ c b x : ℝ) : ℝ :=
  max 0 (min ((1 - c - x) / 2)
    ((2 * (1 - c - x) - θ * (1 - b - 2 * θ * x)) / (4 - θ ^ 2)))

/-- The corresponding conjectured second-product quantity. -/
def P087_globalQ (θ c b x : ℝ) : ℝ :=
  max 0 ((1 - b - 2 * θ * x - θ * P087_globalY θ c b x) / 2)

theorem P087_globalY_continuous (θ c b : ℝ) : Continuous (P087_globalY θ c b) := by
  unfold P087_globalY
  fun_prop

theorem P087_globalY_nonneg (θ c b x : ℝ) : 0 ≤ P087_globalY θ c b x :=
  le_max_left _ _

theorem P087_global_stageIII (θ c b x : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    IsStageIII θ c b x (P087_globalY θ c b x) (P087_globalQ θ c b x) :=
  P087_stageIII_explicit θ c b x hθ0 hθ1



end

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087SupplierQuadratic -/

namespace NonExclEncroach.Channels

/-- A global supplier-2 revenue bound for every nonnegative deviating price.
The hypotheses are the reseller's two complementary first-order conditions
on one concave quadratic branch, with its supplier-2 optimum price `b`.
They include both reseller boundaries `x=0` and `z=0`. This lemma alone does
not assert that every global response of the original game lies in this branch. -/
theorem P087_supplier2_quadratic_bound
    (r s u V b v x z : ℝ)
    (hr : 0 < r) (hs : 0 ≤ s) (hdet : 0 < 4 * r - s ^ 2)
    (hv : 0 ≤ v) (hz : 0 ≤ z)
    (hprice : 2 * r * (V - 2 * b) = s * u)
    (hxopt : u ≤ 2 * r * x + s * z)
    (hzopt : z * (2 * z + s * x - (V - v)) = 0) :
    supplier2Profit z v ≤ (2 * r / (4 * r - s ^ 2)) * b ^ 2 := by
  unfold supplier2Profit
  by_cases hz0 : z = 0
  · rw [hz0, zero_mul]
    exact mul_nonneg (div_nonneg (by linarith) hdet.le) (sq_nonneg _)
  · have hzEq : 2 * z + s * x = V - v := by
      rcases mul_eq_zero.mp hzopt with h | h
      · exact (hz0 h).elim
      · linarith
    have hsopt := mul_le_mul_of_nonneg_left hxopt hs
    have hbound : (4 * r - s ^ 2) * z ≤ 2 * r * (2 * b - v) := by
      calc
        (4 * r - s ^ 2) * z = 2 * r * (V - v) - s * (2 * r * x + s * z) := by
          rw [← hzEq]
          ring
        _ ≤ 2 * r * (V - v) - s * u := sub_le_sub_left hsopt _
        _ = 2 * r * (2 * b - v) := by nlinarith [hprice]
    have hscaled := mul_le_mul_of_nonneg_left hbound hv
    have hsquare : 0 ≤ 2 * r * (v - b) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    rw [div_mul_eq_mul_div, le_div_iff₀ hdet]
    nlinarith [hscaled, hsquare]

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087SupplierResponse -/

namespace NonExclEncroach.Channels

def P087_retailQuadratic (r s u W x z : ℝ) : ℝ :=
  u * x + W * z - r * x ^ 2 - z ^ 2 - s * x * z

theorem P087_retailQuadratic_max_of_complementarity
    (r s u W X Z : ℝ) (hdet : 0 < 4 * r - s ^ 2)
    (hxopt : u ≤ 2 * r * X + s * Z) (hzopt : W ≤ 2 * Z + s * X)
    (hxcomp : X * (2 * r * X + s * Z - u) = 0)
    (hzcomp : Z * (2 * Z + s * X - W) = 0)
    (x z : ℝ) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    P087_retailQuadratic r s u W x z ≤ P087_retailQuadratic r s u W X Z := by
  have h₁ := mul_nonneg hx (sub_nonneg.mpr hxopt)
  have h₂ := mul_nonneg hz (sub_nonneg.mpr hzopt)
  have h₃ := sq_nonneg (2 * (z - Z) + s * (x - X))
  have h₄ := mul_nonneg hdet.le (sq_nonneg (x - X))
  unfold P087_retailQuadratic
  nlinarith only [h₁, h₂, h₃, h₄, hxcomp, hzcomp]

/-- The three active sets of a strictly concave retailer quadratic. -/
theorem P087_retailQuadratic_complementarity_exists
    (r s u W : ℝ) (hr : 0 < r) (hs : 0 < s) (hu : 0 ≤ u)
    (hdet : 0 < 4 * r - s ^ 2) :
    ∃ x z : ℝ, 0 ≤ x ∧ 0 ≤ z ∧ x ≤ u / (2 * r) ∧
      u ≤ 2 * r * x + s * z ∧ W ≤ 2 * z + s * x ∧
      x * (2 * r * x + s * z - u) = 0 ∧
      z * (2 * z + s * x - W) = 0 := by
  by_cases hzeroX : 2 * u ≤ s * W
  · have hW : 0 ≤ W :=
      nonneg_of_mul_nonneg_right (show 0 ≤ s * W by linarith) hs
    refine ⟨0, W / 2, le_rfl, by positivity, div_nonneg hu (by linarith), ?_, ?_, ?_, ?_⟩
    · nlinarith only [hzeroX]
    · ring_nf
      exact le_rfl
    · ring
    · ring
  · by_cases hzeroZ : 2 * r * W ≤ s * u
    · let x := u / (2 * r)
      have hx0 : 0 ≤ x := div_nonneg hu (by linarith)
      have hxEq : 2 * r * x = u := by dsimp [x]; field_simp
      have hW : W ≤ s * x := by
        dsimp [x]
        rw [← mul_div_assoc, le_div_iff₀ (show 0 < 2 * r by linarith)]
        nlinarith only [hzeroZ]
      refine ⟨x, 0, hx0, le_rfl, le_rfl, ?_, ?_, ?_, ?_⟩
      · nlinarith only [hxEq]
      · simpa using hW
      · rw [mul_zero, add_zero, hxEq]
        ring
      · ring
    · let δ := 4 * r - s ^ 2
      have hδ : δ ≠ 0 := ne_of_gt hdet
      let x := (2 * u - s * W) / δ
      let z := (2 * r * W - s * u) / δ
      have hx0 : 0 ≤ x := div_nonneg (by linarith) hdet.le
      have hz0 : 0 ≤ z := div_nonneg (by linarith) hdet.le
      have hxEq : 2 * r * x + s * z = u := by
        change 2 * r * ((2 * u - s * W) / δ) + s * ((2 * r * W - s * u) / δ) = u
        field_simp [hδ]
        dsimp [δ]
        ring
      have hzEq : 2 * z + s * x = W := by
        change 2 * ((2 * r * W - s * u) / δ) + s * ((2 * u - s * W) / δ) = W
        field_simp [hδ]
        dsimp [δ]
        ring
      have hxBound : x ≤ u / (2 * r) := by
        apply (le_div_iff₀ (show 0 < 2 * r by linarith)).2
        nlinarith only [hxEq, mul_nonneg hs.le hz0]
      refine ⟨x, z, hx0, hz0, hxBound, le_of_eq hxEq.symm, le_of_eq hzEq.symm, ?_, ?_⟩
      · rw [hxEq]
        ring
      · rw [hzEq]
        ring

/-- At every nonnegative actual price, choose a globally optimal quadratic
retailer response and obtain the supplier-2 revenue bound. -/
theorem P087_supplier2_quadratic_response_exists
    (r s u V b v : ℝ) (hr : 0 < r) (hs : 0 < s) (hu : 0 ≤ u)
    (hdet : 0 < 4 * r - s ^ 2) (hv : 0 ≤ v)
    (hprice : 2 * r * (V - 2 * b) = s * u) :
    ∃ x z : ℝ, 0 ≤ x ∧ 0 ≤ z ∧ x ≤ u / (2 * r) ∧
      (∀ x' z', 0 ≤ x' → 0 ≤ z' →
        P087_retailQuadratic r s u (V - v) x' z' ≤
          P087_retailQuadratic r s u (V - v) x z) ∧
      supplier2Profit z v ≤ (2 * r / (4 * r - s ^ 2)) * b ^ 2 := by
  obtain ⟨x, z, hx, hz, hcut, hxopt, hzopt, hxcomp, hzcomp⟩ :=
    P087_retailQuadratic_complementarity_exists r s u (V - v) hr hs hu hdet
  refine ⟨x, z, hx, hz, hcut, ?_, ?_⟩
  · exact P087_retailQuadratic_max_of_complementarity r s u (V - v) x z
      hdet hxopt hzopt hxcomp hzcomp
  · exact P087_supplier2_quadratic_bound r s u V b v x z hr hs.le hdet hv hz
      hprice hxopt hzcomp

/-- A same-quantity cover of the full retailer objective by its first branch
transfers the chosen quadratic response and its global supplier bound. -/
theorem P087_supplier2_response_of_cover
    (F : ℝ → ℝ → ℝ) (r s u V b v k : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hu : 0 ≤ u)
    (hdet : 0 < 4 * r - s ^ 2) (hv : 0 ≤ v)
    (hprice : 2 * r * (V - 2 * b) = s * u) (hcut : u / (2 * r) ≤ k)
    (hmatch : ∀ x z, 0 ≤ x → x ≤ k → 0 ≤ z →
      F x z = P087_retailQuadratic r s u (V - v) x z)
    (hcover : ∀ x z, 0 ≤ x → 0 ≤ z → ∃ w, 0 ≤ w ∧ w ≤ k ∧
      F x z ≤ P087_retailQuadratic r s u (V - v) w z) :
    ∃ x z : ℝ, 0 ≤ x ∧ 0 ≤ z ∧ x ≤ k ∧
      (∀ x' z', 0 ≤ x' → 0 ≤ z' → F x' z' ≤ F x z) ∧
      supplier2Profit z v ≤ (2 * r / (4 * r - s ^ 2)) * b ^ 2 := by
  obtain ⟨x, z, hx, hz, hxu, hmax, hprofit⟩ :=
    P087_supplier2_quadratic_response_exists r s u V b v hr hs hu hdet hv hprice
  have hxk := hxu.trans hcut
  refine ⟨x, z, hx, hz, hxk, ?_, hprofit⟩
  intro x' z' hx' hz'
  obtain ⟨w, hw, hwk, hdom⟩ := hcover x' z' hx' hz'
  rw [hmatch x z hx hxk hz]
  exact hdom.trans (hmax w z' hw hz')

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087DOClipping -/

namespace NonExclEncroach.Channels

/-- Every piece of the exact direct-quantity rule decreases at slope at most one half. -/
theorem P087_clippedY_half_lipschitz (A α β h x : ℝ)
    (hβ : β ≤ 1 / 2) (hhx : h ≤ x) :
    max 0 (min ((A-h)/2) (α-β*h)) ≤
      max 0 (min ((A-x)/2) (α-β*x)) + (x-h)/2 := by
  let ε := (x-h)/2
  have hε : 0 ≤ ε := by dsimp [ε]; linarith
  have h₁ : (A-h)/2 ≤ (A-x)/2 + ε := by dsimp [ε]; linarith
  have h₂ : α-β*h ≤ α-β*x + ε := by
    have := mul_nonneg (show 0 ≤ 1/2-β by linarith) (sub_nonneg.mpr hhx)
    dsimp [ε]
    nlinarith only [this]
  have hm := min_le_min h₁ h₂
  have hs : min ((A-x)/2+ε) (α-β*x+ε) =
      min ((A-x)/2) (α-β*x) + ε := by
    rw [min_add_add_right]
  rw [hs] at hm
  apply max_le
  · exact add_nonneg (le_max_left _ _) hε
  · have hmax : min ((A-x)/2) (α-β*x) ≤ max 0 (min ((A-x)/2) (α-β*x)) := le_max_right _ _
    dsimp [ε] at hm
    linarith only [hm, hmax]

/-- The same rule lies above its half-slope affine lower support. -/
theorem P087_clippedY_lower (A α β x : ℝ)
    (hα : α ≤ A/2) (hβ : β ≤ 1/2) (hx : 0 ≤ x) :
    α-x/2 ≤ max 0 (min ((A-x)/2) (α-β*x)) := by
  apply (le_min ?_ ?_).trans (le_max_right _ _)
  · linarith
  · nlinarith [mul_nonneg (show 0 ≤ 1/2-β by linarith) hx]

/-- Large first-product orders can be clipped without changing the second order.
The bound is uniform in both actual wholesale prices. -/
theorem P087_reseller_clip (θ a v α h x z Yh Yx : ℝ)
    (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hz : 0 ≤ z) (hh : 0 ≤ h)
    (hhx : h ≤ x) (hcut : 1-α ≤ h)
    (hlower : α-x/2 ≤ Yx) (hlip : Yh ≤ Yx+(x-h)/2) :
    resellerProfit θ x z a v Yx + (x-h)^2/2 ≤
      resellerProfit θ h z a v Yh := by
  have hdist : 0 ≤ x-h := sub_nonneg.mpr hhx
  have hθz := mul_nonneg hθ hz
  have hc : 0 ≤ h+θ*z := by linarith
  have h₁ := mul_nonneg hc (show 0 ≤ Yx+(x-h)/2-Yh by linarith)
  have h₂ := mul_nonneg hdist (show 0 ≤ Yx-(α-x/2) by linarith)
  have h₃ := mul_nonneg hdist (show 0 ≤ h-1+α+a+3/2*(θ*z) by linarith)
  unfold resellerProfit p1 p2
  nlinarith only [h₁, h₂, h₃]

/-- Complementarity exists without a restriction on the first linear coefficient. -/
theorem P087_retailQuadratic_complementarity_all
    (r s u W h : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hdet : 0 < 4*r-s^2) (hh : 0 ≤ h) (huh : u ≤ 2*r*h) :
    ∃ x z : ℝ, 0 ≤ x ∧ 0 ≤ z ∧ x ≤ h ∧
      u ≤ 2*r*x+s*z ∧ W ≤ 2*z+s*x ∧
      x*(2*r*x+s*z-u)=0 ∧ z*(2*z+s*x-W)=0 := by
  by_cases hu : 0 ≤ u
  · obtain ⟨x,z,hx,hz,hxu,hxopt,hzopt,hxc,hzc⟩ :=
      P087_retailQuadratic_complementarity_exists r s u W hr hs hu hdet
    have hcut : u/(2*r) ≤ h :=
      (div_le_iff₀ (show 0 < 2*r by linarith)).2 (by nlinarith only [huh])
    exact ⟨x,z,hx,hz,hxu.trans hcut,hxopt,hzopt,hxc,hzc⟩
  · by_cases hW : 0 ≤ W
    · refine ⟨0,W/2,le_rfl,by positivity,hh,?_,?_,?_,?_⟩
      · have := mul_nonneg hs.le hW
        nlinarith only [this, hu]
      · ring_nf
        exact le_rfl
      · ring
      · ring
    · refine ⟨0,0,le_rfl,le_rfl,hh,?_,?_,?_,?_⟩ <;> simp_all <;> linarith

/-- A bounded affine stage rule, plus the uniform clipping certificate, reduces
all actual wholesale prices to a single positive-definite quadratic. -/
theorem P087_DO_response_exists
    (θ a v α β r s V h : ℝ) (Y : ℝ → ℝ)
    (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hr : 0 < r) (hs : 0 < s)
    (hdet : 0 < 4*r-s^2) (hh : 0 ≤ h)
    (hcut : 1-α ≤ h) (hu : 1-a-α ≤ 2*r*h)
    (hrdef : r=1-β) (hsdef : s=θ*(2-β)) (hVdef : V=1-θ*α)
    (hlinear : ∀x, 0 ≤ x → x ≤ h → Y x=α-β*x)
    (hlower : ∀x, 0 ≤ x → α-x/2 ≤ Y x)
    (hlip : ∀x, h ≤ x → Y h ≤ Y x+(x-h)/2) :
    ∃ x z : ℝ, 0 ≤ x ∧ 0 ≤ z ∧ x ≤ h ∧
      1-a-α ≤ 2*r*x+s*z ∧ V-v ≤ 2*z+s*x ∧
      x*(2*r*x+s*z-(1-a-α))=0 ∧ z*(2*z+s*x-(V-v))=0 ∧
      (∀x' z', 0 ≤ x' → 0 ≤ z' →
        resellerProfit θ x' z' a v (Y x') ≤ resellerProfit θ x z a v (Y x)) := by
  obtain ⟨x,z,hx,hz,hxh,hxo,hzo,hxc,hzc⟩ :=
    P087_retailQuadratic_complementarity_all r s (1-a-α) (V-v) h hr hs hdet hh hu
  have hmatch : ∀q Z, 0 ≤ q → q ≤ h →
      resellerProfit θ q Z a v (Y q)=P087_retailQuadratic r s (1-a-α) (V-v) q Z := by
    intro q Z hq hqh
    rw [hlinear q hq hqh, hrdef, hsdef, hVdef]
    unfold resellerProfit p1 p2 P087_retailQuadratic
    ring
  refine ⟨x,z,hx,hz,hxh,hxo,hzo,hxc,hzc,?_⟩
  intro q Z hq hZ
  have hmax := P087_retailQuadratic_max_of_complementarity r s (1-a-α) (V-v)
    x z hdet hxo hzo hxc hzc
  rw [hmatch x z hx hxh]
  by_cases hqh : q ≤ h
  · rw [hmatch q Z hq hqh]
    exact hmax q Z hq hZ
  · have hhq : h ≤ q := le_of_lt (lt_of_not_ge hqh)
    have hc := P087_reseller_clip θ a v α h q Z (Y h) (Y q)
      hθ ha hZ hh hhq hcut (hlower q hq) (hlip q hhq)
    have hdom : resellerProfit θ q Z a v (Y q) ≤ resellerProfit θ h Z a v (Y h) := by
      nlinarith only [hc, sq_nonneg (q-h)]
    rw [hmatch h Z hh le_rfl] at hdom
    exact hdom.trans (hmax h Z hh hZ)

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087DOCoefficients -/

namespace NonExclEncroach.Channels

noncomputable def doBeta (t : ℝ) : ℝ := 2*(1-t^2)/(4-t^2)
noncomputable def doEll (t : ℝ) : ℝ := 3*t/(4-t^2)
noncomputable def doR (t : ℝ) : ℝ := 1-doBeta t
noncomputable def doS (t : ℝ) : ℝ := 2*doEll t

theorem P087_DO_coefficient_identities (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    2*doBeta t+t*doEll t=1 ∧ 2*doEll t+t*doBeta t=2*t ∧
    4*doR t-(doS t)^2=4*(1-t^2)*(8+t^2)/(4-t^2)^2 ∧
    2*doR t-doS t*doEll t-(doBeta t)^2=
      6*(1-t^2)*(2+t^2)/(4-t^2)^2 := by
  have ht : t^2 < 1 := by nlinarith [sq_nonneg (t-1)]
  have hd : 4-t^2 ≠ 0 := by linarith
  unfold doR doS doBeta doEll
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    ring
  constructor <;> field_simp <;> ring

theorem P087_DO_coefficient_signs (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    0 ≤ doBeta t ∧ doBeta t ≤ 1/2 ∧ 0 < doEll t ∧
    0 < doR t ∧ 0 < doS t ∧
    0 < 4*doR t-(doS t)^2 ∧
    0 < 2*doR t-doS t*doEll t-(doBeta t)^2 := by
  have ht : t^2 < 1 := by nlinarith [sq_nonneg (t-1)]
  have hd : 0 < 4-t^2 := by linarith
  have hβ : 0 ≤ doBeta t := by unfold doBeta; positivity
  have hβu : doBeta t ≤ 1/2 := by
    unfold doBeta
    apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg t]
  have hell : 0 < doEll t := by unfold doEll; positivity
  have hr : 0 < doR t := by unfold doR; linarith
  have hs : 0 < doS t := by unfold doS; linarith
  obtain ⟨_,_,hδ,hη⟩ := P087_DO_coefficient_identities t ht0.le ht1
  refine ⟨hβ,hβu,hell,hr,hs,?_,?_⟩
  · rw [hδ]
    positivity
  · rw [hη]
    positivity

/-- A loose uniform box suffices to keep every selected reseller optimum in the
interior stage branch; its estimates use only the exact intercept equations. -/
theorem P087_DO_intercept_box (t c b α γ : ℝ)
    (ht0 : 0 ≤ t) (htu : t ≤ 7/20) (hc0 : 0 ≤ c) (hcu : c ≤ 1/50)
    (hb0 : 0 ≤ b) (hbu : b ≤ 1/2)
    (hα : 2*α+t*γ=1-c) (hγ : 2*γ+t*α=1-b) :
    2/5 ≤ α ∧ (3/5)*doEll t ≤ γ := by
  have ht2 : t^2 < 1 := by nlinarith [sq_nonneg (t-1)]
  have hd : 0 < 4-t^2 := by linarith
  have hαid : α*(4-t^2)=2*(1-c)-t*(1-b) := by
    linear_combination 2*hα-t*hγ
  have hγid : γ*(4-t^2)=2*(1-b)-t*(1-c) := by
    linear_combination 2*hγ-t*hα
  have hellid : doEll t*(4-t^2)=3*t := by
    unfold doEll
    exact div_mul_cancel₀ _ (ne_of_gt hd)
  constructor
  · have hh : 0 ≤ (α-2/5)*(4-t^2) := by
      nlinarith only [hαid,hcu,htu,mul_nonneg ht0 hb0,sq_nonneg t]
    have hh' : 0 ≤ α-2/5 := nonneg_of_mul_nonneg_left hh hd
    linarith
  · have hh : 0 ≤ (γ-(3/5)*doEll t)*(4-t^2) := by
      nlinarith only [hγid,hellid,hbu,htu,mul_nonneg ht0 hc0]
    have hh' : 0 ≤ γ-(3/5)*doEll t := nonneg_of_mul_nonneg_left hh hd
    linarith

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087DOModel -/

namespace NonExclEncroach.Channels

/-- Exact global stage coordinates expressed through the two positive intercepts. -/
theorem P087_DO_globalY_formula (t c b α γ x : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t<1)
    (hα : 2*α+t*γ=1-c) (hγ : 2*γ+t*α=1-b) :
    P087_globalY t c b x=max 0 (min ((1-c-x)/2) (α-doBeta t*x)) := by
  have hd : 4-t^2 ≠ 0 := by nlinarith [sq_nonneg (t-1)]
  obtain ⟨hβ,hell,_,_⟩ := P087_DO_coefficient_identities t ht0 ht1
  have heq : (2*(1-c-x)-t*(1-b-2*t*x))/(4-t^2)=α-doBeta t*x := by
    apply (div_eq_iff hd).2
    linear_combination -2*hα+t*hγ+2*x*hβ-t*x*hell
  unfold P087_globalY
  rw [heq]

theorem P087_DO_globalY_linear (t c b α γ x : ℝ)
    (ht0 : 0<t) (ht1 : t<1)
    (hα : 2*α+t*γ=1-c) (hγ : 2*γ+t*α=1-b)
    (hαlo : 2/5 ≤ α) (hγlo : (3/5)*doEll t ≤ γ)
    (hx : 0 ≤ x) (hxh : x ≤ 3/5) :
    P087_globalY t c b x=α-doBeta t*x := by
  obtain ⟨hβ0,hβh,hell0,_,_,_,_⟩ := P087_DO_coefficient_signs t ht0 ht1
  obtain ⟨hβ,_,_,_⟩ := P087_DO_coefficient_identities t ht0.le ht1
  have hy0 : 0 ≤ α-doBeta t*x := by
    have := mul_le_mul_of_nonneg_right hβh hx
    nlinarith only [this,hxh,hαlo]
  have hz0 : 0 ≤ γ-doEll t*x := by
    have := mul_nonneg hell0.le (show 0 ≤ 3/5-x by linarith)
    nlinarith only [this,hγlo]
  have hyeq : 2*(α-doBeta t*x)+t*(γ-doEll t*x)=1-c-x := by
    linear_combination hα-x*hβ
  have hyle : α-doBeta t*x ≤ (1-c-x)/2 := by
    nlinarith only [hyeq,mul_nonneg ht0.le hz0]
  rw [P087_DO_globalY_formula t c b α γ x ht0.le ht1 hα hγ,
    min_eq_right hyle,max_eq_right hy0]

/-- Every actual wholesale price pair admits a globally optimal response in the
single affine branch, together with its complete quadratic optimality certificate. -/
theorem P087_DO_model_response_exists (t c b α γ a v : ℝ)
    (ht0 : 0<t) (ht1 : t<1) (ha : 0 ≤ a)
    (hα : 2*α+t*γ=1-c) (hγ : 2*γ+t*α=1-b)
    (hαlo : 2/5 ≤ α) (hγlo : (3/5)*doEll t ≤ γ) :
    ∃ x z : ℝ, 0 ≤ x ∧ 0 ≤ z ∧ x ≤ 3/5 ∧
      1-a-α ≤ 2*doR t*x+doS t*z ∧
      1-t*α-v ≤ 2*z+doS t*x ∧
      x*(2*doR t*x+doS t*z-(1-a-α))=0 ∧
      z*(2*z+doS t*x-(1-t*α-v))=0 ∧
      (∀x' z', 0 ≤ x' → 0 ≤ z' →
        resellerProfit t x' z' a v (P087_globalY t c b x') ≤
          resellerProfit t x z a v (P087_globalY t c b x)) := by
  obtain ⟨hβ0,hβh,hell0,hr0,hs0,hδ,_⟩ := P087_DO_coefficient_signs t ht0 ht1
  obtain ⟨_,hell,_,_⟩ := P087_DO_coefficient_identities t ht0.le ht1
  have hγ0 : 0 ≤ γ := by nlinarith only [hell0,hγlo]
  have hαupper : α ≤ (1-c)/2 := by nlinarith only [hα,mul_nonneg ht0.le hγ0]
  have hs : doS t=t*(2-doBeta t) := by unfold doS; nlinarith only [hell]
  have hcut : 1-a-α ≤ 2*doR t*(3/5) := by
    unfold doR
    nlinarith only [ha,hαlo,hβh]
  apply P087_DO_response_exists t a v α (doBeta t) (doR t) (doS t)
    (1-t*α) (3/5) (P087_globalY t c b)
    ht0.le ha hr0 hs0 hδ (by norm_num) (by linarith) hcut rfl hs rfl
  · exact fun x hx hxh => P087_DO_globalY_linear t c b α γ x ht0 ht1 hα hγ hαlo hγlo hx hxh
  · intro x hx
    rw [P087_DO_globalY_formula t c b α γ x ht0.le ht1 hα hγ]
    exact P087_clippedY_lower (1-c) α (doBeta t) x hαupper hβh hx
  · intro x hxh
    rw [P087_DO_globalY_formula t c b α γ (3/5) ht0.le ht1 hα hγ,
      P087_DO_globalY_formula t c b α γ x ht0.le ht1 hα hγ]
    exact P087_clippedY_half_lipschitz (1-c) α (doBeta t) (3/5) x hβh hxh

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087DOSupplierBounds -/

namespace NonExclEncroach.Channels

/-- With a direct-only monopoly price, the actual second-product order cannot
give supplier 2 more than its base revenue, irrespective of the first order. -/
theorem P087_DO_supplier2_bound (s V b γ v x z : ℝ)
    (hs : 0 ≤ s) (hx : 0 ≤ x) (hz : 0 ≤ z) (hv : 0 ≤ v)
    (hb : b=2*γ) (hV : V-b=2*γ)
    (hc : z*(2*z+s*x-(V-v))=0) :
    supplier2Profit z v ≤ b*γ := by
  have hcross := mul_nonneg (mul_nonneg hs hx) hz
  have hVe : V=4*γ := by linarith only [hb,hV]
  rw [hVe] at hc
  rw [supplier2Profit,hb]
  nlinarith only [hc,hcross,sq_nonneg (z-γ)]

/-- At the direct-only boundary price, both sides of supplier 2's kink slope
point toward the base price. This bounds all prices and all quadratic active sets. -/
theorem P087_DOB_supplier2_bound (r s u V b γ v x z : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hδ : 0 < 4*r-s^2)
    (hb : 0 ≤ b) (hγ : 0 ≤ γ) (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hV : V-b=2*γ) (hu : u=s*γ)
    (hleft : b ≤ 2*γ) (hright : (4*r-s^2)*γ ≤ 2*r*b)
    (hxo : u ≤ 2*r*x+s*z)
    (hxc : x*(2*r*x+s*z-u)=0)
    (hzc : z*(2*z+s*x-(V-v))=0) :
    supplier2Profit z v ≤ b*γ := by
  by_cases hz0 : z=0
  · simp [supplier2Profit, hz0, mul_nonneg hb hγ]
  have hzEq : 2*z+s*x=V-v := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzc).resolve_left hz0)
  by_cases hx0 : x=0
  · have hγz : γ ≤ z := by
      have hmul : 0 ≤ s*(z-γ) := by rw [hx0, hu] at hxo; nlinarith only [hxo]
      have hnon := nonneg_of_mul_nonneg_right hmul hs
      linarith
    have h₁ := mul_nonneg (sub_nonneg.mpr hγz) (show 0 ≤ 2*γ-b by linarith)
    rw [hx0] at hzEq
    have hve : v=b+2*γ-2*z := by linarith only [hzEq,hV]
    rw [supplier2Profit,hve]
    nlinarith only [h₁,sq_nonneg (z-γ)]
  · have hxEq : 2*r*x+s*z=u :=
      sub_eq_zero.mp ((mul_eq_zero.mp hxc).resolve_left hx0)
    have hzγ : z ≤ γ := by
      have hmul : 0 ≤ s*(γ-z) := by
        rw [hu] at hxEq
        nlinarith only [hxEq, mul_nonneg hr.le hx]
      have hnon := nonneg_of_mul_nonneg_right hmul hs
      linarith
    have hdiff : (4*r-s^2)*(γ-z)=2*r*(v-b) := by
      rw [hu] at hxEq
      linear_combination s * hxEq - 2*r*hzEq - 2*r*hV
    have hpositive : 0 ≤ 2*r*b-(4*r-s^2)*z := by
      nlinarith only [hright, mul_nonneg hδ.le (sub_nonneg.mpr hzγ)]
    have hbound := mul_nonneg (sub_nonneg.mpr hzγ) hpositive
    have heq : 2*r*(b*γ-z*v)=(γ-z)*(2*r*b-(4*r-s^2)*z) := by
      linear_combination z * hdiff
    have hnon : 0 ≤ b*γ-z*v := by
      apply nonneg_of_mul_nonneg_right (a:=2*r)
      · rw [heq]
        exact hbound
      · linarith
    unfold supplier2Profit
    linarith

/-- Supplier 1's envelope is a decreasing concave quadratic whenever the
candidate direct-only first derivative is nonpositive. -/
theorem P087_DO_supplier1_bound (θ c a α β γ ell r s x z : ℝ)
    (hx : 0 ≤ x) (hyz : 2*(α-β*x)+θ*z=1-c-x)
    (hz : z=γ-ell*x) (hs : s=2*ell)
    (hν : 1-α-s*γ ≤ 2*α*β)
    (hη : 0 ≤ 2*r-s*ell-β^2)
    (hxc : x*(2*r*x+s*z-(1-a-α))=0) :
    supplier1Profit θ c x z a (α-β*x) ≤ α^2 := by
  have hsquare : supplier1Profit θ c x z a (α-β*x)=(α-β*x)^2+a*x := by
    unfold supplier1Profit pd
    linear_combination -(α-β*x)*hyz
  have hlin := mul_nonneg hx (sub_nonneg.mpr hν)
  have hquad := mul_nonneg hη (sq_nonneg x)
  rw [hsquare, hz] at *
  nlinarith only [hlin, hquad, hxc]

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087EquilibriumSelected -/

namespace NonExclEncroach.Channels

/-- Assemble all-price strategies from global reseller response certificates.
The selected equilibrium outcome is retained exactly. -/
theorem P087_equilibrium_of_selected_certificates
    (θ c a b X Z : ℝ) (Y Q : ℝ → ℝ)
    (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hYcont : Continuous Y) (hYpos : ∀ x, 0 ≤ Y x)
    (hstage : ∀ x, 0 ≤ x → IsStageIII θ c b x (Y x) (Q x))
    (hX : 0 ≤ X) (hZ : 0 ≤ Z)
    (hbase : ∀ x z, 0 ≤ x → 0 ≤ z →
      resellerProfit θ x z a b (Y x) ≤ resellerProfit θ X Z a b (Y X))
    (hsupplier1 : ∀ a', 0 ≤ a' → ∃ x z, 0 ≤ x ∧ 0 ≤ z ∧
      (∀ x' z', 0 ≤ x' → 0 ≤ z' →
        resellerProfit θ x' z' a' b (Y x') ≤ resellerProfit θ x z a' b (Y x)) ∧
      supplier1Profit θ c x z a' (Y x) ≤ supplier1Profit θ c X Z a (Y X))
    (hsupplier2 : ∀ v, 0 ≤ v → ∃ x z, 0 ≤ x ∧ 0 ≤ z ∧
      (∀ x' z', 0 ≤ x' → 0 ≤ z' →
        resellerProfit θ x' z' a v (Y x') ≤ resellerProfit θ x z a v (Y x)) ∧
      supplier2Profit z v ≤ supplier2Profit Z b) :
    ∃ σ : Profile, IsEquilibrium θ c σ ∧ σ.w1=a ∧ σ.w2=b ∧
      σ.q1=X ∧ σ.q2=Z ∧ σ.y=Y X := by
  classical
  have hRex : ∀ w1 w2 : ℝ, ∃ q : ℝ × ℝ,
      0 ≤ w1 → 0 ≤ w2 → 0 ≤ q.1 ∧ 0 ≤ q.2 ∧
      ∀ x z, 0 ≤ x → 0 ≤ z →
        resellerProfit θ x z w1 w2 (Y x) ≤ resellerProfit θ q.1 q.2 w1 w2 (Y q.1) := by
    intro w1 w2
    by_cases h1 : 0 ≤ w1
    · by_cases h2 : 0 ≤ w2
      · obtain ⟨x,z,hx,hz,hm⟩ := P087_reseller_exists θ w1 w2 hθ h1 h2 Y hYcont hYpos
        exact ⟨(x,z),fun _ _ => ⟨hx,hz,hm⟩⟩
      · exact ⟨(0,0),fun _ hh => (h2 hh).elim⟩
    · exact ⟨(0,0),fun hh _ => (h1 hh).elim⟩
  choose R0 hR0 using hRex
  have hSex : ∀ v : ℝ, ∃ q : ℝ × ℝ, 0 ≤ v →
      0 ≤ q.1 ∧ 0 ≤ q.2 ∧
      (∀ x z, 0 ≤ x → 0 ≤ z →
        resellerProfit θ x z a v (Y x) ≤ resellerProfit θ q.1 q.2 a v (Y q.1)) ∧
      supplier2Profit q.2 v ≤ supplier2Profit Z b := by
    intro v
    by_cases hv : 0 ≤ v
    · obtain ⟨x,z,hx,hz,hm,hp⟩ := hsupplier2 v hv
      exact ⟨(x,z),fun _ => ⟨hx,hz,hm,hp⟩⟩
    · exact ⟨(0,0),fun h => (hv h).elim⟩
  choose S hS using hSex
  have hTex : ∀ w : ℝ, ∃ q : ℝ × ℝ, 0 ≤ w →
      0 ≤ q.1 ∧ 0 ≤ q.2 ∧
      (∀ x z, 0 ≤ x → 0 ≤ z →
        resellerProfit θ x z w b (Y x) ≤ resellerProfit θ q.1 q.2 w b (Y q.1)) ∧
      supplier1Profit θ c q.1 q.2 w (Y q.1) ≤ supplier1Profit θ c X Z a (Y X) := by
    intro w
    by_cases hw : 0 ≤ w
    · obtain ⟨x,z,hx,hz,hm,hp⟩ := hsupplier1 w hw
      exact ⟨(x,z),fun _ => ⟨hx,hz,hm,hp⟩⟩
    · exact ⟨(0,0),fun h => (hw h).elim⟩
  choose T hT using hTex
  let R : ℝ → ℝ → ℝ × ℝ := fun w1 w2 =>
    if w1=a then (if w2=b then (X,Z) else S w2) else (if w2=b then T w1 else R0 w1 w2)
  have hRbase : R a b=(X,Z) := by simp [R]
  have hR : ∀ w1 w2, 0 ≤ w1 → 0 ≤ w2 →
      0 ≤ (R w1 w2).1 ∧ 0 ≤ (R w1 w2).2 ∧
      ∀ x z, 0 ≤ x → 0 ≤ z →
        resellerProfit θ x z w1 w2 (Y x) ≤
          resellerProfit θ (R w1 w2).1 (R w1 w2).2 w1 w2 (Y (R w1 w2).1) := by
    intro w1 w2 h1 h2
    by_cases h1a : w1=a
    · subst w1
      by_cases h2b : w2=b
      · subst w2
        simpa only [hRbase] using And.intro hX (And.intro hZ hbase)
      · simpa only [R,if_pos rfl,if_neg h2b] using
          And.intro (hS w2 h2).1 (And.intro (hS w2 h2).2.1 (hS w2 h2).2.2.1)
    · by_cases h2b : w2=b
      · subst w2
        simpa [R,h1a] using
          And.intro (hT w1 h1).1 (And.intro (hT w1 h1).2.1 (hT w1 h1).2.2.1)
      · simpa only [R,if_neg h1a,if_neg h2b] using hR0 w1 w2 h1 h2
  let σ : Profile := ⟨a,b,Y,Q,R⟩
  have hq1 : σ.q1=X := by change (R a b).1=X; rw [hRbase]
  have hq2 : σ.q2=Z := by change (R a b).2=Z; rw [hRbase]
  have hy : σ.y=Y X := by change Y σ.q1=Y X; rw [hq1]
  refine ⟨σ,?_,rfl,rfl,hq1,hq2,hy⟩
  refine ⟨ha,hb,hstage,hR,?_,?_⟩
  · intro w1 hw1
    change supplier1Profit θ c (R w1 b).1 (R w1 b).2 w1 (Y (R w1 b).1) ≤
      supplier1Profit θ c (R a b).1 (R a b).2 a (Y (R a b).1)
    rw [hRbase]
    by_cases h1a : w1=a
    · subst w1
      simp only [hRbase,le_refl]
    · simpa [R,h1a] using (hT w1 hw1).2.2.2
  · intro v hv
    change supplier2Profit (R a v).2 v ≤ supplier2Profit (R a b).2 b
    rw [hRbase]
    by_cases hvb : v=b
    · subst v
      simp only [hRbase,le_refl]
    · simpa only [R,if_pos rfl,if_neg hvb] using (hS v hv).2.2.2

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087DOExistenceGeneric -/

namespace NonExclEncroach.Channels

/-- A complete direct-only equilibrium certificate. Every wholesale deviation
is paired with a genuine global reseller optimum, and the base outcome is fixed. -/
theorem P087_DO_equilibrium_generic (t c a b α γ : ℝ)
    (ht0 : 0<t) (ht1 : t<1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hα : 2*α+t*γ=1-c) (hγ : 2*γ+t*α=1-b)
    (hαlo : 2/5 ≤ α) (hγlo : (3/5)*doEll t ≤ γ)
    (hν : 1-α-doS t*γ ≤ 2*α*doBeta t)
    (hbaseX : 1-a-α ≤ doS t*γ)
    (hS2 : b=2*γ ∨
      ((1-a-α)=doS t*γ ∧ b ≤ 2*γ ∧
        (4*doR t-(doS t)^2)*γ ≤ 2*doR t*b)) :
    ∃ σ : Profile, IsEquilibrium t c σ ∧ σ.q1=0 ∧ σ.y=α := by
  obtain ⟨hβ0,hβh,hell0,hr0,hs0,hδ,hη⟩ := P087_DO_coefficient_signs t ht0 ht1
  obtain ⟨hβ,hell,_,_⟩ := P087_DO_coefficient_identities t ht0.le ht1
  have hγ0 : 0 ≤ γ := by nlinarith only [hγlo,hell0]
  have hV : (1-t*α)-b=2*γ := by linarith only [hγ]
  have hsdef : doS t=t*(2-doBeta t) := by unfold doS; nlinarith only [hell]
  have hY0 : P087_globalY t c b 0=α := by
    simpa only [mul_zero,sub_zero] using
      P087_DO_globalY_linear t c b α γ 0 ht0 ht1 hα hγ hαlo hγlo le_rfl (by norm_num)
  have hmatch : ∀ w v x z, 0 ≤ x → x ≤ 3/5 →
      resellerProfit t x z w v (P087_globalY t c b x)=
        P087_retailQuadratic (doR t) (doS t) (1-w-α) ((1-t*α)-v) x z := by
    intro w v x z hx hxh
    rw [P087_DO_globalY_linear t c b α γ x ht0 ht1 hα hγ hαlo hγlo hx hxh]
    rw [hsdef]
    unfold resellerProfit p1 p2 P087_retailQuadratic doR
    ring
  have hbaseQ : ∀ x z, 0 ≤ x → 0 ≤ z →
      P087_retailQuadratic (doR t) (doS t) (1-a-α) ((1-t*α)-b) x z ≤
        P087_retailQuadratic (doR t) (doS t) (1-a-α) ((1-t*α)-b) 0 γ := by
    apply P087_retailQuadratic_max_of_complementarity _ _ _ _ _ _ hδ
    · simpa only [mul_zero,zero_add] using hbaseX
    · linarith only [hV]
    · ring
    · rw [hV]
      ring
  have hbase : ∀ x z, 0 ≤ x → 0 ≤ z →
      resellerProfit t x z a b (P087_globalY t c b x) ≤
        resellerProfit t 0 γ a b (P087_globalY t c b 0) := by
    obtain ⟨X,Z,hX,hZ,hXh,hxo,hzo,hxc,hzc,hmax⟩ :=
      P087_DO_model_response_exists t c b α γ a b ht0 ht1 ha hα hγ hαlo hγlo
    have hdom : resellerProfit t X Z a b (P087_globalY t c b X) ≤
        resellerProfit t 0 γ a b (P087_globalY t c b 0) := by
      rw [hmatch a b X Z hX hXh,hmatch a b 0 γ le_rfl (by norm_num)]
      exact hbaseQ X Z hX hZ
    exact fun x z hx hz => (hmax x z hx hz).trans hdom
  have hbaseProfit : supplier1Profit t c 0 γ a (P087_globalY t c b 0)=α^2 := by
    rw [hY0]
    unfold supplier1Profit pd
    linear_combination -α*hα
  have hsupplier1 : ∀ w, 0 ≤ w → ∃ x z, 0 ≤ x ∧ 0 ≤ z ∧
      (∀ x' z', 0 ≤ x' → 0 ≤ z' →
        resellerProfit t x' z' w b (P087_globalY t c b x') ≤
          resellerProfit t x z w b (P087_globalY t c b x)) ∧
      supplier1Profit t c x z w (P087_globalY t c b x) ≤
        supplier1Profit t c 0 γ a (P087_globalY t c b 0) := by
    intro w hw
    obtain ⟨x,z,hx,hz,hxh,hxo,hzo,hxc,hzc,hmax⟩ :=
      P087_DO_model_response_exists t c b α γ w b ht0 ht1 hw hα hγ hαlo hγlo
    have hzlin0 : 0 ≤ γ-doEll t*x := by
      have hh := mul_nonneg hell0.le (show 0 ≤ 3/5-x by linarith)
      nlinarith only [hh,hγlo]
    have hzlin : z=γ-doEll t*x := by
      by_cases hz0 : z=0
      · rw [hz0] at hzo
        rw [hV] at hzo
        unfold doS at hzo
        nlinarith only [hzo,hzlin0,hz0]
      · have hzeq := sub_eq_zero.mp ((mul_eq_zero.mp hzc).resolve_left hz0)
        rw [hV] at hzeq
        unfold doS at hzeq
        nlinarith only [hzeq]
    have hyz : 2*(α-doBeta t*x)+t*z=1-c-x := by
      rw [hzlin]
      linear_combination hα-x*hβ
    refine ⟨x,z,hx,hz,hmax,?_⟩
    rw [P087_DO_globalY_linear t c b α γ x ht0 ht1 hα hγ hαlo hγlo hx hxh,hbaseProfit]
    exact P087_DO_supplier1_bound t c w α (doBeta t) γ (doEll t) (doR t) (doS t) x z
      hx hyz hzlin rfl hν hη.le hxc
  have hsupplier2 : ∀ v, 0 ≤ v → ∃ x z, 0 ≤ x ∧ 0 ≤ z ∧
      (∀ x' z', 0 ≤ x' → 0 ≤ z' →
        resellerProfit t x' z' a v (P087_globalY t c b x') ≤
          resellerProfit t x z a v (P087_globalY t c b x)) ∧
      supplier2Profit z v ≤ supplier2Profit γ b := by
    intro v hv
    obtain ⟨x,z,hx,hz,hxh,hxo,hzo,hxc,hzc,hmax⟩ :=
      P087_DO_model_response_exists t c b α γ a v ht0 ht1 ha hα hγ hαlo hγlo
    refine ⟨x,z,hx,hz,hmax,?_⟩
    have hbound : supplier2Profit z v ≤ b*γ := by
      rcases hS2 with hDO | ⟨hkink,hleft,hright⟩
      · exact P087_DO_supplier2_bound (doS t) (1-t*α) b γ v x z hs0.le hx hz hv hDO hV hzc
      · exact P087_DOB_supplier2_bound (doR t) (doS t) (1-a-α) (1-t*α) b γ v x z
          hr0 hs0 hδ hb hγ0 hx hz hV hkink hleft hright hxo hxc hzc
    simpa only [supplier2Profit,mul_comm] using hbound
  obtain ⟨σ,hEq,hw1,hw2,hq1,hq2,hy⟩ :=
    P087_equilibrium_of_selected_certificates t c a b 0 γ
      (P087_globalY t c b) (P087_globalQ t c b) ht0.le ha hb
      (P087_globalY_continuous t c b) (P087_globalY_nonneg t c b)
      (fun x _ => P087_global_stageIII t c b x ht0.le ht1)
      le_rfl hγ0 hbase hsupplier1 hsupplier2
  exact ⟨σ,hEq,hq1,hy.trans hY0⟩

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087DOParameterIdentities -/

namespace NonExclEncroach.Channels

noncomputable def doAlpha (t c : ℝ) : ℝ := (4-t-4*c)/(8-t^2)
noncomputable def doGamma (t c : ℝ) : ℝ := (2-t+t*c)/(8-t^2)
noncomputable def doB (t c : ℝ) : ℝ := 2*doGamma t c
noncomputable def dobAlpha (t c : ℝ) : ℝ := (2+t^2-6*c)/(4+5*t^2)
noncomputable def dobGamma (t c : ℝ) : ℝ := (3*t^2+c*(8-5*t^2))/(t*(4+5*t^2))
noncomputable def dobB (t c : ℝ) : ℝ := 1-2*dobGamma t c-t*dobAlpha t c

/-- Denominator-cleared equations for the two direct-only candidates. -/
theorem P087_DO_parameter_identities (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    2*doAlpha t c+t*doGamma t c=1-c ∧
    2*doGamma t c+t*doAlpha t c=1-doB t c ∧
    (4-t^2)*(8-t^2)*(1-doAlpha t c-doS t*doGamma t c-
      2*doAlpha t c*doBeta t) =
      (32-26*t^2)*c-(4*t-14*t^2+5*t^3-t^4) := by
  have ht2 : t^2 < 1 := by nlinarith [sq_nonneg (t-1)]
  have hD : 4-t^2 ≠ 0 := by linarith
  have hE : 8-t^2 ≠ 0 := by linarith
  dsimp only [doAlpha, doGamma, doB, doS, doEll, doBeta]
  constructor
  · field_simp [hE]
    ring
  constructor
  · field_simp [hE]
    ring
  · field_simp [hD, hE]
    ring

theorem P087_DOB_parameter_identities (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    2*dobAlpha t c+t*dobGamma t c=1-c ∧
    2*dobGamma t c+t*dobAlpha t c=1-dobB t c ∧
    1-dobAlpha t c-doS t*dobGamma t c=2*dobAlpha t c*doBeta t ∧
    dobB t c = (1-t)*(4*t-4*t^2+t^3-16*c*(1+t))/(t*(4+5*t^2)) ∧
    t*(4+5*t^2)*(2*dobGamma t c-dobB t c)=
      (32-26*t^2)*c-(4*t-14*t^2+5*t^3-t^4) ∧
    t*(4-t^2)^2*(4+5*t^2)*
      (2*doR t*dobB t c-(4*doR t-(doS t)^2)*dobGamma t c)=
      2*(1-t)*((32*t-80*t^2-32*t^3-14*t^4-8*t^5+4*t^6-t^7)-
        2*(1+t)*(128-16*t^2-13*t^4)*c) := by
  have ht2 : t^2 < 1 := by nlinarith [sq_nonneg (t-1)]
  have hD : 4-t^2 ≠ 0 := by linarith
  have hF : 4+5*t^2 ≠ 0 := by positivity
  have ht : t ≠ 0 := ne_of_gt ht0
  dsimp only [dobAlpha, dobGamma, dobB, doS, doEll, doBeta, doR]
  constructor
  · field_simp [ht, hF]
    ring
  constructor
  · ring
  constructor
  · field_simp [ht, hF, hD]
    ring
  constructor
  · field_simp [ht, hF]
    ring
  constructor
  · field_simp [ht, hF]
    ring
  · field_simp [ht, hF, hD]
    ring

theorem P087_DO_DOB_price_difference (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    t*(8-t^2)*(4+5*t^2)*(doB t c-dobB t c)=
      (4-t^2)*((32-26*t^2)*c-(4*t-14*t^2+5*t^3-t^4)) := by
  have ht2 : t^2 < 1 := by nlinarith [sq_nonneg (t-1)]
  have hE : 8-t^2 ≠ 0 := by linarith
  have hF : 4+5*t^2 ≠ 0 := by positivity
  have ht : t ≠ 0 := ne_of_gt ht0
  dsimp only [doB, doGamma, dobB, dobAlpha, dobGamma]
  field_simp [ht, hE, hF]
  ring

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087DOCostBounds -/

namespace NonExclEncroach.Channels

/-- Two coarse uniform bounds on the positive-cost threshold. -/
theorem P087_c2_cost_bounds (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    c2 t ≤ 1/50 ∧ c2 t ≤ t/8 := by
  have h2 : t^2 ≤ 1 := pow_le_one₀ ht0 ht1
  have h4 : t^4 ≤ 1 := pow_le_one₀ ht0 ht1
  have h64 : t^6 ≤ t^4 := by
    calc
      t^6 = t^4*t^2 := by ring
      _ ≤ t^4*1 := mul_le_mul_of_nonneg_left h2 (pow_nonneg ht0 4)
      _ = t^4 := by ring
  let H := 128-16*t^2-13*t^4
  let den := 2*(1+t)*H
  let N := 32*t-80*t^2-32*t^3-14*t^4-8*t^5+4*t^6-t^7
  have hH : 99 ≤ H := by dsimp [H]; linarith
  have hH0 : 0 ≤ H := by linarith
  have hden : 198 ≤ den := by dsimp [den]; nlinarith [mul_nonneg ht0 hH0]
  have hden0 : 0 < den := by linarith
  have hN : N ≤ 16/5 := by
    dsimp [N]
    nlinarith [sq_nonneg (t-1/5), pow_nonneg ht0 3, pow_nonneg ht0 4,
      pow_nonneg ht0 5, pow_nonneg ht0 7]
  have hP : 0 ≤ 4*t^5-29*t^4+19*t^3+40*t^2+112*t+448 := by
    nlinarith [pow_nonneg ht0 2, pow_nonneg ht0 3, pow_nonneg ht0 5]
  have hcert := mul_nonneg (sq_nonneg t) hP
  have hid : 4*(t/8*den-N) =
      t^2*(4*t^5-29*t^4+19*t^3+40*t^2+112*t+448) := by
    dsimp [den, H, N]
    ring
  change N/den ≤ 1/50 ∧ N/den ≤ t/8
  constructor
  · apply (div_le_iff₀ hden0).mpr
    linarith
  · apply (div_le_iff₀ hden0).mpr
    nlinarith only [hid, hcert]

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087DOParameters -/

namespace NonExclEncroach.Channels

private theorem P087_doB_box (t c : ℝ) (ht0 : 0 < t) (htu : t ≤ 7/20)
    (hc0 : 0 ≤ c) (hcu : c ≤ 1/50) : 0 ≤ doB t c ∧ doB t c ≤ 1/2 := by
  have ht2 : t^2 < 1 := by nlinarith [sq_nonneg (t-1)]
  have hE : 0 < 8-t^2 := by linarith
  have hN : 0 ≤ 2-t+t*c := by nlinarith [mul_nonneg ht0.le hc0]
  constructor
  · exact mul_nonneg (by norm_num) (div_nonneg hN hE.le)
  · unfold doB doGamma
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hE).mpr
    have hh := mul_nonneg ht0.le (show 0 ≤ 4-t-4*c by linarith)
    nlinarith only [hh]

/-- Direct-only monopoly parameters in the lower positive-cost subregime. -/
theorem P087_DO_parameters (t c : ℝ) (ht0 : 0 < t) (htu : t ≤ 7/20)
    (hc0 : 0 < c) (hc2 : c ≤ c2 t) (hc1 : c ≤ c1 t) :
    0 ≤ doB t c ∧ doB t c ≤ 1/2 ∧
    2*doAlpha t c+t*doGamma t c=1-c ∧
    2*doGamma t c+t*doAlpha t c=1-doB t c ∧
    2/5 ≤ doAlpha t c ∧ (3/5)*doEll t ≤ doGamma t c ∧
    1-doAlpha t c-doS t*doGamma t c ≤ 2*doAlpha t c*doBeta t := by
  have ht1 : t < 1 := by linarith
  have hcost := P087_c2_cost_bounds t ht0.le ht1.le
  have hcu : c ≤ 1/50 := hc2.trans hcost.1
  obtain ⟨hb0,hbu⟩ := P087_doB_box t c ht0 htu hc0.le hcu
  obtain ⟨hα,hγ,hν⟩ := P087_DO_parameter_identities t c ht0 ht1
  obtain ⟨hαlo,hγlo⟩ := P087_DO_intercept_box t c (doB t c) (doAlpha t c) (doGamma t c)
    ht0.le htu hc0.le hcu hb0 hbu hα hγ
  have ht2 : t^2 < 1 := by nlinarith [sq_nonneg (t-1)]
  have hH : 0 < 32-26*t^2 := by linarith
  have hD : 0 < 4-t^2 := by linarith
  have hE : 0 < 8-t^2 := by linarith
  have hc : (32-26*t^2)*c ≤ 4*t-14*t^2+5*t^3-t^4 := by
    unfold c1 at hc1
    have hh := (le_div_iff₀ hH).mp hc1
    nlinarith only [hh]
  have hνle : 1-doAlpha t c-doS t*doGamma t c-2*doAlpha t c*doBeta t ≤ 0 := by
    apply nonpos_of_mul_nonpos_right (a := (4-t^2)*(8-t^2))
    · rw [hν]
      linarith only [hc]
    · exact mul_pos hD hE
  exact ⟨hb0,hbu,hα,hγ,hαlo,hγlo,by linarith only [hνle]⟩

/-- Boundary direct-only parameters in the upper positive-cost subregime. -/
theorem P087_DOB_parameters (t c : ℝ) (ht0 : 0 < t) (htu : t ≤ 7/20)
    (hc0 : 0 < c) (hc2 : c ≤ c2 t) (hc1 : c1 t ≤ c) :
    0 ≤ dobB t c ∧ dobB t c ≤ 1/2 ∧
    2*dobAlpha t c+t*dobGamma t c=1-c ∧
    2*dobGamma t c+t*dobAlpha t c=1-dobB t c ∧
    2/5 ≤ dobAlpha t c ∧ (3/5)*doEll t ≤ dobGamma t c ∧
    1-dobAlpha t c-doS t*dobGamma t c=2*dobAlpha t c*doBeta t ∧
    dobB t c ≤ 2*dobGamma t c ∧
    (4*doR t-(doS t)^2)*dobGamma t c ≤ 2*doR t*dobB t c := by
  have ht1 : t < 1 := by linarith
  have hcost := P087_c2_cost_bounds t ht0.le ht1.le
  have hcu : c ≤ 1/50 := hc2.trans hcost.1
  have hct : c ≤ t/8 := hc2.trans hcost.2
  have ht2 : t^2 < 1 := by nlinarith [sq_nonneg (t-1)]
  have hH : 0 < 32-26*t^2 := by linarith
  have hD : 0 < 4-t^2 := by linarith
  have hE : 0 < 8-t^2 := by linarith
  have hF : 0 < 4+5*t^2 := by positivity
  obtain ⟨hα,hγ,hν,hbformula,hleft,hright⟩ := P087_DOB_parameter_identities t c ht0 ht1
  have hcleared : 0 ≤ (32-26*t^2)*c-(4*t-14*t^2+5*t^3-t^4) := by
    unfold c1 at hc1
    have hh := (div_le_iff₀ hH).mp hc1
    nlinarith only [hh]
  have hb0 : 0 ≤ dobB t c := by
    have hf : 0 ≤ 2-6*t+t^2 := by nlinarith [sq_nonneg (t-7/20)]
    have hn : 0 ≤ 4*t-4*t^2+t^3-16*c*(1+t) := by
      have hfirst := mul_nonneg ht0.le hf
      have hsecond := mul_nonneg (show 0 ≤ t/8-c by linarith) (show 0 ≤ 16*(1+t) by linarith)
      nlinarith only [hfirst,hsecond]
    rw [hbformula]
    exact div_nonneg (mul_nonneg (by linarith) hn) (mul_nonneg ht0.le hF.le)
  have hbu : dobB t c ≤ 1/2 := by
    have hdiff := P087_DO_DOB_price_difference t c ht0 ht1
    have hh : 0 ≤ doB t c-dobB t c := by
      apply nonneg_of_mul_nonneg_right (a := t*(8-t^2)*(4+5*t^2))
      · rw [hdiff]
        exact mul_nonneg hD.le hcleared
      · exact mul_pos (mul_pos ht0 hE) hF
    have hdo := (P087_doB_box t c ht0 htu hc0.le hcu).2
    linarith only [hh,hdo]
  obtain ⟨hαlo,hγlo⟩ := P087_DO_intercept_box t c (dobB t c) (dobAlpha t c) (dobGamma t c)
    ht0.le htu hc0.le hcu hb0 hbu hα hγ
  have hleft' : dobB t c ≤ 2*dobGamma t c := by
    have hh : 0 ≤ 2*dobGamma t c-dobB t c := by
      apply nonneg_of_mul_nonneg_right (a := t*(4+5*t^2))
      · rwa [hleft]
      · exact mul_pos ht0 hF
    linarith only [hh]
  have hright' : (4*doR t-(doS t)^2)*dobGamma t c ≤ 2*doR t*dobB t c := by
    have ht4 : t^4 ≤ 1 := pow_le_one₀ ht0.le ht1.le
    have hden : 0 < 2*(1+t)*(128-16*t^2-13*t^4) := by
      have hh : 0 < 128-16*t^2-13*t^4 := by linarith
      positivity
    have hcostgap : 0 ≤ (32*t-80*t^2-32*t^3-14*t^4-8*t^5+4*t^6-t^7)-
        2*(1+t)*(128-16*t^2-13*t^4)*c := by
      unfold c2 at hc2
      have hh := (le_div_iff₀ hden).mp hc2
      nlinarith only [hh]
    have hh : 0 ≤ 2*doR t*dobB t c-(4*doR t-(doS t)^2)*dobGamma t c := by
      apply nonneg_of_mul_nonneg_right (a := t*(4-t^2)^2*(4+5*t^2))
      · rw [hright]
        exact mul_nonneg (by linarith) hcostgap
      · positivity
    linarith only [hh]
  exact ⟨hb0,hbu,hα,hγ,hαlo,hγlo,hν,hleft',hright'⟩

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087DOExistence -/

namespace NonExclEncroach.Channels

/-- Full direct-only equilibrium existence on the positive-cost branch of the
original proposition, with the exact model and all nonnegative wholesale deviations. -/
theorem P087_DO_equilibrium_exists (t c : ℝ)
    (ht0 : 0<t) (htu : t ≤ 7/20) (hc0 : 0<c) (hc2 : c ≤ c2 t) :
    ∃ σ : Profile, IsEquilibrium t c σ ∧ σ.q1=0 ∧ 0<σ.y := by
  have ht1 : t<1 := by linarith
  obtain ⟨hβ0,hβu,hell0,hr0,hs0,hδ,hη⟩ := P087_DO_coefficient_signs t ht0 ht1
  by_cases hc1 : c ≤ c1 t
  · obtain ⟨hb0,hbu,hα,hγ,hαlo,hγlo,hν⟩ :=
      P087_DO_parameters t c ht0 htu hc0 hc2 hc1
    have hγ0 : 0 ≤ doGamma t c := by nlinarith only [hγlo,hell0]
    have hbase : 1-1-doAlpha t c ≤ doS t*doGamma t c := by
      nlinarith only [hαlo,mul_nonneg hs0.le hγ0]
    obtain ⟨σ,hEq,hq,hy⟩ := P087_DO_equilibrium_generic t c 1 (doB t c)
      (doAlpha t c) (doGamma t c) ht0 ht1 (by norm_num) hb0 hα hγ hαlo hγlo hν
      hbase (Or.inl rfl)
    refine ⟨σ,hEq,hq,?_⟩
    rw [hy]
    linarith only [hαlo]
  · have hc1' : c1 t ≤ c := le_of_lt (lt_of_not_ge hc1)
    obtain ⟨hb0,hbu,hα,hγ,hαlo,hγlo,hν,hleft,hright⟩ :=
      P087_DOB_parameters t c ht0 htu hc0 hc2 hc1'
    have hα0 : 0 ≤ dobAlpha t c := by linarith only [hαlo]
    let a := 2*dobAlpha t c*doBeta t
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hbase : 1-a-dobAlpha t c=doS t*dobGamma t c := by
      dsimp [a]
      linarith only [hν]
    obtain ⟨σ,hEq,hq,hy⟩ := P087_DO_equilibrium_generic t c a (dobB t c)
      (dobAlpha t c) (dobGamma t c) ht0 ht1 ha hb0 hα hγ hαlo hγlo hν.le hbase.le
      (Or.inr ⟨hbase,hleft,hright⟩)
    refine ⟨σ,hEq,hq,?_⟩
    rw [hy]
    linarith only [hαlo]

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087RDParameters -/

set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

namespace NonExclEncroach.Channels

noncomputable section

def rdD (t : ℝ) : ℝ := 4 - t ^ 2
def rdP (t : ℝ) : ℝ := 256 + 2*t^8 - 11*t^6 - 52*t^4 + 48*t^2
def rdF (t c : ℝ) : ℝ := 16 + t*(8 - 3*t^3 - 4*(1+t)*(2-t^2)*c + 4*t)
def rdAlpha (t c : ℝ) : ℝ := (2*(1-c)-t*(1-wRD2 t c))/rdD t
def rdBeta (t : ℝ) : ℝ := 2*(1-t^2)/rdD t
def rdGamma (t c : ℝ) : ℝ := (2*(1-wRD2 t c)-t*(1-c))/rdD t
def rdLambda (t : ℝ) : ℝ := 3*t/rdD t
def rdR (t : ℝ) : ℝ := (2+t^2)/rdD t
def rdS (t : ℝ) : ℝ := 6*t/rdD t
def rdKappa (t : ℝ) : ℝ := (1-t^2)*(8+t^2)/(rdD t)^2
def rdU (t c : ℝ) : ℝ := 1-wRD1 t c-rdAlpha t c
def rdV (t c : ℝ) : ℝ := 1-t*rdAlpha t c
def rdX (t c : ℝ) : ℝ := (rdU t c-rdS t*rdGamma t c)/(2*rdKappa t)
def rdY (t c : ℝ) : ℝ := rdAlpha t c-rdBeta t*rdX t c
def rdZ (t c : ℝ) : ℝ := rdGamma t c-rdLambda t*rdX t c
def rdCutoff (t c : ℝ) : ℝ := rdGamma t c/rdLambda t

theorem rdD_pos (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) : 0 < rdD t := by
  have h2 : t^2 ≤ 1 := pow_le_one₀ ht0 ht1.le
  unfold rdD
  linarith

theorem rdP_pos (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) : 0 < rdP t := by
  have h4 : t^4 ≤ 1 := pow_le_one₀ ht0 ht1.le
  have h6 : t^6 ≤ 1 := pow_le_one₀ ht0 ht1.le
  unfold rdP
  nlinarith [sq_nonneg t, pow_nonneg ht0 8]

theorem rdN_pos (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < 128-16*t^2-13*t^4 := by
  have h2 : t^2 ≤ 1 := pow_le_one₀ ht0 ht1.le
  have h4 : t^4 ≤ 1 := pow_le_one₀ ht0 ht1.le
  nlinarith

theorem rdF_pos (t c : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hc : c ≤ 0) :
    0 < rdF t c := by
  have h2 : t^2 ≤ 1 := pow_le_one₀ ht0 ht1.le
  have h3 : t^3 ≤ 1 := pow_le_one₀ ht0 ht1.le
  have h2p : 0 ≤ 2-t^2 := by linarith
  have hprod : 4*(1+t)*(2-t^2)*c ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
  have hbr : 0 ≤ 8-3*t^3-4*(1+t)*(2-t^2)*c+4*t := by nlinarith
  unfold rdF
  nlinarith [mul_nonneg ht0 hbr]

theorem rdB_pos (t c : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hc : c ≤ 0) :
    0 < wRD2 t c := by
  change 0 < (1-t)*(8+t^2)*rdF t c/rdP t
  exact div_pos (mul_pos (mul_pos (by linarith) (by positivity))
    (rdF_pos t c ht0 ht1 hc)) (rdP_pos t ht0 ht1)

theorem P087_theta_third_of_c2_neg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hc2 : c2 t < 0) : 1/3 < t := by
  by_contra hn
  have ht3 : t ≤ 1/3 := le_of_not_gt hn
  have h2 : t^2 ≤ (1/3:ℝ)^2 := by gcongr
  have h3 : t^3 ≤ (1/3:ℝ)^3 := by gcongr
  have h4 : t^4 ≤ (1/3:ℝ)^4 := by gcongr
  have h6 : t^6 ≤ (1/3:ℝ)^6 := by gcongr
  have hnum : 0 ≤ num1 t := by
    unfold num1
    nlinarith [pow_nonneg ht0 5]
  have hnumer : 0 ≤ 32*t-80*t^2-32*t^3-14*t^4-8*t^5+4*t^6-t^7 := by
    have h := mul_nonneg ht0 hnum
    have heq : t * num1 t = 32*t-80*t^2-32*t^3-14*t^4-8*t^5+4*t^6-t^7 := by
      unfold num1
      ring
    rwa [heq] at h
  have hc2nonneg : 0 ≤ c2 t := by
    unfold c2
    exact div_nonneg hnumer (le_of_lt (mul_pos (by positivity) (rdN_pos t ht0 ht1)))
  linarith

theorem rd_supplier2_stationary (t c : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    2*rdR t*(rdV t c-2*wRD2 t c) = rdS t*rdU t c := by
  let d := 256 + 2*t^8 - 11*t^6 - 52*t^4 + 48*t^2
  let D := 4-t^2
  let aN := 128*(3-c)-t*(128+t*(56+t*(96+t*(90-5*t^4+t^3+34*t^2*c+18*t+6*c))-168*c))
  let bN := (1-t)*(8+t^2)*(16+t*(8-3*t^3-4*(1+t)*(2-t^2)*c+4*t))
  have hD : D ≠ 0 := (rdD_pos t ht0 ht1).ne'
  have hd : d ≠ 0 := (rdP_pos t ht0 ht1).ne'
  change 2*((2+t^2)/D)*(1-t*((2*(1-c)-t*(1-bN/d))/D)-2*(bN/d)) =
    (6*t/D)*(1-aN/(3*d)-(2*(1-c)-t*(1-bN/d))/D)
  field_simp [hd, hD]
  dsimp [d, D, aN, bN]
  ring

end

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087RDCandidate -/

set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

namespace NonExclEncroach.Channels
noncomputable section

def rdEta (t : ℝ) : ℝ := 6*(1-t^2)*(2+t^2)/(rdD t)^2
def rdU0 (t c : ℝ) : ℝ := 1-rdAlpha t c-2*rdGamma t c*rdLambda t
def rdNu (t c : ℝ) : ℝ := rdU0 t c-2*rdAlpha t c*rdBeta t

theorem rd_coefficients (t c : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    2*rdAlpha t c+t*rdGamma t c=1-c ∧
    2*rdGamma t c+t*rdAlpha t c=1-wRD2 t c ∧
    2*rdBeta t+t*rdLambda t=1 ∧
    2*rdLambda t+t*rdBeta t=2*t ∧
    rdKappa t=1-rdBeta t-(rdLambda t)^2 ∧
    rdEta t=2*rdKappa t-(rdBeta t)^2 ∧
    rdR t=1-rdBeta t ∧ rdS t=2*rdLambda t := by
  have hD := (rdD_pos t ht0 ht1).ne'
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals
    dsimp only [rdAlpha,rdGamma,rdBeta,rdLambda,rdKappa,rdEta,rdR,rdS]
    field_simp [hD]
    try dsimp [rdD]
    ring

theorem rd_coefficient_signs (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < rdBeta t ∧ rdBeta t < 1/2 ∧ 0 < rdLambda t ∧
    0 < rdKappa t ∧ 0 < rdEta t ∧ 0 < rdR t ∧ 0 < rdS t := by
  have hD := rdD_pos t ht0.le ht1
  have ht2 : t^2 < 1 := by nlinarith
  have h1t : 0 < 1-t^2 := by linarith
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact div_pos (by positivity) hD
  · unfold rdBeta
    apply (div_lt_iff₀ hD).2
    dsimp [rdD]
    nlinarith [sq_pos_of_pos ht0]
  · exact div_pos (by positivity) hD
  · exact div_pos (by positivity) (sq_pos_of_pos hD)
  · exact div_pos (by positivity) (sq_pos_of_pos hD)
  · exact div_pos (by positivity) hD
  · exact div_pos (by positivity) hD

theorem rd_X_formula (t c : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    rdX t c = rdD t*(128-16*t^2-13*t^4)*(c-c2 t)/(3*rdP t) := by
  let d := 256+2*t^8-11*t^6-52*t^4+48*t^2
  let D := 4-t^2
  let E := 128-16*t^2-13*t^4
  let aN := 128*(3-c)-t*(128+t*(56+t*(96+t*(90-5*t^4+t^3+34*t^2*c+18*t+6*c))-168*c))
  let bN := (1-t)*(8+t^2)*(16+t*(8-3*t^3-4*(1+t)*(2-t^2)*c+4*t))
  let N := 32*t-80*t^2-32*t^3-14*t^4-8*t^5+4*t^6-t^7
  have hD : D ≠ 0 := (rdD_pos t ht0 ht1).ne'
  have hd : d ≠ 0 := (rdP_pos t ht0 ht1).ne'
  have hE : E ≠ 0 := (rdN_pos t ht0 ht1).ne'
  have h1t : 1-t^2 ≠ 0 := by nlinarith
  have h8t : 8+t^2 ≠ 0 := by positivity
  have hpt : 1+t ≠ 0 := by positivity
  change ((1-aN/(3*d)-(2*(1-c)-t*(1-bN/d))/D)-(6*t/D)*
    ((2*(1-bN/d)-t*(1-c))/D))/(2*((1-t^2)*(8+t^2)/D^2)) =
    D*E*(c-N/(2*(1+t)*E))/(3*d)
  field_simp [hD,hd,hE,h1t,h8t,hpt]
  dsimp [D,d,E,N,aN,bN]
  ring

theorem rd_X_pos (t c : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hc : c2 t < c) :
    0 < rdX t c := by
  rw [rd_X_formula t c ht0 ht1]
  exact div_pos (mul_pos (mul_pos (rdD_pos t ht0 ht1) (rdN_pos t ht0 ht1))
    (sub_pos.mpr hc)) (mul_pos (by norm_num) (rdP_pos t ht0 ht1))

theorem rd_supplier1_stationary (t c : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    rdNu t c = 2*rdEta t*rdX t c := by
  rw [rd_X_formula t c ht0 ht1]
  let d := 256+2*t^8-11*t^6-52*t^4+48*t^2
  let D := 4-t^2
  let E := 128-16*t^2-13*t^4
  let bN := (1-t)*(8+t^2)*(16+t*(8-3*t^3-4*(1+t)*(2-t^2)*c+4*t))
  let N := 32*t-80*t^2-32*t^3-14*t^4-8*t^5+4*t^6-t^7
  have hD : D ≠ 0 := (rdD_pos t ht0 ht1).ne'
  have hd : d ≠ 0 := (rdP_pos t ht0 ht1).ne'
  have hE : E ≠ 0 := (rdN_pos t ht0 ht1).ne'
  have hpt : 1+t ≠ 0 := by positivity
  change 1-(2*(1-c)-t*(1-bN/d))/D-2*((2*(1-bN/d)-t*(1-c))/D)*(3*t/D)-
    2*((2*(1-c)-t*(1-bN/d))/D)*(2*(1-t^2)/D) =
    2*(6*(1-t^2)*(2+t^2)/D^2)*(D*E*(c-N/(2*(1+t)*E))/(3*d))
  field_simp [hD,hd,hE,hpt]
  dsimp [D,d,E,N,bN]
  ring

end
end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087RDFeasible -/

set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

namespace NonExclEncroach.Channels
noncomputable section

theorem rd_X_relation (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    2*rdKappa t*rdX t c = rdU t c-rdS t*rdGamma t c := by
  have hk := (rd_coefficient_signs t ht0 ht1).2.2.2.1
  unfold rdX
  field_simp [ne_of_gt hk]

theorem rd_Z_relation (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    2*rdKappa t*rdZ t c=rdR t*wRD2 t c := by
  obtain ⟨hA,hB,hsA,hsB,hκ,hη,hr,hs⟩ := rd_coefficients t c ht0.le ht1
  have hV : rdV t c=2*rdGamma t c+wRD2 t c := by dsimp [rdV]; linarith
  have hstat := rd_supplier2_stationary t c ht0.le ht1
  rw [hV,hs] at hstat
  have hx := rd_X_relation t c ht0 ht1
  rw [hs] at hx
  have hkr : rdKappa t+(rdLambda t)^2=rdR t := by linarith
  dsimp only [rdZ]
  nlinarith only [hstat,congrArg (fun z : ℝ => rdLambda t*z) hx,
    congrArg (fun z : ℝ => 2*rdGamma t c*z) hkr]

theorem rd_Z_pos (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hc : c ≤ 0) :
    0 < rdZ t c := by
  obtain ⟨hβ,hβh,hell,hκ,hη,hr,hs⟩ := rd_coefficient_signs t ht0 ht1
  have hp : 0 < 2*rdKappa t*rdZ t c := by
    rw [rd_Z_relation t c ht0 ht1]
    exact mul_pos hr (rdB_pos t c ht0.le ht1 hc)
  rcases mul_pos_iff.mp hp with ⟨_,h⟩|⟨h,_⟩
  · exact h
  · linarith

theorem rd_cutoff_relation (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    rdGamma t c=rdLambda t*rdCutoff t c := by
  have hl := (rd_coefficient_signs t ht0 ht1).2.2.1
  unfold rdCutoff
  field_simp [ne_of_gt hl]

theorem rd_X_lt_cutoff (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hc : c ≤ 0) :
    rdX t c < rdCutoff t c := by
  have hl := (rd_coefficient_signs t ht0 ht1).2.2.1
  have hz := rd_Z_pos t c ht0 ht1 hc
  dsimp only [rdZ] at hz
  unfold rdCutoff
  apply (lt_div_iff₀ hl).2
  nlinarith only [hz]

theorem rd_cutoff_pos (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hc2 : c2 t < c) (hc : c ≤ 0) : 0 < rdCutoff t c :=
  lt_trans (rd_X_pos t c ht0.le ht1 hc2) (rd_X_lt_cutoff t c ht0 ht1 hc)

theorem rd_b_small_theta (t c : ℝ) (ht3 : 1/3 < t) (ht2 : t ≤ 1/2) (hc : c ≤ 0) :
    (1-t)/2 ≤ wRD2 t c := by
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t < 1 := by linarith
  have ht2p : t^2 ≤ (1/2:ℝ)^2 := by gcongr
  have ht3p : t^3 ≤ (1/2:ℝ)^3 := by gcongr
  have ht8p : t^8 ≤ (1/2:ℝ)^8 := by gcongr
  have h2pos : 0 ≤ 2-t^2 := by nlinarith
  have hpc : 4*(1+t)*(2-t^2)*c ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
  have hbr : 6 ≤ 8-3*t^3-4*(1+t)*(2-t^2)*c+4*t := by nlinarith
  have hF : 18 ≤ rdF t c := by
    unfold rdF
    nlinarith only [mul_nonneg ht0 (sub_nonneg.mpr hbr),ht3]
  have hP : rdP t ≤ 270 := by
    unfold rdP
    nlinarith [pow_nonneg ht0 4,pow_nonneg ht0 6]
  have hF0 : 0 ≤ rdF t c := by linarith
  have hbase : rdP t/2 ≤ (8+t^2)*rdF t c := by
    nlinarith only [hP,hF,mul_nonneg (sq_nonneg t) hF0]
  change (1-t)/2 ≤ (1-t)*(8+t^2)*rdF t c/rdP t
  apply (le_div_iff₀ (rdP_pos t ht0 ht1)).2
  have hm := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 1-t by linarith)
  nlinarith only [hm]

theorem rd_cutoff_lt_A (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hc2 : c2 t < c) (hc : c < 0) : rdCutoff t c < 1-c := by
  have ht3 := P087_theta_third_of_c2_neg t ht0.le ht1 (lt_trans hc2 hc)
  have hb := rdB_pos t c ht0.le ht1 hc.le
  have htc := mul_nonpos_of_nonneg_of_nonpos ht0.le hc.le
  have hmargin : 0 < 2*t*(1-c)-1+wRD2 t c := by
    by_cases ht2 : t ≤ 1/2
    · have hbl := rd_b_small_theta t c ht3 ht2 hc.le
      nlinarith only [hbl,ht3,htc]
    · have ht2' : 1/2 < t := lt_of_not_ge ht2
      nlinarith only [ht2',hb,htc]
  have hD := (rdD_pos t ht0.le ht1).ne'
  have hform : rdCutoff t c=(2*(1-wRD2 t c)-t*(1-c))/(3*t) := by
    unfold rdCutoff rdGamma rdLambda
    field_simp [hD,ne_of_gt ht0]
  rw [hform]
  apply (div_lt_iff₀ (show 0 < 3*t by positivity)).2
  nlinarith only [hmargin]

theorem rd_Y_pos (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hc2 : c2 t < c) (hc : c < 0) : 0 < rdY t c := by
  obtain ⟨hA,hB,hsA,hsB,hκ,hη,hr,hs⟩ := rd_coefficients t c ht0.le ht1
  have hβ := (rd_coefficient_signs t ht0 ht1).1
  have hg := rd_cutoff_relation t c ht0 ht1
  have hkA := rd_cutoff_lt_A t c ht0 ht1 hc2 hc
  have hxk := rd_X_lt_cutoff t c ht0 ht1 hc.le
  have hcut : 2*(rdAlpha t c-rdBeta t*rdCutoff t c)=1-c-rdCutoff t c := by
    nlinarith only [hA,congrArg (fun z : ℝ => rdCutoff t c*z) hsA,
      congrArg (fun z : ℝ => t*z) hg]
  dsimp only [rdY]
  nlinarith only [hcut,hkA,mul_pos hβ (sub_pos.mpr hxk)]

theorem rd_A_stationary (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    wRD1 t c=2*rdBeta t*rdY t c+2*rdKappa t*rdX t c := by
  have hx := rd_X_relation t c ht0 ht1
  have hs := (rd_coefficients t c ht0.le ht1).2.2.2.2.2.2.2
  have hη := (rd_coefficients t c ht0.le ht1).2.2.2.2.2.1
  have hstation := rd_supplier1_stationary t c ht0.le ht1
  dsimp only [rdU,rdNu,rdU0] at hx hstation
  rw [hs] at hx
  dsimp only [rdY]
  nlinarith only [hx,hstation,congrArg (fun z : ℝ => rdX t c*z) hη]

theorem rd_A_pos (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hc2 : c2 t < c) (hc : c < 0) : 0 < wRD1 t c := by
  rw [rd_A_stationary t c ht0 ht1]
  obtain ⟨hβ,hβh,hell,hκ,hη,hr,hs⟩ := rd_coefficient_signs t ht0 ht1
  have hx := rd_X_pos t c ht0.le ht1 hc2
  have hy := rd_Y_pos t c ht0 ht1 hc2 hc
  positivity

end
end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087SupplierCertificates -/

namespace NonExclEncroach.Channels

def P087_rdGapAtZeroPolynomial (t : ℝ) : ℝ :=
  -6*t ^ 14 + 12*t ^ 13 - 86*t ^ 12 - 4*t ^ 11 - 343*t ^ 10 + 2120*t ^ 9 + 1472*t ^ 8 + 4352*t ^ 7 - 6720*t ^ 6 - 15872*t ^ 5 - 28160*t ^ 4 - 29696*t ^ 3 + 4096*t ^ 2 + 4096*t + 45056

theorem P087_rdGapAtZeroPolynomial_pos (t : ℝ) (ht : 0 < t) (hupper : t ≤ 9 / 10) :
    0 < P087_rdGapAtZeroPolynomial t := by
  have hbase : 0 ≤ 9 - 10 * t := by linarith
  calc
    0 < (45056 * (9 - 10 * t) ^ 14 +
        6344704 * t ^ 1 * (9 - 10 * t) ^ 13 +
        415133696 * t ^ 2 * (9 - 10 * t) ^ 12 +
        16706087936 * t ^ 3 * (9 - 10 * t) ^ 11 +
        461177305600 * t ^ 4 * (9 - 10 * t) ^ 10 +
        9218300406272 * t ^ 5 * (9 - 10 * t) ^ 9 +
        137198541120960 * t ^ 6 * (9 - 10 * t) ^ 8 +
        1538607704978688 * t ^ 7 * (9 - 10 * t) ^ 7 +
        12994111320641472 * t ^ 8 * (9 - 10 * t) ^ 6 +
        81584165193720200 * t ^ 9 * (9 - 10 * t) ^ 5 +
        370106952166032457 * t ^ 10 * (9 - 10 * t) ^ 4 +
        1150152444213499844 * t ^ 11 * (9 - 10 * t) ^ 3 +
        2207824025111383754 * t ^ 12 * (9 - 10 * t) ^ 2 +
        2046614524754689828 * t ^ 13 * (9 - 10 * t) ^ 1 +
        238552322257067114 * t ^ 14) / 22876792454961 := by positivity
    _ = P087_rdGapAtZeroPolynomial t := by unfold P087_rdGapAtZeroPolynomial; ring

def P087_rdGapCurvaturePolynomial (t : ℝ) : ℝ :=
  12*t ^ 14 + 140*t ^ 12 - 101*t ^ 10 - 5648*t ^ 8 + 19392*t ^ 6 - 3328*t ^ 4 - 56320*t ^ 2 + 65536

theorem P087_rdGapCurvaturePolynomial_pos (t : ℝ) (ht : 0 < t) (hupper : t ≤ 9 / 10) :
    0 < P087_rdGapCurvaturePolynomial t := by
  have hbase : 0 ≤ 9 - 10 * t := by linarith
  calc
    0 < (65536 * (9 - 10 * t) ^ 14 +
        9175040 * t ^ 1 * (9 - 10 * t) ^ 13 +
        591815680 * t ^ 2 * (9 - 10 * t) ^ 12 +
        23307673600 * t ^ 3 * (9 - 10 * t) ^ 11 +
        625884852992 * t ^ 4 * (9 - 10 * t) ^ 10 +
        12114501299200 * t ^ 5 * (9 - 10 * t) ^ 9 +
        174135152167872 * t ^ 6 * (9 - 10 * t) ^ 8 +
        1886095711349760 * t ^ 7 * (9 - 10 * t) ^ 7 +
        15448006046161392 * t ^ 8 * (9 - 10 * t) ^ 6 +
        95084955142419520 * t ^ 9 * (9 - 10 * t) ^ 5 +
        432463917044863499 * t ^ 10 * (9 - 10 * t) ^ 4 +
        1408521287870059960 * t ^ 11 * (9 - 10 * t) ^ 3 +
        3106570031385206740 * t ^ 12 * (9 - 10 * t) ^ 2 +
        4160347643439342800 * t ^ 13 * (9 - 10 * t) ^ 1 +
        2561479309767183532 * t ^ 14) / 22876792454961 := by positivity
    _ = P087_rdGapCurvaturePolynomial t := by unfold P087_rdGapCurvaturePolynomial; ring

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087SupplierDominance -/

namespace NonExclEncroach.Channels

/-- A concave quadratic is nonnegative between two nonnegative endpoint values. -/
theorem P087_quadratic_nonneg_between
    (A B C T z : ℝ) (hA : A ≤ 0) (hC : 0 ≤ C) (hT : 0 < T)
    (hTop : 0 ≤ A * T ^ 2 + B * T + C) (hz : 0 ≤ z) (hzT : z ≤ T) :
    0 ≤ A * z ^ 2 + B * z + C := by
  have h₁ := mul_nonneg (sub_nonneg.mpr hzT) hC
  have h₂ := mul_nonneg hz hTop
  have h₃ := mul_nonneg
    (mul_nonneg (mul_nonneg (neg_nonneg.mpr hA) hT.le) hz) (sub_nonneg.mpr hzT)
  have hscaled : 0 ≤ T * (A * z ^ 2 + B * z + C) := by
    nlinarith only [h₁, h₂, h₃]
  exact nonneg_of_mul_nonneg_right hscaled hT

/-- Same-quantity domination of a later quadratic retailer branch by the first
branch. The two branches agree at the cutoff `k`. The comparison is uniform
in the other ordered quantity `z` and in the common wholesale-price term.
The application to the original R&D formulas requires the listed parameter
inequalities; this helper does not assume those checks have been performed. -/
theorem P087_two_branch_dominance
    (r u₀ s₀ V₀ u₁ s₁ V₁ k z x : ℝ)
    (hr : 0 < r) (hs₀ : 0 ≤ s₀) (hs₁ : 0 < s₁) (hk : 0 ≤ k)
    (hz : 0 ≤ z) (hx : k ≤ x)
    (hcut : u₀ ≤ 2 * r * k)
    (hratio : s₀ * u₁ ≤ s₁ * u₀)
    (hgap : 2 * r * u₁ ^ 2 ≤ u₀ ^ 2)
    (hconcave : s₀ ^ 2 ≤ 2 * r * s₁ ^ 2)
    (hcont₀ : u₀ * k - r * k ^ 2 = u₁ * k - k ^ 2 / 2)
    (hcont₁ : V₀ - s₀ * k = V₁ - s₁ * k) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ k ∧
      u₁ * x - x ^ 2 / 2 - s₁ * x * z + V₁ * z - z ^ 2 ≤
        u₀ * w - r * w ^ 2 - s₀ * w * z + V₀ * z - z ^ 2 := by
  have hcont (t : ℝ) :
      u₀ * k - r * k ^ 2 - s₀ * k * t + V₀ * t =
        u₁ * k - k ^ 2 / 2 - s₁ * k * t + V₁ * t := by
    have h := congrArg (fun a : ℝ => a * t) hcont₁
    nlinarith only [hcont₀, h]
  by_cases hvertex : u₁ - s₁ * z ≤ k
  · refine ⟨k, hk, le_rfl, ?_⟩
    have hprod := mul_nonneg (sub_nonneg.mpr hx)
      (show 0 ≤ (x + k) / 2 - (u₁ - s₁ * z) by linarith)
    have hc := hcont z
    nlinarith only [hprod, hc]
  · have hvertex' : k < u₁ - s₁ * z := lt_of_not_ge hvertex
    let T := (u₁ - k) / s₁
    have hTpos : 0 < T := by
      apply div_pos _ hs₁
      nlinarith only [hvertex', mul_nonneg hs₁.le hz]
    have hzT : z ≤ T := by
      apply (le_div_iff₀ hs₁).2
      linarith
    have hT : u₁ - s₁ * T = k := by
      dsimp [T]
      field_simp
      ring
    let A := s₀ ^ 2 - 2 * r * s₁ ^ 2
    let B := -2 * u₀ * s₀ + 4 * r * u₁ * s₁ + 4 * r * (V₀ - V₁)
    let C := u₀ ^ 2 - 2 * r * u₁ ^ 2
    have hA : A ≤ 0 := by dsimp [A]; linarith
    have hC : 0 ≤ C := by dsimp [C]; linarith
    have hTop : 0 ≤ A * T ^ 2 + B * T + C := by
      have hc := hcont T
      have hTk := congrArg (fun a : ℝ => a * k) hT
      have hct : u₀ * k - r * k ^ 2 - s₀ * k * T + (V₀ - V₁) * T = k ^ 2 / 2 := by
        nlinarith only [hc, hTk]
      have hct4 := congrArg (fun a : ℝ => 4 * r * a) hct
      have hTsq := congrArg (fun a : ℝ => 2 * r * a ^ 2) hT
      have hsq := sq_nonneg (u₀ - s₀ * T - 2 * r * k)
      dsimp [A, B, C]
      nlinarith only [hct4, hTsq, hsq]
    have hD := P087_quadratic_nonneg_between A B C T z hA hC hTpos hTop hz hzT
    have hD' : 0 ≤ (u₀ - s₀ * z) ^ 2 - 2 * r * (u₁ - s₁ * z) ^ 2 +
        4 * r * (V₀ - V₁) * z := by
      dsimp [A, B, C] at hD
      nlinarith only [hD]
    let w := (u₀ - s₀ * z) / (2 * r)
    have hnum : 0 ≤ u₀ - s₀ * z := by
      have hp := mul_nonneg hs₀ (show 0 ≤ u₁ - s₁ * z by linarith)
      have hscaled : 0 ≤ s₁ * (u₀ - s₀ * z) := by nlinarith only [hp, hratio]
      exact nonneg_of_mul_nonneg_right hscaled hs₁
    have hw0 : 0 ≤ w := div_nonneg hnum (by linarith)
    have hwk : w ≤ k := by
      apply (div_le_iff₀ (show 0 < 2 * r by linarith)).2
      nlinarith only [hcut, mul_nonneg hs₀ hz]
    refine ⟨w, hw0, hwk, ?_⟩
    have hpositive : 0 ≤ ((u₀ - s₀ * z) ^ 2 - 2 * r * (u₁ - s₁ * z) ^ 2 +
        4 * r * (V₀ - V₁) * z + 2 * r * (x - (u₁ - s₁ * z)) ^ 2) / (4 * r) := by
      apply div_nonneg _ (by linarith)
      exact add_nonneg hD' (mul_nonneg (by linarith) (sq_nonneg _))
    have hid :
        u₀ * w - r * w ^ 2 - s₀ * w * z + V₀ * z - z ^ 2 -
          (u₁ * x - x ^ 2 / 2 - s₁ * x * z + V₁ * z - z ^ 2) =
        ((u₀ - s₀ * z) ^ 2 - 2 * r * (u₁ - s₁ * z) ^ 2 +
          4 * r * (V₀ - V₁) * z + 2 * r * (x - (u₁ - s₁ * z)) ^ 2) / (4 * r) := by
      dsimp [w]
      field_simp
      ring
    linarith only [hid, hpositive]

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087SupplierGap -/

set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

namespace NonExclEncroach.Channels

/-- Difference between the unrestricted one-dimensional retailer maxima at
zero order from supplier 2, for the interior and direct-only stage branches. -/
noncomputable def P087_supplierRDGap (t c : ℝ) : ℝ :=
  let a := wRD1 t c
  let b := wRD2 t c
  let α := (2 * (1 - c) - t * (1 - b)) / (4 - t ^ 2)
  let r := (2 + t ^ 2) / (4 - t ^ 2)
  (1 - a - α) ^ 2 / (4 * r) - ((1 + c) / 2 - a) ^ 2 / 2

/-- The one-dimensional gap is nonnegative throughout the complete R&D
cost regime. The proof checks the two cost endpoints and concavity in cost. -/
theorem P087_supplierRDGap_nonneg (t c : ℝ) (ht : 0 < t) (hupper : t ≤ 9 / 10)
    (hc2 : c2 t < c) (hc : c < 0) : 0 ≤ P087_supplierRDGap t c := by
  let d := 256 + 2 * t ^ 8 - 11 * t ^ 6 - 52 * t ^ 4 + 48 * t ^ 2
  let D := 4 - t ^ 2
  let E := 128 - 16 * t ^ 2 - 13 * t ^ 4
  let L := 2 * t * (8 * t ^ 15 - 4 * t ^ 14 + 106 * t ^ 13 - 62 * t ^ 12 +
    321 * t ^ 11 - 1308 * t ^ 10 - 4312 * t ^ 9 + 1952 * t ^ 8 +
    4096 * t ^ 7 + 11008 * t ^ 6 + 19200 * t ^ 5 - 29184 * t ^ 4 -
    19456 * t ^ 3 - 34816 * t ^ 2 - 32768 * t + 65536)
  have ht1 : t ≤ 1 := by linarith
  have hp2 := pow_le_pow_left₀ ht.le ht1 2
  have hp4 := pow_le_pow_left₀ ht.le ht1 4
  have hp6 := pow_le_pow_left₀ ht.le ht1 6
  norm_num only [one_pow] at hp2 hp4 hp6
  have hd : 0 < d := by
    dsimp [d]
    nlinarith only [hp4, hp6, sq_nonneg t, pow_nonneg ht.le 8]
  have hD : 0 < D := by dsimp [D]; linarith
  have hE : 0 < E := by dsimp [E]; linarith
  have htplus : 0 < t + 1 := by linarith
  have ht2plus : 0 < 2 + t ^ 2 := by nlinarith only [sq_nonneg t]
  have hd0 : (256 + 2 * t ^ 8 - 11 * t ^ 6 - 52 * t ^ 4 + 48 * t ^ 2) ≠ 0 := ne_of_gt hd
  have hD0 : (4 - t ^ 2) ≠ 0 := ne_of_gt hD
  have hE0 : (128 - 16 * t ^ 2 - 13 * t ^ 4) ≠ 0 := ne_of_gt hE
  have hE0' : (13 * t ^ 4 + 16 * t ^ 2 - 128) ≠ 0 := by dsimp [E] at hE; linarith
  have htplus0 : (t + 1) ≠ 0 := ne_of_gt htplus
  have ht2plus0 : (2 + t ^ 2) ≠ 0 := ne_of_gt ht2plus
  have hd0n := hd0
  have hD0n := hD0
  have hE0n := hE0
  have hE0n' := hE0'
  have hdsq0 := pow_ne_zero 2 hd0
  have hEsq0 := pow_ne_zero 2 hE0
  ring_nf at hd0n hD0n hE0n hE0n' hdsq0 hEsq0
  have hden : 0 < 24 * d ^ 2 := by positivity
  have hP := P087_rdGapAtZeroPolynomial_pos t ht hupper
  have hQ := P087_rdGapCurvaturePolynomial_pos t ht hupper
  have hpoly (v : ℝ) :
      P087_supplierRDGap t v =
        (t ^ 2 * P087_rdGapAtZeroPolynomial t + v * L -
          v ^ 2 * t ^ 2 * P087_rdGapCurvaturePolynomial t) / (24 * d ^ 2) := by
    let aN := 128 * (3 - v) - t * (128 + t * (56 + t * (96 + t *
      (90 - 5 * t ^ 4 + t ^ 3 + 34 * t ^ 2 * v + 18 * t + 6 * v)) - 168 * v))
    let bN := (1 - t) * (8 + t ^ 2) *
      (16 + t * (8 - 3 * t ^ 3 - 4 * (1 + t) * (2 - t ^ 2) * v + 4 * t))
    change (1 - aN / (3 * d) - (2 * (1 - v) - t * (1 - bN / d)) / D) ^ 2 /
      (4 * ((2 + t ^ 2) / D)) - ((1 + v) / 2 - aN / (3 * d)) ^ 2 / 2 =
        (t ^ 2 * P087_rdGapAtZeroPolynomial t + v * L -
          v ^ 2 * t ^ 2 * P087_rdGapCurvaturePolynomial t) / (24 * d ^ 2)
    field_simp [ne_of_gt hd, ne_of_gt hD, ht2plus0]
    dsimp [aN, bN, d, D, L, P087_rdGapAtZeroPolynomial, P087_rdGapCurvaturePolynomial]
    ring
  have hendformula :
      P087_supplierRDGap t (c2 t) =
        t ^ 2 * (t ^ 2 + 2) * (t ^ 2 - 4 * t - 8) ^ 2 *
          (160 - 168 * t ^ 2 - 18 * t ^ 4 - t ^ 6) /
          (32 * (t + 1) ^ 2 * (13 * t ^ 4 + 16 * t ^ 2 - 128) ^ 2) := by
    rw [hpoly]
    let N := 32 * t - 80 * t ^ 2 - 32 * t ^ 3 - 14 * t ^ 4 - 8 * t ^ 5 + 4 * t ^ 6 - t ^ 7
    have hEneg : 13 * t ^ 4 + 16 * t ^ 2 - 128 = -E := by dsimp [E]; ring
    rw [hEneg]
    change (t ^ 2 * P087_rdGapAtZeroPolynomial t + (N / (2 * (1 + t) * E)) * L -
        (N / (2 * (1 + t) * E)) ^ 2 * t ^ 2 * P087_rdGapCurvaturePolynomial t) / (24 * d ^ 2) = _
    have hplus0 : 1 + t ≠ 0 := by linarith
    field_simp [ne_of_gt hd, ne_of_gt hE, htplus0, hplus0]
    dsimp [N, E, d, L, P087_rdGapAtZeroPolynomial, P087_rdGapCurvaturePolynomial]
    ring
  have hp2' : t ^ 2 ≤ 81 / 100 := calc
    t ^ 2 ≤ (9 / 10 : ℝ) ^ 2 := pow_le_pow_left₀ ht.le hupper 2
    _ = 81 / 100 := by norm_num
  have hp4' : t ^ 4 ≤ 6561 / 10000 := calc
    t ^ 4 ≤ (9 / 10 : ℝ) ^ 4 := pow_le_pow_left₀ ht.le hupper 4
    _ = 6561 / 10000 := by norm_num
  have hp6' : t ^ 6 ≤ 531441 / 1000000 := calc
    t ^ 6 ≤ (9 / 10 : ℝ) ^ 6 := pow_le_pow_left₀ ht.le hupper 6
    _ = 531441 / 1000000 := by norm_num
  have hsmall : 0 ≤ 160 - 168 * t ^ 2 - 18 * t ^ 4 - t ^ 6 := by
    nlinarith only [hp2', hp4', hp6']
  have hend : 0 ≤ P087_supplierRDGap t (c2 t) := by
    rw [hendformula]
    positivity
  have hFend : 0 ≤ t ^ 2 * P087_rdGapAtZeroPolynomial t + c2 t * L -
      (c2 t) ^ 2 * t ^ 2 * P087_rdGapCurvaturePolynomial t := by
    rw [hpoly] at hend
    have := (le_div_iff₀ hden).mp hend
    simpa using this
  have hFzero : 0 ≤ t ^ 2 * P087_rdGapAtZeroPolynomial t := by positivity
  let A := -(t ^ 2 * P087_rdGapCurvaturePolynomial t)
  let B := L + 2 * A * c2 t
  let C := t ^ 2 * P087_rdGapAtZeroPolynomial t + c2 t * L + A * (c2 t) ^ 2
  have hA : A ≤ 0 := by dsimp [A]; apply neg_nonpos.mpr; positivity
  have hC : 0 ≤ C := by dsimp [C, A]; nlinarith only [hFend]
  have hT : 0 < -(c2 t) := by linarith
  have hTop : 0 ≤ A * (-(c2 t)) ^ 2 + B * (-(c2 t)) + C := by
    dsimp [A, B, C]
    nlinarith only [hFzero]
  have hF := P087_quadratic_nonneg_between A B C (-(c2 t)) (c - c2 t)
    hA hC hT hTop (by linarith) (by linarith)
  rw [hpoly]
  apply div_nonneg _ hden.le
  dsimp [A, B, C] at hF
  nlinarith only [hF]

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087RDGuards -/

set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

namespace NonExclEncroach.Channels
noncomputable section

theorem rd_U_pos (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hc2 : c2 t < c) (hc : c < 0) : 0 < rdU t c := by
  obtain ⟨hβ,hβh,hell,hκ,hη,hr,hs⟩ := rd_coefficient_signs t ht0 ht1
  have hx := rd_X_pos t c ht0.le ht1 hc2
  have hk := rd_cutoff_pos t c ht0 ht1 hc2 hc.le
  have hg : 0 < rdGamma t c := by
    rw [rd_cutoff_relation t c ht0 ht1]
    exact mul_pos hell hk
  have hrel := rd_X_relation t c ht0 ht1
  nlinarith only [hrel,mul_pos (mul_pos (by norm_num : (0:ℝ)<2) hκ) hx,mul_pos hs hg]

theorem rd_det_formula (t c : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    4*rdR t-(rdS t)^2=4*rdKappa t := by
  obtain ⟨hA,hB,hsA,hsB,hκ,hη,hr,hs⟩ := rd_coefficients t c ht0 ht1
  rw [hs]
  nlinarith only [hκ,hr]

theorem rd_cut_guard (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hc : c ≤ 0) :
    rdU t c/(2*rdR t) < rdCutoff t c := by
  obtain ⟨hA,hB,hsA,hsB,hκ,hη,hrdef,hsdef⟩ := rd_coefficients t c ht0.le ht1
  obtain ⟨hβ,hβh,hell,hκp,hηp,hr,hs⟩ := rd_coefficient_signs t ht0 ht1
  have hV : rdV t c=2*rdGamma t c+wRD2 t c := by dsimp [rdV]; linarith
  have hstat := rd_supplier2_stationary t c ht0.le ht1
  rw [hV] at hstat
  have hg := rd_cutoff_relation t c ht0 ht1
  have hid : rdS t*(2*rdR t*rdCutoff t c-rdU t c)=2*rdR t*wRD2 t c := by
    rw [hsdef] at hstat ⊢
    nlinarith only [hstat,congrArg (fun z : ℝ => 4*rdR t*z) hg]
  have hp : 0 < rdS t*(2*rdR t*rdCutoff t c-rdU t c) := by
    rw [hid]
    exact mul_pos (mul_pos (by norm_num) hr) (rdB_pos t c ht0.le ht1 hc)
  have hgap : 0 < 2*rdR t*rdCutoff t c-rdU t c := by
    rcases mul_pos_iff.mp hp with ⟨_,h⟩|⟨h,_⟩
    · exact h
    · linarith
  apply (div_lt_iff₀ (show 0 < 2*rdR t by positivity)).2
  nlinarith only [hgap]

theorem rd_ratio_guard (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hc2 : c2 t < c) (hc : c < 0) :
    rdS t*((1+c)/2-wRD1 t c) ≤ (3*t/2)*rdU t c := by
  obtain ⟨hA,hB,hsA,hsB,hκ,hη,hrdef,hsdef⟩ := rd_coefficients t c ht0.le ht1
  obtain ⟨hβ,hβh,hell,hκp,hηp,hr,hs⟩ := rd_coefficient_signs t ht0 ht1
  have hk := rd_cutoff_pos t c ht0 ht1 hc2 hc.le
  have hg := rd_cutoff_relation t c ht0 ht1
  have hcut := (div_lt_iff₀ (show 0 < 2*rdR t by positivity)).mp
    (rd_cut_guard t c ht0 ht1 hc.le)
  have hcont : (1+c)/2-wRD1 t c = rdU t c-(rdR t-1/2)*rdCutoff t c := by
    dsimp only [rdU]
    nlinarith only [hA,congrArg (fun z : ℝ => rdCutoff t c*z) hsA,
      congrArg (fun z : ℝ => t*z) hg,congrArg (fun z : ℝ => rdCutoff t c*z) hrdef]
  have hD := rdD_pos t ht0.le ht1
  have hsdiff : rdS t-3*t/2=3*t^3/(2*rdD t) := by
    unfold rdS
    field_simp [ne_of_gt hD]
    dsimp [rdD]
    ring
  have hsdiffp : 0 ≤ rdS t-3*t/2 := by rw [hsdiff]; positivity
  have halg : rdS t*(rdR t-1/2)=(rdS t-3*t/2)*(2*rdR t+rdBeta t) := by
    dsimp only [rdS,rdR,rdBeta]
    field_simp [ne_of_gt hD]
    dsimp [rdD]
    ring
  have hl : rdU t c ≤ (2*rdR t+rdBeta t)*rdCutoff t c := by
    nlinarith only [hcut,mul_pos hβ hk]
  have hm := mul_le_mul_of_nonneg_left hl hsdiffp
  rw [hcont]
  nlinarith only [hm,congrArg (fun z : ℝ => rdCutoff t c*z) halg]

theorem rd_concave_guard (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    (rdS t)^2 ≤ 2*rdR t*(3*t/2)^2 := by
  have hD := rdD_pos t ht0.le ht1
  have ht2 : t^2 < 1 := by nlinarith
  have h2 : 0 ≤ 2-t^2 := by linarith
  have hid : 2*rdR t*(3*t/2)^2-(rdS t)^2=9*t^4*(2-t^2)/(2*(rdD t)^2) := by
    dsimp only [rdR,rdS]
    field_simp [ne_of_gt hD]
    dsimp [rdD]
    ring
  have hnonneg : 0 ≤ 9*t^4*(2-t^2)/(2*(rdD t)^2) := by positivity
  linarith

theorem rd_gap_guard (t c : ℝ) (ht0 : 0 < t) (ht9 : t ≤ 9/10)
    (hc2 : c2 t < c) (hc : c < 0) :
    2*rdR t*((1+c)/2-wRD1 t c)^2 ≤ (rdU t c)^2 := by
  have hgap := P087_supplierRDGap_nonneg t c ht0 ht9 hc2 hc
  change 0 ≤ (rdU t c)^2/(4*rdR t)-((1+c)/2-wRD1 t c)^2/2 at hgap
  have hr := (rd_coefficient_signs t ht0 (by linarith)).2.2.2.2.2.1
  have h : ((1+c)/2-wRD1 t c)^2/2 ≤ (rdU t c)^2/(4*rdR t) := by linarith
  have hh := (le_div_iff₀ (show 0 < 4*rdR t by positivity)).mp h
  nlinarith only [hh]

end
end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087SupplierTerminal -/

namespace NonExclEncroach.Channels

/-- After the direct quantity reaches zero, every larger order from supplier 1
is dominated by the boundary order `1-c`, at the same order from supplier 2.
This is uniform in the actual price charged by supplier 2. -/
theorem P087_reseller_terminal_bound (t c a v x z : ℝ)
    (ht : 0 ≤ t) (hc : c ≤ 0) (ha : 0 ≤ a) (hz : 0 ≤ z) (hx : 1 - c ≤ x) :
    resellerProfit t x z a v 0 ≤ resellerProfit t (1 - c) z a v 0 := by
  have htz := mul_nonneg ht hz
  have hf : 0 ≤ x + (1 - c) - (1 - a - 2 * t * z) := by linarith
  have hp := mul_nonneg (sub_nonneg.mpr hx) hf
  unfold resellerProfit p1 p2
  nlinarith only [hp]

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087Supplier2Global -/

namespace NonExclEncroach.Channels

/-- A globally optimal retailer response to every supplier-2 price, with a
uniform supplier-2 profit bound, for the exact three-branch direct strategy.
Candidate-parameter identities and inequalities are explicit hypotheses. -/
theorem P087_supplier2_global_response_exists
    (θ c a b α β r s u V k : ℝ) (Y : ℝ → ℝ)
    (hθ : 0 < θ) (hc : c ≤ 0) (ha : 0 ≤ a) (hk : 0 ≤ k) (hkA : k ≤ 1 - c)
    (hr : 0 < r) (hs : 0 < s) (hu : 0 ≤ u) (hdet : 0 < 4 * r - s ^ 2)
    (hrdef : r = 1 - β) (hsdef : s = θ * (2 - β))
    (hudef : u = 1 - a - α) (hVdef : V = 1 - θ * α)
    (hcut : u / (2 * r) ≤ k)
    (hratio : s * ((1 + c) / 2 - a) ≤ (3 * θ / 2) * u)
    (hgap : 2 * r * ((1 + c) / 2 - a) ^ 2 ≤ u ^ 2)
    (hconcave : s ^ 2 ≤ 2 * r * (3 * θ / 2) ^ 2)
    (hprice : 2 * r * (V - 2 * b) = s * u)
    (hYlo : ∀ x, 0 ≤ x → x ≤ k → Y x = α - β * x)
    (hYmid : ∀ x, k ≤ x → x ≤ 1 - c → Y x = (1 - c - x) / 2)
    (hYhi : ∀ x, 1 - c ≤ x → Y x = 0)
    (v : ℝ) (hv : 0 ≤ v) :
    ∃ x z : ℝ, 0 ≤ x ∧ 0 ≤ z ∧ x ≤ k ∧
      (∀ x' z', 0 ≤ x' → 0 ≤ z' →
        resellerProfit θ x' z' a v (Y x') ≤ resellerProfit θ x z a v (Y x)) ∧
      supplier2Profit z v ≤ (2 * r / (4 * r - s ^ 2)) * b ^ 2 := by
  let F := fun x z => resellerProfit θ x z a v (Y x)
  let u₁ := (1 + c) / 2 - a
  let s₁ := 3 * θ / 2
  let V₁ := 1 - v - θ * (1 - c) / 2
  have hs₁ : 0 < s₁ := by dsimp [s₁]; positivity
  have hcut' : u ≤ 2 * r * k := by
    have := (div_le_iff₀ (show 0 < 2 * r by linarith)).mp hcut
    nlinarith only [this]
  have hcutY : α - β * k = (1 - c - k) / 2 :=
    (hYlo k hk le_rfl).symm.trans (hYmid k le_rfl hkA)
  have hcont₀ : u * k - r * k ^ 2 = u₁ * k - k ^ 2 / 2 := by
    rw [hudef, hrdef]
    dsimp [u₁]
    have h := congrArg (fun z : ℝ => z * k) hcutY
    nlinarith only [h]
  have hcont₁ : (V - v) - s * k = V₁ - s₁ * k := by
    rw [hVdef, hsdef]
    dsimp [V₁, s₁]
    have h := congrArg (fun z : ℝ => θ * z) hcutY
    nlinarith only [h]
  have hmatch : ∀ x z, 0 ≤ x → x ≤ k → 0 ≤ z →
      F x z = P087_retailQuadratic r s u (V - v) x z := by
    intro x z hx hxk hz
    dsimp only [F]
    rw [hYlo x hx hxk]
    dsimp [P087_retailQuadratic, resellerProfit, p1, p2]
    rw [hrdef, hsdef, hudef, hVdef]
    ring
  have hmid (x z : ℝ) (hkx : k ≤ x) (hxA : x ≤ 1 - c) :
      F x z = u₁ * x - x ^ 2 / 2 - s₁ * x * z + V₁ * z - z ^ 2 := by
    dsimp only [F]
    rw [hYmid x hkx hxA]
    dsimp [u₁, s₁, V₁, resellerProfit, p1, p2]
    ring
  have hmidCover (x z : ℝ) (hkx : k ≤ x) (hxA : x ≤ 1 - c) (hz : 0 ≤ z) :
      ∃ w, 0 ≤ w ∧ w ≤ k ∧ F x z ≤ P087_retailQuadratic r s u (V - v) w z := by
    obtain ⟨w, hw0, hwk, hdom⟩ := P087_two_branch_dominance
      r u s (V - v) u₁ s₁ V₁ k z x hr hs.le hs₁ hk hz hkx
      hcut' hratio hgap hconcave hcont₀ hcont₁
    refine ⟨w, hw0, hwk, ?_⟩
    rw [hmid x z hkx hxA]
    calc
      _ ≤ u * w - r * w ^ 2 - s * w * z + (V - v) * z - z ^ 2 := hdom
      _ = P087_retailQuadratic r s u (V - v) w z := by unfold P087_retailQuadratic; ring
  have hcover : ∀ x z, 0 ≤ x → 0 ≤ z → ∃ w, 0 ≤ w ∧ w ≤ k ∧
      F x z ≤ P087_retailQuadratic r s u (V - v) w z := by
    intro x z hx hz
    by_cases hxk : x ≤ k
    · exact ⟨x, hx, hxk, le_of_eq (hmatch x z hx hxk hz)⟩
    · have hkx : k ≤ x := le_of_not_ge hxk
      by_cases hxA : x ≤ 1 - c
      · exact hmidCover x z hkx hxA hz
      · have hAx : 1 - c ≤ x := le_of_not_ge hxA
        obtain ⟨w, hw0, hwk, hdom⟩ := hmidCover (1 - c) z hkA le_rfl hz
        refine ⟨w, hw0, hwk, le_trans ?_ hdom⟩
        dsimp only [F]
        rw [hYhi x hAx, hYhi (1 - c) le_rfl]
        exact P087_reseller_terminal_bound θ c a v x z hθ.le hc ha hz hAx
  exact P087_supplier2_response_of_cover F r s u V b v k hr hs hu hdet hv hprice
    hcut hmatch hcover

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087StageBranches -/

namespace NonExclEncroach.Channels

/-- Exact three-branch form when the conjectured second order vanishes first. -/
theorem P087_stageIII_three_branches
    (θ c b α β γ ell k r y z : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ : 0 ≤ β) (hell : 0 ≤ ell)
    (hkA : k < 1-c)
    (hA : 2*α+θ*γ = 1-c) (hB : 2*γ+θ*α = 1-b)
    (hsA : 2*β+θ*ell = 1) (hsB : 2*ell+θ*β = 2*θ)
    (hγ : γ = ell*k) (h : IsStageIII θ c b r y z) :
    (r ≤ k → y = α-β*r ∧ z = γ-ell*r) ∧
    (k ≤ r → r ≤ 1-c → y = (1-c-r)/2 ∧ z = 0) ∧
    (1-c ≤ r → y = 0 ∧ z = 0) := by
  have hlinY : ∀ v : ℝ, 2*(α-β*v)+θ*(γ-ell*v) = 1-c-v := by
    intro v
    calc
      2*(α-β*v)+θ*(γ-ell*v) = (2*α+θ*γ)-(2*β+θ*ell)*v := by ring
      _ = 1-c-v := by rw [hA, hsA]; ring
  have hlinZ : ∀ v : ℝ, 2*(γ-ell*v)+θ*(α-β*v) = 1-b-2*θ*v := by
    intro v
    calc
      2*(γ-ell*v)+θ*(α-β*v) = (2*γ+θ*α)-(2*ell+θ*β)*v := by ring
      _ = 1-b-2*θ*v := by rw [hB, hsB]
  have hcutY : α-β*k = (1-c-k)/2 := by
    have hh := hlinY k
    rw [hγ] at hh
    nlinarith only [hh]
  have hcutZ : θ*((1-c-k)/2) = 1-b-2*θ*k := by
    have hh := hlinZ k
    rw [hγ, hcutY] at hh
    nlinarith only [hh]
  refine ⟨?_, ?_, ?_⟩
  · intro hrk
    have hy : 0 ≤ α-β*r := by
      nlinarith [mul_nonneg hβ (sub_nonneg.mpr hrk)]
    have hz : 0 ≤ γ-ell*r := by
      rw [hγ]
      nlinarith [mul_nonneg hell (sub_nonneg.mpr hrk)]
    have hh : IsStageIII θ c b r (α-β*r) (γ-ell*r) := by
      apply P087_stageIII_of_complementarity θ c b r _ _ hy hz
      · exact (hlinY r).ge
      · exact (hlinZ r).ge
      · rw [hlinY r]
        ring
      · rw [hlinZ r]
        ring
    exact P087_stageIII_unique θ c b r y z _ _ hθ0 hθ1 h hh
  · intro hkr hrA
    have hh : IsStageIII θ c b r ((1-c-r)/2) 0 := by
      apply P087_stageIII_of_complementarity θ c b r _ _ (by linarith) (le_refl 0)
      · linarith
      · nlinarith [mul_nonneg hθ0 (sub_nonneg.mpr hkr)]
      · ring
      · ring
    exact P087_stageIII_unique θ c b r y z _ _ hθ0 hθ1 h hh
  · intro hAr
    have hh : IsStageIII θ c b r 0 0 := by
      apply P087_stageIII_of_complementarity θ c b r _ _ (le_refl 0) (le_refl 0)
      · linarith
      · nlinarith [mul_nonneg hθ0 (sub_nonneg.mpr hAr),
          mul_nonneg hθ0 (sub_nonneg.mpr hkA.le)]
      · ring
      · ring
    exact P087_stageIII_unique θ c b r y z _ _ hθ0 hθ1 h hh

theorem P087_supplier1Profit_eq_square (θ c b r y z a : ℝ)
    (h : IsStageIII θ c b r y z) :
    supplier1Profit θ c r z a y = y^2+a*r := by
  obtain ⟨_, _, _, _, hyc, _⟩ := P087_stageIII_complementarity θ c b r y z h
  dsimp only [supplier1Profit, pd]
  nlinarith only [hyc]

theorem P087_resellerProfit_reduced (θ r z a b y : ℝ) :
    resellerProfit θ r z a b y = r*(1-a-r-y)+z*((1-b-2*θ*r-θ*y)-z) := by
  dsimp only [resellerProfit, p1, p2]
  ring

theorem P087_resellerProfit_stageIII (θ c b r y z a : ℝ)
    (h : IsStageIII θ c b r y z) :
    resellerProfit θ r z a b y = r*(1-a-r-y)+z^2 := by
  obtain ⟨_, _, _, _, _, hzc⟩ := P087_stageIII_complementarity θ c b r y z h
  rw [P087_resellerProfit_reduced]
  nlinarith only [hzc]

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087RDResponses -/

set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

namespace NonExclEncroach.Channels
noncomputable section

theorem rd_branch_formulas (t c x : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hc2 : c2 t < c) (hc : c < 0) (hx : 0 ≤ x) :
    (x ≤ rdCutoff t c → P087_globalY t c (wRD2 t c) x=rdAlpha t c-rdBeta t*x ∧
      P087_globalQ t c (wRD2 t c) x=rdGamma t c-rdLambda t*x) ∧
    (rdCutoff t c ≤ x → x ≤ 1-c → P087_globalY t c (wRD2 t c) x=(1-c-x)/2 ∧
      P087_globalQ t c (wRD2 t c) x=0) ∧
    (1-c ≤ x → P087_globalY t c (wRD2 t c) x=0 ∧ P087_globalQ t c (wRD2 t c) x=0) := by
  obtain ⟨hA,hB,hsA,hsB,hκ,hη,hr,hs⟩ := rd_coefficients t c ht0.le ht1
  obtain ⟨hβ,hβh,hell,hκp,hηp,hrp,hsp⟩ := rd_coefficient_signs t ht0 ht1
  exact P087_stageIII_three_branches t c (wRD2 t c) (rdAlpha t c) (rdBeta t)
    (rdGamma t c) (rdLambda t) (rdCutoff t c) x _ _ ht0.le ht1 hβ.le hell.le
    (rd_cutoff_lt_A t c ht0 ht1 hc2 hc) hA hB hsA hsB
    (rd_cutoff_relation t c ht0 ht1) (P087_global_stageIII t c (wRD2 t c) x ht0.le ht1)

theorem rd_supplier2_response_exists (t c : ℝ) (ht0 : 0 < t) (ht9 : t ≤ 9/10)
    (hc2 : c2 t < c) (hc : c < 0) (v : ℝ) (hv : 0 ≤ v) :
    ∃ x z : ℝ, 0 ≤ x ∧ 0 ≤ z ∧ x ≤ rdCutoff t c ∧
      (∀ x' z', 0 ≤ x' → 0 ≤ z' →
        resellerProfit t x' z' (wRD1 t c) v (P087_globalY t c (wRD2 t c) x') ≤
          resellerProfit t x z (wRD1 t c) v (P087_globalY t c (wRD2 t c) x)) ∧
      supplier2Profit z v ≤ (2*rdR t/(4*rdR t-(rdS t)^2))*(wRD2 t c)^2 := by
  have ht1 : t < 1 := by linarith
  obtain ⟨hA,hB,hsA,hsB,hκ,hη,hr,hs⟩ := rd_coefficients t c ht0.le ht1
  obtain ⟨hβ,hβh,hell,hκp,hηp,hrp,hsp⟩ := rd_coefficient_signs t ht0 ht1
  have hk := rd_cutoff_pos t c ht0 ht1 hc2 hc.le
  have hdet : 0 < 4*rdR t-(rdS t)^2 := by rw [rd_det_formula t c ht0.le ht1]; positivity
  have hsdef : rdS t=t*(2-rdBeta t) := by rw [hs]; nlinarith only [hsB]
  refine P087_supplier2_global_response_exists t c (wRD1 t c) (wRD2 t c)
    (rdAlpha t c) (rdBeta t) (rdR t) (rdS t) (rdU t c) (rdV t c) (rdCutoff t c)
    (P087_globalY t c (wRD2 t c)) ht0 hc.le (rd_A_pos t c ht0 ht1 hc2 hc).le hk.le
    (rd_cutoff_lt_A t c ht0 ht1 hc2 hc).le hrp hsp (rd_U_pos t c ht0 ht1 hc2 hc).le hdet
    hr hsdef rfl rfl (rd_cut_guard t c ht0 ht1 hc.le).le
    (rd_ratio_guard t c ht0 ht1 hc2 hc) (rd_gap_guard t c ht0 ht9 hc2 hc)
    (rd_concave_guard t ht0 ht1) (rd_supplier2_stationary t c ht0.le ht1) ?_ ?_ ?_ v hv
  · intro x hx hxk
    exact ((rd_branch_formulas t c x ht0 ht1 hc2 hc hx).1 hxk).1
  · intro x hkx hxA
    exact ((rd_branch_formulas t c x ht0 ht1 hc2 hc (le_trans hk.le hkx)).2.1 hkx hxA).1
  · intro x hAx
    have hx : 0 ≤ x := by linarith
    exact ((rd_branch_formulas t c x ht0 ht1 hc2 hc hx).2.2 hAx).1

theorem rd_quadratic_stationarity (t c : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    2*rdR t*rdX t c+rdS t*rdZ t c=rdU t c ∧
    2*rdZ t c+rdS t*rdX t c=rdV t c-wRD2 t c := by
  obtain ⟨hA,hB,hsA,hsB,hκ,hη,hr,hs⟩ := rd_coefficients t c ht0.le ht1
  have hx := rd_X_relation t c ht0 ht1
  have hkr : rdR t=rdKappa t+(rdLambda t)^2 := by linarith
  rw [hs] at hx ⊢
  dsimp only [rdZ,rdV]
  constructor
  · nlinarith only [hx,congrArg (fun z : ℝ => 2*rdX t c*z) hkr]
  · nlinarith only [hB]

theorem rd_retail_match (t c x z : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hc2 : c2 t < c) (hc : c < 0) (hx : 0 ≤ x) (hxk : x ≤ rdCutoff t c) :
    resellerProfit t x z (wRD1 t c) (wRD2 t c) (P087_globalY t c (wRD2 t c) x) =
      P087_retailQuadratic (rdR t) (rdS t) (rdU t c) (rdV t c-wRD2 t c) x z := by
  have hy := ((rd_branch_formulas t c x ht0 ht1 hc2 hc hx).1 hxk).1
  obtain ⟨hA,hB,hsA,hsB,hκ,hη,hr,hs⟩ := rd_coefficients t c ht0.le ht1
  have hsdef : rdS t=t*(2-rdBeta t) := by rw [hs]; nlinarith only [hsB]
  rw [hy]
  dsimp only [resellerProfit,p1,p2,P087_retailQuadratic,rdU,rdV]
  rw [hr,hsdef]
  ring

theorem rd_base_reseller_global (t c : ℝ) (ht0 : 0 < t) (ht9 : t ≤ 9/10)
    (hc2 : c2 t < c) (hc : c < 0) :
    ∀ x z, 0 ≤ x → 0 ≤ z →
      resellerProfit t x z (wRD1 t c) (wRD2 t c) (P087_globalY t c (wRD2 t c) x) ≤
        resellerProfit t (rdX t c) (rdZ t c) (wRD1 t c) (wRD2 t c)
          (P087_globalY t c (wRD2 t c) (rdX t c)) := by
  have ht1 : t < 1 := by linarith
  have hX := rd_X_pos t c ht0.le ht1 hc2
  have hZ := rd_Z_pos t c ht0 ht1 hc.le
  have hXk := rd_X_lt_cutoff t c ht0 ht1 hc.le
  have hκ := (rd_coefficient_signs t ht0 ht1).2.2.2.1
  have hdet : 0 < 4*rdR t-(rdS t)^2 := by rw [rd_det_formula t c ht0.le ht1]; positivity
  obtain ⟨hxstat,hzstat⟩ := rd_quadratic_stationarity t c ht0 ht1
  obtain ⟨x0,z0,hx0,hz0,hx0k,hm,_⟩ := rd_supplier2_response_exists t c ht0 ht9 hc2 hc
    (wRD2 t c) (rdB_pos t c ht0.le ht1 hc.le).le
  have hcap : resellerProfit t x0 z0 (wRD1 t c) (wRD2 t c) (P087_globalY t c (wRD2 t c) x0) ≤
      resellerProfit t (rdX t c) (rdZ t c) (wRD1 t c) (wRD2 t c)
        (P087_globalY t c (wRD2 t c) (rdX t c)) := by
    rw [rd_retail_match t c x0 z0 ht0 ht1 hc2 hc hx0 hx0k,
      rd_retail_match t c (rdX t c) (rdZ t c) ht0 ht1 hc2 hc hX.le hXk.le]
    apply P087_retailQuadratic_max_of_complementarity _ _ _ _ _ _ hdet hxstat.ge hzstat.ge
    · rw [hxstat]; ring
    · rw [hzstat]; ring
    · exact hx0
    · exact hz0
  intro x z hx hz
  exact le_trans (hm x z hx hz) hcap

end
end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087QuadraticCalculus -/

namespace NonExclEncroach.Channels

/-- A maximum against nearby moves to the right has a nonpositive right slope. -/
theorem P087_quadratic_right_nonpos (A B C x u : ℝ) (hC : 0 < C) (hu : x < u)
    (hmax : ∀ r, x ≤ r → r ≤ u → A+B*r-C*r^2 ≤ A+B*x-C*x^2) :
    B ≤ 2*C*x := by
  by_contra h
  have hL : 0 < B-2*C*x := by linarith
  let e := min ((u-x)/2) ((B-2*C*x)/(2*C))
  have he : 0 < e := lt_min (by linarith) (div_pos hL (by linarith))
  have heu : e ≤ (u-x)/2 := min_le_left _ _
  have heC : e*(2*C) ≤ B-2*C*x :=
    (le_div_iff₀ (by linarith : 0 < 2*C)).mp (min_le_right _ _)
  have hmax' := hmax (x+e) (by linarith) (by linarith)
  have hprod : 0 ≤ e*(B-2*C*x-2*C*e) := by
    apply mul_nonneg (le_of_lt he)
    nlinarith
  have hpos : 0 < e*(B-2*C*x) := mul_pos he hL
  nlinarith

/-- A maximum against nearby moves to the left has a nonnegative left slope. -/
theorem P087_quadratic_left_nonneg (A B C x l : ℝ) (hC : 0 < C) (hl : l < x)
    (hmax : ∀ r, l ≤ r → r ≤ x → A+B*r-C*r^2 ≤ A+B*x-C*x^2) :
    2*C*x ≤ B := by
  have hright := P087_quadratic_right_nonpos A (-B) C (-x) (-l) hC (by linarith)
    (by
      intro r hrx hrl
      have hh := hmax (-r) (by linarith) (by linarith)
      nlinarith only [hh])
  linarith

/-- Interior first-order condition for a strictly concave quadratic. -/
theorem P087_quadratic_localFOC (A B C x l u : ℝ) (hC : 0 < C) (hl : l < x) (hu : x < u)
    (hmax : ∀ r, l < r → r < u → A+B*r-C*r^2 ≤ A+B*x-C*x^2) :
    B = 2*C*x := by
  apply le_antisymm
  · exact P087_quadratic_right_nonpos A B C x ((x+u)/2) hC (by linarith)
      (by intro r hr1 hr2; exact hmax r (by linarith) (by linarith))
  · exact P087_quadratic_left_nonneg A B C x ((l+x)/2) hC (by linarith)
      (by intro r hr1 hr2; exact hmax r (by linarith) (by linarith))

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087Supplier1Bound -/

namespace NonExclEncroach.Channels

/-- Supplier 1's deviation bound for the complete three-branch reduced retailer problem.

`F` is the retailer's profit after conditionally optimizing its second order.
`P` is supplier 1's profit at the same response. The hypotheses describe the
interior, zero-conjecture, and zero-direct branches, including both joins.
-/
theorem P087_supplier1_piecewise_bound
    (a c A0 α β γ κ U0 η ν k xstar x : ℝ) (F P : ℝ → ℝ)
    (ha : 0 ≤ a) (hc : c < 0) (hA0c : A0 = 1-c)
    (hγ : 0 ≤ γ) (hk : 0 < k) (hkA : k < A0)
    (hκ : 0 < κ) (hη : 0 < η) (hηeq : η = 2*κ-β^2)
    (hνeq : ν = U0-2*α*β) (hstation : ν = 2*η*xstar)
    (hjump : U0-2*κ*k < (1+c)/2-k)
    (hmargin : A0^2/4+c*γ-3*γ^2/2 ≤ α^2)
    (hF0 : ∀ r, 0 ≤ r → r ≤ k → F r = γ^2+(U0-a)*r-κ*r^2)
    (hF1 : ∀ r, k ≤ r → r ≤ A0 → F r = ((1+c)/2-a)*r-r^2/2)
    (hF2 : ∀ r, A0 ≤ r → F r = (1-a)*r-r^2)
    (hP0 : ∀ r, 0 ≤ r → r ≤ k → P r = (α-β*r)^2+a*r)
    (hP1 : ∀ r, k ≤ r → r ≤ A0 → P r = ((A0-r)/2)^2+a*r)
    (hx : 0 ≤ x) (hmax : ∀ r, 0 ≤ r → F r ≤ F x) :
    P x ≤ α^2+η*xstar^2 := by
  have hbase : F 0 = γ^2 := by simpa using hF0 0 (le_refl 0) hk.le
  have hcap : 0 ≤ η*xstar^2 := mul_nonneg hη.le (sq_nonneg _)
  have hxA : x < A0 := by
    by_contra h
    have hxA' : A0 ≤ x := le_of_not_gt h
    have hzero := hmax 0 (le_refl 0)
    rw [hbase, hF2 x hxA'] at hzero
    have hx1 : 1 < x := by linarith
    have hp : 0 < x*(x-1) := mul_pos (by linarith) (by linarith)
    nlinarith [mul_nonneg ha hx, sq_nonneg γ]
  by_cases hx0 : x = 0
  · subst x
    rw [hP0 0 (le_refl 0) hk.le]
    nlinarith
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  by_cases hxk : x < k
  · have hfoc := P087_quadratic_localFOC (γ^2) (U0-a) κ x 0 k hκ hxpos hxk
      (by
        intro r hr0 hrk
        have hh := hmax r hr0.le
        rwa [hF0 r hr0.le hrk.le, hF0 x hx hxk.le] at hh)
    have haeq : a = U0-2*κ*x := by linarith
    have hp : P x = α^2+ν*x-η*x^2 := by
      rw [hP0 x hx hxk.le, haeq, hνeq, hηeq]
      ring
    rw [hstation] at hp
    have hsquare : 0 ≤ η*(x-xstar)^2 := mul_nonneg hη.le (sq_nonneg _)
    nlinarith
  · have hkx : k ≤ x := le_of_not_gt hxk
    by_cases hxkeq : x = k
    · subst x
      have hleft := P087_quadratic_left_nonneg (γ^2) (U0-a) κ k 0 hκ hk
        (by
          intro r hr0 hrk
          have hh := hmax r hr0
          rwa [hF0 r hr0 hrk, hF0 k hk.le le_rfl] at hh)
      have hright := P087_quadratic_right_nonpos 0 ((1+c)/2-a) (1/2) k A0
        (by norm_num) hkA
        (by
          intro r hrk hrA
          have hh := hmax r (le_trans hk.le hrk)
          rw [hF1 r hrk hrA, hF1 k le_rfl hkA.le] at hh
          nlinarith only [hh])
      linarith
    · have hkx' : k < x := lt_of_le_of_ne hkx (Ne.symm hxkeq)
      have hfoc := P087_quadratic_localFOC 0 ((1+c)/2-a) (1/2) x k A0
        (by norm_num) hkx' hxA
        (by
          intro r hrk hrA
          have hh := hmax r (le_trans hk.le hrk.le)
          rw [hF1 r hrk.le hrA.le, hF1 x hkx hxA.le] at hh
          nlinarith only [hh])
      have haeq : a = (1+c)/2-x := by linarith
      have hzero := hmax 0 (le_refl 0)
      rw [hbase, hF1 x hkx hxA.le, haeq] at hzero
      have hsq : 2*γ^2 ≤ x^2 := by nlinarith
      have hxγ : γ ≤ x := by nlinarith
      have hcx : c*x ≤ c*γ := mul_le_mul_of_nonpos_left hxγ hc.le
      have hp : P x = A0^2/4+c*x-3*x^2/4 := by
        rw [hP1 x hkx hxA.le, haeq, hA0c]
        ring
      nlinarith

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087DirectOnly -/

namespace NonExclEncroach.Channels

/-- At fixed first-product quantity, the reseller chooses a scalar concave quadratic. -/
theorem P087_reseller_quadratic_iff (θ x u b y z : ℝ) :
    IsBestResponse (fun r => resellerProfit θ x r u b y) z ↔
      IsBestResponse (fun r => r * ((1 - b - 2 * θ * x - θ * y) - r)) z := by
  constructor <;> rintro ⟨hz, h⟩ <;> refine ⟨hz, ?_⟩ <;> intro r hr
  · have hh := h r hr
    dsimp only [resellerProfit, p1, p2] at hh
    nlinarith only [hh]
  · have hh := h r hr
    dsimp only [resellerProfit, p1, p2]
    nlinarith only [hh]

/-- Actual and conjectured orders agree whenever both are conditional best responses
at the same believed/actual second wholesale price. No supplier optimality is needed. -/
theorem P087_reseller_order_eq_conjecture (θ c b x y q u z : ℝ)
    (hIII : IsStageIII θ c b x y q)
    (hR : IsBestResponse (fun r => resellerProfit θ x r u b y) z) : z = q := by
  have ha := (P087_reseller_quadratic_iff _ _ _ _ _ _).mp hR
  have hc := (P087_reseller_quadratic_iff _ _ _ _ _ _).mp hIII.2
  exact (P087_quadratic_optimizer _ _ ha).trans
    (P087_quadratic_optimizer _ _ hc).symm

theorem P087_reseller_optimum_stageIII (θ c b x y q u z : ℝ)
    (hIII : IsStageIII θ c b x y q)
    (hR : IsBestResponse (fun r => resellerProfit θ x r u b y) z) :
    IsStageIII θ c b x y z := by
  rw [P087_reseller_order_eq_conjecture θ c b x y q u z hIII hR]
  exact hIII

/-- Consistent beliefs force the actual second-product order to equal the conjectured order,
also after any supplier-1 wholesale-price deviation. -/
theorem P087_consistent_reseller_order (θ c : ℝ) (σ : Profile)
    (hEq : IsEquilibrium θ c σ) (u : ℝ) (hu : 0 ≤ u) :
    (σ.R u σ.w2).2 = σ.Q2c (σ.R u σ.w2).1 := by
  obtain ⟨hw1, hw2, hIII, hR, hS1, hS2⟩ := hEq
  have horders := hR u σ.w2 hu hw2
  have hstage := hIII (σ.R u σ.w2).1 horders.1
  have ha : IsBestResponse
      (fun r => resellerProfit θ (σ.R u σ.w2).1 r u σ.w2 (σ.Y (σ.R u σ.w2).1))
      (σ.R u σ.w2).2 :=
    ⟨horders.2.1, fun r hr => horders.2.2 _ r horders.1 hr⟩
  have haq := (P087_reseller_quadratic_iff _ _ _ _ _ _).mp ha
  have hcq := (P087_reseller_quadratic_iff _ _ _ _ _ _).mp hstage.2
  exact (P087_quadratic_optimizer _ _ haq).trans
    (P087_quadratic_optimizer _ _ hcq).symm

/-- The actual equilibrium quantities themselves satisfy stage III. -/
theorem P087_actual_stageIII (θ c : ℝ) (σ : Profile) (hEq : IsEquilibrium θ c σ) :
    IsStageIII θ c σ.w2 σ.q1 σ.y σ.q2 := by
  have horders := hEq.2.2.2.1 σ.w1 σ.w2 hEq.1 hEq.2.1
  have hstage := hEq.2.2.1 σ.q1 horders.1
  have hc : σ.q2 = σ.Q2c σ.q1 :=
    P087_consistent_reseller_order θ c σ hEq σ.w1 hEq.1
  rw [hc]
  exact hstage


end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087Supplier1Global -/

namespace NonExclEncroach.Channels

/-- Every globally optimal reseller response to every supplier-1 wholesale
deviation obeys the same completed-square profit bound. -/
theorem P087_supplier1_global_bound
    (θ c b α β γ ell κ U0 η ν k xstar a x z : ℝ) (Y Q : ℝ → ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hc : c < 0) (ha : 0 ≤ a)
    (hβ : 0 ≤ β) (hβhalf : β < 1/2) (hell : 0 ≤ ell)
    (hk : 0 < k) (hkA : k < 1-c)
    (hA : 2*α+θ*γ = 1-c) (hB : 2*γ+θ*α = 1-b)
    (hsA : 2*β+θ*ell = 1) (hsB : 2*ell+θ*β = 2*θ)
    (hγeq : γ = ell*k)
    (hκ : 0 < κ) (hκeq : κ = 1-β-ell^2)
    (hU0eq : U0 = 1-α-2*γ*ell)
    (hη : 0 < η) (hηeq : η = 2*κ-β^2)
    (hνeq : ν = U0-2*α*β) (hstation : ν = 2*η*xstar)
    (hmargin : (1-c)^2/4+c*γ-3*γ^2/2 ≤ α^2)
    (hstage : ∀ r, 0 ≤ r → IsStageIII θ c b r (Y r) (Q r))
    (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hmax : ∀ r s, 0 ≤ r → 0 ≤ s →
      resellerProfit θ r s a b (Y r) ≤ resellerProfit θ x z a b (Y x)) :
    supplier1Profit θ c x z a (Y x) ≤ α^2+η*xstar^2 := by
  have hzbr : IsBestResponse (fun s ↦ resellerProfit θ x s a b (Y x)) z :=
    ⟨hz, fun s hs ↦ hmax x s hx hs⟩
  have hzQ : z = Q x := P087_reseller_order_eq_conjecture θ c b x (Y x) (Q x) a z
    (hstage x hx) hzbr
  let F := fun r ↦ resellerProfit θ r (Q r) a b (Y r)
  let P := fun r ↦ supplier1Profit θ c r (Q r) a (Y r)
  have hglobal : ∀ r, 0 ≤ r → F r ≤ F x := by
    intro r hr
    have hh := hmax r (Q r) hr (hstage r hr).2.1
    simpa only [F, hzQ] using hh
  have hbranches : ∀ r, 0 ≤ r →
      (r ≤ k → Y r = α-β*r ∧ Q r = γ-ell*r) ∧
      (k ≤ r → r ≤ 1-c → Y r = (1-c-r)/2 ∧ Q r = 0) ∧
      (1-c ≤ r → Y r = 0 ∧ Q r = 0) := by
    intro r hr
    exact P087_stageIII_three_branches θ c b α β γ ell k r (Y r) (Q r)
      hθ0 hθ1 hβ hell hkA hA hB hsA hsB hγeq (hstage r hr)
  have hγ : 0 ≤ γ := by rw [hγeq]; exact mul_nonneg hell hk.le
  have hcut : α-β*k = (1-c-k)/2 := by
    have hh : 2*(α-β*k) = (2*α+θ*γ)-(2*β+θ*ell)*k := by rw [hγeq]; ring
    rw [hA, hsA] at hh
    linarith
  have hjump : U0-2*κ*k < (1+c)/2-k := by
    rw [hU0eq, hκeq, hγeq]
    nlinarith [mul_pos (sub_pos.mpr hβhalf) hk]
  rw [hzQ]
  change P x ≤ α^2+η*xstar^2
  refine P087_supplier1_piecewise_bound a c (1-c) α β γ κ U0 η ν k xstar x F P
    ha hc rfl hγ hk hkA hκ hη hηeq hνeq hstation hjump hmargin ?_ ?_ ?_ ?_ ?_ hx hglobal
  · intro r hr hrk
    obtain ⟨hy, hq⟩ := (hbranches r hr).1 hrk
    dsimp only [F]
    rw [P087_resellerProfit_stageIII θ c b r (Y r) (Q r) a (hstage r hr), hy, hq,
      hU0eq, hκeq]
    ring
  · intro r hkr hrA
    have hr : 0 ≤ r := le_trans hk.le hkr
    obtain ⟨hy, hq⟩ := (hbranches r hr).2.1 hkr hrA
    dsimp only [F]
    rw [P087_resellerProfit_stageIII θ c b r (Y r) (Q r) a (hstage r hr), hy, hq]
    ring
  · intro r hAr
    have hr : 0 ≤ r := by linarith
    obtain ⟨hy, hq⟩ := (hbranches r hr).2.2 hAr
    dsimp only [F]
    rw [P087_resellerProfit_stageIII θ c b r (Y r) (Q r) a (hstage r hr), hy, hq]
    ring
  · intro r hr hrk
    have hy := ((hbranches r hr).1 hrk).1
    dsimp only [P]
    rw [P087_supplier1Profit_eq_square θ c b r (Y r) (Q r) a (hstage r hr), hy]
  · intro r hkr hrA
    have hr : 0 ≤ r := le_trans hk.le hkr
    have hy := ((hbranches r hr).2.1 hkr hrA).1
    dsimp only [P]
    rw [P087_supplier1Profit_eq_square θ c b r (Y r) (Q r) a (hstage r hr), hy]

theorem P087_supplier1_stationary_value (α β κ U0 η ν xstar a : ℝ)
    (hκ : η = 2*κ-β^2) (hν : ν = U0-2*α*β)
    (hstation : ν = 2*η*xstar) (ha : a = U0-2*κ*xstar) :
    (α-β*xstar)^2+a*xstar = α^2+η*xstar^2 := by
  rw [ha]
  nlinarith [congrArg (fun v : ℝ ↦ v*xstar) hν,
    congrArg (fun v : ℝ ↦ v*xstar) hstation,
    congrArg (fun v : ℝ ↦ v*xstar^2) hκ]

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087Supplier1Certificates -/

namespace NonExclEncroach.Channels
theorem P087_supplier1_margin_constant_nonneg (t : ℝ) (ht0 : 0 ≤ t) (ht9 : t ≤ 9/10) :
    0 ≤ -2 * t^9 - 4 * t^8 + 37 * t^7 - 24 * t^6 + 122 * t^5 + 48 * t^4 - 128 * t^3 + 352 * t^2 - 704 * t + 384 := by
  have htail : 0 ≤ 9-10*t := by linarith
  have hcert : 0 ≤
      128 * t^0 * (9-10*t)^9 +
      9408 * t^1 * (9-10*t)^8 +
      301344 * t^2 * (9-10*t)^7 +
      5472576 * t^3 * (9-10*t)^6 +
      61205136 * t^4 * (9-10*t)^5 +
      428034126 * t^5 * (9-10*t)^4 +
      1825897512 * t^6 * (9-10*t)^3 +
      4658799711 * t^7 * (9-10*t)^2 +
      8806648992 * t^8 * (9-10*t)^1 +
      16062090494 * t^9 * (9-10*t)^0 := by positivity
  have hid : 129140163 * (-2 * t^9 - 4 * t^8 + 37 * t^7 - 24 * t^6 + 122 * t^5 + 48 * t^4 - 128 * t^3 + 352 * t^2 - 704 * t + 384) =
      128 * t^0 * (9-10*t)^9 +
      9408 * t^1 * (9-10*t)^8 +
      301344 * t^2 * (9-10*t)^7 +
      5472576 * t^3 * (9-10*t)^6 +
      61205136 * t^4 * (9-10*t)^5 +
      428034126 * t^5 * (9-10*t)^4 +
      1825897512 * t^6 * (9-10*t)^3 +
      4658799711 * t^7 * (9-10*t)^2 +
      8806648992 * t^8 * (9-10*t)^1 +
      16062090494 * t^9 * (9-10*t)^0 := by ring
  nlinarith only [hcert, hid]

theorem P087_supplier1_margin_slope_nonneg (t : ℝ) (ht0 : 0 ≤ t) (ht9 : t ≤ 9/10) :
    0 ≤ -2 * t^9 + 8 * t^8 + 39 * t^7 - 44 * t^6 + 142 * t^5 - 208 * t^4 - 144 * t^3 + 192 * t^2 - 1088 * t + 1024 := by
  have htail : 0 ≤ 9-10*t := by linarith
  have hcert : 0 ≤
      1024 * t^0 * (9-10*t)^9 +
      82368 * t^1 * (9-10*t)^8 +
      2918592 * t^2 * (9-10*t)^7 +
      59582064 * t^3 * (9-10*t)^6 +
      766883952 * t^4 * (9-10*t)^5 +
      6375006558 * t^5 * (9-10*t)^4 +
      33471806916 * t^6 * (9-10*t)^3 +
      102245928471 * t^7 * (9-10*t)^2 +
      146483900388 * t^8 * (9-10*t)^1 +
      40663851802 * t^9 * (9-10*t)^0 := by positivity
  have hid : 387420489 * (-2 * t^9 + 8 * t^8 + 39 * t^7 - 44 * t^6 + 142 * t^5 - 208 * t^4 - 144 * t^3 + 192 * t^2 - 1088 * t + 1024) =
      1024 * t^0 * (9-10*t)^9 +
      82368 * t^1 * (9-10*t)^8 +
      2918592 * t^2 * (9-10*t)^7 +
      59582064 * t^3 * (9-10*t)^6 +
      766883952 * t^4 * (9-10*t)^5 +
      6375006558 * t^5 * (9-10*t)^4 +
      33471806916 * t^6 * (9-10*t)^3 +
      102245928471 * t^7 * (9-10*t)^2 +
      146483900388 * t^8 * (9-10*t)^1 +
      40663851802 * t^9 * (9-10*t)^0 := by ring
  nlinarith only [hcert, hid]

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087Supplier1Margin -/

namespace NonExclEncroach.Channels

/-- R&D parameters satisfy the margin used to rule out supplier-1 gains on the
zero-conjecture branch. The price hypothesis is the exact denominator-cleared
definition of `wRD2`; no threshold sign argument is assumed. -/
theorem P087_supplier1_RD_margin (t c b α γ : ℝ)
    (ht0 : 0 ≤ t) (ht9 : t ≤ 9/10) (hc : c ≤ 0) (hγ : 0 ≤ γ)
    (hd : 0 < 256+2*t^8-11*t^6-52*t^4+48*t^2)
    (hA : 2*α+t*γ = 1-c) (hB : 2*γ+t*α = 1-b)
    (hb : b*(256+2*t^8-11*t^6-52*t^4+48*t^2) =
      (1-t)*(8+t^2)*(16+t*(8-3*t^3-4*(1+t)*(2-t^2)*c+4*t))) :
    (1-c)^2/4+c*γ-3*γ^2/2 ≤ α^2 := by
  let d := 256+2*t^8-11*t^6-52*t^4+48*t^2
  let p0 := -2*t^9-4*t^8+37*t^7-24*t^6+122*t^5+48*t^4-128*t^3+352*t^2-704*t+384
  let pc := -2*t^9+8*t^8+39*t^7-44*t^6+142*t^5-208*t^4-144*t^3+192*t^2-1088*t+1024
  let S := (6-t^2)*γ-4*t*α-4*c
  have hD : 0 < 4-t^2 := by nlinarith [sq_nonneg t, sq_nonneg (t-1)]
  have hp0 : 0 ≤ p0 := P087_supplier1_margin_constant_nonneg t ht0 ht9
  have hpc : 0 ≤ pc := P087_supplier1_margin_slope_nonneg t ht0 ht9
  have heq : (4-t^2)*(d*S) = (4-t^2)*(p0-c*pc) := by
    dsimp only [d, S, p0, pc]
    linear_combination
      t*(t^2-14)*(256+2*t^8-11*t^6-52*t^4+48*t^2)*hA +
      (12+2*t^2)*(256+2*t^8-11*t^6-52*t^4+48*t^2)*hB -
      (12+2*t^2)*hb
  have hid : d*S = p0-c*pc := mul_left_cancel₀ (ne_of_gt hD) heq
  have hprod : 0 ≤ d*S := by
    rw [hid]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc hpc]
  have hS : 0 ≤ S := by
    by_contra hs
    have hneg := mul_neg_of_pos_of_neg hd (lt_of_not_ge hs)
    linarith
  have hbound := mul_nonneg hγ hS
  dsimp only [S] at hbound
  rw [← hA]
  nlinarith only [hbound]

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087EquilibriumAssembly -/

namespace NonExclEncroach.Channels

/-- Assemble all-price strategies from global reseller response certificates.
The selected equilibrium outcome is retained exactly. -/
theorem P087_equilibrium_of_global_certificates
    (θ c a b X Z : ℝ) (Y Q : ℝ → ℝ)
    (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hYcont : Continuous Y) (hYpos : ∀ x, 0 ≤ Y x)
    (hstage : ∀ x, 0 ≤ x → IsStageIII θ c b x (Y x) (Q x))
    (hX : 0 ≤ X) (hZ : 0 ≤ Z)
    (hbase : ∀ x z, 0 ≤ x → 0 ≤ z →
      resellerProfit θ x z a b (Y x) ≤ resellerProfit θ X Z a b (Y X))
    (hsupplier1 : ∀ a' x z, 0 ≤ a' → 0 ≤ x → 0 ≤ z →
      (∀ x' z', 0 ≤ x' → 0 ≤ z' →
        resellerProfit θ x' z' a' b (Y x') ≤ resellerProfit θ x z a' b (Y x)) →
      supplier1Profit θ c x z a' (Y x) ≤ supplier1Profit θ c X Z a (Y X))
    (hsupplier2 : ∀ v, 0 ≤ v → ∃ x z, 0 ≤ x ∧ 0 ≤ z ∧
      (∀ x' z', 0 ≤ x' → 0 ≤ z' →
        resellerProfit θ x' z' a v (Y x') ≤ resellerProfit θ x z a v (Y x)) ∧
      supplier2Profit z v ≤ supplier2Profit Z b) :
    ∃ σ : Profile, IsEquilibrium θ c σ ∧ σ.w1=a ∧ σ.w2=b ∧
      σ.q1=X ∧ σ.q2=Z ∧ σ.y=Y X := by
  classical
  have hRex : ∀ w1 w2 : ℝ, ∃ q : ℝ × ℝ,
      0 ≤ w1 → 0 ≤ w2 → 0 ≤ q.1 ∧ 0 ≤ q.2 ∧
      ∀ x z, 0 ≤ x → 0 ≤ z →
        resellerProfit θ x z w1 w2 (Y x) ≤ resellerProfit θ q.1 q.2 w1 w2 (Y q.1) := by
    intro w1 w2
    by_cases h1 : 0 ≤ w1
    · by_cases h2 : 0 ≤ w2
      · obtain ⟨x,z,hx,hz,hm⟩ := P087_reseller_exists θ w1 w2 hθ h1 h2 Y hYcont hYpos
        exact ⟨(x,z),fun _ _ => ⟨hx,hz,hm⟩⟩
      · exact ⟨(0,0),fun _ hh => (h2 hh).elim⟩
    · exact ⟨(0,0),fun hh _ => (h1 hh).elim⟩
  choose R0 hR0 using hRex
  have hSex : ∀ v : ℝ, ∃ q : ℝ × ℝ, 0 ≤ v →
      0 ≤ q.1 ∧ 0 ≤ q.2 ∧
      (∀ x z, 0 ≤ x → 0 ≤ z →
        resellerProfit θ x z a v (Y x) ≤ resellerProfit θ q.1 q.2 a v (Y q.1)) ∧
      supplier2Profit q.2 v ≤ supplier2Profit Z b := by
    intro v
    by_cases hv : 0 ≤ v
    · obtain ⟨x,z,hx,hz,hm,hp⟩ := hsupplier2 v hv
      exact ⟨(x,z),fun _ => ⟨hx,hz,hm,hp⟩⟩
    · exact ⟨(0,0),fun h => (hv h).elim⟩
  choose S hS using hSex
  let R : ℝ → ℝ → ℝ × ℝ := fun w1 w2 =>
    if w1=a then (if w2=b then (X,Z) else S w2) else R0 w1 w2
  have hRbase : R a b=(X,Z) := by simp [R]
  have hR : ∀ w1 w2, 0 ≤ w1 → 0 ≤ w2 →
      0 ≤ (R w1 w2).1 ∧ 0 ≤ (R w1 w2).2 ∧
      ∀ x z, 0 ≤ x → 0 ≤ z →
        resellerProfit θ x z w1 w2 (Y x) ≤
          resellerProfit θ (R w1 w2).1 (R w1 w2).2 w1 w2 (Y (R w1 w2).1) := by
    intro w1 w2 h1 h2
    by_cases h1a : w1=a
    · subst w1
      by_cases h2b : w2=b
      · subst w2
        simpa only [hRbase] using And.intro hX (And.intro hZ hbase)
      · simpa only [R,if_pos rfl,if_neg h2b] using
          And.intro (hS w2 h2).1 (And.intro (hS w2 h2).2.1 (hS w2 h2).2.2.1)
    · simpa only [R,if_neg h1a] using hR0 w1 w2 h1 h2
  let σ : Profile := ⟨a,b,Y,Q,R⟩
  have hq1 : σ.q1=X := by change (R a b).1=X; rw [hRbase]
  have hq2 : σ.q2=Z := by change (R a b).2=Z; rw [hRbase]
  have hy : σ.y=Y X := by change Y σ.q1=Y X; rw [hq1]
  refine ⟨σ,?_,rfl,rfl,hq1,hq2,hy⟩
  refine ⟨ha,hb,hstage,hR,?_,?_⟩
  · intro w1 hw1
    change supplier1Profit θ c (R w1 b).1 (R w1 b).2 w1 (Y (R w1 b).1) ≤
      supplier1Profit θ c (R a b).1 (R a b).2 a (Y (R a b).1)
    rw [hRbase]
    exact hsupplier1 w1 (R w1 b).1 (R w1 b).2 hw1 (hR w1 b hw1 hb).1
      (hR w1 b hw1 hb).2.1 (hR w1 b hw1 hb).2.2
  · intro v hv
    change supplier2Profit (R a v).2 v ≤ supplier2Profit (R a b).2 b
    rw [hRbase]
    by_cases hvb : v=b
    · subst v
      simp only [hRbase,le_refl]
    · simpa only [R,if_pos rfl,if_neg hvb] using (hS v hv).2.2.2

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087RDExistence -/

set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

namespace NonExclEncroach.Channels

/-- The complete negative-cost R&D equilibrium, including all off-path
stage rules and both suppliers' global wholesale-price deviations. -/
theorem P087_RD_equilibrium_exists (t c : ℝ) (ht0 : 0 < t) (ht9 : t ≤ 9/10)
    (hc2 : c2 t < c) (hc : c < 0) :
    ∃ σ, IsEquilibrium t c σ ∧ 0 < σ.q1 ∧ 0 < σ.y := by
  have ht1 : t < 1 := by linarith
  obtain ⟨hA,hB,hsA,hsB,hκ,hη,hr,hs⟩ := rd_coefficients t c ht0.le ht1
  obtain ⟨hβ,hβh,hell,hκp,hηp,hrp,hsp⟩ := rd_coefficient_signs t ht0 ht1
  have ha := rd_A_pos t c ht0 ht1 hc2 hc
  have hb := rdB_pos t c ht0.le ht1 hc.le
  have hX := rd_X_pos t c ht0.le ht1 hc2
  have hZ := rd_Z_pos t c ht0 ht1 hc.le
  have hY := rd_Y_pos t c ht0 ht1 hc2 hc
  have hk := rd_cutoff_pos t c ht0 ht1 hc2 hc.le
  have hkA := rd_cutoff_lt_A t c ht0 ht1 hc2 hc
  have hXk := rd_X_lt_cutoff t c ht0 ht1 hc.le
  have hgamma : 0 ≤ rdGamma t c := by
    rw [rd_cutoff_relation t c ht0 ht1]
    exact (mul_pos hell hk).le
  have hstage (x : ℝ) (_hx : 0 ≤ x) := P087_global_stageIII t c (wRD2 t c) x ht0.le ht1
  have hYX : P087_globalY t c (wRD2 t c) (rdX t c)=rdY t c :=
    ((rd_branch_formulas t c (rdX t c) ht0 ht1 hc2 hc hX.le).1 hXk.le).1
  have hQX : P087_globalQ t c (wRD2 t c) (rdX t c)=rdZ t c :=
    ((rd_branch_formulas t c (rdX t c) ht0 ht1 hc2 hc hX.le).1 hXk.le).2
  have hstageX := hstage (rdX t c) hX.le
  rw [hYX,hQX] at hstageX
  have haStation : wRD1 t c=rdU0 t c-2*rdKappa t*rdX t c := by
    have hx := rd_X_relation t c ht0 ht1
    rw [hs] at hx
    dsimp only [rdU,rdU0] at hx ⊢
    nlinarith only [hx]
  have hprofit1 : supplier1Profit t c (rdX t c) (rdZ t c) (wRD1 t c)
      (P087_globalY t c (wRD2 t c) (rdX t c))=(rdAlpha t c)^2+rdEta t*(rdX t c)^2 := by
    rw [hYX,P087_supplier1Profit_eq_square t c (wRD2 t c) (rdX t c) (rdY t c)
      (rdZ t c) (wRD1 t c) hstageX]
    exact P087_supplier1_stationary_value (rdAlpha t c) (rdBeta t) (rdKappa t)
      (rdU0 t c) (rdEta t) (rdNu t c) (rdX t c) (wRD1 t c)
      hη rfl (rd_supplier1_stationary t c ht0.le ht1) haStation
  have hbdef : wRD2 t c*rdP t=(1-t)*(8+t^2)*rdF t c := by
    change ((1-t)*(8+t^2)*rdF t c/rdP t)*rdP t=(1-t)*(8+t^2)*rdF t c
    exact div_mul_cancel₀ _ (rdP_pos t ht0.le ht1).ne'
  have hmargin := P087_supplier1_RD_margin t c (wRD2 t c) (rdAlpha t c) (rdGamma t c)
    ht0.le ht9 hc.le hgamma (rdP_pos t ht0.le ht1) hA hB hbdef
  have hprofit2 : supplier2Profit (rdZ t c) (wRD2 t c)=
      (2*rdR t/(4*rdR t-(rdS t)^2))*(wRD2 t c)^2 := by
    have hZeq : rdZ t c=rdR t*wRD2 t c/(2*rdKappa t) := by
      apply (eq_div_iff (show 2*rdKappa t ≠ 0 by positivity)).2
      nlinarith only [rd_Z_relation t c ht0 ht1]
    unfold supplier2Profit
    rw [hZeq,rd_det_formula t c ht0.le ht1]
    field_simp [ne_of_gt hκp]
    ring
  obtain ⟨σ,hEq,_,_,hσX,_,hσY⟩ := P087_equilibrium_of_global_certificates
    t c (wRD1 t c) (wRD2 t c) (rdX t c) (rdZ t c)
    (P087_globalY t c (wRD2 t c)) (P087_globalQ t c (wRD2 t c))
    ht0.le ha.le hb.le (P087_globalY_continuous t c (wRD2 t c))
    (P087_globalY_nonneg t c (wRD2 t c)) hstage hX.le hZ.le
    (rd_base_reseller_global t c ht0 ht9 hc2 hc) (by
      intro a x z ha' hx hz hm
      rw [hprofit1]
      exact P087_supplier1_global_bound t c (wRD2 t c) (rdAlpha t c) (rdBeta t)
        (rdGamma t c) (rdLambda t) (rdKappa t) (rdU0 t c) (rdEta t) (rdNu t c)
        (rdCutoff t c) (rdX t c) a x z (P087_globalY t c (wRD2 t c))
        (P087_globalQ t c (wRD2 t c)) ht0.le ht1 hc ha' hβ.le hβh hell.le hk hkA
        hA hB hsA hsB (rd_cutoff_relation t c ht0 ht1) hκp hκ rfl hηp hη rfl
        (rd_supplier1_stationary t c ht0.le ht1) hmargin hstage hx hz hm) (by
      intro v hv
      obtain ⟨x,z,hx,hz,_,hm,hp⟩ := rd_supplier2_response_exists t c ht0 ht9 hc2 hc v hv
      refine ⟨x,z,hx,hz,hm,?_⟩
      rw [hprofit2]
      exact hp)
  refine ⟨σ,hEq,?_,?_⟩
  · rw [hσX]
    exact hX
  · rw [hσY,hYX]
    exact hY

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087DirectOnlyBoundary -/

namespace NonExclEncroach.Channels

theorem P087_stageIII_direct_le_half (θ c b x y z : ℝ)
    (hθ : 0 ≤ θ) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (h : IsStageIII θ c b x y z) : y ≤ 1 / 2 := by
  obtain ⟨hy, hz, hys, hzs, hyc, hzc⟩ := P087_stageIII_complementarity θ c b x y z h
  by_cases hy0 : y = 0
  · rw [hy0]
    norm_num
  · have heq := (mul_eq_zero.mp hyc).resolve_left hy0
    nlinarith [mul_nonneg hθ hz]

theorem P087_stageIII_conjecture_le_half (θ c b x y z : ℝ)
    (hθ : 0 ≤ θ) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (h : IsStageIII θ c b x y z) : z ≤ 1 / 2 := by
  obtain ⟨hy, hz, hys, hzs, hyc, hzc⟩ := P087_stageIII_complementarity θ c b x y z h
  by_cases hz0 : z = 0
  · rw [hz0]
    norm_num
  · have heq := (mul_eq_zero.mp hzc).resolve_left hz0
    nlinarith [mul_nonneg hθ hy, mul_nonneg hθ hx]

/-- A sufficiently low second wholesale price forces a strictly positive order,
regardless of which global reseller maximizer is selected. -/
theorem P087_reseller_q2_pos_of_low_price (θ u v : ℝ) (Y : ℝ → ℝ) (x z : ℝ)
    (hθ : 0 ≤ θ) (hu : 0 ≤ u) (hv : v < 1 - 2 * θ)
    (hY0 : ∀ r, 0 ≤ r → 0 ≤ Y r) (hYhalf : ∀ r, 0 ≤ r → Y r ≤ 1 / 2)
    (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hopt : ∀ r s, 0 ≤ r → 0 ≤ s →
      resellerProfit θ r s u v (Y r) ≤ resellerProfit θ x z u v (Y x)) : 0 < z := by
  by_contra hnot
  have hz0 : z = 0 := le_antisymm (le_of_not_gt hnot) hz
  have hquad : IsBestResponse (fun s => s * ((1 - v - 2 * θ * x - θ * Y x) - s)) z :=
    (P087_reseller_quadratic_iff θ x u v (Y x) z).mp
      ⟨hz, fun s hs => hopt x s hx hs⟩
  have hslack := (P087_quadratic_necessary _ _ hquad).1
  rw [hz0] at hslack
  have hprofit := hopt 0 0 (le_refl 0) (le_refl 0)
  rw [hz0] at hprofit
  dsimp only [resellerProfit, p1, p2] at hprofit
  have hsum : 2 * x + Y x ≤ 2 := by
    by_cases hx0 : x = 0
    · rw [hx0]
      have hy := hYhalf 0 (le_refl 0)
      linarith
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      have hp : 0 ≤ x * (1 - x - Y x - u) := by nlinarith only [hprofit]
      have hm : 0 ≤ 1 - x - Y x - u := nonneg_of_mul_nonneg_right hp hxpos
      have hy := hY0 x hx
      linarith
  have hm := mul_nonneg hθ (sub_nonneg.mpr hsum)
  nlinarith

/-- In the positive-cost regime relevant to the root, supplier 2 must have both
a positive quantity and a positive price. The profitable deviation is uniform over
all global reseller tie selections. -/
theorem P087_equilibrium_q2_and_w2_pos (θ c : ℝ) (σ : Profile)
    (hθ0 : 0 ≤ θ) (hθhalf : θ < 1 / 2) (hc : 0 ≤ c)
    (hEq : IsEquilibrium θ c σ) : 0 < σ.q2 ∧ 0 < σ.w2 := by
  let v := (1 - 2 * θ) / 2
  have hv : 0 < v := by dsimp [v]; linarith
  have hvlow : v < 1 - 2 * θ := by dsimp [v]; linarith
  have hY0 : ∀ r, 0 ≤ r → 0 ≤ σ.Y r := fun r hr => (hEq.2.2.1 r hr).1.1
  have hYhalf : ∀ r, 0 ≤ r → σ.Y r ≤ 1 / 2 := by
    intro r hr
    exact P087_stageIII_direct_le_half θ c σ.w2 r (σ.Y r) (σ.Q2c r)
      hθ0 hc hr (hEq.2.2.1 r hr)
  have horders := hEq.2.2.2.1 σ.w1 v hEq.1 hv.le
  have hzpos := P087_reseller_q2_pos_of_low_price θ σ.w1 v σ.Y
    (σ.R σ.w1 v).1 (σ.R σ.w1 v).2 hθ0 hEq.1 hvlow hY0 hYhalf
    horders.1 horders.2.1 horders.2.2
  have hbest := hEq.2.2.2.2.2 v hv.le
  change (σ.R σ.w1 v).2 * v ≤ σ.q2 * σ.w2 at hbest
  have hp : 0 < σ.q2 * σ.w2 := (mul_pos hzpos hv).trans_le hbest
  rcases mul_pos_iff.mp hp with h | h
  · exact h
  · linarith [hEq.2.1, h.2]

/-- If the direct channel is inactive at `x`, decreasing the observed first order
by `x-r` can raise the direct response by at most half that amount. -/
theorem P087_stageIII_zero_left_bound (θ c b : ℝ) (Y Q : ℝ → ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hstage : ∀ r, 0 ≤ r → IsStageIII θ c b r (Y r) (Q r))
    (x r : ℝ) (hr : 0 ≤ r) (hrx : r ≤ x) (hyzero : Y x = 0) :
    Y r ≤ (x - r) / 2 := by
  have hd : 0 < 4 - θ ^ 2 := by nlinarith [sq_nonneg θ, sq_nonneg (θ - 1)]
  have hxcoord := (P087_stageIII_coordinates θ c b x (Y x) (Q x)
    hθ0 hθ1 (hstage x (hr.trans hrx))).1
  have hrcoord := (P087_stageIII_coordinates θ c b r (Y r) (Q r)
    hθ0 hθ1 (hstage r hr)).1
  have hmin : min ((1 - c - x) / 2)
      ((2 * (1 - c - x) - θ * (1 - b - 2 * θ * x)) / (4 - θ ^ 2)) ≤ 0 := by
    have hh := le_max_right 0 (min ((1 - c - x) / 2)
      ((2 * (1 - c - x) - θ * (1 - b - 2 * θ * x)) / (4 - θ ^ 2)))
    rw [← hxcoord, hyzero] at hh
    exact hh
  rw [hrcoord]
  apply max_le (by linarith)
  rcases min_le_iff.mp hmin with h | h
  · apply (min_le_left _ _).trans
    linarith
  · apply (min_le_right _ _).trans
    apply (div_le_iff₀ hd).mpr
    have hn := (div_le_iff₀ hd).mp h
    nlinarith [mul_nonneg (sq_nonneg θ) (sub_nonneg.mpr hrx)]

/-- A finite decrease of the first order rules out an inactive direct channel.
The hypotheses isolate exactly the two stage-response facts used by the deviation. -/
theorem P087_reseller_y_pos_of_zero_slack (θ c u v : ℝ) (Y : ℝ → ℝ) (x z : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hc : c < 1 / 3) (hu : 0 ≤ u)
    (hx : 0 ≤ x) (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (hy : 0 ≤ Y x)
    (hslack : Y x = 0 → 1 - c ≤ x + θ * z)
    (hleft : ∀ r, 0 ≤ r → r ≤ x → Y x = 0 → Y r ≤ (x - r) / 2)
    (hopt : ∀ r s, 0 ≤ r → 0 ≤ s →
      resellerProfit θ r s u v (Y r) ≤ resellerProfit θ x z u v (Y x)) : 0 < Y x := by
  by_contra hynot
  have hyzero : Y x = 0 := le_antisymm (le_of_not_gt hynot) hy
  have hys := hslack hyzero
  have hxpos : 0 < x := by
    by_contra hxnot
    have hxzero : x = 0 := le_antisymm (le_of_not_gt hxnot) hx
    rw [hxzero] at hys
    nlinarith [mul_nonneg (sub_nonneg.mpr hθ1.le) hz]
  let ε := min (x / 2) ((1 - 3 * c) / 2)
  have heps : 0 < ε := lt_min (by linarith) (by linarith)
  have hepsx : ε ≤ x / 2 := min_le_left _ _
  have hepsc : ε ≤ (1 - 3 * c) / 2 := min_le_right _ _
  have hr : 0 ≤ x - ε := by linarith
  have hrx : x - ε ≤ x := by linarith
  have hyR : Y (x - ε) ≤ ε / 2 := by
    have h := hleft (x - ε) hr hrx hyzero
    have hsimp : x - (x - ε) = ε := by ring
    simpa only [hsimp] using h
  have hcoeff : 0 ≤ (x - ε) + θ * z := add_nonneg hr (mul_nonneg hθ0 hz)
  have hmY := mul_le_mul_of_nonneg_left hyR hcoeff
  have hgap : 0 < 1 - 3 * c - ε := by linarith
  have hpositive := mul_pos heps hgap
  have hscaled := mul_nonneg heps.le (sub_nonneg.mpr hys)
  have hprice := mul_nonneg heps.le hu
  have hprofit := hopt (x - ε) z hr hz
  rw [hyzero] at hprofit
  dsimp only [resellerProfit, p1, p2] at hprofit
  nlinarith only [hprofit, hmY, hpositive, hscaled, hprice]

/-- Every global reseller maximizer at the believed second price keeps the direct
channel active when `c < 1/3`. This statement covers every maximizing tie selection
and uses no supplier best-response conditions. -/
theorem P087_consistent_reseller_y_pos (θ c b u : ℝ) (Y Q : ℝ → ℝ) (x z : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hc : c < 1 / 3)
    (hb : 0 ≤ b) (hu : 0 ≤ u)
    (hstage : ∀ r, 0 ≤ r → IsStageIII θ c b r (Y r) (Q r))
    (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hopt : ∀ r s, 0 ≤ r → 0 ≤ s →
      resellerProfit θ r s u b (Y r) ≤ resellerProfit θ x z u b (Y x)) : 0 < Y x := by
  have hactual : IsStageIII θ c b x (Y x) z :=
    P087_reseller_optimum_stageIII θ c b x (Y x) (Q x) u z (hstage x hx)
      ⟨hz, fun r hr => hopt x r hx hr⟩
  obtain ⟨hy, hz', hys, hzs, hyc, hzc⟩ :=
    P087_stageIII_complementarity θ c b x (Y x) z hactual
  have hzhalf := P087_stageIII_conjecture_le_half θ c b x (Y x) z hθ0 hb hx hactual
  apply P087_reseller_y_pos_of_zero_slack θ c u b Y x z hθ0 hθ1 hc hu hx hz hzhalf hy
  · intro hyzero
    rw [hyzero] at hys
    linarith
  · intro r hr hrx hyzero
    exact P087_stageIII_zero_left_bound θ c b Y Q hθ0 hθ1 hstage x r hr hrx hyzero
  · exact hopt

/-- A direct-channel zero is impossible in any equilibrium with cost below `1/3`. -/
theorem P087_equilibrium_y_pos (θ c : ℝ) (σ : Profile)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hc : c < 1 / 3)
    (hEq : IsEquilibrium θ c σ) : 0 < σ.y := by
  have horders := hEq.2.2.2.1 σ.w1 σ.w2 hEq.1 hEq.2.1
  exact P087_consistent_reseller_y_pos θ c σ.w2 σ.w1 σ.Y σ.Q2c σ.q1 σ.q2
    hθ0 hθ1 hc hEq.2.1 hEq.1 hEq.2.2.1 horders.1 horders.2.1 horders.2.2

theorem P087_c2_lt_one_third (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) : c2 θ < 1 / 3 := by
  have h2 : θ ^ 2 ≤ 1 := pow_le_one₀ hθ0 hθ1.le
  have h4 : θ ^ 4 ≤ 1 := pow_le_one₀ hθ0 hθ1.le
  have h6 : θ ^ 6 ≤ 1 := pow_le_one₀ hθ0 hθ1.le
  have hH : 99 ≤ 128 - 16 * θ ^ 2 - 13 * θ ^ 4 := by linarith
  have hH0 : 0 ≤ 128 - 16 * θ ^ 2 - 13 * θ ^ 4 := by linarith
  have hden : 198 ≤ 2 * (1 + θ) * (128 - 16 * θ ^ 2 - 13 * θ ^ 4) := by
    nlinarith [mul_nonneg hθ0 hH0]
  have hN : 32 * θ - 80 * θ ^ 2 - 32 * θ ^ 3 - 14 * θ ^ 4 - 8 * θ ^ 5 +
      4 * θ ^ 6 - θ ^ 7 ≤ 36 := by
    nlinarith [pow_nonneg hθ0 2, pow_nonneg hθ0 3, pow_nonneg hθ0 4,
      pow_nonneg hθ0 5, pow_nonneg hθ0 7]
  unfold c2
  apply (div_lt_iff₀ (by linarith : 0 < 2 * (1 + θ) * (128 - 16 * θ ^ 2 - 13 * θ ^ 4))).mpr
  nlinarith only [hden, hN]

theorem P087_num1_root_lt_half (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hnum : num1 t = 0) : t < 1 / 2 := by
  by_contra hn
  have h5 : t ^ 5 ≤ 1 := pow_le_one₀ ht0 ht1.le
  unfold num1 at hnum
  have ht : 1 / 2 ≤ t := le_of_not_gt hn
  nlinarith [pow_nonneg ht0 2, pow_nonneg ht0 3, pow_nonneg ht0 4, pow_nonneg ht0 6]

/-- The exact positive-cost regime of the mission forces all quantities except the
first reseller order to be strictly positive, without any selection convention. -/
theorem P087_root_positive_interior (t θ c : ℝ) (σ : Profile)
    (ht0 : 0 < t) (ht1 : t < 1) (hnum : num1 t = 0)
    (hθ0 : 0 < θ) (hθt : θ < t) (hc0 : 0 < c) (hc2 : c ≤ c2 θ)
    (hEq : IsEquilibrium θ c σ) : 0 < σ.y ∧ 0 < σ.q2 ∧ 0 < σ.w2 := by
  have hθ1 := hθt.trans ht1
  have hθhalf := hθt.trans (P087_num1_root_lt_half t ht0.le ht1 hnum)
  have hc3 := hc2.trans_lt (P087_c2_lt_one_third θ hθ0.le hθ1)
  exact ⟨P087_equilibrium_y_pos θ c σ hθ0.le hθ1 hc3 hEq,
    P087_equilibrium_q2_and_w2_pos θ c σ hθ0.le hθhalf hc0.le hEq⟩

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087DirectOnlyPriceCut -/

namespace NonExclEncroach.Channels

/-- Conditional second-product demand rises by at most half a price cut. -/
theorem P087_price_cut_order_bounds (θ c b u v x y q z : ℝ)
    (hv : v ≤ b) (hstage : IsStageIII θ c b x y q)
    (hopt : IsBestResponse (fun s => resellerProfit θ x s u v y) z) :
    q ≤ z ∧ z ≤ q + (b-v)/2 := by
  have hq := P087_quadratic_optimizer _ q
    ((P087_reseller_quadratic_iff θ x 0 b y q).mp hstage.2)
  have hz := P087_quadratic_optimizer _ z
    ((P087_reseller_quadratic_iff θ x u v y z).mp hopt)
  have hq0 : 0 ≤ q := hstage.2.1
  have hqA : (1-b-2*θ*x-θ*y)/2 ≤ q := by
    rw [hq]
    exact le_max_left _ _
  constructor
  · rw [hq, hz]
    exact max_le_max (by linarith) (le_refl 0)
  · rw [hz]
    exact max_le (by linarith) (by linarith)

/-- Revealed preference forces the second order to weakly increase after a
strict second-price cut, even with arbitrary choices among global maximizers. -/
theorem P087_price_cut_revealed_preference (θ u b v x z y X Z Y : ℝ)
    (hv : v < b)
    (hold : resellerProfit θ X Z u b Y ≤ resellerProfit θ x z u b y)
    (hnew : resellerProfit θ x z u v y ≤ resellerProfit θ X Z u v Y) : z ≤ Z := by
  have hp : 0 ≤ (b-v)*(Z-z) := by
    dsimp only [resellerProfit, p1, p2] at hold hnew
    nlinarith only [hold, hnew]
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hp (sub_pos.mpr hv))

/-- The direct channel stays active after a nonnegative second-price cut. -/
theorem P087_reseller_y_pos_of_price_cut (θ c b u v : ℝ) (Y Q : ℝ → ℝ) (x z : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hc : c < 1/3)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hvb : v ≤ b)
    (hstage : ∀ r, 0 ≤ r → IsStageIII θ c b r (Y r) (Q r))
    (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hopt : ∀ r s, 0 ≤ r → 0 ≤ s →
      resellerProfit θ r s u v (Y r) ≤ resellerProfit θ x z u v (Y x)) : 0 < Y x := by
  have hcond : IsBestResponse (fun s => resellerProfit θ x s u v (Y x)) z :=
    ⟨hz, fun s hs => hopt x s hx hs⟩
  have hbounds := P087_price_cut_order_bounds θ c b u v x (Y x) (Q x) z hvb
    (hstage x hx) hcond
  obtain ⟨hy, hq, hys, hqs, hyc, hqc⟩ :=
    P087_stageIII_complementarity θ c b x (Y x) (Q x) (hstage x hx)
  have hquad := (P087_reseller_quadratic_iff θ x u v (Y x) z).mp hcond
  have hcomp := P087_quadratic_necessary _ _ hquad
  have hzhalf : z ≤ 1/2 := by
    by_cases hz0 : z = 0
    · rw [hz0]
      norm_num
    · have heq := (mul_eq_zero.mp hcomp.2).resolve_left hz0
      nlinarith [mul_nonneg hθ0 hx, mul_nonneg hθ0 hy]
  apply P087_reseller_y_pos_of_zero_slack θ c u v Y x z hθ0 hθ1 hc hu hx hz hzhalf hy
  · intro hy0
    rw [hy0] at hys
    nlinarith [mul_nonneg hθ0 (sub_nonneg.mpr hbounds.1)]
  · intro r hr hrx hy0
    exact P087_stageIII_zero_left_bound θ c b Y Q hθ0 hθ1 hstage x r hr hrx hy0
  · exact hopt

/-- An active stage-III response is affine between any two active observations. -/
theorem P087_active_stage_affine (θ c b β ell x y z X Y Z : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hβ : 2*β+θ*ell = 1) (hell : 2*ell+θ*β = 2*θ)
    (hold : IsStageIII θ c b x y z) (hnew : IsStageIII θ c b X Y Z)
    (hy : 0 < y) (hz : 0 < z) (hY : 0 < Y) (hZ : 0 < Z) :
    Y = y+β*(x-X) ∧ Z = z+ell*(x-X) := by
  obtain ⟨_, _, _, _, hyc, hzc⟩ := P087_stageIII_complementarity θ c b x y z hold
  obtain ⟨_, _, _, _, hYc, hZc⟩ := P087_stageIII_complementarity θ c b X Y Z hnew
  have hyE := (mul_eq_zero.mp hyc).resolve_left (ne_of_gt hy)
  have hzE := (mul_eq_zero.mp hzc).resolve_left (ne_of_gt hz)
  have hYE := (mul_eq_zero.mp hYc).resolve_left (ne_of_gt hY)
  have hZE := (mul_eq_zero.mp hZc).resolve_left (ne_of_gt hZ)
  have hd : 4-θ^2 ≠ 0 := by nlinarith [sq_nonneg (θ-1)]
  constructor
  · apply (mul_left_cancel₀ hd)
    linear_combination 2*hYE-2*hyE-θ*hZE+θ*hzE-(x-X)*(2*hβ-θ*hell)
  · apply (mul_left_cancel₀ hd)
    linear_combination 2*hZE-2*hzE-θ*hYE+θ*hyE-(x-X)*(2*hell-θ*hβ)

/-- An active response remains on its affine branch at every lower observation. -/
theorem P087_stage_affine_left (θ c b β ell : ℝ) (Y Q : ℝ → ℝ) (x y z : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ : 0 ≤ β) (hell : 0 ≤ ell)
    (hsA : 2*β+θ*ell = 1) (hsB : 2*ell+θ*β = 2*θ)
    (hstage : ∀ r, 0 ≤ r → IsStageIII θ c b r (Y r) (Q r))
    (hbase : IsStageIII θ c b x y z) (hy : 0 < y) (hz : 0 < z)
    (r : ℝ) (hr : 0 ≤ r) (hrx : r ≤ x) :
    Y r = y+β*(x-r) ∧ Q r = z+ell*(x-r) := by
  obtain ⟨_, _, _, _, hyc, hzc⟩ := P087_stageIII_complementarity θ c b x y z hbase
  have hA : 2*y+θ*z = 1-c-x :=
    sub_eq_zero.mp ((mul_eq_zero.mp hyc).resolve_left (ne_of_gt hy))
  have hB : 2*z+θ*y = 1-b-2*θ*x :=
    sub_eq_zero.mp ((mul_eq_zero.mp hzc).resolve_left (ne_of_gt hz))
  have hyr : 0 ≤ y+β*(x-r) := by nlinarith [mul_nonneg hβ (sub_nonneg.mpr hrx)]
  have hzr : 0 ≤ z+ell*(x-r) := by nlinarith [mul_nonneg hell (sub_nonneg.mpr hrx)]
  have hAr : 2*(y+β*(x-r))+θ*(z+ell*(x-r)) = 1-c-r := by
    calc
      _ = (2*y+θ*z)+(2*β+θ*ell)*(x-r) := by ring
      _ = _ := by rw [hA, hsA]; ring
  have hBr : 2*(z+ell*(x-r))+θ*(y+β*(x-r)) = 1-b-2*θ*r := by
    calc
      _ = (2*z+θ*y)+(2*ell+θ*β)*(x-r) := by ring
      _ = _ := by rw [hB, hsB]; ring
  have hcand := P087_stageIII_of_complementarity θ c b r _ _ hyr hzr hAr.ge hBr.ge
    (by rw [hAr]; ring) (by rw [hBr]; ring)
  exact P087_stageIII_unique θ c b r _ _ _ _ hθ0 hθ1 (hstage r hr) hcand

theorem P087_affine_reseller_formula (θ β ell α u v X Z : ℝ)
    (hell : 2*ell+θ*β = 2*θ) :
    resellerProfit θ X Z u v (α-β*X) =
      (1-u-α)*X+(1-v-θ*α)*Z-(1-β)*X^2-Z^2-2*ell*X*Z := by
  dsimp only [resellerProfit, p1, p2]
  linear_combination X*Z*hell

/-- The strict quadratic vertex is unique over the whole plane. -/
theorem P087_strict_quadratic_vertex_unique (r ell κ U V x z X Z : ℝ)
    (hκ : 0 < κ) (hκeq : κ = r-ell^2)
    (hU : U = 2*r*x+2*ell*z) (hV : V = 2*z+2*ell*x)
    (hopt : U*x+V*z-r*x^2-z^2-2*ell*x*z ≤
      U*X+V*Z-r*X^2-Z^2-2*ell*X*Z) : X = x ∧ Z = z := by
  have hid : (U*x+V*z-r*x^2-z^2-2*ell*x*z)-
      (U*X+V*Z-r*X^2-Z^2-2*ell*X*Z) =
      κ*(X-x)^2+((Z-z)+ell*(X-x))^2 := by
    rw [hU, hV, hκeq]
    ring
  have hnonneg := sq_nonneg ((Z-z)+ell*(X-x))
  have hxsq : (X-x)^2 = 0 := by
    have hxnonneg := sq_nonneg (X-x)
    nlinarith
  have hx : X = x := sub_eq_zero.mp (sq_eq_zero_iff.mp hxsq)
  rw [hx] at hid hopt
  constructor
  · exact hx
  · have hzsq : (Z-z)^2 = 0 := by nlinarith [sq_nonneg (Z-z)]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hzsq)

/-- Every reseller selector follows the same interior branch after a sufficiently
small second-price cut. The proof first excludes all inactive remote branches. -/
theorem P087_price_cut_response_param (θ c b u β ell κ L G : ℝ)
    (Y Q : ℝ → ℝ) (x z t X Z : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hc : c < 1/3)
    (hu : 0 ≤ u) (hβ : 0 ≤ β) (hell : 0 ≤ ell)
    (hsA : 2*β+θ*ell = 1) (hsB : 2*ell+θ*β = 2*θ)
    (hκ : 0 < κ) (hκeq : κ = 1-β-ell^2)
    (hL : 0 ≤ L) (hG : 0 ≤ G)
    (hLG : (1-β)*L = ell*G) (hGL : 2*G-2*ell*L = 1)
    (hstage : ∀ r, 0 ≤ r → IsStageIII θ c b r (Y r) (Q r))
    (hbase : IsStageIII θ c b x (Y x) z)
    (hx : 0 < x) (hy : 0 < Y x) (hz : 0 < z)
    (hFOC : 1-u-Y x = (2-β)*x+2*ell*z)
    (hmax : ∀ r s, 0 ≤ r → 0 ≤ s →
      resellerProfit θ r s u b (Y r) ≤ resellerProfit θ x z u b (Y x))
    (ht : 0 < t) (htb : t ≤ b) (htz : t < 2*z) (htx : L*t ≤ x)
    (hX : 0 ≤ X) (hZ : 0 ≤ Z)
    (hnew : ∀ r s, 0 ≤ r → 0 ≤ s →
      resellerProfit θ r s u (b-t) (Y r) ≤ resellerProfit θ X Z u (b-t) (Y X)) :
    X = x-L*t ∧ Z = z+G*t := by
  have hZz : z ≤ Z := P087_price_cut_revealed_preference θ u b (b-t) x z (Y x) X Z (Y X)
    (by linarith) (hmax X Z hX hZ) (hnew x z hx.le hz.le)
  have hcond : IsBestResponse (fun s => resellerProfit θ X s u (b-t) (Y X)) Z :=
    ⟨hZ, fun s hs => hnew X s hX hs⟩
  have hbnd := P087_price_cut_order_bounds θ c b u (b-t) X (Y X) (Q X) Z
    (by linarith) (hstage X hX) hcond
  have hQpos : 0 < Q X := by nlinarith only [hbnd.2, hZz, htz]
  have hYpos := P087_reseller_y_pos_of_price_cut θ c b u (b-t) Y Q X Z
    hθ0 hθ1 hc hu (by linarith) (by linarith) hstage hX hZ hnew
  have hactive := P087_active_stage_affine θ c b β ell x (Y x) z X (Y X) (Q X)
    hθ0 hθ1 hsA hsB hbase (hstage X hX) hy hz hYpos hQpos
  have hcandidate0 : 0 ≤ x-L*t := by linarith
  have hcandidatex : x-L*t ≤ x := by nlinarith only [mul_nonneg hL ht.le]
  have hcand := P087_stage_affine_left θ c b β ell Y Q x (Y x) z
    hθ0 hθ1 hβ hell hsA hsB hstage hbase hy hz
    (x-L*t) hcandidate0 hcandidatex
  let α := Y x+β*x
  have hYform : Y X = α-β*X := by dsimp [α]; nlinarith only [hactive.1]
  have hcandform : Y (x-L*t) = α-β*(x-L*t) := by
    dsimp [α]
    nlinarith only [hcand.1]
  have hcandZ : 0 ≤ z+G*t := by positivity
  have hcomparison := hnew (x-L*t) (z+G*t) hcandidate0 hcandZ
  rw [hYform, hcandform, P087_affine_reseller_formula θ β ell α u (b-t) _ _ hsB,
    P087_affine_reseller_formula θ β ell α u (b-t) _ _ hsB] at hcomparison
  have hU : 1-u-α = 2*(1-β)*(x-L*t)+2*ell*(z+G*t) := by
    dsimp [α]
    linear_combination hFOC+2*t*hLG
  obtain ⟨_, _, _, _, _, hzc⟩ := P087_stageIII_complementarity θ c b x (Y x) z hbase
  have hzE := (mul_eq_zero.mp hzc).resolve_left (ne_of_gt hz)
  have hV : 1-(b-t)-θ*α = 2*(z+G*t)+2*ell*(x-L*t) := by
    dsimp [α]
    linear_combination -hzE-x*hsB-t*hGL
  exact P087_strict_quadratic_vertex_unique (1-β) ell κ (1-u-α) (1-(b-t)-θ*α)
    (x-L*t) (z+G*t) X Z hκ hκeq hU hV hcomparison

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087DirectOnlyLocal -/

open Filter Topology

namespace NonExclEncroach.Channels

/-- When both stage-III channels are active, their unique global response agrees
locally with the interior affine response. This derives differentiability from the
actual strategy requirements, without assuming a formula for the strategy. -/
theorem P087_stageIII_Y_hasDerivAt (θ c b : ℝ) (Y Q : ℝ → ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hstage : ∀ r, 0 ≤ r → IsStageIII θ c b r (Y r) (Q r))
    (x : ℝ) (hx : 0 < x) (hy : 0 < Y x) (hz : 0 < Q x) :
    HasDerivAt Y (-(2 * (1 - θ ^ 2) / (4 - θ ^ 2))) x := by
  let B := 2 * (1 - θ ^ 2) / (4 - θ ^ 2)
  let D := 3 * θ / (4 - θ ^ 2)
  let g : ℝ → ℝ := fun r => Y x - B * (r - x)
  let h : ℝ → ℝ := fun r => Q x - D * (r - x)
  have hd : 0 < 4 - θ ^ 2 := by
    nlinarith [sq_nonneg θ, sq_nonneg (θ - 1)]
  have hB : 2 * B + θ * D = 1 := by
    dsimp [B, D]
    field_simp
    <;> ring
  have hD : 2 * D + θ * B = 2 * θ := by
    dsimp [B, D]
    field_simp
    <;> ring
  obtain ⟨hy0, hz0, hys, hzs, hyc, hzc⟩ :=
    P087_stageIII_complementarity θ c b x (Y x) (Q x) (hstage x hx.le)
  have hyEq : 2 * Y x + θ * Q x = 1 - c - x :=
    sub_eq_zero.mp ((mul_eq_zero.mp hyc).resolve_left (ne_of_gt hy))
  have hzEq : 2 * Q x + θ * Y x = 1 - b - 2 * θ * x :=
    sub_eq_zero.mp ((mul_eq_zero.mp hzc).resolve_left (ne_of_gt hz))
  have hgcont : Continuous g := by dsimp [g]; fun_prop
  have hhcont : Continuous h := by dsimp [h]; fun_prop
  have hgpos : 0 < g x := by simpa [g] using hy
  have hhpos : 0 < h x := by simpa [h] using hz
  have hzero : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x := continuousAt_const
  have hnearG := hzero.eventually_lt hgcont.continuousAt hgpos
  have hnearH := hzero.eventually_lt hhcont.continuousAt hhpos
  have heq : Y =ᶠ[𝓝 x] g := by
    filter_upwards [eventually_gt_nhds hx, hnearG, hnearH] with r hr hgr hhr
    have hyR : 2 * g r + θ * h r = 1 - c - r := by
      calc
        2 * g r + θ * h r = (2 * Y x + θ * Q x) - (2 * B + θ * D) * (r - x) := by
          dsimp [g, h]
          ring
        _ = 1 - c - r := by rw [hyEq, hB]; ring
    have hzR : 2 * h r + θ * g r = 1 - b - 2 * θ * r := by
      calc
        2 * h r + θ * g r = (2 * Q x + θ * Y x) - (2 * D + θ * B) * (r - x) := by
          dsimp [g, h]
          ring
        _ = 1 - b - 2 * θ * r := by rw [hzEq, hD]; ring
    have hcand : IsStageIII θ c b r (g r) (h r) :=
      P087_stageIII_of_complementarity θ c b r (g r) (h r) hgr.le hhr.le
        hyR.ge hzR.ge (by rw [hyR]; ring) (by rw [hzR]; ring)
    exact (P087_stageIII_unique θ c b r (Y r) (Q r) (g r) (h r)
      hθ0 hθ1 (hstage r hr.le) hcand).1
  have hgder : HasDerivAt g (-B) x := by
    simpa [g] using (((hasDerivAt_id x).sub_const x).const_mul B).const_sub (Y x)
  exact hgder.congr_of_eventuallyEq heq

/-- The reseller's interior first-order condition follows from global equilibrium
optimality and the locally derived stage-III response. -/
theorem P087_equilibrium_reseller_FOC (θ c : ℝ) (σ : Profile)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hEq : IsEquilibrium θ c σ)
    (hx : 0 < σ.q1) (hy : 0 < σ.y) (hz : 0 < σ.q2) :
    (4 - θ ^ 2) * (1 - σ.w1 - σ.y) = 6 * (σ.q1 + θ * σ.q2) := by
  let B := 2 * (1 - θ ^ 2) / (4 - θ ^ 2)
  have hconj : σ.q2 = σ.Q2c σ.q1 :=
    P087_consistent_reseller_order θ c σ hEq σ.w1 hEq.1
  have hY : HasDerivAt σ.Y (-B) σ.q1 :=
    P087_stageIII_Y_hasDerivAt θ c σ.w2 σ.Y σ.Q2c hθ0 hθ1 hEq.2.2.1
      σ.q1 hx hy (by rw [← hconj]; exact hz)
  let f : ℝ → ℝ := fun r => resellerProfit θ r σ.q2 σ.w1 σ.w2 (σ.Y r)
  have hid := hasDerivAt_id (𝕜 := ℝ) σ.q1
  have hfirst := ((((hasDerivAt_const σ.q1 (1 : ℝ)).sub hid).sub_const
    (θ * σ.q2)).sub hY).sub_const σ.w1
  have hsecond := (((hasDerivAt_const σ.q1 (1 - σ.q2)).sub
    (hid.const_mul θ)).sub (hY.const_mul θ)).sub_const σ.w2
  have hf : HasDerivAt f
      (1 - σ.w1 - 2 * σ.q1 - 2 * θ * σ.q2 - σ.y + B * (σ.q1 + θ * σ.q2)) σ.q1 := by
    convert! (hid.mul hfirst).add (hsecond.const_mul σ.q2) using 1 <;>
      simp [f, resellerProfit, p1, p2, Profile.y] <;> ring
  have horders := hEq.2.2.2.1 σ.w1 σ.w2 hEq.1 hEq.2.1
  have hmax : IsMaxOn f (Set.Ici 0) σ.q1 := by
    intro r hr
    exact horders.2.2 r σ.q2 hr hz.le
  have hzero := (hmax.isLocalMax (Ici_mem_nhds hx)).hasDerivAt_eq_zero hf
  have hd : 0 < 4 - θ ^ 2 := by nlinarith [sq_nonneg θ, sq_nonneg (θ - 1)]
  have hcoef : B * (4 - θ ^ 2) = 2 * (1 - θ ^ 2) := by
    dsimp [B]
    field_simp
  linear_combination (4 - θ ^ 2) * hzero - (σ.q1 + θ * σ.q2) * hcoef

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087DirectOnlySupplier2 -/

namespace NonExclEncroach.Channels

/-- The one-sided supplier-2 necessary inequality follows from price cuts. All
reseller selectors are covered by the preceding global branch argument. -/
theorem P087_supplier2_necessary_param (θ c β ell κ L G : ℝ) (σ : Profile)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hc : c < 1/3)
    (hβ : 0 ≤ β) (hell : 0 ≤ ell)
    (hsA : 2*β+θ*ell = 1) (hsB : 2*ell+θ*β = 2*θ)
    (hκ : 0 < κ) (hκeq : κ = 1-β-ell^2)
    (hL : 0 ≤ L) (hG : 0 < G)
    (hLG : (1-β)*L = ell*G) (hGL : 2*G-2*ell*L = 1)
    (hEq : IsEquilibrium θ c σ) (hx : 0 < σ.q1) (hy : 0 < σ.y)
    (hz : 0 < σ.q2) (hb : 0 < σ.w2)
    (hFOC : 1-σ.w1-σ.y = (2-β)*σ.q1+2*ell*σ.q2) :
    σ.w2*G ≤ σ.q2 := by
  let x := σ.q1
  let z := σ.q2
  let b := σ.w2
  let e := min (b/2) (min z (x/(2*(L+1))))
  have he : 0 < e := lt_min (by change 0 < σ.w2/2; linarith)
    (lt_min hz (div_pos hx (by linarith)))
  have heb : e ≤ b/2 := min_le_left _ _
  have hez : e ≤ z := (min_le_right _ _).trans (min_le_left _ _)
  have hex : e ≤ x/(2*(L+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hactual := P087_actual_stageIII θ c σ hEq
  have horders := hEq.2.2.2.1 σ.w1 b hEq.1 hEq.2.1
  have hmax : ∀ t, 0 ≤ t → t ≤ e → (b-t)*(z+G*t) ≤ b*z := by
    intro t ht0 hte
    by_cases ht : t = 0
    · subst t
      simp
    have htp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have htb : t ≤ b := by linarith
    have htz : t < 2*z := by linarith
    have htx : L*t ≤ x := by
      have hh := (le_div_iff₀ (by linarith : 0 < 2*(L+1))).mp (hte.trans hex)
      nlinarith [mul_nonneg hL ht0]
    have hv : 0 ≤ b-t := by linarith
    have hnew := hEq.2.2.2.1 σ.w1 (b-t) hEq.1 hv
    have hresponse := P087_price_cut_response_param θ c b σ.w1 β ell κ L G σ.Y σ.Q2c
      x z t (σ.R σ.w1 (b-t)).1 (σ.R σ.w1 (b-t)).2 hθ0 hθ1 hc hEq.1 hβ hell
      hsA hsB hκ hκeq hL hG.le hLG hGL hEq.2.2.1 hactual hx hy hz hFOC
      horders.2.2 htp htb htz htx hnew.1 hnew.2.1 hnew.2.2
    have hbest := hEq.2.2.2.2.2 (b-t) hv
    change (σ.R σ.w1 (b-t)).2*(b-t) ≤ z*b at hbest
    rw [hresponse.2] at hbest
    nlinarith only [hbest]
  have hslope := P087_quadratic_right_nonpos (b*z) (b*G-z) G 0 e hG he
    (by
      intro t ht hte
      have hh := hmax t ht hte
      nlinarith only [hh])
  change b*G ≤ z
  nlinarith only [hslope]

/-- Supplier 2's necessary polynomial inequality at any interior equilibrium with
`c < 1/3` and a positive second wholesale price. -/
theorem P087_supplier2_E5_nonneg (θ c : ℝ) (σ : Profile)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hc : c < 1/3) (hEq : IsEquilibrium θ c σ)
    (hx : 0 < σ.q1) (hy : 0 < σ.y) (hz : 0 < σ.q2) (hb : 0 < σ.w2) :
    0 ≤ 2*(1-θ^2)*(8+θ^2)*σ.q2-(4-θ^2)*(2+θ^2)*σ.w2 := by
  let D := 4-θ^2
  let β := 2*(1-θ^2)/D
  let ell := 3*θ/D
  let κ := (1-θ^2)*(8+θ^2)/D^2
  let L := ell/(2*κ)
  let G := (1-β)/(2*κ)
  have ht2 : 0 < 1-θ^2 := by nlinarith [mul_self_lt_mul_self hθ0 hθ1]
  have hD : 0 < D := by dsimp [D]; linarith
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hell : 0 ≤ ell := by dsimp [ell]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hsA : 2*β+θ*ell = 1 := by
    dsimp only [β, ell]
    field_simp [ne_of_gt hD]
    dsimp [D]
    ring
  have hsB : 2*ell+θ*β = 2*θ := by
    dsimp only [β, ell]
    field_simp [ne_of_gt hD]
    dsimp [D]
    ring
  have hκeq : κ = 1-β-ell^2 := by
    dsimp only [κ, β, ell]
    field_simp [ne_of_gt hD]
    dsimp [D]
    ring
  have hr : 0 < 1-β := by nlinarith [sq_nonneg ell]
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hG : 0 < G := div_pos hr (by positivity)
  have hLG : (1-β)*L = ell*G := by dsimp [L, G]; ring
  have hGL : 2*G-2*ell*L = 1 := by
    dsimp only [L, G]
    field_simp [ne_of_gt hκ]
    nlinarith only [hκeq]
  have hFOC0 := P087_equilibrium_reseller_FOC θ c σ hθ0 hθ1 hEq hx hy hz
  have hFOC : 1-σ.w1-σ.y = (2-β)*σ.q1+2*ell*σ.q2 := by
    dsimp only [β, ell]
    field_simp [ne_of_gt hD]
    dsimp [D]
    linear_combination hFOC0
  have hnec := P087_supplier2_necessary_param θ c β ell κ L G σ hθ0 hθ1 hc hβ hell
    hsA hsB hκ hκeq hL hG hLG hGL hEq hx hy hz hb hFOC
  have hGcoef : 2*κ*G = 1-β := by dsimp [G]; field_simp
  have hprod := mul_nonneg (mul_nonneg (sq_nonneg D) (show 0 ≤ 2*κ by positivity))
    (sub_nonneg.mpr hnec)
  have hid : D^2*(2*κ)*(σ.q2-σ.w2*G) =
      2*(1-θ^2)*(8+θ^2)*σ.q2-(4-θ^2)*(2+θ^2)*σ.w2 := by
    calc
      _ = D^2*(2*κ*σ.q2-(1-β)*σ.w2) := by
        linear_combination -D^2*σ.w2*hGcoef
      _ = _ := by
        dsimp only [κ, β]
        field_simp [ne_of_gt hD]
        dsimp [D]
        ring
  rwa [hid] at hprod

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087Supplier1Necessary -/

namespace NonExclEncroach.Channels

/-- A positive linear price tilt removes every remote tie to the right of an
interior quadratic maximizer. No continuity assumption on the remote branches is used. -/
theorem P087_tilted_quadratic_selector (F : ℝ → ℝ) (x κ e r : ℝ)
    (hκ : 0 < κ) (he : 0 < e) (hex : e < x) (hr : 0 ≤ r)
    (hmax : ∀ v, 0 ≤ v → F v ≤ F x)
    (hleft : ∀ v, 0 ≤ v → v ≤ x → F v = F x-κ*(v-x)^2)
    (hnew : ∀ v, 0 ≤ v → F v-2*κ*e*v ≤ F r-2*κ*e*r) :
    r = x-e := by
  have hcandidate := hnew (x-e) (by linarith)
  rw [hleft (x-e) (by linarith) (by linarith)] at hcandidate
  by_cases hrx : r ≤ x
  · rw [hleft r hr hrx] at hcandidate
    have hs : κ*(r-(x-e))^2 ≤ 0 := by nlinarith only [hcandidate]
    have hsq : (r-(x-e))^2 = 0 := by
      have hn := sq_nonneg (r-(x-e))
      nlinarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · have hremote := hmax r hr
    have hxr : 0 ≤ r-x := by linarith
    have htilt : 0 ≤ 2*κ*e*(r-x) := by positivity
    have hstrict : 0 < κ*e^2 := mul_pos hκ (sq_pos_of_pos he)
    nlinarith

theorem P087_reseller_price_shift (θ r z a u b y : ℝ) :
    resellerProfit θ r z u b y = resellerProfit θ r z a b y-(u-a)*r := by
  dsimp only [resellerProfit, p1, p2]
  ring

/-- The one-sided supplier-1 first-order inequality is independent of the
retailer's choice among global maximizers at the original price. -/
theorem P087_supplier1_necessary_param (θ c β ell κ : ℝ) (σ : Profile)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ : 0 ≤ β) (hell : 0 ≤ ell)
    (hsA : 2*β+θ*ell = 1) (hsB : 2*ell+θ*β = 2*θ)
    (hκ : 0 < κ) (hκeq : κ = 1-β-ell^2)
    (hEq : IsEquilibrium θ c σ) (hx : 0 < σ.q1) (hy : 0 < σ.y) (hz : 0 < σ.q2)
    (hFOC : 1-σ.w1-σ.y = (2-β)*σ.q1+2*ell*σ.q2) :
    0 ≤ σ.w1-2*β*σ.y-2*κ*σ.q1 := by
  let x := σ.q1
  let y := σ.y
  let z := σ.q2
  let a := σ.w1
  let b := σ.w2
  have ha0 : 0 ≤ a := hEq.1
  have hactual := P087_actual_stageIII θ c σ hEq
  obtain ⟨_, _, _, _, hyc, hzc⟩ := P087_stageIII_complementarity θ c b x y z hactual
  have hA : 2*y+θ*z = 1-c-x := sub_eq_zero.mp ((mul_eq_zero.mp hyc).resolve_left (ne_of_gt hy))
  have hB : 2*z+θ*y = 1-b-2*θ*x := sub_eq_zero.mp ((mul_eq_zero.mp hzc).resolve_left (ne_of_gt hz))
  have hconj : z = σ.Q2c x := P087_consistent_reseller_order θ c σ hEq a hEq.1
  have hfamily : ∀ v, 0 ≤ v → v ≤ x →
      σ.Y v = y+β*(x-v) ∧ σ.Q2c v = z+ell*(x-v) := by
    intro v hv hvx
    have hyv : 0 ≤ y+β*(x-v) := by nlinarith [mul_nonneg hβ (sub_nonneg.mpr hvx)]
    have hzv : 0 ≤ z+ell*(x-v) := by nlinarith [mul_nonneg hell (sub_nonneg.mpr hvx)]
    have hAv : 2*(y+β*(x-v))+θ*(z+ell*(x-v)) = 1-c-v := by
      calc
        _ = (2*y+θ*z)+(2*β+θ*ell)*(x-v) := by ring
        _ = _ := by rw [hA, hsA]; ring
    have hBv : 2*(z+ell*(x-v))+θ*(y+β*(x-v)) = 1-b-2*θ*v := by
      calc
        _ = (2*z+θ*y)+(2*ell+θ*β)*(x-v) := by ring
        _ = _ := by rw [hB, hsB]; ring
    have hh : IsStageIII θ c b v (y+β*(x-v)) (z+ell*(x-v)) := by
      apply P087_stageIII_of_complementarity θ c b v _ _ hyv hzv hAv.ge hBv.ge
      · rw [hAv]
        ring
      · rw [hBv]
        ring
    exact P087_stageIII_unique θ c b v _ _ _ _ hθ0 hθ1 (hEq.2.2.1 v hv) hh
  let F := fun v ↦ resellerProfit θ v (σ.Q2c v) a b (σ.Y v)
  have hmax : ∀ v, 0 ≤ v → F v ≤ F x := by
    intro v hv
    have hh := (hEq.2.2.2.1 a b hEq.1 hEq.2.1).2.2 v (σ.Q2c v) hv (hEq.2.2.1 v hv).2.1
    change resellerProfit θ v (σ.Q2c v) a b (σ.Y v) ≤ resellerProfit θ x z a b (σ.Y x) at hh
    simpa only [F, ← hconj] using hh
  have haeq : a = 1-y-(2-β)*x-2*ell*z := by linarith
  have hleft : ∀ v, 0 ≤ v → v ≤ x → F v = F x-κ*(v-x)^2 := by
    intro v hv hvx
    obtain ⟨hyv, hzv⟩ := hfamily v hv hvx
    dsimp only [F]
    rw [P087_resellerProfit_stageIII θ c b v _ _ a (hEq.2.2.1 v hv),
      P087_resellerProfit_stageIII θ c b x _ _ a (hEq.2.2.1 x hx.le),
      hyv, hzv, ← hconj]
    change v*(1-a-v-(y+β*(x-v)))+(z+ell*(x-v))^2 =
      x*(1-a-x-y)+z^2-κ*(v-x)^2
    rw [haeq, hκeq]
    ring
  have hprofit : ∀ e, 0 < e → e < x →
      (y+β*e)^2+(a+2*κ*e)*(x-e) ≤ y^2+a*x := by
    intro e he hex
    let u := a+2*κ*e
    have hu : 0 ≤ u := by dsimp [u]; positivity
    let r := (σ.R u b).1
    let s := (σ.R u b).2
    have horders := hEq.2.2.2.1 u b hu hEq.2.1
    have hsQ : s = σ.Q2c r := P087_consistent_reseller_order θ c σ hEq u hu
    have hnew : ∀ v, 0 ≤ v → F v-2*κ*e*v ≤ F r-2*κ*e*r := by
      intro v hv
      have hh := horders.2.2 v (σ.Q2c v) hv (hEq.2.2.1 v hv).2.1
      change resellerProfit θ v (σ.Q2c v) u b (σ.Y v) ≤
        resellerProfit θ r s u b (σ.Y r) at hh
      rw [hsQ, P087_reseller_price_shift θ v _ a, P087_reseller_price_shift θ r _ a] at hh
      dsimp only [u] at hh
      dsimp only [F]
      nlinarith only [hh]
    have hr : r = x-e := P087_tilted_quadratic_selector F x κ e r hκ he hex horders.1 hmax hleft hnew
    have hyr : σ.Y r = y+β*e := by
      rw [hr]
      have hh := (hfamily (x-e) (by linarith) (by linarith)).1
      nlinarith only [hh]
    have hstageR : IsStageIII θ c b r (σ.Y r) s := by
      rw [hsQ]
      exact hEq.2.2.1 r horders.1
    have hh := hEq.2.2.2.2.1 u hu
    change supplier1Profit θ c r s u (σ.Y r) ≤ supplier1Profit θ c x z a y at hh
    rw [P087_supplier1Profit_eq_square θ c b r _ _ u hstageR,
      P087_supplier1Profit_eq_square θ c b x _ _ a hactual, hyr, hr] at hh
    exact hh
  let C := max (2*κ-β^2) 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound := P087_quadratic_right_nonpos (y^2+a*x) (2*β*y+2*κ*x-a) C 0 (x/2)
    hC (by linarith)
    (by
      intro e he0 hex2
      by_cases he : e = 0
      · subst e
        simp
      · have hep : 0 < e := lt_of_le_of_ne he0 (Ne.symm he)
        have hh := hprofit e hep (by linarith)
        have hmore : 0 ≤ (C-(2*κ-β^2))*e^2 :=
          mul_nonneg (sub_nonneg.mpr (le_max_left _ _)) (sq_nonneg _)
        nlinarith)
  change 0 ≤ a-2*β*y-2*κ*x
  linarith

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087Supplier1FirstOrder -/

namespace NonExclEncroach.Channels

/-- Supplier 1's one-sided necessary polynomial inequality at every interior
equilibrium. It holds for arbitrary selector choices and every direct cost. -/
theorem P087_supplier1_E4_nonneg (θ c : ℝ) (σ : Profile)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hEq : IsEquilibrium θ c σ)
    (hx : 0 < σ.q1) (hy : 0 < σ.y) (hz : 0 < σ.q2) :
    0 ≤ (4-θ^2)^2*σ.w1-4*(1-θ^2)*(4-θ^2)*σ.y-
      2*(1-θ^2)*(8+θ^2)*σ.q1 := by
  let D := 4-θ^2
  let β := 2*(1-θ^2)/D
  let ell := 3*θ/D
  let κ := (1-θ^2)*(8+θ^2)/D^2
  have ht2 : 0 < 1-θ^2 := by
    nlinarith [mul_self_lt_mul_self hθ0 hθ1]
  have hD : 0 < D := by dsimp [D]; linarith
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hell : 0 ≤ ell := by dsimp [ell]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hsA : 2*β+θ*ell = 1 := by
    dsimp only [β, ell]
    field_simp [ne_of_gt hD]
    dsimp [D]
    ring
  have hsB : 2*ell+θ*β = 2*θ := by
    dsimp only [β, ell]
    field_simp [ne_of_gt hD]
    dsimp [D]
    ring
  have hκeq : κ = 1-β-ell^2 := by
    dsimp only [κ, β, ell]
    field_simp [ne_of_gt hD]
    dsimp [D]
    ring
  have hFOC0 := P087_equilibrium_reseller_FOC θ c σ hθ0 hθ1 hEq hx hy hz
  have hFOC : 1-σ.w1-σ.y = (2-β)*σ.q1+2*ell*σ.q2 := by
    dsimp only [β, ell]
    field_simp [ne_of_gt hD]
    dsimp [D]
    linear_combination hFOC0
  have hnec := P087_supplier1_necessary_param θ c β ell κ σ hθ0 hθ1 hβ hell
    hsA hsB hκ hκeq hEq hx hy hz hFOC
  have hprod := mul_nonneg (sq_nonneg D) hnec
  have hid : D^2*(σ.w1-2*β*σ.y-2*κ*σ.q1) =
      (4-θ^2)^2*σ.w1-4*(1-θ^2)*(4-θ^2)*σ.y-
        2*(1-θ^2)*(8+θ^2)*σ.q1 := by
    dsimp only [β, κ]
    field_simp [ne_of_gt hD]
    dsimp [D]
    ring
  rwa [hid] at hprod

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087DirectOnlyFOC -/

namespace NonExclEncroach.Channels



/-- The one-sided supplier conditions suffice for the universal classification;
neither differentiability of the global selector nor supplier stationarity is assumed. -/
theorem P087_supplier_inequalities_force_nonpositive_q1 (θ c x y z u b : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hc : c ≤ c2 θ)
    (hY : 2*y+θ*z = 1-c-x)
    (hZ : 2*z+θ*y = 1-b-2*θ*x)
    (hR : (4-θ^2)*(1-u-y) = 6*(x+θ*z))
    (hS1 : 0 ≤ (4-θ^2)^2*u-4*(1-θ^2)*(4-θ^2)*y-2*(1-θ^2)*(8+θ^2)*x)
    (hS2 : 0 ≤ 2*(1-θ^2)*(8+θ^2)*z-(4-θ^2)*(2+θ^2)*b) : x ≤ 0 := by
  let R := θ^6-10*θ^4-28*θ^2+64
  let T := θ*(4-θ^2)*(5*θ^2+4)
  let Q := 6*(1+θ)*(256+48*θ^2-52*θ^4-11*θ^6+2*θ^8)*x-
    (4-θ^2)*(2*(1+θ)*(128-16*θ^2-13*θ^4)*c-θ*num1 θ)
  have h2 : θ^2 ≤ 1 := pow_le_one₀ hθ0 hθ1.le
  have h4 : θ^4 ≤ 1 := pow_le_one₀ hθ0 hθ1.le
  have h6 : θ^6 ≤ 1 := pow_le_one₀ hθ0 hθ1.le
  have hd : 0 < 4-θ^2 := by linarith
  have hRpos : 0 < R := by dsimp [R]; nlinarith [pow_nonneg hθ0 6]
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hid : (1-θ)*Q =
      -R*((4-θ^2)^2*u-4*(1-θ^2)*(4-θ^2)*y-2*(1-θ^2)*(8+θ^2)*x)-
      T*(2*(1-θ^2)*(8+θ^2)*z-(4-θ^2)*(2+θ^2)*b) := by
    dsimp [R, T, Q]
    unfold num1
    linear_combination
      (2*(4-θ^2)*(θ^2-1)*(128-16*θ^2-13*θ^4))*hY-
      (θ*(4-θ^2)^2*(θ^2+2)*(5*θ^2+4))*hZ-
      ((4-θ^2)*(θ^6-10*θ^4-28*θ^2+64))*hR
  have hQ : Q ≤ 0 := by
    have hprod : (1-θ)*Q ≤ 0 := by
      nlinarith only [hid, mul_nonneg hRpos.le hS1, mul_nonneg hT hS2]
    by_contra hnot
    have hp := mul_pos (sub_pos.mpr hθ1) (lt_of_not_ge hnot)
    linarith only [hprod, hp]
  have hH : 0 < 128-16*θ^2-13*θ^4 := by linarith
  have hP : 0 < 256+48*θ^2-52*θ^4-11*θ^6+2*θ^8 := by
    nlinarith [sq_nonneg θ, pow_nonneg hθ0 8]
  have hden : 0 < 2*(1+θ)*(128-16*θ^2-13*θ^4) := by positivity
  have hcut : 2*(1+θ)*(128-16*θ^2-13*θ^4)*c ≤ θ*num1 θ := by
    unfold c2 at hc
    have hh := (le_div_iff₀ hden).mp hc
    unfold num1
    nlinarith only [hh]
  have hcoef : 0 < 6*(1+θ)*(256+48*θ^2-52*θ^4-11*θ^6+2*θ^8) := by positivity
  have hcutprod := mul_nonpos_of_nonneg_of_nonpos hd.le (sub_nonpos.mpr hcut)
  by_contra hnot
  have hp := mul_pos hcoef (lt_of_not_ge hnot)
  dsimp only [Q] at hQ
  linarith only [hQ, hcutprod, hp]

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087DirectOnlyClassification -/

namespace NonExclEncroach.Channels

/-- Every equilibrium in the exact positive-cost regime of Proposition 5 is
direct-only. Both supplier inequalities are obtained by global, tie-safe deviations. -/
theorem P087_positive_equilibrium_directOnly (t θ c : ℝ) (σ : Profile)
    (ht0 : 0 < t) (ht1 : t < 1) (hnum : num1 t = 0)
    (hθ0 : 0 < θ) (hθt : θ < t) (hc0 : 0 < c) (hc2 : c ≤ c2 θ)
    (hEq : IsEquilibrium θ c σ) : σ.q1 = 0 ∧ 0 < σ.y := by
  have hθ1 : θ < 1 := hθt.trans ht1
  have hc3 : c < 1/3 := hc2.trans_lt (P087_c2_lt_one_third θ hθ0.le hθ1)
  obtain ⟨hy, hz, hb⟩ := P087_root_positive_interior t θ c σ
    ht0 ht1 hnum hθ0 hθt hc0 hc2 hEq
  refine ⟨?_, hy⟩
  have hx0 : 0 ≤ σ.q1 := (hEq.2.2.2.1 σ.w1 σ.w2 hEq.1 hEq.2.1).1
  by_contra hxne
  have hx : 0 < σ.q1 := lt_of_le_of_ne hx0 (Ne.symm hxne)
  have hstage := P087_actual_stageIII θ c σ hEq
  obtain ⟨_, _, _, _, hyc, hzc⟩ :=
    P087_stageIII_complementarity θ c σ.w2 σ.q1 σ.y σ.q2 hstage
  have hY : 2*σ.y+θ*σ.q2 = 1-c-σ.q1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hyc).resolve_left (ne_of_gt hy))
  have hZ : 2*σ.q2+θ*σ.y = 1-σ.w2-2*θ*σ.q1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hzc).resolve_left (ne_of_gt hz))
  have hR := P087_equilibrium_reseller_FOC θ c σ hθ0.le hθ1 hEq hx hy hz
  have hS1 := P087_supplier1_E4_nonneg θ c σ hθ0.le hθ1 hEq hx hy hz
  have hS2 := P087_supplier2_E5_nonneg θ c σ hθ0.le hθ1 hc3 hEq hx hy hz hb
  have hn := P087_supplier_inequalities_force_nonpositive_q1 θ c σ.q1 σ.y σ.q2 σ.w1 σ.w2
    hθ0.le hθ1 hc2 hY hZ hR hS1 hS2
  linarith only [hx, hn]

end NonExclEncroach.Channels


/- Inlined helper: Solutions.P087Root -/

namespace NonExclEncroach.Channels

theorem P087_proposition_5_proof :
    ∃ θhat : ℝ, 0 < θhat ∧ θhat < 1 ∧ num1 θhat = 0 ∧
      (∀ θ, 0 < θ → θ < θhat →
        0 < c2 θ ∧
        ∀ c, 0 < c → c ≤ c2 θ →
          (∃ σ, IsEquilibrium θ c σ) ∧
          ∀ σ, IsEquilibrium θ c σ → σ.q1 = 0 ∧ 0 < σ.y) ∧
      (∀ θ, θhat < θ → θ < 1 → c2 θ < 0) ∧
      (∀ θ, θhat < θ → θ ≤ 9 / 10 →
        ∀ c, c2 θ < c → c < 0 →
          ∃ σ, IsEquilibrium θ c σ ∧ 0 < σ.q1 ∧ 0 < σ.y) := by
  obtain ⟨θhat, ht0, ht1, hnum, hpos, hneg⟩ := P087_threshold_exists
  refine ⟨θhat, ht0, ht1, hnum, ?_, hneg, ?_⟩
  · intro θ hθ0 hθt
    refine ⟨hpos θ hθ0 hθt, ?_⟩
    intro c hc0 hc2
    have hθ1 : θ < 1 := hθt.trans ht1
    have hn := P087_num1_strictAnti ⟨hθ0.le, hθ1.le⟩ ⟨ht0.le, ht1.le⟩ hθt
    rw [hnum] at hn
    have hθ7 := P087_num1_pos_theta_lt_seven_twentieths θ hθ0.le hθ1 hn
    obtain ⟨σ, hEq, _, _⟩ := P087_DO_equilibrium_exists θ c hθ0 hθ7.le hc0 hc2
    exact ⟨⟨σ, hEq⟩, fun σ hEq =>
      P087_positive_equilibrium_directOnly θhat θ c σ ht0 ht1 hnum hθ0 hθt hc0 hc2 hEq⟩
  · intro θ htθ hθ9 c hc2 hc0
    exact P087_RD_equilibrium_exists θ c (ht0.trans htθ) hθ9 hc2 hc0

end NonExclEncroach.Channels


open NonExclEncroach.Channels

theorem solution :
    ∃ θhat : ℝ, 0 < θhat ∧ θhat < 1 ∧ num1 θhat = 0 ∧
      (∀ θ, 0 < θ → θ < θhat →
        0 < c2 θ ∧
        ∀ c, 0 < c → c ≤ c2 θ →
          (∃ σ, IsEquilibrium θ c σ) ∧
          ∀ σ, IsEquilibrium θ c σ → σ.q1 = 0 ∧ 0 < σ.y) ∧
      (∀ θ, θhat < θ → θ < 1 → c2 θ < 0) ∧
      (∀ θ, θhat < θ → θ ≤ 9 / 10 →
        ∀ c, c2 θ < c → c < 0 →
          ∃ σ, IsEquilibrium θ c σ ∧ 0 < σ.q1 ∧ 0 < σ.y) := by
  exact NonExclEncroach.Channels.P087_proposition_5_proof

#print axioms solution
