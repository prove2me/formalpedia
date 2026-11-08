-- Prove2me | solution 1 for LogRegretOCO.ONS.theorem_2_ons_regret
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T16:14:02.255326+00:00
-- url     : https://prove2.me/submissions/3c7c862f-cd99-43a9-9486-f54439c9faa3

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_qform
import Definitions.Def_LogRegretOCO_ONS_IsExpConcaveOn
import Definitions.Def_LogRegretOCO_ONS_onsBeta
import Definitions.Def_LogRegretOCO_ONS_onsEps
import Definitions.Def_LogRegretOCO_ONS_onsGrad
import Definitions.Def_LogRegretOCO_ONS_onsA
import Definitions.Def_LogRegretOCO_ONS_IsGenProj
import Definitions.Def_LogRegretOCO_ONS_IsONSRun

set_option autoImplicit false

namespace LogRegretOCO.ONS
open Matrix LogRegretOCO.ONS Filter Topology

variable {n : ℕ}

/-- bilinear form `vᵀ A w` -/
def bform (A : Matrix (Fin n) (Fin n) ℝ) (v w : EuclideanSpace ℝ (Fin n)) : ℝ :=
  WithLp.ofLp v ⬝ᵥ (A *ᵥ WithLp.ofLp w)

/-- (L1) expansion of a quadratic form of a difference, A symmetric. -/
lemma qform_sub (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (v w : EuclideanSpace ℝ (Fin n)) :
    qform A (v - w) = qform A v - 2 * bform A v w + qform A w := by
  have key : WithLp.ofLp w ⬝ᵥ (A *ᵥ WithLp.ofLp v) = WithLp.ofLp v ⬝ᵥ (A *ᵥ WithLp.ofLp w) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq, dotProduct_comm]
  unfold qform bform
  simp only [WithLp.ofLp_sub, mulVec_sub, dotProduct_sub, sub_dotProduct, key]
  ring

lemma bform_smul_right (A : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (v w : EuclideanSpace ℝ (Fin n)) :
    bform A v (s • w) = s * bform A v w := by
  unfold bform
  simp only [WithLp.ofLp_smul, mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma qform_smul (A : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    qform A (s • v) = s ^ 2 * qform A v := by
  unfold qform
  simp only [WithLp.ofLp_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

lemma qform_neg (A : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    qform A (-v) = qform A v := by
  unfold qform
  simp only [WithLp.ofLp_neg, mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]

lemma qform_sub_smul (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (s : ℝ)
    (a b : EuclideanSpace ℝ (Fin n)) :
    qform A (a - s • b) = qform A a - 2 * s * bform A a b + s ^ 2 * qform A b := by
  rw [qform_sub A hA, bform_smul_right, qform_smul]
  ring

/-- (L2) Pythagoras for the generalized projection (Lemma 8 of the paper). -/
lemma genProj_pythag (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (hpsd : ∀ v, 0 ≤ qform A v) {P : Set (EuclideanSpace ℝ (Fin n))} (hP : Convex ℝ P)
    {y z u : EuclideanSpace ℝ (Fin n)} (hz : IsGenProj A P y z) (hu : u ∈ P) :
    qform A (z - u) ≤ qform A (y - u) := by
  obtain ⟨hzP, hmin⟩ := hz
  set c := bform A (y - z) (u - z) with hc
  set qb := qform A (u - z) with hqb
  have hqb0 : 0 ≤ qb := hpsd _
  have hs : ∀ s : ℝ, 0 < s → s ≤ 1 → 2 * c ≤ s * qb := by
    intro s hs0 hs1
    have hmem : z + s • (u - z) ∈ P := hP.add_smul_sub_mem hzP hu ⟨hs0.le, hs1⟩
    have h1 := hmin _ hmem
    have h2 : y - (z + s • (u - z)) = (y - z) - s • (u - z) := by abel
    rw [h2, qform_sub_smul A hA] at h1
    have : 0 ≤ s * (s * qb - 2 * c) := by nlinarith
    have := (mul_nonneg_iff_of_pos_left hs0).mp this
    linarith
  have hc0 : c ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    set s := min 1 (c / (qb + 1)) with hsdef
    have hs0 : 0 < s := lt_min one_pos (div_pos hcon (by linarith))
    have hs1 : s ≤ 1 := min_le_left _ _
    have hs2 : s ≤ c / (qb + 1) := min_le_right _ _
    have h3 := hs s hs0 hs1
    have h4 : s * (qb + 1) ≤ c := by
      rwa [le_div_iff₀ (by linarith)] at hs2
    nlinarith
  have h5 : y - u = (y - z) - (1 : ℝ) • (u - z) := by rw [one_smul]; abel
  rw [h5, qform_sub_smul A hA]
  have h6 : z - u = -(u - z) := by abel
  rw [h6, qform_neg]
  have := hpsd (y - z)
  nlinarith

/-- (L5) one Newton step expansion. -/
lemma step_expand (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hdet : IsUnit A.det)
    (β : ℝ) (hβ : β ≠ 0) (x u g : EuclideanSpace ℝ (Fin n)) :
    qform A (x - β⁻¹ • WithLp.toLp 2 (A⁻¹ *ᵥ WithLp.ofLp g) - u)
      = qform A (x - u) - 2 / β * inner ℝ g (x - u)
        + 1 / β ^ 2 * (WithLp.ofLp g ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp g)) := by
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  rw [sub_right_comm, qform_sub_smul A hA]
  have hb : bform A (x - u) (WithLp.toLp 2 (A⁻¹ *ᵥ WithLp.ofLp g)) = inner ℝ g (x - u) := by
    unfold bform
    rw [WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  have hq : qform A (WithLp.toLp 2 (A⁻¹ *ᵥ WithLp.ofLp g))
      = WithLp.ofLp g ⬝ᵥ (A⁻¹ *ᵥ WithLp.ofLp g) := by
    unfold qform
    rw [WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec, dotProduct_comm]
  rw [hb, hq]
  field_simp

/-- (L4a) onsA is symmetric. -/
lemma onsA_symm (ε : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (t : ℕ) : (onsA ε f x t).IsSymm := by
  unfold onsA Matrix.IsSymm
  simp [Matrix.transpose_sum, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_vecMulVec]

/-- (L4b) quadratic form of onsA. -/
lemma qform_onsA (ε : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (t : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    qform (onsA ε f x t) v = ∑ i ∈ Finset.Icc 1 t, (inner ℝ (onsGrad f x i) v) ^ 2 + ε * ‖v‖ ^ 2 := by
  unfold qform onsA
  rw [Matrix.add_mulVec, Matrix.sum_mulVec, dotProduct_add, dotProduct_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.vecMulVec_mulVec, dotProduct_smul, op_smul_eq_mul,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm (WithLp.ofLp v)]
    ring
  · rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
      ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

lemma tangent_concave {P : Set (EuclideanSpace ℝ (Fin n))} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hc : ConcaveOn ℝ P h) {y u : EuclideanSpace ℝ (Fin n)} (hy : y ∈ P) (hu : u ∈ P)
    {L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hd : HasFDerivAt h L y) :
    h u ≤ h y + L (u - y) := by
  have hl : HasLineDerivAt ℝ h (L (u - y)) y (u - y) := hd.hasLineDerivAt (u - y)
  have ht := hl.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), h u - h y ≤ t⁻¹ • (h (y + t • (u - y)) - h y) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h1 := hc.2 hy hu (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (show 1 - t + t = 1 by ring)
    have heq : (1 - t) • y + t • u = y + t • (u - y) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [heq, smul_eq_mul, smul_eq_mul] at h1
    rw [smul_eq_mul, le_inv_mul_iff₀ ht0]
    nlinarith
  have := ge_of_tendsto ht hev
  linarith

lemma one_add_le_exp_quad {z : ℝ} (hz : |z| ≤ 1 / 4) : 1 + z ≤ Real.exp (z - z ^ 2 / 4) := by
  set w := z - z ^ 2 / 4 with hwdef
  set s := |z| with hs
  have hs0 : 0 ≤ s := abs_nonneg z
  have hz2 : z ^ 2 = s ^ 2 := (sq_abs z).symm
  have hz3 : z ^ 3 ≤ s ^ 3 := by
    have : z ≤ s := le_abs_self z
    have : z ^ 3 = z * s ^ 2 := by rw [← hz2]; ring
    nlinarith
  have hw : |w| ≤ s + s ^ 2 / 4 := by
    rw [hwdef]
    calc |z - z ^ 2 / 4| ≤ |z| + |z ^ 2 / 4| := abs_sub _ _
      _ = s + s ^ 2 / 4 := by rw [abs_div, abs_pow, hs]; norm_num
  have hw1 : |w| ≤ 1 := by nlinarith
  have hb := Real.exp_bound hw1 (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.succ_eq_add_one] at hb
  norm_num at hb
  have hlow := (abs_le.mp hb).1
  have hw3 : |w| ^ 3 ≤ (s + s ^ 2 / 4) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hw 3
  have hw2 : w ^ 2 = z ^ 2 - z ^ 3 / 2 + z ^ 4 / 16 := by rw [hwdef]; ring
  have hz4 : z ^ 4 = s ^ 4 := by rw [show z ^ 4 = (z ^ 2) ^ 2 by ring, hz2]; ring
  have key : (s + s ^ 2 / 4) ^ 3 * (2 / 9) ≤ s ^ 2 / 4 - s ^ 3 / 4 := by
    have hs4 : s ≤ 1 / 4 := hz
    have h17 : s + s ^ 2 / 4 ≤ 17 / 16 * s := by nlinarith
    have hc : (s + s ^ 2 / 4) ^ 3 ≤ (17 / 16 * s) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h17 3
    have hss : 0 ≤ s ^ 2 * (1 / 4 - s) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  nlinarith

lemma expconcave_bound {P : Set (EuclideanSpace ℝ (Fin n))} {G D α β : ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hβ : 0 < β) (hβα : 2 * β ≤ α) (hβGD : 2 * β * G * D ≤ 1 / 4)
    (hdiam : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D)
    (hdiff : ∀ y ∈ P, DifferentiableAt ℝ f y) (hgrad : ∀ y ∈ P, ‖gradient f y‖ ≤ G)
    (hexp : IsExpConcaveOn α P f) {y u : EuclideanSpace ℝ (Fin n)} (hy : y ∈ P) (hu : u ∈ P) :
    f y - f u ≤ inner ℝ (gradient f y) (y - u) - β / 2 * (inner ℝ (gradient f y) (y - u)) ^ 2 := by
  set g := gradient f y with hg
  set a := inner ℝ g (y - u) with ha
  have hα : 0 < α := by linarith
  have hfd : HasFDerivAt f ((InnerProductSpace.toDual ℝ _) g) y := (hdiff y hy).hasGradientAt
  have hhd := ((hfd.const_mul α).neg).exp
  have htan := tangent_concave hexp hy hu hhd
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
    InnerProductSpace.toDual_apply_apply, smul_eq_mul, Pi.neg_apply] at htan
  have hin : inner ℝ g (u - y) = -a := by
    rw [ha, ← inner_neg_right, neg_sub]
  rw [hin] at htan
  set d := f y - f u with hd
  set E := Real.exp (-(α * f y)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hsplit : Real.exp (-(α * f u)) = Real.exp (α * d) * E := by
    rw [hE, ← Real.exp_add, hd]; ring_nf
  rw [hsplit] at htan
  have h1 : Real.exp (α * d) ≤ 1 + α * a := by
    have : Real.exp (α * d) * E ≤ E * (1 + α * a) := by nlinarith
    nlinarith
  have hpos : 0 < 1 + α * a := lt_of_lt_of_le (Real.exp_pos _) h1
  set p := 2 * β / α with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hα]; exact hβα
  have hb := rpow_one_add_le_one_add_mul_self (s := α * a) (by linarith) hp0 hp1
  have hmono : Real.exp (α * d) ^ p ≤ (1 + α * a) ^ p :=
    Real.rpow_le_rpow (Real.exp_pos _).le h1 hp0
  rw [← Real.exp_mul] at hmono
  have hpa : p * (α * a) = 2 * β * a := by rw [hp]; field_simp
  have hpd : α * d * p = 2 * β * d := by rw [hp]; field_simp
  rw [hpa] at hb
  rw [hpd] at hmono
  have hG : 0 ≤ G := le_trans (norm_nonneg _) (hgrad y hy)
  have hD : ‖y - u‖ ≤ D := hdiam y hy u hu
  have habs : |a| ≤ G * D := by
    calc |a| ≤ ‖g‖ * ‖y - u‖ := abs_real_inner_le_norm _ _
      _ ≤ G * D := mul_le_mul (hgrad y hy) hD (norm_nonneg _) hG
  have hz : |2 * β * a| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * β)]
    calc 2 * β * |a| ≤ 2 * β * (G * D) := by gcongr
      _ = 2 * β * G * D := by ring
      _ ≤ 1 / 4 := hβGD
  have hq := one_add_le_exp_quad hz
  have hfin : Real.exp (2 * β * d) ≤ Real.exp (2 * β * a - (2 * β * a) ^ 2 / 4) :=
    le_trans hmono (le_trans hb hq)
  rw [Real.exp_le_exp] at hfin
  have : 2 * β * d ≤ 2 * β * (a - β / 2 * a ^ 2) := by nlinarith
  exact le_of_mul_le_mul_left this (by linarith)

/-- (L7) numeric inequality with explicit β, ε. -/
lemma numeric' {G D α β ε : ℝ} (hD : 0 < D) (hα : 0 < α) (hG : 0 < G)
    (hβ : β = 1 / 2 * min (1 / (4 * G * D)) α) (hε : ε = 1 / (β ^ 2 * D ^ 2))
    (hn : 1 ≤ n) (T : ℕ) (hT : 3 ≤ T) :
    1 / (2 * β) * (n * Real.log (1 + T * G ^ 2 / (n * ε)) + 1)
      ≤ 5 * (1 / α + G * D) * n * Real.log T := by
  have hGD : 0 < G * D := mul_pos hG hD
  have hmin0 : 0 < min (1 / (4 * G * D)) α := lt_min (by positivity) hα
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have hβ1 : β * (G * D) ≤ 1 / 8 := by
    have : min (1 / (4 * G * D)) α ≤ 1 / (4 * G * D) := min_le_left _ _
    rw [hβ]
    calc 1 / 2 * min (1 / (4 * G * D)) α * (G * D) ≤ 1 / 2 * (1 / (4 * G * D)) * (G * D) := by
          gcongr
      _ = 1 / 8 := by field_simp; norm_num
  have h2β : 1 / (2 * β) ≤ 4 * (G * D) + 1 / α := by
    have h2 : 2 * β = min (1 / (4 * G * D)) α := by rw [hβ]; ring
    rw [h2]
    rcases min_choice (1 / (4 * G * D)) α with h | h
    · rw [h]
      have : 1 / (1 / (4 * G * D)) = 4 * (G * D) := by field_simp
      rw [this]; have : 0 < 1 / α := by positivity
      linarith
    · rw [h]; have : 0 ≤ 4 * (G * D) := by positivity
      linarith
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hTR : (3 : ℝ) ≤ T := by exact_mod_cast hT
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hratio : T * G ^ 2 / (n * ε) ≤ T / 64 := by
    rw [hε, div_le_div_iff₀ (by positivity) (by norm_num)]
    have hsq : (β * (G * D)) ^ 2 ≤ 1 / 64 := by
      have : 0 ≤ β * (G * D) := by positivity
      nlinarith
    have : (n : ℝ) * (1 / (β ^ 2 * D ^ 2)) = n / (β ^ 2 * D ^ 2) := by ring
    rw [this, mul_div_assoc']
    rw [le_div_iff₀ (by positivity)]
    have : T * G ^ 2 * 64 * (β ^ 2 * D ^ 2) = 64 * T * (β * (G * D)) ^ 2 := by ring
    rw [this]
    have hT0 : (0:ℝ) ≤ T := by linarith
    nlinarith
  have hratio0 : 0 ≤ T * G ^ 2 / (n * ε) := by positivity
  have hlog1 : Real.log (1 + T * G ^ 2 / (n * ε)) ≤ Real.log (1 + T / 64) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog0 : 0 ≤ Real.log (1 + T * G ^ 2 / (n * ε)) := Real.log_nonneg (by linarith)
  have hkey : Real.log (1 + T / 64) + 1 ≤ Real.log T := by
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h1 : (1 + (T:ℝ) / 64) * Real.exp 1 ≤ T := by nlinarith [Real.exp_pos 1]
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp] at h2
    exact h2
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hA : 0 ≤ 4 * (G * D) + 1 / α := by positivity
  calc 1 / (2 * β) * (n * Real.log (1 + T * G ^ 2 / (n * ε)) + 1)
      ≤ (4 * (G * D) + 1 / α) * (n * Real.log (1 + T * G ^ 2 / (n * ε)) + 1) := by
        gcongr
    _ ≤ (4 * (G * D) + 1 / α) * (n * (Real.log (1 + T / 64) + 1)) := by
        gcongr
        nlinarith
    _ ≤ (4 * (G * D) + 1 / α) * (n * Real.log T) := by gcongr
    _ ≤ 5 * (1 / α + G * D) * n * Real.log T := by
        have : 0 ≤ (n : ℝ) * Real.log T := by positivity
        have h5 : 4 * (G * D) + 1 / α ≤ 5 * (1 / α + G * D) := by
          have : 0 < 1 / α := by positivity
          nlinarith
        calc (4 * (G * D) + 1 / α) * (n * Real.log T) ≤ 5 * (1 / α + G * D) * (n * Real.log T) := by
              gcongr
          _ = _ := by ring


noncomputable def Am (ε : ℝ) (g : ℕ → Fin n → ℝ) (t : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i ∈ Finset.Icc 1 t, vecMulVec (g i) (g i) + ε • (1 : Matrix (Fin n) (Fin n) ℝ)

lemma Am_posDef (ε : ℝ) (hε : 0 < ε) (g : ℕ → Fin n → ℝ) (t : ℕ) : (Am ε g t).PosDef := by
  unfold Am
  rw [add_comm]
  refine (PosDef.one.smul hε).add_posSemidef (posSemidef_sum _ fun i _ => ?_)
  simpa using posSemidef_vecMulVec_self_star (g i)

lemma Am_succ (ε : ℝ) (g : ℕ → Fin n → ℝ) (t : ℕ) :
    Am ε g (t + 1) = Am ε g t + vecMulVec (g (t + 1)) (g (t + 1)) := by
  unfold Am
  rw [Finset.sum_Icc_succ_top (by omega)]
  abel

lemma det_step (ε : ℝ) (hε : 0 < ε) (g : ℕ → Fin n → ℝ) (t : ℕ) :
    (Am ε g t).det = (Am ε g (t + 1)).det *
      (1 - g (t + 1) ⬝ᵥ ((Am ε g (t + 1))⁻¹ *ᵥ g (t + 1))) := by
  have hU : IsUnit (Am ε g (t + 1)).det := (Am_posDef ε hε g (t + 1)).det_pos.ne'.isUnit
  have h := det_add_replicateCol_mul_replicateRow (ι := Unit) hU (-(g (t + 1))) (g (t + 1))
  have heq : Am ε g (t + 1) + replicateCol Unit (-(g (t + 1))) * replicateRow Unit (g (t + 1))
      = Am ε g t := by
    rw [← vecMulVec_eq, Am_succ, neg_vecMulVec]
    abel
  rw [heq] at h
  rw [h]
  congr 1
  simp [det_unique, Matrix.mul_apply, replicateRow, replicateCol, dotProduct, mulVec,
    Finset.sum_neg_distrib, Finset.mul_sum, sub_eq_add_neg]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma step_log (ε : ℝ) (hε : 0 < ε) (g : ℕ → Fin n → ℝ) (t : ℕ) :
    g (t + 1) ⬝ᵥ ((Am ε g (t + 1))⁻¹ *ᵥ g (t + 1))
      ≤ Real.log (Am ε g (t + 1)).det - Real.log (Am ε g t).det := by
  have h0 := (Am_posDef ε hε g t).det_pos
  have h1 := (Am_posDef ε hε g (t + 1)).det_pos
  have hs := det_step ε hε g t
  set r := g (t + 1) ⬝ᵥ ((Am ε g (t + 1))⁻¹ *ᵥ g (t + 1))
  set D0 := (Am ε g t).det
  set D1 := (Am ε g (t + 1)).det
  have hq : 0 < D1 / D0 := div_pos h1 h0
  have hl := Real.one_sub_inv_le_log_of_pos hq
  rw [Real.log_div h1.ne' h0.ne', inv_div] at hl
  have : D0 / D1 = 1 - r := by rw [hs]; field_simp
  linarith

lemma sum_le_logdet (ε : ℝ) (hε : 0 < ε) (g : ℕ → Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, g t ⬝ᵥ ((Am ε g t)⁻¹ *ᵥ g t)
      ≤ Real.log (Am ε g T).det - Real.log (Am ε g 0).det := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := step_log ε hε g T
    linarith

lemma det_Am_zero (ε : ℝ) (g : ℕ → Fin n → ℝ) : (Am ε g 0).det = ε ^ n := by
  unfold Am
  simp

lemma logdet_le (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hn : 1 ≤ n) :
    Real.log A.det ≤ n * Real.log (A.trace / n) := by
  have hH := hA.1
  have hdet : A.det = ∏ i, hH.eigenvalues i := by
    rw [hH.det_eq_prod_eigenvalues]; simp
  have htr : A.trace = ∑ i, hH.eigenvalues i := by
    rw [hH.trace_eq_sum_eigenvalues]; simp
  have hpos : ∀ i, 0 < hH.eigenvalues i := fun i => hA.eigenvalues_pos i
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set m := A.trace / n with hm
  have hS : 0 < A.trace := by
    rw [htr]
    exact Finset.sum_pos (fun i _ => hpos i) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hm0 : 0 < m := div_pos hS hnR
  rw [hdet, Real.log_prod (fun i _ => (hpos i).ne')]
  have hi : ∀ i, Real.log (hH.eigenvalues i) ≤ Real.log m + hH.eigenvalues i / m - 1 := by
    intro i
    have := Real.log_le_sub_one_of_pos (div_pos (hpos i) hm0)
    rw [Real.log_div (hpos i).ne' hm0.ne'] at this
    linarith
  calc ∑ i, Real.log (hH.eigenvalues i) ≤ ∑ i : Fin n, (Real.log m + hH.eigenvalues i / m - 1) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = n * Real.log m + (∑ i, hH.eigenvalues i) / m - n := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_div]
        simp
    _ = n * Real.log m := by
        rw [← htr, hm]; field_simp; ring

lemma trace_Am (ε : ℝ) (g : ℕ → Fin n → ℝ) (t : ℕ) :
    (Am ε g t).trace = ∑ i ∈ Finset.Icc 1 t, g i ⬝ᵥ g i + n * ε := by
  unfold Am
  rw [trace_add, trace_sum]
  simp [trace_vecMulVec, trace_smul, trace_one, mul_comm]

lemma potential_gen (ε G : ℝ) (hε : 0 < ε) (hn : 1 ≤ n) (g : ℕ → Fin n → ℝ)
    (hg : ∀ t, 1 ≤ t → g t ⬝ᵥ g t ≤ G ^ 2) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, g t ⬝ᵥ ((Am ε g t)⁻¹ *ᵥ g t)
      ≤ n * Real.log (1 + T * G ^ 2 / (n * ε)) := by
  have h1 := sum_le_logdet ε hε g T
  rw [det_Am_zero, Real.log_pow] at h1
  have h2 := logdet_le (Am ε g T) (Am_posDef ε hε g T) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htr := trace_Am ε g T
  have hsum : ∑ i ∈ Finset.Icc 1 T, g i ⬝ᵥ g i ≤ T * G ^ 2 := by
    calc ∑ i ∈ Finset.Icc 1 T, g i ⬝ᵥ g i ≤ ∑ i ∈ Finset.Icc 1 T, G ^ 2 :=
          Finset.sum_le_sum fun i hi => hg i (Finset.mem_Icc.mp hi).1
      _ = T * G ^ 2 := by simp
  have hS : 0 < (Am ε g T).trace := by
    have := (Am_posDef ε hε g T).det_pos
    rw [htr]
    have : 0 ≤ ∑ i ∈ Finset.Icc 1 T, g i ⬝ᵥ g i :=
      Finset.sum_nonneg fun i _ => by
        simp only [dotProduct]; exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
    positivity
  have hkey : Real.log ((Am ε g T).trace / n) - Real.log ε ≤ Real.log (1 + T * G ^ 2 / (n * ε)) := by
    rw [← Real.log_div (by positivity) hε.ne']
    apply Real.log_le_log (by positivity)
    rw [htr, div_div, div_le_iff₀ (by positivity)]
    have : (1 + T * G ^ 2 / (n * ε)) * (n * ε) = n * ε + T * G ^ 2 := by field_simp
    rw [this]; linarith
  have : n * Real.log ((Am ε g T).trace / n) - n * Real.log ε ≤ n * Real.log (1 + T * G ^ 2 / (n * ε)) := by
    rw [← mul_sub]; exact mul_le_mul_of_nonneg_left hkey hnR.le
  linarith

end LogRegretOCO.ONS

set_option maxHeartbeats 1000000 in
open Matrix LogRegretOCO.ONS in
theorem solution {n : ℕ} {P : Set (EuclideanSpace ℝ (Fin n))} {G D α : ℝ}
    {f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)}
    (hPc : Convex ℝ P) (hPcl : IsClosed P)
    (hD : 0 < D) (hdiam : ∀ y ∈ P, ∀ z ∈ P, ‖y - z‖ ≤ D)
    (hα : 0 < α) (hG : 0 < G)
    (hdiff : ∀ t : ℕ, 1 ≤ t → ∀ y ∈ P, DifferentiableAt ℝ (f t) y)
    (hgrad : ∀ t : ℕ, 1 ≤ t → ∀ y ∈ P, ‖gradient (f t) y‖ ≤ G)
    (hexp : ∀ t : ℕ, 1 ≤ t → IsExpConcaveOn α P (f t))
    (hrun : IsONSRun P G D α f x) :
    ∀ T : ℕ, 2 ≤ T → ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t u) ≤ 5 * (1 / α + G * D) * n * Real.log T := by
  intro T hT u hu
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hsub : ∀ v w : EuclideanSpace ℝ (Fin 0), v = w := fun v w => by
      ext i; exact i.elim0
    have h0 : ∀ t, f t (x t) - f t u = 0 := fun t => by rw [hsub (x t) u, sub_self]
    simp only [h0, Finset.sum_const_zero, Nat.cast_zero, mul_zero, zero_mul, le_refl]
  have hn : 1 ≤ n := hnpos
  obtain ⟨hx1, hstep⟩ := hrun
  set β := onsBeta G D α with hβdef
  set ε := onsEps G D α with hεdef
  have hGD : 0 < G * D := mul_pos hG hD
  have hmin0 : 0 < min (1 / (4 * G * D)) α := lt_min (by positivity) hα
  have h2β : 2 * β = min (1 / (4 * G * D)) α := by rw [hβdef, onsBeta]; ring
  have hβ0 : 0 < β := by linarith
  have hβα : 2 * β ≤ α := h2β ▸ min_le_right _ _
  have hβGD : 2 * β * G * D ≤ 1 / 4 := by
    have h1 : 2 * β ≤ 1 / (4 * G * D) := h2β ▸ min_le_left _ _
    calc 2 * β * G * D = 2 * β * (G * D) := by ring
      _ ≤ 1 / (4 * G * D) * (G * D) := by gcongr
      _ = 1 / 4 := by field_simp
  have hεβ : ε = 1 / (β ^ 2 * D ^ 2) := by rw [hεdef, onsEps, ← hβdef]
  have hε0 : 0 < ε := by rw [hεβ]; positivity
  have hx : ∀ t, 1 ≤ t → x t ∈ P := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hx1
    | succ t ht _ => exact (hstep t ht).1
  have hApd : ∀ t, (onsA ε f x t).PosDef := fun t =>
    Am_posDef ε hε0 (fun i => WithLp.ofLp (onsGrad f x i)) t
  have hqnn : ∀ t v, 0 ≤ qform (onsA ε f x t) v := fun t v => by
    rw [qform_onsA]
    exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (mul_nonneg hε0.le (sq_nonneg _))
  have habs : ∀ t, 1 ≤ t → |inner ℝ (gradient (f t) (x t)) (x t - u)| ≤ G * D := fun t ht =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hgrad t ht _ (hx t ht))
      (hdiam _ (hx t ht) u hu) (norm_nonneg _) hG.le)
  -- T = 2: per-round bound
  rcases (show T = 2 ∨ 3 ≤ T by omega) with rfl | hT3
  · have hper : ∀ t ∈ Finset.Icc 1 2, f t (x t) - f t u ≤ G * D := by
      intro t ht
      have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
      have h3 := expconcave_bound hβ0 hβα hβGD hdiam (hdiff t ht1) (hgrad t ht1) (hexp t ht1)
        (hx t ht1) hu
      have h4 := le_abs_self (inner ℝ (gradient (f t) (x t)) (x t - u))
      have h5 : 0 ≤ β / 2 * (inner ℝ (gradient (f t) (x t)) (x t - u)) ^ 2 := by positivity
      linarith [habs t ht1]
    have hsum : ∑ t ∈ Finset.Icc 1 2, (f t (x t) - f t u) ≤ 2 * (G * D) := by
      calc ∑ t ∈ Finset.Icc 1 2, (f t (x t) - f t u) ≤ ∑ t ∈ Finset.Icc 1 2, G * D :=
            Finset.sum_le_sum hper
        _ = 2 * (G * D) := by rw [Finset.sum_const, Nat.card_Icc]; norm_num
    have hl := Real.log_two_gt_d9
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hα' : 0 < 1 / α := by positivity
    have hK : 2 * (G * D) ≤ 5 * (1 / α + G * D) * Real.log 2 := by nlinarith
    have hK0 : 0 ≤ 5 * (1 / α + G * D) * Real.log 2 := by nlinarith
    push_cast
    calc ∑ t ∈ Finset.Icc 1 2, (f t (x t) - f t u) ≤ 2 * (G * D) := hsum
      _ ≤ 5 * (1 / α + G * D) * Real.log 2 := hK
      _ ≤ 5 * (1 / α + G * D) * n * Real.log 2 := by nlinarith
  -- T ≥ 3
  have hround : ∀ t, 1 ≤ t → f t (x t) - f t u ≤
      β / 2 * (qform (onsA ε f x (t - 1)) (x t - u) - qform (onsA ε f x t) (x (t + 1) - u)) +
      (WithLp.ofLp (onsGrad f x t) ⬝ᵥ ((onsA ε f x t)⁻¹ *ᵥ WithLp.ofLp (onsGrad f x t))) /
        (2 * β) := by
    intro t ht
    have h3 := expconcave_bound hβ0 hβα hβGD hdiam (hdiff t ht) (hgrad t ht) (hexp t ht)
      (hx t ht) hu
    have hgt : gradient (f t) (x t) = onsGrad f x t := rfl
    rw [hgt] at h3
    have hproj := genProj_pythag (onsA ε f x t) (onsA_symm ε f x t) (hqnn t) hPc (hstep t ht) hu
    rw [step_expand _ (onsA_symm ε f x t) (hApd t).det_pos.ne'.isUnit β hβ0.ne' (x t) u
      (onsGrad f x t)] at hproj
    have hq : qform (onsA ε f x t) (x t - u) =
        qform (onsA ε f x (t - 1)) (x t - u) + (inner ℝ (onsGrad f x t) (x t - u)) ^ 2 := by
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [qform_onsA, qform_onsA, Finset.sum_Icc_succ_top (by omega : 1 ≤ s + 1)]
      ring
    set a := inner ℝ (onsGrad f x t) (x t - u)
    set r := WithLp.ofLp (onsGrad f x t) ⬝ᵥ ((onsA ε f x t)⁻¹ *ᵥ WithLp.ofLp (onsGrad f x t))
    set Q := qform (onsA ε f x t) (x t - u)
    set Φ := qform (onsA ε f x t) (x (t + 1) - u)
    have key : β / 2 * Φ ≤ β / 2 * Q - a + r / (2 * β) := by
      calc β / 2 * Φ ≤ β / 2 * (Q - 2 / β * a + 1 / β ^ 2 * r) :=
            mul_le_mul_of_nonneg_left hproj (by positivity)
        _ = β / 2 * Q - a + r / (2 * β) := by field_simp
    rw [hq] at key
    nlinarith
  have htel : ∀ N : ℕ, ∑ t ∈ Finset.Icc 1 N, (f t (x t) - f t u) ≤
      β / 2 * (qform (onsA ε f x 0) (x 1 - u) - qform (onsA ε f x N) (x (N + 1) - u)) +
      (∑ t ∈ Finset.Icc 1 N,
        WithLp.ofLp (onsGrad f x t) ⬝ᵥ ((onsA ε f x t)⁻¹ *ᵥ WithLp.ofLp (onsGrad f x t))) /
        (2 * β) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      have h := hround (N + 1) (by omega)
      simp only [Nat.add_sub_cancel] at h
      rw [add_div]
      linarith
  have hfin := htel T
  have hq0 : qform (onsA ε f x 0) (x 1 - u) ≤ ε * D ^ 2 := by
    rw [qform_onsA]
    simp only [Finset.Icc_eq_empty_of_lt (show 0 < 1 by norm_num), Finset.sum_empty, zero_add]
    have h1 := hdiam (x 1) hx1 u hu
    have h2 : ‖x 1 - u‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    exact mul_le_mul_of_nonneg_left h2 hε0.le
  have hqT := hqnn T (x (T + 1) - u)
  have hgg : ∀ t, 1 ≤ t →
      (fun i => WithLp.ofLp (onsGrad f x i)) t ⬝ᵥ (fun i => WithLp.ofLp (onsGrad f x i)) t ≤ G ^ 2 := by
    intro t ht
    have e : ‖onsGrad f x t‖ ^ 2 = WithLp.ofLp (onsGrad f x t) ⬝ᵥ WithLp.ofLp (onsGrad f x t) := by
      rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    show WithLp.ofLp (onsGrad f x t) ⬝ᵥ WithLp.ofLp (onsGrad f x t) ≤ G ^ 2
    rw [← e]
    exact pow_le_pow_left₀ (norm_nonneg _) (hgrad t ht _ (hx t ht)) 2
  have hpot : (∑ t ∈ Finset.Icc 1 T,
        WithLp.ofLp (onsGrad f x t) ⬝ᵥ ((onsA ε f x t)⁻¹ *ᵥ WithLp.ofLp (onsGrad f x t)))
      ≤ n * Real.log (1 + T * G ^ 2 / (n * ε)) :=
    potential_gen ε G hε0 hn (fun i => WithLp.ofLp (onsGrad f x i)) hgg T
  have hnum := numeric' hD hα hG (show β = 1 / 2 * min (1 / (4 * G * D)) α by linarith) hεβ hn T hT3
  have hβεD : β / 2 * (ε * D ^ 2) = 1 / (2 * β) := by
    rw [hεβ]; field_simp
  have hS := div_le_div_of_nonneg_right hpot (by positivity : (0:ℝ) ≤ 2 * β)
  have hfirst : β / 2 * (qform (onsA ε f x 0) (x 1 - u) - qform (onsA ε f x T) (x (T + 1) - u))
      ≤ 1 / (2 * β) := by
    rw [← hβεD]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e2 : 1 / (2 * β) * (n * Real.log (1 + T * G ^ 2 / (n * ε)) + 1) =
      n * Real.log (1 + T * G ^ 2 / (n * ε)) / (2 * β) + 1 / (2 * β) := by ring
  linarith
