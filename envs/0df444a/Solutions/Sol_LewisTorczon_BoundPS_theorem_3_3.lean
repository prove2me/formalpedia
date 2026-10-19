-- Prove2me | solution 1 for LewisTorczon.BoundPS.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T05:07:31.250115+00:00
-- url     : https://prove2.me/submissions/61d1985d-60d0-4894-bad5-834853e3f8e1

-- Licensed under Apache 2.0. Full exact theorem: Lewis–Torczon full projected-stationarity convergence, Theorem 3.3.
import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS


open Filter Topology LewisTorczon.BoundPS

namespace BoundPSProof
noncomputable section

lemma clamp_finite {a b : EReal} (hab : a < b) (t : ℝ) :
    max a (min b (t : EReal)) ≠ ⊤ ∧ max a (min b (t : EReal)) ≠ ⊥ := by
  constructor
  · exact (max_lt (lt_of_lt_of_le hab le_top)
      (lt_of_le_of_lt (min_le_right _ _) (EReal.coe_lt_top t))).ne
  · exact (lt_of_lt_of_le (lt_min (lt_of_le_of_lt bot_le hab)
      (EReal.bot_lt_coe t)) (le_max_right _ _)).ne'

lemma coe_clamp {a b : EReal} (hab : a < b) (t : ℝ) :
    (clampCoord a b t : EReal) = max a (min b (t : EReal)) := by
  exact EReal.coe_toReal (clamp_finite hab t).1 (clamp_finite hab t).2

lemma clamp_mem {a b : EReal} (hab : a < b) (t : ℝ) :
    a ≤ (clampCoord a b t : EReal) ∧ (clampCoord a b t : EReal) ≤ b := by
  rw [coe_clamp hab]
  exact ⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩

lemma clamp_fix {a b : EReal} {x : ℝ}
    (ha : a ≤ (x : EReal)) (hb : (x : EReal) ≤ b) : clampCoord a b x = x := by
  simp only [clampCoord, min_eq_right hb, max_eq_right ha, EReal.toReal_coe]

lemma continuous_clamp {a b : EReal} (hab : a < b) : Continuous (clampCoord a b) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (EReal.tendsto_toReal (clamp_finite hab t).1 (clamp_finite hab t).2).comp
    ((continuous_const.max (continuous_const.min continuous_coe_real_ereal)).continuousAt)

lemma clamp_above_input {a b : EReal} (hab : a < b) {x t : ℝ}
    (ha : a ≤ (x : EReal)) (h : x < clampCoord a b t) : clampCoord a b t ≤ t := by
  have hx : (x : EReal) < max a (min b (t : EReal)) := by
    rw [← coe_clamp hab]; exact_mod_cast h
  have hm : a < min b (t : EReal) := by
    rcases (lt_max_iff.mp (lt_of_le_of_lt ha hx)) with hbad | hm
    · exact (lt_irrefl _ hbad).elim
    · exact hm
  have ht : (clampCoord a b t : EReal) ≤ (t : EReal) := by
    rw [coe_clamp hab, max_eq_right hm.le]
    exact min_le_right _ _
  exact_mod_cast ht

lemma clamp_below_input {a b : EReal} (hab : a < b) {x t : ℝ}
    (hb : (x : EReal) ≤ b) (h : clampCoord a b t < x) : t ≤ clampCoord a b t := by
  have hx : max a (min b (t : EReal)) < (x : EReal) := by
    rw [← coe_clamp hab]; exact_mod_cast h
  have ht : (t : EReal) ≤ b := by
    by_contra hn
    have he : min b (t : EReal) = b := min_eq_left (le_of_not_ge hn)
    have hcontra : (x : EReal) ≤ max a (min b (t : EReal)) := by
      rw [he]
      exact le_trans hb (le_max_right a b)
    exact (not_le_of_gt hx) hcontra
  have he : (t : EReal) ≤ (clampCoord a b t : EReal) := by
    rw [coe_clamp hab, min_eq_right ht]
    exact le_max_right _ _
  exact_mod_cast he

lemma scalar_move_pos {a b : EReal} (hab : a < b) {x g α : ℝ}
    (ha : a ≤ (x : EReal)) (_hb : (x : EReal) ≤ b)
    (hα : 0 ≤ α) (hstep : α ≤ clampCoord a b (x-g) - x)
    (hq : 0 < clampCoord a b (x-g) - x) :
    (a ≤ ((x+α : ℝ) : EReal) ∧ ((x+α : ℝ) : EReal) ≤ b) ∧
      α*g ≤ -α*(clampCoord a b (x-g)-x) := by
  have hc := clamp_above_input hab ha (show x < clampCoord a b (x-g) by linarith)
  have hmem := clamp_mem hab (x-g)
  constructor
  · constructor
    · exact le_trans ha (by exact_mod_cast (show x ≤ x+α by linarith))
    · exact le_trans (by exact_mod_cast (show x+α ≤ clampCoord a b (x-g) by linarith)) hmem.2
  · nlinarith [mul_nonneg hα (show 0 ≤ x-g-clampCoord a b (x-g) by linarith)]

lemma scalar_move_neg {a b : EReal} (hab : a < b) {x g α : ℝ}
    (_ha : a ≤ (x : EReal)) (hb : (x : EReal) ≤ b)
    (hα : α ≤ 0) (hstep : clampCoord a b (x-g)-x ≤ α)
    (hq : clampCoord a b (x-g)-x < 0) :
    (a ≤ ((x+α : ℝ) : EReal) ∧ ((x+α : ℝ) : EReal) ≤ b) ∧
      α*g ≤ -α*(clampCoord a b (x-g)-x) := by
  have hc := clamp_below_input hab hb (show clampCoord a b (x-g) < x by linarith)
  have hmem := clamp_mem hab (x-g)
  constructor
  · constructor
    · exact le_trans hmem.1 (by exact_mod_cast (show clampCoord a b (x-g) ≤ x+α by linarith))
    · exact le_trans (by exact_mod_cast (show x+α ≤ x by linarith)) hb
  · nlinarith [mul_nonneg (show 0 ≤ -α by linarith)
      (show 0 ≤ clampCoord a b (x-g)-(x-g) by linarith)]

end
end BoundPSProof


open Set Finset Filter Topology LewisTorczon.BoundPS

namespace BoundPSProof
noncomputable section

variable {n : ℕ}

lemma continuous_boxProj {lo hi : Fin n → EReal} (h : ∀ j, lo j < hi j) :
    Continuous (boxProj lo hi) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  exact (continuous_clamp (h j)).comp (PiLp.continuous_apply 2 _ j)

lemma continuousOn_projQ {lo hi : Fin n → EReal} (h : ∀ j, lo j < hi j)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) : ContinuousOn (projQ lo hi f) U := by
  have hg : ContinuousOn (gradient f) U :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen hU le_rfl)
  exact ((continuous_boxProj h).comp_continuousOn (continuousOn_id.sub hg)).sub continuousOn_id

lemma norm_le_sum_abs (x : EuclideanSpace ℝ (Fin n)) : ‖x‖ ≤ ∑ j, |x j| := by
  have he : x = ∑ j, EuclideanSpace.single j (x j) := by
    ext i
    simp
  calc
    ‖x‖ = ‖∑ j, EuclideanSpace.single j (x j)‖ := congrArg norm he
    _ ≤ ∑ j, ‖EuclideanSpace.single j (x j)‖ := norm_sum_le _ _
    _ = ∑ j, |x j| := by simp

lemma exists_large_coordinate {ε : ℝ} (_hε : 0 < ε) (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ε ≤ ‖x‖) :
    ∃ j, ε / (n : ℝ) ≤ |x j| := by
  by_contra h
  push Not at h
  have hs : (∑ j, |x j|) < ∑ _j : Fin n, ε / (n : ℝ) := by
    exact Finset.sum_lt_sum (fun j _ => (h j).le) ⟨⟨0, hn⟩, mem_univ _, h _⟩
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have he : (∑ _j : Fin n, ε / (n : ℝ)) = ε := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [he] at hs
  exact (not_lt_of_ge (hx.trans (norm_le_sum_abs x))) hs

lemma coordinate_move {lo hi : Fin n → EReal} (h : ∀ j, lo j < hi j)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ box lo hi) (j : Fin n) (α : ℝ)
    (hsign : 0 < α * (projQ lo hi f x) j)
    (hlen : |α| ≤ |(projQ lo hi f x) j|) :
    x + EuclideanSpace.single j α ∈ box lo hi ∧
      inner ℝ (gradient f x) (EuclideanSpace.single j α) ≤
        -|(projQ lo hi f x) j| * ‖EuclideanSpace.single j α‖ := by
  let q := clampCoord (lo j) (hi j) (x j - gradient f x j) - x j
  have he : (projQ lo hi f x) j = q := rfl
  rw [he] at hsign hlen ⊢
  have hq : q ≠ 0 := by intro hz; simp [hz] at hsign
  have hs : (lo j ≤ ((x j + α : ℝ) : EReal) ∧
      ((x j + α : ℝ) : EReal) ≤ hi j) ∧ α * gradient f x j ≤ -|q| * |α| := by
    rcases lt_or_gt_of_ne hq with hqn | hqp
    · have han : α < 0 := by nlinarith
      have ht := scalar_move_neg (h j) (hx j).1 (hx j).2 han.le
        (show q ≤ α by simpa [abs_of_neg han, abs_of_neg hqn] using hlen) hqn
      refine ⟨ht.1, ?_⟩
      rw [abs_of_neg han, abs_of_neg hqn]
      nlinarith [ht.2]
    · have hap : 0 < α := by nlinarith
      have ht := scalar_move_pos (h j) (hx j).1 (hx j).2 hap.le
        (show α ≤ q by simpa [abs_of_pos hap, abs_of_pos hqp] using hlen) hqp
      refine ⟨ht.1, ?_⟩
      rw [abs_of_pos hap, abs_of_pos hqp]
      nlinarith [ht.2]
  constructor
  · intro i
    by_cases hij : i = j
    · subst i
      simpa using hs.1
    · simpa [PiLp.single_apply, hij] using hx i
  · rw [EuclideanSpace.inner_single_right]
    simpa only [conj_trivial, PiLp.norm_single, Real.norm_eq_abs, mul_comm] using hs.2

end
end BoundPSProof


open Finset Matrix LewisTorczon.BoundPS

namespace BoundPSProof
noncomputable section

variable {n m : ℕ}

def coreMatrix (P : GPSParams n) (M : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) ℝ := P.B * M.map (fun z : ℤ => (z : ℝ))

lemma coreMatrix_det_ne_zero (P : GPSParams n) {M : Matrix (Fin n) (Fin n) ℤ}
    (hM : M ∈ P.𝕄) : (coreMatrix P M).det ≠ 0 := by
  have hm : (M.map (fun z : ℤ => (z : ℝ))).det ≠ 0 := by
    change ((Int.castRingHom ℝ).mapMatrix M).det ≠ 0
    rw [← (Int.castRingHom ℝ).map_det]
    change (M.det : ℝ) ≠ 0
    exact_mod_cast P.𝕄_det_ne_zero M hM
  change (P.B * M.map (fun z : ℤ => (z : ℝ))).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero P.B_det_ne_zero hm

lemma diagonal_entry_ne_zero (P : GPSParams n) {M : Matrix (Fin n) (Fin n) ℤ}
    (hM : M ∈ P.𝕄) (hd : (coreMatrix P M).IsDiag) (j : Fin n) :
    coreMatrix P M j j ≠ 0 := by
  have hh := coreMatrix_det_ne_zero P hM
  rw [← hd.diagonal_diag, Matrix.det_diagonal] at hh
  exact (Finset.prod_ne_zero_iff.mp hh) j (mem_univ j)

lemma stepOf_neg (P : GPSParams n) (Δ : ℝ) (c : Fin n → ℤ) :
    stepOf P Δ (-c) = -stepOf P Δ c := by
  ext i
  simp [stepOf, Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]

lemma stepOf_column (P : GPSParams n) (R : GPSRun n m) (k : ℕ)
    (hd : (coreMatrix P (R.M k)).IsDiag) (Δ : ℝ) (j : Fin n) :
    stepOf P Δ ((R.M k).transpose j) =
      EuclideanSpace.single j (Δ * coreMatrix P (R.M k) j j) := by
  have he (i : Fin n) : stepOf P Δ ((R.M k).transpose j) i =
      Δ * coreMatrix P (R.M k) i j := by
    simp [stepOf, coreMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  ext i
  rw [he]
  by_cases hij : i = j
  · subst i; simp
  · simp [hij, hd hij]

lemma exists_core_single (P : GPSParams n) (R : GPSRun n m) (k : ℕ)
    (hd : (coreMatrix P (R.M k)).IsDiag) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (j : Fin n) (α : ℝ) (ha : |α| = Δ * |coreMatrix P (R.M k) j j|) :
    ∃ c ∈ coreCols R k, stepOf P Δ c = EuclideanSpace.single j α := by
  have he : |α| = |Δ * coreMatrix P (R.M k) j j| := by
    simpa only [abs_mul, abs_of_nonneg hΔ] using ha
  rcases abs_eq_abs.mp he with h | h
  · refine ⟨(R.M k).transpose j, ⟨j, Or.inl rfl⟩, ?_⟩
    rw [stepOf_column P R k hd Δ j, h]
  · refine ⟨-((R.M k).transpose j), ⟨j, Or.inr rfl⟩, ?_⟩
    rw [stepOf_neg, stepOf_column P R k hd Δ j, h]
    ext i
    by_cases hij : i = j <;> simp [hij]

lemma exists_core_bounds (P : GPSParams n) (R : GPSRun n m)
    (hmem : ∀ k, R.M k ∈ P.𝕄) (hdiag : ∀ k, (coreMatrix P (R.M k)).IsDiag)
    (hn : 0 < n) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ k j, a ≤ |coreMatrix P (R.M k) j j| ∧ |coreMatrix P (R.M k) j j| ≤ b := by
  classical
  let T := (P.𝕄.filter fun M => (coreMatrix P M).IsDiag).product
    (Finset.univ : Finset (Fin n))
  let F : Matrix (Fin n) (Fin n) ℤ × Fin n → ℝ :=
    fun p => |coreMatrix P p.1 p.2 p.2|
  let S : Finset ℝ := T.image F
  have hS : ∀ k j, |coreMatrix P (R.M k) j j| ∈ S := by
    intro k j
    change F (R.M k, j) ∈ T.image F
    apply Finset.mem_image.mpr
    refine ⟨(R.M k, j), ?_, rfl⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hmem k, hdiag k⟩, Finset.mem_univ j⟩
  have hpos : ∀ z ∈ S, 0 < z := by
    intro z hz
    change z ∈ T.image F at hz
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hz
    have hp' := Finset.mem_product.mp hp
    have hM := Finset.mem_filter.mp hp'.1
    rw [← he]
    change 0 < |coreMatrix P p.1 p.2 p.2|
    exact abs_pos.mpr (diagonal_entry_ne_zero P hM.1 hM.2 p.2)
  have hs : S.Nonempty := ⟨_, hS 0 ⟨0,hn⟩⟩
  refine ⟨S.min' hs, S.max' hs, hpos _ (S.min'_mem hs), hpos _ (S.max'_mem hs), ?_⟩
  intro k j
  exact ⟨S.min'_le _ (hS k j), S.le_max' _ (hS k j)⟩

lemma stepOf_eq_smul (P : GPSParams n) (Δ : ℝ) (c : Fin n → ℤ) :
    stepOf P Δ c = Δ • Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P.B (intVec c) := by
  ext i
  rfl

lemma bounded_step (P : GPSParams n) (R : GPSRun n m) (hb : BoundedCols R) :
    ∃ C : ℝ, 0 < C ∧ ∀ k Δ, 0 ≤ Δ → ∀ c ∈ cols R k, ‖stepOf P Δ c‖ ≤ C * Δ := by
  obtain ⟨K,hK,hbound⟩ := hb
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) P.B
  refine ⟨‖T‖ * K + 1, by positivity, ?_⟩
  intro k Δ hΔ c hc
  rw [stepOf_eq_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hΔ]
  have ht : ‖T (intVec c)‖ ≤ ‖T‖ * K :=
    (T.le_opNorm (intVec c)).trans (mul_le_mul_of_nonneg_left (hbound k c hc).le (norm_nonneg T))
  change Δ * ‖T (intVec c)‖ ≤ (‖T‖ * K + 1) * Δ
  nlinarith [mul_le_mul_of_nonneg_left ht hΔ]

end
end BoundPSProof


open LewisTorczon.BoundPS

namespace BoundPSProof
noncomputable section

lemma core_descent_move {n m : ℕ} (P : GPSParams n) (R : GPSRun n m)
    {lo hi : Fin n → EReal} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hR : IsGPSRun P lo hi f R) (hlohi : ∀ j, lo j < hi j) (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ box lo hi) (k : ℕ)
    {ε a b Δ : ℝ} (hε : 0 < ε) (hq : ε ≤ ‖projQ lo hi f x‖)
    (ha : 0 < a) (hΔ : 0 < Δ)
    (hab : ∀ j, a ≤ |coreMatrix P (R.M k) j j| ∧ |coreMatrix P (R.M k) j j| ≤ b)
    (hsmall : b * Δ ≤ ε / (n : ℝ)) :
    ∃ c ∈ coreCols R k, x + stepOf P Δ c ∈ box lo hi ∧
      a * Δ ≤ ‖stepOf P Δ c‖ ∧ ‖stepOf P Δ c‖ ≤ b * Δ ∧
      inner ℝ (gradient f x) (stepOf P Δ c) ≤ -(ε / (n : ℝ)) * ‖stepOf P Δ c‖ := by
  obtain ⟨j,hj⟩ := exists_large_coordinate hε hn (projQ lo hi f x) hq
  let q := (projQ lo hi f x) j
  let d := coreMatrix P (R.M k) j j
  have hγ : 0 < ε / (n : ℝ) := div_pos hε (by exact_mod_cast hn)
  have hq0 : q ≠ 0 := by
    intro hzero
    have : |q| = 0 := by rw [hzero, abs_zero]
    change ε / (n : ℝ) ≤ |q| at hj
    linarith
  have hd : 0 < |d| := lt_of_lt_of_le ha (hab j).1
  let α := if 0 < q then Δ * |d| else -(Δ * |d|)
  have hmag : |α| = Δ * |d| := by
    dsimp [α]
    split_ifs <;> simp [abs_of_pos (mul_pos hΔ hd)]
  have hsign : 0 < α*q := by
    dsimp [α]
    split_ifs with hpos
    · exact mul_pos (mul_pos hΔ hd) hpos
    · have hneg : q < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hq0
      exact mul_pos_of_neg_of_neg (neg_neg_of_pos (mul_pos hΔ hd)) hneg
  have hlen : |α| ≤ |q| := by
    rw [hmag]
    calc
      Δ * |d| ≤ b * Δ := by nlinarith [mul_le_mul_of_nonneg_left (hab j).2 hΔ.le]
      _ ≤ ε / (n : ℝ) := hsmall
      _ ≤ |q| := hj
  obtain ⟨c,hc,he⟩ := exists_core_single P R k (hR.diag k) hΔ.le j α hmag
  have hmove := coordinate_move hlohi hx j α hsign hlen
  refine ⟨c,hc,?_,?_,?_,?_⟩
  · simpa only [he] using hmove.1
  · rw [he]
    have hnrm : ‖EuclideanSpace.single j α‖ = Δ * |d| := by simpa using hmag
    rw [hnrm]
    nlinarith [mul_le_mul_of_nonneg_right (hab j).1 hΔ.le]
  · rw [he]
    have hnrm : ‖EuclideanSpace.single j α‖ = Δ * |d| := by simpa using hmag
    rw [hnrm]
    nlinarith [mul_le_mul_of_nonneg_right (hab j).2 hΔ.le]
  · rw [he]
    exact hmove.2.trans (mul_le_mul_of_nonneg_right (neg_le_neg hj) (norm_nonneg _))

end
end BoundPSProof


open Filter Set
open scoped Topology
namespace BoundPSProof
open LewisTorczon.BoundPS

variable {n m : ℕ} {P : GPSParams n} {lo hi : Fin n → EReal}
  {f : EuclideanSpace ℝ (Fin n) → ℝ} {R : GPSRun n m}

theorem delta_pos (hR : IsGPSRun P lo hi f R) (k : ℕ) : 0 < R.Δ k := by
  have ht : 0 < (P.τ : ℝ) := by exact_mod_cast lt_trans zero_lt_one P.one_lt_τ
  induction k with
  | zero => exact hR.Δ_zero_pos
  | succ k ih =>
    by_cases hs : f (R.x k + R.s k) < f (R.x k)
    · obtain ⟨w, _, hw⟩ := hR.Δ_succ_success k hs
      rw [hw]
      exact mul_pos (zpow_pos ht _) ih
    · rw [hR.Δ_succ_failure k hs]
      exact mul_pos (zpow_pos ht _) ih

theorem delta_le_next_of_success (hR : IsGPSRun P lo hi f R) (k : ℕ)
    (hs : f (R.x k + R.s k) < f (R.x k)) : R.Δ k ≤ R.Δ (k+1) := by
  obtain ⟨w, hw, he⟩ := hR.Δ_succ_success k hs
  rw [he]
  have ht : (1 : ℝ) ≤ P.τ := by exact_mod_cast le_of_lt P.one_lt_τ
  have hp : (1 : ℝ) ≤ (P.τ : ℝ)^w := one_le_zpow₀ ht (P.W_nonneg w hw)
  nlinarith [delta_pos hR k]

theorem iterate_mem (hR : IsGPSRun P lo hi f R) (k : ℕ) : R.x k ∈ box lo hi := by
  induction k with
  | zero => exact hR.x_zero_mem
  | succ k ih =>
    rw [hR.x_succ]
    split
    · exact hR.step_feasible k
    · exact ih

theorem value_antitone (hR : IsGPSRun P lo hi f R) : Antitone (fun k => f (R.x k)) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [hR.x_succ]
  split
  · exact le_of_lt ‹f (R.x k + R.s k) < f (R.x k)›
  · exact le_rfl

theorem iterate_level (hR : IsGPSRun P lo hi f R) (k : ℕ) :
    R.x k ∈ levelSet lo hi f (R.x 0) :=
  ⟨iterate_mem hR k, value_antitone hR (Nat.zero_le k)⟩

end BoundPSProof


open Set Metric
namespace BoundPSProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

 theorem uniform_taylor {f : E → ℝ} {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ K, ∀ v : E, ‖v‖ < δ →
      ‖f (x+v)-f x-fderiv ℝ f x v‖ ≤ η*‖v‖ := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hKr : IsCompact (cthickening r K) := hK.cthickening
  have hc := (hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hrU
  obtain ⟨d, hd, hdiff⟩ := Metric.uniformContinuousOn_iff.mp
    (hKr.uniformContinuousOn_of_continuous hc) η hη
  refine ⟨min r d, lt_min hr hd, ?_⟩
  intro x hx v hv
  have hball : ball x (min r d) ⊆ cthickening r K := by
    intro z hz
    exact mem_cthickening_of_dist_le z x r K hx
      (le_trans (le_of_lt hz) (min_le_left _ _))
  have hdif : ∀ z ∈ ball x (min r d), DifferentiableAt ℝ f z := by
    intro z hz
    exact (hf.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds (hrU (hball hz)))
  have hb : ∀ z ∈ ball x (min r d), ‖fderiv ℝ f z-fderiv ℝ f x‖ ≤ η := by
    intro z hz
    exact le_of_lt (by simpa [dist_eq_norm] using
      (hdiff z (hball hz) x (self_subset_cthickening K hx)
        (lt_of_lt_of_le hz (min_le_right _ _))))
  have he := (convex_ball x (min r d)).norm_image_sub_le_of_norm_fderiv_le'
    hdif hb (mem_ball_self (lt_min hr hd))
    (show x+v ∈ ball x (min r d) by simpa [dist_eq_norm] using hv)
  simpa using he

end BoundPSProof


open Set Filter
open scoped Topology
namespace BoundPSProof
open LewisTorczon.BoundPS

 theorem transfer_core_descent {n m : ℕ} {P : GPSParams n} {lo hi : Fin n → EReal}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {R : GPSRun n m}
    (hR : IsGPSRun P lo hi f R) (hstrong : StrongHyp P lo hi f R)
    {k : ℕ} {a γ : ℝ} (ha : 0 < a) (hγ : 0 < γ)
    {c : Fin n → ℤ} (hc : c ∈ coreCols R k)
    (hfeas : R.x k + stepOf P (R.Δ k) c ∈ box lo hi)
    (hsize : a * R.Δ k ≤ ‖stepOf P (R.Δ k) c‖)
    (hslope : fderiv ℝ f (R.x k) (stepOf P (R.Δ k) c) ≤ -γ * ‖stepOf P (R.Δ k) c‖)
    (hrem : ‖f (R.x k+stepOf P (R.Δ k) c)-f (R.x k)-
      fderiv ℝ f (R.x k) (stepOf P (R.Δ k) c)‖ ≤ (γ/2)*‖stepOf P (R.Δ k) c‖) :
    f (R.x k+R.s k) < f (R.x k) ∧
      (a*γ/2)*R.Δ k ≤ f (R.x k)-f (R.x (k+1)) := by
  have hr := le_trans (le_abs_self (f (R.x k+stepOf P (R.Δ k) c)-f (R.x k)-
    fderiv ℝ f (R.x k) (stepOf P (R.Δ k) c))) hrem
  have hmul := mul_le_mul_of_nonneg_left hsize (show 0 ≤ γ/2 by positivity)
  have hdrop : (a*γ/2)*R.Δ k ≤ f (R.x k)-f (R.x k+stepOf P (R.Δ k) c) := by
    nlinarith
  have hdelta := delta_pos hR k
  have hpos : 0 < (a*γ/2)*R.Δ k := by positivity
  have hcore : f (R.x k+stepOf P (R.Δ k) c) < f (R.x k) := by linarith
  have hbest := hstrong k ⟨c,hc,hfeas,hcore⟩ c hc hfeas
  have hs : f (R.x k+R.s k) < f (R.x k) := lt_of_le_of_lt hbest hcore
  refine ⟨hs, ?_⟩
  rw [hR.x_succ, if_pos hs]
  linarith

end BoundPSProof


open Set Filter
open scoped Topology
namespace BoundPSProof
open LewisTorczon.BoundPS

 theorem uniform_descent_of_core {n m : ℕ} {P : GPSParams n} {lo hi : Fin n → EReal}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {R : GPSRun n m}
    (hn : 0 < n) (hR : IsGPSRun P lo hi f R) (hstrong : StrongHyp P lo hi f R)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hbox : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (hK : IsCompact (levelSet lo hi f (R.x 0)))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcore : ∀ ε > 0, ∀ k, ε ≤ ‖projQ lo hi f (R.x k)‖ → b*R.Δ k ≤ ε/(n:ℝ) →
      ∃ c ∈ coreCols R k,
        R.x k+stepOf P (R.Δ k) c ∈ box lo hi ∧
        a*R.Δ k ≤ ‖stepOf P (R.Δ k) c‖ ∧
        ‖stepOf P (R.Δ k) c‖ ≤ b*R.Δ k ∧
        inner ℝ (gradient f (R.x k)) (stepOf P (R.Δ k) c) ≤
          -(ε/(n:ℝ))*‖stepOf P (R.Δ k) c‖) :
    ∀ ε > 0, ∃ δ > 0, ∃ c > 0, ∀ k,
      ε ≤ ‖projQ lo hi f (R.x k)‖ → R.Δ k < δ →
      f (R.x k+R.s k) < f (R.x k) ∧ c*R.Δ k ≤ f (R.x k)-f (R.x (k+1)) := by
  intro ε hε
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hγ : 0 < ε/(n:ℝ) := div_pos hε hnR
  obtain ⟨r, hr, htaylor⟩ := uniform_taylor hK hU
    (fun _ hx => hbox hx.1) hf (half_pos hγ)
  refine ⟨min (r/b) ((ε/(n:ℝ))/b), lt_min (div_pos hr hb) (div_pos hγ hb),
    a*(ε/(n:ℝ))/2, by positivity, ?_⟩
  intro k hq hδ
  have hbr : b*R.Δ k < r := by
    have := (lt_div_iff₀ hb).mp (lt_of_lt_of_le hδ (min_le_left _ _))
    nlinarith
  have hbg : b*R.Δ k ≤ ε/(n:ℝ) := by
    have := (lt_div_iff₀ hb).mp (lt_of_lt_of_le hδ (min_le_right _ _))
    nlinarith
  obtain ⟨c, hc, hfeas, hsize, hupper, hslope⟩ := hcore ε hε k hq hbg
  rw [inner_gradient_left] at hslope
  exact transfer_core_descent hR hstrong ha hγ hc hfeas hsize hslope
    (htaylor (R.x k) (iterate_level hR k) _ (lt_of_le_of_lt hupper hbr))

end BoundPSProof


open Set Filter
open scoped Topology
namespace BoundPSProof
open LewisTorczon.BoundPS

 theorem objective_cauchy {n m : ℕ} {P : GPSParams n} {lo hi : Fin n → EReal}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {R : GPSRun n m}
    (hR : IsGPSRun P lo hi f R)
    (hK : IsCompact (levelSet lo hi f (R.x 0)))
    (hf : ContinuousOn f (levelSet lo hi f (R.x 0))) :
    CauchySeq (fun k => f (R.x k)) := by
  have hb : BddBelow (range (fun k => f (R.x k))) :=
    (hK.bddBelow_image hf).mono (by
      rintro _ ⟨k, rfl⟩
      exact ⟨R.x k, iterate_level hR k, rfl⟩)
  exact (tendsto_atTop_ciInf (value_antitone hR) hb).cauchySeq

end BoundPSProof


open Filter Set
open scoped Topology
namespace BoundPSProof
open LewisTorczon.BoundPS

 theorem arbitrarily_late_small {n m : ℕ} {P : GPSParams n} {lo hi : Fin n → EReal}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {R : GPSRun n m}
    (hR : IsGPSRun P lo hi f R) (hΔ : Tendsto R.Δ atTop (𝓝 0))
    {q : ℕ → ℝ} (hs : ∀ ε > 0, ∃ δ > 0, ∀ k, ε ≤ q k → R.Δ k < δ →
      f (R.x k+R.s k) < f (R.x k)) :
    ∀ ε > 0, ∀ N : ℕ, ∃ k ≥ N, q k < ε := by
  intro ε hε N
  by_contra hn
  push Not at hn
  obtain ⟨δ, hδ, hdec⟩ := hs ε hε
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hΔ.eventually (gt_mem_nhds hδ))
  let A := max N M
  have hinc : ∀ k ≥ A, R.Δ k ≤ R.Δ (k+1) := by
    intro k hk
    exact delta_le_next_of_success hR k (hdec k
      (hn k (le_trans (le_max_left _ _) hk))
      (hM k (le_trans (le_max_right _ _) hk)))
  have hlower : ∀ k ≥ A, R.Δ A ≤ R.Δ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih => exact le_trans ih (hinc k hk)
  have hz : R.Δ A ≤ (0 : ℝ) := ge_of_tendsto hΔ
    (eventually_atTop.2 ⟨A, hlower⟩)
  exact (not_le_of_gt (delta_pos hR A)) hz

end BoundPSProof


open Filter Set
open scoped Topology
namespace BoundPSProof

variable {E : Type*} [PseudoMetricSpace E]

lemma distance_of_descent {x : ℕ → E} {v : ℕ → ℝ} {σ : ℝ} (hσ : 0 ≤ σ)
    {a b : ℕ} (hab : a ≤ b)
    (h : ∀ k, a ≤ k → k < b → σ * dist (x k) (x (k+1)) ≤ v k-v (k+1)) :
    σ * dist (x a) (x b) ≤ v a-v b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hi := ih (fun k hak hkb => h k hak (by omega))
    have hs := h b hab (by omega)
    have ht := mul_le_mul_of_nonneg_left (dist_triangle (x a) (x b) (x (b+1))) hσ
    nlinarith

 theorem excursion_tendsto {x : ℕ → E} {q : E → ℝ} {K : Set E} {v : ℕ → ℝ}
    (hx : ∀ k, x k ∈ K) (hq : UniformContinuousOn q K) (hq0 : ∀ k, 0 ≤ q (x k))
    (hv : CauchySeq v)
    (hlow : ∀ ε > 0, ∀ N : ℕ, ∃ k ≥ N, q (x k) < ε)
    (hdrop : ∀ ε > 0, ∃ σ > 0, ∃ N : ℕ, ∀ k ≥ N, ε ≤ q (x k) →
      σ * dist (x k) (x (k+1)) ≤ v k-v (k+1)) :
    Tendsto (fun k => q (x k)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨ρ, hρ, hcont⟩ := Metric.uniformContinuousOn_iff.mp hq (ε/2) (by positivity)
  obtain ⟨σ, hσ, N, hN⟩ := hdrop (ε/2) (by positivity)
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp hv (σ*ρ) (mul_pos hσ hρ)
  refine ⟨max N M, ?_⟩
  intro a ha
  have hex : ∃ d : ℕ, q (x (a+d)) < ε/2 := by
    obtain ⟨b, hab, hb⟩ := hlow (ε/2) (by positivity) a
    exact ⟨b-a, by simpa [Nat.add_sub_of_le hab] using hb⟩
  let d := Nat.find hex
  have hd : q (x (a+d)) < ε/2 := Nat.find_spec hex
  have hbefore : ∀ k, a ≤ k → k < a+d → ε/2 ≤ q (x k) := by
    intro k hak hkd
    have hn := Nat.find_min hex (show k-a < d by omega)
    have he : a+(k-a)=k := Nat.add_sub_of_le hak
    rw [he] at hn
    exact le_of_not_gt hn
  have hdist := distance_of_descent (le_of_lt hσ) (Nat.le_add_right a d)
    (fun k hak hkb => hN k (le_trans (le_trans (le_max_left N M) ha) hak)
      (hbefore k hak hkb))
  have hval := hM a (le_trans (le_max_right N M) ha) (a+d)
    (by omega)
  have hclose : dist (x a) (x (a+d)) < ρ := by
    have hlt : v a-v (a+d) < σ*ρ := lt_of_le_of_lt (le_abs_self _) (by
      simpa [Real.dist_eq] using hval)
    nlinarith
  have hqc := hcont (x a) (hx a) (x (a+d)) (hx _) hclose
  have hqa : q (x a) < ε := by
    have := lt_of_le_of_lt (le_abs_self (q (x a)-q (x (a+d))))
      (show |q (x a)-q (x (a+d))| < ε/2 from by simpa [Real.dist_eq] using hqc)
    linarith
  simpa [Real.dist_eq, abs_of_nonneg (hq0 a)] using hqa

end BoundPSProof


open Filter Set
open scoped Topology
namespace BoundPSProof
open LewisTorczon.BoundPS

 theorem convergence_from_descent {n m : ℕ} {P : GPSParams n} {lo hi : Fin n → EReal}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {R : GPSRun n m}
    (hR : IsGPSRun P lo hi f R) (hΔ : Tendsto R.Δ atTop (𝓝 0))
    (hK : IsCompact (levelSet lo hi f (R.x 0)))
    (hf : ContinuousOn f (levelSet lo hi f (R.x 0)))
    {q : EuclideanSpace ℝ (Fin n) → ℝ}
    (hq : ContinuousOn q (levelSet lo hi f (R.x 0))) (hq0 : ∀ k, 0 ≤ q (R.x k))
    (hstep : ∃ C > 0, ∀ k, ‖R.s k‖ ≤ C*R.Δ k)
    (hdes : ∀ ε > 0, ∃ δ > 0, ∃ c > 0, ∀ k,
      ε ≤ q (R.x k) → R.Δ k < δ →
      f (R.x k+R.s k) < f (R.x k) ∧ c*R.Δ k ≤ f (R.x k)-f (R.x (k+1))) :
    Tendsto (fun k => q (R.x k)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hCbound⟩ := hstep
  apply excursion_tendsto (iterate_level hR) (hK.uniformContinuousOn_of_continuous hq)
    hq0 (objective_cauchy hR hK hf)
  · apply arbitrarily_late_small hR hΔ
    intro ε hε
    obtain ⟨δ, hδ, c, _, hh⟩ := hdes ε hε
    exact ⟨δ, hδ, fun k hk hd => (hh k hk hd).1⟩
  · intro ε hε
    obtain ⟨δ, hδ, c, hc, hh⟩ := hdes ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hΔ.eventually (gt_mem_nhds hδ))
    refine ⟨c/C, div_pos hc hC, N, ?_⟩
    intro k hk hqk
    obtain ⟨hs, hd⟩ := hh k hqk (hN k hk)
    have he : dist (R.x k) (R.x (k+1)) = ‖R.s k‖ := by
      rw [hR.x_succ, if_pos hs, dist_eq_norm]
      simp
    rw [he]
    calc
      (c/C)*‖R.s k‖ ≤ (c/C)*(C*R.Δ k) :=
        mul_le_mul_of_nonneg_left (hCbound k) (le_of_lt (div_pos hc hC))
      _ = c*R.Δ k := by field_simp
      _ ≤ f (R.x k)-f (R.x (k+1)) := hd

end BoundPSProof


open Set Filter
open scoped Topology
namespace BoundPSProof
open LewisTorczon.BoundPS

 theorem native_convergence {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hΩU : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0))) (hbdd : BoundedCols R)
    (hΔ : Filter.Tendsto R.Δ Filter.atTop (nhds 0)) (hstrong : StrongHyp P lo hi f R) :
    Filter.Tendsto (fun k => ‖projQ lo hi f (R.x k)‖) Filter.atTop (nhds 0) := by
  by_cases hn : n = 0
  · subst n
    have he : (fun k => ‖projQ lo hi f (R.x k)‖) = fun _ => (0 : ℝ) := by
      funext k
      have hz : projQ lo hi f (R.x k) = 0 := Subsingleton.elim _ _
      simp [hz]
    rw [he]
    exact tendsto_const_nhds
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hKU : levelSet lo hi f (R.x 0) ⊆ U := fun _ hx => hΩU hx.1
  obtain ⟨a,b,ha,hb,hab⟩ := exists_core_bounds P R hR.M_mem hR.diag hnpos
  apply convergence_from_descent hR hΔ hcpt (hf.continuousOn.mono hKU)
    (((continuousOn_projQ hlohi hU hf).norm).mono hKU) (fun _ => norm_nonneg _)
  · obtain ⟨C,hC,hbound⟩ := bounded_step P R hbdd
    refine ⟨C,hC,?_⟩
    intro k
    obtain ⟨c,hc,he⟩ := hR.step_mem k
    rw [he]
    exact hbound k (R.Δ k) (le_of_lt (delta_pos hR k)) c hc
  · apply uniform_descent_of_core hnpos hR hstrong hU hΩU hf hcpt ha hb
    intro ε hε k hq hs
    exact core_descent_move P R hR hlohi hnpos (R.x k) (iterate_mem hR k) k
      hε hq ha (delta_pos hR k) (hab k) hs

end BoundPSProof


open LewisTorczon.BoundPS

namespace LewisTorczon.BoundPS

/-- **Theorem 3.3**, p. 7: if `L_Ω(x_0)` is compact, `f` is `C¹`, the columns of the generating
matrices are uniformly bounded in norm, `Δ_k → 0`, and the method enforces the Strong Hypotheses
on Bound Constrained Exploratory Moves, then `‖q(x_k)‖ → 0`. -/
theorem theorem_3_3 {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hΩU : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0))) (hbdd : BoundedCols R)
    (hΔ : Filter.Tendsto R.Δ Filter.atTop (nhds 0)) (hstrong : StrongHyp P lo hi f R) :
    Filter.Tendsto (fun k => ‖projQ lo hi f (R.x k)‖) Filter.atTop (nhds 0) := by
  exact BoundPSProof.native_convergence P lo hi hlohi f U hU hΩU hf R hR hcpt hbdd hΔ hstrong

end LewisTorczon.BoundPS

open LewisTorczon.BoundPS

theorem solution {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hΩU : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0))) (hbdd : BoundedCols R)
    (hΔ : Filter.Tendsto R.Δ Filter.atTop (nhds 0)) (hstrong : StrongHyp P lo hi f R) :
    Filter.Tendsto (fun k => ‖projQ lo hi f (R.x k)‖) Filter.atTop (nhds 0) := LewisTorczon.BoundPS.theorem_3_3 P lo hi hlohi f U hU hΩU hf R hR hcpt hbdd hΔ hstrong
