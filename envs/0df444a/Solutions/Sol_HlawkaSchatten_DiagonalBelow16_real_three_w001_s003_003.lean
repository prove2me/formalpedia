-- Prove2me | solution 1 for HlawkaSchatten.DiagonalBelow16.real_three_w001_s003_003
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:35:42.514995+00:00
-- url     : https://prove2.me/submissions/397ad80b-1633-42d9-8830-585eedb1a36f

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_nonnegative_of_curvature_margins
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_coarse_failure_window01
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxCoordinates
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.GCongr
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Mathlib.Topology.Order.Compact

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The coordinate `p`-norm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- The coordinate `p`-norm agrees with the `PiLp` norm. -/
theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

/-- The `p`-norm of zero is zero. -/
@[simp]
theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

/-- The `p`-norm is invariant under negation. -/
@[simp]
theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]

/-- Minkowski's inequality for the coordinate `p`-norm. -/
theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

/-- Each coordinate norm is at most the `p`-norm. -/
theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

/-- Raising the `p`-norm to the `p`-th power recovers the sum of `p`-th powers. -/
theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm vanishes iff the vector is zero. -/
theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp

/-- A nonzero vector has strictly positive `p`-norm. -/
theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))

/-- The `p`-norm of a constant vector. -/
theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm scales homogeneously. -/
theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The coordinate `p`-norm is convex for `p ≥ 1`. -/
theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)

/-- The coordinate `p`-norm is continuous. -/
theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

/-- The `p`-norm is at most `n^(1/p) * M` when each coordinate norm is at most `M`. -/
theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

/-- The `p`-norm of real coordinates equals the `p`-norm of their complex embeddings. -/
theorem lpNorm_ofReal (p : ℝ) (x : ι → ℝ) :
    lpNorm p (fun i ↦ (x i : ℂ)) = lpNorm p x := by
  simp [lpNorm]

/-- Appending zero coordinates does not change the `p`-norm. -/
theorem lpNorm_fin_append_zero {p : ℝ} (hp : 0 < p) {n : ℕ}
    (x : Fin n → E) (m : ℕ) :
    lpNorm p (Fin.append x (0 : Fin m → E)) = lpNorm p x := by
  simp [lpNorm, Fin.sum_univ_add, hp.ne']

/-- A Hlawka constant in dimension `n` is also admissible in every lower dimension. -/
theorem hasHlawkaConstant_fin_of_le {p C : ℝ} (hp : 0 < p)
    {m n : ℕ} (hn : m ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin m → E) → ℝ) C := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro x y z
  have h := hC (Fin.append x (0 : Fin k → E))
    (Fin.append y (0 : Fin k → E)) (Fin.append z (0 : Fin k → E))
  have hadd (u v : Fin m → E) :
      Fin.append u (0 : Fin k → E) + Fin.append v (0 : Fin k → E) =
        Fin.append (u + v) (0 : Fin k → E) := by
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_fin_append_zero hp] using h

/-- A Hlawka constant in dimension `n ≥ 3` is admissible in dimension 3. -/
theorem hasHlawkaConstant_fin_three_of_ge {p C : ℝ} (hp : 0 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C :=
  hasHlawkaConstant_fin_of_le hp hn hC

/-- The `p`-norm is invariant under coordinate permutation. -/
theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

/-- The `p`-norm restricted to a subtype equals the full norm when unsupported entries vanish. -/
theorem lpNorm_subtype {p : ℝ} (hp : 0 < p) (x : ι → E)
    (P : ι → Prop) [DecidablePred P] (hx : ∀ i, ¬P i → x i = 0) :
    lpNorm p (fun i : Subtype P ↦ x i.1) = lpNorm p x := by
  unfold lpNorm
  congr 1
  have hzero : (∑ i : {i : ι // ¬P i}, ‖x i.1‖ ^ p) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by simp [hx i.1 i.2, hp.ne']
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i ↦ ‖x i‖ ^ p), hzero, add_zero]

/-- A Hlawka constant in dimension 3 lifts to any index type of cardinality at most 3. -/
theorem hasHlawkaConstant_of_card_le_three {p C : ℝ} (hp : 0 < p)
    (hcard : Fintype.card ι ≤ 3)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (ι → E) → ℝ) C := by
  let e := (Fintype.equivFin ι).symm
  have hf := hasHlawkaConstant_fin_of_le hp hcard hC
  intro x y z
  have h := hf (x ∘ e) (y ∘ e) (z ∘ e)
  have hadd (u v : ι → E) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_comp_equiv] using h

/-- The pair deficit is nonneg for `p ≥ 1` by Minkowski. -/
theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

/-- The sum of pair deficits is nonneg for `p ≥ 1`. -/
theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalConstruction
variable {ι : Type*} [Fintype ι]
theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring


end HlawkaSchatten.DiagonalConstruction


open HlawkaSchatten HlawkaSchatten.DiagonalConstruction


/- Adapted from @bwdaugherty's accepted cutoff-32 contribution,
   submission d75400b0-5a0e-4167-8192-7fd299469c2e (2026-10-16),
   https://prove2.me/theorems/4e05427b-74d9-4e61-8d14-a52384a5ca10 .
   Public Prove2Me contribution under Apache-2.0; see sources/NOTICE.md.
   These generic lemmas do not assume p >= 32. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle

/-- Increments of `x ↦ x ^ p` over intervals of equal length grow to the right. -/
theorem rpow_swap_le {p : ℝ} (hp : 1 ≤ p) {x y c : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hc : 0 ≤ c) : (x + c) ^ p + y ^ p ≤ x ^ p + (y + c) ^ p := by
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ y - x + c by linarith) with h | h
  · have hc0 : c = 0 := by linarith
    have hy : y = x := by linarith
    subst hc0 hy; simp
  · have hconv := (convexOn_rpow hp).2
    have hxm : x ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 hx
    have hym : y + c ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 (by linarith)
    have hl : 0 ≤ (y - x) / (y - x + c) := div_nonneg (by linarith) h.le
    have hm : 0 ≤ c / (y - x + c) := div_nonneg hc h.le
    have hs : (y - x) / (y - x + c) + c / (y - x + c) = 1 := by
      rw [← add_div, div_self h.ne']
    have h1 := hconv hxm hym hl hm hs
    have h2 := hconv hxm hym hm hl (by linarith)
    simp only [smul_eq_mul] at h1 h2
    have e1 : (y - x) / (y - x + c) * x + c / (y - x + c) * (y + c) = x + c := by
      field_simp; ring
    have e2 : c / (y - x + c) * x + (y - x) / (y - x + c) * (y + c) = y := by
      field_simp; ring
    rw [e1] at h1
    rw [e2] at h2
    calc (x + c) ^ p + y ^ p ≤ _ := add_le_add h1 h2
      _ = ((y - x) / (y - x + c) + c / (y - x + c)) * (x ^ p + (y + c) ^ p) := by ring
      _ = _ := by rw [hs, one_mul]

/-- Power mean for two terms. -/
theorem add_rpow_le_two {p : ℝ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (u + v) ^ p ≤ 2 ^ p / 2 * (u ^ p + v ^ p) := by
  have h := (convexOn_rpow hp).2 (Set.mem_Ici.2 hu) (Set.mem_Ici.2 hv)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at h
  have e : 1/2 * u + 1/2 * v = (u + v) / 2 := by ring
  rw [e, Real.div_rpow (by linarith) (by norm_num)] at h
  have h2p : 0 < (2:ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  rw [div_le_iff₀ h2p] at h
  calc (u + v) ^ p ≤ _ := h
    _ = _ := by ring

/-- The two-coordinate constant `2 ^ (1 - 1/p)`. -/
noncomputable def cp (p : ℝ) : ℝ := 2 * (1/2 : ℝ) ^ (1/p)

theorem cp_pos (p : ℝ) : 0 < cp p := by unfold cp; positivity

theorem cp_rpow {p : ℝ} (hp : 0 < p) : cp p ^ p = 2 ^ p / 2 := by
  unfold cp
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by norm_num),
    one_div_mul_cancel hp.ne', Real.rpow_one]; ring

theorem sum_div_cp_rpow_le {p : ℝ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ((u + v) / cp p) ^ p ≤ u ^ p + v ^ p := by
  have hp0 : 0 < p := by linarith
  rw [Real.div_rpow (by linarith) (cp_pos p).le, cp_rpow hp0, div_le_iff₀ (by positivity)]
  rw [mul_comm]; exact add_rpow_le_two hp hu hv

theorem sum_le_cp_mul {p : ℝ} (hp : 1 ≤ p) {u v S : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hS : 0 ≤ S) (h : u ^ p + v ^ p ≤ S ^ p) : u + v ≤ cp p * S := by
  have hp0 : 0 < p := by linarith
  have h1 := (sum_div_cp_rpow_le hp hu hv).trans h
  have h2 : (u + v) / cp p ≤ S :=
    (Real.rpow_le_rpow_iff (div_nonneg (by linarith) (cp_pos p).le) hS hp0).1 h1
  rw [div_le_iff₀ (cp_pos p)] at h2; linarith

/-- Diagonal certificate: a row with nearly extremal two-coordinate mass has a small
diagonal entry. -/
theorem diag_cert {p : ℝ} (hp : 1 ≤ p) {a w c N D δ U Ab : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hrow : a ^ p + (w / c) ^ p ≤ N ^ p) (hw : c * N - D ≤ w) (hDc : D / c ≤ δ)
    (hδ : 0 ≤ δ) (hδN : δ ≤ N) (hNU : N ≤ U) (hU : 0 < U) (hAb : 0 ≤ Ab)
    (hcert : 1 ≤ (Ab / U) ^ p + (1 - δ / U) ^ p) : a ≤ Ab := by
  have hp0 : 0 < p := by linarith
  have h1 : N - δ ≤ w / c := by
    have e : w / c = N - D / c + (w - (c * N - D)) / c := by field_simp; ring
    rw [e]
    have : 0 ≤ (w - (c * N - D)) / c := div_nonneg (by linarith) hc.le
    linarith
  have h2 : (N - δ) ^ p ≤ (w / c) ^ p := Real.rpow_le_rpow (by linarith) h1 hp0.le
  have h3 := rpow_swap_le hp (x := N - δ) (y := U - δ) (c := δ) (by linarith) (by linarith) hδ
  rw [sub_add_cancel, sub_add_cancel] at h3
  have h4 : U ^ p ≤ Ab ^ p + (U - δ) ^ p := by
    have e : 1 - δ / U = (U - δ) / U := by field_simp
    rw [e, Real.div_rpow hAb hU.le, Real.div_rpow (by linarith) hU.le, ← add_div,
      le_div_iff₀ (by positivity), one_mul] at hcert
    exact hcert
  have h5 : a ^ p ≤ Ab ^ p := by linarith
  exact (Real.rpow_le_rpow_iff ha hAb hp0).1 h5

/-- Two-dimensional Minkowski inequality in power form. -/
theorem mink2 {p : ℝ} (hp : 1 ≤ p) {x1 y1 x2 y2 N1 N2 : ℝ} (hx1 : 0 ≤ x1) (hy1 : 0 ≤ y1)
    (hx2 : 0 ≤ x2) (hy2 : 0 ≤ y2) (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2)
    (h1 : x1 ^ p + y1 ^ p ≤ N1 ^ p) (h2 : x2 ^ p + y2 ^ p ≤ N2 ^ p) :
    (x1 + x2) ^ p + (y1 + y2) ^ p ≤ (N1 + N2) ^ p := by
  have hp0 : 0 < p := by linarith
  have hM := Real.Lp_add_le (Finset.univ : Finset (Fin 2)) ![x1, y1] ![x2, y2] hp
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hM
  rw [abs_of_nonneg (by linarith : 0 ≤ x1 + x2), abs_of_nonneg (by linarith : 0 ≤ y1 + y2),
    abs_of_nonneg hx1, abs_of_nonneg hy1, abs_of_nonneg hx2, abs_of_nonneg hy2] at hM
  have hr1 : (x1 ^ p + y1 ^ p) ^ (1/p) ≤ N1 := by
    calc (x1 ^ p + y1 ^ p) ^ (1/p) ≤ (N1 ^ p) ^ (1/p) :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
      _ = N1 := by rw [one_div, Real.rpow_rpow_inv hN1 hp0.ne']
  have hr2 : (x2 ^ p + y2 ^ p) ^ (1/p) ≤ N2 := by
    calc (x2 ^ p + y2 ^ p) ^ (1/p) ≤ (N2 ^ p) ^ (1/p) :=
          Real.rpow_le_rpow (by positivity) h2 (by positivity)
      _ = N2 := by rw [one_div, Real.rpow_rpow_inv hN2 hp0.ne']
  have h3 : ((x1 + x2) ^ p + (y1 + y2) ^ p) ^ (1/p) ≤ N1 + N2 := by linarith
  have hS : 0 ≤ (x1 + x2) ^ p + (y1 + y2) ^ p := by positivity
  calc (x1 + x2) ^ p + (y1 + y2) ^ p
      = (((x1 + x2) ^ p + (y1 + y2) ^ p) ^ (1/p)) ^ p := by
        rw [← Real.rpow_mul hS, one_div_mul_cancel hp0.ne', Real.rpow_one]
    _ ≤ (N1 + N2) ^ p := Real.rpow_le_rpow (by positivity) h3 hp0.le

/-- Ratio lower bound from a convexity certificate. -/
theorem ratio_lower {p x y s τ : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) (_hy : 0 ≤ y)
    (hxy : x ^ p + y ^ p ≤ 1) (hs : s ≤ x + y) (hτ0 : 0 ≤ τ) (hτs : 2 * τ ≤ s)
    (hc : 1 < τ ^ p + (s - τ) ^ p) : τ < x := by
  have hp0 : 0 < p := by linarith
  by_contra hle
  push Not at hle
  have h1 := rpow_swap_le hp (x := x) (y := s - τ) (c := τ - x) hx (by linarith) (by linarith)
  have e1 : x + (τ - x) = τ := by ring
  have e2 : s - τ + (τ - x) = s - x := by ring
  rw [e1, e2] at h1
  have h2 : (s - x) ^ p ≤ y ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp0.le
  linarith

/-- Ratio upper bound from a convexity certificate. -/
theorem ratio_upper {p x y s σ : ℝ} (hp : 1 ≤ p) (_hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ^ p + y ^ p ≤ 1) (hs : s ≤ x + y) (hs1 : 1 ≤ s) (hσs : s ≤ 2 * σ)
    (hc : 1 < σ ^ p + (s - σ) ^ p) : x < σ := by
  have hp0 : 0 < p := by linarith
  by_contra hle
  push Not at hle
  have hx1 : x ≤ 1 := by
    by_contra h
    push Not at h
    have : 1 < x ^ p := Real.one_lt_rpow h hp0
    have : 0 ≤ y ^ p := Real.rpow_nonneg hy p
    linarith
  have h1 := rpow_swap_le hp (x := s - x) (y := σ) (c := x - σ) (by linarith) (by linarith)
    (by linarith)
  have e1 : s - x + (x - σ) = s - σ := by ring
  have e2 : σ + (x - σ) = x := by ring
  rw [e1, e2] at h1
  have h2 : (s - x) ^ p ≤ y ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp0.le
  linarith

/-! ## Turning integer-power checks into real-exponent certificates -/

theorem le_rpow_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (m k : ℕ) (hk : 0 < k)
    (h : X ^ k ≤ x ^ m) : X ≤ x ^ ((m : ℝ) / k) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.rpow_nonneg hx _)
  · have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
    rw [e]
    calc X = (X ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX.le hk.ne').symm
      _ ≤ (x ^ m) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)

theorem rpow_le_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (m k : ℕ) (hk : 0 < k)
    (h : x ^ m ≤ X ^ k) : x ^ ((m : ℝ) / k) ≤ X := by
  have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  rw [e]
  calc (x ^ m) ^ ((k : ℝ)⁻¹) ≤ (X ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = X := Real.pow_rpow_inv_natCast hX hk.ne'

theorem cert_le {x y X Y : ℝ} (m k : ℕ) (hk : 0 < k) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hX : X ^ k ≤ x ^ m) (hY : Y ^ k ≤ y ^ m)
    (hXY : 1 ≤ X + Y) : ∀ p : ℝ, 0 ≤ p → p ≤ (m : ℝ) / k → 1 ≤ x ^ p + y ^ p := by
  intro p hp0 hpb
  have h1 := le_rpow_of_pow_le hx0 m k hk hX
  have h2 := le_rpow_of_pow_le hy0 m k hk hY
  have h3 : x ^ ((m : ℝ) / k) ≤ x ^ p := Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 hp0 hpb
  have h4 : y ^ ((m : ℝ) / k) ≤ y ^ p := Real.rpow_le_rpow_of_exponent_ge' hy0 hy1 hp0 hpb
  linarith

theorem cert_lt {x y X Y : ℝ} (m k : ℕ) (hk : 0 < k) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hX : X ^ k ≤ x ^ m) (hY : Y ^ k ≤ y ^ m)
    (hXY : 1 < X + Y) : ∀ p : ℝ, 0 ≤ p → p ≤ (m : ℝ) / k → 1 < x ^ p + y ^ p := by
  intro p hp0 hpb
  have h1 := le_rpow_of_pow_le hx0 m k hk hX
  have h2 := le_rpow_of_pow_le hy0 m k hk hY
  have h3 : x ^ ((m : ℝ) / k) ≤ x ^ p := Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 hp0 hpb
  have h4 : y ^ ((m : ℝ) / k) ≤ y ^ p := Real.rpow_le_rpow_of_exponent_ge' hy0 hy1 hp0 hpb
  linarith


end HlawkaSchatten.DiagonalRealBundle


/- Generic contraction lemmas adapted from accepted Prove2Me submission 3735254f-536b-45fe-a0c1-2ea9ffc9d938 (Yuxuan Xu, bwdaugherty; Apache-2.0). The gap budget is now an arbitrary certified bound. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalRealBundle

theorem others (i : Fin 3) : ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  fin_cases i <;> decide

theorem third {i j : Fin 3} (h : i ≠ j) : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

structure Facts (p c D δ h A cmax tlo : ℝ) (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ) : Prop where
  Nnonneg : ∀ i, 0 ≤ N i
  hp : 1 ≤ p
  hc : 0 < c
  hcm : c ≤ cmax
  hct : 2 * tlo ≤ c
  hDc : D / c ≤ δ
  hA : 0 < A
  diag : ∀ i, 0 ≤ -X i i
  off : ∀ i j, i ≠ j → 0 ≤ X i j
  nsum : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    N i + N j + N k = 3
  rowfull : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (-X i i) ^ p + X i j ^ p + X i k ^ p = N i ^ p
  row : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (-X i i) ^ p + ((X i j + X i k) / c) ^ p ≤ N i ^ p
  wD : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → c * N i - D ≤ X i j + X i k
  wD2 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    c * (N j + N k) - D ≤ (X j i + X j k) + (X k i + X k j)
  offsum : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    6 - h < (X i j + X i k) + (X j i + X j k) + (X k i + X k j)
  T1 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → X i i + X j i + X k i < A
  T2 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (X i j + X j j + X k j) + (X i k + X j k + X k k) < cmax * A

section Rounds

variable {p c D δ h A cmax tlo : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N : Fin 3 → ℝ}

theorem ratio_round (F : Facts p c D δ h A cmax tlo X N) {n s τ σ : ℝ}
    (hn : ∀ i, n ≤ N i) (hn0 : 0 < n) (hD0 : 0 ≤ D) (hs : s ≤ 2 * tlo - D / n)
    (hτ0 : 0 ≤ τ) (hτs : 2 * τ ≤ s) (hs1 : 1 ≤ s) (hσs : s ≤ 2 * σ)
    (hτc : 1 < τ ^ p + (s - τ) ^ p) (hσc : 1 < σ ^ p + (s - σ) ^ p) :
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      τ * N i < X i j ∧ X i j < σ * N i := by
  intro i j k hij hik hjk
  have hp0 : 0 < p := by linarith [F.hp]
  have hN : 0 < N i := lt_of_lt_of_le hn0 (hn i)
  set Ni := N i with hNdef
  have hbj := F.off i j hij
  have hbk := F.off i k hik
  have hxy : (X i j / Ni) ^ p + (X i k / Ni) ^ p ≤ 1 := by
    rw [Real.div_rpow (by linarith) hN.le, Real.div_rpow (by linarith) hN.le, ← add_div,
      div_le_one (by positivity)]
    have := F.rowfull i j k hij hik hjk
    have := Real.rpow_nonneg (F.diag i) p
    linarith
  have hsum : s ≤ X i j / Ni + X i k / Ni := by
    rw [← add_div, le_div_iff₀ hN]
    have a1 : s * Ni ≤ (2 * tlo - D / n) * Ni := mul_le_mul_of_nonneg_right hs hN.le
    have a2 : D ≤ D / n * Ni := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hn0]; exact mul_le_mul_of_nonneg_left (hn i) hD0
    have a3 : 2 * tlo * Ni ≤ c * Ni := mul_le_mul_of_nonneg_right F.hct hN.le
    have a4 := F.wD i j k hij hik hjk
    have e : (2 * tlo - D / n) * Ni = 2 * tlo * Ni - D / n * Ni := by ring
    linarith
  have h1 := ratio_lower F.hp (by positivity) (by positivity) hxy hsum hτ0 hτs hτc
  have h2 := ratio_upper F.hp (by positivity) (by positivity) hxy hsum hs1 hσs hσc
  exact ⟨(lt_div_iff₀ hN).1 h1, (div_lt_iff₀ hN).1 h2⟩

theorem lower_round (F : Facts p c D δ h A cmax tlo X N) {n τ n' Ab : ℝ}
    (hn : ∀ i, n ≤ N i) (hδn : δ ≤ n) (hδ0 : 0 ≤ δ) (hτ0 : 0 ≤ τ)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → τ * N i < X i j)
    (hn'0 : 0 < n') (hAb : 0 ≤ Ab) (hcert : 1 ≤ (Ab / n') ^ p + (1 - δ / n') ^ p)
    (hchk : A ≤ τ * (3 - n') - Ab) : ∀ i, n' ≤ N i := by
  intro i
  obtain ⟨j, k, hij, hik, hjk⟩ := others i
  by_contra hlt
  push Not at hlt
  have ha := diag_cert F.hp (F.diag i) F.hc (F.row i j k hij hik hjk) (F.wD i j k hij hik hjk)
    F.hDc hδ0 (hδn.trans (hn i)) hlt.le hn'0 hAb hcert
  have t1 := F.T1 i j k hij hik hjk
  have r1 := hr j i k (Ne.symm hij) hjk hik
  have r2 := hr k i j (Ne.symm hik) (Ne.symm hjk) hij
  have ns := F.nsum i j k hij hik hjk
  have m1 : τ * (3 - n') ≤ τ * (N j + N k) :=
    mul_le_mul_of_nonneg_left (by linarith) hτ0
  rw [mul_add] at m1
  linarith

theorem upper_round (F : Facts p c D δ h A cmax tlo X N) {n σ U Ab : ℝ}
    (hn : ∀ i, n ≤ N i) (hδn : δ ≤ n) (hδ0 : 0 ≤ δ) (hσ0 : 0 ≤ σ)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → X i j < σ * N i)
    (hU3 : U < 3) (hAb : 0 ≤ Ab) (hcert : 1 ≤ (Ab / (3 - U)) ^ p + (1 - δ / (3 - U)) ^ p)
    (hchk : cmax * A ≤ 6 - h - σ * (3 - U) - Ab) : ∀ i, N i ≤ U := by
  intro i
  obtain ⟨j, k, hij, hik, hjk⟩ := others i
  by_contra hlt
  push Not at hlt
  have ns := F.nsum i j k hij hik hjk
  have rj := F.row j i k (Ne.symm hij) hjk hik
  have rk := F.row k i j (Ne.symm hik) (Ne.symm hjk) hij
  have hbji := F.off j i (Ne.symm hij)
  have hbjk := F.off j k hjk
  have hbki := F.off k i (Ne.symm hik)
  have hbkj := F.off k j (Ne.symm hjk)
  have hm := mink2 F.hp (F.diag j) (div_nonneg (by linarith) F.hc.le) (F.diag k)
    (div_nonneg (by linarith) F.hc.le) (F.Nnonneg j) (F.Nnonneg k) rj rk
  rw [← add_div] at hm
  have hNj := hn j
  have hNk := hn k
  have ha := diag_cert F.hp (by linarith [F.diag j, F.diag k]) F.hc hm (F.wD2 i j k hij hik hjk)
    F.hDc hδ0 (by linarith) (by linarith : N j + N k ≤ 3 - U)
    (by linarith) hAb hcert
  have t2 := F.T2 i j k hij hik hjk
  have os := F.offsum i j k hij hik hjk
  have r1 := hr j i k (Ne.symm hij) hjk hik
  have r2 := hr k i j (Ne.symm hik) (Ne.symm hjk) hij
  have m1 : σ * (N j + N k) ≤ σ * (3 - U) :=
    mul_le_mul_of_nonneg_left (by linarith) hσ0
  rw [mul_add] at m1
  linarith

theorem final_round (F : Facts p c D δ h A cmax tlo X N) {n U τ σ Ab ell u v w : ℝ}
    (hn : ∀ i, n ≤ N i) (hU : ∀ i, N i ≤ U) (hδn : δ ≤ n)
    (hδ0 : 0 ≤ δ) (hτ0 : 0 ≤ τ) (hσ0 : 0 ≤ σ)
    (hr : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      τ * N i < X i j ∧ X i j < σ * N i)
    (hU0 : 0 < U) (hAb : 0 ≤ Ab) (hcert : 1 ≤ (Ab / U) ^ p + (1 - δ / U) ^ p)
    (h1 : v ≤ τ * n) (h2 : σ * U ≤ w) (h3 : Ab ≤ u)
    (h4 : ell ≤ τ * (3 - U) - A) : (∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
      else v ≤ X j i ∧ X j i ≤ w) := by
  intro j i
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl]
    obtain ⟨k, l, hjk, hjl, hkl⟩ := others j
    have ha := diag_cert F.hp (F.diag j) F.hc (F.row j k l hjk hjl hkl)
      (F.wD j k l hjk hjl hkl) F.hDc hδ0 (hδn.trans (hn j)) (hU j) hU0 hAb hcert
    have t1 := F.T1 j k l hjk hjl hkl
    have r1 := (hr k j l (Ne.symm hjk) hkl hjl).1
    have r2 := (hr l j k (Ne.symm hjl) (Ne.symm hkl) hjk).1
    have ns := F.nsum j k l hjk hjl hkl
    have m1 : τ * (3 - U) ≤ τ * (N k + N l) :=
      mul_le_mul_of_nonneg_left (by linarith [hU j]) hτ0
    rw [mul_add] at m1
    constructor <;> linarith
  · rw [if_neg hji]
    obtain ⟨k, hjk, hik⟩ := third hji
    have r := hr j i k hji hjk hik
    have m1 : τ * n ≤ τ * N j := mul_le_mul_of_nonneg_left (hn j) hτ0
    have m2 : σ * N j ≤ σ * U := mul_le_mul_of_nonneg_left (hU j) hσ0
    constructor <;> linarith [r.1, r.2]

end Rounds


end HlawkaSchatten.DiagonalRealBundle

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction
abbrev Triple := Fin 3 → Fin 3 → ℝ

theorem sum3 (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring

theorem offperm (X : Triple) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (X i j + X i k) + (X j i + X j k) + (X k i + X k j) =
      X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring

theorem lpNorm_nonneg3 (p : ℝ) (x : Fin 3 → ℝ) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

theorem lpNorm_pow3 {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ) :
    lpNorm p x ^ p = ∑ l, |x l| ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _),
    one_div_mul_cancel hp.ne', Real.rpow_one]
  simp [Real.norm_eq_abs]

theorem lpNorm_eq3 (p : ℝ) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : lpNorm p x = (|x i| ^ p + |x j| ^ p + |x k| ^ p) ^ (1/p) := by
  unfold lpNorm
  rw [sum3 (fun l ↦ ‖x l‖ ^ p) hij hik hjk]
  simp [Real.norm_eq_abs]

theorem coord_le {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) : |x i| ≤ lpNorm p x := by
  have h := lpNorm_pow3 hp x
  rw [sum3 _ hij hik hjk] at h
  have : |x i| ^ p ≤ lpNorm p x ^ p := by
    rw [h]; have := Real.rpow_nonneg (abs_nonneg (x j)) p
    have := Real.rpow_nonneg (abs_nonneg (x k)) p; linarith
  exact (Real.rpow_le_rpow_iff (abs_nonneg _) (lpNorm_nonneg3 p x) hp).1 this

theorem two_coord_le {p : ℝ} (hp : 1 ≤ p) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) : |x j| + |x k| ≤ cp p * lpNorm p x := by
  have hp0 : 0 < p := by linarith
  have h := lpNorm_pow3 hp0 x
  rw [sum3 _ hij hik hjk] at h
  apply sum_le_cp_mul hp (abs_nonneg _) (abs_nonneg _) (lpNorm_nonneg3 p x)
  rw [h]; have := Real.rpow_nonneg (abs_nonneg (x i)) p; linarith


end HlawkaSchatten.DiagonalRealBundle

set_option autoImplicit false

namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

def coordinateBox (ell u v w : ℝ) (X : Triple) : Prop :=
  ∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
    else v ≤ X j i ∧ X j i ≤ w

theorem facts_of {p α β tlo thib D δ h A g eps ell u v w : ℝ} {X : Triple}
    (hα : 0 < α) (hαp : α ≤ p) (hpβ : p ≤ β) (hp1 : 1 ≤ p)
    (hell : 0 < ell) (hv : 0 < v) (hA : 0 < A)
    (htlo0 : 0 < tlo) (htlo : tlo ≤ (1/2 : ℝ) ^ (1/α))
    (hthib : (1/2 : ℝ) ^ (1/β) ≤ thib)
    (hD : g + 3 * eps - 6 + 6 * thib ≤ D) (hD0 : 0 ≤ D)
    (hδ : D / (2 * tlo) ≤ δ) (hh : g + 3 * eps ≤ h)
    (hB : coordinateBox ell u v w X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : lpNorm p (X 0 + X 1 + X 2) < A)
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < g)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ (X j i + X k i) + eps) :
    Facts p (cp p) D δ h A (2 * thib) tlo X (fun i ↦ lpNorm p (X i)) := by
  have hp : 1 ≤ p := hp1
  have hp0 : 0 < p := by linarith
  have hdiag : ∀ i, -(u : ℝ) ≤ X i i ∧ X i i ≤ -(ell : ℝ) := fun i ↦ by
    simpa using hB i i
  have hoff : ∀ i j, i ≠ j → (v : ℝ) ≤ X i j ∧ X i j ≤ w := fun i j h ↦ by
    have := hB i j; rwa [if_neg h] at this
  have hrowfull : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (-X i i) ^ p + X i j ^ p + X i k ^ p = lpNorm p (X i) ^ p := by
    intro i j k hij hik hjk
    rw [lpNorm_pow3 hp0, sum3 _ hij hik hjk, abs_of_neg (by linarith [(hdiag i).2]),
      abs_of_pos (by linarith [(hoff i j hij).1]), abs_of_pos (by linarith [(hoff i k hik).1])]
  have hdn : ∀ i, 0 ≤ -X i i := fun i ↦ by linarith [(hdiag i).2]
  have hrow : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (-X i i) ^ p + ((X i j + X i k) / cp p) ^ p ≤ lpNorm p (X i) ^ p := by
    intro i j k hij hik hjk
    have := sum_div_cp_rpow_le hp (u := X i j) (v := X i k) (by linarith [(hoff i j hij).1])
      (by linarith [(hoff i k hik).1])
    have := hrowfull i j k hij hik hjk
    linarith
  have hwle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → X i j + X i k ≤ cp p * lpNorm p (X i) := by
    intro i j k hij hik hjk
    apply sum_le_cp_mul hp (by linarith [(hoff i j hij).1]) (by linarith [(hoff i k hik).1])
      (lpNorm_nonneg3 p _)
    have := hrowfull i j k hij hik hjk
    have := Real.rpow_nonneg (hdn i) p
    linarith
  have hoffsum0 : 6 - g - 3 * eps <
      X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
    unfold pairGapSum pairGap at hG
    have t01 := htail 2 0 1 (by decide) (by decide) (by decide)
    have t02 := htail 1 0 2 (by decide) (by decide) (by decide)
    have t12 := htail 0 1 2 (by decide) (by decide) (by decide)
    linarith
  have hct : 2 * tlo ≤ cp p := by
    unfold cp
    have : (1/2 : ℝ) ^ (1/α) ≤ (1/2 : ℝ) ^ (1/p) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        (one_div_le_one_div_of_le hα hαp)
    linarith
  have hcm : cp p ≤ 2 * thib := by
    unfold cp
    have : (1/2 : ℝ) ^ (1/p) ≤ (1/2 : ℝ) ^ (1/β) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        (one_div_le_one_div_of_le hp0 hpβ)
    linarith
  have hnsum : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X i) + lpNorm p (X j) + lpNorm p (X k) = 3 := by
    intro i j k hij hik hjk
    have := sum3 (fun l ↦ lpNorm p (X l)) hij hik hjk
    rw [Fin.sum_univ_three] at this
    linarith
  have hoffperm : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (X i j + X i k) + (X j i + X j k) + (X k i + X k j) =
        X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
    intro i j k hij hik hjk
    exact offperm X hij hik hjk
  have key : cp p * 3 - (X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1) < D := by
    linarith only [hoffsum0, hcm, hD]
  have hcN : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      cp p * lpNorm p (X i) + cp p * lpNorm p (X j) + cp p * lpNorm p (X k) = cp p * 3 := by
    intro i j k hij hik hjk
    rw [← hnsum i j k hij hik hjk]; ring
  have hcpos := cp_pos p
  set vtotal : Fin 3 → ℝ := X 0 + X 1 + X 2 with hvtotal
  have hvc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → vtotal i = X i i + X j i + X k i := by
    intro i j k hij hik hjk
    have := sum3 (fun l ↦ X l i) hij hik hjk
    rw [Fin.sum_univ_three] at this
    simp only [hvtotal, Pi.add_apply]
    linarith
  refine ⟨fun i ↦ lpNorm_nonneg3 p (X i), hp, hcpos, hcm, hct, ?_, by linarith, hdn, fun i j h ↦ hv.le.trans (hoff i j h).1, hnsum,
    hrowfull, hrow, ?_, ?_, ?_, ?_, ?_⟩
  · calc D / cp p ≤ D / (2 * tlo) := div_le_div_of_nonneg_left hD0 (by positivity) hct
      _ ≤ δ := hδ
  · intro i j k hij hik hjk
    have := hwle j i k (Ne.symm hij) hjk hik
    have := hwle k i j (Ne.symm hik) (Ne.symm hjk) hij
    have := hcN i j k hij hik hjk
    have := hoffperm i j k hij hik hjk
    linarith
  · intro i j k hij hik hjk
    have := hwle i j k hij hik hjk
    have := hcN i j k hij hik hjk
    have := hoffperm i j k hij hik hjk
    rw [mul_add]
    linarith
  · intro i j k hij hik hjk
    have := hoffperm i j k hij hik hjk
    linarith
  · intro i j k hij hik hjk
    have h1 := coord_le hp0 vtotal hij hik hjk
    rw [hvc i j k hij hik hjk] at h1
    linarith [le_abs_self (X i i + X j i + X k i)]
  · intro i j k hij hik hjk
    have h1 := two_coord_le hp vtotal hij hik hjk
    rw [hvc j i k (Ne.symm hij) hjk hik, hvc k i j (Ne.symm hik) (Ne.symm hjk) hij] at h1
    have h2 : cp p * lpNorm p vtotal < cp p * (A) := mul_lt_mul_of_pos_left hT hcpos
    have h3 : cp p * (A) ≤ 2 * thib * (A) :=
      mul_le_mul_of_nonneg_right hcm (by linarith)
    have := le_abs_self (X j j + X i j + X k j)
    have := le_abs_self (X k k + X i k + X j k)
    linarith


end HlawkaSchatten.DiagonalRealBundle



set_option autoImplicit false
namespace HlawkaSchatten.DiagonalRealBundle

theorem coordinateBox_weaken {ell u v w ell' u' v' w' : ℝ} {X : Triple}
    (hB : coordinateBox ell' u' v' w' X)
    (hell : ell ≤ ell') (hu : u' ≤ u) (hv : v ≤ v') (hw : w' ≤ w) :
    coordinateBox ell u v w X := by
  intro j i
  have hh := hB j i
  by_cases hji : j = i
  · rw [if_pos hji] at hh ⊢
    constructor <;> linarith
  · rw [if_neg hji] at hh ⊢
    constructor <;> linarith

end HlawkaSchatten.DiagonalRealBundle

open HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalRealBundle
def offsum (X : Triple) : ℝ :=
  X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1

def normCappedDomain (p ell u v w U A J W0 : ℝ) : Set Triple :=
  {X | coordinateBox ell u v w X ∧
    (∀ i, lpNorm p (X i) ≤ U) ∧ lpNorm p (X 0 + X 1 + X 2) ≤ A ∧
    (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → J ≤ X j i + X k i) ∧
    W0 ≤ offsum X}

noncomputable def shapeFactor (m s t : ℝ) : ℝ := (s^2+t^2)/(m^2*(s+t)^2)

noncomputable def pairTotalFactor (m M s t eps1 eps2 : ℝ) : ℝ :=
  4*M^2*(1+eps2)*shapeFactor m s t*(1+eps1)

noncomputable def pairColumnFactor (m M s t eta L eps1 eps2 : ℝ) : ℝ :=
  12*M^2*(1+eps2)*shapeFactor m s t*(1+1/eps1) + (7/4+2*(eta/L))^2*(1+1/eps2)


end HlawkaSchatten.DiagonalRealBundle



set_option autoImplicit false
set_option maxHeartbeats 4000000

open HlawkaSchatten.DiagonalRealBundle

namespace HlawkaSchatten.DiagonalCutoff16

/-- Minkowski combines the three two-coordinate row budgets. -/
theorem aggregate_rows {p γ : ℝ} (hp : 1 ≤ p) (hγ : 0 < γ)
    (a w N : Fin 3 → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hw : ∀ i, 0 ≤ w i) (hN : ∀ i, 0 ≤ N i)
    (hrow : ∀ i, a i ^ p + (w i / γ) ^ p ≤ N i ^ p)
    (hS : ∑ i, N i = 3) :
    (∑ i, a i) ^ p + ((∑ i, w i) / γ) ^ p ≤ (3 : ℝ) ^ p := by
  have h01 := mink2 hp (ha 0) (div_nonneg (hw 0) hγ.le)
    (ha 1) (div_nonneg (hw 1) hγ.le) (hN 0) (hN 1) (hrow 0) (hrow 1)
  have h012 := mink2 hp (add_nonneg (ha 0) (ha 1))
    (add_nonneg (div_nonneg (hw 0) hγ.le) (div_nonneg (hw 1) hγ.le))
    (ha 2) (div_nonneg (hw 2) hγ.le) (add_nonneg (hN 0) (hN 1)) (hN 2)
    h01 (hrow 2)
  simp only [Fin.sum_univ_three] at hS ⊢
  rw [← hS]
  simpa only [add_div] using h012

/-- A scalar certificate bounds the diagonal sum and improves the total norm. -/
theorem aggregate_bootstrap {p β A W γ Γ H T W0 B t' : ℝ}
    (hp : 0 < p) (hpβ : p ≤ β) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hγ : 0 < γ) (hγΓ : γ ≤ Γ) (hH : 0 < H)
    (hbudget : A ^ p + (W / γ) ^ p ≤ (3 : ℝ) ^ p)
    (hHolder : W - A ≤ H * T) (hW0 : 0 ≤ W0) (hWstrict : W0 < W)
    (hB0 : 0 ≤ B) (hB3 : B ≤ 3) (hWbase : W0 / (3 * Γ) ≤ 1)
    (hcert : 1 ≤ (B / 3) ^ β + (W0 / (3 * Γ)) ^ β)
    (hnext : H * t' ≤ W0 - B) : t' < T := by
  have hΓ : 0 < Γ := hγ.trans_le hγΓ
  have hthree : 0 < (3 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  have hnormalized : (A / 3) ^ p + ((W / γ) / 3) ^ p ≤ 1 := by
    rw [Real.div_rpow hA (by norm_num),
      Real.div_rpow (div_nonneg hW hγ.le) (by norm_num), ← add_div]
    exact (div_le_iff₀ hthree).2 (by simpa using hbudget)
  have hBx0 : 0 ≤ B / 3 := by positivity
  have hBx1 : B / 3 ≤ 1 := by linarith
  have hWx0 : 0 ≤ W0 / (3 * Γ) := by positivity
  have hcertp : 1 ≤ (B / 3) ^ p + (W0 / (3 * Γ)) ^ p :=
    hcert.trans (add_le_add
      (Real.rpow_le_rpow_of_exponent_ge' hBx0 hBx1 hp.le hpβ)
      (Real.rpow_le_rpow_of_exponent_ge' hWx0 hWbase hp.le hpβ))
  have hWcompare : W0 / (3 * Γ) ≤ (W / γ) / 3 := by
    have h1 : W0 / Γ ≤ W / γ := calc
      W0 / Γ ≤ W / Γ := div_le_div_of_nonneg_right hWstrict.le hΓ.le
      _ ≤ W / γ := div_le_div_of_nonneg_left hW hγ hγΓ
    calc W0 / (3 * Γ) = (W0 / Γ) / 3 := by ring
         _ ≤ (W / γ) / 3 := div_le_div_of_nonneg_right h1 (by norm_num)
  have hApow : A ≤ B := by
    by_contra hn
    have hBA : B < A := lt_of_not_ge hn
    have hr := Real.rpow_lt_rpow hBx0 (div_lt_div_of_pos_right hBA (by norm_num)) hp
    have hw := Real.rpow_le_rpow hWx0 hWcompare hp.le
    linarith
  have hmul : H * t' < H * T := by linarith
  nlinarith only [hmul, hH]

/-- The total-norm bootstrap for normalized three-row Hlawka data.

The two-coordinate row budgets come from Holder. The sum-coordinate bound
is the three-coordinate Holder inequality. The strict gap inequality and
pair-tail estimate are precisely the consequences of a normalized strict
Hlawka counterexample used in bootstrap.tex.
-/
theorem total_norm_bootstrap {p α β c γ Γ H T G ε t B t' : ℝ}
    (hp : 1 ≤ p) (hα : 0 < α) (hαp : α ≤ p) (hpβ : p ≤ β)
    (hc : 0 < c) (hγ : 0 < γ) (hγΓ : γ ≤ Γ) (hH : 0 < H)
    (a w N : Fin 3 → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hw : ∀ i, 0 ≤ w i) (hN : ∀ i, 0 ≤ N i)
    (hrow : ∀ i, a i ^ p + (w i / γ) ^ p ≤ N i ^ p)
    (hS : ∑ i, N i = 3)
    (hHolder : (∑ i, w i) - (∑ i, a i) ≤ H * T)
    (hG : 0 ≤ G) (hfailure : (c * p) * G + T < 3)
    (ht : t ≤ T) (htail : 6 - G ≤ (∑ i, w i) + 3 * ε)
    (hW0 : 0 ≤ 6 - (3 - t) / (c * α) - 3 * ε)
    (hWbase : (6 - (3 - t) / (c * α) - 3 * ε) / (3 * Γ) ≤ 1)
    (hB0 : 0 ≤ B) (hB3 : B ≤ 3)
    (hcert : 1 ≤ (B / 3) ^ β +
      ((6 - (3 - t) / (c * α) - 3 * ε) / (3 * Γ)) ^ β)
    (hnext : H * t' ≤ 6 - (3 - t) / (c * α) - 3 * ε - B) : t' < T := by
  have hcmp : (c * α) * G ≤ (c * p) * G :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαp hc.le) hG
  have hGupper : G < (3 - t) / (c * α) := by
    apply (lt_div_iff₀ (mul_pos hc hα)).2
    nlinarith only [hcmp, hfailure, ht]
  have hWstrict : 6 - (3 - t) / (c * α) - 3 * ε < ∑ i, w i := by
    linarith
  exact aggregate_bootstrap (lt_of_lt_of_le zero_lt_one hp) hpβ
    (Finset.sum_nonneg fun i _ ↦ ha i) (Finset.sum_nonneg fun i _ ↦ hw i)
    hγ hγΓ hH (aggregate_rows hp hγ a w N ha hw hN hrow hS)
    hHolder hW0 hWstrict hB0 hB3 hWbase hcert hnext

end HlawkaSchatten.DiagonalCutoff16



set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace HlawkaSchatten.DiagonalCutoff16

theorem rpow_tangent_lower {p x y : ℝ} (hp : 1 ≤ p) (hx : 0 < x) (hy : 0 ≤ y) :
    x ^ p + p * x ^ (p - 1) * (y - x) ≤ y ^ p := by
  have hb := one_add_mul_self_le_rpow_one_add
    (show -1 ≤ (y - x) / x by apply (le_div_iff₀ hx).2; linarith) hp
  have he : 1 + (y - x) / x = y / x := by field_simp; ring
  rw [he, Real.div_rpow hy hx.le] at hb
  have hm := (le_div_iff₀ (Real.rpow_pos_of_pos hx p)).1 hb
  have hpowers : x ^ p = x ^ (p - 1) * x := by
    conv_lhs => rw [show p = (p - 1) + 1 by ring]
    rw [Real.rpow_add hx, Real.rpow_one]
  have hid : (1 + p * ((y - x) / x)) * x ^ p =
      x ^ p + p * x ^ (p - 1) * (y - x) := by
    rw [hpowers]
    field_simp <;> ring
  rwa [hid] at hm

/-- A pair of power checks controls an entire ray, rather than an iteration. -/
theorem power_barrier {p β x y k l d : ℝ}
    (hp : 1 ≤ p) (hpβ : p ≤ β)
    (hx : 0 < x) (hx1 : x ≤ 1) (hy : 0 < y) (hy1 : y ≤ 1)
    (hk : 0 ≤ k) (hl : 0 ≤ l) (hd : 0 ≤ d) (hyd : 0 ≤ y - l * d)
    (hvalue : 1 < x ^ β + y ^ β) (hslope : l ≤ k * x ^ (β - 1)) :
    1 < (x + k * d) ^ p + (y - l * d) ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have hv : 1 < x ^ p + y ^ p := hvalue.trans_le (add_le_add
    (Real.rpow_le_rpow_of_exponent_ge' hx.le hx1 hp0 hpβ)
    (Real.rpow_le_rpow_of_exponent_ge' hy.le hy1 hp0 hpβ))
  have hxp : x ^ (β - 1) ≤ x ^ (p - 1) :=
    Real.rpow_le_rpow_of_exponent_ge' hx.le hx1 hp1 (by linarith)
  have hyp : y ^ (p - 1) ≤ 1 := by
    simpa using Real.rpow_le_rpow hy.le hy1 hp1
  have hcoeff : l * y ^ (p - 1) ≤ k * x ^ (p - 1) := calc
    l * y ^ (p - 1) ≤ l := by nlinarith only [mul_le_mul_of_nonneg_left hyp hl]
    _ ≤ k * x ^ (β - 1) := hslope
    _ ≤ k * x ^ (p - 1) := mul_le_mul_of_nonneg_left hxp hk
  have h1 := rpow_tangent_lower hp hx (show 0 ≤ x + k * d by positivity)
  have h2 := rpow_tangent_lower hp hy hyd
  have h3 := mul_nonneg (mul_nonneg hp0 hd) (sub_nonneg.mpr hcoeff)
  nlinarith only [hv, h1, h2, h3]

theorem aggregate_barrier {p β A W γ Γ H T u v t x y k l : ℝ}
    (hp : 1 ≤ p) (hpβ : p ≤ β) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hγ : 0 < γ) (hγΓ : γ ≤ Γ) (hH : 0 < H)
    (hbudget : A ^ p + (W / γ) ^ p ≤ (3 : ℝ) ^ p)
    (hHolder : W - A ≤ H * T) (hT : 1 ≤ T)
    (hv : 0 ≤ v) (huv : 0 ≤ u + v) (hWlower : u + v * T ≤ W)
    (hxdef : x = (u + (v - H) * t) / 3)
    (hydef : y = (u + v * t) / (3 * Γ))
    (hkdef : k = (H - v) / 3) (hldef : l = v / (3 * Γ))
    (hx : 0 < x) (hx1 : x ≤ 1) (hy : 0 < y) (hy1 : y ≤ 1)
    (hk : 0 ≤ k) (hvalue : 1 < x ^ β + y ^ β)
    (hslope : l ≤ k * x ^ (β - 1)) : t < T := by
  by_contra hn
  have hTt : T ≤ t := le_of_not_gt hn
  have hΓ : 0 < Γ := hγ.trans_le hγΓ
  have hp0 : 0 < p := by linarith
  have hthree : 0 < (3 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  have hnormalized : (A / 3) ^ p + ((W / γ) / 3) ^ p ≤ 1 := by
    rw [Real.div_rpow hA (by norm_num),
      Real.div_rpow (div_nonneg hW hγ.le) (by norm_num), ← add_div]
    exact (div_le_iff₀ hthree).2 (by simpa using hbudget)
  have hld : 0 ≤ l := by rw [hldef]; positivity
  have hyt : y - l * (t - T) = (u + v * T) / (3 * Γ) := by
    rw [hydef, hldef]; ring
  have hxt : x + k * (t - T) = (u + (v - H) * T) / 3 := by
    rw [hxdef, hkdef]; ring
  have hupos : 0 ≤ u + v * T := by nlinarith only [hv, huv, hT]
  have hyd : 0 ≤ y - l * (t - T) := by rw [hyt]; positivity
  have hxmin : x + k * (t - T) ≤ A / 3 := by
    rw [hxt]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    nlinarith only [hWlower, hHolder]
  have hymin : y - l * (t - T) ≤ (W / γ) / 3 := by
    rw [hyt]
    have h1 : (u + v * T) / Γ ≤ W / γ := calc
      (u + v * T) / Γ ≤ W / Γ := div_le_div_of_nonneg_right hWlower hΓ.le
      _ ≤ W / γ := div_le_div_of_nonneg_left hW hγ hγΓ
    calc (u + v * T) / (3 * Γ) = ((u + v * T) / Γ) / 3 := by ring
         _ ≤ (W / γ) / 3 := div_le_div_of_nonneg_right h1 (by norm_num)
  have hb := power_barrier hp hpβ hx hx1 hy hy1 hk hld
    (sub_nonneg.mpr hTt) hyd hvalue hslope
  have hxnonneg : 0 ≤ x + k * (t - T) := by positivity
  have h1 := Real.rpow_le_rpow hxnonneg hxmin hp0.le
  have h2 := Real.rpow_le_rpow hyd hymin hp0.le
  linarith

end HlawkaSchatten.DiagonalCutoff16



set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalRealBundle

namespace HlawkaSchatten.DiagonalCutoff16

theorem cp_upper_interval {p β B : ℝ} (hp : 0 < p) (hpβ : p ≤ β)
    (hB : (1/2 : ℝ) ^ (1/β) ≤ B) : cp p ≤ 2*B := by
  have he := one_div_le_one_div_of_le hp hpβ
  have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) he
  unfold cp
  linarith

theorem holder_upper_interval {p β H : ℝ} (hp : 0 < p) (hpβ : p ≤ β)
    (hH : (3 : ℝ) ^ (1 - 1/β) ≤ H) : (3 : ℝ) ^ (1 - 1/p) ≤ H := by
  have he := one_div_le_one_div_of_le hp hpβ
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    (by linarith : 1 - 1/p ≤ 1 - 1/β)).trans hH

theorem sum_le_three_holder {p : ℝ} (hp : 1 ≤ p) (v : Fin 3 → ℝ) :
    (∑ i, v i) ≤ (3 : ℝ) ^ (1 - 1 / p) * lpNorm p v := by
  have hp0 : 0 < p := by linarith
  have hpow := Real.rpow_sum_le_const_mul_sum_rpow Finset.univ v hp
  have he : ((3 : ℝ) ^ (1 - 1 / p) * lpNorm p v) ^ p =
      (3 : ℝ) ^ (p - 1) * ∑ i, |v i| ^ p := by
    rw [Real.mul_rpow (by positivity) (lpNorm_nonneg p v),
      ← Real.rpow_mul (by norm_num), lpNorm_pow3 hp0]
    congr 2
    field_simp
  have hright : 0 ≤ (3 : ℝ) ^ (1 - 1 / p) * lpNorm p v :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (lpNorm_nonneg p v)
  have hleft : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hsum : (∑ i, |v i|) ≤ (3 : ℝ) ^ (1 - 1 / p) * lpNorm p v := by
    apply (Real.rpow_le_rpow_iff hleft hright hp0).mp
    rw [he]
    simpa using hpow
  exact (Finset.sum_le_sum fun i _ ↦ le_abs_self (v i)).trans hsum

theorem oriented_aggregate_budget {p ell u v w : ℝ} (hp : 1 ≤ p)
    (hell : 0 < ell) (hv : 0 < v) (X : Fin 3 → Fin 3 → ℝ)
    (hB : coordinateBox ell u v w X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3) :
    (-X 0 0 - X 1 1 - X 2 2) ^ p + (offsum X / cp p) ^ p ≤ (3 : ℝ) ^ p := by
  have hp0 : 0 < p := by linarith
  have hd (i : Fin 3) : 0 ≤ -X i i := by
    have hi := hB i i
    simp only [coordinateBox, if_pos rfl] at hi
    linarith [hi.2]
  have ho (i j : Fin 3) (hij : i ≠ j) : 0 ≤ X i j := by
    have hi := hB i j
    rw [if_neg hij] at hi
    linarith [hi.1]
  have row (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      (-X i i) ^ p + ((X i j + X i k) / cp p) ^ p ≤ lpNorm p (X i) ^ p := by
    have hf := lpNorm_pow3 hp0 (X i)
    rw [sum3 _ hij hik hjk, abs_of_nonpos (by linarith [hd i]),
      abs_of_nonneg (ho i j hij), abs_of_nonneg (ho i k hik)] at hf
    have ht := sum_div_cp_rpow_le hp (ho i j hij) (ho i k hik)
    linarith
  let a : Fin 3 → ℝ := fun i ↦ -X i i
  let b : Fin 3 → ℝ := ![X 0 1 + X 0 2, X 1 0 + X 1 2, X 2 0 + X 2 1]
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    fin_cases i
    · exact add_nonneg (ho 0 1 (by decide)) (ho 0 2 (by decide))
    · exact add_nonneg (ho 1 0 (by decide)) (ho 1 2 (by decide))
    · exact add_nonneg (ho 2 0 (by decide)) (ho 2 1 (by decide))
  have hr : ∀ i, a i ^ p + (b i / cp p) ^ p ≤ lpNorm p (X i) ^ p := by
    intro i
    fin_cases i
    · exact row 0 1 2 (by decide) (by decide) (by decide)
    · exact row 1 0 2 (by decide) (by decide) (by decide)
    · exact row 2 0 1 (by decide) (by decide) (by decide)
  have h := aggregate_rows hp (cp_pos p) a b (fun i ↦ lpNorm p (X i))
    hd hb (fun i ↦ lpNorm_nonneg p _) hr (by simpa only [Fin.sum_univ_three] using hS)
  simpa [Fin.sum_univ_three, a, b, offsum, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h

theorem norm_barrier {p α β c H Γ ell ub vb wb ε t x y k l : ℝ}
    (hp : 1 ≤ p) (hα : 0 < α) (hαp : α ≤ p) (hpβ : p ≤ β)
    (hc : 0 < c) (hH : 0 < H) (hΓ : cp p ≤ Γ)
    (hHolder : (3 : ℝ) ^ (1 - 1 / p) ≤ H)
    (hell : 0 < ell) (hv : 0 < vb) (X : Fin 3 → Fin 3 → ℝ)
    (hB : coordinateBox ell ub vb wb X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT : 1 ≤ lpNorm p (X 0 + X 1 + X 2))
    (hfailure : (c * p) * pairGapSum (lpNorm p) (X 0) (X 1) (X 2) +
      lpNorm p (X 0 + X 1 + X 2) < 3)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ X j i + X k i + ε)
    (huv : 0 ≤ 6 - 2 / (c * α) - 3 * ε)
    (hxdef : x = (6 - 3 / (c * α) - 3 * ε + (1 / (c * α) - H) * t) / 3)
    (hydef : y = (6 - 3 / (c * α) - 3 * ε + t / (c * α)) / (3 * Γ))
    (hkdef : k = (H - 1 / (c * α)) / 3)
    (hldef : l = (1 / (c * α)) / (3 * Γ))
    (hx : 0 < x) (hx1 : x ≤ 1) (hy : 0 < y) (hy1 : y ≤ 1) (hk : 0 ≤ k)
    (hvalue : 1 < x ^ β + y ^ β) (hslope : l ≤ k * x ^ (β - 1)) :
    t < lpNorm p (X 0 + X 1 + X 2) := by
  have hA : 0 ≤ -X 0 0 - X 1 1 - X 2 2 := by
    have h0 := hB 0 0; have h1 := hB 1 1; have h2 := hB 2 2
    simp only [if_pos rfl] at h0 h1 h2
    linarith [h0.2, h1.2, h2.2]
  have hW : 0 ≤ offsum X := by
    have ho (i j : Fin 3) (hij : i ≠ j) : 0 ≤ X i j := by
      have hi := hB i j
      rw [if_neg hij] at hi
      linarith [hi.1]
    dsimp [offsum]
    linarith [ho 0 1 (by decide), ho 0 2 (by decide), ho 1 0 (by decide),
      ho 1 2 (by decide), ho 2 0 (by decide), ho 2 1 (by decide)]
  have hHnorm := mul_le_mul_of_nonneg_right hHolder
    (lpNorm_nonneg p (X 0 + X 1 + X 2))
  have hh := sum_le_three_holder hp (X 0 + X 1 + X 2)
  have holder : offsum X - (-X 0 0 - X 1 1 - X 2 2) ≤
      H * lpNorm p (X 0 + X 1 + X 2) := by
    simp only [Fin.sum_univ_three, Pi.add_apply] at hh
    dsimp [offsum]
    linarith
  have hG0 := pairGapSum_nonneg hp (X 0) (X 1) (X 2)
  have hcmp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαp hc.le) hG0
  have hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) <
      (3 - lpNorm p (X 0 + X 1 + X 2)) / (c * α) := by
    apply (lt_div_iff₀ (mul_pos hc hα)).2
    nlinarith only [hcmp, hfailure]
  have ht0 := htail 0 1 2 (by decide) (by decide) (by decide)
  have ht1 := htail 1 0 2 (by decide) (by decide) (by decide)
  have ht2 := htail 2 0 1 (by decide) (by decide) (by decide)
  have hwlower : 6 - 3 / (c * α) - 3 * ε +
      (1 / (c * α)) * lpNorm p (X 0 + X 1 + X 2) ≤ offsum X := by
    dsimp [pairGapSum, pairGap] at hG
    dsimp [offsum]
    rw [sub_div] at hG
    simp only [div_eq_mul_inv, one_mul] at hG ⊢
    linarith
  exact aggregate_barrier hp hpβ hA hW (cp_pos p) hΓ hH
    (oriented_aggregate_budget hp hell hv X hB hS) holder hT
    (by positivity) (by convert huv using 1 <;> ring) hwlower hxdef
    (by simpa only [one_div_mul_eq_div] using hydef)
    hkdef hldef hx hx1 hy hy1 hk hvalue hslope

end HlawkaSchatten.DiagonalCutoff16


set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalRealBundle

namespace HlawkaSchatten.DiagonalCutoff16

theorem failure_linear_bound {p c : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (hK : c*p ≤ cyclicConstant p)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hf : tripleDeficit p (cyclicConstant p) X < 0) :
    (c*p)*pairGapSum (lpNorm p) (X 0) (X 1) (X 2) + lpNorm p (X 0 + X 1 + X 2) < 3 := by
  change hlawkaDeficit p (cyclicConstant p) (X 0) (X 1) (X 2) < 0 at hf
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf
  have h := mul_le_mul_of_nonneg_right hK (pairGapSum_nonneg hp (X 0) (X 1) (X 2))
  linarith

theorem gap_of_total_lower {p α c G T t : ℝ} (hα : 0 < α) (hαp : α ≤ p)
    (hc : 0 < c) (hG : 0 ≤ G) (hf : (c*p)*G+T < 3) (ht : t ≤ T) :
    G < (3-t)/(c*α) := by
  apply (lt_div_iff₀ (mul_pos hc hα)).2
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαp hc.le) hG
  nlinarith only [h, hf, ht]

theorem initial_norm_lower {p ell u v w : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (hB : coordinateBox ell u v w X) : ∀ i, v ≤ lpNorm p (X i) := by
  intro i
  obtain ⟨j, k, hij, hik, hjk⟩ := others i
  have hx : v ≤ X i j := by
    have h : v ≤ X i j ∧ X i j ≤ w := by simpa [coordinateBox, hij] using hB i j
    exact h.1
  have hc := norm_apply_le_lpNorm hp (X i) j
  rw [Real.norm_eq_abs] at hc
  exact hx.trans ((le_abs_self _).trans hc)

theorem pairGapSum_perm (p : ℝ) (X : Fin 3 → Fin 3 → ℝ) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    pairGapSum (lpNorm p) (X i) (X j) (X k) =
      pairGapSum (lpNorm p) (X 0) (X 1) (X 2) := by
  have h10 : lpNorm p (X 1 + X 0) = lpNorm p (X 0 + X 1) := by rw [add_comm]
  have h20 : lpNorm p (X 2 + X 0) = lpNorm p (X 0 + X 2) := by rw [add_comm]
  have h21 : lpNorm p (X 2 + X 1) = lpNorm p (X 1 + X 2) := by rw [add_comm]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  all_goals simp only [pairGapSum, pairGap, h10, h20, h21]; ring

theorem pair_floor_of_gap {p g U eps : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hU : ∀ i, lpNorm p (X i) ≤ U)
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < g)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ X j i + X k i + eps) :
    ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      3 - U - g - eps ≤ X j i + X k i := by
  intro i j k hij hik hjk
  have hperm := pairGapSum_perm p X hij hik hjk
  have hg := hG
  rw [← hperm] at hg
  have h1 := pairGap_nonneg hp (X i) (X j)
  have h2 := pairGap_nonneg hp (X i) (X k)
  have hsum := sum3 (fun l ↦ lpNorm p (X l)) hij hik hjk
  rw [Fin.sum_univ_three] at hsum
  have ht := htail i j k hij hik hjk
  have hi := hU i
  dsimp only [pairGapSum, pairGap] at hg h1 h2
  linarith

theorem offsum_floor_of_gap {p g eps : ℝ} (X : Fin 3 → Fin 3 → ℝ)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < g)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ X j i + X k i + eps) :
    6-g-3*eps ≤ offsum X := by
  have t0 := htail 0 1 2 (by decide) (by decide) (by decide)
  have t1 := htail 1 0 2 (by decide) (by decide) (by decide)
  have t2 := htail 2 0 1 (by decide) (by decide) (by decide)
  dsimp only [pairGapSum, pairGap] at hG
  dsimp only [offsum]
  linarith

end HlawkaSchatten.DiagonalCutoff16


namespace HlawkaSchatten.DiagonalCutoff16

theorem rpow_sum_lower {x y X Y p b : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hp : 0 ≤ p) (hpb : p ≤ b) (hX : X ≤ x^b) (hY : Y ≤ y^b)
    (hs : 1 < X+Y) : 1 < x^p+y^p := by
  have hx' := hX.trans (Real.rpow_le_rpow_of_exponent_ge' hx hx1 hp hpb)
  have hy' := hY.trans (Real.rpow_le_rpow_of_exponent_ge' hy hy1 hp hpb)
  linarith only [hx', hy', hs]

theorem rpow_nat_add_lower {x X d : ℝ} (n : ℕ) (hx : 0 < x) (h : X ≤ x^d) :
    x^n*X ≤ x^((n : ℝ)+d) := by
  rw [Real.rpow_add hx, Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left h (pow_nonneg hx.le n)

theorem rpow_nat_add_upper {x X d : ℝ} (n : ℕ) (hx : 0 < x) (h : x^d ≤ X) :
    x^((n : ℝ)+d) ≤ x^n*X := by
  rw [Real.rpow_add hx, Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_left h (pow_nonneg hx.le n)

theorem lower_root_of_power {x y a : ℝ} (ha : 0 < a) (hy : 0 ≤ y)
    (h : y^a ≤ x) : y ≤ x^(1/a) := by
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hy _) h (one_div_nonneg.mpr ha.le)
  rw [← Real.rpow_mul hy, mul_one_div_cancel ha.ne', Real.rpow_one] at hh
  exact hh

theorem upper_root_of_power {x y a : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ≤ y^a) : x^(1/a) ≤ y := by
  have hh := Real.rpow_le_rpow hx h (one_div_nonneg.mpr ha.le)
  rw [← Real.rpow_mul hy, mul_one_div_cancel ha.ne', Real.rpow_one] at hh
  exact hh

theorem holder_of_power {a H : ℝ} (ha : 0 < a) (hH : 0 ≤ H)
    (h : (1/3 : ℝ) ≤ (H/3)^a) : (3 : ℝ)^(1-1/a) ≤ H := by
  have hh := upper_root_of_power ha (by norm_num : (0 : ℝ) ≤ 1/3) (by positivity : 0 ≤ H/3) h
  have he : (3 : ℝ)^(1-1/a) = 3*((1/3 : ℝ)^(1/a)) := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 3), Real.rpow_one]
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 3), Real.one_rpow]
    ring
  rw [he]
  linarith

end HlawkaSchatten.DiagonalCutoff16


set_option autoImplicit false
namespace HlawkaSchatten.DiagonalBelow16Dyadic

theorem dyadic_step_upper {x a A B : ℝ} (n : ℕ)
    (hx : 0 < x) (hB : 0 ≤ B) (h : x^a ≤ A)
    (hcert : A*x^n ≤ B^2) : x^((a+(n : ℝ))/2) ≤ B := by
  have hh : x^(a+(n : ℝ)) ≤ B^2 := by
    rw [Real.rpow_add hx, Real.rpow_natCast]
    exact (mul_le_mul_of_nonneg_right h (pow_nonneg hx.le n)).trans hcert
  apply (sq_le_sq₀ (Real.rpow_nonneg hx.le _) hB).mp
  have he : (x^((a+(n : ℝ))/2))^2 = x^(a+(n : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  rw [he]
  exact hh

theorem dyadic_step_lower {x a A B : ℝ} (n : ℕ)
    (hx : 0 < x) (hB : 0 ≤ B) (h : A ≤ x^a)
    (hcert : B^2 ≤ A*x^n) : B ≤ x^((a+(n : ℝ))/2) := by
  have hh : B^2 ≤ x^(a+(n : ℝ)) := by
    rw [Real.rpow_add hx, Real.rpow_natCast]
    exact hcert.trans (mul_le_mul_of_nonneg_right h (pow_nonneg hx.le n))
  apply (sq_le_sq₀ hB (Real.rpow_nonneg hx.le _)).mp
  have he : (x^((a+(n : ℝ))/2))^2 = x^(a+(n : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  rw [he]
  exact hh

end HlawkaSchatten.DiagonalBelow16Dyadic

/- Exact certificates for the non-iterative total-norm barrier. -/
open HlawkaSchatten.DiagonalCutoff16
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 20000
namespace HlawkaSchatten.DiagonalBelow16


theorem roots_w001_s003 :
    (957496667/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (512/8171 : ℝ) ∧
    (1/2 : ℝ) ^ (128/2043 : ℝ) ≤ (957501757/1000000000 : ℝ) ∧
    (3 : ℝ) ^ (1915/2043 : ℝ) ≤ (7001131/2500000 : ℝ) := by
  have hpLoFraction : (957496667/1000000000 : ℝ) ^ (491/512 : ℝ) ≤ (19184078071951/20000000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (957496667/1000000000 : ℝ)) (X := (19184078071951/20000000000000 : ℝ)) (by norm_num) (by norm_num) 491 512 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hpLo : (957496667/1000000000 : ℝ) ^ (8171/512 : ℝ) ≤ (1/2 : ℝ) := by
    have hs := rpow_nat_add_upper 15 (by norm_num : (0 : ℝ) < (957496667/1000000000 : ℝ)) hpLoFraction
    have he : ((15 : ℕ) : ℝ) + (491/512 : ℝ) = (8171/512 : ℝ) := by norm_num
    rw [he] at hs
    exact hs.trans (by norm_num : (957496667/1000000000 : ℝ) ^ (15 : ℕ) * (19184078071951/20000000000000 : ℝ) ≤ (1/2 : ℝ))
  have hpHiFraction : (959127437110617/1000000000000000 : ℝ) ≤ (957501757/1000000000 : ℝ) ^ (123/128 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (957501757/1000000000 : ℝ)) (X := (959127437110617/1000000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hpHi : (1/2 : ℝ) ≤ (957501757/1000000000 : ℝ) ^ (2043/128 : ℝ) := by
    have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (957501757/1000000000 : ℝ)) hpHiFraction
    have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
    rw [he] at hs
    exact (show (1/2 : ℝ) ≤ (957501757/1000000000 : ℝ) ^ (15 : ℕ) * (959127437110617/1000000000000000 : ℝ) by norm_num).trans hs
  have hpHolderFraction : (467998695481419/500000000000000 : ℝ) ≤ (7001131/7500000 : ℝ) ^ (123/128 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (7001131/7500000 : ℝ)) (X := (467998695481419/500000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hpHolder : (1/3 : ℝ) ≤ (7001131/7500000 : ℝ) ^ (2043/128 : ℝ) := by
    have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (7001131/7500000 : ℝ)) hpHolderFraction
    have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
    rw [he] at hs
    exact (show (1/3 : ℝ) ≤ (7001131/7500000 : ℝ) ^ (15 : ℕ) * (467998695481419/500000000000000 : ℝ) by norm_num).trans hs
  have h1 := lower_root_of_power (by norm_num : (0 : ℝ) < (8171/512 : ℝ)) (by norm_num : (0 : ℝ) ≤ (957496667/1000000000 : ℝ)) hpLo
  have h2 := upper_root_of_power (by norm_num : (0 : ℝ) < (2043/128 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ (957501757/1000000000 : ℝ)) hpHi
  have h3 := holder_of_power (a := (2043/128 : ℝ)) (H := (7001131/2500000 : ℝ)) (by norm_num) (by norm_num) (by convert hpHolder using 1 <;> norm_num)
  constructor
  · convert h1 using 1 <;> norm_num
  constructor
  · convert h2 using 1 <;> norm_num
  · convert h3 using 1 <;> norm_num


theorem barrier_w001_s003 (p : ℝ) (hpa : (8171/512 : ℝ) ≤ p) (hpb : p ≤ (2043/128 : ℝ))
    (Z : Fin 3 → Fin 3 → ℝ) (hB : coordinateBox (2249/10000 : ℝ) (63/50 : ℝ) (1537/2500 : ℝ) (63/50 : ℝ) Z)
    (hS : lpNorm p (Z 0) + lpNorm p (Z 1) + lpNorm p (Z 2) = 3)
    (hT : 1 ≤ lpNorm p (Z 0 + Z 1 + Z 2))
    (hfailure : ((10689/25000 : ℝ)*p) * pairGapSum (lpNorm p) (Z 0) (Z 1) (Z 2) + lpNorm p (Z 0 + Z 1 + Z 2) < 3)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (Z j + Z k) ≤ Z j i + Z k i + (1/25000000 : ℝ)) :
    (74900157/62500000 : ℝ) < lpNorm p (Z 0 + Z 1 + Z 2) := by
  have hxSmallFraction : (400253899852407/500000000000000 : ℝ) ≤ (10826040624398499003209/13646846718750000000000 : ℝ) ^ (123/128 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10826040624398499003209/13646846718750000000000 : ℝ)) (X := (400253899852407/500000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hxSmall : (24827080391/1000000000000 : ℝ) ≤ (10826040624398499003209/13646846718750000000000 : ℝ) ^ (2043/128 : ℝ) := by
    have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (10826040624398499003209/13646846718750000000000 : ℝ)) hxSmallFraction
    have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
    rw [he] at hs
    exact (show (24827080391/1000000000000 : ℝ) ≤ (10826040624398499003209/13646846718750000000000 : ℝ) ^ (15 : ℕ) * (400253899852407/500000000000000 : ℝ) by norm_num).trans hs
  have hySmallFraction : (249621887184837/250000000000000 : ℝ) ≤ (83496409278803620/83628030148561983 : ℝ) ^ (123/128 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (83496409278803620/83628030148561983 : ℝ)) (X := (249621887184837/250000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hySmall : (121896615811/125000000000 : ℝ) ≤ (83496409278803620/83628030148561983 : ℝ) ^ (2043/128 : ℝ) := by
    have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (83496409278803620/83628030148561983 : ℝ)) hySmallFraction
    have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
    rw [he] at hs
    exact (show (121896615811/125000000000 : ℝ) ≤ (83496409278803620/83628030148561983 : ℝ) ^ (15 : ℕ) * (249621887184837/250000000000000 : ℝ) by norm_num).trans hs
  have hvalue : 1 < (10826040624398499003209/13646846718750000000000 : ℝ)^(2043/128 : ℝ) + (83496409278803620/83628030148561983 : ℝ)^(2043/128 : ℝ) := by
    have hsum : (1 : ℝ) < (24827080391/1000000000000 : ℝ)+(121896615811/125000000000 : ℝ) := by norm_num
    linarith only [hxSmall, hySmall, hsum]
  have hsFraction : (400253899852407/500000000000000 : ℝ) ≤ (10826040624398499003209/13646846718750000000000 : ℝ) ^ (123/128 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10826040624398499003209/13646846718750000000000 : ℝ)) (X := (400253899852407/500000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hs : (16000000000000000000000/554850738118031904602773 : ℝ) ≤ (10826040624398499003209/13646846718750000000000 : ℝ) ^ (1915/128 : ℝ) := by
    have hs := rpow_nat_add_lower 14 (by norm_num : (0 : ℝ) < (10826040624398499003209/13646846718750000000000 : ℝ)) hsFraction
    have he : ((14 : ℕ) : ℝ) + (123/128 : ℝ) = (1915/128 : ℝ) := by norm_num
    rw [he] at hs
    exact (show (16000000000000000000000/554850738118031904602773 : ℝ) ≤ (10826040624398499003209/13646846718750000000000 : ℝ) ^ (14 : ℕ) * (400253899852407/500000000000000 : ℝ) by norm_num).trans hs
  have hslope : (6400000000000000/250884090445685949 : ℝ) ≤ (579477514335289/655048642500000 : ℝ) * (10826040624398499003209/13646846718750000000000 : ℝ) ^ ((2043/128 : ℝ)-1) := by
    have hh := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ (579477514335289/655048642500000 : ℝ) by norm_num)
    have he : ((2043/128 : ℝ)-1) = (1915/128 : ℝ) := by norm_num
    have hl : (579477514335289/655048642500000 : ℝ)*(16000000000000000000000/554850738118031904602773 : ℝ) = (6400000000000000/250884090445685949 : ℝ) := by norm_num
    rw [he]
    simpa only [hl] using hh
  have hthi : (1/2 : ℝ) ^ (1/(2043/128 : ℝ)) ≤ (957501757/1000000000 : ℝ) := by
    convert roots_w001_s003.2.1 using 1 <;> norm_num
  have hH : (3 : ℝ) ^ (1-1/(2043/128 : ℝ)) ≤ (7001131/2500000 : ℝ) := by
    convert roots_w001_s003.2.2 using 1 <;> norm_num
  apply norm_barrier (α := (8171/512 : ℝ)) (β := (2043/128 : ℝ)) (c := (10689/25000 : ℝ)) (H := (7001131/2500000 : ℝ)) (Γ := (957501757/500000000 : ℝ))
    (x := (10826040624398499003209/13646846718750000000000 : ℝ)) (y := (83496409278803620/83628030148561983 : ℝ)) (k := (579477514335289/655048642500000 : ℝ)) (l := (6400000000000000/250884090445685949 : ℝ))
    (by linarith) (by norm_num) hpa hpb (by norm_num) (by norm_num)
    (by have h := cp_upper_interval (by linarith : 0 < p) hpb hthi; norm_num at h ⊢; exact h)
    (holder_upper_interval (by linarith) hpb hH)
    (by norm_num) (by norm_num) Z hB hS hT hfailure htail
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hvalue hslope



end HlawkaSchatten.DiagonalBelow16

open HlawkaSchatten.DiagonalCutoff16
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 20000
namespace HlawkaSchatten.DiagonalRealBundle
theorem contract_w001_s003 (p : ℝ) (hpa : (8171/512 : ℝ) ≤ p) (hpb : p ≤ (2043/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (N : Fin 3 → ℝ)
    (F : Facts p (cp p) (131620869758363/14556636500000000 : ℝ) (4721679/1000000000 : ℝ) (192170486059819/727831825000000 : ℝ) (62997/50000 : ℝ) (957501757/500000000 : ℝ) (957496667/1000000000 : ℝ) X N)
    (hn0 : ∀ i, (1537/2500 : ℝ) ≤ N i) :
    (∀ i, N i ≤ (35924473/31250000 : ℝ)) ∧ coordinateBox (4531/10000 : ℝ) (4837/5000 : ℝ) (197/250 : ℝ) (9/8 : ℝ) X := by
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ (131620869758363/14556636500000000 : ℝ) := by norm_num
  have hd0 : (0 : ℝ) ≤ (4721679/1000000000 : ℝ) := by norm_num
  have pc0 : 1 < (918920031/1000000000 : ℝ) ^ p + (981366107/1000000000 : ℝ) ^ p := by
    have hcxFraction : (921960219599729/1000000000000000 : ℝ) ≤ (918920031/1000000000 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (918920031/1000000000 : ℝ)) (X := (921960219599729/1000000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcx : (2593450487223/10000000000000 : ℝ) ≤ (918920031/1000000000 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (918920031/1000000000 : ℝ)) hcxFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (2593450487223/10000000000000 : ℝ) ≤ (918920031/1000000000 : ℝ) ^ (15 : ℕ) * (921960219599729/1000000000000000 : ℝ) by norm_num).trans hs
    have hcyFraction : (245521858553183/250000000000000 : ℝ) ≤ (981366107/1000000000 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (981366107/1000000000 : ℝ)) (X := (245521858553183/250000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcy : (74065503127783/100000000000000 : ℝ) ≤ (981366107/1000000000 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (981366107/1000000000 : ℝ)) hcyFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (74065503127783/100000000000000 : ℝ) ≤ (981366107/1000000000 : ℝ) ^ (15 : ℕ) * (245521858553183/250000000000000 : ℝ) by norm_num).trans hs
    exact HlawkaSchatten.DiagonalCutoff16.rpow_sum_lower (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp0 hpb hcx hcy (by norm_num)
  have pc1 : 1 < (981366107/1000000000 : ℝ) ^ p + (918920031/1000000000 : ℝ) ^ p := by simpa only [add_comm] using pc0
  have R0 := ratio_round F hn0 (by norm_num) hD0
    (s := (950143069/500000000 : ℝ)) (τ := (918920031/1000000000 : ℝ)) (σ := (981366107/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc0) (by norm_num; exact pc1)
  have pc2 : 1 < (722481685/842661178 : ℝ) ^ p + (837939499/842661178 : ℝ) ^ p := by
    have hcxFraction : (862549945908307/1000000000000000 : ℝ) ≤ (722481685/842661178 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (722481685/842661178 : ℝ)) (X := (862549945908307/1000000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcx : (4289059755979/50000000000000 : ℝ) ≤ (722481685/842661178 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (722481685/842661178 : ℝ)) hcxFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (4289059755979/50000000000000 : ℝ) ≤ (722481685/842661178 : ℝ) ^ (15 : ℕ) * (862549945908307/1000000000000000 : ℝ) by norm_num).trans hs
    have hcyFraction : (24865374837141/25000000000000 : ℝ) ≤ (837939499/842661178 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (837939499/842661178 : ℝ)) (X := (24865374837141/25000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcy : (91421880795173/100000000000000 : ℝ) ≤ (837939499/842661178 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (837939499/842661178 : ℝ)) hcyFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (91421880795173/100000000000000 : ℝ) ≤ (837939499/842661178 : ℝ) ^ (15 : ℕ) * (24865374837141/25000000000000 : ℝ) by norm_num).trans hs
    exact HlawkaSchatten.DiagonalCutoff16.rpow_sum_lower (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp0 hpb hcx hcy (by norm_num)
  have L0 := lower_round F hn0 (by norm_num) hd0
    (τ := (918920031/1000000000 : ℝ)) (n' := (421330589/500000000 : ℝ)) (Ab := (144496337/200000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R0 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc2.le) (by norm_num)
  have pc3 : 1 < (231395611/250000000 : ℝ) ^ p + (978680617/1000000000 : ℝ) ^ p := by
    have hcxFraction : (928382655927259/1000000000000000 : ℝ) ≤ (231395611/250000000 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (231395611/250000000 : ℝ)) (X := (928382655927259/1000000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcx : (1819004040349/6250000000000 : ℝ) ≤ (231395611/250000000 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (231395611/250000000 : ℝ)) hcxFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (1819004040349/6250000000000 : ℝ) ≤ (231395611/250000000 : ℝ) ^ (15 : ℕ) * (928382655927259/1000000000000000 : ℝ) by norm_num).trans hs
    have hcyFraction : (979504811216023/1000000000000000 : ℝ) ≤ (978680617/1000000000 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (978680617/1000000000 : ℝ)) (X := (979504811216023/1000000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcy : (35447971215771/50000000000000 : ℝ) ≤ (978680617/1000000000 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (978680617/1000000000 : ℝ)) hcyFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (35447971215771/50000000000000 : ℝ) ≤ (978680617/1000000000 : ℝ) ^ (15 : ℕ) * (979504811216023/1000000000000000 : ℝ) by norm_num).trans hs
    exact HlawkaSchatten.DiagonalCutoff16.rpow_sum_lower (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp0 hpb hcx hcy (by norm_num)
  have pc4 : 1 < (978680617/1000000000 : ℝ) ^ p + (231395611/250000000 : ℝ) ^ p := by simpa only [add_comm] using pc3
  have R1 := ratio_round F L0 (by norm_num) hD0
    (s := (1904263061/1000000000 : ℝ)) (τ := (231395611/250000000 : ℝ)) (σ := (978680617/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc3) (by norm_num; exact pc4)
  have pc5 : 1 < (104167192/121566205 : ℝ) ^ p + (846241756/850963435 : ℝ) ^ p := by
    have hcxFraction : (172412393264733/200000000000000 : ℝ) ≤ (104167192/121566205 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (104167192/121566205 : ℝ)) (X := (172412393264733/200000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcx : (339914698327/4000000000000 : ℝ) ≤ (104167192/121566205 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (104167192/121566205 : ℝ)) hcxFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (339914698327/4000000000000 : ℝ) ≤ (104167192/121566205 : ℝ) ^ (15 : ℕ) * (172412393264733/200000000000000 : ℝ) by norm_num).trans hs
    have hcyFraction : (124333442119399/125000000000000 : ℝ) ≤ (846241756/850963435 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (846241756/850963435 : ℝ)) (X := (124333442119399/125000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcy : (45751066431117/50000000000000 : ℝ) ≤ (846241756/850963435 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (846241756/850963435 : ℝ)) hcyFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (45751066431117/50000000000000 : ℝ) ≤ (846241756/850963435 : ℝ) ^ (15 : ℕ) * (124333442119399/125000000000000 : ℝ) by norm_num).trans hs
    exact HlawkaSchatten.DiagonalCutoff16.rpow_sum_lower (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp0 hpb hcx hcy (by norm_num)
  have L1 := lower_round F L0 (by norm_num) hd0
    (τ := (231395611/250000000 : ℝ)) (n' := (170192687/200000000 : ℝ)) (Ab := (91146293/125000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R1 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc5.le) (by norm_num)
  have pc6 : 1 < (925767729/1000000000 : ℝ) ^ p + (48930001/50000000 : ℝ) ^ p := by
    have hcxFraction : (46428062059469/50000000000000 : ℝ) ≤ (925767729/1000000000 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (925767729/1000000000 : ℝ)) (X := (46428062059469/50000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcx : (364964927841/1250000000000 : ℝ) ≤ (925767729/1000000000 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (925767729/1000000000 : ℝ)) hcxFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (364964927841/1250000000000 : ℝ) ≤ (925767729/1000000000 : ℝ) ^ (15 : ℕ) * (46428062059469/50000000000000 : ℝ) by norm_num).trans hs
    have hcyFraction : (979427297188381/1000000000000000 : ℝ) ≤ (48930001/50000000 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (48930001/50000000 : ℝ)) (X := (979427297188381/1000000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcy : (35401406157617/50000000000000 : ℝ) ≤ (48930001/50000000 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (48930001/50000000 : ℝ)) hcyFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (35401406157617/50000000000000 : ℝ) ≤ (48930001/50000000 : ℝ) ^ (15 : ℕ) * (979427297188381/1000000000000000 : ℝ) by norm_num).trans hs
    exact HlawkaSchatten.DiagonalCutoff16.rpow_sum_lower (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp0 hpb hcx hcy (by norm_num)
  have pc7 : 1 < (48930001/50000000 : ℝ) ^ p + (925767729/1000000000 : ℝ) ^ p := by simpa only [add_comm] using pc6
  have R2 := ratio_round F L1 (by norm_num) hD0
    (s := (1904367749/1000000000 : ℝ)) (τ := (925767729/1000000000 : ℝ)) (σ := (48930001/50000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc6) (by norm_num; exact pc7)
  have pc8 : 1 < (729355591/851193445 : ℝ) ^ p + (846471766/851193445 : ℝ) ^ p := by
    have hcxFraction : (862048515375709/1000000000000000 : ℝ) ≤ (729355591/851193445 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (729355591/851193445 : ℝ)) (X := (862048515375709/1000000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcx : (8495665369883/100000000000000 : ℝ) ≤ (729355591/851193445 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (729355591/851193445 : ℝ)) hcxFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (8495665369883/100000000000000 : ℝ) ≤ (729355591/851193445 : ℝ) ^ (15 : ℕ) * (862048515375709/1000000000000000 : ℝ) by norm_num).trans hs
    have hcyFraction : (198933795610647/200000000000000 : ℝ) ≤ (846471766/851193445 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (846471766/851193445 : ℝ)) (X := (198933795610647/200000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcy : (45752167425167/50000000000000 : ℝ) ≤ (846471766/851193445 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (846471766/851193445 : ℝ)) hcyFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (45752167425167/50000000000000 : ℝ) ≤ (846471766/851193445 : ℝ) ^ (15 : ℕ) * (198933795610647/200000000000000 : ℝ) by norm_num).trans hs
    exact HlawkaSchatten.DiagonalCutoff16.rpow_sum_lower (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp0 hpb hcx hcy (by norm_num)
  have L2 := lower_round F L1 (by norm_num) hd0
    (τ := (925767729/1000000000 : ℝ)) (n' := (170238689/200000000 : ℝ)) (Ab := (729355591/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (R2 i j k a b c).1) (by norm_num) (by norm_num)
    (by norm_num; exact pc8.le) (by norm_num)
  have pc9 : 1 < (462886409/500000000 : ℝ) ^ p + (489298901/500000000 : ℝ) ^ p := by
    have hcxFraction : (185713229231209/200000000000000 : ℝ) ≤ (462886409/500000000 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (462886409/500000000 : ℝ)) (X := (185713229231209/200000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcx : (29199756042417/100000000000000 : ℝ) ≤ (462886409/500000000 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (462886409/500000000 : ℝ)) hcxFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (29199756042417/100000000000000 : ℝ) ≤ (462886409/500000000 : ℝ) ^ (15 : ℕ) * (185713229231209/200000000000000 : ℝ) by norm_num).trans hs
    have hcyFraction : (122428145503391/125000000000000 : ℝ) ≤ (489298901/500000000 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (489298901/500000000 : ℝ)) (X := (122428145503391/125000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcy : (14160050206097/20000000000000 : ℝ) ≤ (489298901/500000000 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (489298901/500000000 : ℝ)) hcyFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (14160050206097/20000000000000 : ℝ) ≤ (489298901/500000000 : ℝ) ^ (15 : ℕ) * (122428145503391/125000000000000 : ℝ) by norm_num).trans hs
    exact HlawkaSchatten.DiagonalCutoff16.rpow_sum_lower (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp0 hpb hcx hcy (by norm_num)
  have pc10 : 1 < (489298901/500000000 : ℝ) ^ p + (462886409/500000000 : ℝ) ^ p := by simpa only [add_comm] using pc9
  have Rf := ratio_round F L2 (by norm_num) hD0
    (s := (95218531/50000000 : ℝ)) (τ := (462886409/500000000 : ℝ)) (σ := (489298901/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact pc9) (by norm_num; exact pc10)
  have pc11 : 1 < (1512364981/1850416864 : ℝ) ^ p + (1845695185/1850416864 : ℝ) ^ p := by
    have hcxFraction : (823776533623377/1000000000000000 : ℝ) ≤ (1512364981/1850416864 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (1512364981/1850416864 : ℝ)) (X := (823776533623377/1000000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcx : (998975755539/25000000000000 : ℝ) ≤ (1512364981/1850416864 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (1512364981/1850416864 : ℝ)) hcxFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (998975755539/25000000000000 : ℝ) ≤ (1512364981/1850416864 : ℝ) ^ (15 : ℕ) * (823776533623377/1000000000000000 : ℝ) by norm_num).trans hs
    have hcyFraction : (12469348361257/12500000000000 : ℝ) ≤ (1845695185/1850416864 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (1845695185/1850416864 : ℝ)) (X := (12469348361257/12500000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcy : (3840163881117/4000000000000 : ℝ) ≤ (1845695185/1850416864 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (1845695185/1850416864 : ℝ)) hcyFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (3840163881117/4000000000000 : ℝ) ≤ (1845695185/1850416864 : ℝ) ^ (15 : ℕ) * (12469348361257/12500000000000 : ℝ) by norm_num).trans hs
    exact HlawkaSchatten.DiagonalCutoff16.rpow_sum_lower (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp0 hpb hcx hcy (by norm_num)
  have pc12 : 1 < (967308313/1149583136 : ℝ) ^ p + (1144861457/1149583136 : ℝ) ^ p := by
    have hcxFraction : (423568123840519/500000000000000 : ℝ) ≤ (967308313/1149583136 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (967308313/1149583136 : ℝ)) (X := (423568123840519/500000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcx : (6358011411973/100000000000000 : ℝ) ≤ (967308313/1149583136 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (967308313/1149583136 : ℝ)) hcxFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (6358011411973/100000000000000 : ℝ) ≤ (967308313/1149583136 : ℝ) ^ (15 : ℕ) * (423568123840519/500000000000000 : ℝ) by norm_num).trans hs
    have hcyFraction : (249013206881041/250000000000000 : ℝ) ≤ (1144861457/1149583136 : ℝ) ^ (123/128 : ℝ) := by
      have h := le_rpow_of_pow_le (x := (1144861457/1149583136 : ℝ)) (X := (249013206881041/250000000000000 : ℝ)) (by norm_num) 123 128 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    have hcy : (5852624298777/6250000000000 : ℝ) ≤ (1144861457/1149583136 : ℝ) ^ (2043/128 : ℝ) := by
      have hs := rpow_nat_add_lower 15 (by norm_num : (0 : ℝ) < (1144861457/1149583136 : ℝ)) hcyFraction
      have he : ((15 : ℕ) : ℝ) + (123/128 : ℝ) = (2043/128 : ℝ) := by norm_num
      rw [he] at hs
      exact (show (5852624298777/6250000000000 : ℝ) ≤ (1144861457/1149583136 : ℝ) ^ (15 : ℕ) * (249013206881041/250000000000000 : ℝ) by norm_num).trans hs
    exact HlawkaSchatten.DiagonalCutoff16.rpow_sum_lower (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp0 hpb hcx hcy (by norm_num)
  have V := upper_round F L2 (by norm_num) hd0
    (σ := (489298901/500000000 : ℝ)) (U := (35924473/31250000 : ℝ)) (Ab := (1512364981/1000000000 : ℝ)) (by norm_num)
    (fun i j k a b c ↦ (Rf i j k a b c).2) (by norm_num) (by norm_num)
    (by norm_num; exact pc11.le) (by norm_num)
  refine ⟨V, ?_⟩
  exact final_round F L2 V (by norm_num) hd0
    (τ := (462886409/500000000 : ℝ)) (σ := (489298901/500000000 : ℝ)) (Ab := (967308313/1000000000 : ℝ))
    (by norm_num) (by norm_num) Rf (by norm_num) (by norm_num)
    (by norm_num; exact pc12.le) (by norm_num) (by norm_num) (by norm_num) (by norm_num)


end HlawkaSchatten.DiagonalRealBundle

/- The proof uses original lpNorm data and previously checked finite certificates. -/
open HlawkaSchatten.DiagonalCutoff16
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalBelow16

theorem localize_w001_s003 (p : ℝ) (hpa : (8171/512 : ℝ) ≤ p) (hpb : p ≤ (2043/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hB : coordinateBox (2249/10000 : ℝ) (63/50 : ℝ) (1537/2500 : ℝ) (63/50 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT1 : 1 ≤ lpNorm p (X 0 + X 1 + X 2))
    (hT : lpNorm p (X 0 + X 1 + X 2) < (62997/50000 : ℝ))
    (hfailure : ((10689/25000 : ℝ)*p) * pairGapSum (lpNorm p) (X 0) (X 1) (X 2) + lpNorm p (X 0 + X 1 + X 2) < 3)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      lpNorm p (X j + X k) ≤ X j i + X k i + (1/25000000 : ℝ)) :
    X ∈ normCappedDomain p (4531/10000 : ℝ) (4837/5000 : ℝ) (197/250 : ℝ) (9/8 : ℝ) (35924473/31250000 : ℝ) (62997/50000 : ℝ) (5773109276513119/3639159125000000 : ℝ) (4174820463940181/727831825000000 : ℝ) := by
  have htotal := barrier_w001_s003 p hpa hpb X hB hS hT1 hfailure htail
  have hg := gap_of_total_lower (by norm_num : (0 : ℝ) < (8171/512 : ℝ)) hpa
    (by norm_num : (0 : ℝ) < (10689/25000 : ℝ)) (pairGapSum_nonneg (by linarith) (X 0) (X 1) (X 2))
    hfailure htotal.le
  have hG : pairGapSum (lpNorm p) (X 0) (X 1) (X 2) < (4804259968/18195795625 : ℝ) := by
    convert hg using 1 <;> norm_num
  have hlo : (957496667/1000000000 : ℝ) ≤ (1/2 : ℝ) ^ (1/(8171/512 : ℝ)) := by
    convert roots_w001_s003.1 using 1 <;> norm_num
  have hhi : (1/2 : ℝ) ^ (1/(2043/128 : ℝ)) ≤ (957501757/1000000000 : ℝ) := by
    convert roots_w001_s003.2.1 using 1 <;> norm_num
  have facts := facts_of (α := (8171/512 : ℝ)) (β := (2043/128 : ℝ))
    (D := (131620869758363/14556636500000000 : ℝ)) (δ := (4721679/1000000000 : ℝ)) (h := (192170486059819/727831825000000 : ℝ))
    (A := (62997/50000 : ℝ)) (g := (4804259968/18195795625 : ℝ)) (eps := (1/25000000 : ℝ))
    (tlo := (957496667/1000000000 : ℝ)) (thib := (957501757/1000000000 : ℝ))
    (by norm_num) hpa hpb (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo hhi
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hB hS hT hG htail
  have hcontract := contract_w001_s003 p hpa hpb X (fun i ↦ lpNorm p (X i))
    (by convert facts using 1 <;> norm_num) (initial_norm_lower (by linarith) X hB)
  have hJ := pair_floor_of_gap (by linarith) X hS hcontract.1 hG htail
  have hW := offsum_floor_of_gap X hS hG htail
  refine ⟨hcontract.2, hcontract.1, hT.le, ?_, ?_⟩
  · intro i j k hij hik hjk
    have h := hJ i j k hij hik hjk
    convert h using 1 <;> norm_num
  · convert hW using 1 <;> norm_num


end HlawkaSchatten.DiagonalBelow16

/- The generic Hessian and averaging proofs are from accepted submission
de577b6b-0253-45ac-9b17-ccf002bb69a6 (Ezzeri Esa, bwdaugherty, Yuxuan Xu;
Apache-2.0). All geometry and finite margins below are checked anew. -/
open HlawkaSchatten.DiagonalCutoff16
set_option autoImplicit false
set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 20000
namespace HlawkaSchatten.DiagonalRealBundle
open HlawkaSchatten.DiagonalConstruction


theorem curvature_w001_s003 (p : ℝ) (hpa : (8171/512 : ℝ) ≤ p) (hpb : p ≤ (2043/128 : ℝ)) :
    p * (15806561823382794364855430326836005688511142578125000/330494131319107745981999577781637525193254883479297 : ℝ) * (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ) ^ (p-2) < 1 ∧
    (64412508456954863591021535081656563872395423511900893012678332787451936507776376836845/2026754431506327542118084680652014067589136371227896616545438945126625346821172678328 : ℝ) * (98718426092086216052/130789790659404710945 : ℝ) ^ (p-2) < 2*(10689/25000 : ℝ)-1/p := by
  have hp0 : 0 < p := by linarith

  have hbTFractionStep0 : (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)^(0 : ℝ) ≤ (1 : ℝ) := by norm_num
  have hbTFractionStep1 : (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)^(1/2 : ℝ) ≤ (97271079205302851364100498991/125000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)) (a := (0 : ℝ)) (A := (1 : ℝ)) (B := (97271079205302851364100498991/125000000000000000000000000000 : ℝ)) 1
      (by norm_num) (by norm_num) hbTFractionStep0 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbTFractionStep2 : (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)^(3/4 : ℝ) ≤ (21451645117254932753829177587/31250000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)) (a := (1/2 : ℝ)) (A := (97271079205302851364100498991/125000000000000000000000000000 : ℝ)) (B := (21451645117254932753829177587/31250000000000000000000000000 : ℝ)) 1
      (by norm_num) (by norm_num) hbTFractionStep1 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbTFractionStep3 : (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)^(3/8 : ℝ) ≤ (414262188641492432829907323473/500000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)) (a := (3/4 : ℝ)) (A := (21451645117254932753829177587/31250000000000000000000000000 : ℝ)) (B := (414262188641492432829907323473/500000000000000000000000000000 : ℝ)) 0
      (by norm_num) (by norm_num) hbTFractionStep2 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbTFractionStep4 : (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)^(11/16 : ℝ) ≤ (177078720581130462372531660009/250000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)) (a := (3/8 : ℝ)) (A := (414262188641492432829907323473/500000000000000000000000000000 : ℝ)) (B := (177078720581130462372531660009/250000000000000000000000000000 : ℝ)) 1
      (by norm_num) (by norm_num) hbTFractionStep3 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbTFractionStep5 : (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)^(11/32 : ℝ) ≤ (841614449926165329911264642337/1000000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)) (a := (11/16 : ℝ)) (A := (177078720581130462372531660009/250000000000000000000000000000 : ℝ)) (B := (841614449926165329911264642337/1000000000000000000000000000000 : ℝ)) 0
      (by norm_num) (by norm_num) hbTFractionStep4 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbTFractionStep6 : (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)^(43/64 : ℝ) ≤ (356944190028440516351185732463/500000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)) (a := (11/32 : ℝ)) (A := (841614449926165329911264642337/1000000000000000000000000000000 : ℝ)) (B := (356944190028440516351185732463/500000000000000000000000000000 : ℝ)) 1
      (by norm_num) (by norm_num) hbTFractionStep5 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbTFractionStep7 : (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)^(107/128 : ℝ) ≤ (164372396277022246577825786557/250000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)) (a := (43/64 : ℝ)) (A := (356944190028440516351185732463/500000000000000000000000000000 : ℝ)) (B := (164372396277022246577825786557/250000000000000000000000000000 : ℝ)) 1
      (by norm_num) (by norm_num) hbTFractionStep6 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbTFractionStep8 : (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)^(235/256 : ℝ) ≤ (630983728805700295859986045759/1000000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)) (a := (107/128 : ℝ)) (A := (164372396277022246577825786557/250000000000000000000000000000 : ℝ)) (B := (630983728805700295859986045759/1000000000000000000000000000000 : ℝ)) 1
      (by norm_num) (by norm_num) hbTFractionStep7 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbTFractionStep9 : (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)^(491/512 : ℝ) ≤ (618134240728812407242422661201/1000000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)) (a := (235/256 : ℝ)) (A := (630983728805700295859986045759/1000000000000000000000000000000 : ℝ)) (B := (618134240728812407242422661201/1000000000000000000000000000000 : ℝ)) 1
      (by norm_num) (by norm_num) hbTFractionStep8 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbTFraction : (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)^(491/512 : ℝ) ≤ (123626848145763/200000000000000 : ℝ) := by linarith only [hbTFractionStep9]
  have hbT : (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ) ^ (7147/512 : ℝ) ≤ (113739043/125000000000 : ℝ) := by
    have hs := rpow_nat_add_upper 13 (by norm_num : (0 : ℝ) < (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ)) hbTFraction
    have he : ((13 : ℕ) : ℝ) + (491/512 : ℝ) = (7147/512 : ℝ) := by norm_num
    rw [he] at hs
    exact hs.trans (by norm_num : (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ) ^ (13 : ℕ) * (123626848145763/200000000000000 : ℝ) ≤ (113739043/125000000000 : ℝ))

  have hrT : (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ) ^ (p-2) ≤ (113739043/125000000000 : ℝ) := by
    exact (Real.rpow_le_rpow_of_exponent_ge' (x := (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : 0 ≤ (7147/512 : ℝ)) (by linarith : (7147/512 : ℝ) ≤ p-2)).trans hbT

  have hbCFractionStep0 : (98718426092086216052/130789790659404710945 : ℝ)^(0 : ℝ) ≤ (1 : ℝ) := by norm_num
  have hbCFractionStep1 : (98718426092086216052/130789790659404710945 : ℝ)^(1/2 : ℝ) ≤ (434392374950173199616598541239/500000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (98718426092086216052/130789790659404710945 : ℝ)) (a := (0 : ℝ)) (A := (1 : ℝ)) (B := (434392374950173199616598541239/500000000000000000000000000000 : ℝ)) 1
      (by norm_num) (by norm_num) hbCFractionStep0 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbCFractionStep2 : (98718426092086216052/130789790659404710945 : ℝ)^(3/4 : ℝ) ≤ (809782306757572743987386522757/1000000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (98718426092086216052/130789790659404710945 : ℝ)) (a := (1/2 : ℝ)) (A := (434392374950173199616598541239/500000000000000000000000000000 : ℝ)) (B := (809782306757572743987386522757/1000000000000000000000000000000 : ℝ)) 1
      (by norm_num) (by norm_num) hbCFractionStep1 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbCFractionStep3 : (98718426092086216052/130789790659404710945 : ℝ)^(3/8 : ℝ) ≤ (112484881397844191018537478343/125000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (98718426092086216052/130789790659404710945 : ℝ)) (a := (3/4 : ℝ)) (A := (809782306757572743987386522757/1000000000000000000000000000000 : ℝ)) (B := (112484881397844191018537478343/125000000000000000000000000000 : ℝ)) 0
      (by norm_num) (by norm_num) hbCFractionStep2 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbCFractionStep4 : (98718426092086216052/130789790659404710945 : ℝ)^(11/16 : ℝ) ≤ (824146198744858563820029691251/1000000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (98718426092086216052/130789790659404710945 : ℝ)) (a := (3/8 : ℝ)) (A := (112484881397844191018537478343/125000000000000000000000000000 : ℝ)) (B := (824146198744858563820029691251/1000000000000000000000000000000 : ℝ)) 1
      (by norm_num) (by norm_num) hbCFractionStep3 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbCFractionStep5 : (98718426092086216052/130789790659404710945 : ℝ)^(11/32 : ℝ) ≤ (907824982441471790002542775301/1000000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (98718426092086216052/130789790659404710945 : ℝ)) (a := (11/16 : ℝ)) (A := (824146198744858563820029691251/1000000000000000000000000000000 : ℝ)) (B := (907824982441471790002542775301/1000000000000000000000000000000 : ℝ)) 0
      (by norm_num) (by norm_num) hbCFractionStep4 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbCFractionStep6 : (98718426092086216052/130789790659404710945 : ℝ)^(43/64 : ℝ) ≤ (827776806910536575980827571981/1000000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (98718426092086216052/130789790659404710945 : ℝ)) (a := (11/32 : ℝ)) (A := (907824982441471790002542775301/1000000000000000000000000000000 : ℝ)) (B := (827776806910536575980827571981/1000000000000000000000000000000 : ℝ)) 1
      (by norm_num) (by norm_num) hbCFractionStep5 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbCFractionStep7 : (98718426092086216052/130789790659404710945 : ℝ)^(107/128 : ℝ) ≤ (790439829755936419732419609867/1000000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (98718426092086216052/130789790659404710945 : ℝ)) (a := (43/64 : ℝ)) (A := (827776806910536575980827571981/1000000000000000000000000000000 : ℝ)) (B := (790439829755936419732419609867/1000000000000000000000000000000 : ℝ)) 1
      (by norm_num) (by norm_num) hbCFractionStep6 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbCFractionStep8 : (98718426092086216052/130789790659404710945 : ℝ)^(235/256 : ℝ) ≤ (193101926075852803368924824187/250000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (98718426092086216052/130789790659404710945 : ℝ)) (a := (107/128 : ℝ)) (A := (790439829755936419732419609867/1000000000000000000000000000000 : ℝ)) (B := (193101926075852803368924824187/250000000000000000000000000000 : ℝ)) 1
      (by norm_num) (by norm_num) hbCFractionStep7 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbCFractionStep9 : (98718426092086216052/130789790659404710945 : ℝ)^(491/512 : ℝ) ≤ (763546494226340924492623188309/1000000000000000000000000000000 : ℝ) := by
    have hstep := HlawkaSchatten.DiagonalBelow16Dyadic.dyadic_step_upper
      (x := (98718426092086216052/130789790659404710945 : ℝ)) (a := (235/256 : ℝ)) (A := (193101926075852803368924824187/250000000000000000000000000000 : ℝ)) (B := (763546494226340924492623188309/1000000000000000000000000000000 : ℝ)) 1
      (by norm_num) (by norm_num) hbCFractionStep8 (by norm_num)
    convert hstep using 1 <;> norm_num
  have hbCFraction : (98718426092086216052/130789790659404710945 : ℝ)^(491/512 : ℝ) ≤ (763546494226343/1000000000000000 : ℝ) := by linarith only [hbCFractionStep9]
  have hbC : (98718426092086216052/130789790659404710945 : ℝ) ^ (7147/512 : ℝ) ≤ (9851954679/500000000000 : ℝ) := by
    have hs := rpow_nat_add_upper 13 (by norm_num : (0 : ℝ) < (98718426092086216052/130789790659404710945 : ℝ)) hbCFraction
    have he : ((13 : ℕ) : ℝ) + (491/512 : ℝ) = (7147/512 : ℝ) := by norm_num
    rw [he] at hs
    exact hs.trans (by norm_num : (98718426092086216052/130789790659404710945 : ℝ) ^ (13 : ℕ) * (763546494226343/1000000000000000 : ℝ) ≤ (9851954679/500000000000 : ℝ))

  have hrC : (98718426092086216052/130789790659404710945 : ℝ) ^ (p-2) ≤ (9851954679/500000000000 : ℝ) := by
    exact (Real.rpow_le_rpow_of_exponent_ge' (x := (98718426092086216052/130789790659404710945 : ℝ))
      (by norm_num) (by norm_num) (by norm_num : 0 ≤ (7147/512 : ℝ)) (by linarith : (7147/512 : ℝ) ≤ p-2)).trans hbC

  constructor
  · have h1 := mul_le_mul_of_nonneg_left hrT (show 0 ≤ p*(15806561823382794364855430326836005688511142578125000/330494131319107745981999577781637525193254883479297 : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hpb (show 0 ≤ (15806561823382794364855430326836005688511142578125000/330494131319107745981999577781637525193254883479297 : ℝ)*((113739043/125000000000 : ℝ)) by norm_num)
    have hend : (2043/128 : ℝ)*(15806561823382794364855430326836005688511142578125000/330494131319107745981999577781637525193254883479297 : ℝ)*((113739043/125000000000 : ℝ)) < 1 := by norm_num
    nlinarith only [h1,h2,hend]
  · have h1 := mul_le_mul_of_nonneg_left hrC (show 0 ≤ (64412508456954863591021535081656563872395423511900893012678332787451936507776376836845/2026754431506327542118084680652014067589136371227896616545438945126625346821172678328 : ℝ) by norm_num)
    have hinv : 1/p ≤ 1/(8171/512 : ℝ) := one_div_le_one_div_of_le (by norm_num) hpa
    have hend : (64412508456954863591021535081656563872395423511900893012678332787451936507776376836845/2026754431506327542118084680652014067589136371227896616545438945126625346821172678328 : ℝ)*((9851954679/500000000000 : ℝ)) < 2*(10689/25000 : ℝ)-1/(8171/512 : ℝ) := by norm_num
    linarith only [h1,hinv,hend]



theorem nonneg_w001_s003 (p : ℝ) (hpa : (8171/512 : ℝ) ≤ p) (hpb : p ≤ (2043/128 : ℝ))
    (hKlo : (10689/25000 : ℝ)*p ≤ cyclicConstant p) (hKhi : cyclicConstant p ≤ p/2)
    (X : Triple) (hX : X ∈ normCappedDomain p (4531/10000 : ℝ) (4837/5000 : ℝ) (197/250 : ℝ) (9/8 : ℝ) (35924473/31250000 : ℝ) (62997/50000 : ℝ) (5773109276513119/3639159125000000 : ℝ) (4174820463940181/727831825000000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by
  let GT : ℝ := pairTotalFactor (4531/10000 : ℝ) (9/8 : ℝ) (2252586738988119/3639159125000000 : ℝ) (62997/50000 : ℝ) (6 : ℝ) (1/4 : ℝ)
  let GC : ℝ := pairColumnFactor (4531/10000 : ℝ) (9/8 : ℝ) (2252586738988119/3639159125000000 : ℝ) (62997/50000 : ℝ) (23597/50000 : ℝ) (5773109276513119/3639159125000000 : ℝ) (6 : ℝ) (1/4 : ℝ)
  have hmarg := curvature_w001_s003 p hpa hpb
  have hNT : (p/2) * GT * ((62997/50000 : ℝ)/(5773109276513119/3639159125000000 : ℝ)) *
      (((23597/50000 : ℝ)*(62997/50000 : ℝ))/((5773109276513119/3639159125000000 : ℝ)*(2252586738988119/3639159125000000 : ℝ))) ^ (p-2) ≤ 1 := by
    have hbase : (((23597/50000 : ℝ)*(62997/50000 : ℝ))/((5773109276513119/3639159125000000 : ℝ)*(2252586738988119/3639159125000000 : ℝ))) = (2624928565907775410663668750000/4334809799667581902538229544387 : ℝ) := by norm_num
    have hconst : GT * ((62997/50000 : ℝ)/(5773109276513119/3639159125000000 : ℝ)) / 2 = (15806561823382794364855430326836005688511142578125000/330494131319107745981999577781637525193254883479297 : ℝ) := by
      norm_num [GT, pairTotalFactor, shapeFactor]
    have hprod : (p/2) * GT * ((62997/50000 : ℝ)/(5773109276513119/3639159125000000 : ℝ)) = p * (15806561823382794364855430326836005688511142578125000/330494131319107745981999577781637525193254883479297 : ℝ) := by
      calc _ = p * (GT * ((62997/50000 : ℝ)/(5773109276513119/3639159125000000 : ℝ)) / 2) := by ring
           _ = _ := by rw [hconst]
    rw [hbase, hprod]
    exact hmarg.1.le
  have hNC : (GC/2) * ((35924473/31250000 : ℝ)/(5773109276513119/3639159125000000 : ℝ)) *
      (((23597/50000 : ℝ)*(35924473/31250000 : ℝ))/((5773109276513119/3639159125000000 : ℝ)*(4531/10000 : ℝ))) ^ (p-2) ≤ 2*(10689/25000 : ℝ)-1/p := by
    have hbase : (((23597/50000 : ℝ)*(35924473/31250000 : ℝ))/((5773109276513119/3639159125000000 : ℝ)*(4531/10000 : ℝ))) = (98718426092086216052/130789790659404710945 : ℝ) := by norm_num
    have hconst : (GC/2) * ((35924473/31250000 : ℝ)/(5773109276513119/3639159125000000 : ℝ)) = (64412508456954863591021535081656563872395423511900893012678332787451936507776376836845/2026754431506327542118084680652014067589136371227896616545438945126625346821172678328 : ℝ) := by
      norm_num [GC, pairColumnFactor, shapeFactor]
    rw [hbase, hconst]
    exact hmarg.2.le
  exact HlawkaSchatten.DiagonalCutoff16.nonnegative_of_curvature_margins
    (p := p) (c := (10689/25000 : ℝ)) (ell := (4531/10000 : ℝ)) (u := (4837/5000 : ℝ)) (v := (197/250 : ℝ)) (w := (9/8 : ℝ)) (U := (35924473/31250000 : ℝ)) (A := (62997/50000 : ℝ)) (J := (5773109276513119/3639159125000000 : ℝ)) (W0 := (4174820463940181/727831825000000 : ℝ)) (m := (4531/10000 : ℝ)) (M := (9/8 : ℝ)) (L := (5773109276513119/3639159125000000 : ℝ)) (s := (2252586738988119/3639159125000000 : ℝ)) (t := (62997/50000 : ℝ)) (eta := (23597/50000 : ℝ)) (eps1 := (6 : ℝ)) (eps2 := (1/4 : ℝ)) (gT := GT) (gC := GC)
    (by linarith) (by nlinarith [hKlo]) hKlo hKhi
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [GT, pairTotalFactor, shapeFactor])
    (by norm_num [GC, pairColumnFactor, shapeFactor])
    hNT hNC X hX.1 hX.2.1 hX.2.2.1 hX.2.2.2.1 hX.2.2.2.2


end HlawkaSchatten.DiagonalRealBundle

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
namespace HlawkaSchatten.DiagonalBelow16

theorem no_failure_w001_s003 (p : ℝ) (hpa : (8171/512 : ℝ) ≤ p) (hpb : p ≤ (2043/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hKlo : (10689/25000 : ℝ)*p ≤ cyclicConstant p) (hKhi : cyclicConstant p ≤ p/2)
    (hB : coordinateBox (2249/10000 : ℝ) (63/50 : ℝ) (1537/2500 : ℝ) (63/50 : ℝ) X)
    (hS : lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3)
    (hT1 : 1 ≤ lpNorm p (X 0 + X 1 + X 2)) (hT : lpNorm p (X 0 + X 1 + X 2) < (62997/50000 : ℝ))
    (hf : ((10689/25000 : ℝ)*p)*pairGapSum (lpNorm p) (X 0) (X 1) (X 2) + lpNorm p (X 0 + X 1 + X 2) < 3)
    (htail : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → lpNorm p (X j + X k) ≤ X j i + X k i + (1/25000000 : ℝ))
    (hneg : tripleDeficit p (cyclicConstant p) X < 0) : False := by
  have hloc := localize_w001_s003 p hpa hpb X hB hS hT1 hT hf htail
  have hn := nonneg_w001_s003 p hpa hpb hKlo hKhi X hloc
  linarith

theorem real_three_w001_s003_003 (p : ℝ) (hpa : (8171/512 : ℝ) ≤ p) (hpb : p ≤ (2043/128 : ℝ)) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro x y z
  by_contra hn
  have hf : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by
    rw [hlawkaDeficit_eq]
    exact sub_neg.mpr (lt_of_not_ge hn)
  obtain ⟨X,hKlo,hKhi,hB,hS,hT1,hT,hfailure,htail,hneg⟩ :=
    coarse_failure_window01 p (by linarith) (by linarith) x y z hf

  exact no_failure_w001_s003 p (by linarith) hpb X hKlo hKhi hB hS hT1 hT hfailure htail hneg

end HlawkaSchatten.DiagonalBelow16


theorem solution :
    ∀ p : ℝ, (8171/512 : ℝ) ≤ p → p ≤ (2043/128 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro p hpa hpb
  exact HlawkaSchatten.DiagonalBelow16.real_three_w001_s003_003 p hpa hpb

#print axioms solution
