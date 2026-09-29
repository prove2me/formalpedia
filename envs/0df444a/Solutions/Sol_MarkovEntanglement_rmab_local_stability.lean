-- Prove2me | solution 1 for MarkovEntanglement.rmab_local_stability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T00:02:57.593392+00:00
-- url     : https://prove2.me/submissions/fab9b9b4-973b-478e-a3bf-68a3055f7ac9

import Mathlib
import Definitions.Def_markov_entanglement_meanfield

open scoped BigOperators
open MarkovEntanglement

namespace ME11

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ### The sup norm on configurations -/
set_option linter.unusedSectionVars false

theorem le_supNorm [Nonempty S] (v : S → ℝ) (z : S) : |v z| ≤ supNorm v :=
  le_ciSup (Finite.bddAbove_range (fun x => |v x|)) z

theorem supNorm_le [Nonempty S] {v : S → ℝ} {c : ℝ} (h : ∀ z, |v z| ≤ c) : supNorm v ≤ c :=
  ciSup_le h

theorem supNorm_nonneg [Nonempty S] (v : S → ℝ) : 0 ≤ supNorm v := by
  obtain ⟨z⟩ := ‹Nonempty S›
  exact le_trans (abs_nonneg _) (le_supNorm v z)

theorem supNorm_eq_zero [Nonempty S] {v : S → ℝ} (h : supNorm v = 0) (z : S) : v z = 0 := by
  have := le_supNorm v z
  rw [h] at this
  exact abs_eq_zero.1 (le_antisymm this (abs_nonneg _))

theorem supNorm_smul [Nonempty S] {c : ℝ} (hc : 0 ≤ c) (v : S → ℝ) :
    supNorm (fun z => c * v z) = c * supNorm v := by
  refine le_antisymm (supNorm_le fun z => ?_) ?_
  · rw [abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (le_supNorm v z) hc
  · rcases eq_or_lt_of_le hc with h | h
    · simp [← h, supNorm_nonneg]
    · rw [← le_div_iff₀' h]
      refine supNorm_le fun z => ?_
      rw [le_div_iff₀' h]
      have he : c * |v z| = |c * v z| := by rw [abs_mul, abs_of_pos h]
      rw [he]
      exact le_supNorm (fun z => c * v z) z

theorem supNorm_sub_le [Nonempty S] (v w : S → ℝ) :
    supNorm (fun z => v z - w z) ≤ supNorm v + supNorm w :=
  supNorm_le fun z => le_trans (abs_sub _ _) (add_le_add (le_supNorm v z) (le_supNorm w z))

/-! ### A crude operator norm for `vecMul` -/

/-- The sum of the absolute values of all entries: a crude but submultiplicative-free bound
for the action of a matrix on row vectors in the sup norm. -/
noncomputable def nrm (A : Matrix S S ℝ) : ℝ := ∑ i, ∑ j, |A i j|

theorem nrm_nonneg (A : Matrix S S ℝ) : 0 ≤ nrm A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem vecMul_apply (v : S → ℝ) (A : Matrix S S ℝ) (j : S) :
    Matrix.vecMul v A j = ∑ i, v i * A i j := rfl

theorem supNorm_vecMul_le [Nonempty S] (v : S → ℝ) (A : Matrix S S ℝ) :
    supNorm (Matrix.vecMul v A) ≤ nrm A * supNorm v := by
  refine supNorm_le fun j => ?_
  rw [vecMul_apply]
  calc |∑ i, v i * A i j| ≤ ∑ i, |v i * A i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, supNorm v * |A i j| := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (le_supNorm v i) (abs_nonneg _)
    _ = supNorm v * ∑ i, |A i j| := by rw [Finset.mul_sum]
    _ ≤ supNorm v * nrm A := by
        refine mul_le_mul_of_nonneg_left ?_ (supNorm_nonneg v)
        unfold nrm
        exact Finset.sum_le_sum fun i _ =>
          Finset.single_le_sum (fun k _ => abs_nonneg (A i k)) (Finset.mem_univ j)
    _ = nrm A * supNorm v := by ring

/-! ### The mean-field map preserves configurations -/

theorem activateFraction_bounds (ν : S → ℝ) (α : ℝ) (m : S → ℝ) (x : S) (hm : 0 ≤ m x) :
    0 ≤ activateFraction ν α m x ∧ activateFraction ν α m x ≤ m x := by
  unfold activateFraction
  exact ⟨le_min hm (le_max_left _ _), min_le_left _ _⟩

theorem meanFieldMap_sum (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0)
    (hP1 : IsTransitionMatrix P1) (ν : S → ℝ) (α : ℝ) (m : S → ℝ) :
    ∑ z, meanFieldMap P0 P1 ν α m z = ∑ x, m x := by
  unfold meanFieldMap
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hP0.2 x, hP1.2 x]
  ring

theorem meanFieldMap_config (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0)
    (hP1 : IsTransitionMatrix P1) (ν : S → ℝ) (α : ℝ) (m : S → ℝ) (hm : IsConfiguration m) :
    IsConfiguration (meanFieldMap P0 P1 ν α m) := by
  refine ⟨fun z => ?_, by rw [meanFieldMap_sum P0 P1 hP0 hP1, hm.2]⟩
  unfold meanFieldMap
  refine Finset.sum_nonneg fun x _ => ?_
  obtain ⟨h1, h2⟩ := activateFraction_bounds ν α m x (hm.1 x)
  exact add_nonneg (mul_nonneg (by linarith) (hP0.1 x z)) (mul_nonneg h1 (hP1.1 x z))

/-! ### The priority region is a neighbourhood of a non-degenerate fixed point -/

set_option linter.unusedSectionVars false

theorem hpm_lip [Nonempty S] (ν : S → ℝ) (m mstar : S → ℝ) (x : S) :
    |higherPriorityMass ν m x - higherPriorityMass ν mstar x|
      ≤ (Fintype.card S : ℝ) * supNorm (fun z => m z - mstar z) := by
  unfold higherPriorityMass
  rw [← Finset.sum_sub_distrib]
  calc |∑ y ∈ Finset.univ.filter fun y => ν x < ν y, (m y - mstar y)|
      ≤ ∑ y ∈ Finset.univ.filter fun y => ν x < ν y, |m y - mstar y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ Finset.univ.filter fun y => ν x < ν y,
          supNorm (fun z => m z - mstar z) :=
        Finset.sum_le_sum fun y _ => le_supNorm (fun z => m z - mstar z) y
    _ ≤ ∑ _y : S, supNorm (fun z => m z - mstar z) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => supNorm_nonneg _)
    _ = (Fintype.card S : ℝ) * supNorm (fun z => m z - mstar z) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem region_of_close [Nonempty S] (ν : S → ℝ) (α : ℝ) (mstar : S → ℝ) (x : S)
    (hx1 : higherPriorityMass ν mstar x < α)
    (hx2 : α < higherPriorityMass ν mstar x + mstar x)
    (m : S → ℝ)
    (hclose : ((Fintype.card S : ℝ) + 1) * supNorm (fun z => m z - mstar z)
        < min (α - higherPriorityMass ν mstar x)
          (higherPriorityMass ν mstar x + mstar x - α)) :
    IsPriorityRegion ν α m x := by
  have hs := supNorm_nonneg (fun z => m z - mstar z)
  have hlip := hpm_lip ν m mstar x
  have hcard : (0:ℝ) ≤ (Fintype.card S : ℝ) := by positivity
  have hxz : |m x - mstar x| ≤ supNorm (fun z => m z - mstar z) :=
    le_supNorm (fun z => m z - mstar z) x
  have h1 : higherPriorityMass ν m x - higherPriorityMass ν mstar x
      ≤ (Fintype.card S : ℝ) * supNorm (fun z => m z - mstar z) :=
    le_trans (le_abs_self _) hlip
  have h2 : higherPriorityMass ν mstar x - higherPriorityMass ν m x
      ≤ (Fintype.card S : ℝ) * supNorm (fun z => m z - mstar z) := by
    have := neg_le_abs (higherPriorityMass ν m x - higherPriorityMass ν mstar x)
    linarith
  have h3 : mstar x - m x ≤ supNorm (fun z => m z - mstar z) := by
    have := neg_le_abs (m x - mstar x)
    linarith
  have hm1 := min_le_left (α - higherPriorityMass ν mstar x)
    (higherPriorityMass ν mstar x + mstar x - α)
  have hm2 := min_le_right (α - higherPriorityMass ν mstar x)
    (higherPriorityMass ν mstar x + mstar x - α)
  constructor
  · nlinarith
  · nlinarith

/-! ### Transport of tangent perturbations by the affine piece -/

theorem affine_step [Nonempty S] (P0 P1 : Matrix S S ℝ) (ν : S → ℝ) (α : ℝ)
    (mstar : S → ℝ) (x : S) (K : Matrix S S ℝ) (b : S → ℝ)
    (hK : ∀ m : S → ℝ, (∀ z, 0 ≤ m z) → IsPriorityRegion ν α m x →
      meanFieldMap P0 P1 ν α m = fun z => (∑ y, m y * K y z) + b z)
    (hmstar0 : ∀ z, 0 ≤ mstar z) (hregstar : IsPriorityRegion ν α mstar x)
    (hfix : meanFieldMap P0 P1 ν α mstar = mstar)
    (w : S → ℝ) (hw0 : ∀ z, 0 ≤ mstar z + w z)
    (hwreg : IsPriorityRegion ν α (fun z => mstar z + w z) x) :
    meanFieldMap P0 P1 ν α (fun z => mstar z + w z)
      = fun z => mstar z + Matrix.vecMul w K z := by
  funext z
  have h2 := congrFun (hK mstar hmstar0 hregstar) z
  rw [hfix] at h2
  simp only [hK _ hw0 hwreg, vecMul_apply]
  have hs : ∑ y, (mstar y + w y) * K y z
      = (∑ y, mstar y * K y z) + ∑ y, w y * K y z := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => add_mul _ _ _
  rw [hs, h2]
  ring

theorem iterate_config (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0)
    (hP1 : IsTransitionMatrix P1) (ν : S → ℝ) (α : ℝ) (m : S → ℝ)
    (hm : IsConfiguration m) (s : ℕ) :
    IsConfiguration (meanFieldIterate (meanFieldMap P0 P1 ν α) s m) := by
  induction s with
  | zero => exact hm
  | succ n ih => exact meanFieldMap_config P0 P1 hP0 hP1 ν α _ ih

theorem affine_iterate [Nonempty S] (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0)
    (hP1 : IsTransitionMatrix P1) (ν : S → ℝ) (α : ℝ)
    (mstar : S → ℝ) (x : S) (K : Matrix S S ℝ) (b : S → ℝ)
    (hK : ∀ m : S → ℝ, (∀ z, 0 ≤ m z) → IsPriorityRegion ν α m x →
      meanFieldMap P0 P1 ν α m = fun z => (∑ y, m y * K y z) + b z)
    (hmstar : IsConfiguration mstar) (hregstar : IsPriorityRegion ν α mstar x)
    (hfix : meanFieldMap P0 P1 ν α mstar = mstar)
    (w : S → ℝ) (hconf : IsConfiguration (fun z => mstar z + w z)) :
    ∀ t : ℕ, (∀ s, s ≤ t → IsPriorityRegion ν α
        (fun z => mstar z + Matrix.vecMul w (K ^ s) z) x) →
      meanFieldIterate (meanFieldMap P0 P1 ν α) t (fun z => mstar z + w z)
        = fun z => mstar z + Matrix.vecMul w (K ^ t) z := by
  intro t
  induction t with
  | zero =>
    intro _
    simp [meanFieldIterate]
  | succ n ih =>
    intro hreg
    have hn := ih (fun s hs => hreg s (Nat.le_succ_of_le hs))
    have hcfg : IsConfiguration (fun z => mstar z + Matrix.vecMul w (K ^ n) z) := by
      have := iterate_config P0 P1 hP0 hP1 ν α _ hconf n
      rwa [hn] at this
    show meanFieldMap P0 P1 ν α
      (meanFieldIterate (meanFieldMap P0 P1 ν α) n (fun z => mstar z + w z)) = _
    rw [hn, affine_step P0 P1 ν α mstar x K b hK hmstar.1 hregstar hfix
      (Matrix.vecMul w (K ^ n)) hcfg.1 (hreg n (Nat.le_succ n))]
    funext z
    rw [pow_succ, ← Matrix.vecMul_vecMul]

/-! ### Uniform control of the first few powers, and the running maximum -/

/-- A crude uniform bound on the action of the first `T+1` powers of `K`. -/
noncomputable def Gbd (K : Matrix S S ℝ) (T : ℕ) : ℝ := ∑ s ∈ Finset.range (T + 1), nrm (K ^ s)

theorem Gbd_nonneg (K : Matrix S S ℝ) (T : ℕ) : 0 ≤ Gbd K T :=
  Finset.sum_nonneg fun s _ => nrm_nonneg _

theorem nrm_pow_le_Gbd (K : Matrix S S ℝ) {T s : ℕ} (hs : s ≤ T) : nrm (K ^ s) ≤ Gbd K T :=
  Finset.single_le_sum (f := fun r => nrm (K ^ r)) (fun r _ => nrm_nonneg (K ^ r))
    (Finset.mem_range.2 (Nat.lt_succ_of_le hs))

theorem supNorm_vecMul_pow_le [Nonempty S] (K : Matrix S S ℝ) (v : S → ℝ) {T s : ℕ}
    (hs : s ≤ T) : supNorm (Matrix.vecMul v (K ^ s)) ≤ Gbd K T * supNorm v :=
  le_trans (supNorm_vecMul_le v (K ^ s))
    (mul_le_mul_of_nonneg_right (nrm_pow_le_Gbd K hs) (supNorm_nonneg v))

/-- The largest sup norm attained by the first `t + 1` iterates of a tangent vector. -/
noncomputable def Mmax [Nonempty S] (K : Matrix S S ℝ) (w : S → ℝ) (t : ℕ) : ℝ :=
  (Finset.range (t + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos t)⟩
    (fun s => supNorm (Matrix.vecMul w (K ^ s)))

theorem le_Mmax [Nonempty S] (K : Matrix S S ℝ) (w : S → ℝ) {t s : ℕ} (hs : s ≤ t) :
    supNorm (Matrix.vecMul w (K ^ s)) ≤ Mmax K w t :=
  Finset.le_sup' (fun r => supNorm (Matrix.vecMul w (K ^ r)))
    (Finset.mem_range.2 (Nat.lt_succ_of_le hs))

theorem Mmax_le [Nonempty S] (K : Matrix S S ℝ) (w : S → ℝ) {t : ℕ} {c : ℝ}
    (h : ∀ s, s ≤ t → supNorm (Matrix.vecMul w (K ^ s)) ≤ c) : Mmax K w t ≤ c :=
  Finset.sup'_le _ _ fun s hs => h s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs))

theorem Mmax_nonneg [Nonempty S] (K : Matrix S S ℝ) (w : S → ℝ) (t : ℕ) : 0 ≤ Mmax K w t :=
  le_trans (supNorm_nonneg _) (le_Mmax K w (Nat.zero_le t))

theorem Mmax_mono [Nonempty S] (K : Matrix S S ℝ) (w : S → ℝ) {t t' : ℕ} (h : t ≤ t') :
    Mmax K w t ≤ Mmax K w t' :=
  Mmax_le K w fun s hs => le_Mmax K w (le_trans hs h)

theorem Mmax_le_Gbd [Nonempty S] (K : Matrix S S ℝ) (w : S → ℝ) (t : ℕ) :
    Mmax K w t ≤ Gbd K t * supNorm w :=
  Mmax_le K w fun s hs => supNorm_vecMul_pow_le K w hs

theorem Mmax_succ_of_le [Nonempty S] (K : Matrix S S ℝ) (w : S → ℝ) {t : ℕ}
    (h : supNorm (Matrix.vecMul w (K ^ (t + 1))) ≤ Mmax K w t) :
    Mmax K w (t + 1) = Mmax K w t := by
  refine le_antisymm (Mmax_le K w fun s hs => ?_) (Mmax_mono K w (Nat.le_succ t))
  rcases Nat.lt_or_ge s (t + 1) with hlt | hge
  · exact le_Mmax K w (Nat.lt_succ_iff.1 hlt)
  · rw [le_antisymm hs hge]
    exact h

/-! ### The realisable cone at the fixed point -/

/-- A tangent direction that is strictly positive on the zero set of `mstar`. -/
theorem exists_cone_dir (mstar : S → ℝ) (hmstar : IsConfiguration mstar) :
    ∃ u : S → ℝ, (∑ z, u z = 0) ∧ ∀ z, mstar z = 0 → 1 ≤ u z := by
  classical
  obtain ⟨z₀, -, hz₀⟩ : ∃ z ∈ (Finset.univ : Finset S), mstar z ≠ 0 := by
    by_contra h
    push_neg at h
    have := hmstar.2
    rw [Finset.sum_congr rfl (fun z hz => h z hz)] at this
    simp at this
  refine ⟨fun z => (if mstar z = 0 then (1 : ℝ) else 0)
      - (if z = z₀ then (((Finset.univ.filter fun y : S => mstar y = 0)).card : ℝ) else 0),
    ?_, ?_⟩
  · rw [Finset.sum_sub_distrib]
    simp [Finset.sum_boole]
  · intro z hz
    have hne : z ≠ z₀ := by rintro rfl; exact hz₀ hz
    simp only [if_pos hz, if_neg hne]
    norm_num

/-- Every tangent vector splits into two tangent vectors that are nonnegative on the zero set
of `mstar`, with norms controlled by the original. -/
theorem cone_split [Nonempty S] (mstar u : S → ℝ)
    (hu0 : ∑ z, u z = 0) (hu1 : ∀ z, mstar z = 0 → 1 ≤ u z)
    (v : S → ℝ) (hv : ∑ z, v z = 0) :
    ∃ w1 w2 : S → ℝ,
      (∑ z, w1 z = 0) ∧ (∀ z, mstar z = 0 → 0 ≤ w1 z) ∧
      (∑ z, w2 z = 0) ∧ (∀ z, mstar z = 0 → 0 ≤ w2 z) ∧
      (∀ z, v z = w1 z - w2 z) ∧
      supNorm w1 ≤ (1 + supNorm u) * supNorm v ∧
      supNorm w2 ≤ supNorm u * supNorm v := by
  have hσ := supNorm_nonneg v
  have hU := supNorm_nonneg u
  refine ⟨fun z => v z + supNorm v * u z, fun z => supNorm v * u z, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hu0, hv]
    ring
  · intro z hz
    have h1 : 1 ≤ u z := hu1 z hz
    have h2 : |v z| ≤ supNorm v := le_supNorm v z
    have h3 := abs_le.1 h2
    nlinarith
  · rw [← Finset.mul_sum, hu0]
    ring
  · intro z hz
    exact mul_nonneg hσ (le_trans zero_le_one (hu1 z hz))
  · intro z; ring
  · have h : supNorm (fun z => v z + supNorm v * u z) ≤ supNorm v + supNorm v * supNorm u := by
      refine supNorm_le fun z => ?_
      calc |v z + supNorm v * u z| ≤ |v z| + |supNorm v * u z| := abs_add_le _ _
        _ ≤ supNorm v + supNorm v * supNorm u := by
            refine add_le_add (le_supNorm v z) ?_
            rw [abs_mul, abs_of_nonneg hσ]
            exact mul_le_mul_of_nonneg_left (le_supNorm u z) hσ
    calc supNorm (fun z => v z + supNorm v * u z)
        ≤ supNorm v + supNorm v * supNorm u := h
      _ = (1 + supNorm u) * supNorm v := by ring
  · rw [supNorm_smul hσ]
    exact le_of_eq (mul_comm _ _)

/-! ### The linearisation at a non-degenerate attracting fixed point is stable -/

theorem stable_of_ugap [Nonempty S] (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0)
    (hP1 : IsTransitionMatrix P1) (ν : S → ℝ) (α : ℝ)
    (mstar : S → ℝ) (hmstar : IsConfiguration mstar)
    (hfix : meanFieldMap P0 P1 ν α mstar = mstar)
    (hattr : ∀ ε > 0, ∃ T : ℕ, ∀ t ≥ T, ∀ m : S → ℝ, IsConfiguration m →
      supNorm (fun z => meanFieldIterate (meanFieldMap P0 P1 ν α) t m z - mstar z) < ε)
    (x : S) (hx1 : higherPriorityMass ν mstar x < α)
    (hx2 : α < higherPriorityMass ν mstar x + mstar x)
    (K : Matrix S S ℝ) (b : S → ℝ)
    (hK : ∀ m : S → ℝ, (∀ z, 0 ≤ m z) → IsPriorityRegion ν α m x →
      meanFieldMap P0 P1 ν α m = fun z => (∑ y, m y * K y z) + b z) :
    IsStableOnTangent K := by
  classical
  have hregstar : IsPriorityRegion ν α mstar x := ⟨le_of_lt hx1, hx2⟩
  -- a radius inside which every point lies in the priority region of `x`
  obtain ⟨ε₀, hε₀pos, hε₀⟩ : ∃ e : ℝ, 0 < e ∧ ∀ m : S → ℝ,
      supNorm (fun z => m z - mstar z) ≤ e → IsPriorityRegion ν α m x := by
    obtain ⟨q, hq, hq1, hq2⟩ : ∃ q : ℝ, 0 < q ∧ q ≤ α - higherPriorityMass ν mstar x ∧
        q ≤ higherPriorityMass ν mstar x + mstar x - α :=
      ⟨min (α - higherPriorityMass ν mstar x) (higherPriorityMass ν mstar x + mstar x - α),
        lt_min (by linarith) (by linarith), min_le_left _ _, min_le_right _ _⟩
    have hc : (0:ℝ) < (Fintype.card S : ℝ) + 1 := by positivity
    refine ⟨q / (2 * ((Fintype.card S : ℝ) + 1)), by positivity, fun m hm => ?_⟩
    refine region_of_close ν α mstar x hx1 hx2 m ?_
    have hb : ((Fintype.card S : ℝ) + 1) * supNorm (fun z => m z - mstar z)
        ≤ ((Fintype.card S : ℝ) + 1) * (q / (2 * ((Fintype.card S : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hm (le_of_lt hc)
    have he : ((Fintype.card S : ℝ) + 1) * (q / (2 * ((Fintype.card S : ℝ) + 1))) = q / 2 := by
      field_simp
    rw [he] at hb
    have hlt : q / 2 < min (α - higherPriorityMass ν mstar x)
        (higherPriorityMass ν mstar x + mstar x - α) := lt_min (by linarith) (by linarith)
    linarith
  -- a radius inside which every tangent perturbation keeps the point nonnegative
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ : ∃ d : ℝ, 0 < d ∧ ∀ z : S, mstar z ≠ 0 → d ≤ mstar z := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty (fun z => if mstar z = 0 then 1 else mstar z),
      ?_, fun z hz => ?_⟩
    · refine (Finset.lt_inf'_iff _).2 fun z _ => ?_
      by_cases h : mstar z = 0
      · simp [h]
      · simp only [if_neg h]
        exact lt_of_le_of_ne (hmstar.1 z) (Ne.symm h)
    · have := Finset.inf'_le (f := fun z : S => if mstar z = 0 then 1 else mstar z)
        (Finset.mem_univ z)
      simp only [if_neg hz] at this
      exact this
  obtain ⟨ε₁, hε₁pos, hε₁ε₀, hε₁δ₀⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ ε₀ ∧ e ≤ δ₀ :=
    ⟨min ε₀ δ₀, lt_min hε₀pos hδ₀pos, min_le_left _ _, min_le_right _ _⟩
  -- perturbations of size at most `ε₁` give configurations inside the region
  have hconf_of : ∀ w : S → ℝ, (∑ z, w z = 0) → (∀ z, mstar z = 0 → 0 ≤ w z) →
      supNorm w ≤ ε₁ → IsConfiguration (fun z => mstar z + w z) := by
    intro w hw0 hwZ hwn
    constructor
    · intro z
      show 0 ≤ mstar z + w z
      by_cases h : mstar z = 0
      · have := hwZ z h
        rw [h]
        linarith
      · have h1 : δ₀ ≤ mstar z := hδ₀ z h
        have h2 : |w z| ≤ ε₁ := le_trans (le_supNorm w z) hwn
        have h3 := abs_le.1 h2
        linarith [h3.1]
    · rw [Finset.sum_add_distrib, hmstar.2, hw0]
      ring
  have hreg_of : ∀ w : S → ℝ, supNorm w ≤ ε₁ →
      IsPriorityRegion ν α (fun z => mstar z + w z) x := by
    intro w hw
    refine hε₀ _ ?_
    have he : (fun z => (mstar z + w z) - mstar z) = w := by funext z; ring
    rw [he]
    linarith
  -- the rows of `K` sum to one, so the tangent space is invariant
  have hrow : ∀ y : S, ∑ z, K y z = 1 := by
    intro y
    set w : S → ℝ := fun z => if z = y then ε₁ else 0 with hwdef
    have hwn : supNorm w ≤ ε₁ := by
      refine supNorm_le fun z => ?_
      by_cases h : z = y
      · simp [hwdef, h, abs_of_pos hε₁pos]
      · simp [hwdef, h, le_of_lt hε₁pos]
    have hw0 : ∀ z, 0 ≤ mstar z + w z := by
      intro z
      have h : 0 ≤ w z := by
        by_cases hzy : z = y
        · simp [hwdef, hzy, le_of_lt hε₁pos]
        · simp [hwdef, hzy]
      linarith [hmstar.1 z]
    have hwreg := hreg_of w hwn
    have hsum1 : ∑ z, meanFieldMap P0 P1 ν α (fun z' => mstar z' + w z') z
        = ∑ y', (mstar y' + w y') := meanFieldMap_sum P0 P1 hP0 hP1 ν α _
    have hsum2 : ∑ z, meanFieldMap P0 P1 ν α mstar z = ∑ y', mstar y' :=
      meanFieldMap_sum P0 P1 hP0 hP1 ν α _
    have hA : ∑ y', (mstar y' + w y')
        = (∑ y', (mstar y' + w y') * (∑ z, K y' z)) + ∑ z, b z := by
      rw [← hsum1]
      simp only [hK _ hw0 hwreg]
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl fun y' _ => by rw [← Finset.mul_sum]
    have hB : ∑ y', mstar y' = (∑ y', mstar y' * (∑ z, K y' z)) + ∑ z, b z := by
      rw [← hsum2]
      simp only [hK mstar hmstar.1 hregstar]
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      congr 1
      exact Finset.sum_congr rfl fun y' _ => by rw [← Finset.mul_sum]
    have e : ∑ y', (mstar y' + w y') * (∑ z, K y' z)
        = (∑ y', mstar y' * (∑ z, K y' z)) + ∑ y', w y' * (∑ z, K y' z) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y' _ => add_mul _ _ _
    have e2 : ∑ y', (mstar y' + w y') = (∑ y', mstar y') + ∑ y', w y' :=
      Finset.sum_add_distrib
    rw [e, e2] at hA
    have hC : ∑ y', w y' * (∑ z, K y' z) = ∑ y', w y' := by linarith
    have hw1 : ∑ y', w y' * (∑ z, K y' z) = ε₁ * (∑ z, K y z) := by
      simp [hwdef, Finset.sum_ite_eq']
    have hw2 : ∑ y' : S, w y' = ε₁ := by simp [hwdef]
    rw [hw1, hw2] at hC
    have := mul_left_cancel₀ (ne_of_gt hε₁pos) (by rw [hC]; ring :
      ε₁ * (∑ z, K y z) = ε₁ * 1)
    simpa using this
  have hinv : ∀ v : S → ℝ, (∑ z, v z = 0) → ∑ z, Matrix.vecMul v K z = 0 := by
    intro v hv
    simp only [vecMul_apply]
    rw [Finset.sum_comm]
    calc ∑ y, ∑ z, v y * K y z = ∑ y, v y * (∑ z, K y z) :=
          Finset.sum_congr rfl fun y _ => by rw [← Finset.mul_sum]
      _ = ∑ y, v y := Finset.sum_congr rfl fun y _ => by rw [hrow y, mul_one]
      _ = 0 := hv
  have hinvpow : ∀ v : S → ℝ, (∑ z, v z = 0) → ∀ s : ℕ,
      ∑ z, Matrix.vecMul v (K ^ s) z = 0 := by
    intro v hv s
    induction s with
    | zero => simpa using hv
    | succ n ih =>
      have he : Matrix.vecMul v (K ^ (n + 1)) = Matrix.vecMul (Matrix.vecMul v (K ^ n)) K := by
        rw [pow_succ, ← Matrix.vecMul_vecMul]
      rw [he]
      exact hinv _ ih
  -- the key scaling estimate
  have main : ∀ η : ℝ, 0 < η → ∃ T : ℕ, ∀ w : S → ℝ, (∑ z, w z = 0) →
      (∀ z, mstar z = 0 → 0 ≤ w z) → ∀ t, T ≤ t →
        supNorm (Matrix.vecMul w (K ^ t)) ≤ η * Mmax K w t := by
    intro η hη
    obtain ⟨T, hT⟩ := hattr (η * ε₁) (by positivity)
    refine ⟨T, fun w hw0 hwZ t ht => ?_⟩
    rcases eq_or_lt_of_le (Mmax_nonneg K w t) with hM | hM
    · have h1 : supNorm (Matrix.vecMul w (K ^ t)) ≤ Mmax K w t := le_Mmax K w le_rfl
      rw [← hM] at h1 ⊢
      have := supNorm_nonneg (Matrix.vecMul w (K ^ t))
      nlinarith
    · set c : ℝ := ε₁ / Mmax K w t with hcdef
      have hcpos : 0 < c := div_pos hε₁pos hM
      set w' : S → ℝ := fun z => c * w z with hw'def
      have hvm : ∀ A : Matrix S S ℝ,
          Matrix.vecMul w' A = fun z => c * Matrix.vecMul w A z := by
        intro A
        funext z
        simp only [vecMul_apply, hw'def, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hn' : ∀ s : ℕ, supNorm (Matrix.vecMul w' (K ^ s))
          = c * supNorm (Matrix.vecMul w (K ^ s)) := by
        intro s
        rw [hvm, supNorm_smul (le_of_lt hcpos)]
      have hsmall : ∀ s, s ≤ t → supNorm (Matrix.vecMul w' (K ^ s)) ≤ ε₁ := by
        intro s hs
        rw [hn' s]
        calc c * supNorm (Matrix.vecMul w (K ^ s)) ≤ c * Mmax K w t :=
              mul_le_mul_of_nonneg_left (le_Mmax K w hs) (le_of_lt hcpos)
          _ = ε₁ := by rw [hcdef]; field_simp
      have hw'0 : ∑ z, w' z = 0 := by
        simp only [hw'def, ← Finset.mul_sum, hw0, mul_zero]
      have hw'Z : ∀ z, mstar z = 0 → 0 ≤ w' z := fun z hz =>
        mul_nonneg (le_of_lt hcpos) (hwZ z hz)
      have hw'n : supNorm w' ≤ ε₁ := by
        have h0 := hsmall 0 (Nat.zero_le t)
        simpa using h0
      have hconf := hconf_of w' hw'0 hw'Z hw'n
      have hreg : ∀ s, s ≤ t → IsPriorityRegion ν α
          (fun z => mstar z + Matrix.vecMul w' (K ^ s) z) x :=
        fun s hs => hreg_of _ (hsmall s hs)
      have hiter := affine_iterate P0 P1 hP0 hP1 ν α mstar x K b hK hmstar hregstar hfix
        w' hconf t hreg
      have hU := hT t ht (fun z => mstar z + w' z) hconf
      rw [hiter] at hU
      have he : (fun z => (mstar z + Matrix.vecMul w' (K ^ t) z) - mstar z)
          = Matrix.vecMul w' (K ^ t) := by funext z; ring
      rw [he, hn' t, hcdef] at hU
      have h3 := mul_lt_mul_of_pos_right hU hM
      have h4 : ε₁ / Mmax K w t * supNorm (Matrix.vecMul w (K ^ t)) * Mmax K w t
          = ε₁ * supNorm (Matrix.vecMul w (K ^ t)) := by field_simp
      rw [h4] at h3
      have h5 : ε₁ * supNorm (Matrix.vecMul w (K ^ t)) < ε₁ * (η * Mmax K w t) := by
        calc ε₁ * supNorm (Matrix.vecMul w (K ^ t)) < η * ε₁ * Mmax K w t := h3
          _ = ε₁ * (η * Mmax K w t) := by ring
      exact le_of_lt (lt_of_mul_lt_mul_left h5 (le_of_lt hε₁pos))
  -- boundedness of the orbit on the realisable cone
  obtain ⟨T₁, hT₁⟩ := main (1/2) (by norm_num)
  have hbdd : ∀ w : S → ℝ, (∑ z, w z = 0) → (∀ z, mstar z = 0 → 0 ≤ w z) →
      ∀ t, Mmax K w t ≤ Mmax K w T₁ := by
    intro w hw0 hwZ
    have hstab : ∀ t, T₁ ≤ t → Mmax K w t = Mmax K w T₁ := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => rfl
      | succ n hn ih =>
        have h1 : supNorm (Matrix.vecMul w (K ^ (n + 1))) ≤ (1/2) * Mmax K w (n + 1) :=
          hT₁ w hw0 hwZ (n + 1) (le_trans hn (Nat.le_succ n))
        have h2 : supNorm (Matrix.vecMul w (K ^ (n + 1))) ≤ Mmax K w n := by
          by_contra hcon
          push_neg at hcon
          have h3 : Mmax K w (n + 1) = supNorm (Matrix.vecMul w (K ^ (n + 1))) := by
            refine le_antisymm (Mmax_le K w fun s hs => ?_) (le_Mmax K w le_rfl)
            rcases Nat.lt_or_ge s (n + 1) with hlt | hge
            · exact le_trans (le_Mmax K w (Nat.lt_succ_iff.1 hlt)) (le_of_lt hcon)
            · rw [le_antisymm hs hge]
          rw [h3] at h1
          have hnn := supNorm_nonneg (Matrix.vecMul w (K ^ (n + 1)))
          have hz : supNorm (Matrix.vecMul w (K ^ (n + 1))) = 0 := by linarith
          rw [hz] at hcon
          linarith [Mmax_nonneg K w n]
        rw [Mmax_succ_of_le K w h2, ih]
    intro t
    rcases Nat.lt_or_ge t T₁ with h | h
    · exact Mmax_mono K w (le_of_lt h)
    · rw [hstab t h]
  have hA₀nn : (0:ℝ) ≤ Gbd K T₁ := Gbd_nonneg K T₁
  have hbound : ∀ w : S → ℝ, (∑ z, w z = 0) → (∀ z, mstar z = 0 → 0 ≤ w z) →
      ∀ t, Mmax K w t ≤ Gbd K T₁ * supNorm w := fun w h1 h2 t =>
    le_trans (hbdd w h1 h2 t) (Mmax_le_Gbd K w T₁)
  -- pass from the cone to the whole tangent space and extract a contraction
  obtain ⟨u, hu0, hu1⟩ := exists_cone_dir mstar hmstar
  have hUnn : (0:ℝ) ≤ supNorm u := supNorm_nonneg u
  obtain ⟨D, hDpos, hD⟩ : ∃ D : ℝ, 0 < D ∧ Gbd K T₁ * (1 + 2 * supNorm u) ≤ D :=
    ⟨Gbd K T₁ * (1 + 2 * supNorm u) + 1, by positivity, by linarith⟩
  obtain ⟨T', hT'⟩ := main (1 / (2 * D)) (by positivity)
  obtain ⟨T2, hT2pos, hT2ge⟩ : ∃ T2 : ℕ, 0 < T2 ∧ T' ≤ T2 :=
    ⟨max T' 1, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), le_max_left _ _⟩
  have hcontr : ∀ v : S → ℝ, (∑ z, v z = 0) →
      supNorm (Matrix.vecMul v (K ^ T2)) ≤ (1/2) * supNorm v := by
    intro v hv
    obtain ⟨w1, w2, hw10, hw1Z, hw20, hw2Z, hsplit, hn1, hn2⟩ :=
      cone_split mstar u hu0 hu1 v hv
    have hfun : Matrix.vecMul v (K ^ T2)
        = fun z => Matrix.vecMul w1 (K ^ T2) z - Matrix.vecMul w2 (K ^ T2) z := by
      funext z
      simp only [vecMul_apply]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hsplit i]; ring
    rw [hfun]
    have htri := supNorm_sub_le (Matrix.vecMul w1 (K ^ T2)) (Matrix.vecMul w2 (K ^ T2))
    have e1 := hT' w1 hw10 hw1Z T2 hT2ge
    have e2 := hT' w2 hw20 hw2Z T2 hT2ge
    have b1 := hbound w1 hw10 hw1Z T2
    have b2 := hbound w2 hw20 hw2Z T2
    have hσ := supNorm_nonneg v
    have hs2 : supNorm w1 + supNorm w2 ≤ (1 + 2 * supNorm u) * supNorm v := by
      have hr : (1 + supNorm u) * supNorm v + supNorm u * supNorm v
          = (1 + 2 * supNorm u) * supNorm v := by ring
      linarith
    have hstep : supNorm (Matrix.vecMul w1 (K ^ T2)) + supNorm (Matrix.vecMul w2 (K ^ T2))
        ≤ (1 / (2 * D)) * (Gbd K T₁ * (supNorm w1 + supNorm w2)) := by
      have hA : Mmax K w1 T2 + Mmax K w2 T2 ≤ Gbd K T₁ * (supNorm w1 + supNorm w2) := by
        have hr : Gbd K T₁ * supNorm w1 + Gbd K T₁ * supNorm w2
            = Gbd K T₁ * (supNorm w1 + supNorm w2) := by ring
        linarith
      calc supNorm (Matrix.vecMul w1 (K ^ T2)) + supNorm (Matrix.vecMul w2 (K ^ T2))
          ≤ (1 / (2 * D)) * Mmax K w1 T2 + (1 / (2 * D)) * Mmax K w2 T2 := add_le_add e1 e2
        _ = (1 / (2 * D)) * (Mmax K w1 T2 + Mmax K w2 T2) := by ring
        _ ≤ (1 / (2 * D)) * (Gbd K T₁ * (supNorm w1 + supNorm w2)) :=
            mul_le_mul_of_nonneg_left hA (by positivity)
    have hfin : (1 / (2 * D)) * (Gbd K T₁ * (supNorm w1 + supNorm w2)) ≤ (1/2) * supNorm v := by
      have t1 : Gbd K T₁ * (supNorm w1 + supNorm w2)
          ≤ Gbd K T₁ * ((1 + 2 * supNorm u) * supNorm v) :=
        mul_le_mul_of_nonneg_left hs2 hA₀nn
      have t2 : Gbd K T₁ * ((1 + 2 * supNorm u) * supNorm v)
          = (Gbd K T₁ * (1 + 2 * supNorm u)) * supNorm v := by ring
      have t3 : (Gbd K T₁ * (1 + 2 * supNorm u)) * supNorm v ≤ D * supNorm v :=
        mul_le_mul_of_nonneg_right hD hσ
      have t4 : (1 / (2 * D)) * (D * supNorm v) = (1/2) * supNorm v := by
        field_simp
      calc (1 / (2 * D)) * (Gbd K T₁ * (supNorm w1 + supNorm w2))
          ≤ (1 / (2 * D)) * (D * supNorm v) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            linarith
        _ = (1/2) * supNorm v := t4
    linarith
  -- iterate the contraction
  have hpowk : ∀ v : S → ℝ, (∑ z, v z = 0) → ∀ k : ℕ,
      supNorm (Matrix.vecMul v (K ^ (k * T2))) ≤ (1/2) ^ k * supNorm v := by
    intro v hv k
    induction k with
    | zero => simp
    | succ n ih =>
      have hz : ∑ z, Matrix.vecMul v (K ^ (n * T2)) z = 0 := hinvpow v hv _
      have he : (n + 1) * T2 = n * T2 + T2 := by ring
      have hvm : Matrix.vecMul v (K ^ ((n + 1) * T2))
          = Matrix.vecMul (Matrix.vecMul v (K ^ (n * T2))) (K ^ T2) := by
        rw [he, pow_add, ← Matrix.vecMul_vecMul]
      rw [hvm]
      calc supNorm (Matrix.vecMul (Matrix.vecMul v (K ^ (n * T2))) (K ^ T2))
          ≤ (1/2) * supNorm (Matrix.vecMul v (K ^ (n * T2))) := hcontr _ hz
        _ ≤ (1/2) * ((1/2) ^ n * supNorm v) := by linarith
        _ = (1/2) ^ (n + 1) * supNorm v := by ring
  -- the geometric rate
  have hT2R : (1:ℝ) ≤ (T2 : ℝ) := by exact_mod_cast hT2pos
  set ρ : ℝ := 1 - 1 / (2 * (T2 : ℝ)) with hρdef
  have hT2pos' : (0:ℝ) < 2 * (T2 : ℝ) := by linarith
  have hsmallinv : 1 / (2 * (T2 : ℝ)) ≤ 1/2 := by
    rw [div_le_div_iff₀ hT2pos' (by norm_num : (0:ℝ) < 2)]
    linarith
  have hρnn : (0:ℝ) ≤ ρ := by rw [hρdef]; linarith
  have hρlt : ρ < 1 := by
    rw [hρdef]
    have : 0 < 1 / (2 * (T2 : ℝ)) := by positivity
    linarith
  have hρle1 : ρ ≤ 1 := le_of_lt hρlt
  have hbern : (1:ℝ)/2 ≤ ρ ^ T2 := by
    have hb := one_add_mul_le_pow (a := -(1 / (2 * (T2 : ℝ)))) (by linarith) T2
    have he : (1 : ℝ) + (T2 : ℝ) * (-(1 / (2 * (T2 : ℝ)))) = 1/2 := by
      field_simp
      norm_num
    have he2 : (1 : ℝ) + -(1 / (2 * (T2 : ℝ))) = ρ := by rw [hρdef]; ring
    rw [he2] at hb
    linarith [hb, he.symm.le, he.le]
  refine ⟨2 * Gbd K T2, ρ, by linarith [Gbd_nonneg K T2], hρnn, hρlt, fun v hv t => ?_⟩
  obtain ⟨k, s, hks, hsl⟩ : ∃ k s : ℕ, k * T2 + s = t ∧ s < T2 :=
    ⟨t / T2, t % T2, by rw [Nat.mul_comm]; exact Nat.div_add_mod t T2, Nat.mod_lt t hT2pos⟩
  have hdecomp : Matrix.vecMul v (K ^ t)
      = Matrix.vecMul (Matrix.vecMul v (K ^ (k * T2))) (K ^ s) := by
    rw [Matrix.vecMul_vecMul, ← pow_add, hks]
  have hρs : (1:ℝ)/2 ≤ ρ ^ s :=
    le_trans hbern (pow_le_pow_of_le_one hρnn hρle1 (le_of_lt hsl))
  have hkey : (1/2 : ℝ) ^ k ≤ 2 * ρ ^ t := by
    have h1 : (1/2 : ℝ) ^ k ≤ (ρ ^ T2) ^ k := pow_le_pow_left₀ (by norm_num) hbern k
    have h2 : (ρ ^ T2) ^ k = ρ ^ (k * T2) := by rw [← pow_mul, Nat.mul_comm]
    have h3 : ρ ^ (k * T2) * ρ ^ s = ρ ^ t := by rw [← pow_add, hks]
    have h4 : (0:ℝ) ≤ ρ ^ (k * T2) := by positivity
    nlinarith [h1, h3, hρs, h4]
  rw [hdecomp]
  have hσ := supNorm_nonneg v
  calc supNorm (Matrix.vecMul (Matrix.vecMul v (K ^ (k * T2))) (K ^ s))
      ≤ Gbd K T2 * supNorm (Matrix.vecMul v (K ^ (k * T2))) :=
        supNorm_vecMul_pow_le K _ (le_of_lt hsl)
    _ ≤ Gbd K T2 * ((1/2) ^ k * supNorm v) :=
        mul_le_mul_of_nonneg_left (hpowk v hv k) (Gbd_nonneg K T2)
    _ ≤ Gbd K T2 * ((2 * ρ ^ t) * supNorm v) := by
        refine mul_le_mul_of_nonneg_left ?_ (Gbd_nonneg K T2)
        exact mul_le_mul_of_nonneg_right hkey hσ
    _ = 2 * Gbd K T2 * ρ ^ t * supNorm v := by ring

end ME11

open MarkovEntanglement ME11 in
theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (hν : Function.Injective ν) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (mstar : S → ℝ) (hmstar : IsConfiguration mstar)
    (hUGAP : IsUniformGlobalAttractor (meanFieldMap P0 P1 ν α) mstar)
    (x : S) (hx : 0 < mstar x ∧ 0 < α - higherPriorityMass ν mstar x ∧
      α - higherPriorityMass ν mstar x < mstar x)
    (K : Matrix S S ℝ) (b : S → ℝ)
    (hK : ∀ m : S → ℝ, (∀ z, 0 ≤ m z) → IsPriorityRegion ν α m x →
      meanFieldMap P0 P1 ν α m = fun z => (∑ y, m y * K y z) + b z) :
    IsStableOnTangent K ∧
      ∀ ε > 0, ∃ T : ℕ, ∀ m : S → ℝ, IsConfiguration m →
        supNorm (fun z => meanFieldIterate (meanFieldMap P0 P1 ν α) T m z - mstar z) < ε := by
  have hSne : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := hmstar.2
    simp at h1
  haveI := hSne
  obtain ⟨hxp, hx1', hx2'⟩ := hx
  refine ⟨stable_of_ugap P0 P1 hP0 hP1 ν α mstar hmstar hUGAP.1 hUGAP.2 x
    (by linarith) (by linarith) K b hK, fun ε hε => ?_⟩
  obtain ⟨T, hT⟩ := hUGAP.2 ε hε
  exact ⟨T, fun m hm => hT T le_rfl m hm⟩
