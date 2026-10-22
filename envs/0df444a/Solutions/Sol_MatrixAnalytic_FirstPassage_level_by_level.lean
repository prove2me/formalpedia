-- Prove2me | solution 1 for MatrixAnalytic.FirstPassage.level_by_level
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T05:33:56.123579+00:00
-- url     : https://prove2.me/submissions/4209cbea-3607-4d5e-8306-5d44094b552b

import Mathlib
import Definitions.Def_MatrixAnalytic_FirstPassage_Chain
import Definitions.Def_MatrixAnalytic_FirstPassage_QBD
import Definitions.Def_MatrixAnalytic_FirstPassage_Passage
set_option linter.unusedSimpArgs false

open scoped ENNReal
open MatrixAnalytic.FirstPassage

section fpGen
variable {V : Type*}

open Classical in
/-- the inner sum of `hitDist`: first entrance at time `t + 1`. -/
noncomputable def fpHS (P : V → V → ℝ) (A : Set V) (x y : V) (t : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 2) → V,
    if ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ A ∧
        ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ A
    then pathWeight P ω else 0

theorem fp_hitDist_eq (P : V → V → ℝ) (A : Set V) (x y : V) :
    hitDist P A x y = ∑' t, fpHS P A x y t := rfl

theorem fp_pw_cons (P : V → V → ℝ) {t : ℕ} (a : V) (τ : Fin (t + 1) → V) :
    pathWeight P (Fin.cons a τ : Fin (t + 2) → V) = ENNReal.ofReal (P a (τ 0)) * pathWeight P τ := by
  simp only [pathWeight]
  rw [Fin.prod_univ_succ]
  simp [Fin.cons_succ]

open Classical in
theorem fp_HS_zero (P : V → V → ℝ) (A : Set V) (x y : V) :
    fpHS P A x y 0 = if y ∈ A then ENNReal.ofReal (P x y) else 0 := by
  unfold fpHS
  rw [tsum_eq_single (![x, y])]
  · by_cases hy : y ∈ A
    · rw [if_pos, if_pos hy]
      · simp [pathWeight]
      · refine ⟨rfl, rfl, hy, fun i h0 h1 => ?_⟩
        fin_cases i <;> simp_all
    · rw [if_neg, if_neg hy]
      rintro ⟨-, -, h, -⟩; exact hy h
  · intro ω hω
    rw [if_neg]
    rintro ⟨h0, h1, _⟩
    apply hω; funext i; fin_cases i
    · simpa using h0
    · simpa using h1

open Classical in
theorem fp_HS_succ (P : V → V → ℝ) (A : Set V) (x y : V) (t : ℕ) :
    fpHS P A x y (t + 1) =
      ∑' z, (if z ∈ A then 0 else ENNReal.ofReal (P x z) * fpHS P A z y t) := by
  unfold fpHS
  rw [← (Fin.consEquiv (fun _ : Fin (t + 1 + 2) => V)).tsum_eq]
  rw [show (∑' p : V × (Fin (t + 1 + 1) → V), _) = _ from
    ENNReal.tsum_prod (f := fun a τ => if ((Fin.consEquiv fun _ => V) (a, τ)) 0 = x ∧
      ((Fin.consEquiv fun _ => V) (a, τ)) (Fin.last (t + 1 + 1)) = y ∧ y ∈ A ∧
      ∀ m : Fin (t + 1 + 2), m ≠ 0 → m ≠ Fin.last (t + 1 + 1) →
        ((Fin.consEquiv fun _ => V) (a, τ)) m ∉ A
      then pathWeight P ((Fin.consEquiv fun _ => V) (a, τ)) else 0)]
  rw [tsum_eq_single x]
  · simp_rw [← ENNReal.tsum_mul_left]
    have hR : ∀ z, (if z ∈ A then 0 else ∑' τ : Fin (t + 2) → V, ENNReal.ofReal (P x z) *
        (if τ 0 = z ∧ τ (Fin.last (t + 1)) = y ∧ y ∈ A ∧
          ∀ i : Fin (t + 2), i ≠ 0 → i ≠ Fin.last (t + 1) → τ i ∉ A
          then pathWeight P τ else 0)) =
        ∑' τ : Fin (t + 2) → V, (if τ 0 = z then
          (if τ 0 ∈ A then 0 else if τ (Fin.last (t + 1)) = y ∧ y ∈ A ∧
            ∀ i : Fin (t + 2), i ≠ 0 → i ≠ Fin.last (t + 1) → τ i ∉ A
            then ENNReal.ofReal (P x (τ 0)) * pathWeight P τ else 0) else 0) := by
      intro z
      split_ifs with hz
      · refine (ENNReal.tsum_eq_zero.2 fun τ => ?_).symm
        split_ifs with h1 <;> first | rfl | (exfalso; exact ‹τ 0 ∉ A› (h1 ▸ hz))
      · congr 1; funext τ
        by_cases h1 : τ 0 = z
        · subst h1; simp [hz]
        · simp [h1]
    rw [show (fun z => if z ∈ A then 0 else ∑' τ : Fin (t + 2) → V, ENNReal.ofReal (P x z) *
        (if τ 0 = z ∧ τ (Fin.last (t + 1)) = y ∧ y ∈ A ∧
          ∀ i : Fin (t + 2), i ≠ 0 → i ≠ Fin.last (t + 1) → τ i ∉ A
          then pathWeight P τ else 0)) = _ from funext hR, ENNReal.tsum_comm]
    congr 1; funext τ
    rw [tsum_eq_single (τ 0) (fun b hb => if_neg (Ne.symm hb)), if_pos rfl]
    rw [show (Fin.consEquiv fun _ => V) (x, τ) = (Fin.cons x τ : Fin (t + 1 + 2) → V) from rfl,
      fp_pw_cons]
    have hlast : (Fin.cons x τ : Fin (t + 1 + 2) → V) (Fin.last (t + 1 + 1)) =
        τ (Fin.last (t + 1)) := by
      rw [show Fin.last (t + 1 + 1) = (Fin.last (t + 1)).succ from rfl, Fin.cons_succ]
    have hint : (∀ i : Fin (t + 1 + 2), i ≠ 0 → i ≠ Fin.last (t + 1 + 1) →
        (Fin.cons x τ : Fin (t + 1 + 2) → V) i ∉ A) ↔
        (τ 0 ∉ A ∧ ∀ i : Fin (t + 2), i ≠ 0 → i ≠ Fin.last (t + 1) → τ i ∉ A) := by
      constructor
      · intro h
        refine ⟨?_, fun i h0 h1 => ?_⟩
        · have := h (1 : Fin (t + 1 + 2)) (by simp) (by
            intro h'; have := congrArg Fin.val h'; simp at this)
          simpa using this
        · have := h i.succ (Fin.succ_ne_zero _) (by
            intro h'; apply h1; exact Fin.succ_injective _ h')
          simpa [Fin.cons_succ] using this
      · rintro ⟨h0, h⟩ i hi0 hil
        obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hi0
        rw [Fin.cons_succ]
        by_cases hj : j = 0
        · subst hj; exact h0
        · exact h j hj (by intro h'; apply hil; rw [h']; rfl)
    by_cases hA : τ 0 ∈ A
    · rw [if_pos hA, if_neg]
      rintro ⟨-, -, -, h⟩
      exact (hint.1 h).1 hA
    · rw [if_neg hA]
      simp only [Fin.cons_zero, true_and, hlast, hint, hA, not_false_eq_true]
  · intro a ha
    refine ENNReal.tsum_eq_zero.2 fun τ => ?_
    rw [if_neg]
    rintro ⟨h0, -⟩
    exact ha (by simpa [Fin.consEquiv_apply] using h0)

open Classical in
theorem fp_AT_zero (P : V → V → ℝ) (A : Set V) (x : V) : avoidTail P A x 0 = 1 := by
  unfold avoidTail
  rw [tsum_eq_single (fun _ => x)]
  · rw [if_pos]
    · simp [pathWeight]
    · exact ⟨rfl, fun m hm => absurd (Fin.fin_one_eq_zero m) hm⟩
  · intro ω hω
    rw [if_neg]
    rintro ⟨h0, -⟩
    apply hω; funext i; rw [Fin.fin_one_eq_zero i]; exact h0

open Classical in
theorem fp_AT_succ (P : V → V → ℝ) (A : Set V) (x : V) (t : ℕ) :
    avoidTail P A x (t + 1) =
      ∑' z, (if z ∈ A then 0 else ENNReal.ofReal (P x z) * avoidTail P A z t) := by
  unfold avoidTail
  rw [← (Fin.consEquiv (fun _ : Fin (t + 1 + 1) => V)).tsum_eq]
  rw [show (∑' p : V × (Fin (t + 1) → V), _) = _ from
    ENNReal.tsum_prod (f := fun a τ => if ((Fin.consEquiv fun _ => V) (a, τ)) 0 = x ∧
      ∀ m : Fin (t + 1 + 1), m ≠ 0 → ((Fin.consEquiv fun _ => V) (a, τ)) m ∉ A
      then pathWeight P ((Fin.consEquiv fun _ => V) (a, τ)) else 0)]
  rw [tsum_eq_single x]
  · simp_rw [← ENNReal.tsum_mul_left]
    have hR : ∀ z, (if z ∈ A then 0 else ∑' τ : Fin (t + 1) → V, ENNReal.ofReal (P x z) *
        (if τ 0 = z ∧ ∀ i : Fin (t + 1), i ≠ 0 → τ i ∉ A then pathWeight P τ else 0)) =
        ∑' τ : Fin (t + 1) → V, (if τ 0 = z then
          (if τ 0 ∈ A then 0 else if ∀ i : Fin (t + 1), i ≠ 0 → τ i ∉ A
            then ENNReal.ofReal (P x (τ 0)) * pathWeight P τ else 0) else 0) := by
      intro z
      split_ifs with hz
      · refine (ENNReal.tsum_eq_zero.2 fun τ => ?_).symm
        split_ifs with h1 <;> first | rfl | (exfalso; exact ‹τ 0 ∉ A› (h1 ▸ hz))
      · congr 1; funext τ
        by_cases h1 : τ 0 = z
        · subst h1; simp [hz]
        · simp [h1]
    rw [show (fun z => if z ∈ A then 0 else ∑' τ : Fin (t + 1) → V, ENNReal.ofReal (P x z) *
        (if τ 0 = z ∧ ∀ i : Fin (t + 1), i ≠ 0 → τ i ∉ A then pathWeight P τ else 0)) = _ from
      funext hR, ENNReal.tsum_comm]
    congr 1; funext τ
    rw [tsum_eq_single (τ 0) (fun b hb => if_neg (Ne.symm hb)), if_pos rfl]
    rw [show (Fin.consEquiv fun _ => V) (x, τ) = (Fin.cons x τ : Fin (t + 1 + 1) → V) from rfl,
      fp_pw_cons]
    have hint : (∀ i : Fin (t + 1 + 1), i ≠ 0 → (Fin.cons x τ : Fin (t + 1 + 1) → V) i ∉ A) ↔
        (τ 0 ∉ A ∧ ∀ i : Fin (t + 1), i ≠ 0 → τ i ∉ A) := by
      constructor
      · intro h
        refine ⟨?_, fun i h0 => ?_⟩
        · simpa using h 1 (by simp)
        · simpa [Fin.cons_succ] using h i.succ (Fin.succ_ne_zero _)
      · rintro ⟨h0, h⟩ i hi0
        obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hi0
        rw [Fin.cons_succ]
        by_cases hj : j = 0
        · subst hj; exact h0
        · exact h j hj
    by_cases hA : τ 0 ∈ A
    · rw [if_pos hA, if_neg]
      rintro ⟨-, h⟩
      exact (hint.1 h).1 hA
    · rw [if_neg hA]
      simp only [Fin.cons_zero, true_and, hint, hA, not_false_eq_true]
  · intro a ha
    refine ENNReal.tsum_eq_zero.2 fun τ => ?_
    rw [if_neg]
    rintro ⟨h0, -⟩
    exact ha (by simpa [Fin.consEquiv_apply] using h0)

end fpGen

section fpAn
variable {V : Type*}

/-- standing hypotheses for a finite region `Ω` avoiding `A` -/
structure FPReg (P : V → V → ℝ) (A : Set V) (Ω : Finset V) : Prop where
  nonneg : ∀ x y, 0 ≤ P x y
  row : ∀ x ∈ Ω, ∀ s : Finset V, ∑ z ∈ s, P x z ≤ 1
  disj : ∀ x ∈ Ω, x ∉ A
  cl : ∀ x ∈ Ω, ∀ z, z ∉ A → 0 < P x z → z ∈ Ω
  reach : ∀ x ∈ Ω, ∃ t : ℕ, ∃ ω : Fin (t + 1) → V, ω 0 = x ∧ ω (Fin.last t) ∈ A ∧
    pathWeight P ω ≠ 0

variable {P : V → V → ℝ} {A : Set V} {Ω : Finset V}

theorem FPReg.pos_of_pw {t : ℕ} {ω : Fin (t + 1) → V} (h : pathWeight P ω ≠ 0) (m : Fin t) :
    0 < P (ω m.castSucc) (ω m.succ) := by
  unfold pathWeight at h
  have := (Finset.prod_ne_zero_iff.1 h) m (Finset.mem_univ _)
  exact ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 this)

theorem FPReg.closed (R : FPReg P A Ω) (S : Set V) (hS : ∀ x ∈ S, x ∈ Ω)
    (hcl : ∀ x ∈ S, ∀ z, 0 < P x z → z ∈ S) (x0 : V) (hx0 : x0 ∈ S) : False := by
  obtain ⟨t, ω, h0, hA, hw⟩ := R.reach x0 (hS x0 hx0)
  have key : ∀ k (hk : k ≤ t), ω ⟨k, Nat.lt_succ_of_le hk⟩ ∈ S := by
    intro k
    induction k with
    | zero => intro _; simpa [← h0] using hx0
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have := FPReg.pos_of_pw hw ⟨k, by omega⟩
      exact hcl _ h1 _ this
  have := key t le_rfl
  exact R.disj _ (hS _ this) hA

theorem FPReg.sum_lt_one (R : FPReg P A Ω) {x z : V} (hx : x ∈ Ω) (hz : z ∉ Ω)
    (hp : 0 < P x z) : ∑ w ∈ Ω, P x w < 1 := by
  classical
  have := R.row x hx (insert z Ω)
  rw [Finset.sum_insert hz] at this
  linarith

/-- maximum principle: harmonic functions on `Ω` (killed outside) vanish. -/
theorem FPReg.maxp (R : FPReg P A Ω) (u : V → ℝ) (hu : ∀ x ∈ Ω, u x = ∑ z ∈ Ω, P x z * u z) :
    ∀ x ∈ Ω, u x = 0 := by
  intro x hx
  obtain ⟨x0, hx0, hmax⟩ := Finset.exists_max_image Ω (fun x => |u x|) ⟨x, hx⟩
  set m := |u x0|
  by_contra hne
  have hm : 0 < m := lt_of_lt_of_le (abs_pos.2 hne) (hmax x hx)
  refine R.closed {x | x ∈ Ω ∧ |u x| = m} (fun x h => h.1) ?_ x0 ⟨hx0, rfl⟩
  rintro y ⟨hy, hym⟩ z hp
  have hb : |u y| ≤ ∑ w ∈ Ω, P y w * |u w| := by
    rw [hu y hy]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [abs_mul, abs_of_nonneg (R.nonneg _ _)]
  have hb2 : ∑ w ∈ Ω, P y w * |u w| ≤ ∑ w ∈ Ω, P y w * m :=
    Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left (hmax w hw) (R.nonneg _ _)
  rw [← Finset.sum_mul] at hb2
  by_cases hz : z ∈ Ω
  · refine ⟨hz, ?_⟩
    by_contra hzm
    have hlt : |u z| < m := lt_of_le_of_ne (hmax z hz) hzm
    have : ∑ w ∈ Ω, P y w * |u w| < ∑ w ∈ Ω, P y w * m := by
      apply Finset.sum_lt_sum
      · exact fun w hw => mul_le_mul_of_nonneg_left (hmax w hw) (R.nonneg _ _)
      · exact ⟨z, hz, mul_lt_mul_of_pos_left hlt hp⟩
    rw [← Finset.sum_mul] at this
    have h1 := R.row y hy Ω
    nlinarith
  · have := R.sum_lt_one hy hz hp
    nlinarith

/-- minimum principle -/
theorem FPReg.minp (R : FPReg P A Ω) (b X : V → ℝ) (hb : ∀ x ∈ Ω, 0 ≤ b x)
    (hX : ∀ x ∈ Ω, X x = b x + ∑ z ∈ Ω, P x z * X z) : ∀ x ∈ Ω, 0 ≤ X x := by
  intro x hx
  obtain ⟨x0, hx0, hmin⟩ := Finset.exists_min_image Ω X ⟨x, hx⟩
  set m := X x0
  by_contra hne
  have hm : m < 0 := lt_of_le_of_lt (hmin x hx) (lt_of_not_ge hne)
  refine R.closed {x | x ∈ Ω ∧ X x = m} (fun x h => h.1) ?_ x0 ⟨hx0, rfl⟩
  rintro y ⟨hy, hym⟩ z hp
  have e := hX y hy
  have hb2 : ∑ w ∈ Ω, P y w * m ≤ ∑ w ∈ Ω, P y w * X w :=
    Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left (hmin w hw) (R.nonneg _ _)
  rw [← Finset.sum_mul] at hb2
  have h1 := R.row y hy Ω
  have hby := hb y hy
  by_cases hz : z ∈ Ω
  · refine ⟨hz, ?_⟩
    by_contra hzm
    have hlt : m < X z := lt_of_le_of_ne (hmin z hz) (Ne.symm hzm)
    have : ∑ w ∈ Ω, P y w * m < ∑ w ∈ Ω, P y w * X w := by
      apply Finset.sum_lt_sum
      · exact fun w hw => mul_le_mul_of_nonneg_left (hmin w hw) (R.nonneg _ _)
      · exact ⟨z, hz, mul_lt_mul_of_pos_left hlt hp⟩
    rw [← Finset.sum_mul] at this
    nlinarith
  · have := R.sum_lt_one hy hz hp
    nlinarith

theorem FPReg.uniq (R : FPReg P A Ω) (b X Y : V → ℝ)
    (hX : ∀ x ∈ Ω, X x = b x + ∑ z ∈ Ω, P x z * X z)
    (hY : ∀ x ∈ Ω, Y x = b x + ∑ z ∈ Ω, P x z * Y z) : ∀ x ∈ Ω, X x = Y x := by
  have := R.maxp (fun x => X x - Y x) (fun x hx => by
    rw [hX x hx, hY x hx]; simp only [mul_sub, Finset.sum_sub_distrib]; ring)
  intro x hx; linarith [this x hx]

theorem FPReg.exists_sol (R : FPReg P A Ω) (b : V → ℝ) :
    ∃ X : V → ℝ, ∀ x ∈ Ω, X x = b x + ∑ z ∈ Ω, P x z * X z := by
  classical
  let Q : Matrix Ω Ω ℝ := fun x z => P x z
  have hinj : Function.Injective (1 - Q).mulVec := by
    intro v w hvw
    have h0 : (1 - Q).mulVec (v - w) = 0 := by rw [Matrix.mulVec_sub, hvw, sub_self]
    let u : V → ℝ := fun x => if h : x ∈ Ω then (v - w) ⟨x, h⟩ else 0
    have hu : ∀ x ∈ Ω, u x = ∑ z ∈ Ω, P x z * u z := by
      intro x hx
      have := congrFun h0 ⟨x, hx⟩
      rw [Matrix.sub_mulVec, Matrix.one_mulVec] at this
      simp only [Pi.sub_apply, Pi.zero_apply, Matrix.mulVec, dotProduct, Q] at this
      simp only [u, dif_pos hx]
      rw [← Finset.sum_attach Ω]
      have : (v - w) ⟨x, hx⟩ = ∑ z : Ω, P x z * (v - w) z := by
        simp only [Pi.sub_apply]; linarith
      rw [this]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp [dif_pos z.2]
    have := R.maxp u hu
    funext ⟨x, hx⟩
    have h := this x hx
    simp only [u, dif_pos hx] at h
    exact sub_eq_zero.1 h
  have hU : IsUnit (1 - Q) := Matrix.mulVec_injective_iff_isUnit.1 hinj
  let c : Ω → ℝ := fun x => b x
  let Xs := (1 - Q)⁻¹.mulVec c
  have hXs : (1 - Q).mulVec Xs = c := by
    simp only [Xs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU),
      Matrix.one_mulVec]
  refine ⟨fun x => if h : x ∈ Ω then Xs ⟨x, h⟩ else 0, fun x hx => ?_⟩
  have := congrFun hXs ⟨x, hx⟩
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at this
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Q, c] at this
  simp only [dif_pos hx]
  rw [← Finset.sum_attach Ω]
  have e : ∑ z ∈ Ω.attach, P x z * (if h : (z : V) ∈ Ω then Xs ⟨z, h⟩ else 0) =
      ∑ z : Ω, P x z * Xs z := by
    refine Finset.sum_congr rfl fun z _ => ?_
    simp [dif_pos z.2]
  rw [e]; linarith

open Classical in
theorem FPReg.tsum_to_fin (R : FPReg P A Ω) {x : V} (hx : x ∈ Ω) (g : V → ℝ≥0∞) :
    (∑' z, (if z ∈ A then 0 else ENNReal.ofReal (P x z) * g z)) =
      ∑ z ∈ Ω, ENNReal.ofReal (P x z) * g z := by
  rw [tsum_eq_sum (s := Ω)]
  · refine Finset.sum_congr rfl fun z hz => ?_
    rw [if_neg (R.disj z hz)]
  · intro z hz
    split_ifs with hA
    · rfl
    · have : P x z = 0 := le_antisymm (not_lt.1 fun h => hz (R.cl x hx z hA h)) (R.nonneg _ _)
      simp [this]

open Classical in
/-- generic identification of a first-step path series with the unique solution of the linear
system on `Ω`. -/
theorem FPReg.series (R : FPReg P A Ω) (b : V → ℝ) (hb : ∀ x ∈ Ω, 0 ≤ b x)
    (f : ℕ → V → ℝ≥0∞) (hf0 : ∀ x ∈ Ω, f 0 x = ENNReal.ofReal (b x))
    (hfs : ∀ t, ∀ x ∈ Ω, f (t + 1) x = ∑' z, (if z ∈ A then 0 else ENNReal.ofReal (P x z) * f t z))
    (X : V → ℝ) (hX : ∀ x ∈ Ω, X x = b x + ∑ z ∈ Ω, P x z * X z) :
    ∀ x ∈ Ω, ∑' t, f t x = ENNReal.ofReal (X x) := by
  have hXn := R.minp b X hb hX
  have hfs' : ∀ t, ∀ x ∈ Ω, f (t + 1) x = ∑ z ∈ Ω, ENNReal.ofReal (P x z) * f t z := fun t x hx =>
    (hfs t x hx).trans (R.tsum_to_fin hx _)
  have hofX : ∀ x ∈ Ω, ENNReal.ofReal (X x) =
      ENNReal.ofReal (b x) + ∑ z ∈ Ω, ENNReal.ofReal (P x z) * ENNReal.ofReal (X z) := by
    intro x hx
    rw [hX x hx, ENNReal.ofReal_add (hb x hx) (Finset.sum_nonneg fun z hz =>
      mul_nonneg (R.nonneg _ _) (hXn z hz)), ENNReal.ofReal_sum_of_nonneg (fun z hz =>
      mul_nonneg (R.nonneg _ _) (hXn z hz))]
    congr 1
    refine Finset.sum_congr rfl fun z _ => ENNReal.ofReal_mul (R.nonneg _ _)
  have hbd : ∀ T, ∀ x ∈ Ω, ∑ t ∈ Finset.range T, f t x ≤ ENNReal.ofReal (X x) := by
    intro T
    induction T with
    | zero => intro x hx; simp
    | succ T ih =>
      intro x hx
      rw [Finset.sum_range_succ', hf0 x hx, hofX x hx, add_comm]
      gcongr
      simp only [hfs' _ x hx]
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun z hz => ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul' le_rfl (ih z hz)
  have hS : ∀ x ∈ Ω, ∑' t, f t x ≤ ENNReal.ofReal (X x) := fun x hx =>
    ENNReal.tsum_le_of_sum_range_le fun T => hbd T x hx
  have hSfin : ∀ x ∈ Ω, ∑' t, f t x ≠ ⊤ := fun x hx => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hS x hx)
  have hSeq : ∀ x ∈ Ω, ∑' t, f t x = ENNReal.ofReal (b x) +
      ∑ z ∈ Ω, ENNReal.ofReal (P x z) * ∑' t, f t z := by
    intro x hx
    rw [tsum_eq_zero_add' ENNReal.summable, hf0 x hx]
    congr 1
    rw [tsum_congr fun t => hfs' t x hx, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    exact Finset.sum_congr rfl fun z _ => ENNReal.tsum_mul_left
  have hreal : ∀ x ∈ Ω, (∑' t, f t x).toReal = b x + ∑ z ∈ Ω, P x z * (∑' t, f t z).toReal := by
    intro x hx
    rw [hSeq x hx, ENNReal.toReal_add ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (hb x hx),
      ENNReal.toReal_sum]
    · congr 1
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (R.nonneg _ _)]
    · intro z hz; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hSfin z hz)
    · exact (ENNReal.sum_lt_top.2 fun z hz =>
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 (hSfin z hz))).ne
  have := R.uniq b X _ hX hreal
  intro x hx
  rw [← ENNReal.ofReal_toReal (hSfin x hx), this x hx]

open Classical in
/-- `hitDist` on `Ω` is `ofReal` of the solution of `X = P_{·y}1_A(y) + P_Ω X`. -/
theorem FPReg.hit_eq (R : FPReg P A Ω) (y : V) (X : V → ℝ)
    (hX : ∀ x ∈ Ω, X x = (if y ∈ A then P x y else 0) + ∑ z ∈ Ω, P x z * X z) :
    ∀ x ∈ Ω, hitDist P A x y = ENNReal.ofReal (X x) := by
  intro x hx
  rw [fp_hitDist_eq]
  refine R.series (fun x => if y ∈ A then P x y else 0)
    (fun x _ => by split_ifs <;> first | exact R.nonneg _ _ | exact le_rfl)
    (fun t x => fpHS P A x y t) (fun x _ => ?_) (fun t x _ => fp_HS_succ P A x y t) X hX x hx
  rw [fp_HS_zero]; split_ifs <;> simp

open Classical in
theorem FPReg.hit_sys (R : FPReg P A Ω) (y : V) :
    (∀ x ∈ Ω, hitDist P A x y ≠ ⊤) ∧
    ∀ x ∈ Ω, (hitDist P A x y).toReal =
      (if y ∈ A then P x y else 0) + ∑ z ∈ Ω, P x z * (hitDist P A z y).toReal := by
  obtain ⟨X, hX⟩ := R.exists_sol (fun x => if y ∈ A then P x y else 0)
  have h := R.hit_eq y X hX
  have hXn := R.minp _ X (fun x _ => by split_ifs <;> first | exact R.nonneg _ _ | exact le_rfl) hX
  refine ⟨fun x hx => by rw [h x hx]; exact ENNReal.ofReal_ne_top, fun x hx => ?_⟩
  rw [h x hx, ENNReal.toReal_ofReal (hXn x hx), hX x hx]
  congr 1
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [h z hz, ENNReal.toReal_ofReal (hXn z hz)]

/-- `expHitTime` on `Ω` is `ofReal` of the solution of `X = 1 + P_Ω X`. -/
theorem FPReg.time_eq (R : FPReg P A Ω) (X : V → ℝ)
    (hX : ∀ x ∈ Ω, X x = 1 + ∑ z ∈ Ω, P x z * X z) :
    ∀ x ∈ Ω, expHitTime P A x = ENNReal.ofReal (X x) := by
  intro x hx
  exact R.series (fun _ => 1) (fun _ _ => zero_le_one) (fun t x => avoidTail P A x t)
    (fun x _ => by rw [fp_AT_zero]; simp) (fun t x _ => fp_AT_succ P A x t) X hX x hx

theorem FPReg.time_sys (R : FPReg P A Ω) :
    (∀ x ∈ Ω, expHitTime P A x ≠ ⊤) ∧
    ∀ x ∈ Ω, (expHitTime P A x).toReal = 1 + ∑ z ∈ Ω, P x z * (expHitTime P A z).toReal := by
  obtain ⟨X, hX⟩ := R.exists_sol (fun _ => 1)
  have h := R.time_eq X hX
  have hXn := R.minp _ X (fun _ _ => zero_le_one) hX
  refine ⟨fun x hx => by rw [h x hx]; exact ENNReal.ofReal_ne_top, fun x hx => ?_⟩
  rw [h x hx, ENNReal.toReal_ofReal (hXn x hx), hX x hx]
  congr 1
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [h z hz, ENNReal.toReal_ofReal (hXn z hz)]

end fpAn

section fpSplit
variable {V : Type*} {P : V → V → ℝ} {A : Set V} {Ω : Finset V}

/-- splitting at the first exit: a function satisfying the first-step equation inside `Ω` with
boundary data `g` on `B ⊆ A` is the `hitDist`-average of `g`. -/
theorem FPReg.split_hit (R : FPReg P A Ω) (B : Finset V) (hB : ∀ w ∈ B, w ∈ A) (g F : V → ℝ)
    (hF : ∀ x ∈ Ω, F x = ∑ w ∈ B, P x w * g w + ∑ z ∈ Ω, P x z * F z) :
    ∀ x ∈ Ω, F x = ∑ w ∈ B, (hitDist P A x w).toReal * g w := by
  classical
  refine R.uniq (fun x => ∑ w ∈ B, P x w * g w) F _ hF fun x hx => ?_
  have hs : ∀ w ∈ B, (hitDist P A x w).toReal = P x w + ∑ z ∈ Ω, P x z * (hitDist P A z w).toReal :=
    fun w hw => by rw [(R.hit_sys w).2 x hx, if_pos (hB w hw)]
  rw [Finset.sum_congr rfl fun w hw => by rw [hs w hw]]
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

theorem FPReg.split_time (R : FPReg P A Ω) (B : Finset V) (hB : ∀ w ∈ B, w ∈ A) (g F : V → ℝ)
    (hF : ∀ x ∈ Ω, F x = 1 + ∑ w ∈ B, P x w * g w + ∑ z ∈ Ω, P x z * F z) :
    ∀ x ∈ Ω, F x = (expHitTime P A x).toReal + ∑ w ∈ B, (hitDist P A x w).toReal * g w := by
  classical
  refine R.uniq (fun x => 1 + ∑ w ∈ B, P x w * g w) F _ hF fun x hx => ?_
  have hs : ∀ w ∈ B, (hitDist P A x w).toReal = P x w + ∑ z ∈ Ω, P x z * (hitDist P A z w).toReal :=
    fun w hw => by rw [(R.hit_sys w).2 x hx, if_pos (hB w hw)]
  rw [Finset.sum_congr rfl fun w hw => by rw [hs w hw], (R.time_sys).2 x hx]
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_add, Finset.mul_sum]
  have : ∑ z ∈ Ω, ∑ w ∈ B, P x z * ((hitDist P A z w).toReal * g w) =
      ∑ w ∈ B, ∑ z ∈ Ω, P x z * (hitDist P A z w).toReal * g w := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => by ring
  rw [this]; ring

end fpSplit

section fpExt
variable {V : Type*} {P : V → V → ℝ} {A : Set V} {Ω : Finset V}

/-- the `hitDist`-average of boundary data is harmonic inside. -/
theorem FPReg.ext_hit (R : FPReg P A Ω) (B : Finset V) (hB : ∀ w ∈ B, w ∈ A) (g : V → ℝ) :
    ∀ x ∈ Ω, ∑ w ∈ B, (hitDist P A x w).toReal * g w =
      ∑ w ∈ B, P x w * g w + ∑ z ∈ Ω, P x z * ∑ w ∈ B, (hitDist P A z w).toReal * g w := by
  classical
  intro x hx
  have hs : ∀ w ∈ B, (hitDist P A x w).toReal = P x w + ∑ z ∈ Ω, P x z * (hitDist P A z w).toReal :=
    fun w hw => by rw [(R.hit_sys w).2 x hx, if_pos (hB w hw)]
  rw [Finset.sum_congr rfl fun w hw => by rw [hs w hw]]
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

end fpExt


open scoped ENNReal
open Matrix MatrixAnalytic.FirstPassage

section fpQ
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the diagonal block at level `l` -/
def fqD (M : ℕ) (P₀₀ A₁ P_MM : Matrix ι ι ℝ) (l : ℕ) : Matrix ι ι ℝ :=
  if l = 0 then P₀₀ else if l = M then P_MM else A₁

theorem fq_apply (M : ℕ) (P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ) (l k : ℕ) (i j : ι) :
    finiteQBD M P₀₀ A₀ A₁ A₂ P_MM (l, i) (k, j) =
      if l ≤ M ∧ k ≤ M then (if k = l + 1 then A₀ i j else if k + 1 = l then A₂ i j
        else if k = l then fqD M P₀₀ A₁ P_MM l i j else 0) else 0 := by
  simp only [finiteQBD, fqD]
  split_ifs <;> simp_all

theorem fq_supp (M : ℕ) (P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ) (x z : ℕ × ι)
    (h : finiteQBD M P₀₀ A₀ A₁ A₂ P_MM x z ≠ 0) :
    x.1 ≤ M ∧ z.1 ≤ M ∧ (z.1 = x.1 + 1 ∨ z.1 + 1 = x.1 ∨ z.1 = x.1) := by
  obtain ⟨l, i⟩ := x; obtain ⟨k, j⟩ := z
  rw [fq_apply] at h
  split_ifs at h with h1 h2 h3 h4 <;> simp_all

theorem fq_nonneg {M : ℕ} {P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ}
    (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (x z : ℕ × ι) :
    0 ≤ finiteQBD M P₀₀ A₀ A₁ A₂ P_MM x z := by
  obtain ⟨l, i⟩ := x; obtain ⟨k, j⟩ := z
  rw [fq_apply]
  simp only [fqD]
  split_ifs <;> first | exact le_rfl | exact hQ.nonneg_A₀ _ _ | exact hQ.nonneg_A₁ _ _ |
    exact hQ.nonneg_A₂ _ _ | exact hQ.nonneg_P₀₀ _ _ | exact hQ.nonneg_P_MM _ _

/-- the first-step sum over a block of levels -/
theorem fq_sum (M : ℕ) (P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ) (l : ℕ) (hl : l ≤ M) (i : ι)
    (K : Finset ℕ) (hK : ∀ k ∈ K, k ≤ M) (X : ℕ × ι → ℝ) :
    ∑ z ∈ K ×ˢ (Finset.univ : Finset ι), finiteQBD M P₀₀ A₀ A₁ A₂ P_MM (l, i) z * X z =
      (if l + 1 ∈ K then (A₀ *ᵥ fun j => X (l + 1, j)) i else 0) +
      (if 1 ≤ l ∧ l - 1 ∈ K then (A₂ *ᵥ fun j => X (l - 1, j)) i else 0) +
      (if l ∈ K then (fqD M P₀₀ A₁ P_MM l *ᵥ fun j => X (l, j)) i else 0) := by
  rw [Finset.sum_product]
  have hk : ∀ k ∈ K, ∑ j, finiteQBD M P₀₀ A₀ A₁ A₂ P_MM (l, i) (k, j) * X (k, j) =
      (if k = l + 1 then (A₀ *ᵥ fun j => X (l + 1, j)) i else 0) +
      (if 1 ≤ l ∧ k = l - 1 then (A₂ *ᵥ fun j => X (l - 1, j)) i else 0) +
      (if k = l then (fqD M P₀₀ A₁ P_MM l *ᵥ fun j => X (l, j)) i else 0) := by
    intro k hkK
    have hkM := hK k hkK
    simp only [fq_apply, hl, hkM, and_self, if_true, mulVec, dotProduct]
    by_cases h1 : k = l + 1
    · subst h1; simp; intros; omega
    · by_cases h2 : 1 ≤ l ∧ k = l - 1
      · obtain ⟨h2a, rfl⟩ := h2
        have : l - 1 + 1 = l := by omega
        simp [h1, this, show l - 1 ≠ l by omega]; intros; omega
      · by_cases h3 : k = l
        · subst h3; simp [h1, h2]
        · have : ¬ (k + 1 = l) := fun h => h2 ⟨by omega, by omega⟩
          simp [h1, h2, h3, this]
  rw [Finset.sum_congr rfl hk, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  congr 1
  congr 1
  by_cases h : 1 ≤ l
  · simp only [h, true_and, Finset.sum_ite_eq']
  · simp [h]

theorem fq_row {M : ℕ} {P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ}
    (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (x : ℕ × ι) (s : Finset (ℕ × ι)) :
    ∑ z ∈ s, finiteQBD M P₀₀ A₀ A₁ A₂ P_MM x z ≤ 1 := by
  classical
  obtain ⟨l, i⟩ := x
  set Q := finiteQBD M P₀₀ A₀ A₁ A₂ P_MM
  let T : Finset (ℕ × ι) := Finset.range (M + 1) ×ˢ Finset.univ
  have h1 : ∑ z ∈ s, Q (l, i) z ≤ ∑ z ∈ s ∪ T, Q (l, i) z :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      fun z _ _ => fq_nonneg hQ _ _
  have h2 : ∑ z ∈ s ∪ T, Q (l, i) z = ∑ z ∈ T, Q (l, i) z := by
    refine (Finset.sum_subset Finset.subset_union_right fun z _ hz => ?_).symm
    by_contra hne
    have := fq_supp M P₀₀ A₀ A₁ A₂ P_MM _ _ hne
    exact hz (by simp [T]; omega)
  refine h1.trans (h2.trans_le ?_)
  by_cases hl : l ≤ M
  · have := fq_sum M P₀₀ A₀ A₁ A₂ P_MM l hl i (Finset.range (M + 1))
      (fun k hk => by simp at hk; omega) (fun _ => 1)
    simp only [mul_one] at this
    rw [this]
    simp only [mulVec, dotProduct, mul_one, Finset.mem_range, fqD]
    rcases Nat.eq_zero_or_pos l with h0 | h0
    · subst h0
      have := hQ.row_zero i
      rw [Finset.sum_add_distrib] at this
      have hM := hQ.one_le
      simp only [show 0 + 1 < M + 1 by omega, if_true, show ¬ (1 ≤ 0) by omega, false_and,
        if_false, show 0 < M + 1 by omega]
      linarith
    · by_cases hlM : l = M
      · subst hlM
        have := hQ.row_top i
        rw [Finset.sum_add_distrib] at this
        simp only [show ¬ (l + 1 < l + 1) by omega, if_false, show 1 ≤ l by omega, true_and,
          show l - 1 < l + 1 by omega, if_true, show l < l + 1 by omega, show l ≠ 0 by omega]
        linarith
      · have := hQ.row_mid (by omega) i
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
        simp only [show l + 1 < M + 1 by omega, if_true, show 1 ≤ l by omega, true_and,
          show l - 1 < M + 1 by omega, show l < M + 1 by omega, show l ≠ 0 by omega, hlM,
          if_false]
        linarith
  · simp only [Q]
    rw [Finset.sum_eq_zero fun z _ => ?_]
    · norm_num
    · obtain ⟨k, j⟩ := z
      rw [fq_apply, if_neg (by omega)]

/-- regions for the finite QBD: a block of levels `[a, b]` whose exits are in `A`. -/
theorem fq_reg {M : ℕ} {P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ}
    (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (a b : ℕ) (hb : b ≤ M) (A : Set (ℕ × ι))
    (hAd : ∀ z ∈ A, z.1 < a ∨ b < z.1) (hlo : 1 ≤ a → ∀ i, (a - 1, i) ∈ A)
    (hhi : b < M → ∀ i, (b + 1, i) ∈ A) (k : ℕ) (hk : k ≤ M) (hkA : ∀ i, (k, i) ∈ A) :
    FPReg (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) A (Finset.Icc a b ×ˢ Finset.univ) where
  nonneg := fq_nonneg hQ
  row := fun x _ s => fq_row hQ x s
  disj := by
    intro x hx hA
    simp only [Finset.mem_product, Finset.mem_Icc] at hx
    rcases hAd x hA with h | h <;> omega
  cl := by
    intro x hx z hz hp
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true] at hx ⊢
    obtain ⟨h1, h2, h3⟩ := fq_supp M P₀₀ A₀ A₁ A₂ P_MM x z hp.ne'
    obtain ⟨k', j⟩ := z
    simp only at h1 h2 h3 ⊢
    by_contra hc
    rcases Nat.lt_or_ge k' a with h4 | h4
    · exact hz (by have := hlo (by omega) j; rwa [show a - 1 = k' by omega] at this)
    · exact hz (by have := hhi (by omega) j; rwa [show b + 1 = k' by omega] at this)
  reach := by
    intro x hx
    simp only [Finset.mem_product, Finset.mem_Icc] at hx
    obtain ⟨t, ω, h0, hl, hw⟩ := hQ.irreducible x (by simp; omega) (k, x.2) (by simpa using hk)
    exact ⟨t, ω, h0, by rw [hl]; exact hkA _, hw⟩

end fpQ

section fpQ2
variable {ι : Type*} [Fintype ι]

theorem fq_sum_split (f : ℕ × ι → ℝ) (a b c : ℕ) (h1 : a ≤ b + 1) (h2 : b ≤ c) :
    ∑ z ∈ Finset.Icc a c ×ˢ (Finset.univ : Finset ι), f z =
      ∑ z ∈ Finset.Icc a b ×ˢ (Finset.univ : Finset ι), f z +
      ∑ z ∈ Finset.Icc (b + 1) c ×ˢ (Finset.univ : Finset ι), f z := by
  simp only [Finset.sum_product]
  rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_consecutive _ h1 (by omega)]

theorem fq_sum_single (f : ℕ × ι → ℝ) (n : ℕ) :
    ∑ z ∈ Finset.Icc n n ×ˢ (Finset.univ : Finset ι), f z = ∑ j, f (n, j) := by
  simp [Finset.sum_product]

theorem fq_mem {a b : ℕ} {x : ℕ × ι} :
    x ∈ Finset.Icc a b ×ˢ (Finset.univ : Finset ι) ↔ a ≤ x.1 ∧ x.1 ≤ b := by
  simp

end fpQ2


open scoped ENNReal
open Matrix MatrixAnalytic.FirstPassage

section fpLBL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ℕ} {P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ}

theorem fl_reg (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (b : ℕ) (hb : b < M) :
    FPReg (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level (b + 1)) (Finset.Icc 0 b ×ˢ Finset.univ) :=
  fq_reg hQ 0 b hb.le (level (b + 1))
    (fun z hz => Or.inr (by have : z.1 = b + 1 := hz; omega)) (fun h => absurd h (by omega))
    (fun _ i => rfl) (b + 1) hb (fun i => rfl)

theorem fl_matC_succ (m : ℕ) :
    matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ (m + 1) =
      A₁ + A₂ * toRealMat (GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) m (m + 1)) := by
  simp [matC]

theorem fl_Gam (n : ℕ) (i j : ι) :
    toRealMat (GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1)) i j =
      (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level (n + 1)) (n, i) (n + 1, j)).toReal := by
  simp [toRealMat, GammaPass]

theorem fl_t (n : ℕ) (i : ι) :
    toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1)) i =
      (expHitTime (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level (n + 1)) (n, i)).toReal := by
  simp [toRealVec, tPass]

/-- the exit split at level `m + 1` for a function harmonic below `m + 2`. -/
theorem fl_lower (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (m : ℕ) (hm : m + 1 < M)
    (F : ℕ × ι → ℝ) (c : ℝ)
    (hF : ∀ x ∈ Finset.Icc 0 m ×ˢ (Finset.univ : Finset ι),
      F x = c + ∑ z ∈ Finset.Icc 0 (m + 1) ×ˢ Finset.univ,
        finiteQBD M P₀₀ A₀ A₁ A₂ P_MM x z * F z) :
    ∀ x ∈ Finset.Icc 0 m ×ˢ (Finset.univ : Finset ι),
      F x = c * (expHitTime (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level (m + 1)) x).toReal +
        ∑ r, (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level (m + 1)) x (m + 1, r)).toReal *
          F (m + 1, r) := by
  have R0 := fl_reg hQ m (by omega)
  set B : Finset (ℕ × ι) := Finset.Icc (m + 1) (m + 1) ×ˢ Finset.univ
  have hB : ∀ w ∈ B, w ∈ level (m + 1) := fun w hw => by
    have := fq_mem.1 hw; show w.1 = m + 1; omega
  have hF' : ∀ x ∈ Finset.Icc 0 m ×ˢ (Finset.univ : Finset ι),
      F x = c + ∑ w ∈ B, finiteQBD M P₀₀ A₀ A₁ A₂ P_MM x w * F w +
        ∑ z ∈ Finset.Icc 0 m ×ˢ Finset.univ, finiteQBD M P₀₀ A₀ A₁ A₂ P_MM x z * F z := by
    intro x hx
    rw [hF x hx, fq_sum_split _ 0 m (m + 1) (by omega) (by omega)]; ring
  rcases (eq_or_ne c 0) with hc | hc
  · subst hc
    intro x hx
    have := R0.split_hit B hB F F (fun x hx => by rw [hF' x hx]; ring) x hx
    rw [this, fq_sum_single]; ring
  · have hc1 : ∀ x ∈ Finset.Icc 0 m ×ˢ (Finset.univ : Finset ι),
        F x / c = 1 + ∑ w ∈ B, finiteQBD M P₀₀ A₀ A₁ A₂ P_MM x w * (F w / c) +
          ∑ z ∈ Finset.Icc 0 m ×ˢ Finset.univ, finiteQBD M P₀₀ A₀ A₁ A₂ P_MM x z * (F z / c) := by
      intro x hx
      rw [hF' x hx]
      simp only [mul_div_assoc', ← Finset.sum_div]
      field_simp
    intro x hx
    have := R0.split_time B hB (fun w => F w / c) (fun w => F w / c) hc1 x hx
    rw [fq_sum_single] at this
    field_simp at this
    rw [this, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp

/-- column equation `Γ_n = A₀ + C_n Γ_n`. -/
theorem fl_col (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n : ℕ) (hn : n < M) (j : ι) :
    (fun i => toRealMat (GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1)) i j) =
      (fun i => A₀ i j) + matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ n *ᵥ
        (fun i => toRealMat (GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1)) i j) := by
  have R1 := fl_reg hQ n hn
  set F : ℕ × ι → ℝ := fun x => (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level (n + 1)) x (n + 1, j)).toReal
  have hmem : (n + 1, j) ∈ (level (n + 1) : Set (ℕ × ι)) := rfl
  have hsys : ∀ x ∈ Finset.Icc 0 n ×ˢ (Finset.univ : Finset ι),
      F x = (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) x (n + 1, j) + ∑ z ∈ Finset.Icc 0 n ×ˢ (Finset.univ : Finset ι), (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) x z * F z := by
    intro x hx
    have := (R1.hit_sys (n + 1, j)).2 x hx
    rw [if_pos hmem] at this
    exact this
  have hlev : ∀ i, F (n, i) = A₀ i j + (if 1 ≤ n then (A₂ *ᵥ fun r => F (n - 1, r)) i else 0) +
      (fqD M P₀₀ A₁ P_MM n *ᵥ fun r => F (n, r)) i := by
    intro i
    have e := hsys (n, i) (fq_mem.2 ⟨by omega, le_rfl⟩)
    rw [fq_sum M P₀₀ A₀ A₁ A₂ P_MM n hn.le i _ (fun k hk => by have := Finset.mem_Icc.1 hk; omega)]
      at e
    simp only [Finset.mem_Icc, show ¬ (n + 1 ≤ n) by omega, and_false, if_false, le_refl,
      and_true, zero_le, true_and, if_true, add_zero, show n - 1 ≤ n by omega] at e
    rw [fq_apply, if_pos ⟨hn.le, hn⟩, if_pos rfl] at e
    exact e.trans (by ring)
  have hcol : (fun i => toRealMat (GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1)) i j) = fun i => F (n, i) :=
    funext fun i => fl_Gam n i j
  rw [hcol]
  funext i
  simp only [Pi.add_apply]
  rw [hlev i]
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    simp [matC, fqD]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hsplit := fl_lower hQ m hn F 0 (fun x hx => by
      have hx' := fq_mem.1 hx
      rw [hsys x (fq_mem.2 ⟨by omega, by omega⟩)]
      congr 1
      by_contra hne
      have := fq_supp M P₀₀ A₀ A₁ A₂ P_MM _ _ hne
      simp at this; omega)
    have hm : ∀ r, F (m, r) = (toRealMat (GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) m (m + 1)) *ᵥ fun r => F (m + 1, r)) r := by
      intro r
      rw [hsplit (m, r) (fq_mem.2 ⟨by omega, le_rfl⟩), zero_mul, zero_add]
      simp only [mulVec, dotProduct, fl_Gam]
    simp only [show 1 ≤ m + 1 by omega, if_true, Nat.add_sub_cancel, fqD,
      show m + 1 ≠ 0 by omega, show m + 1 ≠ M by omega, if_false]
    rw [fl_matC_succ, add_mulVec, ← mulVec_mulVec]
    rw [show (fun r => F (m, r)) = toRealMat (GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) m (m + 1)) *ᵥ fun r => F (m + 1, r) from
      funext hm]
    simp only [Pi.add_apply]; ring

theorem fl_unit (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n : ℕ) (hn : n < M) :
    IsUnit (1 - matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ n) := by
  set C := matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ n
  have R1 := fl_reg hQ n hn
  refine mulVec_injective_iff_isUnit.1 fun v w hvw => ?_
  set d := v - w
  have hd : d = C *ᵥ d := by
    have : (1 - C) *ᵥ d = 0 := by simp only [d, mulVec_sub, hvw, sub_self]
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at this; exact this
  suffices d = 0 from sub_eq_zero.1 this
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    let u : ℕ × ι → ℝ := fun x => d x.2
    have hu := R1.maxp u (fun x hx => by
      have hx' := fq_mem.1 hx
      obtain ⟨l, i⟩ := x
      obtain rfl : l = 0 := by simp at hx'; omega
      rw [fq_sum M P₀₀ A₀ A₁ A₂ P_MM 0 (by omega) i _ (fun k hk => by
        have := Finset.mem_Icc.1 hk; omega)]
      simp only [Finset.mem_Icc, le_refl, and_self, if_true, zero_add, show ¬ (1 ≤ 0) by omega,
        false_and, if_false, show ¬ (0 + 1 ≤ 0) by omega, and_false, add_zero]
      have := congrFun hd i
      simp only [C, matC, if_true] at this
      simp only [u, fqD, if_true]; exact this)
    funext i
    exact hu (0, i) (fq_mem.2 ⟨le_rfl, le_rfl⟩)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have R0 := fl_reg hQ m (by omega)
    set B : Finset (ℕ × ι) := Finset.Icc (m + 1) (m + 1) ×ˢ Finset.univ
    have hB : ∀ w ∈ B, w ∈ level (m + 1) := fun w hw => by
      have := fq_mem.1 hw; show w.1 = m + 1; omega
    let g : ℕ × ι → ℝ := fun x => d x.2
    let u : ℕ × ι → ℝ := fun x => if x.1 = m + 1 then d x.2 else
      ∑ w ∈ B, (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level (m + 1)) x w).toReal * g w
    have hext := R0.ext_hit B hB g
    have huB : ∀ w ∈ B, u w = g w := fun w hw => by
      have := fq_mem.1 hw; simp only [u, g, if_pos (show w.1 = m + 1 by omega)]
    have huΩ : ∀ z ∈ Finset.Icc 0 m ×ˢ (Finset.univ : Finset ι),
        u z = ∑ w ∈ B, (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level (m + 1)) z w).toReal * g w := fun z hz => by
      have := fq_mem.1 hz; simp only [u, if_neg (show z.1 ≠ m + 1 by omega)]
    have hum : ∀ r, u (m, r) = (toRealMat (GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) m (m + 1)) *ᵥ d) r := by
      intro r
      rw [huΩ (m, r) (fq_mem.2 ⟨by omega, le_rfl⟩), fq_sum_single]
      simp only [mulVec, dotProduct, fl_Gam, g]
    have hu := R1.maxp u (fun x hx => by
      have hx' := fq_mem.1 hx
      by_cases hxl : x.1 = m + 1
      · obtain ⟨l, i⟩ := x
        simp only at hxl; subst hxl
        rw [fq_sum M P₀₀ A₀ A₁ A₂ P_MM (m + 1) (by omega) i _ (fun k hk => by
          have := Finset.mem_Icc.1 hk; omega)]
        simp only [Nat.add_sub_cancel]
        have h1 : (fun j => u (m, j)) = toRealMat (GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) m (m + 1)) *ᵥ d := funext hum
        have h2 : (fun j => u (m + 1, j)) = d := by funext r; simp [u]
        have hl : u (m + 1, i) = d i := by simp [u]
        rw [h1, h2, hl]
        simp only [Finset.mem_Icc, show ¬ (m + 1 + 1 ≤ m + 1) by omega, and_false, if_false,
          zero_add, show 1 ≤ m + 1 by omega, zero_le, true_and, show m ≤ m + 1 by omega,
          le_refl, if_true, fqD, show m + 1 ≠ 0 by omega, show m + 1 ≠ M by omega]
        have e := congrFun hd i
        conv_lhs => rw [e]
        simp only [C, fl_matC_succ, add_mulVec, ← mulVec_mulVec, Pi.add_apply]
        ring
      · have hxΩ : x ∈ Finset.Icc 0 m ×ˢ (Finset.univ : Finset ι) := fq_mem.2 ⟨by omega, by omega⟩
        rw [fq_sum_split _ 0 m (m + 1) (by omega) (by omega)]
        have s1 : ∑ z ∈ Finset.Icc 0 m ×ˢ (Finset.univ : Finset ι), (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) x z * u z =
            ∑ z ∈ Finset.Icc 0 m ×ˢ (Finset.univ : Finset ι),
              (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) x z * ∑ w ∈ B, (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level (m + 1)) z w).toReal * g w :=
          Finset.sum_congr rfl fun z hz => by rw [huΩ z hz]
        have s2 : ∑ w ∈ Finset.Icc (m + 1) (m + 1) ×ˢ (Finset.univ : Finset ι), (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) x w * u w =
            ∑ w ∈ B, (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) x w * g w :=
          Finset.sum_congr rfl fun w hw => by rw [huB w hw]
        rw [s1, s2, huΩ x hxΩ, hext x hxΩ]
        ring)
    funext i
    have := hu (m + 1, i) (fq_mem.2 ⟨by omega, le_rfl⟩)
    simpa [u] using this

/-- time equation at level `n`. -/
theorem fl_time (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n : ℕ) (hn : n < M) :
    toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1)) =
      (fun _ => 1) + (if 1 ≤ n then
        A₂ *ᵥ toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n - 1) n) else 0) +
      matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ n *ᵥ
        toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1)) := by
  have R1 := fl_reg hQ n hn
  set E : ℕ × ι → ℝ := fun x => (expHitTime (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level (n + 1)) x).toReal
  have hsys : ∀ x ∈ Finset.Icc 0 n ×ˢ (Finset.univ : Finset ι),
      E x = 1 + ∑ z ∈ Finset.Icc 0 n ×ˢ (Finset.univ : Finset ι), (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) x z * E z :=
    R1.time_sys.2
  have hlev : ∀ i, E (n, i) = 1 + (if 1 ≤ n then (A₂ *ᵥ fun r => E (n - 1, r)) i else 0) +
      (fqD M P₀₀ A₁ P_MM n *ᵥ fun r => E (n, r)) i := by
    intro i
    have e := hsys (n, i) (fq_mem.2 ⟨by omega, le_rfl⟩)
    rw [fq_sum M P₀₀ A₀ A₁ A₂ P_MM n hn.le i _ (fun k hk => by have := Finset.mem_Icc.1 hk; omega)]
      at e
    simp only [Finset.mem_Icc, show ¬ (n + 1 ≤ n) by omega, and_false, if_false, le_refl,
      and_true, zero_le, true_and, if_true, zero_add, show n - 1 ≤ n by omega] at e
    rw [e]; ring
  have hE : toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1)) = fun i => E (n, i) := funext fun i => fl_t n i
  rw [hE]
  funext i
  simp only [Pi.add_apply]
  rw [hlev i]
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    simp [matC, fqD]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hsplit := fl_lower hQ m hn E 1 (fun x hx => by
      rw [hsys x (fq_mem.2 ⟨by have := fq_mem.1 hx; omega, by have := fq_mem.1 hx; omega⟩)])
    have hm : (fun r => E (m, r)) = toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) m (m + 1)) +
        toRealMat (GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) m (m + 1)) *ᵥ fun r => E (m + 1, r) := by
      funext r
      rw [hsplit (m, r) (fq_mem.2 ⟨by omega, le_rfl⟩), one_mul]
      simp only [Pi.add_apply, mulVec, dotProduct, fl_Gam, fl_t]
    simp only [show 1 ≤ m + 1 by omega, if_true, Nat.add_sub_cancel, fqD,
      show m + 1 ≠ 0 by omega, show m + 1 ≠ M by omega, if_false]
    rw [hm, fl_matC_succ, add_mulVec, ← mulVec_mulVec]
    simp only [Pi.add_apply, mulVec_add]; ring

end fpLBL


open scoped ENNReal
open Matrix MatrixAnalytic.FirstPassage

theorem fl_main {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℕ) (P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ)
    (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) :
    (∀ n : ℕ, n < M →
        IsUnit (1 - matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ n) ∧
        toRealMat (GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1)) =
          (1 - matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ n)⁻¹ * A₀) ∧
      (∀ n : ℕ, n < M → ∀ i : ι, tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1) i ≠ ⊤) ∧
      toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) 0 1) =
        (1 - matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ 0)⁻¹ *ᵥ (fun _ => (1 : ℝ)) ∧
      (∀ n : ℕ, 1 ≤ n → n < M →
        toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1)) =
          (1 - matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ n)⁻¹ *ᵥ (fun _ => (1 : ℝ)) +
          (1 - matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ n)⁻¹ *ᵥ
            (A₂ *ᵥ toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n - 1) n))) := by
  have inv_vec : ∀ (C : Matrix ι ι ℝ) (x y : ι → ℝ), IsUnit (1 - C) → x = y + C *ᵥ x →
      x = (1 - C)⁻¹ *ᵥ y := by
    intro C x y hU h
    have h1 : (1 - C) *ᵥ x = y := by
      rw [sub_mulVec, one_mulVec]; nth_rewrite 1 [h]; abel
    rw [← h1, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hU), one_mulVec]
  refine ⟨fun n hn => ⟨fl_unit hQ n hn, ?_⟩, fun n hn i => ?_, ?_, fun n hn1 hn => ?_⟩
  · have hU := fl_unit hQ n hn
    ext i j
    have := inv_vec _ _ _ hU (fl_col hQ n hn j)
    have := congrFun this i
    rw [this]
    simp [mulVec, dotProduct, mul_apply]
  · have R1 := fl_reg hQ n hn
    have := R1.time_sys.1 (n, i) (fq_mem.2 ⟨by omega, le_rfl⟩)
    simpa [tPass] using this
  · have hM := hQ.one_le
    have := inv_vec _ _ _ (fl_unit hQ 0 (by omega)) (fl_time hQ 0 (by omega))
    simpa using this
  · have := fl_time hQ n hn
    simp only [hn1, if_true] at this
    rw [inv_vec _ _ _ (fl_unit hQ n hn) this, mulVec_add]


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℕ) (P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ)
    (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) :
    (∀ n : ℕ, n < M →
        IsUnit (1 - matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ n) ∧
        toRealMat (GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1)) =
          (1 - matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ n)⁻¹ * A₀) ∧
      (∀ n : ℕ, n < M → ∀ i : ι, tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1) i ≠ ⊤) ∧
      toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) 0 1) =
        (1 - matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ 0)⁻¹ *ᵥ (fun _ => (1 : ℝ)) ∧
      (∀ n : ℕ, 1 ≤ n → n < M →
        toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1)) =
          (1 - matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ n)⁻¹ *ᵥ (fun _ => (1 : ℝ)) +
          (1 - matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ n)⁻¹ *ᵥ
            (A₂ *ᵥ toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n - 1) n))) :=
  fl_main M P₀₀ A₀ A₁ A₂ P_MM hQ

