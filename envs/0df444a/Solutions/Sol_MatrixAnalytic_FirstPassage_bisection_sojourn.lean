-- Prove2me | solution 1 for MatrixAnalytic.FirstPassage.bisection_sojourn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T05:46:31.863462+00:00
-- url     : https://prove2.me/submissions/0d7caf33-a050-4fbf-b384-a5fc7855344d

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

section fpBS
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ℕ} {P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ}

/-- the strip of levels `l+1, …, b`, killed at levels `l` and `b + 1`. -/
theorem bs_reg (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (l b : ℕ) (hlb : l < b) (hb : b < M) :
    FPReg (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level l ∪ level (b + 1))
      (Finset.Icc (l + 1) b ×ˢ Finset.univ) :=
  fq_reg hQ (l + 1) b hb.le (level l ∪ level (b + 1))
    (fun z hz => by
      rcases hz with h | h
      · left; have : z.1 = l := h; omega
      · right; have : z.1 = b + 1 := h; omega)
    (fun _ i => Or.inl (by show (l + 1 - 1) = l; omega)) (fun _ i => Or.inr rfl) l (by omega)
    (fun i => Or.inl rfl)

/-- extended level values: boundary data at levels `l` and `b + 1`. -/
def bsX (l b : ℕ) (gL gR : ι → ℝ) (F : ℕ × ι → ℝ) (m : ℕ) : ι → ℝ :=
  if m = l then gL else if m = b + 1 then gR else fun i => F (m, i)

/-- level form of the first-step system in a strip. -/
def bsLF (A₀ A₁ A₂ : Matrix ι ι ℝ) (l b : ℕ) (c : ℝ) (gL gR : ι → ℝ) (F : ℕ × ι → ℝ) : Prop :=
  ∀ k, l + 1 ≤ k → k ≤ b → ∀ i, F (k, i) = c + (A₂ *ᵥ bsX l b gL gR F (k - 1)) i +
    (A₁ *ᵥ fun j => F (k, j)) i + (A₀ *ᵥ bsX l b gL gR F (k + 1)) i

theorem bs_lf (l b : ℕ) (hlb : l < b) (hb : b < M) (c : ℝ) (gL gR : ι → ℝ) (F : ℕ × ι → ℝ)
    (k : ℕ) (hk1 : l + 1 ≤ k) (hk2 : k ≤ b) (i : ι) :
    c + ∑ r, finiteQBD M P₀₀ A₀ A₁ A₂ P_MM (k, i) (l, r) * gL r +
      ∑ r, finiteQBD M P₀₀ A₀ A₁ A₂ P_MM (k, i) (b + 1, r) * gR r +
      ∑ z ∈ Finset.Icc (l + 1) b ×ˢ Finset.univ, finiteQBD M P₀₀ A₀ A₁ A₂ P_MM (k, i) z * F z =
    c + (A₂ *ᵥ bsX l b gL gR F (k - 1)) i +
      (A₁ *ᵥ fun j => F (k, j)) i + (A₀ *ᵥ bsX l b gL gR F (k + 1)) i := by
  have hL : ∑ r, finiteQBD M P₀₀ A₀ A₁ A₂ P_MM (k, i) (l, r) * gL r =
      if k = l + 1 then (A₂ *ᵥ gL) i else 0 := by
    simp only [fq_apply, show k ≤ M by omega, show l ≤ M by omega, and_self, if_true,
      show l ≠ k + 1 by omega, show l ≠ k by omega, if_false, mulVec, dotProduct]
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega) | simp
  have hR : ∑ r, finiteQBD M P₀₀ A₀ A₁ A₂ P_MM (k, i) (b + 1, r) * gR r =
      if k = b then (A₀ *ᵥ gR) i else 0 := by
    simp only [fq_apply, show k ≤ M by omega, show b + 1 ≤ M by omega, and_self, if_true,
      show b + 1 + 1 ≠ k by omega, show b + 1 ≠ k by omega, if_false, mulVec, dotProduct]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; omega) | simp
  rw [hL, hR, fq_sum M P₀₀ A₀ A₁ A₂ P_MM k (by omega) i _ (fun m hm => by
    have := Finset.mem_Icc.1 hm; omega)]
  simp only [Finset.mem_Icc, fqD, show k ≠ 0 by omega, show k ≠ M by omega, if_false,
    show l + 1 ≤ k by omega, show k ≤ b by omega, and_self, if_true, bsX,
    show k - 1 ≠ b + 1 by omega, show k + 1 ≠ l by omega, show 1 ≤ k by omega, true_and]
  by_cases h1 : k = l + 1 <;> by_cases h2 : k = b
  · simp only [h1, h2, if_true, show ¬ (l + 1 + 1 ≤ l + 1) by omega, false_and, and_false,
      if_false, show l + 1 - 1 = l by omega] at *
    subst h2
    simp only [show ¬ (l + 1 + 1 ≤ l + 1) by omega, if_false, show ¬ (l + 1 ≤ l + 1 - 1) by omega,
      show l + 1 - 1 = l by omega, if_true]
    split_ifs <;> first | (exfalso; omega) | ring1 | (exfalso; simp_all)
  · subst h1
    simp only [if_true, if_false, h2, show l + 1 + 1 ≤ b by omega, show ¬ (l + 1 ≤ l + 1 - 1) by omega,
      false_and, show l + 1 - 1 = l by omega, show l + 1 + 1 ≠ b + 1 by omega, and_true]
    split_ifs <;> first | (exfalso; omega) | ring1 | (exfalso; simp_all)
  · subst h2
    simp only [if_true, if_false, h1, show ¬ (k + 1 ≤ k) by omega, show l + 1 ≤ k - 1 by omega,
      show k - 1 ≠ l by omega, and_true, show k - 1 ≤ k by omega]
    split_ifs <;> first | (exfalso; omega) | ring1 | (exfalso; simp_all)
  · simp only [h1, h2, if_false, show k + 1 ≤ b by omega, show l + 1 ≤ k - 1 by omega,
      show k - 1 ≠ l by omega, show k + 1 ≠ b + 1 by omega, show k - 1 ≤ b by omega, and_true,
      if_true]
    split_ifs <;> first | (exfalso; omega) | ring1 | (exfalso; simp_all)

theorem bs_sys_iff (l b : ℕ) (hlb : l < b) (hb : b < M) (c : ℝ) (gL gR : ι → ℝ)
    (F : ℕ × ι → ℝ) :
    (∀ x ∈ Finset.Icc (l + 1) b ×ˢ (Finset.univ : Finset ι), F x =
      c + ∑ r, finiteQBD M P₀₀ A₀ A₁ A₂ P_MM x (l, r) * gL r +
      ∑ r, finiteQBD M P₀₀ A₀ A₁ A₂ P_MM x (b + 1, r) * gR r +
      ∑ z ∈ Finset.Icc (l + 1) b ×ˢ Finset.univ, finiteQBD M P₀₀ A₀ A₁ A₂ P_MM x z * F z) ↔
    bsLF A₀ A₁ A₂ l b c gL gR F := by
  constructor
  · intro h k hk1 hk2 i
    rw [h (k, i) (fq_mem.2 ⟨hk1, hk2⟩), bs_lf l b hlb hb c gL gR F k hk1 hk2 i]
  · intro h x hx
    obtain ⟨k, i⟩ := x
    have := fq_mem.1 hx
    rw [bs_lf l b hlb hb c gL gR F k this.1 this.2 i]
    exact h k this.1 this.2 i

theorem bs_B (l b : ℕ) (hlb : l < b) (gL gR : ι → ℝ) (x : ℕ × ι) :
    ∑ w ∈ Finset.Icc l l ×ˢ (Finset.univ : Finset ι) ∪ Finset.Icc (b + 1) (b + 1) ×ˢ Finset.univ,
      finiteQBD M P₀₀ A₀ A₁ A₂ P_MM x w * (if w.1 = l then gL w.2 else gR w.2) =
    ∑ r, finiteQBD M P₀₀ A₀ A₁ A₂ P_MM x (l, r) * gL r +
      ∑ r, finiteQBD M P₀₀ A₀ A₁ A₂ P_MM x (b + 1, r) * gR r := by
  rw [Finset.sum_union]
  · rw [fq_sum_single, fq_sum_single]
    simp only [if_true, show b + 1 ≠ l by omega, if_false]
  · rw [Finset.disjoint_left]
    intro w h1 h2
    have := fq_mem.1 h1; have := fq_mem.1 h2; omega

theorem bs_Bmem (l b : ℕ) (w : ℕ × ι)
    (hw : w ∈ Finset.Icc l l ×ˢ (Finset.univ : Finset ι) ∪ Finset.Icc (b + 1) (b + 1) ×ˢ Finset.univ) :
    w ∈ level l ∪ level (b + 1) := by
  rcases Finset.mem_union.1 hw with h | h
  · left; have := fq_mem.1 h; show w.1 = l; omega
  · right; have := fq_mem.1 h; show w.1 = b + 1; omega

/-- splitting at the exit of a strip. -/
theorem bs_split (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (l b : ℕ) (hlb : l < b) (hb : b < M)
    (gL gR : ι → ℝ) (F : ℕ × ι → ℝ) (hF : bsLF A₀ A₁ A₂ l b 0 gL gR F) (k : ℕ)
    (hk1 : l + 1 ≤ k) (hk2 : k ≤ b) (i : ι) :
    F (k, i) = ∑ r, (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level l ∪ level (b + 1))
        (k, i) (l, r)).toReal * gL r +
      ∑ r, (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level l ∪ level (b + 1))
        (k, i) (b + 1, r)).toReal * gR r := by
  have R := bs_reg hQ l b hlb hb
  have hs := (bs_sys_iff (P₀₀ := P₀₀) (P_MM := P_MM) l b hlb hb 0 gL gR F).2 hF
  have := R.split_hit _ (bs_Bmem l b) (fun w => if w.1 = l then gL w.2 else gR w.2) F
    (fun x hx => by rw [bs_B l b hlb, hs x hx]; ring) (k, i) (fq_mem.2 ⟨hk1, hk2⟩)
  rw [this]
  have := bs_B (M := M) (P₀₀ := P₀₀) (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) (P_MM := P_MM) l b hlb gL gR
  rw [Finset.sum_union]
  · rw [fq_sum_single, fq_sum_single]
    simp only [if_true, show b + 1 ≠ l by omega, if_false]
  · rw [Finset.disjoint_left]
    intro w h1 h2
    have := fq_mem.1 h1; have := fq_mem.1 h2; omega

theorem bs_split_time (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (l b : ℕ) (hlb : l < b) (hb : b < M)
    (gL gR : ι → ℝ) (F : ℕ × ι → ℝ) (hF : bsLF A₀ A₁ A₂ l b 1 gL gR F) (k : ℕ)
    (hk1 : l + 1 ≤ k) (hk2 : k ≤ b) (i : ι) :
    F (k, i) = (expHitTime (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level l ∪ level (b + 1)) (k, i)).toReal +
      ∑ r, (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level l ∪ level (b + 1))
        (k, i) (l, r)).toReal * gL r +
      ∑ r, (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level l ∪ level (b + 1))
        (k, i) (b + 1, r)).toReal * gR r := by
  have R := bs_reg hQ l b hlb hb
  have hs := (bs_sys_iff (P₀₀ := P₀₀) (P_MM := P_MM) l b hlb hb 1 gL gR F).2 hF
  have := R.split_time _ (bs_Bmem l b) (fun w => if w.1 = l then gL w.2 else gR w.2) F
    (fun x hx => by rw [bs_B l b hlb, hs x hx]; ring) (k, i) (fq_mem.2 ⟨hk1, hk2⟩)
  rw [this, add_assoc]
  congr 1
  rw [Finset.sum_union]
  · rw [fq_sum_single, fq_sum_single]
    simp only [if_true, show b + 1 ≠ l by omega, if_false]
  · rw [Finset.disjoint_left]
    intro w h1 h2
    have := fq_mem.1 h1; have := fq_mem.1 h2; omega

/-- the hitting averages of boundary data satisfy the strip system. -/
theorem bs_ext (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (l b : ℕ) (hlb : l < b) (hb : b < M)
    (gL gR : ι → ℝ) :
    bsLF A₀ A₁ A₂ l b 0 gL gR (fun x =>
      ∑ r, (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level l ∪ level (b + 1)) x (l, r)).toReal * gL r +
      ∑ r, (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level l ∪ level (b + 1))
        x (b + 1, r)).toReal * gR r) := by
  have R := bs_reg hQ l b hlb hb
  refine (bs_sys_iff (P₀₀ := P₀₀) (P_MM := P_MM) l b hlb hb 0 gL gR _).1 fun x hx => ?_
  have hd : ∀ x, ∑ r, (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level l ∪ level (b + 1)) x (l, r)).toReal * gL r +
      ∑ r, (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level l ∪ level (b + 1)) x (b + 1, r)).toReal * gR r =
      ∑ w ∈ Finset.Icc l l ×ˢ (Finset.univ : Finset ι) ∪ Finset.Icc (b + 1) (b + 1) ×ˢ Finset.univ,
        (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level l ∪ level (b + 1)) x w).toReal *
          (if w.1 = l then gL w.2 else gR w.2) := by
    intro x
    rw [Finset.sum_union]
    · rw [fq_sum_single, fq_sum_single]
      simp only [if_true, show b + 1 ≠ l by omega, if_false]
    · rw [Finset.disjoint_left]
      intro w h1 h2
      have := fq_mem.1 h1; have := fq_mem.1 h2; omega
  simp only [hd]
  rw [R.ext_hit _ (bs_Bmem l b) _ x hx, bs_B l b hlb]
  ring

theorem bs_hit_lf (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (l b : ℕ) (hlb : l < b) (hb : b < M)
    (q : ι) :
    bsLF A₀ A₁ A₂ l b 0 (fun r => if r = q then 1 else 0) 0 (fun x =>
      (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level l ∪ level (b + 1)) x (l, q)).toReal) ∧
    bsLF A₀ A₁ A₂ l b 0 0 (fun r => if r = q then 1 else 0) (fun x =>
      (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level l ∪ level (b + 1)) x (b + 1, q)).toReal) ∧
    bsLF A₀ A₁ A₂ l b 1 0 0 (fun x =>
      (expHitTime (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level l ∪ level (b + 1)) x).toReal) := by
  have R := bs_reg hQ l b hlb hb
  refine ⟨(bs_sys_iff (P₀₀ := P₀₀) (P_MM := P_MM) l b hlb hb 0 _ _ _).1 fun x hx => ?_,
    (bs_sys_iff (P₀₀ := P₀₀) (P_MM := P_MM) l b hlb hb 0 _ _ _).1 fun x hx => ?_,
    (bs_sys_iff (P₀₀ := P₀₀) (P_MM := P_MM) l b hlb hb 1 _ _ _).1 fun x hx => ?_⟩
  · rw [(R.hit_sys (l, q)).2 x hx, if_pos (show (l, q) ∈ level l ∪ level (b + 1) from Or.inl rfl)]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Pi.zero_apply, Finset.sum_const_zero, zero_add, add_zero]
  · rw [(R.hit_sys (b + 1, q)).2 x hx, if_pos (show (b + 1, q) ∈ level l ∪ level (b + 1) from Or.inr rfl)]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Pi.zero_apply, Finset.sum_const_zero, zero_add, add_zero]
  · rw [R.time_sys.2 x hx]
    simp

theorem bs_maxp (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (l b : ℕ) (hlb : l < b) (hb : b < M)
    (F : ℕ × ι → ℝ) (hF : bsLF A₀ A₁ A₂ l b 0 0 0 F) (k : ℕ) (hk1 : l + 1 ≤ k) (hk2 : k ≤ b)
    (i : ι) : F (k, i) = 0 := by
  rw [bs_split hQ l b hlb hb 0 0 F hF k hk1 hk2 i]
  simp

theorem bsLF_sub (l b l' b' : ℕ) (h1 : l ≤ l') (h2 : l' < b') (h3 : b' ≤ b) (c : ℝ)
    (gL gR : ι → ℝ) (F : ℕ × ι → ℝ) (hF : bsLF A₀ A₁ A₂ l b c gL gR F) :
    bsLF A₀ A₁ A₂ l' b' c (bsX l b gL gR F l') (bsX l b gL gR F (b' + 1)) F := by
  intro k hk1 hk2 i
  rw [hF k (by omega) (by omega) i]
  have e1 : bsX l b gL gR F (k - 1) =
      bsX l' b' (bsX l b gL gR F l') (bsX l b gL gR F (b' + 1)) F (k - 1) := by
    by_cases hk : k - 1 = l'
    · rw [hk]; simp [bsX]
    · simp only [bsX, hk, if_false, show k - 1 ≠ b' + 1 by omega]
      split_ifs <;> first | rfl | (exfalso; omega)
  have e2 : bsX l b gL gR F (k + 1) =
      bsX l' b' (bsX l b gL gR F l') (bsX l b gL gR F (b' + 1)) F (k + 1) := by
    by_cases hk : k + 1 = b' + 1
    · rw [hk]; simp only [bsX, show b' + 1 ≠ l' by omega, if_false, if_true]
    · simp only [bsX, hk, if_false, show k + 1 ≠ l' by omega]
      split_ifs <;> first | rfl | (exfalso; omega)
  rw [e1, e2]

theorem bsLF_shift (l b n : ℕ) (c : ℝ) (gL gR : ι → ℝ) (F : ℕ × ι → ℝ)
    (hF : bsLF A₀ A₁ A₂ l b c gL gR F) :
    bsLF A₀ A₁ A₂ (n + l) (n + b) c gL gR (fun x => F (x.1 - n, x.2)) := by
  intro k hk1 hk2 i
  simp only
  rw [hF (k - n) (by omega) (by omega) i]
  have e1 : bsX l b gL gR F (k - n - 1) =
      bsX (n + l) (n + b) gL gR (fun x => F (x.1 - n, x.2)) (k - 1) := by
    simp only [bsX]
    split_ifs <;> first | rfl | (exfalso; omega) | (funext j; congr 2; omega)
  have e2 : bsX l b gL gR F (k - n + 1) =
      bsX (n + l) (n + b) gL gR (fun x => F (x.1 - n, x.2)) (k + 1) := by
    simp only [bsX]
    split_ifs <;> first | rfl | (exfalso; omega) | (funext j; congr 2; omega)
  rw [e1, e2]

end fpBS


open scoped ENNReal
open Matrix MatrixAnalytic.FirstPassage

section fpTR
variable {ι : Type*} [Fintype ι]

theorem tr_add (X Y : Matrix ι ι ℝ≥0∞) (hX : ∀ i j, X i j ≠ ⊤) (hY : ∀ i j, Y i j ≠ ⊤) :
    toRealMat (X + Y) = toRealMat X + toRealMat Y := by
  ext i j; simp [toRealMat, ENNReal.toReal_add (hX i j) (hY i j)]

theorem tr_mul (X Y : Matrix ι ι ℝ≥0∞) (hX : ∀ i j, X i j ≠ ⊤) (hY : ∀ i j, Y i j ≠ ⊤) :
    toRealMat (X * Y) = toRealMat X * toRealMat Y := by
  ext i j
  simp only [toRealMat, map_apply, mul_apply]
  rw [ENNReal.toReal_sum fun k _ => ENNReal.mul_ne_top (hX i k) (hY k j)]
  simp [ENNReal.toReal_mul]

theorem fin_add (X Y : Matrix ι ι ℝ≥0∞) (hX : ∀ i j, X i j ≠ ⊤) (hY : ∀ i j, Y i j ≠ ⊤) :
    ∀ i j, (X + Y) i j ≠ ⊤ := fun i j => by simp [ENNReal.add_ne_top, hX i j, hY i j]

theorem fin_mul (X Y : Matrix ι ι ℝ≥0∞) (hX : ∀ i j, X i j ≠ ⊤) (hY : ∀ i j, Y i j ≠ ⊤) :
    ∀ i j, (X * Y) i j ≠ ⊤ := fun i j => by
  simp only [mul_apply]
  exact (ENNReal.sum_lt_top.2 fun k _ =>
    ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (hX i k)) (lt_top_iff_ne_top.2 (hY k j))).ne

theorem tr_inj (X Y : Matrix ι ι ℝ≥0∞) (hX : ∀ i j, X i j ≠ ⊤) (hY : ∀ i j, Y i j ≠ ⊤)
    (h : toRealMat X = toRealMat Y) : X = Y := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [toRealMat, map_apply] at this
  exact (ENNReal.toReal_eq_toReal_iff' (hX i j) (hY i j)).1 this

theorem trv_add (x y : ι → ℝ≥0∞) (hx : ∀ i, x i ≠ ⊤) (hy : ∀ i, y i ≠ ⊤) :
    toRealVec (x + y) = toRealVec x + toRealVec y := by
  funext i; simp [toRealVec, ENNReal.toReal_add (hx i) (hy i)]

theorem trv_mulVec (X : Matrix ι ι ℝ≥0∞) (y : ι → ℝ≥0∞) (hX : ∀ i j, X i j ≠ ⊤)
    (hy : ∀ i, y i ≠ ⊤) : toRealVec (X *ᵥ y) = toRealMat X *ᵥ toRealVec y := by
  funext i
  simp only [toRealVec, toRealMat, mulVec, dotProduct, map_apply]
  rw [ENNReal.toReal_sum fun k _ => ENNReal.mul_ne_top (hX i k) (hy k)]
  simp [ENNReal.toReal_mul]

theorem finv_add (x y : ι → ℝ≥0∞) (hx : ∀ i, x i ≠ ⊤) (hy : ∀ i, y i ≠ ⊤) :
    ∀ i, (x + y) i ≠ ⊤ := fun i => by simp [ENNReal.add_ne_top, hx i, hy i]

theorem finv_mulVec (X : Matrix ι ι ℝ≥0∞) (y : ι → ℝ≥0∞) (hX : ∀ i j, X i j ≠ ⊤)
    (hy : ∀ i, y i ≠ ⊤) : ∀ i, (X *ᵥ y) i ≠ ⊤ := fun i => by
  simp only [mulVec, dotProduct]
  exact (ENNReal.sum_lt_top.2 fun k _ =>
    ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (hX i k)) (lt_top_iff_ne_top.2 (hy k))).ne

theorem trv_inj (x y : ι → ℝ≥0∞) (hx : ∀ i, x i ≠ ⊤) (hy : ∀ i, y i ≠ ⊤)
    (h : toRealVec x = toRealVec y) : x = y := by
  funext i
  exact (ENNReal.toReal_eq_toReal_iff' (hx i) (hy i)).1 (congrFun h i)

end fpTR

section fpBis
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ℕ} {P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ}

theorem bb_fin (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (N i : ℕ) (hN : N < M) (hi1 : 1 ≤ i)
    (hi2 : i ≤ N) :
    (∀ p q, GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) N i p q ≠ ⊤) ∧
    (∀ p q, GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) N i p q ≠ ⊤) ∧
    (∀ p, sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) N i p ≠ ⊤) := by
  have R := bs_reg hQ 0 N (by omega) hN
  have hm : ∀ p, (i, p) ∈ Finset.Icc (0 + 1) N ×ˢ (Finset.univ : Finset ι) :=
    fun p => fq_mem.2 ⟨by omega, hi2⟩
  exact ⟨fun p q => (R.hit_sys (0, q)).1 _ (hm p), fun p q => (R.hit_sys (N + 1, q)).1 _ (hm p),
    fun p => R.time_sys.1 _ (hm p)⟩

/-- shift invariance of the strip quantities. -/
theorem bb_shift (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n ν : ℕ) (hν : 1 ≤ ν) (hnν : n + ν < M)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ ν) (p r : ι) :
    hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level n ∪ level (n + ν + 1)) (n + j, p) (n, r) =
      GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j p r ∧
    hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level n ∪ level (n + ν + 1)) (n + j, p)
      (n + ν + 1, r) = GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j p r ∧
    expHitTime (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level n ∪ level (n + ν + 1)) (n + j, p) =
      sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j p := by
  have Rν := bs_reg hQ 0 ν (by omega) (by omega)
  have Rs := bs_reg hQ n (n + ν) (by omega) hnν
  have hm : (n + j, p) ∈ Finset.Icc (n + 1) (n + ν) ×ˢ (Finset.univ : Finset ι) :=
    fq_mem.2 ⟨by simp; omega, by simp; omega⟩
  have hmν : (j, p) ∈ Finset.Icc (0 + 1) ν ×ˢ (Finset.univ : Finset ι) :=
    fq_mem.2 ⟨by omega, hj2⟩
  have hL := bs_hit_lf hQ 0 ν (by omega) (by omega) r
  have hsh := fun c gL gR F (h : bsLF A₀ A₁ A₂ 0 ν c gL gR F) => by
    have := bsLF_shift 0 ν n c gL gR F h
    simpa only [Nat.add_zero] using this
  have hjn : n + j - n = j := by omega
  refine ⟨?_, ?_, ?_⟩
  · have := bs_split hQ n (n + ν) (by omega) hnν _ _ _ (hsh _ _ _ _ hL.1) (n + j) (by omega)
      (by omega) p
    simp only [hjn, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Pi.zero_apply, Finset.sum_const_zero, add_zero] at this
    exact ((ENNReal.toReal_eq_toReal_iff' ((Rs.hit_sys _).1 _ hm) ((Rν.hit_sys _).1 _ hmν)).1
      this.symm)
  · have := bs_split hQ n (n + ν) (by omega) hnν _ _ _ (hsh _ _ _ _ hL.2.1) (n + j) (by omega)
      (by omega) p
    simp only [hjn, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Pi.zero_apply, Finset.sum_const_zero, zero_add] at this
    exact ((ENNReal.toReal_eq_toReal_iff' ((Rs.hit_sys _).1 _ hm) ((Rν.hit_sys _).1 _ hmν)).1
      this.symm)
  · have := bs_split_time hQ n (n + ν) (by omega) hnν _ _ _ (hsh _ _ _ _ hL.2.2) (n + j) (by omega)
      (by omega) p
    simp only [hjn, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero] at this
    exact ((ENNReal.toReal_eq_toReal_iff' (Rs.time_sys.1 _ hm) (Rν.time_sys.1 _ hmν)).1
      this.symm)

theorem bsLF_congr (l b : ℕ) (c : ℝ) (gL gR : ι → ℝ) (F G : ℕ × ι → ℝ)
    (h : ∀ k, l + 1 ≤ k → k ≤ b → ∀ i, F (k, i) = G (k, i)) (hF : bsLF A₀ A₁ A₂ l b c gL gR F) :
    bsLF A₀ A₁ A₂ l b c gL gR G := by
  intro k hk1 hk2 i
  rw [← h k hk1 hk2 i, hF k hk1 hk2 i]
  have e0 : (fun j => F (k, j)) = fun j => G (k, j) := funext fun j => h k hk1 hk2 j
  have e1 : bsX l b gL gR F (k - 1) = bsX l b gL gR G (k - 1) := by
    simp only [bsX]; split_ifs <;> first | rfl | (funext j; exact h _ (by omega) (by omega) j)
  have e2 : bsX l b gL gR F (k + 1) = bsX l b gL gR G (k + 1) := by
    simp only [bsX]; split_ifs <;> first | rfl | (funext j; exact h _ (by omega) (by omega) j)
  rw [e0, e1, e2]

theorem bs_glue (l m b : ℕ) (h1 : l < m) (h2 : m < b) (c : ℝ) (gL gR : ι → ℝ) (F : ℕ × ι → ℝ)
    (hF1 : bsLF A₀ A₁ A₂ l m c gL (fun i => F (m + 1, i)) F)
    (hF2 : bsLF A₀ A₁ A₂ m b c (fun i => F (m, i)) gR F) : bsLF A₀ A₁ A₂ l b c gL gR F := by
  intro k hk1 hk2 i
  by_cases hk : k ≤ m
  · rw [hF1 k hk1 hk i]
    have e1 : bsX l m gL (fun i => F (m + 1, i)) F (k - 1) = bsX l b gL gR F (k - 1) := by
      simp only [bsX]; split_ifs <;> first | rfl | (exfalso; omega)
    have e2 : bsX l m gL (fun i => F (m + 1, i)) F (k + 1) = bsX l b gL gR F (k + 1) := by
      simp only [bsX]; split_ifs <;> first | rfl | (exfalso; omega) | (subst_vars; rfl) |
        (funext j; congr 2; omega)
    rw [e1, e2]
  · rw [hF2 k (by omega) hk2 i]
    have e1 : bsX m b (fun i => F (m, i)) gR F (k - 1) = bsX l b gL gR F (k - 1) := by
      simp only [bsX]; split_ifs <;> first | rfl | (exfalso; omega) | (funext j; congr 2; omega)
    have e2 : bsX m b (fun i => F (m, i)) gR F (k + 1) = bsX l b gL gR F (k + 1) := by
      simp only [bsX]; split_ifs <;> first | rfl | (exfalso; omega)
    rw [e1, e2]

variable (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n ν : ℕ) (hn : 1 ≤ n) (hν : 1 ≤ ν)
  (hnν : n + ν < M)
include hQ hn hν hnν

/-- (11.13) with `G_{n+1}^{(n+ν)}` -/
theorem bd_13 (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) i) =
      toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i) +
      toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i) *
        toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) (n + 1)) := by
  ext p q
  have hL := (bs_hit_lf hQ 0 (n + ν) (by omega) hnν q).1
  have hs := bsLF_sub 0 (n + ν) 0 n le_rfl (by omega) (by omega) _ _ _ _ hL
  have := bs_split hQ 0 n (by omega) (by omega) _ _ _ hs i (by omega) hi2 p
  simp only [bsX, if_true, if_false, show n ≠ 0 by omega, show n + 1 ≠ 0 by omega, show n ≠ n + ν + 1 by omega, show n + ν + 1 ≠ 0 by omega, show n + ν + 1 ≠ n by omega, show n + 1 ≠ n + ν + 1 by omega, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ] at this
  simp only [toRealMat, map_apply, Matrix.add_apply, mul_apply, GBis, GamBis]
  exact this

/-- (11.14) -/
theorem bd_14 (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ ν) :
    toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) (n + j)) =
      toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j) *
        toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n) := by
  ext p q
  have hL := (bs_hit_lf hQ 0 (n + ν) (by omega) hnν q).1
  have hs := bsLF_sub 0 (n + ν) n (n + ν) (by omega) (by omega) le_rfl _ _ _ _ hL
  have := bs_split hQ n (n + ν) (by omega) hnν _ _ _ hs (n + j) (by omega) (by omega) p
  simp only [bsX, if_true, if_false, show n ≠ 0 by omega, show n + 1 ≠ 0 by omega, show n ≠ n + ν + 1 by omega, show n + ν + 1 ≠ 0 by omega, show n + ν + 1 ≠ n by omega, show n + 1 ≠ n + ν + 1 by omega, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ] at this
  simp only [toRealMat, map_apply, mul_apply, GBis]
  rw [this]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [(bb_shift hQ n ν hν hnν j hj1 hj2 p r).1]
  rfl

/-- (11.15) -/
theorem bd_15 (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) i) =
      toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i) *
        toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) (n + 1)) := by
  ext p q
  have hL := (bs_hit_lf hQ 0 (n + ν) (by omega) hnν q).2.1
  have hs := bsLF_sub 0 (n + ν) 0 n le_rfl (by omega) (by omega) _ _ _ _ hL
  have := bs_split hQ 0 n (by omega) (by omega) _ _ _ hs i (by omega) hi2 p
  simp only [bsX, if_true, if_false, show n ≠ 0 by omega, show n + 1 ≠ 0 by omega, show n ≠ n + ν + 1 by omega, show n + ν + 1 ≠ 0 by omega, show n + ν + 1 ≠ n by omega, show n + 1 ≠ n + ν + 1 by omega, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ] at this
  simp only [toRealMat, map_apply, mul_apply, GamBis]
  exact this

/-- (11.16) with `Γ_n^{(n+ν)}` -/
theorem bd_16 (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ ν) :
    toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) (n + j)) =
      toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j) +
      toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j) *
        toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n) := by
  ext p q
  have hL := (bs_hit_lf hQ 0 (n + ν) (by omega) hnν q).2.1
  have hs := bsLF_sub 0 (n + ν) n (n + ν) (by omega) (by omega) le_rfl _ _ _ _ hL
  have := bs_split hQ n (n + ν) (by omega) hnν _ _ _ hs (n + j) (by omega) (by omega) p
  simp only [bsX, if_true, if_false, show n ≠ 0 by omega, show n + 1 ≠ 0 by omega, show n ≠ n + ν + 1 by omega, show n + ν + 1 ≠ 0 by omega, show n + ν + 1 ≠ n by omega, show n + 1 ≠ n + ν + 1 by omega, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ] at this
  simp only [toRealMat, map_apply, mul_apply, Matrix.add_apply, GBis, GamBis]
  rw [this, (bb_shift hQ n ν hν hnν j hj1 hj2 p q).2.1, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [(bb_shift hQ n ν hν hnν j hj1 hj2 p r).1]
  rfl

/-- sojourn splits -/
theorem bd_s1 (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    toRealVec (sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) i) =
      toRealVec (sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i) +
      toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i) *ᵥ
        toRealVec (sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) (n + 1)) := by
  funext p
  have hL := (bs_hit_lf hQ 0 (n + ν) (by omega) hnν p).2.2
  have hs := bsLF_sub 0 (n + ν) 0 n le_rfl (by omega) (by omega) _ _ _ _ hL
  have := bs_split_time hQ 0 n (by omega) (by omega) _ _ _ hs i (by omega) hi2 p
  simp only [bsX, if_true, if_false, show n ≠ 0 by omega, show n + 1 ≠ 0 by omega, show n ≠ n + ν + 1 by omega, show n + ν + 1 ≠ 0 by omega, show n + ν + 1 ≠ n by omega, show n + 1 ≠ n + ν + 1 by omega, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ] at this
  simp only [toRealMat, toRealVec, map_apply, Pi.add_apply, mulVec, dotProduct, sBis, GamBis]
  exact this

theorem bd_s2 (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ ν) :
    toRealVec (sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) (n + j)) =
      toRealVec (sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j) +
      toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j) *ᵥ
        toRealVec (sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n) := by
  funext p
  have hL := (bs_hit_lf hQ 0 (n + ν) (by omega) hnν p).2.2
  have hs := bsLF_sub 0 (n + ν) n (n + ν) (by omega) (by omega) le_rfl _ _ _ _ hL
  have := bs_split_time hQ n (n + ν) (by omega) hnν _ _ _ hs (n + j) (by omega) (by omega) p
  simp only [bsX, if_true, if_false, show n ≠ 0 by omega, show n + 1 ≠ 0 by omega, show n ≠ n + ν + 1 by omega, show n + ν + 1 ≠ 0 by omega, show n + ν + 1 ≠ n by omega, show n + 1 ≠ n + ν + 1 by omega, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ] at this
  simp only [toRealMat, toRealVec, map_apply, Pi.add_apply, mulVec, dotProduct, sBis, GBis]
  rw [this, (bb_shift hQ n ν hν hnν j hj1 hj2 p p).2.2]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [(bb_shift hQ n ν hν hnν j hj1 hj2 p r).1]
  rfl

theorem bd_unit :
    IsUnit (1 - toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n) *
      toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1)) := by
  set Γ := toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n)
  set G1 := toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1)
  refine mulVec_injective_iff_isUnit.1 fun v w hvw => ?_
  set d := v - w
  have hd : d = (Γ * G1) *ᵥ d := by
    have : (1 - Γ * G1) *ᵥ d = 0 := by simp only [d, mulVec_sub, hvw, sub_self]
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at this; exact this
  suffices d = 0 from sub_eq_zero.1 this
  set wv := G1 *ᵥ d
  set U1 : ℕ × ι → ℝ := fun x =>
    ∑ r, (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level 0 ∪ level (n + 1)) x (0, r)).toReal *
      (0 : ι → ℝ) r +
    ∑ r, (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level 0 ∪ level (n + 1)) x (n + 1, r)).toReal *
      wv r
  set U2 : ℕ × ι → ℝ := fun x =>
    ∑ r, (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level n ∪ level (n + ν + 1)) x (n, r)).toReal *
      d r +
    ∑ r, (hitDist (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (level n ∪ level (n + ν + 1)) x
      (n + ν + 1, r)).toReal * (0 : ι → ℝ) r
  set u : ℕ × ι → ℝ := fun x => if x.1 ≤ n then U1 x else U2 x
  have ha : (fun i => u (n, i)) = d := by
    funext i
    simp only [u, le_refl, if_true, U1, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
    conv_rhs => rw [hd]
    rw [← mulVec_mulVec]
    simp only [mulVec, dotProduct, Γ, toRealMat, map_apply, GamBis, wv]
  have hb : (fun i => u (n + 1, i)) = wv := by
    funext i
    simp only [u, show ¬ (n + 1 ≤ n) by omega, if_false, U2, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero]
    simp only [wv, mulVec, dotProduct, G1, toRealMat, map_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [(bb_shift hQ n ν hν hnν 1 le_rfl hν i r).1]
  have p1 : bsLF A₀ A₁ A₂ 0 n 0 0 (fun i => u (n + 1, i)) u := by
    rw [hb]
    refine bsLF_congr 0 n 0 0 wv U1 u (fun k hk1 hk2 i => ?_) (bs_ext hQ 0 n (by omega) (by omega) 0 wv)
    simp only [u, show k ≤ n by omega, if_true]
  have p2 : bsLF A₀ A₁ A₂ n (n + ν) 0 (fun i => u (n, i)) 0 u := by
    rw [ha]
    refine bsLF_congr n (n + ν) 0 d 0 U2 u (fun k hk1 hk2 i => ?_)
      (bs_ext hQ n (n + ν) (by omega) hnν d 0)
    simp only [u, show ¬ (k ≤ n) by omega, if_false]
  have hg := bs_glue 0 n (n + ν) (by omega) (by omega) 0 0 0 u p1 p2
  rw [← ha]
  funext i
  exact bs_maxp hQ 0 (n + ν) (by omega) hnν u hg n (by omega) (by omega) i

end fpBis

theorem fp_inv_of {ι : Type*} [Fintype ι] [DecidableEq ι] (C X Y : Matrix ι ι ℝ)
    (hU : IsUnit (1 - C)) (h : X = Y + C * X) : X = (1 - C)⁻¹ * Y := by
  have h1 : (1 - C) * X = Y := by rw [sub_mul, one_mul]; nth_rewrite 1 [h]; abel
  rw [← h1, ← Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hU), Matrix.one_mul]

theorem fp_inv_ofv {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℝ) (x y : ι → ℝ)
    (hU : IsUnit (1 - C)) (h : x = y + C *ᵥ x) : x = (1 - C)⁻¹ *ᵥ y := by
  have h1 : (1 - C) *ᵥ x = y := by rw [sub_mulVec, one_mulVec]; nth_rewrite 1 [h]; abel
  rw [← h1, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hU), one_mulVec]


open scoped ENNReal
open Matrix MatrixAnalytic.FirstPassage

theorem fs_main {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℕ) (P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ)
    (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n ν : ℕ) (hn : 1 ≤ n) (hν : 1 ≤ ν)
    (hnν : n + ν < M) :
    (∀ i : ℕ, 1 ≤ i → i ≤ n →
        sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) i =
          sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i +
            GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i *ᵥ
              sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1 +
            (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i *
              GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1) *ᵥ
                sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n) ∧
      (∀ p : ι, sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n p ≠ ⊤ ∧
        sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n p ≠ ⊤ ∧
        sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1 p ≠ ⊤) ∧
      IsUnit (1 - toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n) *
        toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1)) ∧
      toRealVec (sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n) =
        (1 - toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n) *
            toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1))⁻¹ *ᵥ
          (toRealVec (sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n) +
            toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n) *ᵥ
              toRealVec (sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1)) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ ν →
        sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) (n + j) =
          sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j +
            GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j *ᵥ
              sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n) := by
  set Q := finiteQBD M P₀₀ A₀ A₁ A₂ P_MM
  have fG : ∀ N i, N < M → 1 ≤ i → i ≤ N → ∀ p q, GBis Q N i p q ≠ ⊤ :=
    fun N i h1 h2 h3 => (bb_fin hQ N i h1 h2 h3).1
  have fΓ : ∀ N i, N < M → 1 ≤ i → i ≤ N → ∀ p q, GamBis Q N i p q ≠ ⊤ :=
    fun N i h1 h2 h3 => (bb_fin hQ N i h1 h2 h3).2.1
  have fs : ∀ N i, N < M → 1 ≤ i → i ≤ N → ∀ p, sBis Q N i p ≠ ⊤ :=
    fun N i h1 h2 h3 => (bb_fin hQ N i h1 h2 h3).2.2
  have hU := bd_unit hQ n ν hn hν hnν
  have hs1 := bd_s1 hQ n ν hn hν hnν
  have hs2 := bd_s2 hQ n ν hn hν hnν
  have hs21 := hs2 1 le_rfl hν
  have fsn := fs (n + ν) n hnν hn (by omega)
  have fs1 := fs ν 1 (by omega) le_rfl hν
  have fG1 := fG ν 1 (by omega) le_rfl hν
  refine ⟨fun i hi1 hi2 => ?_, fun p => ⟨fsn p, fs n n (by omega) hn le_rfl p, fs1 p⟩, hU, ?_,
    fun j hj1 hj2 => ?_⟩
  · have fΓi := fΓ n i (by omega) hi1 hi2
    have f2 := finv_mulVec _ _ (fin_mul _ _ fΓi fG1) fsn
    have f1 := finv_mulVec _ _ fΓi fs1
    refine trv_inj _ _ (fs (n + ν) i hnν hi1 (by omega))
      (finv_add _ _ (finv_add _ _ (fs n i (by omega) hi1 hi2) f1) f2) ?_
    rw [trv_add _ _ (finv_add _ _ (fs n i (by omega) hi1 hi2) f1) f2,
      trv_add _ _ (fs n i (by omega) hi1 hi2) f1, trv_mulVec _ _ fΓi fs1,
      trv_mulVec _ _ (fin_mul _ _ fΓi fG1) fsn, tr_mul _ _ fΓi fG1, hs1 i hi1 hi2, hs21,
      mulVec_add, ← mulVec_mulVec, add_assoc]
  · refine fp_inv_ofv _ _ _ hU ?_
    have := hs1 n hn le_rfl
    rw [hs21, mulVec_add, mulVec_mulVec] at this
    conv_lhs => rw [this]
    rw [add_assoc]
  · have fGj := fG ν j (by omega) hj1 hj2
    refine trv_inj _ _ (fs (n + ν) (n + j) hnν (by omega) (by omega))
      (finv_add _ _ (fs ν j (by omega) hj1 hj2) (finv_mulVec _ _ fGj fsn)) ?_
    rw [trv_add _ _ (fs ν j (by omega) hj1 hj2) (finv_mulVec _ _ fGj fsn),
      trv_mulVec _ _ fGj fsn, hs2 j hj1 hj2]


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℕ) (P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ)
    (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n ν : ℕ) (hn : 1 ≤ n) (hν : 1 ≤ ν)
    (hnν : n + ν < M) :
    (∀ i : ℕ, 1 ≤ i → i ≤ n →
        sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) i =
          sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i +
            GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i *ᵥ
              sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1 +
            (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i *
              GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1) *ᵥ
                sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n) ∧
      (∀ p : ι, sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n p ≠ ⊤ ∧
        sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n p ≠ ⊤ ∧
        sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1 p ≠ ⊤) ∧
      IsUnit (1 - toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n) *
        toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1)) ∧
      toRealVec (sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n) =
        (1 - toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n) *
            toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1))⁻¹ *ᵥ
          (toRealVec (sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n) +
            toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n) *ᵥ
              toRealVec (sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1)) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ ν →
        sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) (n + j) =
          sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j +
            GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j *ᵥ
              sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n) :=
  fs_main M P₀₀ A₀ A₁ A₂ P_MM hQ n ν hn hν hnν

