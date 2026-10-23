-- Prove2me | solution 1 for LeastSquaresTD.Absorbing.value_consistency
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:46:38.44899+00:00
-- url     : https://prove2.me/submissions/9bb08bf8-2e89-4f8c-bedb-f9c9442d140a

import Definitions.Def_LeastSquaresTD_Absorbing_Estimator



namespace LeastSquaresTD.Absorbing

open Matrix

section VC
variable {X : Type*} [Fintype X] [DecidableEq X]


lemma vc_pow_nonneg (C : Chain X) (k : ℕ) (x y : X) : 0 ≤ (C.P ^ k) x y := by
  induction k generalizing x y with
  | zero => simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (C.nonneg _ _) (ih _ _))

lemma vc_pow_rowsum (C : Chain X) (k : ℕ) (x : X) : ∑ y, (C.P ^ k) x y = 1 := by
  induction k generalizing x with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ']
    simp_rw [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact C.row_sum x

lemma vc_abs_off (C : Chain X) {x : X} (hx : C.P x x = 1) {y : X} (hy : y ≠ x) : C.P x y = 0 := by
  have h1 := C.row_sum x
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), hx] at h1
  have h2 : ∑ z ∈ Finset.univ.erase x, C.P x z = 0 := by linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => C.nonneg x z)).1 h2 y
    (Finset.mem_erase.2 ⟨hy, Finset.mem_univ _⟩)
  exact this

lemma vc_pow_abs (C : Chain X) {x : X} (hx : C.P x x = 1) (k : ℕ) (y : X) :
    (C.P ^ k) x y = (1 : Matrix X X ℝ) x y := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    rw [Finset.sum_eq_single x]
    · rw [hx, one_mul, ih]
    · intro z _ hz; rw [vc_abs_off C hx hz, zero_mul]
    · intro h; exact absurd (Finset.mem_univ x) h

/-- indicator of non-absorbing states -/
noncomputable def vcU (C : Chain X) : X → ℝ := fun y => if C.P y y = 1 then 0 else 1

lemma vc_mulVec_mono (C : Chain X) (k : ℕ) {f g : X → ℝ} (h : ∀ y, f y ≤ g y) (x : X) :
    ((C.P ^ k) *ᵥ f) x ≤ ((C.P ^ k) *ᵥ g) x := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (h y) (vc_pow_nonneg C k x y))

lemma vc_Pu_le (C : Chain X) (x : X) : (C.P *ᵥ vcU C) x ≤ vcU C x := by
  by_cases hx : C.P x x = 1
  · have : (C.P *ᵥ vcU C) x = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy : y = x
      · subst hy; simp [vcU, hx]
      · rw [vc_abs_off C hx hy, zero_mul]
    rw [this]; simp [vcU, hx]
  · simp only [vcU, hx, if_false]
    simp only [Matrix.mulVec, dotProduct]
    calc ∑ y, C.P x y * (if C.P y y = 1 then (0:ℝ) else 1) ≤ ∑ y, C.P x y * 1 :=
          Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left
            (by split_ifs <;> norm_num) (C.nonneg _ _))
      _ = 1 := by simp [C.row_sum x]

lemma vc_a_succ_le (C : Chain X) (k : ℕ) (x : X) :
    ((C.P ^ (k+1)) *ᵥ vcU C) x ≤ ((C.P ^ k) *ᵥ vcU C) x := by
  rw [pow_succ, ← Matrix.mulVec_mulVec]
  exact vc_mulVec_mono C k (fun y => vc_Pu_le C y) x

lemma vc_a_le_one (C : Chain X) (k : ℕ) (x : X) : ((C.P ^ k) *ᵥ vcU C) x ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  calc ∑ y, (C.P ^ k) x y * vcU C y ≤ ∑ y, (C.P ^ k) x y * 1 :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left
          (by unfold vcU; split_ifs <;> norm_num) (vc_pow_nonneg C k x y))
    _ = 1 := by simp [vc_pow_rowsum C k x]

lemma vc_a_nonneg (C : Chain X) (k : ℕ) (x : X) : 0 ≤ ((C.P ^ k) *ᵥ vcU C) x := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg (fun y _ => mul_nonneg (vc_pow_nonneg C k x y)
    (by unfold vcU; split_ifs <;> norm_num))

lemma vc_a_abs (C : Chain X) {x : X} (hx : C.P x x = 1) (k : ℕ) : ((C.P ^ k) *ᵥ vcU C) x = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro y _
  rw [vc_pow_abs C hx k y, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp [vcU, hx]
  · simp [h]

lemma vc_a_lt_one (C : Chain X) (habs : C.IsAbsorbing) (x : X) :
    ∃ n, ((C.P ^ n) *ᵥ vcU C) x < 1 := by
  obtain ⟨n, y, hy, hpos⟩ := habs x
  refine ⟨n, ?_⟩
  have h1 : ∑ z, (C.P ^ n) x z * (1 - vcU C z) = 1 - ((C.P ^ n) *ᵥ vcU C) x := by
    simp only [Matrix.mulVec, dotProduct, mul_sub, mul_one, Finset.sum_sub_distrib,
      vc_pow_rowsum]
  have h2 : (C.P ^ n) x y * (1 - vcU C y) ≤ ∑ z, (C.P ^ n) x z * (1 - vcU C z) :=
    Finset.single_le_sum (f := fun z => (C.P ^ n) x z * (1 - vcU C z))
      (fun z _ => mul_nonneg (vc_pow_nonneg C n x z) (by unfold vcU; split_ifs <;> norm_num))
      (Finset.mem_univ y)
  have h3 : vcU C y = 0 := by simp [vcU, hy]
  rw [h3] at h2
  linarith

/-- geometric decay of the unabsorbed mass -/
lemma vc_decay (C : Chain X) (habs : C.IsAbsorbing) [Nonempty X] :
    ∃ (N0 : ℕ) (c : ℝ), 0 < N0 ∧ 0 < c ∧ c < 1 ∧
      ∀ j r x, ((C.P ^ (j * N0 + r)) *ᵥ vcU C) x ≤ c ^ j := by
  choose n hn using vc_a_lt_one C habs
  set N0 := Finset.univ.sup n + 1 with hN0
  have hN0le : ∀ x, n x ≤ N0 := fun x =>
    le_trans (Finset.le_sup (f := n) (Finset.mem_univ x)) (Nat.le_succ _)
  have hmono : ∀ x a b, a ≤ b → ((C.P ^ b) *ᵥ vcU C) x ≤ ((C.P ^ a) *ᵥ vcU C) x := by
    intro x a b hab
    induction hab with
    | refl => exact le_rfl
    | step h ih => exact le_trans (vc_a_succ_le C _ x) ih
  obtain ⟨x0, hx0⟩ := Finite.exists_max (fun x => ((C.P ^ N0) *ᵥ vcU C) x)
  have hc0 : ((C.P ^ N0) *ᵥ vcU C) x0 < 1 :=
    lt_of_le_of_lt (hmono x0 _ _ (hN0le x0)) (hn x0)
  set c := max (((C.P ^ N0) *ᵥ vcU C) x0) (1/2) with hc
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hc1 : c < 1 := max_lt hc0 (by norm_num)
  refine ⟨N0, c, Nat.succ_pos _, hcpos, hc1, ?_⟩
  -- key: a_{k+N0} ≤ c a_k
  have key : ∀ k x, ((C.P ^ (k + N0)) *ᵥ vcU C) x ≤ c * ((C.P ^ k) *ᵥ vcU C) x := by
    intro k x
    rw [pow_add, ← Matrix.mulVec_mulVec]
    have hle : ∀ y, ((C.P ^ N0) *ᵥ vcU C) y ≤ c * vcU C y := by
      intro y
      by_cases hy : C.P y y = 1
      · rw [vc_a_abs C hy]; simp [vcU, hy]
      · simp only [vcU, hy, if_false, mul_one]
        exact le_trans (hx0 y) (le_max_left _ _)
    calc ((C.P ^ k) *ᵥ ((C.P ^ N0) *ᵥ vcU C)) x ≤ ((C.P ^ k) *ᵥ (fun y => c * vcU C y)) x :=
          vc_mulVec_mono C k hle x
      _ = c * ((C.P ^ k) *ᵥ vcU C) x := by
          have : (fun y => c * vcU C y) = c • vcU C := rfl
          rw [this, Matrix.mulVec_smul]; rfl
  intro j r x
  induction j generalizing x with
  | zero => simpa using vc_a_le_one C r x
  | succ j ih =>
    have : (j + 1) * N0 + r = (j * N0 + r) + N0 := by ring
    rw [this, pow_succ]
    calc _ ≤ c * ((C.P ^ (j * N0 + r)) *ᵥ vcU C) x := key _ x
      _ ≤ c * c ^ j := mul_le_mul_of_nonneg_left (ih x) hcpos.le
      _ = c ^ j * c := mul_comm _ _

lemma vc_a_summable (C : Chain X) (habs : C.IsAbsorbing) [Nonempty X] (x : X) :
    Summable (fun k : ℕ => ((C.P ^ k) *ᵥ vcU C) x) := by
  obtain ⟨N0, c, hN, hc0, hc1, hdec⟩ := vc_decay C habs
  have hbound : ∀ k, ((C.P ^ k) *ᵥ vcU C) x ≤ c⁻¹ * (c ^ (1 / (N0:ℝ))) ^ k := by
    intro k
    have h := hdec (k / N0) (k % N0) x
    rw [Nat.div_add_mod'] at h
    refine le_trans h ?_
    have hr : (c ^ (1 / (N0:ℝ))) ^ k = c ^ ((k:ℝ) / N0) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
      congr 1; ring
    rw [hr]
    have : c ^ (k / N0) = c ^ (((k / N0 : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
    rw [this]
    have h2 : ((k:ℝ) / N0) - 1 ≤ ((k / N0 : ℕ) : ℝ) := by
      have := Nat.lt_div_mul_add (a := k) hN
      have hNr : (0:ℝ) < N0 := by exact_mod_cast hN
      rw [sub_le_iff_le_add, div_le_iff₀ hNr]
      have h3 : (k:ℝ) < ((k / N0 : ℕ) : ℝ) * N0 + N0 := by exact_mod_cast this
      nlinarith
    calc c ^ (((k / N0 : ℕ) : ℝ)) ≤ c ^ (((k:ℝ) / N0) - 1) :=
          Real.rpow_le_rpow_of_exponent_ge hc0 hc1.le h2
      _ = c⁻¹ * c ^ ((k:ℝ) / N0) := by
          rw [Real.rpow_sub hc0, Real.rpow_one, div_eq_inv_mul]
  have hρ : c ^ (1 / (N0:ℝ)) < 1 :=
    Real.rpow_lt_one hc0.le hc1 (by positivity)
  have hρ0 : 0 ≤ c ^ (1 / (N0:ℝ)) := Real.rpow_nonneg hc0.le _
  exact Summable.of_nonneg_of_le (fun k => vc_a_nonneg C k x) hbound
    ((summable_geometric_of_lt_one hρ0 hρ).mul_left _)

end VC

variable {m : ℕ}

lemma vc_summable
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (R : X → X → ℝ) (habs : C.IsAbsorbing)
    (hRabs : ∀ x y, C.P x x = 1 → C.P y y = 1 → R x y = 0)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (x : X) :
    Summable (fun k : ℕ => γ ^ k * (Matrix.mulVec (C.P ^ k) (C.rbar R)) x) := by
  set M := ∑ y, |C.rbar R y| with hM
  have hrb : ∀ y, |C.rbar R y| ≤ M * vcU C y := by
    intro y
    by_cases hy : C.P y y = 1
    · have : C.rbar R y = 0 := by
        unfold Chain.rbar
        rw [Finset.sum_eq_single y]
        · rw [hy, hRabs y y hy hy]; simp
        · intro z _ hz; rw [vc_abs_off C hy hz, zero_mul]
        · intro h; exact absurd (Finset.mem_univ y) h
      simp [this, vcU, hy]
    · simp only [vcU, hy, if_false, mul_one]
      exact Finset.single_le_sum (f := fun z => |C.rbar R z|) (fun z _ => abs_nonneg _)
        (Finset.mem_univ y)
  have hb : ∀ k, |γ ^ k * (Matrix.mulVec (C.P ^ k) (C.rbar R)) x| ≤
      M * ((C.P ^ k) *ᵥ vcU C) x := by
    intro k
    rw [abs_mul, abs_of_nonneg (pow_nonneg hγ0 k)]
    have h1 : |(Matrix.mulVec (C.P ^ k) (C.rbar R)) x| ≤ M * ((C.P ^ k) *ᵥ vcU C) x := by
      simp only [Matrix.mulVec, dotProduct]
      calc |∑ y, (C.P ^ k) x y * C.rbar R y| ≤ ∑ y, |(C.P ^ k) x y * C.rbar R y| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ y, (C.P ^ k) x y * (M * vcU C y) := by
            apply Finset.sum_le_sum; intro y _
            rw [abs_mul, abs_of_nonneg (vc_pow_nonneg C k x y)]
            exact mul_le_mul_of_nonneg_left (hrb y) (vc_pow_nonneg C k x y)
        _ = M * ∑ y, (C.P ^ k) x y * vcU C y := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
    have hM0 : 0 ≤ M * ((C.P ^ k) *ᵥ vcU C) x :=
      mul_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (vc_a_nonneg C k x)
    calc γ ^ k * |(Matrix.mulVec (C.P ^ k) (C.rbar R)) x|
        ≤ 1 * |(Matrix.mulVec (C.P ^ k) (C.rbar R)) x| :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hγ0 hγ1) (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h1
  exact Summable.of_norm_bounded (g := fun k => M * ((C.P ^ k) *ᵥ vcU C) x)
    ((vc_a_summable C habs x).mul_left _) (fun k => by simpa [Real.norm_eq_abs] using hb k)

theorem value_consistency_core
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (R : X → X → ℝ) (φ : X → Fin m → ℝ) (γ : ℝ)
    (habs : C.IsAbsorbing) (hRabs : ∀ x y, C.P x x = 1 → C.P y y = 1 → R x y = 0)
    (hm : m = Fintype.card C.Nonabsorbing)
    (hli : LinearIndependent ℝ (fun x : C.Nonabsorbing => φ x.val))
    (hφabs : ∀ x, C.P x x = 1 → φ x = 0)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∃ θstar : Fin m → ℝ,
      (∀ x, Summable (fun k : ℕ => γ ^ k *
        (Matrix.mulVec (C.P ^ k) (C.rbar R)) x)) ∧
      (∀ x, C.value R γ x = ∑ i, φ x i * θstar i) ∧
      C.rbar R = Matrix.mulVec (1 - γ • C.P)
        (Matrix.mulVec (Matrix.of φ) θstar) := by
  have hsum := vc_summable C R habs hRabs γ hγ0 hγ1
  set v : X → ℝ := fun x => C.value R γ x with hv
  -- value vanishes at absorbing states
  have hrb_abs : ∀ y, C.P y y = 1 → C.rbar R y = 0 := by
    intro y hy
    unfold Chain.rbar
    rw [Finset.sum_eq_single y]
    · rw [hy, hRabs y y hy hy]; simp
    · intro z _ hz; rw [vc_abs_off C hy hz, zero_mul]
    · intro h; exact absurd (Finset.mem_univ y) h
  have hv_abs : ∀ x, C.P x x = 1 → v x = 0 := by
    intro x hx
    simp only [hv, Chain.value]
    have : ∀ k : ℕ, γ ^ k * (Matrix.mulVec (C.P ^ k) (C.rbar R)) x = 0 := by
      intro k
      have : (Matrix.mulVec (C.P ^ k) (C.rbar R)) x = 0 := by
        simp only [Matrix.mulVec, dotProduct]
        apply Finset.sum_eq_zero
        intro y _
        rw [vc_pow_abs C hx k y, Matrix.one_apply]
        by_cases h : x = y
        · subst h; rw [hrb_abs x hx]; simp
        · simp [h]
      rw [this, mul_zero]
    simp [this]
  -- Bellman equation
  have hbell : ∀ x, C.rbar R x = v x - γ * (C.P *ᵥ v) x := by
    intro x
    have hs : ∀ y, Summable (fun k : ℕ => γ ^ k * (Matrix.mulVec (C.P ^ k) (C.rbar R)) y) := hsum
    have h0 : v x = C.rbar R x + ∑' k : ℕ, γ ^ (k+1) * (Matrix.mulVec (C.P ^ (k+1)) (C.rbar R)) x := by
      simp only [hv, Chain.value]
      rw [Summable.tsum_eq_zero_add (hs x)]
      simp
    have h1 : γ * (C.P *ᵥ v) x =
        ∑' k : ℕ, γ ^ (k+1) * (Matrix.mulVec (C.P ^ (k+1)) (C.rbar R)) x := by
      have e1 : (C.P *ᵥ v) x = ∑ y, C.P x y * v y := rfl
      have e2 : ∀ y, v y = ∑' k : ℕ, γ ^ k * (Matrix.mulVec (C.P ^ k) (C.rbar R)) y := fun y => rfl
      simp_rw [e1, e2]
      have : ∀ y, C.P x y * ∑' k : ℕ, γ ^ k * (Matrix.mulVec (C.P ^ k) (C.rbar R)) y
          = ∑' k : ℕ, C.P x y * (γ ^ k * (Matrix.mulVec (C.P ^ k) (C.rbar R)) y) := by
        intro y; rw [tsum_mul_left]
      simp_rw [this]
      rw [← Summable.tsum_finsetSum (fun y _ => ((hs y).mul_left _)), ← tsum_mul_left]
      apply tsum_congr; intro k
      rw [pow_succ' γ k, pow_succ' C.P k, ← Matrix.mulVec_mulVec]
      have e3 : (C.P *ᵥ (C.P ^ k *ᵥ C.rbar R)) x = ∑ y, C.P x y * (C.P ^ k *ᵥ C.rbar R) y := rfl
      rw [e3, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro y _
      ring
    linarith
  -- find θ
  obtain ⟨e⟩ : Nonempty (C.Nonabsorbing ≃ Fin m) :=
    ⟨Fintype.equivFinOfCardEq hm.symm⟩
  let Mx : Matrix C.Nonabsorbing C.Nonabsorbing ℝ := fun x y => φ x.val (e y)
  have hMli : LinearIndependent ℝ (fun x => Mx x) := by
    have hinj : Function.Injective (LinearMap.funLeft ℝ ℝ e) :=
      LinearMap.funLeft_injective_of_surjective ℝ ℝ e e.surjective
    exact hli.map' (LinearMap.funLeft ℝ ℝ e) (LinearMap.ker_eq_bot.2 hinj)
  have hunit : IsUnit Mx := Matrix.linearIndependent_rows_iff_isUnit.1 hMli
  set θ' : C.Nonabsorbing → ℝ := Mx⁻¹ *ᵥ (fun x => v x.val) with hθ'
  have hMθ : Mx *ᵥ θ' = fun x => v x.val := by
    rw [hθ', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit),
      Matrix.one_mulVec]
  refine ⟨fun i => θ' (e.symm i), hsum, ?_, ?_⟩
  · have hv_eq : ∀ x, v x = ∑ i, φ x i * θ' (e.symm i) := by
      intro x
      by_cases hx : C.P x x = 1
      · rw [hv_abs x hx, hφabs x hx]; simp
      · have h1 := congrFun hMθ ⟨x, hx⟩
        simp only [Matrix.mulVec, dotProduct, Mx] at h1
        rw [← Equiv.sum_comp e]
        simpa using h1.symm
    intro x; exact hv_eq x
  · have hv_eq : ∀ x, v x = ∑ i, φ x i * θ' (e.symm i) := by
      intro x
      by_cases hx : C.P x x = 1
      · rw [hv_abs x hx, hφabs x hx]; simp
      · have h1 := congrFun hMθ ⟨x, hx⟩
        simp only [Matrix.mulVec, dotProduct, Mx] at h1
        rw [← Equiv.sum_comp e]
        simpa using h1.symm
    have hΦ : Matrix.mulVec (Matrix.of φ) (fun i => θ' (e.symm i)) = v := by
      funext x; simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]; exact (hv_eq x).symm
    rw [hΦ]
    funext x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    simp [hbell x]

end LeastSquaresTD.Absorbing

open LeastSquaresTD.Absorbing
variable {m : ℕ}

theorem solution
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (R : X → X → ℝ) (φ : X → Fin m → ℝ) (γ : ℝ)
    (habs : C.IsAbsorbing) (hRabs : ∀ x y, C.P x x = 1 → C.P y y = 1 → R x y = 0)
    (hm : m = Fintype.card C.Nonabsorbing)
    (hli : LinearIndependent ℝ (fun x : C.Nonabsorbing => φ x.val))
    (hφabs : ∀ x, C.P x x = 1 → φ x = 0)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∃ θstar : Fin m → ℝ,
      (∀ x, Summable (fun k : ℕ => γ ^ k *
        (Matrix.mulVec (C.P ^ k) (C.rbar R)) x)) ∧
      (∀ x, C.value R γ x = ∑ i, φ x i * θstar i) ∧
      C.rbar R = Matrix.mulVec (1 - γ • C.P)
        (Matrix.mulVec (Matrix.of φ) θstar) := by
  exact value_consistency_core C R φ γ habs hRabs hm hli hφabs hγ0 hγ1
