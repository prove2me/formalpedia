-- Prove2me | solution 1 for HeteroBass.HetP.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:35:33.151132+00:00
-- url     : https://prove2.me/submissions/7c5240c8-d6ec-41d5-81a6-e837134bed78

import Mathlib
import Definitions.Def_HeteroBass_HetP_Model

open HeteroBass.HetP

namespace HBT3

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma entry_hasDerivAt {α : Type} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (i j : α) (t : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A) i j)
      (∑ k, NormedSpace.exp (t • A) i k * A k j) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) A t
  have hc : HasDerivAt (fun u : ℝ => (NormedSpace.exp (u • A)) i j)
      ((NormedSpace.exp (t • A) * A) i j) t := by
    have := (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : α => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : α => α → ℝ) i))).hasFDerivAt.comp_hasDerivAt t h
    exact this
  simpa [Matrix.mul_apply] using hc

variable {M : ℕ}

lemma gen_sum (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ) (T : Finset (Fin M))
    (h : Finset (Fin M) → ℝ) :
    ∑ S, generator p Q T S * h S =
      ∑ j ∈ Tᶜ, adoptRate p Q T j * (h (insert j T) - h T) := by
  set r := adopterJumpRate p Q
  have hG : ∀ S, generator p Q T S * h S =
      (if S = T then 0 else r T S) * (h S - h T) +
        (if S = T then 0 else r T S) * h T - (if T = S then ∑ U, (if U = T then 0 else r T U) * h T else 0) := by
    intro S
    simp only [generator, finiteJumpGenerator]
    by_cases hST : T = S
    · subst hST; simp [Finset.sum_mul, r]
    · have : S ≠ T := fun h => hST h.symm
      simp [hST, this]; ring
  simp_rw [hG]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [add_sub_cancel_right]
  have h2 : ∀ S, (if S = T then 0 else r T S) * (h S - h T) = r T S * (h S - h T) := by
    intro S; by_cases hS : S = T <;> simp [hS]
  simp_rw [h2]
  simp only [r, adopterJumpRate, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [ite_mul]


/-! ### Scalar ODE tools -/

lemma ifac {y g : ℝ → ℝ} (K : ℝ) (hy : ∀ t, HasDerivAt y (-K * y t + g t) t) :
    ∀ t, HasDerivAt (fun s => Real.exp (K * s) * y s) (Real.exp (K * t) * g t) t := by
  intro t
  have h1 : HasDerivAt (fun s => Real.exp (K * s)) (Real.exp (K * t) * K) t := by
    have := ((hasDerivAt_id t).const_mul K).exp
    simpa [mul_comm] using this
  exact (h1.mul (hy t)).congr_deriv (by ring)

lemma IF_pos {y g : ℝ → ℝ} (K : ℝ) (hy : ∀ t, HasDerivAt y (-K * y t + g t) t)
    (h0 : 0 ≤ y 0) (hg : ∀ t, 0 < t → 0 < g t) : ∀ t, 0 < t → 0 < y t := by
  have hφ := ifac K hy
  have hmono : StrictMonoOn (fun s => Real.exp (K * s) * y s) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · intro t _; exact (hφ t).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hφ t).deriv]
      exact mul_pos (Real.exp_pos _) (hg t ht)
  intro t ht
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht.le) ht
  simp only [mul_zero, Real.exp_zero, one_mul] at this
  exact pos_of_mul_pos_right (lt_of_le_of_lt h0 this) (Real.exp_pos _).le

lemma IF_nonneg {y g : ℝ → ℝ} (K : ℝ) (hy : ∀ t, HasDerivAt y (-K * y t + g t) t)
    (h0 : 0 ≤ y 0) (hg : ∀ t, 0 < t → 0 ≤ g t) : ∀ t, 0 ≤ t → 0 ≤ y t := by
  have hφ := ifac K hy
  have hmono : MonotoneOn (fun s => Real.exp (K * s) * y s) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro t _; exact (hφ t).continuousAt.continuousWithinAt
    · intro t _; exact (hφ t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hφ t).deriv]
      exact mul_nonneg (Real.exp_pos _).le (hg t ht)
  intro t ht
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  simp only [mul_zero, Real.exp_zero, one_mul] at this
  exact nonneg_of_mul_nonneg_right (by nlinarith [Real.exp_pos (K * t)]) (Real.exp_pos (K * t))

lemma const_of_deriv {y : ℝ → ℝ} (hy : ∀ t, HasDerivAt y 0 t) : ∀ t, y t = y 0 := by
  intro t
  exact is_const_of_deriv_eq_zero (fun s => (hy s).differentiableAt) (fun s => (hy s).deriv) t 0

lemma exp_sol {a : ℝ → ℝ} (s : ℝ) (ha : ∀ t, HasDerivAt a (-s * a t) t) (h0 : a 0 = 1) :
    ∀ t, a t = Real.exp (-s * t) := by
  have hφ := ifac s (g := fun _ => 0) (by intro t; simpa using ha t)
  have hc := const_of_deriv (y := fun u => Real.exp (s * u) * a u) (by intro t; simpa using hφ t)
  intro t
  have := hc t
  simp only [mul_zero, Real.exp_zero, h0, one_mul] at this
  have he : Real.exp (-s * t) * Real.exp (s * t) = 1 := by
    rw [← Real.exp_add]; simp
  calc a t = Real.exp (-s * t) * (Real.exp (s * t) * a t) := by rw [← mul_assoc, he, one_mul]
    _ = Real.exp (-s * t) := by rw [this, mul_one]

/-! ### Dynkin formula and forward equations -/

/-- Probability of adopter set `S` at time `t`, starting from no adopters. -/
noncomputable def U (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ) (t : ℝ) (S : Finset (Fin M)) : ℝ :=
  transition p Q t ∅ S

lemma U_init (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ) (S : Finset (Fin M)) :
    U p Q 0 S = if S = ∅ then 1 else 0 := by
  simp only [U, transition, zero_smul, NormedSpace.exp_zero]
  rw [Matrix.one_apply]
  by_cases h : S = ∅ <;> simp [h, eq_comm]

lemma dyn (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ) (h : Finset (Fin M) → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∑ S, U p Q s S * h S)
      (∑ T, U p Q t T * ∑ j ∈ Tᶜ, adoptRate p Q T j * (h (insert j T) - h T)) t := by
  have hS : ∀ S ∈ (Finset.univ : Finset (Finset (Fin M))),
      HasDerivAt (fun s => U p Q s S * h S) ((∑ T, U p Q t T * generator p Q T S) * h S) t :=
    fun S _ => (entry_hasDerivAt (generator p Q) ∅ S t).mul_const (h S)
  refine (HasDerivAt.fun_sum hS).congr_deriv ?_
  simp_rw [← gen_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun T _ => Finset.sum_congr rfl (fun S _ => ?_))
  ring

lemma comb (S : Finset (Fin M)) (F : Finset (Fin M) → Fin M → ℝ) :
    ∑ T, ∑ j ∈ Tᶜ, (if insert j T = S then F T j else 0) = ∑ l ∈ S, F (S.erase l) l := by
  have h1 : ∀ T : Finset (Fin M), ∑ j ∈ Tᶜ, (if insert j T = S then F T j else 0) =
      ∑ j, (if j ∉ T ∧ insert j T = S then F T j else 0) := by
    intro T
    have : ∀ j ∈ Tᶜ, (if insert j T = S then F T j else 0) =
        (if j ∉ T ∧ insert j T = S then F T j else 0) := by
      intro j hj
      rw [Finset.mem_compl] at hj
      simp [hj]
    rw [Finset.sum_congr rfl this]
    exact Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => by
      rw [Finset.mem_compl, not_not] at hj
      simp [hj])
  simp_rw [h1]
  rw [Finset.sum_comm]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l => l ∈ S)]
  have hfs : Finset.univ.filter (fun l => l ∈ S) = S := by ext; simp
  rw [hfs]
  have h2 : ∀ j ∈ Finset.univ.filter (fun l => l ∉ S),
      ∑ T : Finset (Fin M), (if j ∉ T ∧ insert j T = S then F T j else 0) = 0 := by
    intro j hj
    simp only [Finset.mem_filter] at hj
    refine Finset.sum_eq_zero (fun T _ => ?_)
    rw [if_neg]
    rintro ⟨_, hT⟩
    exact hj.2 (hT ▸ Finset.mem_insert_self j T)
  rw [Finset.sum_eq_zero h2, add_zero]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.sum_eq_single (S.erase j)]
  · rw [if_pos ⟨Finset.notMem_erase j S, Finset.insert_erase hj⟩]
  · intro T _ hT
    rw [if_neg]
    rintro ⟨hjT, hins⟩
    apply hT
    rw [← hins, Finset.erase_insert hjT]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma fwd (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ) (S : Finset (Fin M)) (t : ℝ) :
    HasDerivAt (fun s => U p Q s S)
      (-(totalRate p Q S) * U p Q t S +
        ∑ l ∈ S, adoptRate p Q (S.erase l) l * U p Q t (S.erase l)) t := by
  have hd := dyn p Q (fun S' => if S' = S then 1 else 0) t
  have hf : (fun s => ∑ S', U p Q s S' * (if S' = S then 1 else 0)) = fun s => U p Q s S := by
    funext s; simp
  rw [hf] at hd
  refine hd.congr_deriv ?_
  have e1 : ∀ T, U p Q t T * ∑ j ∈ Tᶜ, adoptRate p Q T j *
      ((if insert j T = S then (1:ℝ) else 0) - (if T = S then 1 else 0)) =
      ∑ j ∈ Tᶜ, (if insert j T = S then adoptRate p Q T j * U p Q t T else 0) -
      (if T = S then U p Q t T * totalRate p Q T else 0) := by
    intro T
    by_cases hT : T = S
    · simp only [hT, if_true, totalRate]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_compl] at hj
      have hne : insert j S ≠ S := Finset.insert_ne_self.mpr hj
      simp only [hne, if_false]
      ring
    · simp only [hT, if_false, sub_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      split_ifs <;> ring
  simp_rw [e1]
  rw [Finset.sum_sub_distrib, comb S (fun T j => adoptRate p Q T j * U p Q t T)]
  simp [Finset.sum_ite_eq']
  ring

lemma adoptRate_nonneg (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hQ : ∀ k j, 0 ≤ Q k j) (T : Finset (Fin M)) (j : Fin M) : 0 ≤ adoptRate p Q T j :=
  add_nonneg (hp j) (Finset.sum_nonneg (fun k _ => hQ k j))

lemma U_nonneg (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hQ : ∀ k j, 0 ≤ Q k j) (S : Finset (Fin M)) : ∀ t, 0 ≤ t → 0 ≤ U p Q t S := by
  induction S using Finset.strongInduction with
  | H S ih =>
    refine IF_nonneg (totalRate p Q S) (fwd p Q S) ?_ ?_
    · rw [U_init]; split_ifs <;> norm_num
    · intro t ht
      exact Finset.sum_nonneg (fun l hl => mul_nonneg (adoptRate_nonneg p Q hp hQ _ _)
        (ih _ (Finset.erase_ssubset hl) t ht.le))

end HBT3

open HeteroBass.HetP

namespace HBT3

variable {M : ℕ}

lemma aR (p : Fin M → ℝ) (q : ℝ) {T : Finset (Fin M)} {j : Fin M} (hj : j ∉ T) :
    adoptRate p (completeQ fun _ : Fin M => q) T j = p j + T.card * (q / ((M:ℝ) - 1)) := by
  simp only [adoptRate, completeQ]
  rw [Finset.sum_congr rfl (g := fun _ => q / ((M:ℝ) - 1))
    (fun k hk => by rw [if_neg (by rintro rfl; exact hj hk)])]
  simp [Finset.sum_const, nsmul_eq_mul]

lemma tR (p : Fin M → ℝ) (q : ℝ) (T : Finset (Fin M)) :
    totalRate p (completeQ fun _ : Fin M => q) T =
      ((∑ l, p l) - ∑ l ∈ T, p l) + ((M:ℝ) - T.card) * (T.card * (q / ((M:ℝ) - 1))) := by
  simp only [totalRate]
  rw [Finset.sum_congr rfl (fun j hj => aR p q (Finset.mem_compl.mp hj))]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_compl, nsmul_eq_mul]
  have h1 := Finset.sum_compl_add_sum T p
  have h2 : ((Fintype.card (Fin M) - T.card : ℕ) : ℝ) = (M:ℝ) - T.card := by
    rw [Nat.cast_sub (by simpa using Finset.card_le_univ T), Fintype.card_fin]
  rw [h2]
  linarith

lemma Q_nonneg (q : ℝ) (hq : 0 ≤ q) (hM : 1 ≤ M) :
    ∀ k j, 0 ≤ (completeQ fun _ : Fin M => q) k j := by
  intro k j
  simp only [completeQ]
  split_ifs
  · exact le_rfl
  · apply div_nonneg hq
    have : (1:ℝ) ≤ M := by exact_mod_cast hM
    linarith

lemma U_empty (p : Fin M → ℝ) (Q : Fin M → Fin M → ℝ) (t : ℝ) :
    U p Q t ∅ = Real.exp (-(totalRate p Q ∅) * t) := by
  refine exp_sol (a := fun s => U p Q s ∅) _ (fun t => ?_) (by rw [U_init]; simp) t
  exact (fwd p Q ∅ t).congr_deriv (by simp)

/-! ### Exchange property -/

section exch
variable (p : Fin M → ℝ) (q : ℝ) (i j : Fin M)

/-- Derivative identity for the difference between a set and its swapped image. -/
lemma exch_deriv (hij : i ≠ j) (S : Finset (Fin M)) (hj : j ∈ S) (hi : i ∉ S) (t : ℝ) :
    HasDerivAt (fun s => U p (completeQ fun _ : Fin M => q) s S -
        U p (completeQ fun _ : Fin M => q) s (S.image (Equiv.swap i j)))
      (-(totalRate p (completeQ fun _ : Fin M => q) (S.image (Equiv.swap i j))) *
          (U p (completeQ fun _ : Fin M => q) t S -
            U p (completeQ fun _ : Fin M => q) t (S.image (Equiv.swap i j))) +
        ((p j - p i) * U p (completeQ fun _ : Fin M => q) t S +
         (p j - p i) * U p (completeQ fun _ : Fin M => q) t (S.erase j) +
         ∑ l ∈ S.erase j, adoptRate p (completeQ fun _ : Fin M => q) (S.erase l) l *
            (U p (completeQ fun _ : Fin M => q) t (S.erase l) -
              U p (completeQ fun _ : Fin M => q) t ((S.erase l).image (Equiv.swap i j))))) t := by
  set σ := Equiv.swap i j with hσ
  set Q := completeQ fun _ : Fin M => q with hQ
  have hinj : Function.Injective σ := σ.injective
  have hcard : (S.image σ).card = S.card := Finset.card_image_of_injective S hinj
  -- sums of p over S and σS
  have hsum : ∑ l ∈ S.image σ, p l = ∑ l ∈ S, p l - p j + p i := by
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    rw [← Finset.add_sum_erase S _ hj, ← Finset.add_sum_erase S _ hj]
    have : ∀ l ∈ S.erase j, p (σ l) = p l := by
      intro l hl
      have hlj : l ≠ j := Finset.ne_of_mem_erase hl
      have hli : l ≠ i := fun h => hi (h ▸ Finset.mem_of_mem_erase hl)
      rw [hσ, Equiv.swap_apply_of_ne_of_ne hli hlj]
    rw [Finset.sum_congr rfl this, hσ, Equiv.swap_apply_right]
    ring
  have htr : totalRate p Q (S.image σ) - totalRate p Q S = p j - p i := by
    rw [hQ, tR, tR, hcard, hsum]; ring
  -- inflow of σS reindexed over S
  have hin : ∑ l ∈ S.image σ, adoptRate p Q ((S.image σ).erase l) l * U p Q t ((S.image σ).erase l) =
      ∑ l ∈ S, adoptRate p Q ((S.erase l).image σ) (σ l) * U p Q t ((S.erase l).image σ) := by
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.image_erase hinj]
  have hfix : (S.erase j).image σ = S.erase j := by
    conv_rhs => rw [← Finset.image_id (s := S.erase j)]
    refine Finset.image_congr (fun l hl => ?_)
    have hlj : l ≠ j := Finset.ne_of_mem_erase hl
    have hli : l ≠ i := fun h => hi (h ▸ Finset.mem_of_mem_erase hl)
    simp [hσ, Equiv.swap_apply_of_ne_of_ne hli hlj]
  have hterm : ∀ l ∈ S,
      adoptRate p Q (S.erase l) l * U p Q t (S.erase l) -
        adoptRate p Q ((S.erase l).image σ) (σ l) * U p Q t ((S.erase l).image σ) =
      (if l = j then (p j - p i) * U p Q t (S.erase j) else
        adoptRate p Q (S.erase l) l * (U p Q t (S.erase l) - U p Q t ((S.erase l).image σ))) := by
    intro l hl
    by_cases hlj : l = j
    · subst hlj
      rw [if_pos rfl, hfix, hσ, Equiv.swap_apply_right]
      have hi' : i ∉ S.erase l := fun h => hi (Finset.mem_of_mem_erase h)
      rw [hQ, aR p q (Finset.notMem_erase l S), aR p q hi']
      ring
    · rw [if_neg hlj]
      have hli : l ≠ i := fun h => hi (h ▸ hl)
      have hσl : σ l = l := by rw [hσ, Equiv.swap_apply_of_ne_of_ne hli hlj]
      rw [hσl]
      have hl1 : l ∉ S.erase l := Finset.notMem_erase l S
      have hl2 : l ∉ (S.erase l).image σ := by
        intro h
        rw [Finset.mem_image] at h
        obtain ⟨x, hx, hxl⟩ := h
        rw [← hσl] at hxl
        exact hl1 (hinj hxl ▸ hx)
      rw [hQ, aR p q hl1, aR p q hl2, Finset.card_image_of_injective _ hinj]
      ring
  have hsplit : ∑ l ∈ S, (if l = j then (p j - p i) * U p Q t (S.erase j) else
        adoptRate p Q (S.erase l) l * (U p Q t (S.erase l) - U p Q t ((S.erase l).image σ))) =
      (p j - p i) * U p Q t (S.erase j) + ∑ l ∈ S.erase j,
        adoptRate p Q (S.erase l) l * (U p Q t (S.erase l) - U p Q t ((S.erase l).image σ)) := by
    rw [← Finset.add_sum_erase S _ hj, if_pos rfl]
    congr 1
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [if_neg (Finset.ne_of_mem_erase hl)]
  refine ((fwd p Q S t).sub (fwd p Q (S.image σ) t)).congr_deriv ?_
  rw [hin]
  have e2 : ∑ l ∈ S, adoptRate p Q (S.erase l) l * U p Q t (S.erase l) -
      ∑ l ∈ S, adoptRate p Q ((S.erase l).image σ) (σ l) * U p Q t ((S.erase l).image σ) =
      (p j - p i) * U p Q t (S.erase j) + ∑ l ∈ S.erase j,
        adoptRate p Q (S.erase l) l * (U p Q t (S.erase l) - U p Q t ((S.erase l).image σ)) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl hterm, hsplit]
  have htr' : totalRate p Q S = totalRate p Q (S.image σ) - (p j - p i) := by linarith
  rw [htr']
  linear_combination e2

lemma exch (hp : ∀ k, 0 ≤ p k) (hq : 0 ≤ q) (hij : i ≠ j) (hpij : p i ≤ p j)
    (S : Finset (Fin M)) (hj : j ∈ S) (hi : i ∉ S) :
    ∀ t, 0 ≤ t → U p (completeQ fun _ : Fin M => q) t (S.image (Equiv.swap i j)) ≤
      U p (completeQ fun _ : Fin M => q) t S := by
  have hM : 1 ≤ M := by have := j.isLt; omega
  induction S using Finset.strongInduction with
  | H S ih =>
    have key := IF_nonneg _ (exch_deriv p q i j hij S hj hi) ?_ ?_
    · intro t ht; have := key t ht; linarith
    · have hS : S ≠ ∅ := Finset.ne_empty_of_mem hj
      have hS' : S.image (Equiv.swap i j) ≠ ∅ := by simpa using hS
      simp [U_init, hS, hS']
    · intro t ht
      have hpos := sub_nonneg.mpr hpij
      have h1 := U_nonneg p _ hp (Q_nonneg q hq hM) S t ht.le
      have h2 := U_nonneg p _ hp (Q_nonneg q hq hM) (S.erase j) t ht.le
      have h3 : 0 ≤ ∑ l ∈ S.erase j, adoptRate p (completeQ fun _ : Fin M => q) (S.erase l) l *
            (U p (completeQ fun _ : Fin M => q) t (S.erase l) -
              U p (completeQ fun _ : Fin M => q) t ((S.erase l).image (Equiv.swap i j))) := by
        refine Finset.sum_nonneg (fun l hl => mul_nonneg
          (adoptRate_nonneg p _ hp (Q_nonneg q hq hM) _ _) (sub_nonneg.mpr ?_))
        have hlS : l ∈ S := Finset.mem_of_mem_erase hl
        have hlj : l ≠ j := Finset.ne_of_mem_erase hl
        exact ih (S.erase l) (Finset.erase_ssubset hlS)
          (Finset.mem_erase.mpr ⟨hlj.symm, hj⟩) (fun h => hi (Finset.mem_of_mem_erase h)) t ht.le
      have := mul_nonneg hpos h1
      have := mul_nonneg hpos h2
      linarith

lemma exch_single (hp : ∀ k, 0 ≤ p k) (hq : 0 ≤ q) (hij : i ≠ j) (hpij : p i < p j) :
    ∀ t, 0 < t → U p (completeQ fun _ : Fin M => q) t {i} <
      U p (completeQ fun _ : Fin M => q) t {j} := by
  have hM : 1 ≤ M := by have := j.isLt; omega
  have himg : ({j} : Finset (Fin M)).image (Equiv.swap i j) = {i} := by simp
  have key := IF_pos _ (exch_deriv p q i j hij {j} (Finset.mem_singleton_self j)
    (by simpa using hij) ) ?_ ?_
  · intro t ht; have := key t ht; rw [himg] at this; linarith
  · simp [U_init, himg]
  · intro t ht
    have hpos := sub_pos.mpr hpij
    have h1 := U_nonneg p _ hp (Q_nonneg q hq hM) {j} t ht.le
    have h2 : 0 < U p (completeQ fun _ : Fin M => q) t (({j} : Finset (Fin M)).erase j) := by
      rw [Finset.erase_singleton, U_empty]; exact Real.exp_pos _
    have := mul_nonneg hpos.le h1
    have := mul_pos hpos h2
    simp only [Finset.erase_singleton, Finset.sum_empty, add_zero] at this ⊢
    simp only [Finset.erase_singleton] at h2
    nlinarith

end exch

end HBT3

open HeteroBass.HetP

namespace HBT3

variable {M : ℕ}

section gap
variable (p : Fin M → ℝ) (q : ℝ) (t : ℝ)

/-- Probability that the adopter set has `k` elements and contains `l`. -/
noncomputable def piK (k : ℕ) (l : Fin M) : ℝ :=
  ∑ T : Finset (Fin M), if T.card = k ∧ l ∈ T then U p (completeQ fun _ : Fin M => q) t T else 0

lemma swap_mem {l m : Fin M} {T : Finset (Fin M)} (hl : l ∈ T) (hm : m ∈ T) (y : Fin M)
    (hy : y ∈ T) : Equiv.swap m l y ∈ T := by
  by_cases hym : y = m
  · subst hym; simpa [Equiv.swap_apply_left] using hl
  · by_cases hyl : y = l
    · subst hyl; simpa [Equiv.swap_apply_right] using hm
    · rw [Equiv.swap_apply_of_ne_of_ne hym hyl]; exact hy

lemma image_swap_eq_self {l m : Fin M} {T : Finset (Fin M)} (hl : l ∈ T) (hm : m ∈ T) :
    T.image (Equiv.swap m l) = T := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact swap_mem hl hm y hy
  · rw [Finset.card_image_of_injective _ (Equiv.swap m l).injective]

lemma piK_mono (hp : ∀ k, 0 ≤ p k) (hq : 0 ≤ q) (k : ℕ) (l m : Fin M) (hlm : p m ≤ p l)
    (ht : 0 ≤ t) : piK p q t k m ≤ piK p q t k l := by
  by_cases hEq : l = m
  · subst hEq; exact le_rfl
  set σ := Equiv.swap m l with hσ
  have hre : piK p q t k m = ∑ T : Finset (Fin M),
      if T.card = k ∧ l ∈ T then U p (completeQ fun _ : Fin M => q) t (T.image σ) else 0 := by
    unfold piK
    refine Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ (fun T => ?_)
    rw [Equiv.finsetCongr_apply]
    have hc : (T.map σ.toEmbedding).card = T.card := Finset.card_map _
    have hmem : l ∈ T.map σ.toEmbedding ↔ m ∈ T := by
      rw [Finset.mem_map_equiv, hσ, Equiv.symm_swap, Equiv.swap_apply_right]
    have hinv : (T.map σ.toEmbedding).image σ = T := by
      rw [Finset.map_eq_image, Finset.image_image]
      have : (⇑σ ∘ ⇑σ.toEmbedding) = id := by
        funext x; simp [hσ]
      rw [this, Finset.image_id]
    simp only [hc, hinv, hmem]
  rw [hre]
  unfold piK
  apply Finset.sum_le_sum
  intro T _
  by_cases h1 : T.card = k ∧ l ∈ T
  · rw [if_pos h1, if_pos h1]
    by_cases hmT : m ∈ T
    · rw [image_swap_eq_self h1.2 hmT]
    · exact exch p q m l hp hq (Ne.symm hEq) hlm T h1.2 hmT t ht
  · rw [if_neg h1, if_neg h1]

lemma gap_eq (hM : 0 < M) (k : ℕ) :
    ∑ T : Finset (Fin M), (if T.card = k then
      U p (completeQ fun _ : Fin M => q) t T * (∑ l ∈ T, p l - k * mean p) else 0) =
      (1 / (2 * M)) * ∑ l, ∑ m, (p l - p m) * (piK p q t k l - piK p q t k m) := by
  have hM' : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have step1 : ∑ T : Finset (Fin M), (if T.card = k then
      U p (completeQ fun _ : Fin M => q) t T * (∑ l ∈ T, p l - k * mean p) else 0) =
      ∑ l, (p l - mean p) * piK p q t k l := by
    have e : ∀ T : Finset (Fin M), (if T.card = k then
        U p (completeQ fun _ : Fin M => q) t T * (∑ l ∈ T, p l - k * mean p) else 0) =
        ∑ l, (p l - mean p) * (if T.card = k ∧ l ∈ T then
          U p (completeQ fun _ : Fin M => q) t T else 0) := by
      intro T
      by_cases h1 : T.card = k
      · simp only [h1, true_and, if_true]
        have : ∑ l, (p l - mean p) * (if l ∈ T then U p (completeQ fun _ : Fin M => q) t T else 0)
            = ∑ l ∈ T, (p l - mean p) * U p (completeQ fun _ : Fin M => q) t T := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l => l ∈ T)]
          have hfs : Finset.univ.filter (fun l => l ∈ T) = T := by ext; simp
          rw [hfs]
          rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun l => l ∉ T))
            (fun l hl => by simp only [Finset.mem_filter] at hl; simp [hl.2])]
          rw [add_zero]
          refine Finset.sum_congr rfl (fun l hl => by simp [hl])
        rw [this, ← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, h1, nsmul_eq_mul]
        ring
      · simp [h1]
    simp_rw [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [piK, Finset.mul_sum]
  rw [step1]
  have hmean : mean p * M = ∑ l, p l := by
    simp only [mean]; field_simp
  have expand : ∑ l, ∑ m, (p l - p m) * (piK p q t k l - piK p q t k m) =
      2 * (M * ∑ l, p l * piK p q t k l - (∑ l, p l) * ∑ l, piK p q t k l) := by
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [expand]
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [← hmean]
  field_simp

/-- The gap term at level `k`. -/
noncomputable def gapK (k : ℕ) : ℝ :=
  ∑ T : Finset (Fin M), (if T.card = k then
      U p (completeQ fun _ : Fin M => q) t T * (∑ l ∈ T, p l - k * mean p) else 0)

lemma gapK_nonneg (hp : ∀ k, 0 ≤ p k) (hq : 0 ≤ q) (hM : 0 < M) (ht : 0 ≤ t) (k : ℕ) :
    0 ≤ gapK p q t k := by
  rw [gapK, gap_eq p q t hM k]
  apply mul_nonneg (by positivity)
  refine Finset.sum_nonneg (fun l _ => Finset.sum_nonneg (fun m _ => ?_))
  rcases le_total (p m) (p l) with h | h
  · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (piK_mono p q t hp hq k l m h ht))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
      (sub_nonpos.mpr (piK_mono p q t hp hq k m l h ht))

lemma piK_one (l : Fin M) : piK p q t 1 l = U p (completeQ fun _ : Fin M => q) t {l} := by
  unfold piK
  rw [Finset.sum_eq_single {l}]
  · simp
  · intro T _ hT
    rw [if_neg]
    rintro ⟨h1, h2⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    rw [Finset.mem_singleton] at h2
    exact hT (by rw [h2])
  · intro h; exact absurd (Finset.mem_univ _) h

lemma gapK_one_pos (hp : ∀ k, 0 ≤ p k) (hq : 0 ≤ q) (hM : 0 < M)
    (hhetero : ∃ i j, p i ≠ p j) (ht : 0 < t) : 0 < gapK p q t 1 := by
  obtain ⟨a, b, hab⟩ := hhetero
  obtain ⟨i, j, hij, hpij⟩ : ∃ i j : Fin M, i ≠ j ∧ p i < p j := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b, fun e => hab (e ▸ rfl), h⟩
    · exact ⟨b, a, fun e => hab (e ▸ rfl), h⟩
  rw [gapK, gap_eq p q t hM 1]
  apply mul_pos (by positivity)
  set F := fun l m : Fin M => (p l - p m) * (piK p q t 1 l - piK p q t 1 m) with hF
  have hnn : ∀ l m, 0 ≤ F l m := by
    intro l m
    rcases le_total (p m) (p l) with h | h
    · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (piK_mono p q t hp hq 1 l m h ht.le))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
        (sub_nonpos.mpr (piK_mono p q t hp hq 1 m l h ht.le))
  have hpos : 0 < F j i := by
    simp only [hF, piK_one]
    exact mul_pos (sub_pos.mpr hpij) (sub_pos.mpr (exch_single p q i j hp hq hij hpij t ht))
  calc (0:ℝ) < F j i := hpos
    _ ≤ ∑ m, F j m := Finset.single_le_sum (fun m _ => hnn j m) (Finset.mem_univ i)
    _ ≤ ∑ l, ∑ m, F l m := Finset.single_le_sum (f := fun l => ∑ m, F l m)
        (fun l _ => Finset.sum_nonneg (fun m _ => hnn l m)) (Finset.mem_univ j)

end gap

end HBT3

open HeteroBass.HetP

namespace HBT3

variable {M : ℕ}

/-- `P(N(t) ≥ m)`. -/
noncomputable def Ptail (p : Fin M → ℝ) (q : ℝ) (t : ℝ) (m : ℕ) : ℝ :=
  ∑ T : Finset (Fin M), U p (completeQ fun _ : Fin M => q) t T * (if m ≤ T.card then 1 else 0)

lemma Ptail_deriv (p : Fin M → ℝ) (q : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (fun s => Ptail p q s m)
      (∑ T : Finset (Fin M), (if T.card + 1 = m then
        U p (completeQ fun _ : Fin M => q) t T * totalRate p (completeQ fun _ : Fin M => q) T
        else 0)) t := by
  refine (dyn p _ (fun T => if m ≤ T.card then (1:ℝ) else 0) t).congr_deriv ?_
  refine Finset.sum_congr rfl (fun T _ => ?_)
  have e : ∀ j ∈ Tᶜ, adoptRate p (completeQ fun _ : Fin M => q) T j *
      ((if m ≤ (insert j T).card then (1:ℝ) else 0) - (if m ≤ T.card then 1 else 0)) =
      adoptRate p (completeQ fun _ : Fin M => q) T j * (if T.card + 1 = m then 1 else 0) := by
    intro j hj
    rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp hj)]
    congr 1
    by_cases h1 : T.card + 1 = m
    · rw [if_pos h1, if_pos (by omega), if_neg (by omega)]; ring
    · rw [if_neg h1]
      by_cases h2 : m ≤ T.card
      · rw [if_pos h2, if_pos (by omega)]; ring
      · rw [if_neg h2, if_neg (by omega)]; ring
  rw [Finset.sum_congr rfl e, ← Finset.sum_mul]
  split_ifs <;> simp [totalRate]

/-- Level-`k` difference of probabilities between the homogeneous and heterogeneous networks. -/
noncomputable def NK (p : Fin M → ℝ) (q : ℝ) (t : ℝ) (k : ℕ) : ℝ :=
  ∑ T : Finset (Fin M), (if T.card = k then
    U (fun _ : Fin M => mean p) (completeQ fun _ : Fin M => q) t T -
      U p (completeQ fun _ : Fin M => q) t T else 0)

noncomputable def lam (p : Fin M → ℝ) (q : ℝ) (k : ℕ) : ℝ :=
  ((M:ℝ) - k) * mean p + ((M:ℝ) - k) * (k * (q / ((M:ℝ) - 1)))

lemma sum_mean (p : Fin M → ℝ) (hM : 0 < M) : ∑ _l : Fin M, mean p = ∑ l, p l := by
  have hM' : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  simp [mean]; field_simp

lemma D_deriv (p : Fin M → ℝ) (q : ℝ) (hM : 0 < M) (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    HasDerivAt (fun s => Ptail (fun _ : Fin M => mean p) q s m - Ptail p q s m)
      (lam p q (m - 1) * NK p q t (m - 1) + gapK p q t (m - 1)) t := by
  refine ((Ptail_deriv _ q m t).sub (Ptail_deriv p q m t)).congr_deriv ?_
  rw [← Finset.sum_sub_distrib, NK, gapK, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  by_cases h : T.card + 1 = m
  · have h' : T.card = m - 1 := by omega
    rw [if_pos h, if_pos h, if_pos h', if_pos h', tR, tR]
    have hs := sum_mean p hM
    simp only [Finset.sum_const, nsmul_eq_mul] at hs ⊢
    rw [hs, lam, h']
    have hmean : (∑ l, p l) = M * mean p := by
      have hM' : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      simp only [mean]; field_simp
    rw [hmean]
    push_cast [Nat.cast_sub hm]
    ring
  · have h' : T.card ≠ m - 1 := by omega
    rw [if_neg h, if_neg h, if_neg h', if_neg h']
    ring

lemma NK_eq (p : Fin M → ℝ) (q : ℝ) (t : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    NK p q t (m - 1) = (Ptail (fun _ : Fin M => mean p) q t (m - 1) - Ptail p q t (m - 1)) -
      (Ptail (fun _ : Fin M => mean p) q t m - Ptail p q t m) := by
  simp only [NK, Ptail]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  by_cases h : T.card = m - 1
  · rw [if_pos h, if_pos (by omega), if_neg (by omega)]; ring
  · rw [if_neg h]
    by_cases h2 : m ≤ T.card
    · rw [if_pos h2, if_pos (by omega)]; ring
    · rw [if_neg h2, if_neg (by omega)]; ring

lemma NK_zero (p : Fin M → ℝ) (q : ℝ) (hM : 0 < M) (t : ℝ) : NK p q t 0 = 0 := by
  simp only [NK, Finset.card_eq_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, U_empty]
  rw [tR, tR, sum_mean p hM]
  simp

lemma gapK_zero (p : Fin M → ℝ) (q : ℝ) (t : ℝ) : gapK p q t 0 = 0 := by
  simp only [gapK, Finset.card_eq_zero]
  rw [Finset.sum_ite_eq']
  simp

lemma Ptail_init (p : Fin M → ℝ) (q : ℝ) (m : ℕ) (hm : 1 ≤ m) : Ptail p q 0 m = 0 := by
  simp only [Ptail, U_init]
  refine Finset.sum_eq_zero (fun T _ => ?_)
  by_cases h : T = ∅
  · subst h; simp; omega
  · simp [h]

lemma lam_pos (p : Fin M → ℝ) (q : ℝ) (hp : ∀ k, 0 ≤ p k) (hq : 0 < q) (k : ℕ)
    (hk1 : 1 ≤ k) (hkM : k + 1 ≤ M) : 0 < lam p q k := by
  have hM1 : (1:ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  have hkM' : (k:ℝ) + 1 ≤ M := by exact_mod_cast hkM
  have hk1' : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have hmean : 0 ≤ mean p := by
    simp only [mean]; exact div_nonneg (Finset.sum_nonneg (fun l _ => hp l)) (by positivity)
  have hc : 0 < q / ((M:ℝ) - 1) := div_pos hq (by linarith)
  unfold lam
  have h1 : 0 < (M:ℝ) - k := by linarith
  have : 0 < ((M:ℝ) - k) * (k * (q / ((M:ℝ) - 1))) := mul_pos h1 (mul_pos (by linarith) hc)
  nlinarith [mul_nonneg h1.le hmean]

lemma D1_zero (p : Fin M → ℝ) (q : ℝ) (hM : 0 < M) :
    ∀ t, Ptail (fun _ : Fin M => mean p) q t 1 - Ptail p q t 1 = 0 := by
  intro t
  have := const_of_deriv (y := fun s => Ptail (fun _ : Fin M => mean p) q s 1 - Ptail p q s 1)
    (fun s => (D_deriv p q hM 1 le_rfl s).congr_deriv (by simp [NK_zero p q hM, gapK_zero]))
  rw [this t]
  simp [Ptail_init _ q 1 le_rfl]

lemma D_pos (p : Fin M → ℝ) (q : ℝ) (hp : ∀ k, 0 ≤ p k) (hq : 0 < q)
    (hhetero : ∃ i j, p i ≠ p j) :
    ∀ m, 2 ≤ m → m ≤ M → ∀ t, 0 < t →
      0 < Ptail (fun _ : Fin M => mean p) q t m - Ptail p q t m := by
  have hM : 0 < M := by
    obtain ⟨i, _, _⟩ := hhetero; exact Fin.pos i
  have hD1 := D1_zero p q hM
  intro m hm2
  induction m, hm2 using Nat.le_induction with
  | base =>
    intro _ t ht
    refine IF_pos (lam p q 1) (y := fun s => Ptail (fun _ : Fin M => mean p) q s 2 - Ptail p q s 2) (g := fun s => gapK p q s 1) (fun s => ?_) ?_ ?_ t ht
    · refine (D_deriv p q hM 2 (by norm_num) s).congr_deriv ?_
      simp only [show (2:ℕ) - 1 = 1 by rfl]
      rw [NK_eq p q s 2 (by norm_num), hD1]
      ring
    · simp [Ptail_init _ q 2 (by norm_num), Ptail_init p q 2 (by norm_num)]
    · intro s hs
      exact gapK_one_pos p q s hp hq.le hM hhetero hs
  | succ m hm ih =>
    intro hmM t ht
    have hD := ih (by omega)
    refine IF_pos (lam p q m) (y := fun s => Ptail (fun _ : Fin M => mean p) q s (m + 1) - Ptail p q s (m + 1)) (g := fun s => lam p q m *
        (Ptail (fun _ : Fin M => mean p) q s m - Ptail p q s m) + gapK p q s m)
      (fun s => ?_) ?_ ?_ t ht
    · refine (D_deriv p q hM (m + 1) (by omega) s).congr_deriv ?_
      simp only [Nat.add_sub_cancel]
      rw [show m = m + 1 - 1 by omega, NK_eq p q s (m + 1) (by omega)]
      simp only [Nat.add_sub_cancel]
      ring
    · simp [Ptail_init _ q (m + 1) (by omega), Ptail_init p q (m + 1) (by omega)]
    · intro s hs
      have h1 := lam_pos p q hp hq m (by omega) (by omega)
      have h2 := hD s hs
      have h3 := gapK_nonneg p q s hp hq.le hM hs.le m
      positivity

lemma card_sum (k M : ℕ) (hk : k ≤ M) :
    ∑ m ∈ Finset.Icc 1 M, (if m ≤ k then (1:ℝ) else 0) = k := by
  rw [Finset.sum_boole]
  have : (Finset.Icc 1 M).filter (fun m => m ≤ k) = Finset.Icc 1 k := by
    ext m; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]
  simp

lemma ef_tails (p : Fin M → ℝ) (q : ℝ) (t : ℝ) :
    expectedFraction p (completeQ fun _ : Fin M => q) t =
      (1 / (M:ℝ)) * ∑ m ∈ Finset.Icc 1 M, Ptail p q t m := by
  simp only [expectedFraction, Ptail]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [← Finset.mul_sum, mul_comm]
  congr 1
  have hk : T.card ≤ M := by simpa using Finset.card_le_univ T
  rw [card_sum _ _ hk]

end HBT3

open HBT3 in
theorem solution (M : ℕ) (p : Fin M → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hhetero : ∃ i j, p i ≠ p j)
    (q : ℝ) (hq : 0 < q) (t : ℝ) (ht : 0 < t) :
    expectedFraction p (completeQ (fun _ : Fin M => q)) t <
      expectedFraction (fun _ : Fin M => mean p)
        (completeQ (fun _ : Fin M => q)) t := by
  have hM2 : 2 ≤ M := by
    obtain ⟨i, j, hij⟩ := hhetero
    have : i ≠ j := fun h => hij (h ▸ rfl)
    by_contra h
    push Not at h
    interval_cases M
    · exact i.elim0
    · exact this (Subsingleton.elim i j)
  have hM : 0 < M := by omega
  rw [ef_tails, ef_tails]
  have hMpos : (0:ℝ) < 1 / (M:ℝ) := by positivity
  have key : 0 < ∑ m ∈ Finset.Icc 1 M,
      (Ptail (fun _ : Fin M => mean p) q t m - Ptail p q t m) := by
    apply Finset.sum_pos'
    · intro m hm
      rw [Finset.mem_Icc] at hm
      by_cases h1 : m = 1
      · subst h1; rw [D1_zero p q hM t]
      · exact (D_pos p q hp hq hhetero m (by omega) hm.2 t ht).le
    · exact ⟨2, Finset.mem_Icc.mpr ⟨by norm_num, hM2⟩, D_pos p q hp hq hhetero 2 le_rfl hM2 t ht⟩
  rw [Finset.sum_sub_distrib] at key
  nlinarith
