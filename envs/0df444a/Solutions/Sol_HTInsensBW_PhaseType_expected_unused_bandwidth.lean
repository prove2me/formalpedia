-- Prove2me | solution 1 for HTInsensBW.PhaseType.expected_unused_bandwidth
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T22:04:51.518171+00:00
-- url     : https://prove2.me/submissions/7b4ff531-b6c6-400b-bc9a-0f37cebc238c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model
import Theorems.Thm_HTInsensBW_PhaseType_lemma_7

namespace HTInsensBWEUB

open HTInsensBW.PhaseType Matrix Finset

lemma subgen_mulVec_apply (D : PhaseTypeD) (v : Phase D → ℝ) (b : Fin D.B) (i : Fin (D.len b)) :
    (subgen D *ᵥ v) ⟨b, i⟩ =
      D.rate b * ((if h : (i : ℕ) + 1 < D.len b then v ⟨b, ⟨i + 1, h⟩⟩ else 0) - v ⟨b, i⟩) := by
  simp only [mulVec, dotProduct, subgen, Matrix.of_apply]
  rw [Fintype.sum_sigma, Finset.sum_eq_single b]
  · have e : ∀ j : Fin (D.len b),
        ((if b = b ∧ (j : ℕ) = i then -D.rate b
          else if b = b ∧ (j : ℕ) = i + 1 then D.rate b else 0) * v ⟨b, j⟩) =
        (if j = i then -D.rate b * v ⟨b, j⟩ else 0) +
        (if (j : ℕ) = i + 1 then D.rate b * v ⟨b, j⟩ else 0) := by
      intro j
      by_cases h1 : j = i
      · subst h1; simp
      · have h1' : (j : ℕ) ≠ i := fun h => h1 (Fin.ext h)
        simp [h1, h1']
    simp only [true_and] at e ⊢
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_ite_eq' ]
    simp only [Finset.mem_univ, if_true]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i + 1, h⟩]
      · simp; ring
      · intro j _ hj
        have : (j : ℕ) ≠ i + 1 := fun h' => hj (Fin.ext h')
        simp [this]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · rw [Finset.sum_eq_zero]
      · ring
      · intro j _
        have : (j : ℕ) ≠ i + 1 := by
          intro h'; apply h; rw [← h']; exact j.2
        simp [this]
  · intro b' _ hne
    apply Finset.sum_eq_zero
    intro j _
    have : ¬ (b = b') := fun h => hne h.symm
    simp [this]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- the expected-remaining-work vector `(-S)^{-1} 1` -/
noncomputable def cvec (D : PhaseTypeD) : Phase D → ℝ :=
  fun k => ((D.len k.1 : ℝ) - (k.2 : ℕ)) / D.rate k.1

lemma cvec_nonneg (D : PhaseTypeD) (k : Phase D) : 0 ≤ cvec D k := by
  unfold cvec
  have h1 : ((k.2 : ℕ) : ℝ) ≤ D.len k.1 := by exact_mod_cast k.2.2.le
  exact div_nonneg (by linarith) (D.rate_pos _).le

lemma subgen_cvec (D : PhaseTypeD) : subgen D *ᵥ cvec D = fun _ => -1 := by
  funext ⟨b, i⟩
  rw [subgen_mulVec_apply]
  have hμ := (D.rate_pos b).ne'
  split_ifs with h
  · simp only [cvec]; push_cast; field_simp; ring
  · have hi : (i : ℕ) + 1 = D.len b := by have := i.2; omega
    simp only [cvec]
    have : (D.len b : ℝ) = (i : ℕ) + 1 := by exact_mod_cast hi.symm
    rw [this]; field_simp; ring

lemma subgen_ker (D : PhaseTypeD) (v : Phase D → ℝ) (hv : subgen D *ᵥ v = 0) : v = 0 := by
  funext ⟨b, i⟩
  have hrec : ∀ i : Fin (D.len b),
      v ⟨b, i⟩ = if h : (i : ℕ) + 1 < D.len b then v ⟨b, ⟨i + 1, h⟩⟩ else 0 := by
    intro i
    have := congrFun hv ⟨b, i⟩
    rw [subgen_mulVec_apply] at this
    simp only [Pi.zero_apply, mul_eq_zero, (D.rate_pos b).ne', false_or] at this
    linarith
  have key : ∀ d : ℕ, ∀ i : Fin (D.len b), D.len b - 1 - (i : ℕ) = d → v ⟨b, i⟩ = 0 := by
    intro d
    induction d with
    | zero =>
      intro i hi
      rw [hrec i, dif_neg]
      omega
    | succ d ih =>
      intro i hi
      have h : (i : ℕ) + 1 < D.len b := by omega
      rw [hrec i, dif_pos h]
      exact ih ⟨i + 1, h⟩ (by simp; omega)
  exact key _ i rfl

lemma subgen_injective (D : PhaseTypeD) : Function.Injective (subgen D).mulVec := by
  intro v w h
  have : subgen D *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 h
  exact sub_eq_zero.1 (subgen_ker D _ this)

lemma neg_subgen_isUnit (D : PhaseTypeD) : IsUnit (-subgen D) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w h
  apply subgen_injective D
  have : -(subgen D *ᵥ v) = -(subgen D *ᵥ w) := by
    rw [← Matrix.neg_mulVec, ← Matrix.neg_mulVec]; exact h
  exact neg_injective this

lemma inv_one_eq_cvec (D : PhaseTypeD) : (-subgen D)⁻¹ *ᵥ (fun _ => (1 : ℝ)) = cvec D := by
  have hu := neg_subgen_isUnit D
  have hc : (-subgen D) *ᵥ cvec D = fun _ => 1 := by
    rw [Matrix.neg_mulVec, subgen_cvec]; funext; simp
  rw [← hc, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu),
    Matrix.one_mulVec]

lemma meanSize_eq (D : PhaseTypeD) : meanSize D = D.init ⬝ᵥ cvec D := by
  rw [meanSize, inv_one_eq_cvec]


/-- Steady-state drift is zero (generic, nonnegative rates and nonnegative `V`). -/
lemma stationary_drift_zero {S : Type*} (q : S → S → ℝ) (π : S → ℝ) (hπ : IsStationary q π)
    (hq0 : ∀ i j, 0 ≤ q i j) (V : S → ℝ) (hV0 : ∀ i, 0 ≤ V i)
    (hqs : ∀ i, Summable (q i)) (hqVs : ∀ i, Summable (fun j => q i j * V j))
    (hA : Summable (fun i => π i * ∑' j, q i j * V j))
    (hB : Summable (fun i => π i * V i * ∑' j, q i j)) :
    Summable (fun i => π i * drift q V i) ∧ ∑' i, π i * drift q V i = 0 := by
  have hπ0 := hπ.1
  have hdr : ∀ i, π i * drift q V i = π i * ∑' j, q i j * V j - π i * V i * ∑' j, q i j := by
    intro i
    unfold drift
    have : ∑' j, q i j * (V j - V i) = ∑' j, q i j * V j - V i * ∑' j, q i j := by
      have e : (fun j => q i j * (V j - V i)) = fun j => q i j * V j - q i j * V i := by
        funext j; ring
      rw [e, Summable.tsum_sub (hqVs i) ((hqs i).mul_right _), tsum_mul_right]; ring
    rw [this]; ring
  simp_rw [hdr]
  refine ⟨hA.sub hB, ?_⟩
  rw [Summable.tsum_sub hA hB, sub_eq_zero]
  set F : S → S → ℝ := fun i j => π i * q i j * V j with hF
  have hF0 : ∀ i j, 0 ≤ F i j := fun i j => mul_nonneg (mul_nonneg (hπ0 i) (hq0 i j)) (hV0 j)
  have hFrow : ∀ i, Summable (F i) := fun i => by
    have := (hqVs i).mul_left (π i)
    refine this.congr (fun j => ?_); simp only [hF]; ring
  have hFrowsum : ∀ i, ∑' j, F i j = π i * ∑' j, q i j * V j := fun i => by
    rw [← tsum_mul_left]; apply tsum_congr; intro j; simp only [hF]; ring
  have hFu : Summable (Function.uncurry F) := by
    rw [summable_prod_of_nonneg (f := Function.uncurry F) (fun p => hF0 p.1 p.2)]
    refine ⟨fun i => hFrow i, ?_⟩
    refine hA.congr (fun i => ?_)
    simp only [Function.uncurry]
    rw [hFrowsum]
  have hFcol : ∀ j, Summable (fun i => F i j) := by
    intro j
    have := hFu.prod_symm.prod_factor j
    simpa [Function.uncurry] using this
  have h1 : ∑' i, π i * ∑' j, q i j * V j = ∑' i, ∑' j, F i j := by
    apply tsum_congr; intro i; rw [hFrowsum]
  rw [h1, ← Summable.tsum_comm' hFu hFrow hFcol]
  apply tsum_congr
  intro j
  have : ∑' i, F i j = V j * ∑' i, π i * q i j := by
    rw [← tsum_mul_left]; apply tsum_congr; intro i; simp only [hF]; ring
  rw [this, ← hπ.2.2 j]; ring

variable {L R : ℕ}

/-- The rates without the diagonal guard. -/
noncomputable def Fr (N : BWNetwork L R) (x : (Fin R → ℕ) → Fin R → ℝ) (ε : ℝ) (n n' : State N) : ℝ :=
  (∑ i : Idx N, if n' = addOne N n i then (1 - ε) * N.lam0 i.1 * (N.D i.1).init i.2 else 0)
    + (∑ r : Fin R, ∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
        if k₁ ≠ k₂ ∧ 0 < n ⟨r, k₁⟩ ∧ n' = addOne N (subOne N n ⟨r, k₁⟩) ⟨r, k₂⟩
        then (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * subgen (N.D r) k₁ k₂ else 0)
    + (∑ i : Idx N, if 0 < n i ∧ n' = subOne N n i
        then (n i : ℝ) * x (routeCount N n) i.1 * exitRate (N.D i.1) i.2 else 0)

lemma addOne_ne (N : BWNetwork L R) (n : State N) (i : Idx N) : addOne N n i ≠ n := by
  intro h
  have := congrFun h i
  simp [addOne] at this

lemma subOne_ne (N : BWNetwork L R) (n : State N) (i : Idx N) (h : 0 < n i) : subOne N n i ≠ n := by
  intro h'
  have := congrFun h' i
  simp [subOne] at this
  omega

lemma move_ne (N : BWNetwork L R) (n : State N) (i j : Idx N) (hij : i ≠ j) :
    addOne N (subOne N n i) j ≠ n := by
  intro h'
  have := congrFun h' j
  simp [addOne, subOne, Function.update_apply, Ne.symm hij] at this

lemma rates_eq_Fr (N : BWNetwork L R) (x : (Fin R → ℕ) → Fin R → ℝ) (ε : ℝ) (n n' : State N) :
    rates N x ε n n' = Fr N x ε n n' := by
  unfold rates
  split_ifs with h
  · subst h
    unfold Fr
    symm
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, Finset.sum_eq_zero]
    · simp
    · intro i _
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact subOne_ne N n' i h1 h2.symm
    · intro r _
      apply Finset.sum_eq_zero; intro k₁ _
      apply Finset.sum_eq_zero; intro k₂ _
      rw [if_neg]
      rintro ⟨h1, _, h3⟩
      exact move_ne N n' ⟨r, k₁⟩ ⟨r, k₂⟩ (by intro h; apply h1; exact eq_of_heq (Sigma.mk.inj h).2) h3.symm
    · intro i _
      rw [if_neg]
      intro h
      exact addOne_ne N n' i h.symm
  · rfl

/-- The weighted rate sum `Σ_{n'} q(n,n') g(n')` in closed form. -/
noncomputable def rateSum (N : BWNetwork L R) (x : (Fin R → ℕ) → Fin R → ℝ) (ε : ℝ) (n : State N)
    (g : State N → ℝ) : ℝ :=
  (∑ i : Idx N, (1 - ε) * N.lam0 i.1 * (N.D i.1).init i.2 * g (addOne N n i))
    + (∑ r : Fin R, ∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
        if k₁ ≠ k₂ ∧ 0 < n ⟨r, k₁⟩
        then (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * subgen (N.D r) k₁ k₂ *
          g (addOne N (subOne N n ⟨r, k₁⟩) ⟨r, k₂⟩) else 0)
    + (∑ i : Idx N, if 0 < n i
        then (n i : ℝ) * x (routeCount N n) i.1 * exitRate (N.D i.1) i.2 * g (subOne N n i) else 0)

lemma hasSum_rates (N : BWNetwork L R) (x : (Fin R → ℕ) → Fin R → ℝ) (ε : ℝ) (n : State N)
    (g : State N → ℝ) :
    HasSum (fun n' => rates N x ε n n' * g n') (rateSum N x ε n g) := by
  classical
  simp_rw [rates_eq_Fr]
  unfold Fr rateSum
  simp_rw [add_mul, Finset.sum_mul]
  refine (HasSum.add (HasSum.add ?_ ?_) ?_)
  · apply hasSum_sum
    intro i _
    have e : (fun n' => (if n' = addOne N n i then (1 - ε) * N.lam0 i.1 * (N.D i.1).init i.2 else 0) * g n')
        = fun n' => if n' = addOne N n i then (1 - ε) * N.lam0 i.1 * (N.D i.1).init i.2 * g (addOne N n i) else 0 := by
      funext n'; split_ifs with h <;> simp [h]
    rw [e]; exact hasSum_ite_eq _ _
  · apply hasSum_sum; intro r _
    apply hasSum_sum; intro k₁ _
    apply hasSum_sum; intro k₂ _
    set t := addOne N (subOne N n ⟨r, k₁⟩) ⟨r, k₂⟩
    have e : (fun n' => (if k₁ ≠ k₂ ∧ 0 < n ⟨r, k₁⟩ ∧ n' = t
          then (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * subgen (N.D r) k₁ k₂ else 0) * g n')
        = fun n' => if n' = t then (if k₁ ≠ k₂ ∧ 0 < n ⟨r, k₁⟩
          then (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * subgen (N.D r) k₁ k₂ * g t else 0) else 0 := by
      funext n'
      by_cases h : n' = t
      · subst h; by_cases h2 : k₁ ≠ k₂ ∧ 0 < n ⟨r, k₁⟩ <;> simp [h2]
      · simp [h]
    rw [e]; exact hasSum_ite_eq _ _
  · apply hasSum_sum
    intro i _
    have e : (fun n' => (if 0 < n i ∧ n' = subOne N n i
          then (n i : ℝ) * x (routeCount N n) i.1 * exitRate (N.D i.1) i.2 else 0) * g n')
        = fun n' => if n' = subOne N n i then (if 0 < n i
          then (n i : ℝ) * x (routeCount N n) i.1 * exitRate (N.D i.1) i.2 * g (subOne N n i) else 0) else 0 := by
      funext n'
      by_cases h : n' = subOne N n i
      · subst h; by_cases h2 : 0 < n i <;> simp [h2]
      · simp [h]
    rw [e]; exact hasSum_ite_eq _ _


lemma exitRate_eq (D : PhaseTypeD) (k : Phase D) :
    exitRate D k = -(subgen D *ᵥ (fun _ => (1 : ℝ))) k := by
  simp [exitRate, mulVec, dotProduct]

lemma exitRate_nonneg (D : PhaseTypeD) (k : Phase D) : 0 ≤ exitRate D k := by
  obtain ⟨b, i⟩ := k
  rw [exitRate_eq, subgen_mulVec_apply]
  have := D.rate_pos b
  split_ifs <;> nlinarith

lemma subgen_offdiag_nonneg (D : PhaseTypeD) (k₁ k₂ : Phase D) (h : k₁ ≠ k₂) :
    0 ≤ subgen D k₁ k₂ := by
  obtain ⟨b, i⟩ := k₁
  obtain ⟨b', j⟩ := k₂
  simp only [subgen, Matrix.of_apply]
  split_ifs with h1 h2
  · exfalso; apply h
    obtain ⟨rfl, h1⟩ := h1
    have : j = i := Fin.ext h1
    rw [this]
  · exact (D.rate_pos _).le
  · exact le_rfl

variable {L R : ℕ}

/-- The linear Lyapunov function `Σ_{r,k} a_{r,k} n_{r,k}`. -/
noncomputable def linV (N : BWNetwork L R) (a : Idx N → ℝ) (n : State N) : ℝ :=
  ∑ i, a i * (n i : ℝ)

lemma linV_update (N : BWNetwork L R) (a : Idx N → ℝ) (n : State N) (i : Idx N) (v : ℕ) :
    linV N a (Function.update n i v) = linV N a n + a i * ((v : ℝ) - n i) := by
  classical
  unfold linV
  have : ∑ j, a j * ((Function.update n i v j : ℕ) : ℝ) - ∑ j, a j * (n j : ℝ) =
      a i * ((v : ℝ) - n i) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp; ring
    · intro j _ hj; simp [Function.update_apply, hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  linarith

lemma linV_addOne (N : BWNetwork L R) (a : Idx N → ℝ) (n : State N) (i : Idx N) :
    linV N a (addOne N n i) = linV N a n + a i := by
  rw [addOne, linV_update]; push_cast; ring

lemma linV_subOne (N : BWNetwork L R) (a : Idx N → ℝ) (n : State N) (i : Idx N) (h : 0 < n i) :
    linV N a (subOne N n i) = linV N a n - a i := by
  rw [subOne, linV_update]
  have : ((n i - 1 : ℕ) : ℝ) = (n i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [this]; ring

lemma linV_move (N : BWNetwork L R) (a : Idx N → ℝ) (n : State N) (i j : Idx N) (hij : i ≠ j)
    (h : 0 < n i) :
    linV N a (addOne N (subOne N n i) j) = linV N a n - a i + a j := by
  rw [linV_addOne, linV_subOne N a n i h]


/-- coefficients `h_ℓr (-S_r)^{-1} 1` of the linear Lyapunov function `w_ℓ`. -/
noncomputable def aL (N : BWNetwork L R) (ℓ : Fin L) : Idx N → ℝ :=
  fun i => N.H ℓ i.1 * cvec (N.D i.1) i.2

lemma rateSum_linV (N : BWNetwork L R) (x : (Fin R → ℕ) → Fin R → ℝ) (ε : ℝ) (n : State N)
    (ℓ : Fin L) :
    rateSum N x ε n (fun n' => linV N (aL N ℓ) n' - linV N (aL N ℓ) n) =
      (1 - ε) * ∑ r, N.H ℓ r * routeLoad0 N r -
        ∑ r, N.H ℓ r * (routeCount N n r : ℝ) * x (routeCount N n) r := by
  classical
  set a := aL N ℓ with ha
  unfold rateSum
  have T1 : ∑ i : Idx N, (1 - ε) * N.lam0 i.1 * (N.D i.1).init i.2 *
      (linV N a (addOne N n i) - linV N a n) = (1 - ε) * ∑ r, N.H ℓ r * routeLoad0 N r := by
    simp_rw [linV_addOne, add_sub_cancel_left]
    rw [Fintype.sum_sigma, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [routeLoad0, meanSize_eq]
    simp only [dotProduct, ha, aL, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have T2 : (∑ r : Fin R, ∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
        if k₁ ≠ k₂ ∧ 0 < n ⟨r, k₁⟩
        then (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * subgen (N.D r) k₁ k₂ *
          (linV N a (addOne N (subOne N n ⟨r, k₁⟩) ⟨r, k₂⟩) - linV N a n) else 0) =
      ∑ r : Fin R, ∑ k₁ : Phase (N.D r), (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * N.H ℓ r *
        ∑ k₂ : Phase (N.D r), subgen (N.D r) k₁ k₂ *
          (cvec (N.D r) k₂ - cvec (N.D r) k₁) := by
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro k₁ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k₂ _
    by_cases hc : k₁ ≠ k₂ ∧ 0 < n ⟨r, k₁⟩
    · rw [if_pos hc, linV_move N a n ⟨r, k₁⟩ ⟨r, k₂⟩ (by
        intro h; apply hc.1; exact eq_of_heq (Sigma.mk.inj h).2) hc.2]
      simp only [ha, aL]; ring
    · rw [if_neg hc]
      rcases not_and_or.1 hc with h | h
      · push_neg at h; subst h; ring
      · have : n ⟨r, k₁⟩ = 0 := by omega
        simp [this]
  have T3 : (∑ i : Idx N, if 0 < n i
        then (n i : ℝ) * x (routeCount N n) i.1 * exitRate (N.D i.1) i.2 *
          (linV N a (subOne N n i) - linV N a n) else 0) =
      ∑ r : Fin R, ∑ k₁ : Phase (N.D r), (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * N.H ℓ r *
        (-(exitRate (N.D r) k₁ * cvec (N.D r) k₁)) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro k₁ _
    by_cases hc : 0 < n ⟨r, k₁⟩
    · rw [if_pos hc, linV_subOne N a n _ hc]
      simp only [ha, aL]; ring
    · rw [if_neg hc]
      have : n ⟨r, k₁⟩ = 0 := by omega
      simp [this]
  rw [T1, T2, T3, add_assoc, ← Finset.sum_add_distrib]
  have hinner : ∀ r : Fin R, ∀ k₁ : Phase (N.D r),
      (∑ k₂ : Phase (N.D r), subgen (N.D r) k₁ k₂ * (cvec (N.D r) k₂ - cvec (N.D r) k₁)) +
        -(exitRate (N.D r) k₁ * cvec (N.D r) k₁) = -1 := by
    intro r k₁
    have h1 := congrFun (subgen_cvec (N.D r)) k₁
    have h2 := exitRate_eq (N.D r) k₁
    simp only [mulVec, dotProduct] at h1 h2
    rw [h2]
    simp only [mul_sub, Finset.sum_sub_distrib, mul_one]
    rw [← Finset.sum_mul] at *
    linarith [h1]
  have e : ∀ r : Fin R, (∑ k₁ : Phase (N.D r), (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * N.H ℓ r *
        ∑ k₂ : Phase (N.D r), subgen (N.D r) k₁ k₂ * (cvec (N.D r) k₂ - cvec (N.D r) k₁)) +
      (∑ k₁ : Phase (N.D r), (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * N.H ℓ r *
        (-(exitRate (N.D r) k₁ * cvec (N.D r) k₁))) =
      -(N.H ℓ r * (routeCount N n r : ℝ) * x (routeCount N n) r) := by
    intro r
    rw [← Finset.sum_add_distrib]
    calc _ = ∑ k₁ : Phase (N.D r), -((n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * N.H ℓ r) := by
          apply Finset.sum_congr rfl; intro k₁ _
          rw [← mul_add, hinner r k₁]; ring
      _ = _ := by
          rw [Finset.sum_neg_distrib]
          congr 1
          rw [routeCount, Nat.cast_sum, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro k _; ring
  rw [Finset.sum_congr rfl (fun r _ => e r), Finset.sum_neg_distrib]
  ring


lemma x_nonneg' (N : BWNetwork L R) (m : Fin R → ℕ) (x : Fin R → ℝ)
    (hx : IsWPFAllocation N m x) (r : Fin R) : 0 ≤ x r := by
  rcases Nat.eq_zero_or_pos (m r) with h | h
  · exact (hx.1 r h).ge
  · exact (hx.2.1 r h).le

lemma rates_nonneg (N : BWNetwork L R) (x : (Fin R → ℕ) → Fin R → ℝ)
    (hx : ∀ m, IsWPFAllocation N m (x m)) (hlam0 : ∀ r, 0 < N.lam0 r) (ε : ℝ) (hε1 : ε < 1)
    (n n' : State N) : 0 ≤ rates N x ε n n' := by
  rw [rates_eq_Fr]
  unfold Fr
  have hxn := fun r => x_nonneg' N _ _ (hx (routeCount N n)) r
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · apply Finset.sum_nonneg; intro i _
    split_ifs
    · have := (N.D i.1).init_nonneg i.2
      have := hlam0 i.1
      have : 0 ≤ 1 - ε := by linarith
      positivity
    · exact le_rfl
  · apply Finset.sum_nonneg; intro r _
    apply Finset.sum_nonneg; intro k₁ _
    apply Finset.sum_nonneg; intro k₂ _
    split_ifs with h
    · have := subgen_offdiag_nonneg (N.D r) k₁ k₂ h.1
      have := hxn r
      positivity
    · exact le_rfl
  · apply Finset.sum_nonneg; intro i _
    split_ifs
    · have := exitRate_nonneg (N.D i.1) i.2
      have := hxn i.1
      positivity
    · exact le_rfl

lemma nx_le (N : BWNetwork L R) (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) (n : State N)
    (i : Idx N) : (n i : ℝ) * x (routeCount N n) i.1 ≤ ∑ ℓ, N.C ℓ := by
  obtain ⟨ℓ, hℓ⟩ := hroute i.1
  have hxn := fun r => x_nonneg' N _ _ (hx (routeCount N n)) r
  have hterm : ∀ r, 0 ≤ N.H ℓ r * (routeCount N n r : ℝ) * x (routeCount N n) r := by
    intro r
    have hH : 0 ≤ N.H ℓ r := by rcases hH01 ℓ r with h | h <;> simp [h]
    have := hxn r
    positivity
  have h1 : N.H ℓ i.1 * (routeCount N n i.1 : ℝ) * x (routeCount N n) i.1 ≤ N.C ℓ :=
    (Finset.single_le_sum (f := fun r => N.H ℓ r * (routeCount N n r : ℝ) * x (routeCount N n) r)
      (fun r _ => hterm r) (Finset.mem_univ i.1)).trans ((hx (routeCount N n)).2.2.1 ℓ)
  rw [hℓ, one_mul] at h1
  have h2 : (n i : ℝ) ≤ routeCount N n i.1 := by
    unfold routeCount
    exact_mod_cast Finset.single_le_sum (f := fun k => n ⟨i.1, k⟩) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i.2)
  have h3 : N.C ℓ ≤ ∑ ℓ, N.C ℓ := Finset.single_le_sum (fun ℓ _ => (hC ℓ).le) (Finset.mem_univ ℓ)
  have := hxn i.1
  nlinarith

/-- a uniform bound on the total outgoing rate -/
lemma rateSum_one_le (N : BWNetwork L R) (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ) (hlam0 : ∀ r, 0 < N.lam0 r)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (n : State N) :
    rateSum N x ε n (fun _ => 1) ≤
      (∑ i : Idx N, N.lam0 i.1 * (N.D i.1).init i.2) +
      (∑ r : Fin R, ∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
        (∑ ℓ, N.C ℓ) * |subgen (N.D r) k₁ k₂|) +
      (∑ i : Idx N, (∑ ℓ, N.C ℓ) * exitRate (N.D i.1) i.2) := by
  unfold rateSum
  have hnx := nx_le N hH01 hroute hC x hx n
  have hxn := fun r => x_nonneg' N _ _ (hx (routeCount N n)) r
  refine add_le_add (add_le_add ?_ ?_) ?_
  · apply Finset.sum_le_sum; intro i _
    have := (N.D i.1).init_nonneg i.2
    have := hlam0 i.1
    have : 0 ≤ N.lam0 i.1 * (N.D i.1).init i.2 := by positivity
    nlinarith
  · apply Finset.sum_le_sum; intro r _
    apply Finset.sum_le_sum; intro k₁ _
    apply Finset.sum_le_sum; intro k₂ _
    split_ifs with h
    · rw [mul_one]
      have h1 := hnx ⟨r, k₁⟩
      have h2 : (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * subgen (N.D r) k₁ k₂ ≤
          (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * |subgen (N.D r) k₁ k₂| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by have := hxn r; positivity)
      exact h2.trans (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
    · exact mul_nonneg (Finset.sum_nonneg (fun ℓ _ => (hC ℓ).le)) (abs_nonneg _)
  · apply Finset.sum_le_sum; intro i _
    split_ifs with h
    · rw [mul_one]
      exact mul_le_mul_of_nonneg_right (hnx i) (exitRate_nonneg _ _)
    · exact mul_nonneg (Finset.sum_nonneg (fun ℓ _ => (hC ℓ).le)) (exitRate_nonneg _ _)

lemma rateSum_affine (N : BWNetwork L R) (x : (Fin R → ℕ) → Fin R → ℝ) (ε : ℝ) (n : State N)
    (g : State N → ℝ) (c : ℝ) :
    rateSum N x ε n g = rateSum N x ε n (fun n' => g n' - c) + c * rateSum N x ε n (fun _ => 1) := by
  have h1 := hasSum_rates N x ε n g
  have h2 := ((hasSum_rates N x ε n (fun n' => g n' - c)).add
    ((hasSum_rates N x ε n (fun _ => 1)).mul_left c))
  have e : (fun n' => rates N x ε n n' * (g n' - c) + c * (rates N x ε n n' * 1)) =
      fun n' => rates N x ε n n' * g n' := by funext n'; ring
  rw [e] at h2
  exact h1.unique h2


lemma pow_le_sum_choose (y : ℝ) (hy : 0 ≤ y) (k : ℕ) :
    y ^ (k+1) ≤ ((k+1).factorial : ℝ) * ∑ j ∈ range ⌈y⌉₊, ((j + k).choose k : ℝ) := by
  have h1 : y ^ (k+1) ≤ (⌈y⌉₊ : ℝ) ^ (k+1) := pow_le_pow_left₀ hy (Nat.le_ceil y) _
  rcases Nat.eq_zero_or_eq_succ_pred ⌈y⌉₊ with h0 | hK
  · rw [h0] at h1 ⊢
    simp only [Nat.cast_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      not_false_eq_true, zero_pow] at h1
    simpa using h1
  · set K' := ⌈y⌉₊.pred
    rw [hK] at h1 ⊢
    have hs : ∑ j ∈ range (K' + 1), ((j + k).choose k : ℝ) = ((K' + k + 1).choose (k+1) : ℝ) := by
      exact_mod_cast Nat.sum_range_add_choose K' k
    rw [hs]
    have h2 : ((K'+1) : ℕ) ^ (k+1) ≤ (K'+1).ascFactorial (k+1) := Nat.pow_succ_le_ascFactorial _ _
    rw [Nat.ascFactorial_eq_factorial_mul_choose] at h2
    have h3 : (((K'+1 : ℕ) : ℝ)) ^ (k+1) ≤ ((k+1).factorial : ℝ) * ((K' + (k + 1)).choose (k+1) : ℝ) := by
      exact_mod_cast h2
    have : K' + k + 1 = K' + (k+1) := by omega
    rw [this]
    exact h1.trans (by simpa using h3)

lemma moment_of_tail {S : Type*} (π : S → ℝ) (hπ0 : ∀ n, 0 ≤ π n) (hπ : HasSum π 1)
    (W : S → ℝ) (hW : ∀ n, 0 ≤ W n) (a b β : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (htail : ∀ j : ℕ, ∑' n, (if a + b * j < W n then π n else 0) ≤ β ^ (j+1)) (k : ℕ) :
    Summable (fun n => π n * W n ^ (k+1)) ∧
    ∑' n, π n * W n ^ (k+1) ≤
      2 ^ k * (a ^ (k+1) + b ^ (k+1) * (k+1).factorial / (1 - β) ^ (k+1)) := by
  set Y : S → ℝ := fun n => max 0 ((W n - a) / b) with hYdef
  have hY0 : ∀ n, 0 ≤ Y n := fun n => le_max_left _ _
  have hWY : ∀ n, W n ≤ a + b * Y n := by
    intro n
    have : (W n - a) / b ≤ Y n := le_max_right _ _
    have := (div_le_iff₀ hb).1 this
    linarith
  have hind : ∀ n (j : ℕ), j < ⌈Y n⌉₊ → a + b * j < W n := by
    intro n j hj
    have hj' : (j : ℝ) < Y n := Nat.lt_ceil.1 hj
    have hjpos : (0:ℝ) ≤ j := Nat.cast_nonneg j
    have hYeq : Y n = (W n - a) / b := by
      rcases le_total 0 ((W n - a) / b) with h | h
      · exact max_eq_right h
      · have : Y n = 0 := max_eq_left h
        linarith
    rw [hYeq, lt_div_iff₀ hb] at hj'
    linarith
  have hπs : Summable π := hπ.summable
  have hite_s : ∀ j : ℕ, Summable (fun n => if a + b * j < W n then π n else 0) := by
    intro j
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hπs
    · split_ifs <;> simp [hπ0 n]
    · split_ifs <;> simp [hπ0 n]
  have hgeo : Summable (fun j : ℕ => ((j + k).choose k : ℝ) * β ^ j) :=
    summable_choose_mul_geometric_of_norm_lt_one k (by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1)
  have hgeo_t : ∑' j : ℕ, ((j + k).choose k : ℝ) * β ^ j = 1 / (1 - β) ^ (k+1) :=
    tsum_choose_mul_geometric_of_norm_lt_one k (by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1)
  set c : ℝ := 2 ^ k * (a ^ (k+1) + b ^ (k+1) * (k+1).factorial / (1 - β) ^ (k+1)) with hc
  have hbound : ∀ s : Finset S, ∑ n ∈ s, π n * W n ^ (k+1) ≤ c := by
    intro s
    set M := s.sup (fun n => ⌈Y n⌉₊)
    have hpt : ∀ n ∈ s, π n * W n ^ (k+1) ≤
        2 ^ k * (a ^ (k+1) * π n + b ^ (k+1) * (k+1).factorial *
          ∑ j ∈ range M, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0)) := by
      intro n hn
      have e1 : W n ^ (k+1) ≤ (a + b * Y n) ^ (k+1) := pow_le_pow_left₀ (hW n) (hWY n) _
      have e2 : (a + b * Y n) ^ (k+1) ≤ 2 ^ k * (a ^ (k+1) + (b * Y n) ^ (k+1)) := by
        simpa using add_pow_le ha (mul_nonneg hb.le (hY0 n)) (k+1)
      have e3 : Y n ^ (k+1) ≤ ((k+1).factorial : ℝ) * ∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ) :=
        pow_le_sum_choose _ (hY0 n) k
      have e4 : (∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ)) * π n ≤
          ∑ j ∈ range M, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0) := by
        rw [Finset.sum_mul]
        have hsub : range ⌈Y n⌉₊ ⊆ range M := by
          apply Finset.range_subset_range.2
          exact Finset.le_sup (f := fun n => ⌈Y n⌉₊) hn
        calc ∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ) * π n
            = ∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [if_pos (hind n j (Finset.mem_range.1 hj))]
          _ ≤ _ := by
              apply Finset.sum_le_sum_of_subset_of_nonneg hsub
              intro j _ _
              apply mul_nonneg (Nat.cast_nonneg _)
              split_ifs <;> simp [hπ0 n]
      have hp := hπ0 n
      calc π n * W n ^ (k+1) ≤ π n * (2 ^ k * (a ^ (k+1) + (b * Y n) ^ (k+1))) :=
            mul_le_mul_of_nonneg_left (e1.trans e2) hp
        _ = 2 ^ k * (a ^ (k+1) * π n + b ^ (k+1) * (Y n ^ (k+1) * π n)) := by ring
        _ ≤ 2 ^ k * (a ^ (k+1) * π n + b ^ (k+1) * (((k+1).factorial : ℝ) *
              ∑ j ∈ range M, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0))) := by
            have e5 : Y n ^ (k+1) * π n ≤ ((k+1).factorial : ℝ) *
                ∑ j ∈ range M, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0) := by
              calc Y n ^ (k+1) * π n ≤ (((k+1).factorial : ℝ) * ∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ)) * π n :=
                    mul_le_mul_of_nonneg_right e3 hp
                _ = ((k+1).factorial : ℝ) * ((∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ)) * π n) := by ring
                _ ≤ _ := mul_le_mul_of_nonneg_left e4 (by positivity)
            have hb' : 0 ≤ b ^ (k+1) := by positivity
            have h2k : (0:ℝ) ≤ 2 ^ k := by positivity
            exact mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left e5 hb') _) h2k
        _ = _ := by ring
    have hsum1 : ∑ n ∈ s, π n ≤ 1 := sum_le_hasSum s (fun n _ => hπ0 n) hπ
    have hsum2 : ∀ j : ℕ, ∑ n ∈ s, (if a + b * j < W n then π n else 0) ≤ β ^ (j+1) := by
      intro j
      refine le_trans ?_ (htail j)
      apply Summable.sum_le_tsum s _ (hite_s j)
      intro n _
      split_ifs <;> simp [hπ0 n]
    have hsum3 : ∑ j ∈ range M, ((j + k).choose k : ℝ) * β ^ (j+1) ≤ 1 / (1 - β) ^ (k+1) := by
      calc ∑ j ∈ range M, ((j + k).choose k : ℝ) * β ^ (j+1)
          = β * ∑ j ∈ range M, ((j + k).choose k : ℝ) * β ^ j := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
        _ ≤ 1 * ∑' j : ℕ, ((j + k).choose k : ℝ) * β ^ j := by
            apply mul_le_mul hβ1.le _ (Finset.sum_nonneg (fun j _ => by positivity)) zero_le_one
            apply Summable.sum_le_tsum _ (fun j _ => by positivity) hgeo
        _ = _ := by rw [hgeo_t, one_mul]
    calc ∑ n ∈ s, π n * W n ^ (k+1)
        ≤ ∑ n ∈ s, 2 ^ k * (a ^ (k+1) * π n + b ^ (k+1) * (k+1).factorial *
          ∑ j ∈ range M, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0)) :=
          Finset.sum_le_sum hpt
      _ = 2 ^ k * (a ^ (k+1) * ∑ n ∈ s, π n + b ^ (k+1) * (k+1).factorial *
          ∑ j ∈ range M, ((j + k).choose k : ℝ) *
            ∑ n ∈ s, (if a + b * j < W n then π n else 0)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_comm]
          congr 3
          apply Finset.sum_congr rfl; intro j _; rw [Finset.mul_sum]
      _ ≤ 2 ^ k * (a ^ (k+1) * 1 + b ^ (k+1) * (k+1).factorial *
          ∑ j ∈ range M, ((j + k).choose k : ℝ) * β ^ (j+1)) := by
          gcongr with j hj
          exact hsum2 j
      _ ≤ 2 ^ k * (a ^ (k+1) * 1 + b ^ (k+1) * (k+1).factorial * (1 / (1 - β) ^ (k+1))) := by
          gcongr
      _ = c := by rw [hc]; ring
  have hnn : 0 ≤ fun n => π n * W n ^ (k+1) := fun n => mul_nonneg (hπ0 n) (pow_nonneg (hW n) _)
  exact ⟨summable_of_sum_le hnn hbound, Real.tsum_le_of_sum_le hnn hbound⟩


lemma wsum_nonneg (N : BWNetwork L R) (hκ : ∀ r, 0 < N.κ r) (n : State N) : 0 ≤ wsum N n := by
  unfold wsum
  exact Finset.sum_nonneg (fun r _ => mul_nonneg (hκ r).le (Nat.cast_nonneg _))


lemma muMax_pos (N : BWNetwork L R) (hC : ∀ ℓ, 0 < N.C ℓ) (hLs : (critical N).Nonempty) :
    0 < muMax N := by
  obtain ⟨ℓ, hℓ⟩ := hLs
  have hR : Nonempty (Fin R) := by
    by_contra h
    rw [not_nonempty_iff] at h
    unfold critical at hℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hℓ
    linarith [hC ℓ]
  obtain ⟨r⟩ := hR
  have hB : Nonempty (Fin (N.D r).B) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : IsEmpty (Phase (N.D r)) := ⟨fun k => h.elim k.1⟩
    have := (N.D r).init_sum
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact zero_ne_one this
  obtain ⟨b⟩ := hB
  unfold muMax
  calc 0 < (N.D r).rate b := (N.D r).rate_pos b
    _ ≤ ⨆ b, (N.D r).rate b := le_ciSup (Finite.bddAbove_range _) b
    _ ≤ ⨆ r, ⨆ b, (N.D r).rate b :=
        le_ciSup (f := fun r => ⨆ b, (N.D r).rate b) (Finite.bddAbove_range _) r

lemma W_moment {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1) (hrank : N.H.rank = L)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (hload : ∀ ℓ, ∑ r, N.H ℓ r * routeLoad0 N r ≤ N.C ℓ) (hLs : (critical N).Nonempty)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ π : State N → ℝ,
      IsStationary (rates N x ε) π →
      Summable (fun n => π n * wsum N n ^ (k+1)) ∧
        ∑' n, π n * wsum N n ^ (k+1) ≤ M / ε ^ (k+1) := by
  obtain ⟨A1, A3, A4, ν, ζ, η, hA1, hA3, hA4, hν, hζ, hη, h7⟩ :=
    lemma_7 N hH01 hrank hroute hC hκ hlam0 hload hLs x hx
  have hμ := muMax_pos N hC hLs
  set μ := muMax N with hμdef
  set c := η * A3 / μ with hcdef
  have hc : 0 < c := by positivity
  set a0 := μ * A1 * A4 / (η * A3) with ha0
  set b := 2 * ν * A4 with hbdef
  set F : ℝ := ((k+1).factorial : ℝ) with hF
  set Q := (ζ * ν + c) / c with hQ
  refine ⟨2 ^ k * (a0 ^ (k+1) + b ^ (k+1) * F * Q ^ (k+1)), by positivity, ?_⟩
  intro ε hε hε1 π hπ
  have htail := (h7 ε hε hε1).2.2.2 π hπ
  set β := ζ * ν / (ζ * ν + ε * η * A3 / μ) with hβdef
  have hεc : ε * η * A3 / μ = ε * c := by rw [hcdef]; ring
  have hβ' : β = ζ * ν / (ζ * ν + ε * c) := by rw [hβdef, hεc]
  have hzn : 0 < ζ * ν := by positivity
  have hβ0 : 0 ≤ β := by rw [hβ']; positivity
  have hβ1 : β < 1 := by
    rw [hβ', div_lt_one (by positivity)]
    have : 0 < ε * c := by positivity
    linarith
  have h1β : 1 - β = ε * c / (ζ * ν + ε * c) := by
    rw [hβ']; field_simp; ring
  obtain ⟨hs, hbd⟩ := moment_of_tail π hπ.1 hπ.2.1 (wsum N) (wsum_nonneg N hκ)
    (μ * A1 * A4 / (η * A3 * ε)) b β (by positivity) (by positivity) hβ0 hβ1 htail k
  refine ⟨hs, hbd.trans ?_⟩
  have ha : μ * A1 * A4 / (η * A3 * ε) = a0 / ε := by
    rw [ha0]; field_simp
  have hinv : 1 / (1 - β) ≤ Q / ε := by
    rw [h1β, one_div_div, hQ, div_div, show c * ε = ε * c by ring,
      div_le_div_iff_of_pos_right (by positivity)]
    have : ε * c ≤ c := by nlinarith
    linarith
  have hinvpow : (1 / (1 - β)) ^ (k+1) ≤ (Q / ε) ^ (k+1) :=
    pow_le_pow_left₀ (by rw [h1β]; positivity) hinv _
  rw [ha]
  have e1 : b ^ (k+1) * F / (1 - β) ^ (k+1) = b ^ (k+1) * F * (1 / (1 - β)) ^ (k+1) := by
    rw [_root_.one_div_pow]; ring
  rw [e1]
  have hb0 : 0 ≤ b ^ (k+1) * F := by positivity
  calc 2 ^ k * ((a0 / ε) ^ (k+1) + b ^ (k+1) * F * (1 / (1 - β)) ^ (k+1))
      ≤ 2 ^ k * ((a0 / ε) ^ (k+1) + b ^ (k+1) * F * (Q / ε) ^ (k+1)) := by
        gcongr
    _ = 2 ^ k * (a0 ^ (k+1) + b ^ (k+1) * F * Q ^ (k+1)) / ε ^ (k+1) := by
        simp only [div_pow]; field_simp


end HTInsensBWEUB

open HTInsensBW.PhaseType HTInsensBWEUB Matrix Finset

theorem solution {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1) (hrank : N.H.rank = L)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (hload : ∀ ℓ, ∑ r, N.H ℓ r * routeLoad0 N r ≤ N.C ℓ) (hLs : (critical N).Nonempty)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ π : State N → ℝ, IsStationary (rates N x ε) π →
      ∀ ℓ ∈ critical N, Summable (fun n => π n * unused N x n ℓ) ∧
        ∑' n, π n * unused N x n ℓ = ε * N.C ℓ := by
  obtain ⟨M1, -, hW1⟩ := W_moment N hH01 hrank hroute hC hκ hlam0 hload hLs x hx 0
  intro ε hε hε1 π hπ ℓ hℓ
  have hπ0 := hπ.1
  have hπs : Summable π := hπ.2.1.summable
  obtain ⟨hWs, -⟩ := hW1 ε hε hε1 π hπ
  have hWs' : Summable (fun n => π n * wsum N n) := by simpa using hWs
  set a := aL N ℓ with ha
  set V := linV N a with hV
  have hH0 : ∀ r, 0 ≤ N.H ℓ r := fun r => by rcases hH01 ℓ r with h | h <;> simp [h]
  have ha0 : ∀ i, 0 ≤ a i := fun i => mul_nonneg (hH0 i.1) (cvec_nonneg _ _)
  have hV0 : ∀ n, 0 ≤ V n := fun n =>
    Finset.sum_nonneg (fun i _ => mul_nonneg (ha0 i) (Nat.cast_nonneg _))
  set K := ∑ i, a i / N.κ i.1 with hK
  have hVK : ∀ n, V n ≤ K * wsum N n := by
    intro n
    have hw : wsum N n = ∑ i : Idx N, N.κ i.1 * (n i : ℝ) := by
      rw [wsum, Fintype.sum_sigma]
      apply Finset.sum_congr rfl; intro r _
      rw [routeCount, Nat.cast_sum, Finset.mul_sum]
    rw [hw, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h1 : a i / N.κ i.1 ≤ K :=
      Finset.single_le_sum (f := fun i => a i / N.κ i.1)
        (fun i _ => div_nonneg (ha0 i) (hκ i.1).le) (Finset.mem_univ i)
    have h2 : a i ≤ K * N.κ i.1 := by rwa [div_le_iff₀ (hκ i.1)] at h1
    have := Nat.cast_nonneg (α := ℝ) (n i)
    nlinarith
  have hVs : Summable (fun n => π n * V n) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hπ0 n) (hV0 n)) (fun n => ?_)
      (hWs'.mul_left K)
    have := mul_le_mul_of_nonneg_left (hVK n) (hπ0 n)
    linarith
  set q := rates N x ε with hq
  have hq0 : ∀ i j, 0 ≤ q i j := rates_nonneg N x hx hlam0 ε hε1
  have h1s : ∀ n, HasSum (fun n' => q n n') (rateSum N x ε n (fun _ => 1)) := by
    intro n
    have := hasSum_rates N x ε n (fun _ => 1)
    simpa using this
  have hVsum : ∀ n, HasSum (fun n' => q n n' * V n') (rateSum N x ε n V) :=
    fun n => hasSum_rates N x ε n V
  set Q := (∑ i : Idx N, N.lam0 i.1 * (N.D i.1).init i.2) +
      (∑ r : Fin R, ∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
        (∑ ℓ, N.C ℓ) * |subgen (N.D r) k₁ k₂|) +
      (∑ i : Idx N, (∑ ℓ, N.C ℓ) * exitRate (N.D i.1) i.2) with hQ
  have hQle : ∀ n, rateSum N x ε n (fun _ => 1) ≤ Q :=
    fun n => rateSum_one_le N hH01 hroute hC hlam0 x hx ε hε hε1 n
  have hQ0 : ∀ n, 0 ≤ rateSum N x ε n (fun _ => 1) := fun n =>
    (h1s n).nonneg (fun n' => hq0 n n')
  set D : State N → ℝ := fun n => (1 - ε) * ∑ r, N.H ℓ r * routeLoad0 N r -
    ∑ r, N.H ℓ r * (routeCount N n r : ℝ) * x (routeCount N n) r with hD
  have hdrift : ∀ n, drift q V n = D n := by
    intro n
    unfold drift
    rw [(hasSum_rates N x ε n (fun n' => V n' - V n)).tsum_eq, rateSum_linV]
  have hRV : ∀ n, rateSum N x ε n V = D n + V n * rateSum N x ε n (fun _ => 1) := by
    intro n
    rw [rateSum_affine N x ε n V (V n), ← hdrift n]
    unfold drift
    rw [(hasSum_rates N x ε n (fun n' => V n' - V n)).tsum_eq]
  have hload_n : ∀ n, 0 ≤ ∑ r, N.H ℓ r * (routeCount N n r : ℝ) * x (routeCount N n) r ∧
      ∑ r, N.H ℓ r * (routeCount N n r : ℝ) * x (routeCount N n) r ≤ N.C ℓ := by
    intro n
    refine ⟨Finset.sum_nonneg (fun r _ => ?_), (hx (routeCount N n)).2.2.1 ℓ⟩
    have := x_nonneg' N _ _ (hx (routeCount N n)) r
    have := hH0 r
    positivity
  set Db := |∑ r, N.H ℓ r * routeLoad0 N r| + N.C ℓ with hDb
  have hDbound : ∀ n, |D n| ≤ Db := by
    intro n
    obtain ⟨h1, h2⟩ := hload_n n
    simp only [hD]
    have hε' : |1 - ε| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc |(1 - ε) * ∑ r, N.H ℓ r * routeLoad0 N r -
          ∑ r, N.H ℓ r * (routeCount N n r : ℝ) * x (routeCount N n) r|
        ≤ |(1 - ε) * ∑ r, N.H ℓ r * routeLoad0 N r| +
          |∑ r, N.H ℓ r * (routeCount N n r : ℝ) * x (routeCount N n) r| := abs_sub _ _
      _ ≤ |∑ r, N.H ℓ r * routeLoad0 N r| + N.C ℓ := by
          rw [abs_mul, abs_of_nonneg h1]
          have : |1 - ε| * |∑ r, N.H ℓ r * routeLoad0 N r| ≤ |∑ r, N.H ℓ r * routeLoad0 N r| := by
            have := abs_nonneg (∑ r, N.H ℓ r * routeLoad0 N r)
            nlinarith
          linarith
  have hA : Summable (fun n => π n * ∑' n', q n n' * V n') := by
    refine Summable.of_norm_bounded ((hπs.mul_right Db).add (hVs.mul_left Q)) (fun n => ?_)
    rw [(hVsum n).tsum_eq, hRV n, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ0 n)]
    have h1 : |D n + V n * rateSum N x ε n (fun _ => 1)| ≤ Db + Q * V n := by
      have := hDbound n
      have h3 : V n * rateSum N x ε n (fun _ => 1) ≤ Q * V n := by
        nlinarith [hQle n, hV0 n]
      have h4 : 0 ≤ V n * rateSum N x ε n (fun _ => 1) := mul_nonneg (hV0 n) (hQ0 n)
      calc _ ≤ |D n| + |V n * rateSum N x ε n (fun _ => 1)| := abs_add_le _ _
        _ ≤ _ := by rw [abs_of_nonneg h4]; linarith
    have := mul_le_mul_of_nonneg_left h1 (hπ0 n)
    linarith
  have hB : Summable (fun n => π n * V n * ∑' n', q n n') := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hVs.mul_left Q)
    · rw [(h1s n).tsum_eq]; exact mul_nonneg (mul_nonneg (hπ0 n) (hV0 n)) (hQ0 n)
    · rw [(h1s n).tsum_eq]
      have := mul_le_mul_of_nonneg_left (hQle n) (mul_nonneg (hπ0 n) (hV0 n))
      linarith
  obtain ⟨-, hzero⟩ := stationary_drift_zero q π hπ hq0 V hV0 (fun n => (h1s n).summable)
    (fun n => (hVsum n).summable) hA hB
  simp_rw [hdrift] at hzero
  have hcrit : ∑ r, N.H ℓ r * routeLoad0 N r = N.C ℓ := by
    unfold critical at hℓ
    simpa using hℓ
  have hU0 : ∀ n, 0 ≤ unused N x n ℓ ∧ unused N x n ℓ ≤ N.C ℓ := by
    intro n
    obtain ⟨h1, h2⟩ := hload_n n
    unfold unused
    constructor <;> linarith
  have hUs : Summable (fun n => π n * unused N x n ℓ) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hπ0 n) (hU0 n).1) (fun n => ?_)
      (hπs.mul_right (N.C ℓ))
    exact mul_le_mul_of_nonneg_left (hU0 n).2 (hπ0 n)
  refine ⟨hUs, ?_⟩
  have hDU : ∀ n, π n * D n = π n * unused N x n ℓ - ε * N.C ℓ * π n := by
    intro n
    simp only [hD, hcrit, unused]
    ring
  simp_rw [hDU] at hzero
  rw [Summable.tsum_sub hUs (hπs.mul_left _), tsum_mul_left, hπ.2.1.tsum_eq, mul_one] at hzero
  linarith
