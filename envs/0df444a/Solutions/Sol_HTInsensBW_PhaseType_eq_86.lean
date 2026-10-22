-- Prove2me | solution 1 for HTInsensBW.PhaseType.eq_86
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T22:58:26.979838+00:00
-- url     : https://prove2.me/submissions/99403a6c-53dd-4c24-8c91-be2f07957f8e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_InnerProduct
import Theorems.Thm_HTInsensBW_PhaseType_lemma_7
import Theorems.Thm_HTInsensBW_PhaseType_lemma_11
import Theorems.Thm_HTInsensBW_PhaseType_lemma_5

namespace HTInsensBWE86

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



/-! ## eq_80 specific part -/

lemma mulVec_bd {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → Type*} [∀ i, Fintype (m i)]
    (A : ∀ i, Matrix (m i) (m i) ℝ) (w : (Σ i, m i) → ℝ) (r : ι) (k : m r) :
    (blockDiagonal' A *ᵥ w) ⟨r, k⟩ = (A r *ᵥ (fun k' => w ⟨r, k'⟩)) k := by
  simp only [mulVec, dotProduct]
  rw [Fintype.sum_sigma, Finset.sum_eq_single r]
  · apply Finset.sum_congr rfl
    intro k' _
    rw [blockDiagonal'_apply_eq]
  · intro r' _ hne
    apply Finset.sum_eq_zero
    intro k' _
    rw [blockDiagonal'_apply_ne _ _ _ (Ne.symm hne), zero_mul]
  · intro h; exact absurd (Finset.mem_univ r) h

lemma sum_rho0 (N : BWNetwork L R) (r : Fin R) :
    ∑ k, rho0 N ⟨r, k⟩ = routeLoad0 N r := by
  simp only [rho0, phaseLoad, routeLoad0, meanSize, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  congr 1
  rw [dotProduct_mulVec]
  simp [dotProduct]

lemma meanSize_pos (D : PhaseTypeD) : 0 < meanSize D := by
  rw [meanSize_eq]
  have hc : ∀ k, 0 < cvec D k := by
    intro k
    unfold cvec
    have h1 : ((k.2 : ℕ) : ℝ) < D.len k.1 := by exact_mod_cast k.2.2
    exact div_pos (by linarith) (D.rate_pos _)
  obtain ⟨k, hk⟩ : ∃ k, 0 < D.init k := by
    by_contra h
    push_neg at h
    have : ∑ k, D.init k ≤ 0 := Finset.sum_nonpos (fun k _ => h k)
    linarith [D.init_sum]
  apply Finset.sum_pos' (fun k _ => mul_nonneg (D.init_nonneg k) (hc k).le)
  exact ⟨k, Finset.mem_univ k, mul_pos hk (hc k)⟩

lemma rho0_vecMul (N : BWNetwork L R) (r : Fin R) :
    (fun k => rho0 N ⟨r, k⟩) ᵥ* (-subgen (N.D r)) = N.lam0 r • (N.D r).init := by
  have hu := neg_subgen_isUnit (N.D r)
  have e : (fun k => rho0 N ⟨r, k⟩) = phaseLoad (N.D r) (N.lam0 r) := rfl
  rw [e, phaseLoad, Matrix.smul_vecMul, Matrix.vecMul_vecMul,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), Matrix.vecMul_one]

lemma sum_ext_crit (N : BWNetwork L R) (α : critical N → ℝ) (f : Fin L → ℝ) :
    ∑ i : critical N, α i * f i =
      ∑ ℓ, (if h : ℓ ∈ critical N then α ⟨ℓ, h⟩ else 0) * f ℓ := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (critical N)) (fun ℓ _ hℓ => by simp [hℓ]),
    Finset.sum_subtype (critical N) (p := fun ℓ => ℓ ∈ critical N) (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl; intro i _
  simp [i.2]

lemma vecMul_H_injective (N : BWNetwork L R) (hrank : N.H.rank = L) :
    ∀ β : Fin L → ℝ, β ᵥ* N.H = 0 → β = 0 := by
  intro β hβ
  have hr : N.Hᵀ.rank = L := by rw [Matrix.rank_transpose, hrank]
  have hk := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin N.Hᵀ)
  rw [Matrix.rank] at hr
  rw [hr, Module.finrank_fin_fun] at hk
  have hker : LinearMap.ker (Matrix.mulVecLin N.Hᵀ) = ⊥ :=
    Submodule.finrank_eq_zero.1 (by omega)
  have : β ∈ LinearMap.ker (Matrix.mulVecLin N.Hᵀ) := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose]; exact hβ
  rw [hker] at this
  exact this

lemma Bs_vecMul_injective (N : BWNetwork L R) (hrank : N.H.rank = L) (hκ : ∀ r, 0 < N.κ r)
    (hlam0 : ∀ r, 0 < N.lam0 r) : Function.Injective (Bs N).vecMul := by
  classical
  have hlin : ∀ α : critical N → ℝ, α ᵥ* Bs N = 0 → α = 0 := by
    intro α hα
    set β : Fin L → ℝ := fun ℓ => if h : ℓ ∈ critical N then α ⟨ℓ, h⟩ else 0 with hβ
    have hrow : ∀ r, ∑ ℓ, β ℓ * N.H ℓ r = 0 := by
      intro r
      have e : ∀ k, (α ᵥ* Bs N) ⟨r, k⟩ = rho0 N ⟨r, k⟩ / N.κ r * ∑ ℓ, β ℓ * N.H ℓ r := by
        intro k
        have : (α ᵥ* Bs N) ⟨r, k⟩ = ∑ i : critical N, α i * (rho0 N ⟨r, k⟩ / N.κ r * N.H i r) := by
          simp only [vecMul, dotProduct, Bs, Matrix.of_apply, bvec]
          apply Finset.sum_congr rfl; intro i _; ring
        rw [this, sum_ext_crit N α (fun ℓ => rho0 N ⟨r, k⟩ / N.κ r * N.H ℓ r), Finset.mul_sum]
        apply Finset.sum_congr rfl; intro ℓ _; simp only [hβ]; ring
      have hsum : ∑ k, (α ᵥ* Bs N) ⟨r, k⟩ = 0 := by rw [hα]; simp
      simp_rw [e] at hsum
      rw [← Finset.sum_mul, ← Finset.sum_div, sum_rho0] at hsum
      have hpos : 0 < routeLoad0 N r / N.κ r :=
        div_pos (mul_pos (hlam0 r) (meanSize_pos _)) (hκ r)
      rcases mul_eq_zero.1 hsum with h | h
      · linarith
      · exact h
    have hβ0 : β = 0 := by
      apply vecMul_H_injective N hrank
      funext r
      simp only [vecMul, dotProduct, Pi.zero_apply]
      exact hrow r
    funext i
    have := congrFun hβ0 i.1
    simp only [hβ, i.2, dif_pos, Pi.zero_apply] at this
    simpa using this
  intro a b h
  have h' : a ᵥ* Bs N = b ᵥ* Bs N := h
  have : (a - b) ᵥ* Bs N = 0 := by rw [Matrix.sub_vecMul, h', sub_self]
  exact sub_eq_zero.1 (hlin _ this)


lemma Mfull_symm (N : BWNetwork L R) (hpd : (Mfull N).PosDef) : (Mfull N)ᵀ = Mfull N := by
  have := hpd.isHermitian
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact this

lemma G_isUnit (N : BWNetwork L R) (hpd : (Mfull N).PosDef)
    (hinj : Function.Injective (Bs N).vecMul) :
    IsUnit (Bs N * Mfull N * (Bs N)ᵀ) := by
  classical
  have := hpd.mul_mul_conjTranspose_same hinj
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact this.isUnit

lemma inner_projS_projS (N : BWNetwork L R) (hpd : (Mfull N).PosDef)
    (hinj : Function.Injective (Bs N).vecMul) (y z : Idx N → ℝ) :
    mInner N (projS N y) (projS N z) = mInner N (projS N y) z := by
  classical
  have hu := G_isUnit N hpd hinj
  have hG : (Bs N * Mfull N * (Bs N)ᵀ) * (Bs N * Mfull N * (Bs N)ᵀ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  have key : ∀ (α : critical N → ℝ) (w : Idx N → ℝ),
      mInner N ((Bs N)ᵀ *ᵥ α) w = α ⬝ᵥ (Bs N *ᵥ (Mfull N *ᵥ w)) := by
    intro α w
    unfold mInner
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  unfold projS
  rw [key, key]
  congr 1
  unfold alphaS
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hG,
    Matrix.one_mulVec]

lemma mInner_comm (N : BWNetwork L R) (hpd : (Mfull N).PosDef) (u w : Idx N → ℝ) :
    mInner N u w = mInner N w u := by
  unfold mInner
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Mfull_symm N hpd, dotProduct_comm]

lemma msq_add (N : BWNetwork L R) (hpd : (Mfull N).PosDef) (u w : Idx N → ℝ) :
    msq N (u + w) = msq N u + 2 * mInner N u w + msq N w := by
  unfold msq
  have h1 : mInner N (u + w) (u + w) = mInner N u u + mInner N u w + mInner N w u + mInner N w w := by
    unfold mInner
    simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add]; ring
  rw [h1, mInner_comm N hpd w u]; ring

lemma msq_neg (N : BWNetwork L R) (u : Idx N → ℝ) : msq N (-u) = msq N u := by
  unfold msq mInner
  rw [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

lemma projS_add (N : BWNetwork L R) (y z : Idx N → ℝ) :
    projS N (y + z) = projS N y + projS N z := by
  unfold projS alphaS
  simp only [Matrix.mulVec_add]

lemma projS_neg (N : BWNetwork L R) (y : Idx N → ℝ) : projS N (-y) = -projS N y := by
  unfold projS alphaS
  simp only [Matrix.mulVec_neg]

lemma toReal_addOne (N : BWNetwork L R) (n : State N) (i : Idx N) :
    toReal N (addOne N n i) = toReal N n + unitVec N i := by
  classical
  funext j
  simp only [toReal, addOne, unitVec, Pi.add_apply, Function.update_apply, Pi.single_apply]
  split_ifs with h
  · subst h; push_cast; ring
  · ring

lemma toReal_subOne (N : BWNetwork L R) (n : State N) (i : Idx N) (h : 0 < n i) :
    toReal N (subOne N n i) = toReal N n + -unitVec N i := by
  classical
  funext j
  simp only [toReal, subOne, unitVec, Pi.add_apply, Pi.neg_apply, Function.update_apply,
    Pi.single_apply]
  split_ifs with h'
  · subst h'; rw [Nat.cast_sub (by omega)]; push_cast; ring
  · ring

/-- the quadratic Lyapunov function `‖n^s_∥‖²` -/
noncomputable def Vq (N : BWNetwork L R) (n : State N) : ℝ := msq N (projS N (toReal N n))

lemma Vq_step (N : BWNetwork L R) (hpd : (Mfull N).PosDef)
    (hinj : Function.Injective (Bs N).vecMul) (n : State N) (d : Idx N → ℝ) (t : State N)
    (ht : toReal N t = toReal N n + d) :
    Vq N t - Vq N n = 2 * mInner N (projS N (toReal N n)) d + msq N (projS N d) := by
  unfold Vq
  rw [ht, projS_add, msq_add N hpd, inner_projS_projS N hpd hinj]
  ring


lemma mInner_add_right (N : BWNetwork L R) (u v w : Idx N → ℝ) :
    mInner N u (v + w) = mInner N u v + mInner N u w := by
  unfold mInner; rw [Matrix.mulVec_add, dotProduct_add]

lemma mInner_neg_right (N : BWNetwork L R) (u v : Idx N → ℝ) :
    mInner N u (-v) = -mInner N u v := by
  unfold mInner; rw [Matrix.mulVec_neg, dotProduct_neg]

lemma mInner_unitVec (N : BWNetwork L R) (u : Idx N → ℝ) (i : Idx N) :
    mInner N u (unitVec N i) = ∑ j, u j * Mfull N j i := by
  classical
  unfold mInner unitVec
  simp [dotProduct, mulVec, Pi.single_apply]

lemma mInner_expand (N : BWNetwork L R) (u v : Idx N → ℝ) :
    mInner N u v = ∑ i, v i * mInner N u (unitVec N i) := by
  simp_rw [mInner_unitVec]
  unfold mInner
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma negSfullT_apply (N : BWNetwork L R) (w : Idx N → ℝ) (r : Fin R) (k : Phase (N.D r)) :
    ((-Sfull N)ᵀ *ᵥ w) ⟨r, k⟩ = ∑ k₁, (-subgen (N.D r)) k₁ k * w ⟨r, k₁⟩ := by
  have hS : (-Sfull N)ᵀ = blockDiagonal' (fun r => (-subgen (N.D r))ᵀ) := by
    rw [Sfull, ← blockDiagonal'_neg, blockDiagonal'_transpose]; rfl
  rw [hS, mulVec_bd]
  simp only [mulVec, dotProduct, Matrix.transpose_apply]

lemma Vq_drift (N : BWNetwork L R) (hpd : (Mfull N).PosDef)
    (hinj : Function.Injective (Bs N).vecMul) (x : (Fin R → ℕ) → Fin R → ℝ) (ε : ℝ)
    (n : State N) :
    rateSum N x ε n (fun n' => Vq N n' - Vq N n) =
      -2 * ε * mInner N (projS N (toReal N n)) ((-Sfull N)ᵀ *ᵥ rho0 N) +
      2 * mInner N (projS N (toReal N n)) ((-Sfull N)ᵀ *ᵥ (rho0 N - nx N x n)) + B1 N x ε n := by
  classical
  set u := projS N (toReal N n) with hu
  set φ : Idx N → ℝ := fun i => mInner N u (unitVec N i) with hφ
  set xr : Fin R → ℝ := fun r => x (routeCount N n) r with hxr
  unfold rateSum
  -- rewrite the jumps
  have T1 : ∀ i : Idx N, Vq N (addOne N n i) - Vq N n = 2 * φ i + msq N (projS N (unitVec N i)) :=
    fun i => Vq_step N hpd hinj n _ _ (toReal_addOne N n i)
  have T3 : ∀ i : Idx N, 0 < n i →
      Vq N (subOne N n i) - Vq N n = -2 * φ i + msq N (projS N (unitVec N i)) := by
    intro i h
    rw [Vq_step N hpd hinj n _ _ (toReal_subOne N n i h), mInner_neg_right, projS_neg, msq_neg]
    ring
  have T2 : ∀ (r : Fin R) (k₁ k₂ : Phase (N.D r)), k₁ ≠ k₂ → 0 < n ⟨r, k₁⟩ →
      Vq N (addOne N (subOne N n ⟨r, k₁⟩) ⟨r, k₂⟩) - Vq N n =
        2 * (φ ⟨r, k₂⟩ - φ ⟨r, k₁⟩) +
          msq N (projS N (unitVec N ⟨r, k₂⟩) - projS N (unitVec N ⟨r, k₁⟩)) := by
    intro r k₁ k₂ _ h
    have ht : toReal N (addOne N (subOne N n ⟨r, k₁⟩) ⟨r, k₂⟩) =
        toReal N n + (-unitVec N ⟨r, k₁⟩ + unitVec N ⟨r, k₂⟩) := by
      rw [toReal_addOne, toReal_subOne N n _ h]; abel
    rw [Vq_step N hpd hinj n _ _ ht, mInner_add_right, mInner_neg_right, projS_add, projS_neg]
    have : -projS N (unitVec N ⟨r, k₁⟩) + projS N (unitVec N ⟨r, k₂⟩) =
        projS N (unitVec N ⟨r, k₂⟩) - projS N (unitVec N ⟨r, k₁⟩) := by abel
    rw [this]
    ring
  have S1 : ∑ i : Idx N, (1 - ε) * N.lam0 i.1 * (N.D i.1).init i.2 * (Vq N (addOne N n i) - Vq N n) =
      2 * ∑ i : Idx N, (1 - ε) * N.lam0 i.1 * (N.D i.1).init i.2 * φ i +
      ∑ r, ∑ k, (1 - ε) * N.lam0 r * (N.D r).init k * msq N (projS N (unitVec N ⟨r, k⟩)) := by
    simp_rw [T1, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    · exact Fintype.sum_sigma _
  have S2 : (∑ r : Fin R, ∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
        if k₁ ≠ k₂ ∧ 0 < n ⟨r, k₁⟩
        then (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * subgen (N.D r) k₁ k₂ *
          (Vq N (addOne N (subOne N n ⟨r, k₁⟩) ⟨r, k₂⟩) - Vq N n) else 0) =
      2 * (∑ r : Fin R, ∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
        (n ⟨r, k₁⟩ : ℝ) * xr r * subgen (N.D r) k₁ k₂ * (φ ⟨r, k₂⟩ - φ ⟨r, k₁⟩)) +
      ∑ r : Fin R, ∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
        (if k₁ ≠ k₂ then (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * subgen (N.D r) k₁ k₂ *
          msq N (projS N (unitVec N ⟨r, k₂⟩) - projS N (unitVec N ⟨r, k₁⟩)) else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k₁ _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k₂ _
    by_cases hc : k₁ ≠ k₂ ∧ 0 < n ⟨r, k₁⟩
    · rw [if_pos hc, if_pos hc.1, T2 r k₁ k₂ hc.1 hc.2]; simp only [hxr]; ring
    · rw [if_neg hc]
      rcases not_and_or.1 hc with h | h
      · push_neg at h; subst h; simp
      · have : n ⟨r, k₁⟩ = 0 := by omega
        simp [this]
  have S3 : (∑ i : Idx N, if 0 < n i
        then (n i : ℝ) * x (routeCount N n) i.1 * exitRate (N.D i.1) i.2 *
          (Vq N (subOne N n i) - Vq N n) else 0) =
      -2 * (∑ r : Fin R, ∑ k : Phase (N.D r),
        (n ⟨r, k⟩ : ℝ) * xr r * exitRate (N.D r) k * φ ⟨r, k⟩) +
      ∑ r : Fin R, ∑ k : Phase (N.D r), (n ⟨r, k⟩ : ℝ) * x (routeCount N n) r *
        exitRate (N.D r) k * msq N (projS N (unitVec N ⟨r, k⟩)) := by
    rw [Fintype.sum_sigma, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _
    by_cases hc : 0 < n ⟨r, k⟩
    · rw [if_pos hc, T3 _ hc]; simp only [hxr]; ring
    · rw [if_neg hc]
      have : n ⟨r, k⟩ = 0 := by omega
      simp [this]
  rw [S1, S2, S3]
  -- the B1 part
  have hB1 : B1 N x ε n =
      (∑ r, ∑ k, (1 - ε) * N.lam0 r * (N.D r).init k * msq N (projS N (unitVec N ⟨r, k⟩))) +
      (∑ r : Fin R, ∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
        (if k₁ ≠ k₂ then (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * subgen (N.D r) k₁ k₂ *
          msq N (projS N (unitVec N ⟨r, k₂⟩) - projS N (unitVec N ⟨r, k₁⟩)) else 0)) +
      ∑ r : Fin R, ∑ k : Phase (N.D r), (n ⟨r, k⟩ : ℝ) * x (routeCount N n) r *
        exitRate (N.D r) k * msq N (projS N (unitVec N ⟨r, k⟩)) := by
    unfold B1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  -- the linear part
  have hlin : (∑ i : Idx N, (1 - ε) * N.lam0 i.1 * (N.D i.1).init i.2 * φ i) +
      (∑ r : Fin R, ∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
        (n ⟨r, k₁⟩ : ℝ) * xr r * subgen (N.D r) k₁ k₂ * (φ ⟨r, k₂⟩ - φ ⟨r, k₁⟩)) -
      (∑ r : Fin R, ∑ k : Phase (N.D r), (n ⟨r, k⟩ : ℝ) * xr r * exitRate (N.D r) k * φ ⟨r, k⟩) =
      mInner N u ((-Sfull N)ᵀ *ᵥ (rho0 N - nx N x n)) - ε * mInner N u ((-Sfull N)ᵀ *ᵥ rho0 N) := by
    have e1 : mInner N u ((-Sfull N)ᵀ *ᵥ (rho0 N - nx N x n)) - ε * mInner N u ((-Sfull N)ᵀ *ᵥ rho0 N)
        = mInner N u ((-Sfull N)ᵀ *ᵥ ((1 - ε) • rho0 N - nx N x n)) := by
      unfold mInner
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul,
        sub_smul, one_smul]
      ring
    have e2 : ∀ (r : Fin R) (k : Phase (N.D r)),
        (∑ k₁, (-subgen (N.D r)) k₁ k * ((1 - ε) • rho0 N - nx N x n) ⟨r, k₁⟩) =
          (1 - ε) * N.lam0 r * (N.D r).init k +
            ∑ k₁, subgen (N.D r) k₁ k * ((n ⟨r, k₁⟩ : ℝ) * xr r) := by
      intro r k
      have hρ := congrFun (rho0_vecMul N r) k
      simp only [vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at hρ
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, nx, hxr, mul_sub, Finset.sum_sub_distrib]
      have : ∑ k₁, (-subgen (N.D r)) k₁ k * ((1 - ε) * rho0 N ⟨r, k₁⟩) =
          (1 - ε) * ∑ k₁, rho0 N ⟨r, k₁⟩ * (-subgen (N.D r)) k₁ k := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k₁ _; ring
      rw [this, hρ]
      simp only [Matrix.neg_apply]
      rw [show ∑ k₁, -subgen (N.D r) k₁ k * ((n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r) =
        -∑ k₁, subgen (N.D r) k₁ k * ((n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r) by
        rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro _ _; ring]
      ring
    have hR : mInner N u ((-Sfull N)ᵀ *ᵥ ((1 - ε) • rho0 N - nx N x n)) =
        ∑ r : Fin R, ∑ k : Phase (N.D r), ((1 - ε) * N.lam0 r * (N.D r).init k +
          ∑ k₁, subgen (N.D r) k₁ k * ((n ⟨r, k₁⟩ : ℝ) * xr r)) * φ ⟨r, k⟩ := by
      rw [mInner_expand, Fintype.sum_sigma]
      apply Finset.sum_congr rfl; intro r _
      apply Finset.sum_congr rfl; intro k _
      rw [negSfullT_apply, e2 r k]
    rw [e1, hR, Fintype.sum_sigma]
    have e3 : ∀ r : Fin R,
        (∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
          (n ⟨r, k₁⟩ : ℝ) * xr r * subgen (N.D r) k₁ k₂ * (φ ⟨r, k₂⟩ - φ ⟨r, k₁⟩)) -
        (∑ k : Phase (N.D r), (n ⟨r, k⟩ : ℝ) * xr r * exitRate (N.D r) k * φ ⟨r, k⟩) =
        ∑ k : Phase (N.D r), (∑ k₁, subgen (N.D r) k₁ k * ((n ⟨r, k₁⟩ : ℝ) * xr r)) * φ ⟨r, k⟩ := by
      intro r
      have A : ∀ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
          (n ⟨r, k₁⟩ : ℝ) * xr r * subgen (N.D r) k₁ k₂ * (φ ⟨r, k₂⟩ - φ ⟨r, k₁⟩) =
          (∑ k₂ : Phase (N.D r), (n ⟨r, k₁⟩ : ℝ) * xr r * subgen (N.D r) k₁ k₂ * φ ⟨r, k₂⟩) -
          (n ⟨r, k₁⟩ : ℝ) * xr r * φ ⟨r, k₁⟩ * ∑ k₂ : Phase (N.D r), subgen (N.D r) k₁ k₂ := by
        intro k₁
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro k₂ _; ring
      have B : ∀ k : Phase (N.D r), (n ⟨r, k⟩ : ℝ) * xr r * exitRate (N.D r) k * φ ⟨r, k⟩ =
          -((n ⟨r, k⟩ : ℝ) * xr r * φ ⟨r, k⟩ * ∑ k₂ : Phase (N.D r), subgen (N.D r) k k₂) := by
        intro k
        unfold exitRate
        rw [Finset.sum_neg_distrib]; ring
      rw [Finset.sum_congr rfl (fun k₁ _ => A k₁), Finset.sum_congr rfl (fun k _ => B k),
        Finset.sum_sub_distrib, Finset.sum_neg_distrib, sub_neg_eq_add, sub_add_cancel,
        Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro k₁ _
      ring
    rw [add_sub_assoc, ← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun r _ => e3 r),
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _
    ring
  rw [hB1]
  linear_combination 2 * hlin


lemma abs_dot_mulVec_le {ι κ : Type*} [Fintype ι] [Fintype κ] (T : Matrix ι κ ℝ) (y : ι → ℝ)
    (v : κ → ℝ) (hy : ∀ i, 0 ≤ y i) (Vb : ℝ) (hVb : 0 ≤ Vb) (hv : ∀ j, |v j| ≤ Vb) :
    |y ⬝ᵥ (T *ᵥ v)| ≤ (∑ i, y i) * Vb * ∑ i, ∑ j, |T i j| := by
  have hrow : ∀ i, |(T *ᵥ v) i| ≤ Vb * ∑ i, ∑ j, |T i j| := by
    intro i
    simp only [mulVec, dotProduct]
    calc |∑ j, T i j * v j| ≤ ∑ j, |T i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |T i j| * Vb := Finset.sum_le_sum (fun j _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _))
      _ = Vb * ∑ j, |T i j| := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ Vb * ∑ i, ∑ j, |T i j| := mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun i => ∑ j, |T i j|)
            (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ i)) hVb
  simp only [dotProduct]
  calc |∑ i, y i * (T *ᵥ v) i| ≤ ∑ i, |y i * (T *ᵥ v) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, y i * (Vb * ∑ i, ∑ j, |T i j|) := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul, abs_of_nonneg (hy i)]; exact mul_le_mul_of_nonneg_left (hrow i) (hy i))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- the matrix of the projection -/
noncomputable def Pm (N : BWNetwork L R) : Matrix (Idx N) (Idx N) ℝ :=
  (Bs N)ᵀ * (Bs N * Mfull N * (Bs N)ᵀ)⁻¹ * Bs N * Mfull N

lemma projS_eq (N : BWNetwork L R) (y : Idx N → ℝ) : projS N y = Pm N *ᵥ y := by
  unfold projS alphaS Pm
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma mInner_Pm (N : BWNetwork L R) (y v : Idx N → ℝ) :
    mInner N (projS N y) v = y ⬝ᵥ (((Pm N)ᵀ * Mfull N) *ᵥ v) := by
  rw [projS_eq]
  unfold mInner
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec y, Matrix.vecMul_transpose]

lemma sum_toReal_le (N : BWNetwork L R) (hκ : ∀ r, 0 < N.κ r) (n : State N) :
    ∑ i, toReal N n i ≤ (∑ r, 1 / N.κ r) * wsum N n := by
  have hw0 : ∀ r, 0 ≤ N.κ r * (routeCount N n r : ℝ) := fun r =>
    mul_nonneg (hκ r).le (Nat.cast_nonneg _)
  have e : ∑ i, toReal N n i = ∑ r, (routeCount N n r : ℝ) := by
    rw [Fintype.sum_sigma]; apply Finset.sum_congr rfl; intro r _
    simp [toReal, routeCount]
  rw [e, Finset.sum_mul]
  apply Finset.sum_le_sum; intro r _
  have h1 : N.κ r * (routeCount N n r : ℝ) ≤ wsum N n :=
    Finset.single_le_sum (f := fun r => N.κ r * (routeCount N n r : ℝ)) (fun r _ => hw0 r)
      (Finset.mem_univ r)
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (hκ r)]
  linarith


lemma entry_bound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] (T : Matrix ι κ ℝ)
    (v : κ → ℝ) (Vb : ℝ) (hVb : 0 ≤ Vb) (hv : ∀ j, |v j| ≤ Vb) (i : ι) :
    |(T *ᵥ v) i| ≤ Vb * ∑ i, ∑ j, |T i j| := by
  have := abs_dot_mulVec_le T (Pi.single i 1) v (fun j => by
    by_cases h : j = i <;> simp [Pi.single_apply, h]) Vb hVb hv
  have e : Pi.single i (1 : ℝ) ⬝ᵥ (T *ᵥ v) = (T *ᵥ v) i := by
    simp [dotProduct, Pi.single_apply]
  have e2 : ∑ j, (Pi.single i (1 : ℝ) : ι → ℝ) j = 1 := by simp
  rw [e, e2, one_mul] at this
  exact this

lemma msq_nonneg' (N : BWNetwork L R) (hpd : (Mfull N).PosDef) (w : Idx N → ℝ) :
    0 ≤ msq N w := by
  have := hpd.posSemidef.dotProduct_mulVec_nonneg w
  simpa [msq, mInner] using this

lemma B1_bound (N : BWNetwork L R) (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) (ε : ℝ) (n : State N) :
    |B1 N x ε n| ≤ ∑ r : Fin R,
      ((|∑ k : Phase (N.D r),
        (1 - ε) * N.lam0 r * (N.D r).init k * msq N (projS N (unitVec N ⟨r, k⟩))|)
      + (∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r), (∑ ℓ, N.C ℓ) * |subgen (N.D r) k₁ k₂| *
          |msq N (projS N (unitVec N ⟨r, k₂⟩) - projS N (unitVec N ⟨r, k₁⟩))|)
      + (∑ k : Phase (N.D r), (∑ ℓ, N.C ℓ) * exitRate (N.D r) k *
          |msq N (projS N (unitVec N ⟨r, k⟩))|)) := by
  unfold B1
  have hnx := nx_le N hH01 hroute hC x hx n
  have hxn := fun r => x_nonneg' N _ _ (hx (routeCount N n)) r
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun r _ => ?_))
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k₁ _ => ?_))
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k₂ _ => ?_))
    split_ifs
    · rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (hxn r)]
      have h1 := hnx ⟨r, k₁⟩
      have := abs_nonneg (subgen (N.D r) k₁ k₂)
      have := abs_nonneg (msq N (projS N (unitVec N ⟨r, k₂⟩) - projS N (unitVec N ⟨r, k₁⟩)))
      have : (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * |subgen (N.D r) k₁ k₂| ≤
          (∑ ℓ, N.C ℓ) * |subgen (N.D r) k₁ k₂| := mul_le_mul_of_nonneg_right h1 (by positivity)
      nlinarith
    · simp only [abs_zero]
      have := Finset.sum_nonneg (fun ℓ (_ : ℓ ∈ Finset.univ) => (hC ℓ).le)
      positivity
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (hxn r),
      abs_of_nonneg (exitRate_nonneg _ _)]
    have h1 := hnx ⟨r, k⟩
    have hex := exitRate_nonneg (N.D r) k
    have := abs_nonneg (msq N (projS N (unitVec N ⟨r, k⟩)))
    have : (n ⟨r, k⟩ : ℝ) * x (routeCount N n) r * exitRate (N.D r) k ≤
        (∑ ℓ, N.C ℓ) * exitRate (N.D r) k := mul_le_mul_of_nonneg_right h1 hex
    nlinarith


/-! ## eq_86 specific part -/

lemma rateSum_linV_gen (N : BWNetwork L R) (x : (Fin R → ℕ) → Fin R → ℝ) (ε : ℝ) (n : State N)
    (a : Idx N → ℝ) :
    rateSum N x ε n (fun n' => linV N a n' - linV N a n) =
      (∑ i : Idx N, (1 - ε) * N.lam0 i.1 * (N.D i.1).init i.2 * a i) +
      ∑ r : Fin R, ∑ k₁ : Phase (N.D r), (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r *
        ((∑ k₂ : Phase (N.D r), subgen (N.D r) k₁ k₂ * (a ⟨r, k₂⟩ - a ⟨r, k₁⟩)) -
          exitRate (N.D r) k₁ * a ⟨r, k₁⟩) := by
  classical
  unfold rateSum
  have T1 : ∑ i : Idx N, (1 - ε) * N.lam0 i.1 * (N.D i.1).init i.2 *
      (linV N a (addOne N n i) - linV N a n) =
      ∑ i : Idx N, (1 - ε) * N.lam0 i.1 * (N.D i.1).init i.2 * a i := by
    simp_rw [linV_addOne, add_sub_cancel_left]
  have T2 : (∑ r : Fin R, ∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
        if k₁ ≠ k₂ ∧ 0 < n ⟨r, k₁⟩
        then (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * subgen (N.D r) k₁ k₂ *
          (linV N a (addOne N (subOne N n ⟨r, k₁⟩) ⟨r, k₂⟩) - linV N a n) else 0) =
      ∑ r : Fin R, ∑ k₁ : Phase (N.D r), (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r *
        ∑ k₂ : Phase (N.D r), subgen (N.D r) k₁ k₂ * (a ⟨r, k₂⟩ - a ⟨r, k₁⟩) := by
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro k₁ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k₂ _
    by_cases hc : k₁ ≠ k₂ ∧ 0 < n ⟨r, k₁⟩
    · rw [if_pos hc, linV_move N a n ⟨r, k₁⟩ ⟨r, k₂⟩ (by
        intro h; apply hc.1; exact eq_of_heq (Sigma.mk.inj h).2) hc.2]
      ring
    · rw [if_neg hc]
      rcases not_and_or.1 hc with h | h
      · push_neg at h; subst h; ring
      · have : n ⟨r, k₁⟩ = 0 := by omega
        simp [this]
  have T3 : (∑ i : Idx N, if 0 < n i
        then (n i : ℝ) * x (routeCount N n) i.1 * exitRate (N.D i.1) i.2 *
          (linV N a (subOne N n i) - linV N a n) else 0) =
      ∑ r : Fin R, ∑ k₁ : Phase (N.D r), (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r *
        (-(exitRate (N.D r) k₁ * a ⟨r, k₁⟩)) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro k₁ _
    by_cases hc : 0 < n ⟨r, k₁⟩
    · rw [if_pos hc, linV_subOne N a n _ hc]; ring
    · rw [if_neg hc]
      have : n ⟨r, k₁⟩ = 0 := by omega
      simp [this]
  rw [T1, T2, T3, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro r _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k₁ _
  ring


lemma inner_simplify (D : PhaseTypeD) (a : Phase D → ℝ) (k₁ : Phase D) :
    (∑ k₂, subgen D k₁ k₂ * (a k₂ - a k₁)) - exitRate D k₁ * a k₁ = ∑ k₂, subgen D k₁ k₂ * a k₂ := by
  unfold exitRate
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul]
  ring

lemma single_sigma (N : BWNetwork L R) (r : Fin R) (k₀ : Phase (N.D r)) (r' : Fin R)
    (k : Phase (N.D r')) :
    (Pi.single (⟨r, k₀⟩ : Idx N) (1 : ℝ) : Idx N → ℝ) ⟨r', k⟩ =
      if h : r' = r then (if (h ▸ k) = k₀ then 1 else 0) else 0 := by
  classical
  by_cases h : r' = r
  · subst h
    by_cases hk : k = k₀
    · subst hk; simp
    · have : (Pi.single (⟨r', k₀⟩ : Idx N) (1 : ℝ) : Idx N → ℝ) ⟨r', k⟩ = 0 := by
        rw [Pi.single_apply, if_neg]
        intro h'
        exact hk (eq_of_heq (Sigma.mk.inj h').2)
      rw [this]; simp [hk]
  · rw [dif_neg h, Pi.single_apply, if_neg]
    intro h'
    exact h (Sigma.mk.inj h').1

lemma drift_single (N : BWNetwork L R) (x : (Fin R → ℕ) → Fin R → ℝ) (ε : ℝ) (n : State N)
    (r : Fin R) (k₀ : Phase (N.D r)) :
    rateSum N x ε n (fun n' => linV N (Pi.single ⟨r, k₀⟩ 1) n' - linV N (Pi.single ⟨r, k₀⟩ 1) n) =
      (1 - ε) * N.lam0 r * (N.D r).init k₀ +
        ∑ k₁ : Phase (N.D r), subgen (N.D r) k₁ k₀ * nx N x n ⟨r, k₁⟩ := by
  classical
  rw [rateSum_linV_gen]
  congr 1
  · rw [Finset.sum_eq_single ⟨r, k₀⟩]
    · simp
    · intro i _ hi; simp [Pi.single_apply, hi]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp_rw [inner_simplify]
    rw [Finset.sum_eq_single r]
    · apply Finset.sum_congr rfl; intro k₁ _
      rw [Finset.sum_eq_single k₀]
      · simp [nx]; ring
      · intro k₂ _ hk; rw [single_sigma]; simp [hk]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro r' _ hr'
      apply Finset.sum_eq_zero; intro k₁ _
      rw [Finset.sum_eq_zero]; · ring
      intro k₂ _; rw [single_sigma]; simp [hr']
    · intro h; exact absurd (Finset.mem_univ _) h


lemma drift_lin_bound (N : BWNetwork L R) (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) (ε : ℝ) (n : State N)
    (a : Idx N → ℝ) :
    |rateSum N x ε n (fun n' => linV N a n' - linV N a n)| ≤
      (∑ i : Idx N, |(1 - ε) * N.lam0 i.1 * (N.D i.1).init i.2 * a i|) +
      ∑ r : Fin R, ∑ k₁ : Phase (N.D r), (∑ ℓ, N.C ℓ) *
        ∑ k₂ : Phase (N.D r), |subgen (N.D r) k₁ k₂ * a ⟨r, k₂⟩| := by
  rw [rateSum_linV_gen]
  simp_rw [inner_simplify]
  have hnx := nx_le N hH01 hroute hC x hx n
  have hxn := fun r => x_nonneg' N _ _ (hx (routeCount N n)) r
  refine (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun r _ => ?_))
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k₁ _ => ?_))
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (hxn r)]
  have h1 := hnx ⟨r, k₁⟩
  have h2 : |∑ k₂ : Phase (N.D r), subgen (N.D r) k₁ k₂ * a ⟨r, k₂⟩| ≤
      ∑ k₂ : Phase (N.D r), |subgen (N.D r) k₁ k₂ * a ⟨r, k₂⟩| := Finset.abs_sum_le_sum_abs _ _
  have h3 : 0 ≤ (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r := by have := hxn r; positivity
  calc (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * |∑ k₂ : Phase (N.D r), subgen (N.D r) k₁ k₂ * a ⟨r, k₂⟩|
      ≤ (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * ∑ k₂ : Phase (N.D r), |subgen (N.D r) k₁ k₂ * a ⟨r, k₂⟩| :=
        mul_le_mul_of_nonneg_left h2 h3
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

/-- Steady state: the expected drift of a nonnegative linear function vanishes. -/
lemma stat_lin (N : BWNetwork L R) (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (π : State N → ℝ) (hπ : IsStationary (rates N x ε) π)
    (hWs' : Summable (fun n => π n * wsum N n)) (a : Idx N → ℝ) (ha0 : ∀ i, 0 ≤ a i) :
    HasSum (fun n => π n * rateSum N x ε n (fun n' => linV N a n' - linV N a n)) 0 := by
  have hπ0 := hπ.1
  have hπs : Summable π := hπ.2.1.summable
  set V := linV N a with hV
  have hV0 : ∀ n, 0 ≤ V n := fun n =>
    Finset.sum_nonneg (fun i _ => mul_nonneg (ha0 i) (Nat.cast_nonneg _))
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ∑ i, a i / N.κ i.1 := ⟨_, rfl⟩
  have hVK : ∀ n, V n ≤ K * wsum N n := by
    intro n
    have hw : wsum N n = ∑ i : Idx N, N.κ i.1 * (n i : ℝ) := by
      rw [wsum, Fintype.sum_sigma]
      apply Finset.sum_congr rfl; intro r _
      rw [routeCount, Nat.cast_sum, Finset.mul_sum]
    rw [hw, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h1 : a i / N.κ i.1 ≤ K := by
      rw [hK]
      exact Finset.single_le_sum (f := fun i => a i / N.κ i.1)
        (fun i _ => div_nonneg (ha0 i) (hκ i.1).le) (Finset.mem_univ i)
    have h2 : a i ≤ K * N.κ i.1 := by rwa [div_le_iff₀ (hκ i.1)] at h1
    have := Nat.cast_nonneg (α := ℝ) (n i)
    nlinarith
  have hK0 : 0 ≤ K := by
    rw [hK]; exact Finset.sum_nonneg (fun i _ => div_nonneg (ha0 i) (hκ i.1).le)
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
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (∑ i : Idx N, N.lam0 i.1 * (N.D i.1).init i.2) +
      (∑ r : Fin R, ∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
        (∑ ℓ, N.C ℓ) * |subgen (N.D r) k₁ k₂|) +
      (∑ i : Idx N, (∑ ℓ, N.C ℓ) * exitRate (N.D i.1) i.2) := ⟨_, rfl⟩
  have hQle : ∀ n, rateSum N x ε n (fun _ => 1) ≤ Q :=
    fun n => by rw [hQ]; exact rateSum_one_le N hH01 hroute hC hlam0 x hx ε hε hε1 n
  have hQ0 : ∀ n, 0 ≤ rateSum N x ε n (fun _ => 1) := fun n =>
    (h1s n).nonneg (fun n' => hq0 n n')
  set D : State N → ℝ := fun n => rateSum N x ε n (fun n' => V n' - V n) with hD
  have hdrift : ∀ n, drift q V n = D n := by
    intro n
    unfold drift
    rw [(hasSum_rates N x ε n (fun n' => V n' - V n)).tsum_eq]
  have hRV : ∀ n, rateSum N x ε n V = D n + V n * rateSum N x ε n (fun _ => 1) :=
    fun n => rateSum_affine N x ε n V (V n)
  obtain ⟨Db, hDb⟩ : ∃ c : ℝ, c = (∑ i : Idx N, |(1 - ε) * N.lam0 i.1 * (N.D i.1).init i.2 * a i|) +
      ∑ r : Fin R, ∑ k₁ : Phase (N.D r), (∑ ℓ, N.C ℓ) *
        ∑ k₂ : Phase (N.D r), |subgen (N.D r) k₁ k₂ * a ⟨r, k₂⟩| := ⟨_, rfl⟩
  have hDbound : ∀ n, |D n| ≤ Db := fun n => by
    rw [hDb]; exact drift_lin_bound N hH01 hroute hC x hx ε n a
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
  obtain ⟨hs, hzero⟩ := stationary_drift_zero q π hπ hq0 V hV0 (fun n => (h1s n).summable)
    (fun n => (hVsum n).summable) hA hB
  simp_rw [hdrift] at hs hzero
  rw [← hzero]
  exact hs.hasSum

/-- `E[N_{r,k} x_r] = ρ_{r,k}` in steady state. -/
lemma mean_nx (N : BWNetwork L R) (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (π : State N → ℝ) (hπ : IsStationary (rates N x ε) π)
    (hWs' : Summable (fun n => π n * wsum N n)) (i : Idx N) :
    HasSum (fun n => π n * nx N x n i) ((1 - ε) * rho0 N i) := by
  classical
  have hπ0 := hπ.1
  have hπs : Summable π := hπ.2.1.summable
  obtain ⟨r, k⟩ := i
  have hnxs : ∀ k : Phase (N.D r), Summable (fun n => π n * nx N x n ⟨r, k⟩) := by
    intro k
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hπ0 n)
      (mul_nonneg (Nat.cast_nonneg _) (x_nonneg' N _ _ (hx _) _))) (fun n => ?_)
      (hπs.mul_right (∑ ℓ, N.C ℓ))
    exact mul_le_mul_of_nonneg_left (nx_le N hH01 hroute hC x hx n ⟨r, k⟩) (hπ0 n)
  set E : Phase (N.D r) → ℝ := fun k => ∑' n, π n * nx N x n ⟨r, k⟩ with hE
  have hEq : ∀ k₀ : Phase (N.D r), (1 - ε) * N.lam0 r * (N.D r).init k₀ +
      ∑ k₁, subgen (N.D r) k₁ k₀ * E k₁ = 0 := by
    intro k₀
    have h := stat_lin N hH01 hroute hC hκ hlam0 x hx ε hε hε1 π hπ hWs' (Pi.single ⟨r, k₀⟩ 1)
      (fun j => by by_cases hj : j = ⟨r, k₀⟩ <;> simp [Pi.single_apply, hj])
    simp_rw [drift_single, mul_add, Finset.mul_sum] at h
    have h2 : HasSum (fun n => π n * ((1 - ε) * N.lam0 r * (N.D r).init k₀) +
        ∑ k₁, π n * (subgen (N.D r) k₁ k₀ * nx N x n ⟨r, k₁⟩))
        (1 * ((1 - ε) * N.lam0 r * (N.D r).init k₀) + ∑ k₁, subgen (N.D r) k₁ k₀ * E k₁) := by
      refine (hπ.2.1.mul_right _ |>.congr_fun ?_).add (hasSum_sum (fun k₁ _ => ?_))
      · intro n; ring
      · have := ((hnxs k₁).hasSum).mul_left (subgen (N.D r) k₁ k₀)
        refine this.congr_fun (fun n => ?_)
        ring
    have := h.unique h2
    linarith
  have hvec : E ᵥ* (-subgen (N.D r)) = (fun k => (1 - ε) * rho0 N ⟨r, k⟩) ᵥ* (-subgen (N.D r)) := by
    have hρ := rho0_vecMul N r
    funext k₀
    have h1 := hEq k₀
    have h2 := congrFun hρ k₀
    simp only [vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.neg_apply] at h2 ⊢
    have e1 : ∑ k₁, E k₁ * -subgen (N.D r) k₁ k₀ = -∑ k₁, subgen (N.D r) k₁ k₀ * E k₁ := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro _ _; ring
    have e2 : ∑ k₁, (1 - ε) * rho0 N ⟨r, k₁⟩ * -subgen (N.D r) k₁ k₀ =
        (1 - ε) * ∑ k₁, rho0 N ⟨r, k₁⟩ * -subgen (N.D r) k₁ k₀ := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro _ _; ring
    rw [e1, e2, h2]
    linarith
  have hinjv : Function.Injective (fun v : Phase (N.D r) → ℝ => v ᵥ* (-subgen (N.D r))) :=
    Matrix.vecMul_injective_iff_isUnit.2 (neg_subgen_isUnit (N.D r))
  have hEe := hinjv hvec
  have := congrFun hEe k
  simp only [hE] at this
  rw [← this]
  exact (hnxs k).hasSum


lemma vecMul_bd {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → Type*} [∀ i, Fintype (m i)]
    (A : ∀ i, Matrix (m i) (m i) ℝ) (b : (Σ i, m i) → ℝ) (r : ι) (k : m r) :
    (b ᵥ* blockDiagonal' A) ⟨r, k⟩ = ((fun k' => b ⟨r, k'⟩) ᵥ* A r) k := by
  simp only [vecMul, dotProduct]
  rw [Fintype.sum_sigma, Finset.sum_eq_single r]
  · apply Finset.sum_congr rfl
    intro k' _
    rw [blockDiagonal'_apply_eq]
  · intro r' _ hne
    apply Finset.sum_eq_zero
    intro k' _
    rw [blockDiagonal'_apply_ne _ _ _ hne, mul_zero]
  · intro h; exact absurd (Finset.mem_univ r) h

/-- `((-S) M b^(ℓ))_{r,k} = h_{ℓ r}` (Lemma 5). -/
lemma negS_Mb (N : BWNetwork L R) (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (ℓ : Fin L) (r : Fin R) (k : Phase (N.D r)) :
    ((-Sfull N) *ᵥ (bvec N ℓ ᵥ* Mfull N)) ⟨r, k⟩ = N.H ℓ r := by
  have h5 := lemma_5 N hκ hlam0
  have e1 : (-Sfull N) *ᵥ (bvec N ℓ ᵥ* Mfull N) = -(Sfull N *ᵥ (bvec N ℓ ᵥ* Mfull N)) := by
    rw [Matrix.neg_mulVec]
  rw [e1, Pi.neg_apply, Sfull, mulVec_bd]
  have e2 : (fun k' => (bvec N ℓ ᵥ* Mfull N) ⟨r, k'⟩) =
      (N.H ℓ r / N.κ r) • (phaseLoad (N.D r) (N.lam0 r) ᵥ* Mr N r) := by
    funext k'
    rw [Mfull, vecMul_bd]
    simp only [vecMul, dotProduct, bvec, rho0, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [e2]
  have h := congrFun (h5 r) k
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [← Matrix.vecMul_vecMul, vecMul_transpose] at h
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have e3 : (-(subgen (N.D r) *ᵥ (phaseLoad (N.D r) (N.lam0 r) ᵥ* Mr N r)) k) =
      ((-subgen (N.D r)) *ᵥ (phaseLoad (N.D r) (N.lam0 r) ᵥ* Mr N r)) k := by
    rw [Matrix.neg_mulVec]; rfl
  calc -(N.H ℓ r / N.κ r * (subgen (N.D r) *ᵥ (phaseLoad (N.D r) (N.lam0 r) ᵥ* Mr N r)) k)
      = N.H ℓ r * (1 / N.κ r * ((-subgen (N.D r)) *ᵥ (phaseLoad (N.D r) (N.lam0 r) ᵥ* Mr N r)) k) := by
        rw [← e3]; ring
    _ = N.H ℓ r := by rw [h, mul_one]

/-- the vectors `u_i = B_s M e_i` -/
noncomputable def uvec (N : BWNetwork L R) (i : Idx N) : critical N → ℝ :=
  Bs N *ᵥ (Mfull N *ᵥ unitVec N i)

lemma uvec_apply (N : BWNetwork L R) (i : Idx N) (ℓ : critical N) :
    uvec N i ℓ = (bvec N ℓ ᵥ* Mfull N) i := by
  classical
  unfold uvec
  rw [Matrix.mulVec_mulVec]
  simp only [mulVec, dotProduct, unitVec, Matrix.mul_apply, Bs, Matrix.of_apply, vecMul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma c_eq (N : BWNetwork L R) (hpd : (Mfull N).PosDef)
    (hinj : Function.Injective (Bs N).vecMul) (i j : Idx N) :
    mInner N (projS N (unitVec N i)) (projS N (unitVec N j)) =
      ((Bs N * Mfull N * (Bs N)ᵀ)⁻¹ *ᵥ uvec N i) ⬝ᵥ uvec N j := by
  rw [inner_projS_projS N hpd hinj]
  unfold projS mInner alphaS uvec
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]


/-- `ρ_rᵀ M_r ρ_r` -/
noncomputable def qr (N : BWNetwork L R) (r : Fin R) : ℝ :=
  (fun k => rho0 N ⟨r, k⟩) ⬝ᵥ ((fun k => rho0 N ⟨r, k⟩) ᵥ* Mr N r)

lemma qr_nonneg (N : BWNetwork L R) (hMr : ∀ r, (Mr N r).PosDef) (r : Fin R) : 0 ≤ qr N r := by
  unfold qr
  rw [dotProduct_comm, ← Matrix.dotProduct_mulVec]
  have := (hMr r).posSemidef.dotProduct_mulVec_nonneg (fun k => rho0 N ⟨r, k⟩)
  simpa using this

lemma sum_negS_u (N : BWNetwork L R) (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (r : Fin R) (k₁ : Phase (N.D r)) :
    ∑ k₂, (-subgen (N.D r)) k₁ k₂ • uvec N ⟨r, k₂⟩ = fun ℓ : critical N => N.H ℓ r := by
  funext ℓ
  have h := negS_Mb N hκ hlam0 ℓ r k₁
  have hS : -Sfull N = blockDiagonal' (fun r => -subgen (N.D r)) := by
    rw [Sfull, ← blockDiagonal'_neg]; rfl
  rw [hS, mulVec_bd] at h
  rw [← h]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, uvec_apply]

lemma sum_rho_u (N : BWNetwork L R) (r : Fin R) :
    ∑ k, rho0 N ⟨r, k⟩ • uvec N ⟨r, k⟩ = fun ℓ : critical N => N.H ℓ r / N.κ r * qr N r := by
  funext ℓ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, uvec_apply]
  have e : ∀ k, (bvec N ℓ ᵥ* Mfull N) ⟨r, k⟩ =
      N.H ℓ r / N.κ r * ((fun k => rho0 N ⟨r, k⟩) ᵥ* Mr N r) k := by
    intro k
    rw [Mfull, vecMul_bd]
    simp only [vecMul, dotProduct, bvec, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  simp_rw [e]
  unfold qr
  simp only [dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _; ring

lemma G_entry (N : BWNetwork L R) (ℓ ℓ' : critical N) :
    (Bs N * Mfull N * (Bs N)ᵀ) ℓ ℓ' = ∑ r, N.H ℓ r * N.H ℓ' r / N.κ r ^ 2 * qr N r := by
  have e : (Bs N * Mfull N * (Bs N)ᵀ) ℓ ℓ' = (bvec N ℓ ᵥ* Mfull N) ⬝ᵥ bvec N ℓ' := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Bs, Matrix.of_apply, dotProduct, vecMul]
  rw [e]
  simp only [dotProduct]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl; intro r _
  have e2 : ∀ k, (bvec N ℓ ᵥ* Mfull N) ⟨r, k⟩ =
      N.H ℓ r / N.κ r * ((fun k => rho0 N ⟨r, k⟩) ᵥ* Mr N r) k := by
    intro k
    rw [Mfull, vecMul_bd]
    simp only [vecMul, dotProduct, bvec, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  simp_rw [e2]
  unfold qr
  simp only [dotProduct, Finset.mul_sum, bvec]
  apply Finset.sum_congr rfl; intro k _
  ring


lemma route_sum (N : BWNetwork L R) (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (r : Fin R) :
    (∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r), rho0 N ⟨r, k₁⟩ * (-subgen (N.D r)) k₁ k₂ *
      (((Bs N * Mfull N * (Bs N)ᵀ)⁻¹ *ᵥ uvec N ⟨r, k₁⟩) ⬝ᵥ uvec N ⟨r, k₂⟩)) =
      qr N r / N.κ r * ((fun ℓ : critical N => N.H ℓ r) ⬝ᵥ
        ((Bs N * Mfull N * (Bs N)ᵀ)⁻¹ *ᵥ (fun ℓ : critical N => N.H ℓ r))) := by
  set Gi := (Bs N * Mfull N * (Bs N)ᵀ)⁻¹ with hGi
  have step1 : ∀ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r), rho0 N ⟨r, k₁⟩ * (-subgen (N.D r)) k₁ k₂ *
      ((Gi *ᵥ uvec N ⟨r, k₁⟩) ⬝ᵥ uvec N ⟨r, k₂⟩) = rho0 N ⟨r, k₁⟩ * ((Gi *ᵥ uvec N ⟨r, k₁⟩) ⬝ᵥ (fun ℓ : critical N => N.H ℓ r)) := by
    intro k₁
    have hs := sum_negS_u N hκ hlam0 r k₁
    rw [← hs, dotProduct_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k₂ _
    rw [dotProduct_smul, smul_eq_mul]; ring
  rw [Finset.sum_congr rfl (fun k₁ _ => step1 k₁)]
  have step2 : ∑ k₁ : Phase (N.D r), rho0 N ⟨r, k₁⟩ * ((Gi *ᵥ uvec N ⟨r, k₁⟩) ⬝ᵥ (fun ℓ : critical N => N.H ℓ r)) =
      (Gi *ᵥ (∑ k₁ : Phase (N.D r), rho0 N ⟨r, k₁⟩ • uvec N ⟨r, k₁⟩)) ⬝ᵥ (fun ℓ : critical N => N.H ℓ r) := by
    rw [Matrix.mulVec_sum, sum_dotProduct]
    apply Finset.sum_congr rfl; intro k₁ _
    rw [Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul]
  rw [step2, sum_rho_u]
  have e : (fun ℓ : critical N => N.H ℓ r / N.κ r * qr N r) =
      (qr N r / N.κ r) • (fun ℓ : critical N => N.H ℓ r) := by
    funext ℓ; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [e, Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul, dotProduct_comm]

lemma sum_t (N : BWNetwork L R) (hpd : (Mfull N).PosDef)
    (hinj : Function.Injective (Bs N).vecMul) :
    ∑ r, qr N r / N.κ r ^ 2 * ((fun ℓ : critical N => N.H ℓ r) ⬝ᵥ
        ((Bs N * Mfull N * (Bs N)ᵀ)⁻¹ *ᵥ (fun ℓ : critical N => N.H ℓ r))) =
      ((critical N).card : ℝ) := by
  classical
  set G := Bs N * Mfull N * (Bs N)ᵀ with hG
  have hu := G_isUnit N hpd hinj
  have hGG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  have hsym : ∀ ℓ ℓ', G ℓ ℓ' = G ℓ' ℓ := by
    intro ℓ ℓ'
    rw [hG, G_entry, G_entry]
    apply Finset.sum_congr rfl; intro r _; ring
  have e1 : ∀ r, qr N r / N.κ r ^ 2 * ((fun ℓ : critical N => N.H ℓ r) ⬝ᵥ
        (G⁻¹ *ᵥ (fun ℓ : critical N => N.H ℓ r))) =
      ∑ ℓ, ∑ ℓ', G⁻¹ ℓ ℓ' * (N.H ℓ r * N.H ℓ' r / N.κ r ^ 2 * qr N r) := by
    intro r
    simp only [dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro ℓ _
    apply Finset.sum_congr rfl; intro ℓ' _
    ring
  rw [Finset.sum_congr rfl (fun r _ => e1 r), Finset.sum_comm]
  have e2 : ∀ ℓ : critical N, ∑ r, ∑ ℓ', G⁻¹ ℓ ℓ' * (N.H ℓ r * N.H ℓ' r / N.κ r ^ 2 * qr N r) =
      (G⁻¹ * G) ℓ ℓ := by
    intro ℓ
    rw [Finset.sum_comm, Matrix.mul_apply]
    apply Finset.sum_congr rfl; intro ℓ' _
    rw [← Finset.mul_sum, hsym ℓ' ℓ, hG, G_entry]
  rw [Finset.sum_congr rfl (fun ℓ _ => e2 ℓ), hGG]
  simp


lemma alg_identity {K : Type*} [Fintype K] [DecidableEq K] (ρ a e : K → ℝ) (S c : K → K → ℝ)
    (hρ : ∀ k₂, ∑ k₁, ρ k₁ * -S k₁ k₂ = a k₂) (he : ∀ k, e k = -∑ j, S k j) :
    (∑ k, a k * c k k) +
      (∑ k₁, ∑ k₂, if k₁ ≠ k₂ then ρ k₁ * S k₁ k₂ * (c k₂ k₂ + c k₁ k₁ - 2 * c k₁ k₂) else 0) +
      (∑ k, ρ k * e k * c k k) =
    2 * ∑ k₁, ∑ k₂, ρ k₁ * -S k₁ k₂ * c k₁ k₂ := by
  have hdrop : ∀ k₁ k₂, (if k₁ ≠ k₂ then ρ k₁ * S k₁ k₂ * (c k₂ k₂ + c k₁ k₁ - 2 * c k₁ k₂) else 0) =
      ρ k₁ * S k₁ k₂ * c k₂ k₂ + ρ k₁ * S k₁ k₂ * c k₁ k₁ - 2 * (ρ k₁ * S k₁ k₂ * c k₁ k₂) := by
    intro k₁ k₂
    split_ifs with h
    · ring
    · push_neg at h; subst h; ring
  simp_rw [hdrop, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 : ∑ k₁, ∑ k₂, ρ k₁ * S k₁ k₂ * c k₂ k₂ = -∑ k, a k * c k k := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro k₂ _
    rw [← hρ k₂, Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro k₁ _; ring
  have h2 : ∑ k₁, ∑ k₂, ρ k₁ * S k₁ k₂ * c k₁ k₁ = -∑ k, ρ k * e k * c k k := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro k _
    rw [he k, ← Finset.sum_mul, ← Finset.mul_sum]; ring
  have h3 : ∑ k₁, ∑ k₂, 2 * (ρ k₁ * S k₁ k₂ * c k₁ k₂) = -(2 * ∑ k₁, ∑ k₂, ρ k₁ * -S k₁ k₂ * c k₁ k₂) := by
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro k₁ _
    apply Finset.sum_congr rfl; intro k₂ _; ring
  rw [h1, h2, h3]; ring

end HTInsensBWE86

open HTInsensBW.PhaseType HTInsensBWE86 Matrix Finset

set_option maxHeartbeats 1000000 in
theorem solution {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1) (hrank : N.H.rank = L)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (hload : ∀ ℓ, ∑ r, N.H ℓ r * routeLoad0 N r ≤ N.C ℓ) (hLs : (critical N).Nonempty)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ π : State N → ℝ, IsStationary (rates N x ε) π →
      Summable (fun n => π n * B1 N x ε n) ∧
      (1 - ε) * ((critical N).card : ℝ) * kappaMin N ≤ (1 / 2) * ∑' n, π n * B1 N x ε n ∧
      (1 / 2) * ∑' n, π n * B1 N x ε n ≤ (1 - ε) * ((critical N).card : ℝ) * kappaMax N := by
  classical
  obtain ⟨M1, -, hW1⟩ := W_moment N hH01 hrank hroute hC hκ hlam0 hload hLs x hx 0
  have h11 := lemma_11 N hκ hlam0
  have hpd := h11.2
  have hMr : ∀ r, (Mr N r).PosDef := fun r => (h11.1 r).2
  have hinj := Bs_vecMul_injective N hrank hκ hlam0
  intro ε hε hε1 π hπ
  have hπ0 := hπ.1
  obtain ⟨hWs1, -⟩ := hW1 ε hε hε1 π hπ
  have hWs : Summable (fun n => π n * wsum N n) := by simpa using hWs1
  have hmean := mean_nx N hH01 hroute hC hκ hlam0 x hx ε hε hε1 π hπ hWs
  -- notation
  set m : Idx N → ℝ := fun i => msq N (projS N (unitVec N i)) with hm
  set m2 : ∀ r : Fin R, Phase (N.D r) → Phase (N.D r) → ℝ := fun r k₁ k₂ =>
    msq N (projS N (unitVec N ⟨r, k₂⟩) - projS N (unitVec N ⟨r, k₁⟩)) with hm2
  -- expected value of B1
  set Bbar : ℝ := ∑ r : Fin R,
    ((∑ k : Phase (N.D r), (1 - ε) * N.lam0 r * (N.D r).init k * m ⟨r, k⟩) +
     (∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
        if k₁ ≠ k₂ then subgen (N.D r) k₁ k₂ * m2 r k₁ k₂ * ((1 - ε) * rho0 N ⟨r, k₁⟩) else 0) +
     (∑ k : Phase (N.D r), exitRate (N.D r) k * m ⟨r, k⟩ * ((1 - ε) * rho0 N ⟨r, k⟩))) with hBbar
  have hB1eq : ∀ n, π n * B1 N x ε n = ∑ r : Fin R,
      ((∑ k : Phase (N.D r), π n * ((1 - ε) * N.lam0 r * (N.D r).init k * m ⟨r, k⟩)) +
       (∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
          if k₁ ≠ k₂ then subgen (N.D r) k₁ k₂ * m2 r k₁ k₂ * (π n * nx N x n ⟨r, k₁⟩) else 0) +
       (∑ k : Phase (N.D r), exitRate (N.D r) k * m ⟨r, k⟩ * (π n * nx N x n ⟨r, k⟩))) := by
    intro n
    unfold B1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1; congr 1
    · apply Finset.sum_congr rfl; intro k₁ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k₂ _
      split_ifs
      · simp only [hm2, nx]; ring
      · ring
    · apply Finset.sum_congr rfl; intro k _
      simp only [hm, nx]; ring
  have hB1sum : HasSum (fun n => π n * B1 N x ε n) Bbar := by
    simp_rw [hB1eq]
    apply hasSum_sum; intro r _
    refine HasSum.add (HasSum.add ?_ ?_) ?_
    · apply hasSum_sum; intro k _
      have := hπ.2.1.mul_right ((1 - ε) * N.lam0 r * (N.D r).init k * m ⟨r, k⟩)
      rw [one_mul] at this
      exact this
    · apply hasSum_sum; intro k₁ _
      apply hasSum_sum; intro k₂ _
      split_ifs
      · exact (hmean ⟨r, k₁⟩).mul_left _
      · exact hasSum_zero
    · apply hasSum_sum; intro k _
      exact (hmean ⟨r, k⟩).mul_left _
  -- algebra: Bbar = 2 (1-ε) Σ_r κ_r t_r
  set Gi := (Bs N * Mfull N * (Bs N)ᵀ)⁻¹ with hGi
  set t : Fin R → ℝ := fun r => qr N r / N.κ r ^ 2 *
    ((fun ℓ : critical N => N.H ℓ r) ⬝ᵥ (Gi *ᵥ (fun ℓ : critical N => N.H ℓ r))) with ht
  have hGpd : (Bs N * Mfull N * (Bs N)ᵀ).PosDef := by
    have := hpd.mul_mul_conjTranspose_same hinj
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hGipd : Gi.PosDef := hGpd.inv
  have ht0 : ∀ r, 0 ≤ t r := by
    intro r
    have h1 := qr_nonneg N hMr r
    have h2 := hGipd.posSemidef.dotProduct_mulVec_nonneg (fun ℓ : critical N => N.H ℓ r)
    simp only [star_trivial] at h2
    have := hκ r
    simp only [ht]
    positivity
  have hsumt : ∑ r, t r = ((critical N).card : ℝ) := sum_t N hpd hinj
  set c : Idx N → Idx N → ℝ := fun i j => mInner N (projS N (unitVec N i)) (projS N (unitVec N j))
    with hc
  have hroute_eq : ∀ r : Fin R,
      ((∑ k : Phase (N.D r), (1 - ε) * N.lam0 r * (N.D r).init k * m ⟨r, k⟩) +
       (∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
          if k₁ ≠ k₂ then subgen (N.D r) k₁ k₂ * m2 r k₁ k₂ * ((1 - ε) * rho0 N ⟨r, k₁⟩) else 0) +
       (∑ k : Phase (N.D r), exitRate (N.D r) k * m ⟨r, k⟩ * ((1 - ε) * rho0 N ⟨r, k⟩))) =
      (1 - ε) * (2 * (N.κ r * t r)) := by
    intro r
    have hm2c : ∀ k₁ k₂ : Phase (N.D r), m2 r k₁ k₂ =
        c ⟨r, k₂⟩ ⟨r, k₂⟩ + c ⟨r, k₁⟩ ⟨r, k₁⟩ - 2 * c ⟨r, k₁⟩ ⟨r, k₂⟩ := by
      intro k₁ k₂
      simp only [hm2, hc]
      rw [sub_eq_add_neg, msq_add N hpd, msq_neg, mInner_neg_right,
        mInner_comm N hpd (projS N (unitVec N ⟨r, k₂⟩))]
      simp only [msq]; ring
    have hmc : ∀ k : Phase (N.D r), m ⟨r, k⟩ = c ⟨r, k⟩ ⟨r, k⟩ := fun k => rfl
    have hid := alg_identity (fun k => rho0 N ⟨r, k⟩) (fun k => N.lam0 r * (N.D r).init k)
      (exitRate (N.D r)) (subgen (N.D r)) (fun k₁ k₂ => c ⟨r, k₁⟩ ⟨r, k₂⟩)
      (fun k₂ => by
        have := congrFun (rho0_vecMul N r) k₂
        simpa [vecMul, dotProduct] using this)
      (fun k => by unfold exitRate; rw [Finset.sum_neg_distrib])
    have hrs := route_sum N hκ hlam0 r
    have hceq : ∀ k₁ k₂ : Phase (N.D r), c ⟨r, k₁⟩ ⟨r, k₂⟩ =
        (Gi *ᵥ uvec N ⟨r, k₁⟩) ⬝ᵥ uvec N ⟨r, k₂⟩ := fun k₁ k₂ => c_eq N hpd hinj _ _
    have e1 : (∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
        rho0 N ⟨r, k₁⟩ * -subgen (N.D r) k₁ k₂ * c ⟨r, k₁⟩ ⟨r, k₂⟩) = N.κ r * t r := by
      simp_rw [hceq]
      have : ∀ k₁ k₂ : Phase (N.D r), rho0 N ⟨r, k₁⟩ * -subgen (N.D r) k₁ k₂ =
          rho0 N ⟨r, k₁⟩ * (-subgen (N.D r)) k₁ k₂ := fun _ _ => rfl
      simp_rw [this]
      rw [hrs]
      simp only [ht]
      have := (hκ r).ne'
      field_simp
      rw [hGi]
    rw [← e1, ← hid]
    simp_rw [hm2c, hmc]
    simp only [mul_add, Finset.mul_sum]
    congr 1; congr 1
    · apply Finset.sum_congr rfl; intro k _; ring
    · apply Finset.sum_congr rfl; intro k₁ _
      apply Finset.sum_congr rfl; intro k₂ _
      split_ifs <;> ring
    · apply Finset.sum_congr rfl; intro k _; ring
  have hBbar : Bbar = (1 - ε) * (2 * ∑ r, N.κ r * t r) := by
    rw [hBbar, Finset.sum_congr rfl (fun r _ => hroute_eq r), ← Finset.mul_sum, ← Finset.mul_sum]
  refine ⟨hB1sum.summable, ?_, ?_⟩
  · rw [hB1sum.tsum_eq, hBbar, ← hsumt]
    have : kappaMin N * ∑ r, t r ≤ ∑ r, N.κ r * t r := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro r _
      exact mul_le_mul_of_nonneg_right (ciInf_le (Finite.bddBelow_range _) r) (ht0 r)
    have h1 : 0 ≤ 1 - ε := by linarith
    nlinarith
  · rw [hB1sum.tsum_eq, hBbar, ← hsumt]
    have : ∑ r, N.κ r * t r ≤ kappaMax N * ∑ r, t r := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro r _
      exact mul_le_mul_of_nonneg_right (le_ciSup (Finite.bddAbove_range _) r) (ht0 r)
    have h1 : 0 ≤ 1 - ε := by linarith
    nlinarith
