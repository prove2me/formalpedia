-- Prove2me | solution 2 for MatousekLP.ZeroSum.minimax_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T05:56:11.707711+00:00
-- url     : https://prove2.me/submissions/22c673ab-bac7-4c49-8d16-73733279349f

import Mathlib
import Definitions.Def_MatousekLP_Duality_Cones
import Definitions.Def_MatousekLP_ZeroSum_Game
import Definitions.Def_MatousekLP_ZeroSum_GameLP
import Theorems.Thm_MatousekLP_Duality_farkas_geometric

-- carved verbatim out of submission c7c10947-f6a0-4c9b-a628-a2393f946746, lines 564-602

section
open Finset
open Matrix MatousekLP.ZeroSum
variable {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)

lemma continuous_payoff_left (y : Fin n → ℝ) : Continuous (fun x => payoff M x y) := by
  unfold payoff; fun_prop

lemma le_alpha (y : Fin n → ℝ) {x : Fin m → ℝ} (hx : x ∈ stdSimplex ℝ (Fin m)) :
    payoff M x y ≤ alpha M y :=
  le_csSup ((isCompact_stdSimplex ℝ (Fin m)).image (continuous_payoff_left M y)).bddAbove
    ⟨x, hx, rfl⟩

lemma payoff_single_left (i : Fin m) (y : Fin n → ℝ) : payoff M (Pi.single i 1) y = (M *ᵥ y) i := by
  simp [payoff, single_dotProduct]

lemma alpha_le_iff (hm : 1 ≤ m) (y : Fin n → ℝ) (t : ℝ) :
    alpha M y ≤ t ↔ ∀ i, (M *ᵥ y) i ≤ t := by
  constructor
  · intro h i
    have := le_alpha M y (single_mem_stdSimplex ℝ i)
    rw [payoff_single_left] at this; linarith
  · intro h
    refine csSup_le ⟨_, ⟨Pi.single ⟨0, hm⟩ 1, single_mem_stdSimplex ℝ _, rfl⟩⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    simp only [payoff, dotProduct]
    calc ∑ i, x i * (M *ᵥ y) i ≤ ∑ i, x i * t :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hx.1 i)
      _ = t := by rw [← Finset.sum_mul, hx.2, one_mul]

lemma alpha_eq_sup (hm : 1 ≤ m) (y : Fin n → ℝ) :
    alpha M y = Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i => (M *ᵥ y) i) := by
  apply le_antisymm
  · rw [alpha_le_iff M hm]; intro i; exact Finset.le_sup' (fun i => (M *ᵥ y) i) (Finset.mem_univ i)
  · exact Finset.sup'_le _ _ fun i _ => (alpha_le_iff M hm y _).mp le_rfl i

lemma continuous_payoff_right (x : Fin m → ℝ) : Continuous (fun y => payoff M x y) := by
  unfold payoff; fun_prop

lemma beta_le (x : Fin m → ℝ) {y : Fin n → ℝ} (hy : y ∈ stdSimplex ℝ (Fin n)) :
    beta M x ≤ payoff M x y :=
  csInf_le ((isCompact_stdSimplex ℝ (Fin n)).image (continuous_payoff_right M x)).bddBelow
    ⟨y, hy, rfl⟩

lemma continuous_alpha (hm : 1 ≤ m) : Continuous (alpha M) := by
  have : alpha M = fun y => Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i => (M *ᵥ y) i) :=
    funext (alpha_eq_sup M hm)
  rw [this]
  exact Continuous.finset_sup'_apply _ fun i _ => (continuous_apply i).comp (Continuous.matrix_mulVec continuous_const continuous_id)

end

section
open Finset
open Matrix MatousekLP.Duality

theorem farkas_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    exact dotProduct_nonneg_of_nonneg hx hy
  · intro h
    set a : Fin n → EuclideanSpace ℝ (Fin m) := fun j => WithLp.toLp 2 (fun i => A i j)
    rcases MatousekLP.Duality.farkas_geometric a (WithLp.toLp 2 b) with ⟨hb, -⟩ | ⟨⟨y, hy, hyb⟩, -⟩
    · obtain ⟨t, ht, hbt⟩ := hb
      refine ⟨t, fun i => ht i, ?_⟩
      have hb' : b = ∑ j, t j • (fun i => A i j) := by
        have := congrArg WithLp.ofLp hbt
        simpa [a, WithLp.ofLp_sum, WithLp.ofLp_smul] using this
      rw [hb']
      funext i
      simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
    · exfalso
      set y' : Fin m → ℝ := WithLp.ofLp y
      have hy' : 0 ≤ Aᵀ *ᵥ y' := by
        intro j
        have := hy j
        simp only [a] at this
        have hy_eq : y = WithLp.toLp 2 y' := rfl
        rw [hy_eq, EuclideanSpace.inner_toLp_toLp] at this
        simpa [mulVec, dotProduct, transpose_apply, mul_comm] using this
      have := h y' hy'
      have hy_eq : y = WithLp.toLp 2 y' := rfl
      rw [hy_eq, EuclideanSpace.inner_toLp_toLp] at hyb
      simp only [star_trivial] at hyb
      rw [dotProduct_comm] at hyb
      linarith

theorem farkas_eq_fintype {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) :
    (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  set e := Fintype.equivFin ι
  set A' : Matrix (Fin m) (Fin (Fintype.card ι)) ℝ := A.submatrix id e.symm
  have hmul : ∀ x : ι → ℝ, A' *ᵥ (x ∘ e.symm) = A *ᵥ x := by
    intro x; funext i
    simp only [A', mulVec, dotProduct, submatrix_apply, id, Function.comp]
    exact Equiv.sum_comp e.symm (fun j => A i j * x j)
  have htr : ∀ y : Fin m → ℝ, A'ᵀ *ᵥ y = (Aᵀ *ᵥ y) ∘ e.symm := by
    intro y; funext j; simp [A', mulVec, dotProduct, transpose_apply]
  have hnonneg : ∀ y : Fin m → ℝ, (0 ≤ A'ᵀ *ᵥ y ↔ 0 ≤ Aᵀ *ᵥ y) := by
    intro y; rw [htr]
    constructor
    · intro h j; simpa using h (e j)
    · intro h j; exact h _
  rw [show (∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) ↔
      (∀ y : Fin m → ℝ, 0 ≤ A'ᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) from
      forall_congr' fun y => by rw [hnonneg]]
  rw [← farkas_eq A' b]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x ∘ e.symm, fun j => hx _, hmul x⟩
  · rintro ⟨x', hx', rfl⟩
    refine ⟨x' ∘ e, fun j => hx' _, ?_⟩
    rw [← hmul]; congr 1; funext j; simp

theorem farkas_eq_gen {ρ ι : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι]
    (A : Matrix ρ ι ℝ) (b : ρ → ℝ) :
    (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : ρ → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  set e := Fintype.equivFin ρ
  set A' : Matrix (Fin (Fintype.card ρ)) ι ℝ := A.submatrix e.symm id
  have h := farkas_eq_fintype A' (b ∘ e.symm)
  have hrow : ∀ x : ι → ℝ, A' *ᵥ x = (A *ᵥ x) ∘ e.symm := by
    intro x; funext r; simp [A', mulVec, dotProduct]
  have hcol : ∀ y' : Fin (Fintype.card ρ) → ℝ, A'ᵀ *ᵥ y' = Aᵀ *ᵥ (y' ∘ e) := by
    intro y'; funext j
    simp only [A', mulVec, dotProduct, transpose_apply, submatrix_apply, id, Function.comp]
    rw [← Equiv.sum_comp e (fun x => A (e.symm x) j * y' x)]
    simp
  have hdot : ∀ y' : Fin (Fintype.card ρ) → ℝ, y' ⬝ᵥ (b ∘ e.symm) = (y' ∘ e) ⬝ᵥ b := by
    intro y'
    simp only [dotProduct, Function.comp]
    rw [← Equiv.sum_comp e (fun x => y' x * b (e.symm x))]
    simp
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    exact dotProduct_nonneg_of_nonneg hx hy
  · intro hy
    obtain ⟨x, hx, hAx⟩ := h.mpr fun y' hy' => by
      rw [hcol] at hy'; rw [hdot]; exact hy _ hy'
    refine ⟨x, hx, ?_⟩
    funext r
    have := congrFun hAx (e r)
    rw [hrow] at this; simpa using this

theorem farkas_le_gen {ρ ι : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι]
    (A : Matrix ρ ι ℝ) (b : ρ → ℝ) :
    (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x ≤ b) ↔ ∀ y : ρ → ℝ, 0 ≤ y → 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  have h := farkas_eq_gen (fromCols A (1 : Matrix ρ ρ ℝ)) b
  have hleft : (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x ≤ b) ↔
      ∃ z : ι ⊕ ρ → ℝ, 0 ≤ z ∧ fromCols A 1 *ᵥ z = b := by
    constructor
    · rintro ⟨x, hx, hAx⟩
      refine ⟨Sum.elim x (b - A *ᵥ x), fun j => ?_, ?_⟩
      · rcases j with j | j
        · exact hx j
        · simpa using hAx j
      · rw [fromCols_mulVec_sumElim, one_mulVec]; abel
    · rintro ⟨z, hz, hzb⟩
      refine ⟨fun j => z (Sum.inl j), fun j => hz _, ?_⟩
      have hz' : z = Sum.elim (fun j => z (Sum.inl j)) (fun j => z (Sum.inr j)) := by
        funext j; rcases j <;> rfl
      rw [hz', fromCols_mulVec_sumElim, one_mulVec] at hzb
      intro i
      have h1 := congrFun hzb i
      have h2 := hz (Sum.inr i)
      simp only [Pi.add_apply, Pi.zero_apply] at h1 h2
      linarith
  have hright : (∀ y : ρ → ℝ, 0 ≤ (fromCols A (1 : Matrix ρ ρ ℝ))ᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) ↔
      ∀ y : ρ → ℝ, 0 ≤ y → 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
    refine forall_congr' fun y => ?_
    rw [transpose_fromCols, transpose_one]
    constructor
    · intro hh hy hAy
      refine hh fun j => ?_
      rcases j with j | j
      · simpa [fromRows_mulVec] using hAy j
      · simpa [fromRows_mulVec] using hy j
    · intro hh hpos
      exact hh (fun i => by simpa [fromRows_mulVec] using hpos (Sum.inr i))
        (fun j => by simpa [fromRows_mulVec] using hpos (Sum.inl j))
  rw [hleft, h, hright]

end

section
open Finset
open Matrix MatousekLP.ZeroSum
variable {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)

lemma payoff_single_right (x : Fin m → ℝ) (j : Fin n) :
    payoff M x (Pi.single j 1) = (Mᵀ *ᵥ x) j := by
  simp only [payoff, dotProduct, mulVec, transpose_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
  simp [mul_comm]

lemma le_beta_iff (hn : 1 ≤ n) (x : Fin m → ℝ) (t : ℝ) :
    t ≤ beta M x ↔ ∀ j, t ≤ (Mᵀ *ᵥ x) j := by
  constructor
  · intro h j
    have := beta_le M x (single_mem_stdSimplex ℝ j)
    rw [payoff_single_right] at this; linarith
  · intro h
    refine le_csInf ⟨_, ⟨Pi.single ⟨0, hn⟩ 1, single_mem_stdSimplex ℝ _, rfl⟩⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    show t ≤ payoff M x y
    have hpay : payoff M x y = ∑ j, y j * (Mᵀ *ᵥ x) j := by
      simp only [payoff, dotProduct, mulVec, transpose_apply, Finset.mul_sum]
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [hpay]
    calc t = ∑ j, y j * t := by rw [← Finset.sum_mul, hy.2, one_mul]
      _ ≤ ∑ j, y j * (Mᵀ *ᵥ x) j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hy.1 j)

lemma exists_beta_ge (hm : 1 ≤ m) (hn : 1 ≤ n) (yt : Fin n → ℝ)
    (hmin : ∀ y ∈ stdSimplex ℝ (Fin n), alpha M yt ≤ alpha M y) :
    ∃ x ∈ stdSimplex ℝ (Fin m), alpha M yt ≤ beta M x := by
  classical
  set v := alpha M yt
  set B : Matrix (Fin n ⊕ (Unit ⊕ Unit)) (Fin m) ℝ := fun r i =>
    match r with
    | .inl j => -M i j
    | .inr (.inl _) => 1
    | .inr (.inr _) => -1
  set d : Fin n ⊕ (Unit ⊕ Unit) → ℝ := Sum.elim (fun _ => -v) (Sum.elim (fun _ => 1) (fun _ => -1))
  by_cases hfeas : ∃ x : Fin m → ℝ, 0 ≤ x ∧ B *ᵥ x ≤ d
  · obtain ⟨x, hx, hBx⟩ := hfeas
    have hsum1 : ∑ i, x i ≤ 1 := by simpa [B, d, mulVec, dotProduct] using hBx (Sum.inr (Sum.inl ()))
    have hsum2 : -∑ i, x i ≤ -1 := by
      simpa [B, d, mulVec, dotProduct, Finset.sum_neg_distrib] using hBx (Sum.inr (Sum.inr ()))
    have hxs : x ∈ stdSimplex ℝ (Fin m) := ⟨hx, by linarith⟩
    refine ⟨x, hxs, (le_beta_iff M hn x v).mpr fun j => ?_⟩
    have := hBx (Sum.inl j)
    simp [B, d, mulVec, dotProduct, transpose_apply, Finset.sum_neg_distrib, mul_comm] at this ⊢
    linarith
  · exfalso
    rw [farkas_le_gen] at hfeas
    push_neg at hfeas
    obtain ⟨w, hw0, hBw, hwd⟩ := hfeas
    set z : Fin n → ℝ := fun j => w (Sum.inl j)
    set s : ℝ := w (Sum.inr (Sum.inl ()))
    set r : ℝ := w (Sum.inr (Sum.inr ()))
    have hz0 : ∀ j, 0 ≤ z j := fun j => hw0 _
    have hBt : ∀ i, (Bᵀ *ᵥ w) i = -(M *ᵥ z) i + s - r := by
      intro i
      simp only [mulVec, dotProduct, transpose_apply, Fintype.sum_sum_type]
      simp [B, z, s, r, Finset.sum_neg_distrib]
      ring
    have hwd' : w ⬝ᵥ d = -(v * ∑ j, z j) + s - r := by
      simp only [d, dotProduct, Fintype.sum_sum_type, z, s, r, Sum.elim_inl, Sum.elim_inr,
        Finset.univ_unique, Finset.sum_singleton, PUnit.default_eq_unit, Finset.mul_sum]
      simp only [mul_neg, Finset.sum_neg_distrib, mul_one]
      rw [Finset.sum_congr rfl fun j _ => mul_comm (w (Sum.inl j)) v]
      ring
    have hMz : ∀ i, (M *ᵥ z) i ≤ s - r := by
      intro i
      have := hBw i
      rw [hBt] at this; simp only [Pi.zero_apply] at this; linarith
    have hval : s - r < v * ∑ j, z j := by
      rw [hwd'] at hwd; linarith
    rcases (Finset.sum_nonneg fun j _ => hz0 j : (0 : ℝ) ≤ ∑ j, z j).lt_or_eq with hS | hS
    · set y : Fin n → ℝ := (∑ j, z j)⁻¹ • z
      have hy : y ∈ stdSimplex ℝ (Fin n) := by
        refine ⟨fun j => ?_, ?_⟩
        · simp only [y, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.mpr hS.le) (hz0 j)
        · simp only [y, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; exact inv_mul_cancel₀ hS.ne'
      have hαy : alpha M y ≤ (s - r) / ∑ j, z j := by
        rw [alpha_le_iff M hm]
        intro i
        simp only [y, mulVec_smul, Pi.smul_apply, smul_eq_mul]
        rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left (hMz i) (inv_nonneg.mpr hS.le)
      have hlt : (s - r) / ∑ j, z j < v := by rw [div_lt_iff₀ hS]; linarith
      have := hmin y hy
      linarith
    · have hz : ∀ j, z j = 0 := fun j =>
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hz0 j).mp hS.symm j (Finset.mem_univ j)
      have h0 := hMz ⟨0, hm⟩
      have : (M *ᵥ z) ⟨0, hm⟩ = 0 := by simp [mulVec, dotProduct, hz]
      rw [← hS] at hval
      simp at hval
      linarith

lemma exists_min_alpha (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ yt ∈ stdSimplex ℝ (Fin n), ∀ y ∈ stdSimplex ℝ (Fin n), alpha M yt ≤ alpha M y := by
  obtain ⟨yt, hyt, hmin⟩ := (isCompact_stdSimplex ℝ (Fin n)).exists_isMinOn
    ⟨_, single_mem_stdSimplex ℝ (⟨0, hn⟩ : Fin n)⟩ (continuous_alpha M hm).continuousOn
  exact ⟨yt, hyt, fun y hy => hmin hy⟩

end

section
open Finset
open Matrix MatousekLP.ZeroSum

open Matrix MatousekLP.ZeroSum in
theorem solution {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (M : Matrix (Fin m) (Fin n) ℝ) :
    (∃ xt : Fin m → ℝ, IsWorstCaseOptimalAlice M xt) ∧
    (∃ yt : Fin n → ℝ, IsWorstCaseOptimalBob M yt) ∧
    (∀ (xt : Fin m → ℝ) (yt : Fin n → ℝ), IsWorstCaseOptimalAlice M xt →
      IsWorstCaseOptimalBob M yt → IsMixedNash M xt yt) ∧
    ∃ v : ℝ, ∀ (xt : Fin m → ℝ) (yt : Fin n → ℝ), IsWorstCaseOptimalAlice M xt →
      IsWorstCaseOptimalBob M yt →
        beta M xt = v ∧ payoff M xt yt = v ∧ alpha M yt = v := by
  obtain ⟨y₁, hy₁, hmin⟩ := exists_min_alpha M hm hn
  obtain ⟨x₁, hx₁, hge⟩ := exists_beta_ge M hm hn y₁ hmin
  have hweak : ∀ x ∈ stdSimplex ℝ (Fin m), ∀ y ∈ stdSimplex ℝ (Fin n), beta M x ≤ alpha M y :=
    fun x hx y hy => (beta_le M x hy).trans (le_alpha M y hx)
  set v := alpha M y₁
  have hx₁v : beta M x₁ = v := le_antisymm (hweak x₁ hx₁ y₁ hy₁) hge
  have hAlice : IsWorstCaseOptimalAlice M x₁ :=
    ⟨hx₁, fun x hx => (hweak x hx y₁ hy₁).trans hx₁v.ge⟩
  have hBob : IsWorstCaseOptimalBob M y₁ := ⟨hy₁, hmin⟩
  -- every worst-case optimal pair attains the value v
  have hvals : ∀ (xt : Fin m → ℝ) (yt : Fin n → ℝ), IsWorstCaseOptimalAlice M xt →
      IsWorstCaseOptimalBob M yt → beta M xt = v ∧ alpha M yt = v := by
    rintro xt yt ⟨hxt, hxopt⟩ ⟨hyt, hyopt⟩
    refine ⟨le_antisymm (hweak xt hxt y₁ hy₁) (hx₁v ▸ hxopt x₁ hx₁), ?_⟩
    exact le_antisymm ((hyopt y₁ hy₁).trans le_rfl) (by
      have := hweak x₁ hx₁ yt hyt; rw [hx₁v] at this; exact this)
  refine ⟨⟨x₁, hAlice⟩, ⟨y₁, hBob⟩, fun xt yt hA hB => ?_, v, fun xt yt hA hB => ?_⟩
  · obtain ⟨hb, ha⟩ := hvals xt yt hA hB
    have hxt := hA.1; have hyt := hB.1
    refine ⟨⟨hxt, fun x hx => ?_⟩, ⟨hyt, fun y hy => ?_⟩⟩
    · calc payoff M x yt ≤ alpha M yt := le_alpha M yt hx
        _ = beta M xt := ha.trans hb.symm
        _ ≤ payoff M xt yt := beta_le M xt hyt
    · calc payoff M xt yt ≤ alpha M yt := le_alpha M yt hxt
        _ = beta M xt := ha.trans hb.symm
        _ ≤ payoff M xt y := beta_le M xt hy
  · obtain ⟨hb, ha⟩ := hvals xt yt hA hB
    have h1 := beta_le M xt hB.1; have h2 := le_alpha M yt hA.1
    exact ⟨hb, le_antisymm (ha ▸ h2) (hb ▸ h1), ha⟩

end
