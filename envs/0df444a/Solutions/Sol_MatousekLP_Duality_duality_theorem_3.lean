-- Prove2me | solution 3 for MatousekLP.Duality.duality_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T05:56:09.194793+00:00
-- url     : https://prove2.me/submissions/55c73fe0-a523-4d4d-99ca-127c73645d81

import Mathlib
import Definitions.Def_MatousekLP_Duality_Cones
import Definitions.Def_MatousekLP_Duality_PrimalDual
import Theorems.Thm_MatousekLP_Duality_farkas_geometric

-- carved verbatim out of submission 4b8ca9b2-939a-4829-93de-34bd2188af3f, lines 566-611

section
open Finset
open Matrix MatousekLP.Duality
variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)

def blockM : Matrix ((Fin m ⊕ Fin n) ⊕ Unit) (Fin n ⊕ Fin m) ℝ := fun r s =>
  match r, s with
  | .inl (.inl i), .inl j => A i j
  | .inl (.inl _), .inr _ => 0
  | .inl (.inr _), .inl _ => 0
  | .inl (.inr j), .inr i => -A i j
  | .inr _, .inl j => -c j
  | .inr _, .inr i => b i

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
open Matrix MatousekLP.Duality
variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)

lemma dual_unbounded (hD : ∃ y, IsDualFeasible A c y) (hP : ¬ ∃ x, IsPrimalFeasible A b x) :
    DualUnbounded A b c := by
  have hF := farkas_le_gen A b
  have hinf : ¬ ∃ x : Fin n → ℝ, 0 ≤ x ∧ A *ᵥ x ≤ b := by
    rintro ⟨x, hx, hAx⟩; exact hP ⟨x, hAx, hx⟩
  rw [hF] at hinf
  push_neg at hinf
  obtain ⟨v, hv0, hAv, hvb⟩ := hinf
  obtain ⟨y₀, hAy₀, hy₀⟩ := hD
  intro M
  have hbv : b ⬝ᵥ v < 0 := by rw [dotProduct_comm]; exact hvb
  set t : ℝ := max 0 ((b ⬝ᵥ y₀ - M) / (-(b ⬝ᵥ v)) + 1)
  have ht : 0 ≤ t := le_max_left _ _
  refine ⟨y₀ + t • v, ⟨fun j => ?_, fun i => ?_⟩, ?_⟩
  · have h1 := hAy₀ j; have h2 := hAv j
    simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at *
    nlinarith
  · have := hy₀ i; have := hv0 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at *
    positivity
  · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    have h1 : (b ⬝ᵥ y₀ - M) / (-(b ⬝ᵥ v)) + 1 ≤ t := le_max_right _ _
    have hpos : 0 < -(b ⬝ᵥ v) := by linarith
    have h2 : b ⬝ᵥ y₀ - M < t * (-(b ⬝ᵥ v)) := by
      rw [← div_lt_iff₀ hpos]; linarith
    linarith

lemma primal_unbounded (hP : ∃ x, IsPrimalFeasible A b x) (hD : ¬ ∃ y, IsDualFeasible A c y) :
    PrimalUnbounded A b c := by
  -- Farkas on the dual system -Aᵀ y ≤ -c, y ≥ 0
  have hF := farkas_le_gen (-Aᵀ) (-c)
  have hinf : ¬ ∃ y : Fin m → ℝ, 0 ≤ y ∧ (-Aᵀ) *ᵥ y ≤ -c := by
    rintro ⟨y, hy, hAy⟩
    refine hD ⟨y, fun j => ?_, hy⟩
    have := hAy j; simp [neg_mulVec] at this; linarith
  rw [hF] at hinf
  push_neg at hinf
  obtain ⟨u, hu0, hAu, hcu⟩ := hinf
  have hAu' : A *ᵥ u ≤ 0 := by
    intro i; have := hAu i; simp [transpose_neg, transpose_transpose, neg_mulVec] at this
    simp only [Pi.zero_apply]; linarith
  have hcu' : 0 < c ⬝ᵥ u := by
    have : u ⬝ᵥ -c = -(c ⬝ᵥ u) := by rw [dotProduct_neg, dotProduct_comm]
    linarith
  obtain ⟨x₀, hAx₀, hx₀⟩ := hP
  intro M
  set t : ℝ := max 0 ((M - c ⬝ᵥ x₀) / (c ⬝ᵥ u) + 1)
  have ht : 0 ≤ t := le_max_left _ _
  refine ⟨x₀ + t • u, ⟨fun i => ?_, fun j => ?_⟩, ?_⟩
  · have h1 := hAx₀ i; have h2 := hAu' i
    simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at *
    nlinarith
  · have := hx₀ j; have := hu0 j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at *
    positivity
  · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    have h1 : (M - c ⬝ᵥ x₀) / (c ⬝ᵥ u) + 1 ≤ t := le_max_right _ _
    have h2 : M - c ⬝ᵥ x₀ < t * (c ⬝ᵥ u) := by
      rw [← div_lt_iff₀ hcu']; linarith
    linarith

lemma weak {x : Fin n → ℝ} {y : Fin m → ℝ} (hx : IsPrimalFeasible A b x)
    (hy : IsDualFeasible A c y) : c ⬝ᵥ x ≤ b ⬝ᵥ y := by
  obtain ⟨hAx, hx0⟩ := hx; obtain ⟨hAy, hy0⟩ := hy
  calc c ⬝ᵥ x ≤ (Aᵀ *ᵥ y) ⬝ᵥ x := dotProduct_le_dotProduct_of_nonneg_right hAy hx0
    _ = y ⬝ᵥ (A *ᵥ x) := by rw [mulVec_transpose, ← dotProduct_mulVec]
    _ ≤ y ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hAx hy0
    _ = b ⬝ᵥ y := dotProduct_comm _ _

lemma strong (hP : ∃ x, IsPrimalFeasible A b x) (hD : ∃ y, IsDualFeasible A c y) :
    ∃ x y, IsPrimalFeasible A b x ∧ IsDualFeasible A c y ∧ b ⬝ᵥ y ≤ c ⬝ᵥ x := by
  classical
  set rhs : (Fin m ⊕ Fin n) ⊕ Unit → ℝ := Sum.elim (Sum.elim b (-c)) (fun _ => 0)
  by_cases hfeas : ∃ z : Fin n ⊕ Fin m → ℝ, 0 ≤ z ∧ blockM A b c *ᵥ z ≤ rhs
  · obtain ⟨z, hz, hMz⟩ := hfeas
    set x : Fin n → ℝ := fun j => z (Sum.inl j)
    set y : Fin m → ℝ := fun i => z (Sum.inr i)
    have hrow : ∀ r, (blockM A b c *ᵥ z) r = match r with
        | .inl (.inl i) => (A *ᵥ x) i
        | .inl (.inr j) => -(Aᵀ *ᵥ y) j
        | .inr _ => -(c ⬝ᵥ x) + b ⬝ᵥ y := by
      intro r
      rcases r with (i | j) | u
      · simp [mulVec, dotProduct, blockM, Fintype.sum_sum_type, x]
      · simp [mulVec, dotProduct, blockM, Fintype.sum_sum_type, y, transpose_apply, Finset.sum_neg_distrib]
      · simp [mulVec, dotProduct, blockM, Fintype.sum_sum_type, x, y, Finset.sum_neg_distrib, mul_comm]
    refine ⟨x, y, ⟨fun i => ?_, fun j => hz _⟩, ⟨fun j => ?_, fun i => hz _⟩, ?_⟩
    · have := hMz (Sum.inl (Sum.inl i)); rw [hrow] at this; simpa [rhs] using this
    · have := hMz (Sum.inl (Sum.inr j)); rw [hrow] at this; simp [rhs] at this; linarith
    · have := hMz (Sum.inr ()); rw [hrow] at this; simp [rhs] at this; linarith
  · exfalso
    rw [farkas_le_gen] at hfeas
    push_neg at hfeas
    obtain ⟨w, hw0, hMw, hwr⟩ := hfeas
    set u : Fin m → ℝ := fun i => w (Sum.inl (Sum.inl i))
    set v : Fin n → ℝ := fun j => w (Sum.inl (Sum.inr j))
    set s : ℝ := w (Sum.inr ())
    have hu0 : 0 ≤ u := fun i => hw0 _
    have hv0 : 0 ≤ v := fun j => hw0 _
    have hs0 : 0 ≤ s := hw0 _
    have hcolx : ∀ j, s * c j ≤ (Aᵀ *ᵥ u) j := by
      intro j
      have := hMw (Sum.inl j)
      simp [mulVec, dotProduct, blockM, transpose_apply, Fintype.sum_sum_type, u, s] at this
      simp [mulVec, dotProduct, transpose_apply, u]
      linarith
    have hcoly : ∀ i, (A *ᵥ v) i ≤ s * b i := by
      intro i
      have := hMw (Sum.inr i)
      simp [mulVec, dotProduct, blockM, transpose_apply, Fintype.sum_sum_type, v, s,
        Finset.sum_neg_distrib] at this
      simp [mulVec, dotProduct, v]
      linarith
    have hval : u ⬝ᵥ b - v ⬝ᵥ c < 0 := by
      simp [dotProduct, rhs, Fintype.sum_sum_type, u, v] at hwr
      simp [dotProduct, Finset.sum_neg_distrib] at hwr ⊢
      linarith
    obtain ⟨x₀, hx₀⟩ := hP
    obtain ⟨y₀, hy₀⟩ := hD
    rcases hs0.lt_or_eq with hs | hs
    · -- scale: v/s is primal feasible, u/s is dual feasible
      have hxs : IsPrimalFeasible A b (s⁻¹ • v) := by
        refine ⟨fun i => ?_, fun j => ?_⟩
        · rw [mulVec_smul]; simp only [Pi.smul_apply, smul_eq_mul]
          rw [inv_mul_le_iff₀ hs]; exact hcoly i
        · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          exact mul_nonneg (inv_nonneg.mpr hs.le) (hv0 j)
      have hys : IsDualFeasible A c (s⁻¹ • u) := by
        refine ⟨fun j => ?_, fun i => ?_⟩
        · rw [mulVec_smul]; simp only [Pi.smul_apply, smul_eq_mul]
          rw [le_inv_mul_iff₀ hs]; exact hcolx j
        · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          exact mul_nonneg (inv_nonneg.mpr hs.le) (hu0 i)
      have := weak A b c hxs hys
      rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
      have h2 := mul_le_mul_of_nonneg_left this hs.le
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul, one_mul] at h2
      rw [dotProduct_comm u b, dotProduct_comm v c] at hval
      linarith
    · -- s = 0: rays in both problems contradict weak duality for large t
      have hAu : ∀ j, 0 ≤ (Aᵀ *ᵥ u) j := fun j => by have := hcolx j; rw [← hs] at this; simpa using this
      have hAv : ∀ i, (A *ᵥ v) i ≤ 0 := fun i => by have := hcoly i; rw [← hs] at this; simpa using this
      have hgap : 0 < c ⬝ᵥ v - b ⬝ᵥ u := by
        rw [dotProduct_comm u b, dotProduct_comm v c] at hval; linarith
      set t : ℝ := (b ⬝ᵥ y₀ - c ⬝ᵥ x₀) / (c ⬝ᵥ v - b ⬝ᵥ u) + 1
      have ht : 0 ≤ t := by
        have := weak A b c hx₀ hy₀
        have : 0 ≤ (b ⬝ᵥ y₀ - c ⬝ᵥ x₀) / (c ⬝ᵥ v - b ⬝ᵥ u) := div_nonneg (by linarith) hgap.le
        linarith
      have hxt : IsPrimalFeasible A b (x₀ + t • v) := by
        refine ⟨fun i => ?_, fun j => ?_⟩
        · have h1 := hx₀.1 i; have h2 := hAv i
          simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
          nlinarith
        · have := hx₀.2 j; have := hv0 j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at *
          positivity
      have hyt : IsDualFeasible A c (y₀ + t • u) := by
        refine ⟨fun j => ?_, fun i => ?_⟩
        · have h1 := hy₀.1 j; have h2 := hAu j
          simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
          nlinarith
        · have := hy₀.2 i; have := hu0 i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at *
          positivity
      have := weak A b c hxt hyt
      rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
        smul_eq_mul] at this
      have hmul : (b ⬝ᵥ y₀ - c ⬝ᵥ x₀) < t * (c ⬝ᵥ v - b ⬝ᵥ u) := by
        rw [← div_lt_iff₀ hgap]; linarith
      nlinarith

end

section
open Finset

open Matrix MatousekLP.Duality in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) :
    ∃! k : Fin 4, DualityCase A b c k := by
  have unbP : PrimalUnbounded A b c → ∃ x, IsPrimalFeasible A b x := fun h =>
    let ⟨x, hx, _⟩ := h 0; ⟨x, hx⟩
  have unbD : DualUnbounded A b c → ∃ y, IsDualFeasible A c y := fun h =>
    let ⟨y, hy, _⟩ := h 0; ⟨y, hy⟩
  by_cases hP : ∃ x, IsPrimalFeasible A b x <;> by_cases hD : ∃ y, IsDualFeasible A c y
  · -- case 3
    obtain ⟨xs, ys, hxs, hys, hge⟩ := strong A b c hP hD
    have heq : c ⬝ᵥ xs = b ⬝ᵥ ys := le_antisymm (weak A b c hxs hys) hge
    have hxopt : IsPrimalOptimal A b c xs :=
      ⟨hxs, fun x hx => (weak A b c hx hys).trans heq.ge⟩
    have hyopt : IsDualOptimal A b c ys :=
      ⟨hys, fun y hy => heq.symm.le.trans (weak A b c hxs hy)⟩
    refine ⟨3, ⟨hP, hD, ⟨xs, hxopt⟩, ⟨ys, hyopt⟩, fun x y hx hy => ?_⟩, fun k hk => ?_⟩
    · have h1 : c ⬝ᵥ x = c ⬝ᵥ xs := le_antisymm (hxopt.2 x hx.1) (hx.2 xs hxs)
      have h2 : b ⬝ᵥ y = b ⬝ᵥ ys := le_antisymm (hy.2 ys hys) (hyopt.2 y hy.1)
      rw [h1, h2, heq]
    · fin_cases k
      · exact absurd hP hk.1
      · exact absurd hD hk.2
      · exact absurd hP hk.1
      · rfl
  · -- case 1
    refine ⟨1, ⟨primal_unbounded A b c hP hD, hD⟩, fun k hk => ?_⟩
    fin_cases k
    · exact absurd hP hk.1
    · rfl
    · exact absurd hP hk.1
    · exact absurd hk.2.1 hD
  · -- case 2
    refine ⟨2, ⟨hP, dual_unbounded A b c hD hP⟩, fun k hk => ?_⟩
    fin_cases k
    · exact absurd hD hk.2
    · exact absurd (unbP hk.1) hP
    · rfl
    · exact absurd hk.1 hP
  · -- case 0
    refine ⟨0, ⟨hP, hD⟩, fun k hk => ?_⟩
    fin_cases k
    · rfl
    · exact absurd (unbP hk.1) hP
    · exact absurd (unbD hk.2) hD
    · exact absurd hk.1 hP

end
