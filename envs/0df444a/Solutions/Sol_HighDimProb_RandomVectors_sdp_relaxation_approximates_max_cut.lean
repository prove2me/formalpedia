-- Prove2me | solution 1 for HighDimProb.RandomVectors.sdp_relaxation_approximates_max_cut
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T21:27:10.64238+00:00
-- url     : https://prove2.me/submissions/8ee06b0b-fc6f-4c09-b259-97a33b18e9fd

import Mathlib
import Definitions.Def_HighDimProb_RandomVectors_IntegerCutValue
import Definitions.Def_HighDimProb_RandomVectors_SdpRelaxationValue

set_option autoImplicit false

namespace P2MAbc21244

/-- The sign map `true ↦ 1`, `false ↦ -1`. -/
noncomputable def sg (b : Bool) : ℝ := if b then 1 else -1

/-- The quadratic form `wᵀ A w`. -/
noncomputable def Q {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * w i * w j

/-- The bilinear form `uᵀ A w`. -/
noncomputable def B {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u w : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * u i * w j

lemma sum_bool_pi_succ {m : ℕ} (f : (Fin (m+1) → Bool) → ℝ) :
    ∑ ε, f ε = ∑ ε : Fin m → Bool, (f (Fin.cons true ε) + f (Fin.cons false ε)) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    ← Finset.sum_add_distrib]
  rfl

lemma Q_par {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n → ℝ) :
    Q A (fun j => a j + b j) + Q A (fun j => -a j + b j) = 2 * Q A a + 2 * Q A b := by
  simp only [Q, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma quad_moment {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ (m : ℕ) (v : Fin m → Fin n → ℝ),
    ∑ ε : Fin m → Bool, Q A (fun j => ∑ k, sg (ε k) * v k j) = 2 ^ m * ∑ k, Q A (v k) := by
  intro m
  induction m with
  | zero => intro v; simp [Q]
  | succ m ih =>
    intro v
    rw [sum_bool_pi_succ]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have h : ∀ ε : Fin m → Bool,
        Q A (fun j => sg true * v 0 j + ∑ k : Fin m, sg (ε k) * v k.succ j) +
          Q A (fun j => sg false * v 0 j + ∑ k : Fin m, sg (ε k) * v k.succ j) =
        2 * Q A (v 0) + 2 * Q A (fun j => ∑ k : Fin m, sg (ε k) * v k.succ j) := by
      intro ε
      rw [show sg true = 1 by simp [sg], show sg false = -1 by simp [sg]]
      simp only [one_mul, neg_one_mul]
      exact Q_par A (v 0) (fun j => ∑ k : Fin m, sg (ε k) * v k.succ j)
    rw [Finset.sum_congr rfl (fun ε _ => h ε), Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ih (fun k => v k.succ)]
    simp [Finset.sum_const, Finset.card_univ]
    ring

lemma sc_moment2 : ∀ (m : ℕ) (c : Fin m → ℝ),
    ∑ ε : Fin m → Bool, (∑ k, sg (ε k) * c k) ^ 2 = 2 ^ m * ∑ k, c k ^ 2 := by
  intro m
  induction m with
  | zero => intro c; simp
  | succ m ih =>
    intro c
    rw [sum_bool_pi_succ]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have h : ∀ ε : Fin m → Bool,
        (sg true * c 0 + ∑ k : Fin m, sg (ε k) * c k.succ) ^ 2 +
          (sg false * c 0 + ∑ k : Fin m, sg (ε k) * c k.succ) ^ 2 =
        2 * (∑ k : Fin m, sg (ε k) * c k.succ) ^ 2 + 2 * c 0 ^ 2 := by
      intro ε; simp only [sg]; simp; ring
    rw [Finset.sum_congr rfl (fun ε _ => h ε), Finset.sum_add_distrib, ← Finset.mul_sum,
      ih (fun k => c k.succ)]
    simp [Finset.sum_const, Finset.card_univ]
    ring

lemma sc_moment4 : ∀ (m : ℕ) (c : Fin m → ℝ),
    ∑ ε : Fin m → Bool, (∑ k, sg (ε k) * c k) ^ 4 ≤ 3 * 2 ^ m * (∑ k, c k ^ 2) ^ 2 := by
  intro m
  induction m with
  | zero => intro c; simp
  | succ m ih =>
    intro c
    rw [sum_bool_pi_succ]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have h : ∀ ε : Fin m → Bool,
        (sg true * c 0 + ∑ k : Fin m, sg (ε k) * c k.succ) ^ 4 +
          (sg false * c 0 + ∑ k : Fin m, sg (ε k) * c k.succ) ^ 4 =
        2 * (∑ k : Fin m, sg (ε k) * c k.succ) ^ 4
          + 12 * c 0 ^ 2 * (∑ k : Fin m, sg (ε k) * c k.succ) ^ 2 + 2 * c 0 ^ 4 := by
      intro ε; simp only [sg]; simp; ring
    rw [Finset.sum_congr rfl (fun ε _ => h ε), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, sc_moment2 m (fun k => c k.succ)]
    have h4 := ih (fun k => c k.succ)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    set M := ∑ ε : Fin m → Bool, (∑ k : Fin m, sg (ε k) * c k.succ) ^ 4
    set s := ∑ k : Fin m, c k.succ ^ 2
    have hp : (0:ℝ) < 2 ^ m := by positivity
    have : (0:ℝ) ≤ 2 ^ m * (c 0 ^ 2) ^ 2 := by positivity
    have h2m : (2:ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [h2m]
    nlinarith [this, h4]

lemma khin (m : ℕ) (a c : Fin m → ℝ) (ha : ∑ k, a k ^ 2 ≤ 1) :
    9 * 2 ^ m * ∑ k, a k * c k ≤ 16 * ∑ ε : Fin m → Bool, |∑ k, sg (ε k) * c k| := by
  set σ := Real.sqrt (∑ k, c k ^ 2) with hσdef
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ ^ 2 = ∑ k, c k ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hac : ∑ k, a k * c k ≤ σ := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a c
    have hc0 : 0 ≤ ∑ k, c k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    have : (∑ k, a k * c k) ^ 2 ≤ ∑ k, c k ^ 2 := by nlinarith
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt this)
  have hpt : ∀ ε : Fin m → Bool,
      12 * σ ^ 2 * (∑ k, sg (ε k) * c k) ^ 2 - (∑ k, sg (ε k) * c k) ^ 4
        ≤ 16 * σ ^ 3 * |∑ k, sg (ε k) * c k| := by
    intro ε
    set s := ∑ k, sg (ε k) * c k
    set t := |s|
    have ht : 0 ≤ t := abs_nonneg _
    have h2 : s ^ 2 = t ^ 2 := (sq_abs s).symm
    have h4 : s ^ 4 = t ^ 4 := by rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, h2]
    rw [h2, h4]
    have := mul_nonneg (mul_nonneg ht (sq_nonneg (t - 2 * σ))) (add_nonneg ht (by positivity : (0:ℝ) ≤ 4 * σ))
    nlinarith [this]
  have hsum := Finset.sum_le_sum fun ε (_ : ε ∈ Finset.univ) => hpt ε
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sc_moment2] at hsum
  have h4 := sc_moment4 m c
  rw [← hσ2] at hsum h4
  have hp : (0:ℝ) < 2 ^ m := by positivity
  have hS0 : 0 ≤ ∑ ε : Fin m → Bool, |∑ k, sg (ε k) * c k| :=
    Finset.sum_nonneg fun ε _ => abs_nonneg _
  have key : 9 * 2 ^ m * σ ≤ 16 * ∑ ε : Fin m → Bool, |∑ k, sg (ε k) * c k| := by
    rcases hσ0.eq_or_lt with h | h
    · rw [← h]; nlinarith
    · have h3 : 0 < σ ^ 3 := by positivity
      have : σ ^ 3 * (9 * 2 ^ m * σ) ≤ σ ^ 3 * (16 * ∑ ε : Fin m → Bool, |∑ k, sg (ε k) * c k|) := by
        nlinarith
      exact le_of_mul_le_mul_left this h3
  nlinarith

lemma main_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (X : Fin n → EuclideanSpace ℝ (Fin n)) (hX : ∀ i, ‖X i‖ = 1) :
    ∑ i, ∑ j, A i j * inner ℝ (X i) (X j) ≤ 4 * HighDimProb.RandomVectors.integerCutValue A := by
  set I := HighDimProb.RandomVectors.integerCutValue A
  have hsym : ∀ i j, A i j = A j i := by
    intro i j
    have := hA.1.apply j i
    simpa using this
  have hQ : ∀ w, 0 ≤ Q A w := by
    intro w
    have := hA.dotProduct_mulVec_nonneg w
    simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] at this
    simp only [Q]
    refine le_of_le_of_eq this ?_
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hI : ∀ b : Fin n → Bool, Q A (fun i => sg (b i)) ≤ I := by
    intro b
    exact le_ciSup (f := fun x : Fin n → Bool => ∑ i, ∑ j, A i j * (if x i then (1 : ℝ) else -1) *
      (if x j then (1 : ℝ) else -1)) (Set.finite_range _).bddAbove b
  have hI0 : 0 ≤ I := by
    have := hI (fun _ => true)
    exact le_trans (hQ _) this
  have hcross : ∀ u w, 4 * B A u w ≤ 4 * Q A u + Q A w := by
    intro u w
    have e1 : ∑ i, ∑ j, A i j * w i * u j = B A u w := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hsym]; ring
    have e2 : Q A (fun i => 2 * u i - w i) =
        4 * Q A u - 2 * B A u w - 2 * (∑ i, ∑ j, A i j * w i * u j) + Q A w := by
      simp only [Q, B, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have := hQ (fun i => 2 * u i - w i)
    rw [e2, e1] at this
    linarith
  have hinner : ∀ i j, inner ℝ (X i) (X j) = ∑ k, X i k * X j k := by
    intro i j
    simp [PiLp.inner_apply, mul_comm]
  -- coefficients
  set c : Fin n → Fin n → ℝ := fun i k => ∑ j, A i j * X j k with hc
  have hS : ∑ i, ∑ j, A i j * inner ℝ (X i) (X j) = ∑ i, ∑ k, X i k * c i k := by
    simp only [hinner, hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hSq : ∑ i, ∑ j, A i j * inner ℝ (X i) (X j) = ∑ k, Q A (fun j => X j k) := by
    simp only [hinner, Q, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  set S := ∑ i, ∑ j, A i j * inner ℝ (X i) (X j)
  -- Khintchine for each row
  have hrow : ∀ i, 9 * 2 ^ n * ∑ k, X i k * c i k ≤
      16 * ∑ ε : Fin n → Bool, |∑ k, sg (ε k) * c i k| := by
    intro i
    apply khin
    rw [← EuclideanSpace.real_norm_sq_eq, hX i]; norm_num
  have h1 : 9 * 2 ^ n * S ≤ 16 * ∑ i, ∑ ε : Fin n → Bool, |∑ k, sg (ε k) * c i k| := by
    rw [hS, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hrow i
  -- per sign vector
  set z : (Fin n → Bool) → Fin n → ℝ := fun ε j => ∑ k, sg (ε k) * X j k with hz
  have hT : ∀ ε i, ∑ k, sg (ε k) * c i k = ∑ j, A i j * z ε j := by
    intro ε i
    simp only [hc, hz, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hper : ∀ ε : Fin n → Bool, 4 * ∑ i, |∑ k, sg (ε k) * c i k| ≤ 4 * I + Q A (z ε) := by
    intro ε
    set b : Fin n → Bool := fun i => decide (0 ≤ ∑ j, A i j * z ε j)
    have habs : ∑ i, |∑ k, sg (ε k) * c i k| = B A (fun i => sg (b i)) (z ε) := by
      simp only [B]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hT]
      have : ∑ j, A i j * sg (b i) * z ε j = sg (b i) * ∑ j, A i j * z ε j := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      rw [this]
      by_cases h : 0 ≤ ∑ j, A i j * z ε j
      · simp [b, sg, h, abs_of_nonneg h]
      · simp [b, sg, h, abs_of_neg (lt_of_not_ge h)]
    rw [habs]
    have := hcross (fun i => sg (b i)) (z ε)
    have := hI b
    linarith
  have h2 : 4 * ∑ i, ∑ ε : Fin n → Bool, |∑ k, sg (ε k) * c i k| ≤ 2 ^ n * (4 * I + S) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun ε _ => hper ε) ?_
    rw [Finset.sum_add_distrib]
    have hm := quad_moment A n (fun k j => X j k)
    simp only [hz]
    rw [hm, ← hSq]
    simp [Finset.sum_const, Finset.card_univ]
    ring_nf
    rfl
  have hp : (0:ℝ) < 2 ^ n := by positivity
  nlinarith

end P2MAbc21244

open HighDimProb.RandomVectors in
theorem solution :
    ∃ K : ℝ, 0 < K ∧ K ≤ 288 ∧
      ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ), A.PosSemidef →
        integerCutValue A ≤ sdpRelaxationValue A ∧
        sdpRelaxationValue A ≤ 2 * K * integerCutValue A := by
  refine ⟨2, by norm_num, by norm_num, ?_⟩
  intro n A hA
  have hub : ∀ v ∈ {v : ℝ | ∃ X : Fin n → EuclideanSpace ℝ (Fin n), (∀ i, ‖X i‖ = 1) ∧
      v = ∑ i, ∑ j, A i j * inner ℝ (X i) (X j)}, v ≤ 4 * HighDimProb.RandomVectors.integerCutValue A := by
    rintro v ⟨X, hX, rfl⟩
    exact P2MAbc21244.main_bound A hA X hX
  have hI0 : 0 ≤ HighDimProb.RandomVectors.integerCutValue A := by
    have h1 := hA.dotProduct_mulVec_nonneg (fun _ => (1:ℝ))
    refine le_trans ?_ (le_ciSup (f := fun x : Fin n → Bool => ∑ i, ∑ j, A i j *
      (if x i then (1 : ℝ) else -1) * (if x j then (1 : ℝ) else -1)) (Set.finite_range _).bddAbove
      (fun _ => true))
    simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] at h1
    simpa using h1
  constructor
  · unfold HighDimProb.RandomVectors.integerCutValue
    apply ciSup_le
    intro b
    apply le_csSup ⟨_, hub⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact ⟨fun i => i.elim0, fun i => i.elim0, by simp⟩
    · refine ⟨fun i => EuclideanSpace.single (⟨0, hn⟩ : Fin n) (P2MAbc21244.sg (b i)), ?_, ?_⟩
      · intro i; cases h : b i <;> simp [P2MAbc21244.sg, h]
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp [EuclideanSpace.inner_single_left, P2MAbc21244.sg]
  · unfold HighDimProb.RandomVectors.sdpRelaxationValue
    refine Real.sSup_le hub ?_ |>.trans (le_of_eq (by ring))
    linarith
