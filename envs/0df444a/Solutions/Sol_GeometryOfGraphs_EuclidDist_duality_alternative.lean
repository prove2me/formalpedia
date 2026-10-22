-- Prove2me | solution 1 for GeometryOfGraphs.EuclidDist.duality_alternative
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:37:36.188558+00:00
-- url     : https://prove2.me/submissions/506f5bd5-7abd-4b48-a001-b4d3c430ad8e

import Mathlib
import Definitions.Def_GeometryOfGraphs_EuclidDist_EuclideanDistortion



namespace GeometryOfGraphs.EuclidDist

open Matrix

lemma g69_psd_iff {X : Type*} [Fintype X] (B : Matrix X X ℝ) :
    B.PosSemidef ↔ (∀ i j, B i j = B j i) ∧ ∀ x : X → ℝ, 0 ≤ ∑ i, ∑ j, x i * B i j * x j := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun x => ?_⟩
    · have := h1.apply i j
      simpa using this.symm
    · have := h2 x
      simpa [dotProduct, mulVec, Finset.mul_sum, mul_assoc] using this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun x => ?_⟩
    · ext i j
      simp [conjTranspose_apply, h1 i j]
    · have := h2 x
      simpa [dotProduct, mulVec, Finset.mul_sum, mul_assoc] using this

lemma g69_Q_identity {X : Type*} [Fintype X] [DecidableEq X] (Y : X → X → ℝ)
    (hsym : ∀ i j, Y i j = Y j i) (A : Matrix X X ℝ) :
    ∑ i, ∑ j, (Matrix.of fun i j => (if i = j then 2 * ∑ k, Y i k else 0) - 2 * Y i j) i j * A i j
      = ∑ i, ∑ j, Y i j * (A i i + A j j - 2 * A i j) := by
  have h1 : ∑ i, ∑ j, Y i j * (A i i + A j j - 2 * A i j)
      = ∑ i, (∑ j, Y i j) * A i i + ∑ i, ∑ j, Y i j * A j j - 2 * ∑ i, ∑ j, Y i j * A i j := by
    have : ∀ i j, Y i j * (A i i + A j j - 2 * A i j)
        = Y i j * A i i + Y i j * A j j - 2 * (Y i j * A i j) := fun i j => by ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul]
  have h2 : ∑ i, ∑ j, Y i j * A j j = ∑ i, (∑ j, Y i j) * A i i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsym i j]
  have h3 : ∑ i, ∑ j, (Matrix.of fun i j => (if i = j then 2 * ∑ k, Y i k else 0) - 2 * Y i j) i j * A i j
      = ∑ i, 2 * (∑ k, Y i k) * A i i - 2 * ∑ i, ∑ j, Y i j * A i j := by
    have : ∀ i j, (Matrix.of fun i j => (if i = j then 2 * ∑ k, Y i k else 0) - 2 * Y i j) i j * A i j
        = (if i = j then 2 * (∑ k, Y i k) * A i i else 0) - 2 * (Y i j * A i j) := by
      intro i j
      by_cases h : i = j
      · subst h; simp; ring
      · simp [h]; ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.mul_sum]
  rw [h1, h3, h2]
  have : ∑ i, 2 * (∑ k, Y i k) * A i i = ∑ i, (∑ j, Y i j) * A i i + ∑ i, (∑ j, Y i j) * A i i := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]


lemma g69_alg {X : Type*} [Fintype X] [DecidableEq X] (d : X → X → ℝ) (c : ℝ) (Y : X → X → ℝ)
    (hsym : ∀ i j, Y i j = Y j i)
    (hC1 : ∑ i, ∑ j, Y i j * (if 0 < Y i j then c ^ 2 * d i j ^ 2 else d i j ^ 2) < 0)
    (hC2 : ∀ z : X → ℝ, ∑ i, z i = 0 → 0 ≤ ∑ i, ∑ j, Y i j * (z i - z j) ^ 2) :
    ∃ Q : Matrix X X ℝ, Q.PosSemidef ∧
        ∃ lam mu : X → X → ℝ, (∀ i j, 0 ≤ lam i j) ∧ (∀ i j, 0 ≤ mu i j) ∧
          (∀ A : Matrix X X ℝ,
            (∑ i, ∑ j, Q i j * A i j) +
              ∑ i, ∑ j, (lam i j * (c ^ 2 * d i j ^ 2 - (A i i + A j j - 2 * A i j)) +
                mu i j * ((A i i + A j j - 2 * A i j) - d i j ^ 2)) =
            ∑ i, ∑ j, (lam i j * (c ^ 2 * d i j ^ 2) - mu i j * d i j ^ 2)) ∧
          ∑ i, ∑ j, (lam i j * (c ^ 2 * d i j ^ 2) - mu i j * d i j ^ 2) < 0 := by
  set Q : Matrix X X ℝ := Matrix.of fun i j => (if i = j then 2 * ∑ k, Y i k else 0) - 2 * Y i j
    with hQ
  refine ⟨Q, ?_, fun i j => max (Y i j) 0, fun i j => max (-Y i j) 0, fun i j => le_max_right _ _,
    fun i j => le_max_right _ _, ?_, ?_⟩
  · rw [g69_psd_iff]
    refine ⟨fun i j => ?_, fun x => ?_⟩
    · simp only [hQ, Matrix.of_apply]
      rw [hsym i j]
      by_cases h : i = j
      · subst h; rfl
      · simp [h, Ne.symm h]
    · rcases isEmpty_or_nonempty X with hX | hX
      · simp
      · have hcard : (Fintype.card X : ℝ) ≠ 0 := by
          have := Fintype.card_pos (α := X)
          exact_mod_cast this.ne'
        set z : X → ℝ := fun i => x i - (∑ k, x k) / Fintype.card X with hz
        have hz0 : ∑ i, z i = 0 := by
          simp only [hz, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp
          ring
        have key := g69_Q_identity Y hsym (Matrix.of fun i j => x i * x j)
        have h4 : ∑ i, ∑ j, x i * Q i j * x j
            = ∑ i, ∑ j, Y i j * (z i - z j) ^ 2 := by
          calc ∑ i, ∑ j, x i * Q i j * x j
              = ∑ i, ∑ j, Q i j * (Matrix.of fun i j => x i * x j) i j := by
                refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
                simp only [Matrix.of_apply]; ring
            _ = ∑ i, ∑ j, Y i j * ((Matrix.of fun i j => x i * x j) i i
                  + (Matrix.of fun i j => x i * x j) j j - 2 * (Matrix.of fun i j => x i * x j) i j) :=
                key
            _ = _ := by
                refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
                simp only [Matrix.of_apply, hz]; ring
        rw [h4]
        exact hC2 z hz0
  · intro A
    have key := g69_Q_identity Y hsym A
    have hpt : ∀ i j, Y i j = max (Y i j) 0 - max (-Y i j) 0 := by
      intro i j
      rcases le_total 0 (Y i j) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    rw [← hQ] at key
    rw [key]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hpt i j]
    ring
  · refine lt_of_eq_of_lt ?_ hC1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    beta_reduce
    rcases lt_or_ge 0 (Y i j) with h | h
    · rw [if_pos h, max_eq_left h.le, max_eq_right (by linarith)]; ring
    · rw [if_neg (not_lt.mpr h), max_eq_right h, max_eq_left (by linarith)]; ring


lemma g69_quad2 {X : Type*} [Fintype X] [DecidableEq X] (B : Matrix X X ℝ) (i j : X) (s : ℝ) :
    ∑ a, ∑ b, ((if a = i then 1 else 0) + s * (if a = j then 1 else 0)) * B a b *
        ((if b = i then 1 else 0) + s * (if b = j then 1 else 0))
      = B i i + s * B i j + s * B j i + s ^ 2 * B j j := by
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  simp [mul_comm, mul_left_comm, pow_two, mul_ite]
  ring

lemma g69_entry_bound {X : Type*} [Fintype X] [DecidableEq X] (B : Matrix X X ℝ)
    (hs : ∀ i j, B i j = B j i)
    (hq : ∀ x : X → ℝ, 0 ≤ ∑ i, ∑ j, x i * B i j * x j) (i j : X) :
    2 * |B i j| ≤ B i i + B j j := by
  have h1 := hq (fun a => (if a = i then 1 else 0) + 1 * (if a = j then 1 else 0))
  have h2 := hq (fun a => (if a = i then 1 else 0) + (-1) * (if a = j then 1 else 0))
  rw [g69_quad2] at h1 h2
  rw [hs j i] at h1 h2
  rcases abs_cases (B i j) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith


def g69K {X : Type*} [Fintype X] (R : ℝ) : Set (Matrix X X ℝ) :=
  {B | (∀ i j, B i j = B j i) ∧ (∀ x : X → ℝ, 0 ≤ ∑ i, ∑ j, x i * B i j * x j) ∧
    (∀ i, ∑ j, B i j = 0) ∧ ∑ i, B i i ≤ R}

lemma g69K_convex {X : Type*} [Fintype X] (R : ℝ) : Convex ℝ (g69K (X := X) R) := by
  intro B1 h1 B2 h2 a b ha hb hab
  obtain ⟨s1, q1, c1, t1⟩ := h1
  obtain ⟨s2, q2, c2, t2⟩ := h2
  refine ⟨fun i j => ?_, fun x => ?_, fun i => ?_, ?_⟩
  · simp [s1 i j, s2 i j]
  · have : ∑ i, ∑ j, x i * (a • B1 + b • B2) i j * x j
        = a * ∑ i, ∑ j, x i * B1 i j * x j + b * ∑ i, ∑ j, x i * B2 i j * x j := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [this]; exact add_nonneg (mul_nonneg ha (q1 x)) (mul_nonneg hb (q2 x))
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, c1 i, c2 i]
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have e : a * R + b * R = R := by rw [← add_mul, hab, one_mul]
    linarith [mul_le_mul_of_nonneg_left t1 ha, mul_le_mul_of_nonneg_left t2 hb]

lemma g69K_psd {X : Type*} [Fintype X] (R : ℝ) {B : Matrix X X ℝ} (h : B ∈ g69K R) :
    B.PosSemidef := (g69_psd_iff B).2 ⟨h.1, h.2.1⟩

lemma g69K_compact {X : Type*} [Fintype X] [DecidableEq X] (R : ℝ) :
    IsCompact (g69K (X := X) R) := by
  have hcl : IsClosed (g69K (X := X) R) := by
    have : g69K (X := X) R = ((⋂ i : X, ⋂ j : X, {B : Matrix X X ℝ | B i j = B j i}) ∩
        (⋂ x : X → ℝ, {B : Matrix X X ℝ | 0 ≤ ∑ i, ∑ j, x i * B i j * x j})) ∩
        (⋂ i : X, {B : Matrix X X ℝ | ∑ j, B i j = 0}) ∩ {B : Matrix X X ℝ | ∑ i, B i i ≤ R} := by
      ext B; simp [g69K, and_assoc]
    rw [this]
    refine (((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ ?_).inter
      (isClosed_iInter fun x => isClosed_le ?_ ?_)).inter
      (isClosed_iInter fun i => isClosed_eq ?_ ?_)).inter (isClosed_le ?_ ?_) <;> fun_prop
  have hsub : g69K (X := X) R ⊆ Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Set.Icc (-R) R)) := by
    intro B hB i _ j _
    have hd : ∀ a, 0 ≤ B a a := by
      intro a
      have := hB.2.1 (fun b => if b = a then 1 else 0)
      simpa [Finset.sum_ite_eq] using this
    have hdle : ∀ a, B a a ≤ R := by
      intro a
      exact le_trans (Finset.single_le_sum (f := fun a => B a a) (fun b _ => hd b) (Finset.mem_univ a))
        hB.2.2.2
    have := g69_entry_bound B hB.1 hB.2.1 i j
    have h1 := hd i
    have h2 := hd j
    have h3 := hdle i
    have h4 := hdle j
    rcases abs_cases (B i j) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at this <;> constructor <;> linarith
  exact IsCompact.of_isClosed_subset (isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_Icc) hcl hsub


lemma g69_rep {X : Type*} [Fintype X] [DecidableEq X] (f : (X → X → ℝ) →L[ℝ] ℝ) :
    ∃ y : X → X → ℝ, ∀ w : X → X → ℝ, f w = ∑ i, ∑ j, y i j * w i j := by
  refine ⟨fun i j => f (Pi.single i (Pi.single j 1)), fun w => ?_⟩
  have hw : w = ∑ i, ∑ j, w i j • (Pi.single i (Pi.single j 1) : X → X → ℝ) := by
    ext a b
    have key : ∀ x x1 : X, (Pi.single x (Pi.single x1 (1:ℝ)) : X → X → ℝ) a b
        = (if a = x then (if b = x1 then 1 else 0) else 0) := by
      intro x x1
      by_cases h : a = x
      · subst h; simp [Pi.single_apply]
      · simp [Pi.single_apply, h]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, key]
    simp
  conv_lhs => rw [hw]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma g69_sumsq {X : Type*} [Fintype X] (z : X → ℝ) (hz : ∑ i, z i = 0) :
    ∑ i, ∑ j, (z i - z j) ^ 2 = 2 * (Fintype.card X : ℝ) * ∑ i, z i ^ 2 := by
  have : ∀ i j, (z i - z j) ^ 2 = z i ^ 2 + z j ^ 2 - 2 * (z i * z j) := fun i j => by ring
  simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul, hz]
  ring

def g69T {X : Type*} [Fintype X] : Matrix X X ℝ →ₗ[ℝ] (X → X → ℝ) where
  toFun A := fun i j => A i i + A j j - 2 * A i j
  map_add' A B := by ext i j; simp; ring
  map_smul' c A := by ext i j; simp; ring

def g69D {X : Type*} (d : X → X → ℝ) (c : ℝ) : Set (X → X → ℝ) :=
  {w | ∀ i j, d i j ^ 2 ≤ w i j ∧ w i j ≤ c ^ 2 * d i j ^ 2}

lemma g69D_convex {X : Type*} (d : X → X → ℝ) (c : ℝ) : Convex ℝ (g69D d c) := by
  intro w1 h1 w2 h2 a b ha hb hab i j
  obtain ⟨l1, u1⟩ := h1 i j
  obtain ⟨l2, u2⟩ := h2 i j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : a * d i j ^ 2 + b * d i j ^ 2 = d i j ^ 2 := by rw [← add_mul, hab, one_mul]
  have e2 : a * (c ^ 2 * d i j ^ 2) + b * (c ^ 2 * d i j ^ 2) = c ^ 2 * d i j ^ 2 := by
    rw [← add_mul, hab, one_mul]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left l1 ha, mul_le_mul_of_nonneg_left l2 hb]
  · nlinarith [mul_le_mul_of_nonneg_left u1 ha, mul_le_mul_of_nonneg_left u2 hb]

lemma g69D_closed {X : Type*} [Finite X] (d : X → X → ℝ) (c : ℝ) : IsClosed (g69D d c) := by
  have : g69D d c = ⋂ i : X, ⋂ j : X, ({w : X → X → ℝ | d i j ^ 2 ≤ w i j} ∩
      {w : X → X → ℝ | w i j ≤ c ^ 2 * d i j ^ 2}) := by
    ext w; simp [g69D, Set.mem_iInter]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (isClosed_le continuous_const (by fun_prop)).inter (isClosed_le (by fun_prop) continuous_const)


lemma g69_sep {X : Type*} [Fintype X] [DecidableEq X]
    (d : X → X → ℝ) (hd : GeometryOfGraphs.FlowCut.IsPseudometric d) (c : ℝ) (hc : 1 ≤ c)
    (h : ¬ ∃ A : Matrix X X ℝ, A.PosSemidef ∧
        ∀ i j, d i j ^ 2 ≤ A i i + A j j - 2 * A i j ∧
          A i i + A j j - 2 * A i j ≤ c ^ 2 * d i j ^ 2) :
    ∃ Y : X → X → ℝ, (∀ i j, Y i j = Y j i) ∧
      (∑ i, ∑ j, Y i j * (if 0 < Y i j then c ^ 2 * d i j ^ 2 else d i j ^ 2) < 0) ∧
      (∀ z : X → ℝ, ∑ i, z i = 0 → 0 ≤ ∑ i, ∑ j, Y i j * (z i - z j) ^ 2) := by
  have hne : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    exact h ⟨0, Matrix.PosSemidef.zero, fun i => isEmptyElim i⟩
  have hn : (0:ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  obtain ⟨n, hn_def⟩ : ∃ n : ℝ, n = Fintype.card X := ⟨_, rfl⟩
  rw [← hn_def] at hn
  obtain ⟨S0, hS0⟩ : ∃ S0 : ℝ, S0 = ∑ i, ∑ j, c ^ 2 * d i j ^ 2 := ⟨_, rfl⟩
  have hS0nn : 0 ≤ S0 := by
    rw [hS0]; exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = S0 / (2 * n) + 1 := ⟨_, rfl⟩
  have hRpos : 0 < R := by
    have : 0 ≤ S0 / (2 * n) := div_nonneg hS0nn (by positivity)
    rw [hR]; linarith
  have hRS0 : S0 = 2 * n * (R - 1) := by
    rw [hR]; field_simp; ring
  have hDsymm : ∀ w ∈ g69D d c, (fun i j => w j i) ∈ g69D d c := by
    intro w hw i j
    have := hw j i
    rw [hd.2.2.1 j i] at this
    exact this
  have h0K : (0 : Matrix X X ℝ) ∈ g69K R :=
    ⟨fun _ _ => rfl, fun x => by simp, fun i => by simp, by simpa using hRpos.le⟩
  obtain ⟨f, u, v, hs, huv, ht⟩ := geometric_hahn_banach_compact_closed
    ((g69K_convex R).linear_image g69T)
    ((g69K_compact R).image (LinearMap.continuous_of_finiteDimensional g69T))
    (g69D_convex d c) (g69D_closed d c) (by
      rw [Set.disjoint_left]
      rintro w ⟨B, hB, rfl⟩ hw
      exact h ⟨B, g69K_psd R hB, fun i j => hw i j⟩)
  obtain ⟨y, hy⟩ := g69_rep f
  have hF1 : ∀ B ∈ g69K (X := X) R, ∑ i, ∑ j, y i j * (B i i + B j j - 2 * B i j) < u := by
    intro B hB
    have := hs _ ⟨B, hB, rfl⟩
    rw [hy] at this
    exact this
  have hF2 : ∀ w ∈ g69D d c, v < ∑ i, ∑ j, y i j * w i j := by
    intro w hw
    have := ht w hw
    rwa [hy] at this
  have hu0 : 0 < u := by
    have := hs _ ⟨0, h0K, rfl⟩
    simpa using this
  obtain ⟨Y, hYdef⟩ : ∃ Y : X → X → ℝ, ∀ i j, Y i j = -(y i j + y j i) / 2 + u / R / (2 * n) :=
    ⟨_, fun _ _ => rfl⟩
  have hεR : u / R * R = u := by field_simp
  refine ⟨Y, fun i j => by rw [hYdef, hYdef]; ring, ?_, ?_⟩
  · -- C1
    obtain ⟨w0, hw0def⟩ : ∃ w0 : X → X → ℝ, ∀ i j,
        w0 i j = if 0 < Y i j then c ^ 2 * d i j ^ 2 else d i j ^ 2 := ⟨_, fun _ _ => rfl⟩
    have hw0 : w0 ∈ g69D d c := by
      intro i j
      rw [hw0def]
      have hc2 : 1 ≤ c ^ 2 := by nlinarith
      have : d i j ^ 2 ≤ c ^ 2 * d i j ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.2 hc2) (sq_nonneg (d i j))]
      split_ifs
      · exact ⟨this, le_rfl⟩
      · exact ⟨le_rfl, this⟩
    have e : ∀ i j, Y i j * (if 0 < Y i j then c ^ 2 * d i j ^ 2 else d i j ^ 2)
        = -(1/2) * (y i j * w0 i j) - (1/2) * (y j i * w0 i j) + u / R / (2 * n) * w0 i j := by
      intro i j
      rw [← hw0def, hYdef]; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_comm (f := fun i j => y j i * w0 i j)]
    have a1 := hF2 w0 hw0
    have a2 := hF2 _ (hDsymm w0 hw0)
    have a3 : ∑ i, ∑ j, w0 i j ≤ S0 := by
      rw [hS0]
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => (hw0 i j).2
    have hε : 0 < u / R / (2 * n) := by positivity
    have a4 : u / R / (2 * n) * ∑ i, ∑ j, w0 i j ≤ u / R / (2 * n) * S0 :=
      mul_le_mul_of_nonneg_left a3 hε.le
    have a5 : u / R / (2 * n) * S0 = u / R * (R - 1) := by
      rw [hRS0]; field_simp
    have a6 : u / R * (R - 1) = u - u / R := by rw [mul_sub, hεR]; ring
    have a7 : 0 < u / R := by positivity
    linarith
  · intro z hz
    by_cases hS : ∑ i, z i ^ 2 = 0
    · have hz0 : ∀ i, z i = 0 := fun i => by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (z i))).1 hS i
          (Finset.mem_univ i)
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      simp [hz0]
    · obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ i, z i ^ 2 := ⟨_, rfl⟩
      have hSpos : 0 < S := by
        rw [hSdef]
        exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg (z i)) (Ne.symm hS)
      obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = R / S := ⟨_, rfl⟩
      have htpos : 0 < t := by rw [htdef]; positivity
      have htS : t * S = R := by rw [htdef]; field_simp
      obtain ⟨z', hz'⟩ : ∃ z' : X → ℝ, ∀ i, z' i = Real.sqrt t * z i := ⟨_, fun _ => rfl⟩
      have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt htpos.le
      have hB : (Matrix.of fun i j => z' i * z' j) ∈ g69K (X := X) R := by
        refine ⟨fun i j => by simp [mul_comm], fun x => ?_, fun i => ?_, ?_⟩
        · have : ∑ i, ∑ j, x i * (Matrix.of fun i j => z' i * z' j) i j * x j
              = (∑ i, x i * z' i) * (∑ j, x j * z' j) := by
            rw [Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            simp only [Matrix.of_apply]; ring
          rw [this]; exact mul_self_nonneg _
        · simp only [Matrix.of_apply, ← Finset.mul_sum]
          have : ∑ j, z' j = 0 := by
            simp only [hz', ← Finset.mul_sum, hz, mul_zero]
          rw [this, mul_zero]
        · have : ∀ i, (Matrix.of fun i j => z' i * z' j) i i = t * z i ^ 2 := fun i => by
            simp only [Matrix.of_apply, hz']; linear_combination (z i ^ 2) * hsq
          simp only [this, ← Finset.mul_sum, ← hSdef, htS]; exact le_rfl
      have hlt := hF1 _ hB
      have hq : ∀ i j, y i j * ((Matrix.of fun i j => z' i * z' j) i i
          + (Matrix.of fun i j => z' i * z' j) j j - 2 * (Matrix.of fun i j => z' i * z' j) i j)
          = t * (y i j * (z i - z j) ^ 2) := by
        intro i j
        simp only [Matrix.of_apply, hz']
        linear_combination (y i j * (z i - z j) ^ 2) * hsq
      simp only [hq, ← Finset.mul_sum] at hlt
      obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ∑ i, ∑ j, y i j * (z i - z j) ^ 2 := ⟨_, rfl⟩
      rw [← hP] at hlt
      have hP2 : R * P < u * S := by
        calc R * P = (t * S) * P := by rw [htS]
          _ = (t * P) * S := by ring
          _ < u * S := mul_lt_mul_of_pos_right hlt hSpos
      have e : ∀ i j, Y i j * (z i - z j) ^ 2
          = -(1/2) * (y i j * (z i - z j) ^ 2) - (1/2) * (y j i * (z i - z j) ^ 2)
            + u / R / (2 * n) * (z i - z j) ^ 2 := by
        intro i j
        rw [hYdef]; ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hc2 : ∑ i, ∑ j, y j i * (z i - z j) ^ 2 = P := by
        rw [Finset.sum_comm, hP]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hc2, g69_sumsq z hz, ← hSdef, ← hn_def]
      have : u / R / (2 * n) * (2 * n * S) = u / R * S := by field_simp
      rw [this]
      have : P < u * S / R := by rw [lt_div_iff₀ hRpos]; linarith
      have h2 : u / R * S = u * S / R := by ring
      linarith


lemma g69_pair_nonneg {X : Type*} [Fintype X] [DecidableEq X] (Q A : Matrix X X ℝ)
    (hQ : Q.PosSemidef) (hA : A.PosSemidef) : 0 ≤ ∑ i, ∑ j, Q i j * A i j := by
  have h := (hQ.hadamard hA).dotProduct_mulVec_nonneg (fun _ => (1:ℝ))
  simpa [dotProduct, mulVec, Matrix.hadamard] using h

theorem g69_core {X : Type*} [Fintype X] [DecidableEq X]
    (d : X → X → ℝ) (hd : GeometryOfGraphs.FlowCut.IsPseudometric d) (c : ℝ) (hc : 1 ≤ c) :
    (¬ ∃ A : Matrix X X ℝ, A.PosSemidef ∧
        ∀ i j, d i j ^ 2 ≤ A i i + A j j - 2 * A i j ∧
          A i i + A j j - 2 * A i j ≤ c ^ 2 * d i j ^ 2) ↔
      ∃ Q : Matrix X X ℝ, Q.PosSemidef ∧
        ∃ lam mu : X → X → ℝ, (∀ i j, 0 ≤ lam i j) ∧ (∀ i j, 0 ≤ mu i j) ∧
          (∀ A : Matrix X X ℝ,
            (∑ i, ∑ j, Q i j * A i j) +
              ∑ i, ∑ j, (lam i j * (c ^ 2 * d i j ^ 2 - (A i i + A j j - 2 * A i j)) +
                mu i j * ((A i i + A j j - 2 * A i j) - d i j ^ 2)) =
            ∑ i, ∑ j, (lam i j * (c ^ 2 * d i j ^ 2) - mu i j * d i j ^ 2)) ∧
          ∑ i, ∑ j, (lam i j * (c ^ 2 * d i j ^ 2) - mu i j * d i j ^ 2) < 0 := by
  constructor
  · intro h
    obtain ⟨Y, hs, h1, h2⟩ := g69_sep d hd c hc h
    exact g69_alg d c Y hs h1 h2
  · rintro ⟨Q, hQ, lam, mu, hl, hm, hid, hneg⟩ ⟨A, hA, hAc⟩
    have h1 := hid A
    have h2 := g69_pair_nonneg Q A hQ hA
    have h3 : 0 ≤ ∑ i, ∑ j, (lam i j * (c ^ 2 * d i j ^ 2 - (A i i + A j j - 2 * A i j)) +
                mu i j * ((A i i + A j j - 2 * A i j) - d i j ^ 2)) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        add_nonneg (mul_nonneg (hl i j) (sub_nonneg.2 (hAc i j).2))
          (mul_nonneg (hm i j) (sub_nonneg.2 (hAc i j).1))
    linarith

end GeometryOfGraphs.EuclidDist

open GeometryOfGraphs.EuclidDist


theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (d : X → X → ℝ) (hd : GeometryOfGraphs.FlowCut.IsPseudometric d) (c : ℝ) (hc : 1 ≤ c) :
    (¬ ∃ A : Matrix X X ℝ, A.PosSemidef ∧
        ∀ i j, d i j ^ 2 ≤ A i i + A j j - 2 * A i j ∧
          A i i + A j j - 2 * A i j ≤ c ^ 2 * d i j ^ 2) ↔
      ∃ Q : Matrix X X ℝ, Q.PosSemidef ∧
        ∃ lam mu : X → X → ℝ, (∀ i j, 0 ≤ lam i j) ∧ (∀ i j, 0 ≤ mu i j) ∧
          (∀ A : Matrix X X ℝ,
            (∑ i, ∑ j, Q i j * A i j) +
              ∑ i, ∑ j, (lam i j * (c ^ 2 * d i j ^ 2 - (A i i + A j j - 2 * A i j)) +
                mu i j * ((A i i + A j j - 2 * A i j) - d i j ^ 2)) =
            ∑ i, ∑ j, (lam i j * (c ^ 2 * d i j ^ 2) - mu i j * d i j ^ 2)) ∧
          ∑ i, ∑ j, (lam i j * (c ^ 2 * d i j ^ 2) - mu i j * d i j ^ 2) < 0 := by
  exact g69_core d hd c hc
