-- Prove2me | solution 1 for NumStochOpt.Bounds.eq_2_30_2_31_dual_multiplier_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T04:00:01.259441+00:00
-- url     : https://prove2.me/submissions/8524d9e4-885e-42e7-b216-670e494a9d17

import Definitions.Def_NumStochOpt_Bounds_RecourseCost
import Mathlib


set_option autoImplicit false
set_option maxHeartbeats 800000

open Matrix MeasureTheory
open scoped BigOperators
open Classical
namespace NumStochOpt.Bounds

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def emBase (W : Matrix ι κ ℝ) (q : κ → ℝ) (z : ι → ℝ) : EReal :=
  ⨅ y ∈ {y : κ → ℝ | 0 ≤ y ∧ W *ᵥ y = z}, ((q ⬝ᵥ y : ℝ) : EReal)

lemma em_base_native {ν : Type*} [Fintype ν] (W : Matrix ι κ ℝ) (q : κ → ℝ)
    (h : ι → ℝ) (T : Matrix ι ν ℝ) (x : ν → ℝ) :
    recourseCost W q h T x = emBase W q (h - T *ᵥ x) := rfl

lemma em_weak_duality (W : Matrix ι κ ℝ) (q : κ → ℝ) (u : ι → ℝ)
    (hu : W.transpose *ᵥ u ≤ q) (y : κ → ℝ) (hy : 0 ≤ y) :
    u ⬝ᵥ (W *ᵥ y) ≤ q ⬝ᵥ y := by
  have he : u ⬝ᵥ (W *ᵥ y) = (W.transpose *ᵥ u) ⬝ᵥ y := by
    simp only [dotProduct, mulVec, transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hu k) (hy k)

lemma em_base_lower (W : Matrix ι κ ℝ) (q : κ → ℝ) (u z : ι → ℝ)
    (hu : W.transpose *ᵥ u ≤ q) : ((u ⬝ᵥ z : ℝ) : EReal) ≤ emBase W q z := by
  refine le_iInf₂ fun y hy => ?_
  rw [EReal.coe_le_coe_iff, ← hy.2]
  exact em_weak_duality W q u hu y hy.1

lemma em_base_finite (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) (q : κ → ℝ)
    (hq : DualFeasible W q) (z : ι → ℝ) : emBase W q z ≠ ⊤ ∧ emBase W q z ≠ ⊥ := by
  obtain ⟨y, hy, he⟩ := hW z
  obtain ⟨u, hu⟩ := hq
  constructor
  · have hb : emBase W q z ≤ ((q ⬝ᵥ y : ℝ) : EReal) := iInf₂_le y ⟨hy, he⟩
    exact ne_of_lt (hb.trans_lt (EReal.coe_lt_top _))
  · have hb := em_base_lower W q u z hu
    exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hb)

end NumStochOpt.Bounds


set_option autoImplicit false
set_option maxHeartbeats 800000

open Matrix Finset
namespace EMFM

/-- Feasibility of the system indexed by an arbitrary finite type. -/
def Feas {ι : Type*} [Fintype ι] {n : ℕ} (A : ι → Fin n → ℝ) (c : ι → ℝ) : Prop :=
  ∃ x : Fin n → ℝ, ∀ i, c i ≤ ∑ k, A i k * x k

/-- Fourier–Motzkin elimination of the last variable, for an arbitrary finite index type. -/
theorem fm_step {ι : Type*} [Fintype ι] {n : ℕ} (A : ι → Fin (n + 1) → ℝ) (c : ι → ℝ) :
    Feas A c ↔
      ∃ y : Fin n → ℝ,
        (∀ i, A i (Fin.last n) = 0 → c i ≤ ∑ k : Fin n, A i k.castSucc * y k) ∧
        (∀ i j, 0 < A i (Fin.last n) → A j (Fin.last n) < 0 →
            A i (Fin.last n) * c j - A j (Fin.last n) * c i ≤
              ∑ k : Fin n, (A i (Fin.last n) * A j k.castSucc
                - A j (Fin.last n) * A i k.castSucc) * y k) := by
  classical
  have hmv : ∀ (x : Fin (n + 1) → ℝ) (i : ι),
      (∑ k, A i k * x k)
        = (∑ k : Fin n, A i k.castSucc * x k.castSucc) + A i (Fin.last n) * x (Fin.last n) :=
    fun x i => Fin.sum_univ_castSucc _
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun k => x k.castSucc, ?_, ?_⟩
    · intro i hi
      have := hx i
      rw [hmv, hi] at this
      linarith
    · intro i j hi hj
      have h1 := hx i
      have h2 := hx j
      rw [hmv] at h1 h2
      have hsum : ∑ k : Fin n, (A i (Fin.last n) * A j k.castSucc
            - A j (Fin.last n) * A i k.castSucc) * x k.castSucc
          = A i (Fin.last n) * (∑ k : Fin n, A j k.castSucc * x k.castSucc)
            - A j (Fin.last n) * (∑ k : Fin n, A i k.castSucc * x k.castSucc) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [hsum]
      nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt (neg_pos.mpr hj)),
        mul_le_mul_of_nonneg_left h2 (le_of_lt hi)]
  · rintro ⟨y, hZ, hPN⟩
    set S : ι → ℝ := fun i => ∑ k : Fin n, A i k.castSucc * y k with hS
    set B : ι → ℝ := fun i => A i (Fin.last n) with hB
    have hpair : ∀ i j, 0 < B i → B j < 0 → B i * c j - B j * c i ≤ B i * S j - B j * S i := by
      intro i j hi hj
      have h := hPN i j hi hj
      have hsum : ∑ k : Fin n, (A i (Fin.last n) * A j k.castSucc
            - A j (Fin.last n) * A i k.castSucc) * y k = B i * S j - B j * S i := by
        rw [hS, hB]
        simp only
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [hsum] at h
      exact h
    set P : Finset ι := Finset.univ.filter (fun i => 0 < B i) with hPdef
    set N : Finset ι := Finset.univ.filter (fun i => B i < 0) with hNdef
    have key : ∀ v : ℝ,
        (∀ i ∈ P, (c i - S i) / B i ≤ v) → (∀ j ∈ N, v ≤ (c j - S j) / B j) → Feas A c := by
      intro v hlow hup
      refine ⟨Fin.snoc y v, fun i => ?_⟩
      have hval : (∑ k, A i k * (Fin.snoc y v : Fin (n+1) → ℝ) k) = S i + B i * v := by
        rw [hmv]
        simp [hS, hB, Fin.snoc_castSucc, Fin.snoc_last]
      rw [hval]
      rcases lt_trichotomy (B i) 0 with hneg | hzero | hpos
      · have := hup i (by simp [hNdef, hneg])
        rw [le_div_iff_of_neg hneg] at this
        linarith
      · have h0 : A i (Fin.last n) = 0 := hzero
        have := hZ i h0
        rw [hzero]
        simpa [hS] using this
      · have := hlow i (by simp [hPdef, hpos])
        rw [div_le_iff₀ hpos] at this
        linarith
    by_cases hP : P.Nonempty
    · obtain ⟨i₀, hi₀, hmax⟩ := P.exists_max_image (fun i => (c i - S i) / B i) hP
      refine key ((c i₀ - S i₀) / B i₀) (fun i hi => hmax i hi) (fun j hj => ?_)
      have hi₀' : 0 < B i₀ := by simpa [hPdef] using hi₀
      have hj' : B j < 0 := by simpa [hNdef] using hj
      have hp := hpair i₀ j hi₀' hj'
      rw [le_div_iff_of_neg hj', div_mul_eq_mul_div, le_div_iff₀ hi₀']
      nlinarith [hp]
    · by_cases hN : N.Nonempty
      · obtain ⟨j₀, hj₀, hmin⟩ := N.exists_min_image (fun j => (c j - S j) / B j) hN
        exact key ((c j₀ - S j₀) / B j₀) (fun i hi => absurd ⟨i, hi⟩ hP) (fun j hj => hmin j hj)
      · exact key 0 (fun i hi => absurd ⟨i, hi⟩ hP) (fun j hj => absurd ⟨j, hj⟩ hN)

end EMFM
namespace EMFM
open Classical
noncomputable def redF {ι : Type*} {n : ℕ} (A : ι → Fin (n + 1) → ℝ) (f : ι → ℝ) :
    (ι ⊕ ι × ι) → ℝ
  | Sum.inl i => if A i (Fin.last n) = 0 then f i else 0
  | Sum.inr (i, j) =>
      if 0 < A i (Fin.last n) ∧ A j (Fin.last n) < 0 then
        A i (Fin.last n) * f j - A j (Fin.last n) * f i
      else 0


lemma feas_red {ι : Type*} [Fintype ι] {n : ℕ} (A : ι → Fin (n + 1) → ℝ) (c : ι → ℝ) :
    Feas A c ↔ Feas (fun i' k => redF A (fun i => A i k.castSucc) i') (redF A c) := by
  classical
  rw [fm_step]
  constructor
  · rintro ⟨y, hZ, hPN⟩
    refine ⟨y, ?_⟩
    rintro (i | ⟨i, j⟩)
    · by_cases h : A i (Fin.last n) = 0
      · have e : ∀ k : Fin n, redF A (fun i => A i k.castSucc) (Sum.inl i) = A i k.castSucc := by
          intro k; simp only [redF, if_pos h]
        simp only [e, redF, if_pos h]
        exact hZ i h
      · simp only [redF, if_neg h]
        simp
    · by_cases h : 0 < A i (Fin.last n) ∧ A j (Fin.last n) < 0
      · have e : ∀ k : Fin n, redF A (fun i => A i k.castSucc) (Sum.inr (i, j))
            = A i (Fin.last n) * A j k.castSucc - A j (Fin.last n) * A i k.castSucc := by
          intro k; simp only [redF, if_pos h]
        simp only [e, redF, if_pos h]
        exact hPN i j h.1 h.2
      · simp only [redF, if_neg h]
        simp
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_, ?_⟩
    · intro i hi
      have := hy (Sum.inl i)
      simp only [redF, if_pos hi] at this
      exact this
    · intro i j hi hj
      have := hy (Sum.inr (i, j))
      simp only [redF, if_pos (And.intro hi hj)] at this
      exact this


end EMFM


set_option autoImplicit false
set_option maxHeartbeats 800000

open Matrix Finset
open scoped BigOperators
open Classical
namespace NumStochOpt.Bounds

universe u v
variable {E : Type v} [AddCommGroup E] [Module ℝ E]

/-- Eliminating all primal variables preserves linear dependence on the parameters. -/
lemma em_fm_linear : ∀ (n : ℕ) {R : Type u} [Fintype R]
    (A : R → Fin n → ℝ) (b : R → E →ₗ[ℝ] ℝ),
    ∃ U : Finset (E →ₗ[ℝ] ℝ), ∀ p : E,
      EMFM.Feas A (fun r => b r p) ↔ ∀ l ∈ U, l p ≤ 0 := by
  intro n
  induction n with
  | zero =>
    intro R _ A b
    refine ⟨Finset.univ.image b, ?_⟩
    intro p
    constructor
    · rintro ⟨x, hx⟩ l hl
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hl
      simpa using hx r
    · intro hp
      refine ⟨fun k => Fin.elim0 k, fun r => ?_⟩
      simpa using hp (b r) (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)
  | succ n ih =>
    intro R _ A b
    let B : (R ⊕ R × R) → E →ₗ[ℝ] ℝ
      | Sum.inl r => if A r (Fin.last n) = 0 then b r else 0
      | Sum.inr (r, s) => if 0 < A r (Fin.last n) ∧ A s (Fin.last n) < 0 then
          A r (Fin.last n) • b s - A s (Fin.last n) • b r else 0
    obtain ⟨U, hU⟩ := ih (fun r k => EMFM.redF A (fun s => A s k.castSucc) r) B
    refine ⟨U, ?_⟩
    intro p
    rw [EMFM.feas_red]
    have he : EMFM.redF A (fun r => b r p) = fun r => B r p := by
      funext r
      rcases r with r | ⟨r, s⟩
      · by_cases h : A r (Fin.last n) = 0 <;> simp [EMFM.redF, B, h]
      · by_cases h : 0 < A r (Fin.last n) ∧ A s (Fin.last n) < 0 <;>
          simp [EMFM.redF, B, h, smul_eq_mul]
    rw [he]
    exact hU p

end NumStochOpt.Bounds



set_option autoImplicit false
set_option maxHeartbeats 1000000

open Matrix Finset
open scoped BigOperators
open Classical
namespace NumStochOpt.Bounds

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def emRowA (W : Matrix ι κ ℝ) (q : κ → ℝ) : (κ ⊕ (ι ⊕ (ι ⊕ Unit))) → κ → ℝ
  | Sum.inl k => fun l => if l = k then 1 else 0
  | Sum.inr (Sum.inl j) => fun k => W j k
  | Sum.inr (Sum.inr (Sum.inl j)) => fun k => -W j k
  | Sum.inr (Sum.inr (Sum.inr _)) => fun k => -q k

def emRowB : (κ ⊕ (ι ⊕ (ι ⊕ Unit))) → ((ι → ℝ) × ℝ) →ₗ[ℝ] ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl j) => (LinearMap.proj j).comp (LinearMap.fst ℝ (ι → ℝ) ℝ)
  | Sum.inr (Sum.inr (Sum.inl j)) => -((LinearMap.proj j).comp (LinearMap.fst ℝ (ι → ℝ) ℝ))
  | Sum.inr (Sum.inr (Sum.inr _)) => -(LinearMap.snd ℝ (ι → ℝ) ℝ)

lemma em_row_feasible (W : Matrix ι κ ℝ) (q : κ → ℝ) (z : ι → ℝ) (t : ℝ) :
    (∃ y : κ → ℝ, ∀ r, emRowB (κ := κ) r (z, t) ≤ ∑ k, emRowA W q r k * y k) ↔
      ∃ y : κ → ℝ, 0 ≤ y ∧ W *ᵥ y = z ∧ q ⬝ᵥ y ≤ t := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_, ?_, ?_⟩
    · intro k
      simpa [emRowA, emRowB] using hy (Sum.inl k)
    · funext j
      have h1 := hy (Sum.inr (Sum.inl j))
      have h2 := hy (Sum.inr (Sum.inr (Sum.inl j)))
      simp [emRowA, emRowB, Finset.sum_neg_distrib] at h1 h2
      change ∑ k, W j k * y k = z j
      linarith
    · have h := hy (Sum.inr (Sum.inr (Sum.inr ())))
      simp [emRowA, emRowB, Finset.sum_neg_distrib] at h
      simpa [dotProduct] using h
  · rintro ⟨y, hy, hWy, hq⟩
    refine ⟨y, ?_⟩
    rintro (k | (j | (j | u)))
    · simpa [emRowA, emRowB] using hy k
    · simpa [emRowA, emRowB, mulVec, dotProduct, hWy] using le_of_eq (congrFun hWy j).symm
    · have hj := congrFun hWy j
      simp [emRowA, emRowB, Finset.sum_neg_distrib, mulVec, dotProduct] at hj ⊢
      linarith
    · simp [emRowA, emRowB, Finset.sum_neg_distrib, dotProduct] at hq ⊢
      linarith

lemma em_epigraph_finite_constraints (W : Matrix ι κ ℝ) (q : κ → ℝ) :
    ∃ U : Finset (((ι → ℝ) × ℝ) →ₗ[ℝ] ℝ), ∀ z t,
      (∃ y : κ → ℝ, 0 ≤ y ∧ W *ᵥ y = z ∧ q ⬝ᵥ y ≤ t) ↔
        ∀ l ∈ U, l (z, t) ≤ 0 := by
  let e := Fintype.equivFin κ
  obtain ⟨U, hU⟩ := em_fm_linear (Fintype.card κ)
    (fun r k => emRowA W q r (e.symm k)) (emRowB (ι := ι) (κ := κ))
  refine ⟨U, ?_⟩
  intro z t
  rw [← hU (z, t), ← em_row_feasible W q z t]
  have hs (x : Fin (Fintype.card κ) → ℝ) (r : κ ⊕ (ι ⊕ (ι ⊕ Unit))) :
      (∑ k, emRowA W q r (e.symm k) * x k) = ∑ k, emRowA W q r k * x (e k) := by
    simpa using (Equiv.sum_comp e (fun k => emRowA W q r (e.symm k) * x k)).symm
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨fun k => y (e.symm k), fun r => ?_⟩
    rw [hs]
    simpa using hy r
  · rintro ⟨x, hx⟩
    refine ⟨fun k => x (e k), fun r => ?_⟩
    simpa only [hs] using hx r

end NumStochOpt.Bounds



set_option autoImplicit false
set_option maxHeartbeats 1000000

open Matrix Finset
open scoped BigOperators
open Classical
namespace NumStochOpt.Bounds

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma em_form_split (l : ((ι → ℝ) × ℝ) →ₗ[ℝ] ℝ) (z : ι → ℝ) (t : ℝ) :
    l (z, t) = l (z, 0) + t * l (0, 1) := by
  have he : (z, t) = (z, (0 : ℝ)) + t • ((0, 1) : (ι → ℝ) × ℝ) := by
    ext <;> simp
  rw [he, map_add, map_smul]
  rfl

/-- Complete recourse and dual feasibility give a finite maximum of linear forms in the
right-hand side. Fourier–Motzkin elimination proves the epigraph representation directly. -/
lemma em_base_finite_max (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) (q : κ → ℝ)
    (hq : DualFeasible W q) :
    ∃ F : Finset ((ι → ℝ) →ₗ[ℝ] ℝ), ∃ hF : F.Nonempty,
      ∀ z, emBase W q z = ((F.sup' hF (fun l => l z) : ℝ) : EReal) := by
  obtain ⟨U, hU⟩ := em_epigraph_finite_constraints W q
  have ht (l : ((ι → ℝ) × ℝ) →ₗ[ℝ] ℝ) (hl : l ∈ U) : l (0, 1) ≤ 0 := by
    exact (hU 0 1).mp ⟨0, by simp, by simp, by simp [dotProduct]⟩ l hl
  have hz (l : ((ι → ℝ) × ℝ) →ₗ[ℝ] ℝ) (hl : l ∈ U) (hl0 : l (0, 1) = 0)
      (z : ι → ℝ) : l (z, 0) = 0 := by
    have hle (w : ι → ℝ) : l (w, 0) ≤ 0 := by
      obtain ⟨y, hy, hWy⟩ := hW w
      have h := (hU w (q ⬝ᵥ y)).mp ⟨y, hy, hWy, le_rfl⟩ l hl
      rwa [em_form_split, hl0, mul_zero, add_zero] at h
    have he : l (-z, 0) = -l (z, 0) := by
      simpa using l.map_neg (z, (0 : ℝ))
    have h1 := hle z
    have h2 := hle (-z)
    rw [he] at h2
    linarith
  have hn : ¬ (∃ y : κ → ℝ, 0 ≤ y ∧ W *ᵥ y = 0 ∧ q ⬝ᵥ y ≤ -1) := by
    rintro ⟨y, hy, hWy, hc⟩
    obtain ⟨u, hu⟩ := hq
    have h := em_weak_duality W q u hu y hy
    rw [hWy, dotProduct_zero] at h
    linarith
  have hbad : ¬ ∀ l ∈ U, l (0, -1) ≤ 0 := (hU 0 (-1)).not.mp hn
  push_neg at hbad
  obtain ⟨l0, hl0, hpos⟩ := hbad
  have hlneg : l0 (0, 1) < 0 := by
    rw [em_form_split] at hpos
    have he : l0 ((0 : ι → ℝ), (0 : ℝ)) = 0 := l0.map_zero
    rw [he] at hpos
    linarith
  let N := U.filter (fun l => l (0, 1) < 0)
  have hN : N.Nonempty := ⟨l0, Finset.mem_filter.mpr ⟨hl0, hlneg⟩⟩
  let f : (((ι → ℝ) × ℝ) →ₗ[ℝ] ℝ) → (ι → ℝ) →ₗ[ℝ] ℝ := fun l =>
    (-l (0, 1))⁻¹ • (l.comp (LinearMap.inl ℝ (ι → ℝ) ℝ))
  have hf (l : ((ι → ℝ) × ℝ) →ₗ[ℝ] ℝ) (z : ι → ℝ) :
      f l z = l (z, 0) / (-l (0, 1)) := by
    simp [f, div_eq_mul_inv, mul_comm]
  have hchar (z : ι → ℝ) (t : ℝ) :
      (∃ y : κ → ℝ, 0 ≤ y ∧ W *ᵥ y = z ∧ q ⬝ᵥ y ≤ t) ↔ ∀ l ∈ N, f l z ≤ t := by
    rw [hU]
    constructor
    · intro hp l hl
      obtain ⟨hlU, hlN⟩ := Finset.mem_filter.mp hl
      rw [hf, div_le_iff₀ (neg_pos.mpr hlN)]
      have h := hp l hlU
      rw [em_form_split] at h
      linarith
    · intro hp l hl
      by_cases hn : l (0, 1) < 0
      · have h := hp l (Finset.mem_filter.mpr ⟨hl, hn⟩)
        rw [hf, div_le_iff₀ (neg_pos.mpr hn)] at h
        rw [em_form_split]
        linarith
      · have h0 : l (0, 1) = 0 := le_antisymm (ht l hl) (not_lt.mp hn)
        rw [em_form_split, hz l hl h0 z, h0]
        simp
  let F := N.image f
  have hF : F.Nonempty := hN.image f
  refine ⟨F, hF, ?_⟩
  intro z
  have hmax (t : ℝ) :
      (∃ y : κ → ℝ, 0 ≤ y ∧ W *ᵥ y = z ∧ q ⬝ᵥ y ≤ t) ↔ F.sup' hF (fun l => l z) ≤ t := by
    rw [hchar, Finset.sup'_le_iff]
    constructor
    · intro hp l hl
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hl
      exact hp k hk
    · intro hp l hl
      exact hp (f l) (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
  apply le_antisymm
  · obtain ⟨y, hy, hWy, hc⟩ := (hmax (F.sup' hF (fun l => l z))).mpr le_rfl
    exact (iInf₂_le y ⟨hy, hWy⟩).trans (EReal.coe_le_coe_iff.mpr hc)
  · refine le_iInf₂ fun y hy => ?_
    rw [EReal.coe_le_coe_iff]
    exact (hmax (q ⬝ᵥ y)).mp ⟨y, hy.1, hy.2, le_rfl⟩

end NumStochOpt.Bounds



set_option autoImplicit false
set_option maxHeartbeats 1000000

open Matrix MeasureTheory Finset
open scoped BigOperators
open Classical
namespace NumStochOpt.Bounds

lemma em_integrable_sup' {Ω β : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S : Finset β) (hS : S.Nonempty) (f : β → Ω → ℝ)
    (hi : ∀ j ∈ S, Integrable (f j) P) :
    Integrable (fun ω => S.sup' hS (fun j => f j ω)) P := by
  revert hi
  induction hS using Finset.Nonempty.cons_induction with
  | singleton j =>
    intro hi
    simpa using hi j (Finset.mem_singleton_self _)
  | cons j S hj hS ih =>
    intro hi
    simp_rw [Finset.sup'_cons hS]
    exact (hi j (Finset.mem_cons_self _ _)).sup
      (ih (fun k hk => hi k (Finset.mem_cons_of_mem hk)))

lemma em_base_integrable_fixed {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    (P : Measure Ω) (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) (q : κ → ℝ)
    (hq : DualFeasible W q) (z : Ω → ι → ℝ)
    (hz : ∀ j, Integrable (fun ω => z ω j) P) :
    Integrable (fun ω => (emBase W q (z ω)).toReal) P := by
  obtain ⟨F, hF, he⟩ := em_base_finite_max W hW q hq
  simp_rw [he, EReal.toReal_coe]
  apply em_integrable_sup' P F hF
  intro l _
  exact (LinearMap.toContinuousLinearMap l).integrable_comp (integrable_pi_iff.mpr hz)

lemma em_native_dual_bound {Ω ι κ ν : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [Fintype ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) (c : ν → ℝ) (q : κ → ℝ)
    (h : Ω → ι → ℝ) (T : Ω → Matrix ι ν ℝ)
    (hh : ∀ i, Integrable (fun ω => h ω i) P) (hT : ∀ i j, Integrable (fun ω => T ω i j) P)
    {L : ℕ} [NeZero L] (u : Fin L → ι → ℝ) (hu : ∀ ℓ, W.transpose *ᵥ u ℓ ≤ q) (x : ν → ℝ) :
    (∀ ω, ((dualLowerBound u (h ω) (T ω) x : ℝ) : EReal) ≤ recourseCost W q (h ω) (T ω) x) ∧
      c ⬝ᵥ x + ∫ ω, dualLowerBound u (h ω) (T ω) x ∂P ≤
        c ⬝ᵥ x + expectedRecourse P W (fun _ => q) h T x := by
  let z : Ω → ι → ℝ := fun ω => h ω - T ω *ᵥ x
  have hz (i : ι) : Integrable (fun ω => z ω i) P := by
    exact (hh i).sub (integrable_finsetSum Finset.univ (fun j _ => (hT i j).mul_const (x j)))
  have hq : DualFeasible W q := ⟨u 0, hu 0⟩
  have hfin (ω : Ω) := em_base_finite W hW q hq (z ω)
  have hl (ω : Ω) : dualLowerBound u (h ω) (T ω) x ≤ (emBase W q (z ω)).toReal := by
    apply Finset.sup'_le
    intro ℓ _
    have hb := em_base_lower W q (u ℓ) (z ω) (hu ℓ)
    have hr := EReal.toReal_le_toReal hb (EReal.coe_ne_bot _) (hfin ω).1
    simp only [EReal.toReal_coe] at hr
    change z ω ⬝ᵥ u ℓ ≤ _
    rw [dotProduct_comm]
    exact hr
  have hli : Integrable (fun ω => dualLowerBound u (h ω) (T ω) x) P := by
    apply em_integrable_sup' P Finset.univ Finset.univ_nonempty
    intro ℓ _
    exact integrable_finsetSum Finset.univ (fun j _ => (hz j).mul_const (u ℓ j))
  have hri := em_base_integrable_fixed P W hW q hq z hz
  refine ⟨?_, ?_⟩
  · intro ω
    rw [em_base_native, ← EReal.coe_toReal (hfin ω).1 (hfin ω).2, EReal.coe_le_coe_iff]
    exact hl ω
  · exact add_le_add_right (integral_mono_ae hli hri (Filter.Eventually.of_forall hl)) _

end NumStochOpt.Bounds


open MeasureTheory Matrix NumStochOpt.Bounds in

/-- Eqs. (2.30)–(2.31), p. 43: with deterministic `q` and dual-feasible multipliers
`u_1, …, u_L` (`Wᵀ u_ℓ ≤ q`), pointwise `Q(x, ξ(ω)) ≥ max_ℓ (h(ω) − T(ω) x)ᵀ u_ℓ`, and taking
expectations `ψ(x) = cᵀx + E Q(x, ξ) ≥ cᵀx + E max_ℓ (h(ω) − T(ω) x)ᵀ u_ℓ`. -/
theorem solution {Ω ι κ ν : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [Fintype ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) (c : ν → ℝ) (q : κ → ℝ)
    (h : Ω → ι → ℝ) (T : Ω → Matrix ι ν ℝ)
    (hh : ∀ i, Integrable (fun ω => h ω i) P) (hT : ∀ i j, Integrable (fun ω => T ω i j) P)
    {L : ℕ} [NeZero L] (u : Fin L → ι → ℝ) (hu : ∀ ℓ, W.transpose *ᵥ u ℓ ≤ q) (x : ν → ℝ) :
    (∀ ω, ((dualLowerBound u (h ω) (T ω) x : ℝ) : EReal) ≤ recourseCost W q (h ω) (T ω) x) ∧
      c ⬝ᵥ x + ∫ ω, dualLowerBound u (h ω) (T ω) x ∂P ≤
        c ⬝ᵥ x + expectedRecourse P W (fun _ => q) h T x := by
  exact em_native_dual_bound P W hW c q h T hh hT u hu x


#print axioms solution
