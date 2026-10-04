-- Prove2me | solution 1 for NumStochOpt.Bounds.property_e_expected_recourse_finite_convex
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T04:03:54.715974+00:00
-- url     : https://prove2.me/submissions/c51c3cd8-882b-494e-aa3d-cad5b2256fd1

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

open Matrix Finset
open scoped BigOperators
open Classical
namespace NumStochOpt.Bounds

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

def emHTMap (x : ν → ℝ) : ((ι → ℝ) × Matrix ι ν ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun p := p.1 - p.2 *ᵥ x
  map_add' p q := by
    ext j
    change (p.1 j + q.1 j) - (∑ k, (p.2 j k + q.2 j k) * x k) =
      (p.1 j - ∑ k, p.2 j k * x k) + (q.1 j - ∑ k, q.2 j k * x k)
    simp only [add_mul, Finset.sum_add_distrib]
    ring
  map_smul' r p := by
    ext j
    change r * p.1 j - (∑ k, (r * p.2 j k) * x k) = r * (p.1 j - ∑ k, p.2 j k * x k)
    simp only [mul_assoc, ← Finset.mul_sum]
    ring

noncomputable def emXMap (h : ι → ℝ) (T : Matrix ι ν ℝ) : (ν → ℝ) →ᵃ[ℝ] (ι → ℝ) where
  toFun x := h - T *ᵥ x
  linear := -(Matrix.toLin' T)
  map_vadd' x y := by
    ext j
    simp only [vadd_eq_add, Pi.sub_apply, Pi.add_apply, LinearMap.neg_apply,
      Pi.neg_apply, Matrix.toLin'_apply, mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
    ring

lemma em_finite_max_transport {E : Type*} [AddCommGroup E] [Module ℝ E]
    (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) (q : κ → ℝ) (hq : DualFeasible W q)
    (g : E →ᵃ[ℝ] (ι → ℝ)) :
    ∃ U : Finset (E →ᵃ[ℝ] ℝ), ∃ hU : U.Nonempty,
      ∀ x, emBase W q (g x) = ((U.sup' hU (fun l => l x) : ℝ) : EReal) := by
  obtain ⟨F, hF, he⟩ := em_base_finite_max W hW q hq
  let lift : ((ι → ℝ) →ₗ[ℝ] ℝ) → E →ᵃ[ℝ] ℝ := fun l => l.toAffineMap.comp g
  refine ⟨F.image lift, hF.image lift, ?_⟩
  intro x
  rw [Finset.sup'_image]
  exact he (g x)

lemma em_native_hT_affine (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) (q : κ → ℝ)
    (hq : DualFeasible W q) (x : ν → ℝ) :
    ∃ U : Finset (((ι → ℝ) × Matrix ι ν ℝ) →ᵃ[ℝ] ℝ), ∃ hU : U.Nonempty,
      ∀ (h : ι → ℝ) (T : Matrix ι ν ℝ),
        recourseCost W q h T x = ((U.sup' hU (fun g => g (h, T)) : ℝ) : EReal) := by
  obtain ⟨U, hU, he⟩ := em_finite_max_transport W hW q hq (emHTMap (ι := ι) x).toAffineMap
  exact ⟨U, hU, fun h T => he (h, T)⟩

lemma em_native_x_affine (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) (q : κ → ℝ)
    (hq : DualFeasible W q) (h : ι → ℝ) (T : Matrix ι ν ℝ) :
    ∃ U : Finset ((ν → ℝ) →ᵃ[ℝ] ℝ), ∃ hU : U.Nonempty,
      ∀ x, recourseCost W q h T x = ((U.sup' hU (fun g => g x) : ℝ) : EReal) := by
  exact em_finite_max_transport W hW q hq (emXMap h T)

end NumStochOpt.Bounds



set_option autoImplicit false
set_option maxHeartbeats 1000000

open Matrix MeasureTheory Filter Topology
open scoped BigOperators
open Classical
namespace NumStochOpt.Bounds

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma em_right_inverse (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) :
    ∃ R : (ι → ℝ) →L[ℝ] (κ → ℝ), ∀ z, W *ᵥ R z = z := by
  let L : (κ → ℝ) →L[ℝ] (ι → ℝ) := LinearMap.toContinuousLinearMap (Matrix.toLin' W)
  have hs : Function.Surjective L := by
    intro z
    obtain ⟨y, _, hy⟩ := hW z
    exact ⟨y, hy⟩
  obtain ⟨R, hR⟩ := L.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hs)
  refine ⟨R, fun z => ?_⟩
  exact congrArg (fun F : (ι → ℝ) →L[ℝ] (ι → ℝ) => F z) hR

lemma em_positive_kernel (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) :
    ∃ k : κ → ℝ, (∀ j, 0 < k j) ∧ W *ᵥ k = 0 := by
  obtain ⟨y, hy, he⟩ := hW (-(W *ᵥ (fun _ => (1 : ℝ))))
  refine ⟨y + (fun _ => 1), ?_, ?_⟩
  · intro j
    change 0 < y j + 1
    exact add_pos_of_nonneg_of_pos (hy j) zero_lt_one
  · rw [Matrix.mulVec_add, he, neg_add_cancel]

/-- The extended recourse value is jointly upper semicontinuous in costs and right-hand
side. Strict feasibility obtained from complete recourse also covers infinite negative values. -/
lemma em_base_upperSemicontinuous (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) :
    UpperSemicontinuous (fun p : (κ → ℝ) × (ι → ℝ) => emBase W p.1 p.2) := by
  obtain ⟨R, hR⟩ := em_right_inverse W hW
  obtain ⟨k, hk, hWk⟩ := em_positive_kernel W hW
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro b
  induction b using EReal.rec with
  | bot => simpa using isOpen_empty
  | top =>
    have he : (fun p : (κ → ℝ) × (ι → ℝ) => emBase W p.1 p.2) ⁻¹' Set.Iio ⊤ = Set.univ := by
      ext p
      obtain ⟨y, hy, hWy⟩ := hW p.2
      have hl : emBase W p.1 p.2 ≤ ((p.1 ⬝ᵥ y : ℝ) : EReal) := iInf₂_le y ⟨hy, hWy⟩
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_univ, iff_true]
      exact hl.trans_lt (EReal.coe_lt_top _)
    rw [he]
    exact isOpen_univ
  | coe b =>
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have he : ∃ y : κ → ℝ, 0 ≤ y ∧ W *ᵥ y = p.2 ∧ p.1 ⬝ᵥ y < b := by
      have h := hp
      change emBase W p.1 p.2 < (b : EReal) at h
      simp only [emBase, iInf_lt_iff, EReal.coe_lt_coe_iff] at h
      obtain ⟨y, hy, hc⟩ := h
      exact ⟨y, hy.1, hy.2, hc⟩
    obtain ⟨y, hy, hWy, hc⟩ := he
    have hcont : Continuous (fun ε : ℝ => p.1 ⬝ᵥ (y + ε • k)) := by
      unfold dotProduct
      fun_prop
    have hlim : Tendsto (fun ε : ℝ => p.1 ⬝ᵥ (y + ε • k)) (𝓝[>] (0 : ℝ)) (𝓝 (p.1 ⬝ᵥ y)) := by
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, p.1 ⬝ᵥ (y + ε • k) < b :=
      hlim.eventually (eventually_lt_nhds hc)
    obtain ⟨ε, hcε, hε⟩ := (hev.and self_mem_nhdsWithin).exists
    let y' := y + ε • k
    have hy' : ∀ j, 0 < y' j := by
      intro j
      exact add_pos_of_nonneg_of_pos (hy j) (mul_pos hε (hk j))
    have hWy' : W *ᵥ y' = p.2 := by
      dsimp [y']
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hWy, hWk, smul_zero, add_zero]
    let cand : ((κ → ℝ) × (ι → ℝ)) → κ → ℝ := fun s => y' + R (s.2 - p.2)
    have hcan : Continuous cand := by fun_prop
    have hcp : cand p = y' := by simp [cand]
    have hpos : ∀ᶠ s in 𝓝 p, ∀ j, 0 ≤ cand s j := by
      rw [Filter.eventually_all]
      intro j
      have hcj : Continuous (fun s => cand s j) := (continuous_apply j).comp hcan
      have he := (hcj.tendsto p).eventually (eventually_gt_nhds (by simpa [hcp] using hy' j))
      exact he.mono (fun _ h => h.le)
    have hcostc : Continuous (fun s : (κ → ℝ) × (ι → ℝ) => s.1 ⬝ᵥ cand s) := by
      unfold dotProduct
      fun_prop
    have hcost : ∀ᶠ s in 𝓝 p, s.1 ⬝ᵥ cand s < b :=
      (hcostc.tendsto p).eventually (eventually_lt_nhds (by simpa [hcp, y'] using hcε))
    filter_upwards [hpos, hcost] with s hs hsc
    have hWc : W *ᵥ cand s = s.2 := by
      dsimp [cand]
      rw [Matrix.mulVec_add, hWy', hR]
      abel
    have hl : emBase W s.1 s.2 ≤ ((s.1 ⬝ᵥ cand s : ℝ) : EReal) := iInf₂_le (cand s) ⟨hs, hWc⟩
    exact hl.trans_lt (EReal.coe_lt_coe_iff.mpr hsc)

lemma em_base_measurable (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) :
    Measurable (fun p : (κ → ℝ) × (ι → ℝ) => (emBase W p.1 p.2).toReal) :=
  (em_base_upperSemicontinuous W hW).measurable.ereal_toReal

end NumStochOpt.Bounds



set_option autoImplicit false
set_option maxHeartbeats 1000000

open Matrix MeasureTheory
open scoped BigOperators
open Classical
namespace NumStochOpt.Bounds

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma em_pos_neg (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
  · rw [max_eq_right hx, max_eq_left (by linarith)]; ring

/-- A fixed finite family of nonnegative feasible decisions controls the recourse value
uniformly, also when the cost vector varies. -/
lemma em_base_growth_bound (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) :
    ∃ D : κ → ι → ℝ, (∀ k j, 0 ≤ D k j) ∧
      ∀ (q : κ → ℝ), DualFeasible W q → ∀ z : ι → ℝ,
        |(emBase W q z).toReal| ≤ ∑ k, ∑ j, D k j * |q k * z j| := by
  choose yp hyp hWp using (fun j : ι => hW (Pi.single j 1))
  choose ym hym hWm using (fun j : ι => hW (-Pi.single j 1))
  let D : κ → ι → ℝ := fun k j => yp j k + ym j k
  have hD : ∀ k j, 0 ≤ D k j := fun k j => add_nonneg (hyp j k) (hym j k)
  let Y : (ι → ℝ) → κ → ℝ := fun z => ∑ j, ((max (z j) 0) • yp j + (max (-z j) 0) • ym j)
  have hY0 (z : ι → ℝ) : 0 ≤ Y z := by
    intro k
    dsimp [Y]
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun j _ => add_nonneg
      (mul_nonneg (le_max_right _ _) (hyp j k)) (mul_nonneg (le_max_right _ _) (hym j k))
  have hWY (z : ι → ℝ) : W *ᵥ Y z = z := by
    change (Matrix.toLin' W) (Y z) = z
    change (Matrix.toLin' W) (∑ j, ((max (z j) 0) • yp j + (max (-z j) 0) • ym j)) = z
    simp only [map_sum, map_add, map_smul, Matrix.toLin'_apply, hWp, hWm]
    ext k
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    simpa [Pi.single_apply, Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]
      using em_pos_neg (z k)
  have hYbound (z : ι → ℝ) (k : κ) : Y z k ≤ ∑ j, D k j * |z j| := by
    dsimp [Y]
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_le_sum
    intro j _
    have hp : max (z j) 0 ≤ |z j| := max_le (le_abs_self _) (abs_nonneg _)
    have hm : max (-z j) 0 ≤ |z j| := max_le (neg_le_abs _) (abs_nonneg _)
    have h1 := mul_le_mul_of_nonneg_right hp (hyp j k)
    have h2 := mul_le_mul_of_nonneg_right hm (hym j k)
    dsimp [D]
    nlinarith
  have hcost (q : κ → ℝ) (z : ι → ℝ) :
      q ⬝ᵥ Y z ≤ ∑ k, ∑ j, D k j * |q k * z j| := by
    unfold dotProduct
    apply Finset.sum_le_sum
    intro k _
    calc
      q k * Y z k ≤ |q k| * Y z k := mul_le_mul_of_nonneg_right (le_abs_self _) (hY0 z k)
      _ ≤ |q k| * (∑ j, D k j * |z j|) := mul_le_mul_of_nonneg_left (hYbound z k) (abs_nonneg _)
      _ = ∑ j, D k j * |q k * z j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul]
        ring
  refine ⟨D, hD, ?_⟩
  intro q hq z
  obtain ⟨u, hu⟩ := hq
  have hi := em_base_finite W hW q ⟨u, hu⟩ z
  have hup : emBase W q z ≤ ((∑ k, ∑ j, D k j * |q k * z j| : ℝ) : EReal) :=
    (iInf₂_le (Y z) ⟨hY0 z, hWY z⟩).trans (EReal.coe_le_coe_iff.mpr (hcost q z))
  have hlo : ((-(∑ k, ∑ j, D k j * |q k * z j|) : ℝ) : EReal) ≤ emBase W q z := by
    have h := em_weak_duality W q u hu (Y (-z)) (hY0 (-z))
    rw [hWY, dotProduct_neg] at h
    have hc := hcost q (-z)
    simp only [Pi.neg_apply, mul_neg, abs_neg] at hc
    have hl : -(∑ k, ∑ j, D k j * |q k * z j|) ≤ u ⬝ᵥ z := by linarith
    exact (EReal.coe_le_coe_iff.mpr hl).trans (em_base_lower W q u z hu)
  rw [abs_le]
  constructor
  · simpa using EReal.toReal_le_toReal hlo (EReal.coe_ne_bot _) hi.1
  · simpa using EReal.toReal_le_toReal hup hi.2 (EReal.coe_ne_top _)

end NumStochOpt.Bounds



set_option autoImplicit false
set_option maxHeartbeats 1000000

open Matrix MeasureTheory
open scoped BigOperators
open Classical
namespace NumStochOpt.Bounds

lemma em_base_convex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) (q : κ → ℝ) (hq : DualFeasible W q) :
    ConvexOn ℝ Set.univ (fun z : ι → ℝ => (emBase W q z).toReal) := by
  obtain ⟨F, hF, he⟩ := em_base_finite_max W hW q hq
  simp_rw [he, EReal.toReal_coe]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ r s hr hs _
  apply Finset.sup'_le
  intro l hl
  simp only [map_add, map_smul, smul_eq_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (Finset.le_sup' (fun l => l x) hl) hr)
    (mul_le_mul_of_nonneg_left (Finset.le_sup' (fun l => l y) hl) hs)

lemma em_variable_integrable {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] (P : Measure Ω)
    (W : Matrix ι κ ℝ) (hW : CompleteRecourse W)
    (q : Ω → κ → ℝ) (z : Ω → ι → ℝ)
    (hq2 : ∀ k, MemLp (fun ω => q ω k) 2 P) (hz2 : ∀ j, MemLp (fun ω => z ω j) 2 P)
    (hdual : ∀ ω, DualFeasible W (q ω)) :
    Integrable (fun ω => (emBase W (q ω) (z ω)).toReal) P := by
  obtain ⟨D, _, hb⟩ := em_base_growth_bound W hW
  have hm : AEStronglyMeasurable (fun ω => (emBase W (q ω) (z ω)).toReal) P := by
    have hqm : AEMeasurable q P := aemeasurable_pi_lambda _ (fun k => (hq2 k).1.aemeasurable)
    have hzm : AEMeasurable z P := aemeasurable_pi_lambda _ (fun j => (hz2 j).1.aemeasurable)
    exact ((em_base_measurable W hW).comp_aemeasurable (hqm.prodMk hzm)).aestronglyMeasurable
  have hbi : Integrable (fun ω => ∑ k, ∑ j, D k j * |q ω k * z ω j|) P := by
    apply integrable_finsetSum
    intro k _
    apply integrable_finsetSum
    intro j _
    exact ((hq2 k).integrable_mul (hz2 j)).abs.const_mul (D k j)
  refine hbi.mono' hm (Filter.Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_eq_abs]
  exact hb (q ω) (hdual ω) (z ω)

lemma em_native_expected {Ω ι κ ν : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [Fintype ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Matrix ι κ ℝ) (hW : CompleteRecourse W)
    (q : Ω → κ → ℝ) (h : Ω → ι → ℝ) (T : Ω → Matrix ι ν ℝ)
    (hq2 : ∀ k, MemLp (fun ω => q ω k) 2 P) (hh2 : ∀ i, MemLp (fun ω => h ω i) 2 P)
    (hT2 : ∀ i j, MemLp (fun ω => T ω i j) 2 P)
    (hdual : ∀ ω, DualFeasible W (q ω)) :
    (∀ (x : ν → ℝ) (ω : Ω), recourseCost W (q ω) (h ω) (T ω) x ≠ ⊤ ∧
        recourseCost W (q ω) (h ω) (T ω) x ≠ ⊥) ∧
      (∀ x : ν → ℝ, Integrable (fun ω => (recourseCost W (q ω) (h ω) (T ω) x).toReal) P) ∧
      ConvexOn ℝ Set.univ (expectedRecourse P W q h T) := by
  have hi (x : ν → ℝ) : Integrable (fun ω => (recourseCost W (q ω) (h ω) (T ω) x).toReal) P := by
    apply em_variable_integrable P W hW q (fun ω => h ω - T ω *ᵥ x) hq2
    · intro j
      exact (hh2 j).sub (memLp_finsetSum Finset.univ (fun k _ => (hT2 j k).mul_const (x k)))
    · exact hdual
  have hc (ω : Ω) : ConvexOn ℝ Set.univ
      (fun x : ν → ℝ => (recourseCost W (q ω) (h ω) (T ω) x).toReal) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ r s hr hs hrs
    have he : h ω - T ω *ᵥ (r • x + s • y) =
        r • (h ω - T ω *ᵥ x) + s • (h ω - T ω *ᵥ y) := by
      ext j
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.sub_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      have ht := congrArg (fun t : ℝ => t * h ω j) hrs
      nlinarith [ht]
    change (emBase W (q ω) (h ω - T ω *ᵥ (r • x + s • y))).toReal ≤ _
    rw [he]
    exact (em_base_convex W hW (q ω) (hdual ω)).2 (Set.mem_univ _) (Set.mem_univ _) hr hs hrs
  refine ⟨fun x ω => em_base_finite W hW (q ω) (hdual ω) _, hi, convex_univ, ?_⟩
  intro x _ y _ r s hr hs hrs
  have hle := integral_mono_ae (hi (r • x + s • y))
    (((hi x).const_mul r).add ((hi y).const_mul s))
    (Filter.Eventually.of_forall (fun ω => (hc ω).2 (Set.mem_univ x) (Set.mem_univ y) hr hs hrs))
  simp only [Pi.add_apply] at hle
  rw [integral_add ((hi x).const_mul r) ((hi y).const_mul s), integral_const_mul,
    integral_const_mul] at hle
  exact hle

end NumStochOpt.Bounds


open MeasureTheory Matrix NumStochOpt.Bounds in

/-- Property (e), p. 40: with complete recourse, `q(ω)` dual feasible for every `ω`, and random
data `ξ(ω) = (q(ω), h(ω), T(ω))` with finite second moments, the recourse cost is finite, its
expectation exists, and the expected recourse function `Q(x) = ∫ Q(x, ξ(ω)) P(dω)` is convex. -/
theorem solution {Ω ι κ ν : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [Fintype ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Matrix ι κ ℝ) (hW : CompleteRecourse W)
    (q : Ω → κ → ℝ) (h : Ω → ι → ℝ) (T : Ω → Matrix ι ν ℝ)
    (hq2 : ∀ k, MemLp (fun ω => q ω k) 2 P) (hh2 : ∀ i, MemLp (fun ω => h ω i) 2 P)
    (hT2 : ∀ i j, MemLp (fun ω => T ω i j) 2 P)
    (hdual : ∀ ω, DualFeasible W (q ω)) :
    (∀ (x : ν → ℝ) (ω : Ω), recourseCost W (q ω) (h ω) (T ω) x ≠ ⊤ ∧
        recourseCost W (q ω) (h ω) (T ω) x ≠ ⊥) ∧
      (∀ x : ν → ℝ, Integrable (fun ω => (recourseCost W (q ω) (h ω) (T ω) x).toReal) P) ∧
      ConvexOn ℝ Set.univ (expectedRecourse P W q h T) := by
  exact em_native_expected P W hW q h T hq2 hh2 hT2 hdual


#print axioms solution
