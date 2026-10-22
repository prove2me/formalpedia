-- Prove2me | solution 1 for ModernConvex.Truss.infeasibility_certificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:27:01.274269+00:00
-- url     : https://prove2.me/submissions/c3a6c3f1-1b68-4473-9b93-ba739611e718

import Mathlib
import Definitions.Def_ModernConvex_Truss_Compliance

open Matrix

theorem g69a1_sq_sum_lt {ι : Type} [Fintype ι] (d : ι → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hd : ∀ i, |d i| < ε / (Fintype.card ι + 1)) : Real.sqrt (∑ i, d i ^ 2) < ε := by
  set δ := ε / (Fintype.card ι + 1) with hδ
  have hc : (0 : ℝ) < Fintype.card ι + 1 := by positivity
  have hδpos : 0 < δ := div_pos hε hc
  have h1 : ∑ i, d i ^ 2 ≤ Fintype.card ι * δ ^ 2 := by
    have : ∑ i, d i ^ 2 ≤ ∑ _i : ι, δ ^ 2 := Finset.sum_le_sum fun i _ => by
      have := hd i
      have h0 := abs_nonneg (d i)
      rw [← sq_abs]; nlinarith
    simpa using this
  rw [Real.sqrt_lt' hε]
  have hεδ : ε = δ * (Fintype.card ι + 1) := by rw [hδ]; field_simp
  rw [hεδ]
  have : (0:ℝ) ≤ Fintype.card ι := by positivity
  nlinarith [sq_nonneg δ, mul_pos hδpos hδpos]

theorem g69a1_abs_le_sqrt {ι : Type} [Fintype ι] (d : ι → ℝ) (i : ι) :
    |d i| ≤ Real.sqrt (∑ j, d j ^ 2) :=
  Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => d j ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i))

theorem g69a1_almost {ι κ : Type} [Fintype ι] [Fintype κ] (K : Set (ι → ℝ))
    (hK0 : K.Nonempty) (hadd : ∀ a ∈ K, ∀ a' ∈ K, a + a' ∈ K)
    (hsm : ∀ a ∈ K, ∀ s : ℝ, 0 ≤ s → s • a ∈ K) (A : Matrix ι κ ℝ) (b : ι → ℝ)
    (hno : ¬ ∃ l : ι → ℝ, (∀ a ∈ K, 0 ≤ l ⬝ᵥ a) ∧ Aᵀ *ᵥ l = 0 ∧ 0 < l ⬝ᵥ b) :
    ∀ ε : ℝ, 0 < ε → ∃ b' : ι → ℝ, Real.sqrt (∑ i, (b' i - b i) ^ 2) < ε ∧
      ∃ x : κ → ℝ, A *ᵥ x - b' ∈ K := by
  classical
  have h0K : (0 : ι → ℝ) ∈ K := by
    obtain ⟨a, ha⟩ := hK0; simpa using hsm a ha 0 le_rfl
  set M : Set (ι → ℝ) := {z | ∃ x : κ → ℝ, ∃ y ∈ K, z = A *ᵥ x - y} with hM
  have hMconv : Convex ℝ M := by
    rintro _ ⟨x, y, hy, rfl⟩ _ ⟨x', y', hy', rfl⟩ α β hα hβ _
    refine ⟨α • x + β • x', α • y + β • y', hadd _ (hsm _ hy _ hα) _ (hsm _ hy' _ hβ), ?_⟩
    simp only [mulVec_add, mulVec_smul, smul_sub]
    abel
  have hb : b ∈ closure M := by
    by_contra hbM
    obtain ⟨f, u, hfb, hfM⟩ :=
      geometric_hahn_banach_point_closed hMconv.closure isClosed_closure hbM
    have hfM' : ∀ z ∈ M, u < f z := fun z hz => hfM z (subset_closure hz)
    have hu : u < 0 := by
      have := hfM' 0 ⟨0, 0, h0K, by simp⟩
      simpa using this
    have hcone : ∀ z ∈ M, ∀ s : ℝ, 0 ≤ s → s • z ∈ M := by
      rintro _ ⟨x, y, hy, rfl⟩ s hs
      exact ⟨s • x, s • y, hsm y hy s hs, by rw [smul_sub, mulVec_smul]⟩
    have hfnn : ∀ z ∈ M, 0 ≤ f z := by
      intro z hz
      by_contra hneg
      push Not at hneg
      have hmem := hcone z hz (u / f z) (div_nonneg_of_nonpos hu.le hneg.le)
      have := hfM' _ hmem
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
      exact lt_irrefl _ this
    let l : ι → ℝ := fun j => - f (Pi.single j 1)
    have hfx : ∀ z : ι → ℝ, f z = - (l ⬝ᵥ z) := by
      intro z
      conv_lhs => rw [show z = ∑ j, z j • Pi.single j (1:ℝ) by
        ext k; simp [Finset.sum_apply, Pi.single_apply]]
      simp [map_sum, dotProduct, l, mul_comm]
    apply hno
    refine ⟨l, ?_, ?_, ?_⟩
    · intro a ha
      have := hfnn (-a) ⟨0, a, ha, by simp⟩
      rw [hfx, dotProduct_neg] at this
      linarith
    · have hAx : ∀ x : κ → ℝ, l ⬝ᵥ (A *ᵥ x) = 0 := by
        intro x
        have h1 := hfnn (A *ᵥ x) ⟨x, 0, h0K, by simp⟩
        have h2 := hfnn (A *ᵥ (-x)) ⟨-x, 0, h0K, by simp⟩
        rw [hfx] at h1 h2
        rw [mulVec_neg, dotProduct_neg] at h2
        linarith
      have := hAx (Aᵀ *ᵥ l)
      rw [dotProduct_mulVec, ← mulVec_transpose] at this
      exact dotProduct_self_eq_zero.mp this
    · rw [hfx] at hfb; linarith
  intro ε hε
  have hδ : 0 < ε / (Fintype.card ι + 1) := by positivity
  obtain ⟨z, hzM, hz⟩ := Metric.mem_closure_iff.mp hb _ hδ
  obtain ⟨x, y, hy, rfl⟩ := hzM
  refine ⟨A *ᵥ x - y, ?_, x, by simpa using hy⟩
  apply g69a1_sq_sum_lt _ ε hε
  intro i
  rw [dist_comm, dist_pi_lt_iff hδ] at hz
  have := hz i
  rwa [Real.dist_eq] at this

theorem g69a1_not_almost {ι κ : Type} [Fintype ι] [Fintype κ] (K : Set (ι → ℝ))
    (A : Matrix ι κ ℝ) (b : ι → ℝ) (l : ι → ℝ) (hl : ∀ a ∈ K, 0 ≤ l ⬝ᵥ a)
    (hAl : Aᵀ *ᵥ l = 0) (hlb : 0 < l ⬝ᵥ b) :
    ¬ ∀ ε : ℝ, 0 < ε → ∃ b' : ι → ℝ, Real.sqrt (∑ i, (b' i - b i) ^ 2) < ε ∧
      ∃ x : κ → ℝ, A *ᵥ x - b' ∈ K := by
  intro h
  set L : ℝ := ∑ i, |l i| + 1 with hL
  have hL0 : 0 < L := by positivity
  obtain ⟨b', hb', x, hx⟩ := h (l ⬝ᵥ b / L) (div_pos hlb hL0)
  have h1 := hl _ hx
  rw [dotProduct_sub, dotProduct_mulVec, ← mulVec_transpose, hAl, zero_dotProduct] at h1
  set S := Real.sqrt (∑ i, (b' i - b i) ^ 2)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have h2 : |l ⬝ᵥ (b' - b)| ≤ (∑ i, |l i|) * S := by
    unfold dotProduct
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (g69a1_abs_le_sqrt (b' - b) i) (abs_nonneg _)
  have h3 : (∑ i, |l i|) * S ≤ L * S := by
    apply mul_le_mul_of_nonneg_right _ hS0; linarith
  have h4 : L * S < l ⬝ᵥ b := by
    rw [lt_div_iff₀ hL0] at hb'; linarith
  rw [dotProduct_sub] at h2
  have := neg_abs_le (l ⬝ᵥ b' - l ⬝ᵥ b)
  linarith

open ModernConvex.Truss

theorem solution {m n : ℕ} (K : Set (Fin m → ℝ)) (hK : IsGoodCone K)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : AssumptionA A) (b : Fin m → ℝ) :
    -- (i)
    ((∃ l : Fin m → ℝ, l ∈ dualCone K ∧ Aᵀ *ᵥ l = 0 ∧ 0 < l ⬝ᵥ b) →
      ¬ ∃ x : Fin n → ℝ, A *ᵥ x - b ∈ K) ∧
    -- (ii)
    ((¬ ∃ l : Fin m → ℝ, l ∈ dualCone K ∧ Aᵀ *ᵥ l = 0 ∧ 0 < l ⬝ᵥ b) →
      IsAlmostSolvable K A b) ∧
    -- (iii)
    ((∃ l : Fin m → ℝ, l ∈ dualCone K ∧ Aᵀ *ᵥ l = 0 ∧ 0 < l ⬝ᵥ b) ↔
      ¬ IsAlmostSolvable K A b) := by
  obtain ⟨⟨hK0, hadd, hsm⟩, -, -, -⟩ := hK
  have hii : (¬ ∃ l : Fin m → ℝ, l ∈ dualCone K ∧ Aᵀ *ᵥ l = 0 ∧ 0 < l ⬝ᵥ b) →
      ∀ ε : ℝ, 0 < ε → ∃ b' : Fin m → ℝ, Real.sqrt (∑ i, (b' i - b i) ^ 2) < ε ∧
        ∃ x : Fin n → ℝ, A *ᵥ x - b' ∈ K :=
    fun hno => g69a1_almost K hK0 hadd hsm A b hno
  have hiii : (∃ l : Fin m → ℝ, l ∈ dualCone K ∧ Aᵀ *ᵥ l = 0 ∧ 0 < l ⬝ᵥ b) →
      ¬ ∀ ε : ℝ, 0 < ε → ∃ b' : Fin m → ℝ, Real.sqrt (∑ i, (b' i - b i) ^ 2) < ε ∧
        ∃ x : Fin n → ℝ, A *ᵥ x - b' ∈ K :=
    fun ⟨l, hl, hAl, hlb⟩ => g69a1_not_almost K A b l hl hAl hlb
  refine ⟨?_, hii, ⟨hiii, fun h => ?_⟩⟩
  · intro hl ⟨x, hx⟩
    apply hiii hl
    intro ε hε
    exact ⟨b, by simpa using hε, x, hx⟩
  · by_contra hn
    exact h (hii hn)
