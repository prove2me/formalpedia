-- Prove2me | solution 1 for MatrixAnalytic.ProductForm.jackson_conditions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:53:51.243164+00:00
-- url     : https://prove2.me/submissions/1655931f-f822-43b0-8bb5-3a5bd32b6553

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain
import Definitions.Def_MatrixAnalytic_ProductForm_QBD
import Definitions.Def_MatrixAnalytic_ProductForm_Jackson
open MatrixAnalytic.ProductForm


section
variable {J : Type*} [Fintype J] [DecidableEq J]
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

lemma g69d2_iff_add (r s : J → ℕ) (j : J) :
    (1 ≤ r j ∧ s = r - Pi.single j 1) ↔ r = s + Pi.single j 1 := by
  constructor
  · rintro ⟨h1, rfl⟩
    funext k
    by_cases hk : k = j
    · subst hk; simp; omega
    · simp [Pi.single_apply, hk]
  · rintro rfl
    refine ⟨by simp, ?_⟩
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]

lemma g69d2_iff_sub (r s : J → ℕ) (i : J) :
    (s = r + Pi.single i 1) ↔ (1 ≤ s i ∧ r = s - Pi.single i 1) := by
  have := g69d2_iff_add s r i
  constructor
  · intro h
    have h2 := (this.mpr h)
    exact ⟨h2.1, h2.2⟩
  · rintro ⟨h1, h2⟩
    exact this.mp ⟨h1, h2⟩

lemma g69d2_iff_move (r s : J → ℕ) (i j : J) :
    (i ≠ j ∧ 1 ≤ r j ∧ s = r - Pi.single j 1 + Pi.single i 1) ↔
      (i ≠ j ∧ 1 ≤ s i ∧ r = s - Pi.single i 1 + Pi.single j 1) := by
  constructor
  · rintro ⟨hij, h1, rfl⟩
    refine ⟨hij, by simp, ?_⟩
    funext k
    by_cases hk : k = j
    · subst hk; simp [Pi.single_apply, Ne.symm hij]; omega
    · by_cases hk' : k = i
      · subst hk'; simp [Pi.single_apply, hk]
      · simp [Pi.single_apply, hk, hk']
  · rintro ⟨hij, h1, rfl⟩
    refine ⟨hij, by simp [Pi.single_apply, hij], ?_⟩
    funext k
    by_cases hk : k = i
    · subst hk; simp [Pi.single_apply, hij]; omega
    · by_cases hk' : k = j
      · subst hk'; simp [Pi.single_apply, hk]
      · simp [Pi.single_apply, hk, hk']

lemma g69d2_hs_diag (θ g : (J → ℕ) → ℝ) (s : J → ℕ) :
    HasSum (fun r => θ r * (if s = r then g r else 0)) (θ s * g s) := by
  have := hasSum_single (f := fun r => θ r * (if s = r then g r else 0)) s
    (fun b hb => by simp [Ne.symm hb])
  simpa using this

lemma g69d2_hs_down (θ : (J → ℕ) → ℝ) (s : J → ℕ) (j : J) (a : ℝ) :
    HasSum (fun r => θ r * (if 1 ≤ r j ∧ s = r - Pi.single j 1 then a else 0))
      (θ (s + Pi.single j 1) * a) := by
  have := hasSum_single
    (f := fun r => θ r * (if 1 ≤ r j ∧ s = r - Pi.single j 1 then a else 0))
    (s + Pi.single j 1)
    (fun b hb => by
      have : ¬ (1 ≤ b j ∧ s = b - Pi.single j 1) := fun h => hb ((g69d2_iff_add b s j).mp h)
      simp only [this, if_false, mul_zero])
  have h2 : (1 ≤ (s + Pi.single j 1 : J → ℕ) j ∧ s = (s + Pi.single j 1) - Pi.single j 1) :=
    (g69d2_iff_add _ s j).mpr rfl
  convert this using 1
  beta_reduce
  rw [if_pos h2]

lemma g69d2_hs_up (θ : (J → ℕ) → ℝ) (s : J → ℕ) (i : J) (a : ℝ) :
    HasSum (fun r => θ r * (if s = r + Pi.single i 1 then a else 0))
      (if 1 ≤ s i then θ (s - Pi.single i 1) * a else 0) := by
  by_cases hs : 1 ≤ s i
  · have := hasSum_single
      (f := fun r => θ r * (if s = r + Pi.single i 1 then a else 0))
      (s - Pi.single i 1)
      (fun b hb => by
        have : ¬ (s = b + Pi.single i 1) := fun h => hb ((g69d2_iff_sub b s i).mp h).2
        simp only [this, if_false, mul_zero])
    have h2 : s = (s - Pi.single i 1) + Pi.single i 1 := (g69d2_iff_sub _ s i).mpr ⟨hs, rfl⟩
    rw [if_pos hs]
    convert this using 1
    beta_reduce
    rw [if_pos h2]
  · have : (fun r => θ r * (if s = r + Pi.single i 1 then a else 0)) = fun _ => 0 := by
      funext r
      have : ¬ (s = r + Pi.single i 1) := fun h => hs ((g69d2_iff_sub r s i).mp h).1
      simp only [this, if_false, mul_zero]
    rw [this, if_neg hs]; exact hasSum_zero

lemma g69d2_hs_move (θ : (J → ℕ) → ℝ) (s : J → ℕ) (i j : J) (a : ℝ) :
    HasSum (fun r => θ r *
        (if i ≠ j ∧ 1 ≤ r j ∧ s = r - Pi.single j 1 + Pi.single i 1 then a else 0))
      (if i ≠ j ∧ 1 ≤ s i then θ (s - Pi.single i 1 + Pi.single j 1) * a else 0) := by
  by_cases hs : i ≠ j ∧ 1 ≤ s i
  · have := hasSum_single
      (f := fun r => θ r *
        (if i ≠ j ∧ 1 ≤ r j ∧ s = r - Pi.single j 1 + Pi.single i 1 then a else 0))
      (s - Pi.single i 1 + Pi.single j 1)
      (fun b hb => by
        have : ¬ (i ≠ j ∧ 1 ≤ b j ∧ s = b - Pi.single j 1 + Pi.single i 1) :=
          fun h => hb ((g69d2_iff_move b s i j).mp h).2.2
        simp only [this, if_false, mul_zero])
    have h2 := (g69d2_iff_move (s - Pi.single i 1 + Pi.single j 1) s i j).mpr ⟨hs.1, hs.2, rfl⟩
    rw [if_pos hs]
    convert this using 1
    beta_reduce
    rw [if_pos h2]
  · have : (fun r => θ r *
        (if i ≠ j ∧ 1 ≤ r j ∧ s = r - Pi.single j 1 + Pi.single i 1 then a else 0)) =
        fun _ => 0 := by
      funext r
      have : ¬ (i ≠ j ∧ 1 ≤ r j ∧ s = r - Pi.single j 1 + Pi.single i 1) := fun h =>
        hs ⟨((g69d2_iff_move r s i j).mp h).1, ((g69d2_iff_move r s i j).mp h).2.1⟩
      simp only [this, if_false, mul_zero]
    rw [this, if_neg hs]; exact hasSum_zero


lemma g69d2_hsA0 (lam μ : Option J → ℝ) (P : Option J → Option J → ℝ)
    (θ : (J → ℕ) → ℝ) (s : J → ℕ) :
    HasSum (fun r => θ r * jacksonA₀ lam μ P r s)
      (θ s * lam none + ∑ j : J, θ (s + Pi.single j 1) * (μ (some j) * P (some j) none)) := by
  have h1 := g69d2_hs_diag θ (fun _ => lam none) s
  have h2 := hasSum_sum (s := Finset.univ)
    (fun j _ => g69d2_hs_down θ s j (μ (some j) * P (some j) none))
  convert h1.add h2 using 1
  funext r
  simp only [jacksonA₀, mul_add, Finset.mul_sum]

lemma g69d2_hsA2 (μ q : Option J → ℝ) (P : Option J → Option J → ℝ)
    (θ : (J → ℕ) → ℝ) (s : J → ℕ) :
    HasSum (fun r => θ r * jacksonA₂ μ q P r s)
      (θ s * (μ none * q none) + ∑ j : J,
        (if 1 ≤ s j then θ (s - Pi.single j 1) * (μ none * P none (some j)) else 0)) := by
  have h1 := g69d2_hs_diag θ (fun _ => μ none * q none) s
  have h2 := hasSum_sum (s := Finset.univ)
    (fun j _ => g69d2_hs_up θ s j (μ none * P none (some j)))
  convert h1.add h2 using 1
  funext r
  simp only [jacksonA₂, mul_add, Finset.mul_sum]

lemma g69d2_hsA1 (lam μ q : Option J → ℝ) (P : Option J → Option J → ℝ)
    (θ : (J → ℕ) → ℝ) (s : J → ℕ) :
    HasSum (fun r => θ r * jacksonA₁ lam μ q P r s)
      ((∑ i : J, (if 1 ≤ s i then θ (s - Pi.single i 1) * lam (some i) else 0)) +
       (∑ j : J, θ (s + Pi.single j 1) * (μ (some j) * q (some j))) +
       (∑ j : J, ∑ i : J, (if i ≠ j ∧ 1 ≤ s i then
          θ (s - Pi.single i 1 + Pi.single j 1) * (μ (some j) * P (some j) (some i)) else 0)) +
       θ s * (-(lam none + μ none + ∑ i : J, lam (some i) +
          ∑ j : J, (if 1 ≤ s j then μ (some j) else 0)))) := by
  have h1 := hasSum_sum (s := Finset.univ)
    (fun i _ => g69d2_hs_up θ s i (lam (some i)))
  have h2 := hasSum_sum (s := Finset.univ)
    (fun j _ => g69d2_hs_down θ s j (μ (some j) * q (some j)))
  have h3 := hasSum_sum (s := Finset.univ) (fun j _ => hasSum_sum (s := Finset.univ)
    (fun i _ => g69d2_hs_move θ s i j (μ (some j) * P (some j) (some i))))
  have h4 := g69d2_hs_diag θ (fun r => -(lam none + μ none + ∑ i : J, lam (some i) +
          ∑ j : J, (if 1 ≤ r j then μ (some j) else 0))) s
  convert ((h1.add h2).add h3).add h4 using 1
  funext r
  simp only [jacksonA₁, mul_add, Finset.mul_sum]

lemma g69d2_hsB (lam μ q : Option J → ℝ) (P : Option J → Option J → ℝ)
    (θ : (J → ℕ) → ℝ) (s : J → ℕ) :
    HasSum (fun r => θ r * jacksonB lam μ q P r s)
      ((∑ i : J, (if 1 ≤ s i then θ (s - Pi.single i 1) * lam (some i) else 0)) +
       (∑ j : J, θ (s + Pi.single j 1) * (μ (some j) * q (some j))) +
       (∑ j : J, ∑ i : J, (if i ≠ j ∧ 1 ≤ s i then
          θ (s - Pi.single i 1 + Pi.single j 1) * (μ (some j) * P (some j) (some i)) else 0)) +
       θ s * (-(lam none + μ none + ∑ i : J, lam (some i) +
          ∑ j : J, (if 1 ≤ s j then μ (some j) else 0))) + θ s * μ none) := by
  have := (g69d2_hsA1 lam μ q P θ s).add (g69d2_hs_diag θ (fun _ => μ none) s)
  convert this using 1
  funext r
  simp only [jacksonB, mul_add]

end

open Filter Topology


lemma g69d2_geom_pi {J : Type*} [Fintype J] [DecidableEq J] (ρ : J → ℝ)
    (h0 : ∀ j, 0 ≤ ρ j) (h1 : ∀ j, ρ j < 1) :
    HasSum (fun r : J → ℕ => ∏ j, ρ j ^ r j) (∏ j, (1 - ρ j)⁻¹) := by
  set f : (J → ℕ) → ℝ := fun r => ∏ j, ρ j ^ r j with hf
  have fnn : ∀ r, 0 ≤ f r := fun r => Finset.prod_nonneg fun j _ => pow_nonneg (h0 j) _
  have hS : ∀ N : ℕ, ∑ r ∈ Fintype.piFinset (fun _ : J => Finset.range N), f r =
      ∏ j, ∑ n ∈ Finset.range N, ρ j ^ n := by
    intro N
    rw [Finset.sum_prod_piFinset]
  have hgeo := fun j => hasSum_geometric_of_lt_one (h0 j) (h1 j)
  have hle : ∀ N, ∑ r ∈ Fintype.piFinset (fun _ : J => Finset.range N), f r ≤
      ∏ j, (1 - ρ j)⁻¹ := by
    intro N
    rw [hS]
    apply Finset.prod_le_prod
    · intro j _; exact Finset.sum_nonneg fun n _ => pow_nonneg (h0 j) _
    · intro j _
      exact sum_le_hasSum _ (fun n _ => pow_nonneg (h0 j) _) (hgeo j)
  have hmono : Monotone (fun N : ℕ => Fintype.piFinset (fun _ : J => Finset.range N)) := by
    intro a b hab
    apply Fintype.piFinset_subset
    intro j
    exact Finset.range_subset_range.mpr hab
  have hcov : ∀ r : J → ℕ, ∃ N, r ∈ Fintype.piFinset (fun _ : J => Finset.range N) := by
    intro r
    refine ⟨∑ j, r j + 1, ?_⟩
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range]
    have := Finset.single_le_sum (f := r) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  have htend := tendsto_atTop_finset_of_monotone hmono hcov
  have hsum : Summable f := by
    apply summable_of_sum_le fnn (c := ∏ j, (1 - ρ j)⁻¹)
    intro u
    obtain ⟨N, hN⟩ : ∃ N, u ⊆ Fintype.piFinset (fun _ : J => Finset.range N) := by
      have := (htend.eventually (Filter.eventually_ge_atTop u))
      obtain ⟨N, hN⟩ := this.exists
      exact ⟨N, hN⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hN (fun r _ _ => fnn r)).trans (hle N)
  have h2 : Tendsto (fun N : ℕ => ∑ r ∈ Fintype.piFinset (fun _ : J => Finset.range N), f r)
      atTop (𝓝 (∏ j, (1 - ρ j)⁻¹)) := by
    simp_rw [hS]
    exact tendsto_finsetProd _ (fun j _ => (hgeo j).tendsto_sum_nat)
  have h3 := hsum.hasSum.comp htend
  have := tendsto_nhds_unique h3 h2
  rw [← this]
  exact hsum.hasSum

section
variable {J : Type*} [Fintype J] [DecidableEq J]

lemma g69d2_theta_add (c : ℝ) (ρ : J → ℝ) (r : J → ℕ) (j : J) :
    c * ∏ k, ρ k ^ ((r + Pi.single j 1 : J → ℕ) k) = (c * ∏ k, ρ k ^ r k) * ρ j := by
  rw [mul_assoc]; congr 1
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  congr 1
  have : ∀ k, ρ k ^ (Pi.single j 1 : J → ℕ) k = if k = j then ρ k else 1 := by
    intro k; by_cases h : k = j
    · subst h; simp
    · simp [h]
  simp only [this, Finset.prod_ite_eq', Finset.mem_univ, if_true]

lemma g69d2_jackson_alg
    (lam μ q y : Option J → ℝ) (P : Matrix (Option J) (Option J) ℝ)
    (hμ : ∀ i, 0 < μ i) (hPii : ∀ i, P i i = 0)
    (hrow : ∀ i, ∑ j, P i j + q i = 1)
    (htraffic : y = lam + Matrix.vecMul y P)
    (hload : ∀ i, y i / μ i < 1) (hy : ∀ i, 0 < y i) :
    let η : ℝ := y none / μ none
    let c : ℝ := ∏ j : J, (1 - y (some j) / μ (some j))
    let θ : (J → ℕ) → ℝ := fun r => c * ∏ j : J, (y (some j) / μ (some j)) ^ r j
    (∀ r, 0 < θ r) ∧ HasSum θ 1 ∧ 0 < η ∧ η < 1 ∧
      (∀ s, HasSum (fun r => θ r * (jacksonA₀ lam μ P r s + η * jacksonA₁ lam μ q P r s +
        η ^ 2 * jacksonA₂ μ q P r s)) 0) ∧
      (∀ s, HasSum (fun r => θ r * (jacksonB lam μ q P r s + η * jacksonA₂ μ q P r s)) 0) := by
  intro η c θ
  set ρ : J → ℝ := fun j => y (some j) / μ (some j) with hρ
  have hρpos : ∀ j, 0 < ρ j := fun j => div_pos (hy _) (hμ _)
  have hρlt : ∀ j, ρ j < 1 := fun j => hload (some j)
  have hρμ : ∀ j, ρ j * μ (some j) = y (some j) := fun j => by
    simp only [hρ]; field_simp [(hμ (some j)).ne']
  have hc : 0 < c := Finset.prod_pos fun j _ => by
    have := hρlt j; simp only [hρ] at this; linarith
  have hθdef : θ = fun r => c * ∏ j, ρ j ^ r j := rfl
  have hθpos : ∀ r, 0 < θ r := fun r =>
    mul_pos hc (Finset.prod_pos fun j _ => pow_pos (hρpos j) _)
  have hθadd : ∀ r j, θ (r + Pi.single j 1) = θ r * ρ j := fun r j => by
    rw [hθdef]; exact g69d2_theta_add c ρ r j
  have hθsub : ∀ s i, 1 ≤ s i → θ (s - Pi.single i 1) = θ s / ρ i := by
    intro s i hs
    have h1 : s - Pi.single i 1 + Pi.single i 1 = s :=
      ((g69d2_iff_sub (s - Pi.single i 1) s i).mpr ⟨hs, rfl⟩).symm
    have := hθadd (s - Pi.single i 1) i
    rw [h1] at this
    rw [this]; field_simp [(hρpos i).ne']
  have hθmove : ∀ s i j, 1 ≤ s i → θ (s - Pi.single i 1 + Pi.single j 1) = θ s / ρ i * ρ j := by
    intro s i j hs; rw [hθadd, hθsub s i hs]
  have hη : η * μ none = y none := by simp only [η]; field_simp [(hμ none).ne']
  -- traffic equations
  have htr : ∀ k, y k = lam k + ∑ l, y l * P l k := by
    intro k
    have := congrFun htraffic k
    simpa [Matrix.vecMul, dotProduct] using this
  have htr' : ∀ k, y k = lam k + y none * P none k + ∑ j : J, y (some j) * P (some j) k := by
    intro k; rw [htr k, Fintype.sum_option, add_assoc]
  -- F2
  have F2 : lam none + ∑ j : J, y (some j) * P (some j) none - y none = 0 := by
    have := htr' none; rw [hPii] at this; linarith
  -- F3
  have F3 : ∑ j : J, y (some j) * q (some j) + y none * q none - lam none -
      ∑ j : J, lam (some j) = 0 := by
    have hq : ∀ k, q k = 1 - ∑ l, P k l := fun k => by linarith [hrow k]
    have h1 : ∑ k, y k * q k = ∑ k, lam k := by
      simp only [hq, mul_sub, mul_one, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ l, ∑ k, y k * P k l = y l - lam l := fun l => by linarith [htr l]
      simp only [this, Finset.sum_sub_distrib]; ring
    rw [Fintype.sum_option, Fintype.sum_option] at h1
    linarith
  -- F1
  have F1 : ∀ s : J → ℕ, (∑ i : J, if 1 ≤ s i then lam (some i) / ρ i else 0) +
      (∑ i : J, if 1 ≤ s i then (∑ j : J, y (some j) * P (some j) (some i)) / ρ i else 0) +
      η * (∑ i : J, if 1 ≤ s i then μ none * P none (some i) / ρ i else 0) -
      (∑ i : J, if 1 ≤ s i then μ (some i) else 0) = 0 := by
    intro s
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with h
    · have key : lam (some i) + (∑ j : J, y (some j) * P (some j) (some i)) +
          η * (μ none * P none (some i)) = ρ i * μ (some i) := by
        rw [hρμ]; linear_combination (htr' (some i)).symm + P none (some i) * hη
      have : lam (some i) / ρ i + (∑ j : J, y (some j) * P (some j) (some i)) / ρ i +
          η * (μ none * P none (some i) / ρ i) = (lam (some i) +
          (∑ j : J, y (some j) * P (some j) (some i)) + η * (μ none * P none (some i))) / ρ i := by
        ring
      rw [this, key]; field_simp [(hρpos i).ne']; ring
    · simp
  refine ⟨hθpos, ?_, div_pos (hy none) (hμ none), hload none, ?_, ?_⟩
  · have hg := (g69d2_geom_pi ρ (fun j => (hρpos j).le) hρlt).mul_left c
    have h1 : c * ∏ j, (1 - ρ j)⁻¹ = 1 := by
      show (∏ j, (1 - ρ j)) * ∏ j, (1 - ρ j)⁻¹ = 1
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro j _
      have : 1 - ρ j ≠ 0 := by linarith [hρlt j]
      field_simp
    rw [h1] at hg
    exact hg
  all_goals intro s
  all_goals
    have E0 : ∑ j : J, θ (s + Pi.single j 1) * (μ (some j) * P (some j) none) =
        θ s * ∑ j : J, y (some j) * P (some j) none := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
      rw [hθadd, ← hρμ]; ring
    have Eq : ∑ j : J, θ (s + Pi.single j 1) * (μ (some j) * q (some j)) =
        θ s * ∑ j : J, y (some j) * q (some j) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
      rw [hθadd, ← hρμ]; ring
    have E1 : (∑ i : J, if 1 ≤ s i then θ (s - Pi.single i 1) * lam (some i) else 0) =
        θ s * ∑ i : J, if 1 ≤ s i then lam (some i) / ρ i else 0 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
      split_ifs with h
      · rw [hθsub s i h]; ring
      · simp
    have E5 : (∑ i : J, if 1 ≤ s i then θ (s - Pi.single i 1) * (μ none * P none (some i))
        else 0) = θ s * ∑ i : J, if 1 ≤ s i then μ none * P none (some i) / ρ i else 0 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
      split_ifs with h
      · rw [hθsub s i h]; ring
      · simp
    have E3 : (∑ j : J, ∑ i : J, if i ≠ j ∧ 1 ≤ s i then
          θ (s - Pi.single i 1 + Pi.single j 1) * (μ (some j) * P (some j) (some i)) else 0) =
        θ s * ∑ i : J, if 1 ≤ s i then (∑ j : J, y (some j) * P (some j) (some i)) / ρ i
          else 0 := by
      rw [Finset.sum_comm, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
      split_ifs with h
      · rw [Finset.sum_div, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
        by_cases hij : i = j
        · subst hij; simp [hPii]
        · rw [if_pos ⟨hij, h⟩, hθmove s i j h, ← hρμ]; field_simp [(hρpos i).ne']
      · rw [mul_zero]; apply Finset.sum_eq_zero; intro j _
        rw [if_neg (fun hh => h hh.2)]
  · have h := ((g69d2_hsA0 lam μ P θ s).add ((g69d2_hsA1 lam μ q P θ s).mul_left η)).add
      ((g69d2_hsA2 μ q P θ s).mul_left (η ^ 2))
    convert h using 1
    · funext r; ring
    · rw [E0, E1, Eq, E3, E5]
      linear_combination -θ s * (F2 + η * F1 s + η * F3 - (1 - η * q none) * hη)
  · have h := (g69d2_hsB lam μ q P θ s).add ((g69d2_hsA2 μ q P θ s).mul_left η)
    convert h using 1
    · funext r; ring
    · rw [E1, Eq, E3, E5]
      linear_combination -θ s * (F1 s + F3 + q none * hη)


lemma g69d2_Zfacts (lam q y : Option J → ℝ) (P : Matrix (Option J) (Option J) ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hP : ∀ i j, 0 ≤ P i j) (hq : ∀ i, 0 ≤ q i)
    (hrow : ∀ i, ∑ j, P i j + q i = 1)
    (htr : ∀ k, y k = lam k + ∑ l, y l * P l k) :
    ∀ k, y k ≤ 0 → lam k = 0 ∧ ∀ l, 0 < y l → P l k = 0 := by
  classical
  set Z := Finset.univ.filter (fun k => y k ≤ 0) with hZ
  have hsum : ∑ k ∈ Z, y k = ∑ k ∈ Z, lam k + ∑ l, y l * ∑ k ∈ Z, P l k := by
    rw [Finset.sum_congr rfl (fun k _ => htr k), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l => y l ≤ 0)] at hsum
  rw [← hZ] at hsum
  have hle1 : ∀ l, ∑ k ∈ Z, P l k ≤ 1 := by
    intro l
    have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Z)
      (fun k _ _ => hP l k)
    linarith [hrow l, hq l]
  have hA : ∑ l ∈ Z, y l ≤ ∑ l ∈ Z, y l * ∑ k ∈ Z, P l k := by
    apply Finset.sum_le_sum
    intro l hl
    have hyl : y l ≤ 0 := (Finset.mem_filter.mp hl).2
    nlinarith [hle1 l, Finset.sum_nonneg (fun k (_ : k ∈ Z) => hP l k)]
  have hB : 0 ≤ ∑ k ∈ Z, lam k := Finset.sum_nonneg fun k _ => hlam k
  have hCnn : ∀ l ∈ Finset.univ.filter (fun l => ¬ y l ≤ 0), 0 ≤ y l * ∑ k ∈ Z, P l k :=
    fun l hl => mul_nonneg (le_of_lt (not_le.mp (Finset.mem_filter.mp hl).2))
      (Finset.sum_nonneg fun k _ => hP l k)
  have hC : 0 ≤ ∑ l ∈ Finset.univ.filter (fun l => ¬ y l ≤ 0), y l * ∑ k ∈ Z, P l k :=
    Finset.sum_nonneg hCnn
  have hB0 : ∑ k ∈ Z, lam k = 0 := by linarith
  have hC0 : ∑ l ∈ Finset.univ.filter (fun l => ¬ y l ≤ 0), y l * ∑ k ∈ Z, P l k = 0 := by
    linarith
  intro k hk
  have hkZ : k ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
  refine ⟨(Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hlam k)).mp hB0 k hkZ, ?_⟩
  intro l hl
  have hlZ : l ∈ Finset.univ.filter (fun l => ¬ y l ≤ 0) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_le.mpr hl⟩
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hCnn).mp hC0 l hlZ
  have h2 : ∑ k ∈ Z, P l k = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hl.ne'
    · exact h
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hP l k)).mp h2 k hkZ

section blocks
variable (lam μ q y : Option J → ℝ) (P : Matrix (Option J) (Option J) ℝ)
  (hZ : ∀ k, y k ≤ 0 → lam k = 0 ∧ ∀ l, 0 < y l → P l k = 0)
include hZ

lemma g69d2_A1zero (r s : J → ℕ) (hr : ∀ j, y (some j) ≤ 0 → r j = 0) (k : J)
    (hk : y (some k) ≤ 0) (hs : s k ≠ 0) : jacksonA₁ lam μ q P r s = 0 := by
  have hrk := hr k hk
  unfold jacksonA₁
  have p1 : (∑ i : J, (if s = r + Pi.single i 1 then lam (some i) else 0)) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    split_ifs with h
    · have := congrFun h k
      by_cases hik : i = k
      · subst hik; exact (hZ _ hk).1
      · simp [Pi.single_apply, Ne.symm hik, hrk] at this; exact absurd this hs
    · rfl
  have p2 : (∑ j : J, (if 1 ≤ r j ∧ s = r - Pi.single j 1 then μ (some j) * q (some j)
      else 0)) = 0 := by
    apply Finset.sum_eq_zero; intro j _
    split_ifs with h
    · have := congrFun h.2 k
      simp [hrk] at this; exact absurd this hs
    · rfl
  have p3 : (∑ j : J, ∑ i : J,
      (if i ≠ j ∧ 1 ≤ r j ∧ s = r - Pi.single j 1 + Pi.single i 1
        then μ (some j) * P (some j) (some i) else 0)) = 0 := by
    apply Finset.sum_eq_zero; intro j _
    apply Finset.sum_eq_zero; intro i _
    split_ifs with h
    · have := congrFun h.2.2 k
      by_cases hik : i = k
      · subst hik
        have hj : 0 < y (some j) := by
          by_contra hc
          have := hr j (not_lt.mp hc); omega
        rw [(hZ _ hk).2 _ hj, mul_zero]
      · simp [Pi.single_apply, Ne.symm hik, hrk] at this; exact absurd this hs
    · rfl
  have p4 : (if s = r then
      -(lam none + μ none + ∑ i : J, lam (some i) +
          ∑ j : J, (if 1 ≤ r j then μ (some j) else 0))
      else 0) = 0 := by
    split_ifs with h
    · subst h; exact absurd hrk hs
    · rfl
  rw [p1, p2, p3, p4]; ring

lemma g69d2_A0zero (r s : J → ℕ) (hr : ∀ j, y (some j) ≤ 0 → r j = 0) (k : J)
    (hk : y (some k) ≤ 0) (hs : s k ≠ 0) : jacksonA₀ lam μ P r s = 0 := by
  have hrk := hr k hk
  unfold jacksonA₀
  rw [if_neg (fun h => by subst h; exact hs hrk)]
  rw [zero_add]
  apply Finset.sum_eq_zero; intro j _
  split_ifs with h
  · have := congrFun h.2 k
    simp [hrk] at this; exact absurd this hs
  · rfl

lemma g69d2_A0zero' (r s : J → ℕ) (hr : ∀ j, y (some j) ≤ 0 → r j = 0)
    (h0 : y none ≤ 0) : jacksonA₀ lam μ P r s = 0 := by
  unfold jacksonA₀
  rw [(hZ none h0).1]
  simp only [ite_self, zero_add]
  apply Finset.sum_eq_zero; intro j _
  split_ifs with h
  · have hj : 0 < y (some j) := by
      by_contra hc
      have := hr j (not_lt.mp hc); omega
    rw [(hZ none h0).2 _ hj, mul_zero]
  · rfl

lemma g69d2_A2zero (r s : J → ℕ) (hr : ∀ j, y (some j) ≤ 0 → r j = 0) (k : J)
    (hk : y (some k) ≤ 0) (hs : s k ≠ 0) (h0 : 0 < y none) : jacksonA₂ μ q P r s = 0 := by
  have hrk := hr k hk
  unfold jacksonA₂
  rw [if_neg (fun h => by subst h; exact hs hrk), zero_add]
  apply Finset.sum_eq_zero; intro i _
  split_ifs with h
  · have := congrFun h k
    by_cases hik : i = k
    · subst hik; rw [(hZ _ hk).2 _ h0, mul_zero]
    · simp [Pi.single_apply, Ne.symm hik, hrk] at this; exact absurd this hs
  · rfl

lemma g69d2_Qzero (w z : ℕ × (J → ℕ))
    (hw : (y none ≤ 0 → w.1 = 0) ∧ ∀ j, y (some j) ≤ 0 → w.2 j = 0)
    (hz : ¬ ((y none ≤ 0 → z.1 = 0) ∧ ∀ j, y (some j) ≤ 0 → z.2 j = 0)) :
    qbdQ (jacksonB lam μ q P) (jacksonA₀ lam μ P) (jacksonA₁ lam μ q P) (jacksonA₂ μ q P)
      w z = 0 := by
  obtain ⟨n, r⟩ := w
  obtain ⟨n', s⟩ := z
  obtain ⟨hw1, hr⟩ := hw
  simp only at hw1 hr hz
  have hz' : (y none ≤ 0 ∧ n' ≠ 0) ∨ ∃ k, y (some k) ≤ 0 ∧ s k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hz ⟨hc.1, hc.2⟩
  unfold qbdQ
  simp only
  split_ifs with h1 h2 h3 h4 h5 h6
  · -- B
    rcases hz' with ⟨_, h⟩ | ⟨k, hk, hs⟩
    · exact absurd h2 h
    · unfold jacksonB
      rw [g69d2_A1zero lam μ q y P hZ r s hr k hk hs,
        if_neg (fun h => by subst h; exact hs (hr k hk))]; ring
  · by_cases h0 : y none ≤ 0
    · exact g69d2_A0zero' (lam := lam) (μ := μ) (y := y) (P := P) hZ r s hr h0
    · rcases hz' with ⟨h, _⟩ | ⟨k, hk, hs⟩
      · exact absurd h h0
      · exact g69d2_A0zero (lam := lam) (μ := μ) (y := y) (P := P) hZ r s hr k hk hs
  · rfl
  all_goals
    have h0 : 0 < y none := by
      by_contra hc; exact h1 (hw1 (not_lt.mp hc))
    obtain ⟨k, hk, hs⟩ : ∃ k, y (some k) ≤ 0 ∧ s k ≠ 0 := by
      rcases hz' with ⟨h, _⟩ | h
      · exact absurd h (not_le.mpr h0)
      · exact h
  · exact g69d2_A0zero (lam := lam) (μ := μ) (y := y) (P := P) hZ r s hr k hk hs
  · exact g69d2_A1zero lam μ q y P hZ r s hr k hk hs
  · exact g69d2_A2zero lam μ q y P hZ r s hr k hk hs h0
  · rfl

end blocks

end



/-- Theorem 15.2.1 (pp. 300–301). For the Jackson network of §15.2 written as a QBD (level
`n₁`, phase `r = (n₂, …, n_K)`, blocks (15.7)ff., `B = A₁ + μ₁I`), irreducible, with routing
matrix `P` (`P_ii = 0`, the network open) and `y` the solution of the traffic equations
`y = λ + yP` (15.14): if `y_i/μ_i < 1` for every node `i`, then `η = y₁/μ₁` (15.15) and
`θ_r = c ∏_{2 ≤ j ≤ K} (y_j/μ_j)^{n_j}` (15.16), `c = ∏_{2 ≤ j ≤ K} (1 − y_j/μ_j)`, satisfy the
conditions of Theorem 15.1.3: `θ > 0`, `θ1 = 1`, `0 < η < 1`, `θ(A₀ + ηA₁ + η²A₂) = 0` and
`θ(B + ηA₂) = 0`. Node `1` is `none`, nodes `2, …, K` are `some j`, `j : J`. -/
theorem solution {J : Type*} [Fintype J] [DecidableEq J]
    (lam μ q y : Option J → ℝ) (P : Matrix (Option J) (Option J) ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hμ : ∀ i, 0 < μ i)
    (hP : ∀ i j, 0 ≤ P i j) (hPii : ∀ i, P i i = 0)
    (hq : ∀ i, 0 ≤ q i) (hrow : ∀ i, ∑ j, P i j + q i = 1)
    (hopen : IsUnit (1 - P))
    (hirr : IrreducibleCT (qbdQ (jacksonB lam μ q P) (jacksonA₀ lam μ P)
      (jacksonA₁ lam μ q P) (jacksonA₂ μ q P)))
    (htraffic : y = lam + Matrix.vecMul y P)
    (hload : ∀ i, y i / μ i < 1) :
    let η : ℝ := y none / μ none
    let c : ℝ := ∏ j : J, (1 - y (some j) / μ (some j))
    let θ : (J → ℕ) → ℝ := fun r => c * ∏ j : J, (y (some j) / μ (some j)) ^ r j
    (∀ r, 0 < θ r) ∧ HasSum θ 1 ∧ 0 < η ∧ η < 1 ∧
      (∀ s, HasSum (fun r => θ r * (jacksonA₀ lam μ P r s + η * jacksonA₁ lam μ q P r s +
        η ^ 2 * jacksonA₂ μ q P r s)) 0) ∧
      (∀ s, HasSum (fun r => θ r * (jacksonB lam μ q P r s + η * jacksonA₂ μ q P r s)) 0) := by
  have htr : ∀ k, y k = lam k + ∑ l, y l * P l k := by
    intro k
    have := congrFun htraffic k
    simpa [Matrix.vecMul, dotProduct] using this
  have hZ := g69d2_Zfacts lam q y P hlam hP hq hrow htr
  have hy : ∀ k, 0 < y k := by
    by_contra hc
    push_neg at hc
    obtain ⟨k0, hk0⟩ := hc
    let inS : ℕ × (J → ℕ) → Prop := fun x =>
      (y none ≤ 0 → x.1 = 0) ∧ ∀ j, y (some j) ≤ 0 → x.2 j = 0
    have hx0 : inS (0, 0) := ⟨fun _ => rfl, fun _ _ => rfl⟩
    have hstep : ∀ t : ℕ, ∀ z, ¬ inS z → stepPow (jumpP (qbdQ (jacksonB lam μ q P)
        (jacksonA₀ lam μ P) (jacksonA₁ lam μ q P) (jacksonA₂ μ q P))) t (0, 0) z = 0 := by
      intro t
      induction t with
      | zero =>
        intro z hz
        have hne : z ≠ (0, 0) := fun h => hz (h ▸ hx0)
        simp [stepPow, hne]
      | succ t ih =>
        intro z hz
        show ∑' w, _ = 0
        have : ∀ w, stepPow (jumpP (qbdQ (jacksonB lam μ q P)
            (jacksonA₀ lam μ P) (jacksonA₁ lam μ q P) (jacksonA₂ μ q P))) t (0, 0) w *
            jumpP (qbdQ (jacksonB lam μ q P)
            (jacksonA₀ lam μ P) (jacksonA₁ lam μ q P) (jacksonA₂ μ q P)) w z = 0 := by
          intro w
          by_cases hw : inS w
          · have hQ := g69d2_Qzero lam μ q y P hZ w z hw hz
            unfold jumpP
            split_ifs
            · rw [mul_zero]
            · rw [hQ, zero_div, mul_zero]
          · rw [ih w hw, zero_mul]
        simp only [this, tsum_zero]
    obtain ⟨z, hz⟩ : ∃ z, ¬ inS z := by
      cases k0 with
      | none => exact ⟨(1, 0), fun h => absurd (h.1 hk0) one_ne_zero⟩
      | some j => exact ⟨(0, Pi.single j 1), fun h => by
          have := h.2 j hk0; simp at this⟩
    obtain ⟨t, ht⟩ := hirr (0, 0) z
    rw [hstep t z hz] at ht
    exact lt_irrefl _ ht
  exact g69d2_jackson_alg lam μ q y P hμ hPii hrow htraffic hload hy


