-- Prove2me | solution 1 for NestedLogitAssort.DeltaGrid.grid_scaled_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T00:41:48.791536+00:00
-- url     : https://prove2.me/submissions/62307929-f499-4ae1-b870-3c17a5a403ca

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_Feas3
import Definitions.Def_NestedLogitAssort_DeltaGrid_IsOpt4
import Definitions.Def_NestedLogitAssort_DeltaGrid_IsApprox15
import Definitions.Def_NestedLogitAssort_DeltaGrid_CandGrid

set_option autoImplicit false

namespace NLDGAux

/-- Ratio bound for real powers of two comparable positive numbers. -/
lemma pow_ratio {a b δ e g : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ δ * b)
    (hba : b ≤ δ * a) (hδ : 1 ≤ δ) (he1 : e ≤ g) (he2 : -e ≤ g) :
    a ^ e ≤ δ ^ g * b ^ e := by
  have hδ0 : 0 < δ := by linarith
  rcases le_or_gt 0 e with he | he
  · calc a ^ e ≤ (δ * b) ^ e := Real.rpow_le_rpow ha.le hab he
      _ = δ ^ e * b ^ e := Real.mul_rpow hδ0.le hb.le
      _ ≤ δ ^ g * b ^ e :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hδ he1)
            (Real.rpow_nonneg hb.le _)
  · have hba' : b / δ ≤ a := by rw [div_le_iff₀ hδ0]; linarith
    calc a ^ e ≤ (b / δ) ^ e := Real.rpow_le_rpow_of_nonpos (div_pos hb hδ0) hba' he.le
      _ = δ ^ (-e) * b ^ e := by
          rw [Real.div_rpow hb.le hδ0.le, Real.rpow_neg hδ0.le, div_eq_inv_mul]
      _ ≤ δ ^ g * b ^ e :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hδ he2)
            (Real.rpow_nonneg hb.le _)

/-- The scalar comparison behind Theorem 12. -/
lemma key {a b A B x δ γ g : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ δ * b)
    (hba : b ≤ δ * a) (hδ : 1 < δ) (hγ0 : 0 ≤ γ) (hγg : γ ≤ g) (hg1 : 1 ≤ g)
    (hA : 0 ≤ A) (hAB : A ≤ δ * B) (hx : 0 ≤ x) :
    a ^ γ * (A / a - δ ^ (2 * g + 1) * x) ≤ δ ^ (g + 1) * (b ^ γ * (B / b - x)) := by
  have hδ0 : 0 < δ := by linarith
  have h1 : a ^ γ * (A / a) = a ^ (γ - 1) * A := by
    rw [Real.rpow_sub_one ha.ne', div_mul_eq_mul_div, mul_div_assoc]
  have h2 : b ^ γ * (B / b) = b ^ (γ - 1) * B := by
    rw [Real.rpow_sub_one hb.ne', div_mul_eq_mul_div, mul_div_assoc]
  have p1 : a ^ (γ - 1) ≤ δ ^ g * b ^ (γ - 1) :=
    pow_ratio ha hb hab hba hδ.le (by linarith) (by linarith)
  have p2 : b ^ γ ≤ δ ^ g * a ^ γ :=
    pow_ratio hb ha hba hab hδ.le hγg (by linarith)
  have e1 : δ ^ (g + 1) = δ ^ g * δ := by
    rw [Real.rpow_add hδ0, Real.rpow_one]
  have e2 : δ ^ (2 * g + 1) = δ ^ (g + 1) * δ ^ g := by
    rw [← Real.rpow_add hδ0]; ring_nf
  have hdg : 0 ≤ δ ^ g := Real.rpow_nonneg hδ0.le _
  have hdg1 : 0 ≤ δ ^ (g + 1) := Real.rpow_nonneg hδ0.le _
  have hbe : 0 ≤ b ^ (γ - 1) := Real.rpow_nonneg hb.le _
  have i1 : a ^ (γ - 1) * A ≤ δ ^ (g + 1) * (b ^ (γ - 1) * B) := by
    calc a ^ (γ - 1) * A ≤ (δ ^ g * b ^ (γ - 1)) * A := mul_le_mul_of_nonneg_right p1 hA
      _ ≤ (δ ^ g * b ^ (γ - 1)) * (δ * B) :=
          mul_le_mul_of_nonneg_left hAB (mul_nonneg hdg hbe)
      _ = δ ^ (g + 1) * (b ^ (γ - 1) * B) := by rw [e1]; ring
  have i2 : δ ^ (g + 1) * (b ^ γ * x) ≤ δ ^ (2 * g + 1) * (a ^ γ * x) := by
    calc δ ^ (g + 1) * (b ^ γ * x) ≤ δ ^ (g + 1) * ((δ ^ g * a ^ γ) * x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right p2 hx) hdg1
      _ = δ ^ (2 * g + 1) * (a ^ γ * x) := by rw [e2]; ring
  have hL : a ^ γ * (A / a - δ ^ (2 * g + 1) * x)
      = a ^ (γ - 1) * A - δ ^ (2 * g + 1) * (a ^ γ * x) := by
    rw [← h1]; ring
  have hR : δ ^ (g + 1) * (b ^ γ * (B / b - x))
      = δ ^ (g + 1) * (b ^ (γ - 1) * B) - δ ^ (g + 1) * (b ^ γ * x) := by
    rw [← h2]; ring
  rw [hL, hR]
  linarith

open NestedLogitAssort.DeltaGrid

lemma main {M : Type*} [Fintype M] {n : ℕ} (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j)
    (hγ0 : ∀ i, 0 ≤ I.γ i)
    (γbar : ℝ) (hγbar : IsGreatest (Set.range I.γ) γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ)
    (Shat : M → ℤ → Finset (Fin n))
    (hShat : ∀ i l, InLevelRange I δ i l → Feasible15 I δ i l → IsApprox15 I δ i l (Shat i l))
    (x : ℝ) (y : M → ℝ) (hopt : IsOpt4 I (fun i => CandGrid I δ Shat i) x y) :
    Feas3 I (δ ^ (2 * γbar + 1) * x) (fun i => δ ^ (γbar + 1) * y i) := by
  obtain ⟨⟨hsum, hcand⟩, hmin⟩ := hopt
  have hδ0 : 0 < δ := by linarith
  have hVnn : ∀ i S, 0 ≤ V I i S := fun i S =>
    add_nonneg (hw0 i) (Finset.sum_nonneg fun j _ => hv i j)
  have hAnn : ∀ i (S : Finset (Fin n)), 0 ≤ ∑ j ∈ S, I.r i j * I.v i j := fun i S =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hr i j) (hv i j)
  have hRnn : ∀ i S, 0 ≤ R I i S := fun i S => div_nonneg (hAnn i S) (hVnn i S)
  have hT0 : ∀ i z, T I i ∅ z = (I.w0 i) ^ (I.γ i) * (0 - z) := by
    intro i z; simp [T, R, V]
  have hemp : ∀ i, (∅ : Finset (Fin n)) ∈ CandGrid I δ Shat i := fun i => Or.inl rfl
  -- Step 1: x ≥ 0
  have hx : 0 ≤ x := by
    by_contra hneg
    rw [not_le] at hneg
    have hy0 : ∀ i, 0 ≤ y i := by
      intro i
      have h := hcand i ∅ (hemp i)
      rw [hT0] at h
      have : 0 ≤ (I.w0 i) ^ (I.γ i) * (0 - x) :=
        mul_nonneg (Real.rpow_nonneg (hw0 i) _) (by linarith)
      linarith
    have hsum0 : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ => hy0 i
    have hv0x : I.v0 * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv0 hneg.le
    have hv0z : I.v0 = 0 := by
      rcases hv0.lt_or_eq with h | h
      · have : I.v0 * x < 0 := mul_neg_of_pos_of_neg h hneg
        linarith
      · exact h.symm
    have hyz : ∀ i, y i = 0 := by
      intro i
      have hs : ∑ i, y i = 0 := le_antisymm (by linarith) hsum0
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hy0 i)).1 hs i (Finset.mem_univ i)
    have hfeas : Feas4 I (fun i => CandGrid I δ Shat i) (x - 1) (fun _ => (0 : ℝ)) := by
      refine ⟨by simp [hv0z], ?_⟩
      intro i S hS
      have h := hcand i S hS
      rw [hyz i] at h
      have hp : 0 ≤ V I i S ^ I.γ i := Real.rpow_nonneg (hVnn i S) _
      have hRx : 0 < R I i S - x := by linarith [hRnn i S]
      have hz : V I i S ^ I.γ i = 0 := by
        by_contra hne
        have : 0 < V I i S ^ I.γ i * (R I i S - x) :=
          mul_pos (lt_of_le_of_ne hp (Ne.symm hne)) hRx
        unfold T at h
        linarith
      show V I i S ^ I.γ i * (R I i S - (x - 1)) ≤ 0
      rw [hz, zero_mul]
    have := hmin (x - 1) (fun _ => 0) hfeas
    linarith
  have hg1 : 1 ≤ γbar := hγbar1.le
  have hγle : ∀ i, I.γ i ≤ γbar := fun i => hγbar.2 ⟨i, rfl⟩
  have hpow : δ ^ (γbar + 1) ≤ δ ^ (2 * γbar + 1) :=
    Real.rpow_le_rpow_of_exponent_le hδ.le (by linarith)
  have hdg1 : 0 ≤ δ ^ (γbar + 1) := Real.rpow_nonneg hδ0.le _
  -- the empty assortment
  have hE : ∀ i, T I i ∅ (δ ^ (2 * γbar + 1) * x) ≤ δ ^ (γbar + 1) * y i := by
    intro i
    have h := hcand i ∅ (hemp i)
    rw [hT0] at h ⊢
    have hc : 0 ≤ (I.w0 i) ^ (I.γ i) := Real.rpow_nonneg (hw0 i) _
    have h1 : δ ^ (γbar + 1) * ((I.w0 i) ^ (I.γ i) * (0 - x))
        ≤ δ ^ (γbar + 1) * y i := mul_le_mul_of_nonneg_left h hdg1
    have h2 : δ ^ (γbar + 1) * ((I.w0 i) ^ (I.γ i) * x)
        ≤ δ ^ (2 * γbar + 1) * ((I.w0 i) ^ (I.γ i) * x) :=
      mul_le_mul_of_nonneg_right hpow (mul_nonneg hc hx)
    nlinarith
  refine ⟨?_, ?_⟩
  · -- the first constraint
    have hvx : 0 ≤ I.v0 * x := mul_nonneg hv0 hx
    calc ∑ i, δ ^ (γbar + 1) * y i = δ ^ (γbar + 1) * ∑ i, y i := by rw [Finset.mul_sum]
      _ ≤ δ ^ (γbar + 1) * (I.v0 * x) := mul_le_mul_of_nonneg_left hsum hdg1
      _ ≤ δ ^ (2 * γbar + 1) * (I.v0 * x) := mul_le_mul_of_nonneg_right hpow hvx
      _ = I.v0 * (δ ^ (2 * γbar + 1) * x) := by ring
  · intro i S
    show T I i S (δ ^ (2 * γbar + 1) * x) ≤ δ ^ (γbar + 1) * y i
    by_cases hS0 : V I i S = 0
    · -- zero weight: same value as the empty assortment
      have hw : I.w0 i = 0 := by
        have h1 := hw0 i
        have h2 : 0 ≤ ∑ j ∈ S, I.v i j := Finset.sum_nonneg fun j _ => hv i j
        unfold V at hS0
        linarith
      have hTS : T I i S (δ ^ (2 * γbar + 1) * x) = T I i ∅ (δ ^ (2 * γbar + 1) * x) := by
        rw [hT0, hw]
        unfold T R
        rw [hS0, div_zero]
      rw [hTS]
      exact hE i
    · by_cases hSe : S = ∅
      · subst hSe; exact hE i
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hSe
      have hVpos : 0 < V I i S := lt_of_le_of_ne (hVnn i S) (Ne.symm hS0)
      obtain ⟨k, hk1, hk2⟩ := exists_mem_Ioc_zpow hVpos hδ
      have hsub : (k + 1 - 1 : ℤ) = k := by ring
      have hlev : InLevelRange I δ i (k + 1) := by
        refine ⟨⟨j, ?_⟩, ?_⟩
        · have : I.v i j ≤ ∑ j ∈ S, I.v i j :=
            Finset.single_le_sum (fun j _ => hv i j) hj
          have hV : V I i S = I.w0 i + ∑ j ∈ S, I.v i j := rfl
          linarith
        · rw [hsub]
          have : ∑ j ∈ S, I.v i j ≤ ∑ j, I.v i j :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
              (fun j _ _ => hv i j)
          have hV : V I i S = I.w0 i + ∑ j ∈ S, I.v i j := rfl
          linarith
      have hwin : Window I δ i (k + 1) S := by
        refine ⟨?_, hk2⟩
        rw [hsub]; exact hk1.le
      have hfe : Feasible15 I δ i (k + 1) := ⟨S, hwin⟩
      obtain ⟨⟨hb1, hb2⟩, hbest⟩ := hShat i (k + 1) hlev hfe
      rw [hsub] at hb1
      have hmem : Shat i (k + 1) ∈ CandGrid I δ Shat i :=
        Or.inr ⟨k + 1, hlev, hfe, rfl⟩
      have hy := hcand i _ hmem
      have hdk : 0 < δ ^ k := zpow_pos hδ0 k
      have hsucc : δ ^ (k + 1) = δ ^ k * δ := zpow_add_one₀ hδ0.ne' k
      have hbpos : 0 < V I i (Shat i (k + 1)) := lt_of_lt_of_le hdk hb1
      have hab : V I i S ≤ δ * V I i (Shat i (k + 1)) := by
        rw [hsucc] at hk2
        nlinarith
      have hba : V I i (Shat i (k + 1)) ≤ δ * V I i S := by
        rw [hsucc] at hb2
        nlinarith
      have hK := key hVpos hbpos hab hba hδ (hγ0 i) (hγle i) hg1 (hAnn i S) (hbest S hwin) hx
      have hstep : δ ^ (γbar + 1) * T I i (Shat i (k + 1)) x ≤ δ ^ (γbar + 1) * y i :=
        mul_le_mul_of_nonneg_left hy hdg1
      unfold T R at hstep ⊢
      linarith

end NLDGAux

open NestedLogitAssort.DeltaGrid in
theorem solution {M : Type*} [Fintype M] {n : ℕ} (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hanti : ∀ i, Antitone (I.r i))
    (hγ0 : ∀ i, 0 ≤ I.γ i)
    (γbar : ℝ) (hγbar : IsGreatest (Set.range I.γ) γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ)
    (Shat : M → ℤ → Finset (Fin n))
    (hShat : ∀ i l, InLevelRange I δ i l → Feasible15 I δ i l → IsApprox15 I δ i l (Shat i l))
    (x : ℝ) (y : M → ℝ) (hopt : IsOpt4 I (fun i => CandGrid I δ Shat i) x y) :
    Feas3 I (δ ^ (2 * γbar + 1) * x) (fun i => δ ^ (γbar + 1) * y i) := by
  exact NLDGAux.main I hv0 hw0 hv hr hγ0 γbar hγbar hγbar1 δ hδ Shat hShat x y hopt
