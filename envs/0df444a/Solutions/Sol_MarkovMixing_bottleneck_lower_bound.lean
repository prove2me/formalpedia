-- Prove2me | solution 1 for MarkovMixing.bottleneck_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-22T15:10:50.511088+00:00
-- url     : https://prove2.me/submissions/94155d37-2658-4c20-8f92-dadb645bd039

import Theorems.Thm_MarkovMixing_convergence_theorem
import Definitions.Def_mm_lower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity

open scoped BigOperators
open scoped Matrix
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (hap : Aperiodic P) (π : V → ℝ) (hπ : IsStationary P π) :
    (4 * bottleneckStar P π)⁻¹ ≤ (tMix P π : ℝ) := by
  classical
  have hpow_nonneg : ∀ (n : ℕ) (a b : V), 0 ≤ (P ^ n) a b := by
    intro n
    induction n with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ m ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun w _ => mul_nonneg (ih a w) (hP.1 w b)
  have hProw : ∀ (n : ℕ) (a : V), ∑ b, (P ^ n) a b = 1 := by
    intro n
    induction n with
    | zero => intro a; simp [Matrix.one_apply]
    | succ m ih =>
        intro a
        rw [pow_succ]
        have e : ∀ b : V, (P ^ m * P) a b = ∑ w, (P ^ m) a w * P w b := fun b => rfl
        rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_comm]
        rw [Finset.sum_congr rfl fun w _ => by rw [← Finset.mul_sum, hP.2 w, mul_one]]
        exact ih a
  have hstat_pow : ∀ n : ℕ, π ᵥ* (P ^ n) = π := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]
  have hπpos : ∀ y : V, 0 < π y := by
    intro y
    obtain ⟨z, hz⟩ : ∃ z : V, 0 < π z := by
      by_contra hcon
      push_neg at hcon
      have hzero : ∀ z : V, π z = 0 := fun z => le_antisymm (hcon z) (hπ.1.1 z)
      have h := hπ.1.2
      simp [hzero] at h
    obtain ⟨n, hn⟩ := hirr z y
    have hval : π y = ∑ w, π w * (P ^ n) w y := (congrFun (hstat_pow n) y).symm
    have hterm : π z * (P ^ n) z y ≤ ∑ w, π w * (P ^ n) w y :=
      Finset.single_le_sum (f := fun w => π w * (P ^ n) w y)
        (fun w _ => mul_nonneg (hπ.1.1 w) (hpow_nonneg n w y)) (Finset.mem_univ z)
    have : 0 < π z * (P ^ n) z y := mul_pos hz hn
    rw [hval]; linarith
  -- supremum bookkeeping for `d(t)`
  have hbdd : ∀ μ ν : V → ℝ,
      BddAbove (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|) :=
    fun μ ν => Set.Finite.bddAbove
      (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|).toFinite
  have hbdd_d : ∀ n : ℕ,
      BddAbove (Set.range fun x : V => tvDist (rowDist P n x) π) :=
    fun n => Set.Finite.bddAbove
      (Set.range fun x : V => tvDist (rowDist P n x) π).toFinite
  have hd_ge : ∀ (n : ℕ) (x : V) (A : Finset V),
      |∑ z ∈ A, (P ^ n) x z - ∑ z ∈ A, π z| ≤ distStationary P π n := by
    intro n x A
    exact le_trans (le_ciSup (hbdd (rowDist P n x) π) A) (le_ciSup (hbdd_d n) x)
  -- the mixing time is attained
  obtain ⟨α, hα, C, hC, hgeo⟩ := MarkovMixing.convergence_theorem P hP hirr hap π hπ
  have hattain : distStationary P π (tMix P π) ≤ 1 / 4 := by
    have hne : {t : ℕ | distStationary P π t ≤ 1 / 4}.Nonempty := by
      obtain ⟨n, hn⟩ :=
        exists_pow_lt_of_lt_one (x := (1 / 4 : ℝ) / C) (y := α) (by positivity) hα.2
      refine ⟨n, ?_⟩
      have h1 : C * α ^ n < C * ((1 / 4 : ℝ) / C) := mul_lt_mul_of_pos_left hn hC
      have h2 : C * ((1 / 4 : ℝ) / C) = 1 / 4 := by field_simp
      have := hgeo n
      simp only [Set.mem_setOf_eq]
      linarith
    exact Nat.sInf_mem hne
  -- the key bound: every bottleneck ratio is at least `1 / (4 t_mix)`
  have hratio : ∀ S : Finset V, S.Nonempty → ∑ x ∈ S, π x ≤ 2⁻¹ →
      1 ≤ tMix P π ∧ 1 / (4 * (tMix P π : ℝ)) ≤ bottleneckRatio P π S := by
    intro S hSne hShalf
    set πS : ℝ := ∑ x ∈ S, π x with hπS
    have hπSpos : 0 < πS := by
      rw [hπS]
      exact Finset.sum_pos (fun x _ => hπpos x) hSne
    set μS : V → ℝ := fun x => if x ∈ S then π x / πS else 0 with hμS
    have hμSnonneg : ∀ x, 0 ≤ μS x := by
      intro x
      show 0 ≤ if x ∈ S then π x / πS else 0
      by_cases h : x ∈ S
      · rw [if_pos h]; exact div_nonneg (hπ.1.1 x) hπSpos.le
      · rw [if_neg h]
    have hμSle : ∀ x, μS x ≤ π x / πS := by
      intro x
      show (if x ∈ S then π x / πS else 0) ≤ π x / πS
      by_cases h : x ∈ S
      · rw [if_pos h]
      · rw [if_neg h]; exact div_nonneg (hπ.1.1 x) hπSpos.le
    have hμSsum : ∑ x, μS x = 1 := by
      rw [hμS]
      rw [← Finset.sum_filter]
      have hfil : Finset.univ.filter (fun x : V => x ∈ S) = S := by
        ext x; simp
      rw [hfil]
      simp only [div_eq_mul_inv, ← Finset.sum_mul, ← hπS]
      exact mul_inv_cancel₀ hπSpos.ne'
    set ν : ℕ → V → ℝ := fun n y => ∑ x, μS x * (P ^ n) x y with hν
    have hνnonneg : ∀ n y, 0 ≤ ν n y := fun n y =>
      Finset.sum_nonneg fun x _ => mul_nonneg (hμSnonneg x) (hpow_nonneg n x y)
    have hνdom : ∀ (n : ℕ) (y : V), ν n y ≤ π y / πS := by
      intro n y
      have hle : ν n y ≤ ∑ x, (π x / πS) * (P ^ n) x y :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_right (hμSle x) (hpow_nonneg n x y)
      have heq : ∑ x, (π x / πS) * (P ^ n) x y = π y / πS := by
        have hfac : ∀ x : V, (π x / πS) * (P ^ n) x y
            = (π x * (P ^ n) x y) * πS⁻¹ := fun x => by ring
        rw [Finset.sum_congr rfl fun x _ => hfac x, ← Finset.sum_mul]
        have : ∑ x, π x * (P ^ n) x y = π y := congrFun (hstat_pow n) y
        rw [this, div_eq_mul_inv]
      linarith [hle, heq.le, heq.ge]
    have hνstep : ∀ (n : ℕ) (y : V), ν (n + 1) y = ∑ w, ν n w * P w y := by
      intro n y
      show ∑ x, μS x * (P ^ (n + 1)) x y = ∑ w, (∑ x, μS x * (P ^ n) x w) * P w y
      have e : ∀ x : V, (P ^ (n + 1)) x y = ∑ w, (P ^ n) x w * P w y := by
        intro x; rw [pow_succ]; rfl
      rw [Finset.sum_congr rfl fun x _ => by rw [e x, Finset.mul_sum], Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by ring
    have hPScle : ∀ x : V, ∑ y ∈ Sᶜ, P x y ≤ 1 := by
      intro x
      rw [← hP.2 x]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun y _ _ => hP.1 x y)
    have hflow : ∑ x ∈ S, (π x / πS) * ∑ y ∈ Sᶜ, P x y = bottleneckRatio P π S := by
      rw [bottleneckRatio, ← hπS]
      have hnum : ∑ x ∈ S, ∑ y ∈ Sᶜ, edgeMeasure P π x y
          = ∑ x ∈ S, π x * ∑ y ∈ Sᶜ, P x y := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => rfl
      rw [hnum]
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by ring
    have hleak : ∀ n : ℕ, ∑ y ∈ Sᶜ, ν n y ≤ (n : ℝ) * bottleneckRatio P π S := by
      intro n
      induction n with
      | zero =>
          have : ∀ y ∈ (Sᶜ : Finset V), ν 0 y = 0 := by
            intro y hy
            have hyS : y ∉ S := Finset.mem_compl.mp hy
            show ∑ x, μS x * (P ^ 0) x y = 0
            rw [Finset.sum_eq_zero]
            intro x _
            rw [pow_zero, Matrix.one_apply]
            by_cases hxy : x = y
            · subst hxy
              rw [hμS]
              simp only [if_neg hyS, zero_mul]
            · rw [if_neg hxy, mul_zero]
          rw [Finset.sum_congr rfl this]
          simp
      | succ m ih =>
          have hexp : ∑ y ∈ Sᶜ, ν (m + 1) y = ∑ w, ν m w * ∑ y ∈ Sᶜ, P w y := by
            rw [Finset.sum_congr rfl fun y _ => hνstep m y, Finset.sum_comm]
            exact Finset.sum_congr rfl fun w _ => by rw [Finset.mul_sum]
          rw [hexp]
          have hsplit : ∑ w, ν m w * ∑ y ∈ Sᶜ, P w y
              = ∑ w ∈ S, ν m w * ∑ y ∈ Sᶜ, P w y
                + ∑ w ∈ Sᶜ, ν m w * ∑ y ∈ Sᶜ, P w y := by
            rw [add_comm]
            exact (Finset.sum_compl_add_sum S _).symm
          rw [hsplit]
          have hA : ∑ w ∈ S, ν m w * ∑ y ∈ Sᶜ, P w y ≤ bottleneckRatio P π S := by
            rw [← hflow]
            refine Finset.sum_le_sum fun w _ => ?_
            refine mul_le_mul_of_nonneg_right (hνdom m w) ?_
            exact Finset.sum_nonneg fun y _ => hP.1 w y
          have hB : ∑ w ∈ Sᶜ, ν m w * ∑ y ∈ Sᶜ, P w y ≤ ∑ w ∈ Sᶜ, ν m w := by
            refine Finset.sum_le_sum fun w _ => ?_
            calc ν m w * ∑ y ∈ Sᶜ, P w y ≤ ν m w * 1 :=
                  mul_le_mul_of_nonneg_left (hPScle w) (hνnonneg m w)
              _ = ν m w := mul_one _
          push_cast
          linarith [hA, hB, ih]
    -- comparing `ν n` with `π` on the complement of `S`
    have hνtv : ∀ (n : ℕ) (A : Finset V),
        |∑ y ∈ A, ν n y - ∑ y ∈ A, π y| ≤ distStationary P π n := by
      intro n A
      have hrw : ∑ y ∈ A, ν n y - ∑ y ∈ A, π y
          = ∑ x, μS x * ((∑ y ∈ A, (P ^ n) x y) - ∑ y ∈ A, π y) := by
        have h1 : ∑ y ∈ A, ν n y = ∑ x, μS x * ∑ y ∈ A, (P ^ n) x y := by
          show ∑ y ∈ A, ∑ x, μS x * (P ^ n) x y = _
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
        rw [h1]
        rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) =>
          (by ring : μS x * ((∑ y ∈ A, (P ^ n) x y) - ∑ y ∈ A, π y)
            = μS x * (∑ y ∈ A, (P ^ n) x y) - μS x * ∑ y ∈ A, π y)]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hμSsum, one_mul]
      rw [hrw]
      calc |∑ x, μS x * ((∑ y ∈ A, (P ^ n) x y) - ∑ y ∈ A, π y)|
          ≤ ∑ x, |μS x * ((∑ y ∈ A, (P ^ n) x y) - ∑ y ∈ A, π y)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ x, μS x * distStationary P π n := by
            refine Finset.sum_le_sum fun x _ => ?_
            rw [abs_mul, abs_of_nonneg (hμSnonneg x)]
            exact mul_le_mul_of_nonneg_left (hd_ge n x A) (hμSnonneg x)
        _ = distStationary P π n := by rw [← Finset.sum_mul, hμSsum, one_mul]
    have hπSc : ∑ y ∈ (Sᶜ : Finset V), π y = 1 - πS := by
      have h := Finset.sum_compl_add_sum S (fun y => π y)
      rw [hπ.1.2] at h
      linarith
    have hgap : ∀ n : ℕ,
        2⁻¹ - (n : ℝ) * bottleneckRatio P π S ≤ distStationary P π n := by
      intro n
      have h := hνtv n Sᶜ
      rw [abs_le] at h
      have h1 := h.1
      rw [hπSc] at h1
      have := hleak n
      linarith
    -- the mixing time must be positive
    have htpos : 1 ≤ tMix P π := by
      by_contra hcon
      push_neg at hcon
      have h0 : tMix P π = 0 := by omega
      have hg : (2:ℝ)⁻¹ ≤ distStationary P π 0 := by
        have h := hgap 0
        simpa using h
      rw [h0] at hattain
      linarith
    refine ⟨htpos, ?_⟩
    have htR : (0:ℝ) < (tMix P π : ℝ) := by exact_mod_cast htpos
    have h := hgap (tMix P π)
    have : 2⁻¹ - (tMix P π : ℝ) * bottleneckRatio P π S ≤ 1 / 4 := le_trans h hattain
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 4 * (tMix P π : ℝ))]
    linarith
  -- assemble
  rcases isEmpty_or_nonempty {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹} with hemp | hnon
  · have hzero : bottleneckStar P π = 0 := by
      show (⨅ S : {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹},
        bottleneckRatio P π S.1) = 0
      rw [iInf, Set.range_eq_empty, Real.sInf_empty]
    rw [hzero, mul_zero, inv_zero]
    exact Nat.cast_nonneg _
  · have htpos : 1 ≤ tMix P π :=
      (hratio hnon.some.1 hnon.some.2.1 hnon.some.2.2).1
    have htR : (0:ℝ) < (tMix P π : ℝ) := by exact_mod_cast htpos
    have hle : 1 / (4 * (tMix P π : ℝ)) ≤ bottleneckStar P π := by
      refine le_ciInf fun S => ?_
      exact (hratio S.1 S.2.1 S.2.2).2
    have h1 : ((tMix P π : ℝ))⁻¹ ≤ 4 * bottleneckStar P π := by
      have h4 := mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ) ≤ 4)
      have heq : (4:ℝ) * (1 / (4 * (tMix P π : ℝ))) = ((tMix P π : ℝ))⁻¹ := by
        field_simp
      rw [heq] at h4
      exact h4
    have hposinv : (0:ℝ) < ((tMix P π : ℝ))⁻¹ := by positivity
    have hpos4 : (0:ℝ) < 4 * bottleneckStar P π := lt_of_lt_of_le hposinv h1
    rw [inv_le_comm₀ hpos4 htR]
    exact h1
