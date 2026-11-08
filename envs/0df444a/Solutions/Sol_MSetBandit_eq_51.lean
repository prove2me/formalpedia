-- Prove2me | solution 1 for MSetBandit.eq_51
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:17:19.32105+00:00
-- url     : https://prove2.me/submissions/a5663d9e-5354-4264-8c08-fd2aa69518bb

import Mathlib
import Definitions.Def_MSetBandit_lossEst
import Definitions.Def_MSetBandit_expect
open Matrix

namespace Aux_MSB51

open MSetBandit

variable {d m : ℕ}

theorem F_eq (p : Action d m → ℝ) (u w : Fin d → ℝ) :
    (secondMoment p *ᵥ u) ⬝ᵥ w = ∑ x, p x * ((ind x ⬝ᵥ u) * (ind x ⬝ᵥ w)) := by
  simp only [secondMoment, Matrix.mulVec, dotProduct, Matrix.of_apply]
  calc ∑ i, (∑ j, (∑ x, p x * (ind x i * ind x j)) * u j) * w i
      = ∑ i, ∑ j, ∑ x, p x * (ind x i * ind x j) * u j * w i := by
        simp only [Finset.sum_mul]
    _ = ∑ i, ∑ x, ∑ j, p x * (ind x i * ind x j) * u j * w i :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ x, ∑ i, ∑ j, p x * (ind x i * ind x j) * u j * w i := Finset.sum_comm
    _ = ∑ x, p x * ((∑ j, ind x j * u j) * ∑ i, ind x i * w i) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        ring

theorem ind_dot (x : Action d m) (z : Fin d → ℝ) : ind x ⬝ᵥ z = ∑ i ∈ x.1, z i := by
  simp only [dotProduct, ind, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem ind_one (x : Action d m) : ind x ⬝ᵥ (fun _ => (1 : ℝ)) = m := by
  rw [ind_dot]; simp [x.2]

end Aux_MSB51

open MSetBandit Aux_MSB51 in
theorem solution {d m : ℕ} (hm : 1 ≤ m) (hmd : m + 1 ≤ d) (θ : Fin d → ℝ) (X₀ : Action d m)
    (Y : ℝ) :
    expect (wdist θ) (fun x : Action d m => ind x ⬝ᵥ lossEst θ X₀ Y) = Y := by
  classical
  set p := wdist (m := m) θ with hpdef
  set Sg := secondMoment p with hSg
  have hp : ∀ x, 0 < p x := by
    intro x
    simp only [hpdef, wdist]
    apply div_pos (Real.exp_pos _)
    exact Finset.sum_pos (fun y _ => Real.exp_pos _) ⟨X₀, Finset.mem_univ _⟩
  -- injectivity
  have hzero : ∀ z : Fin d → ℝ, (∀ x : Action d m, ind x ⬝ᵥ z = 0) → z = 0 := by
    intro z hz
    obtain ⟨i0, hi0⟩ : X₀.1.Nonempty := by
      rw [← Finset.card_pos, X₀.2]; omega
    have hconst : ∀ j, z j = z i0 := by
      intro j
      by_cases hj : j = i0
      · rw [hj]
      · have hcard : m - 1 ≤ ((Finset.univ \ {i0, j}) : Finset (Fin d)).card := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
            Fintype.card_fin, Finset.card_pair (Ne.symm hj)]
          omega
        obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hcard
        have hiT : i0 ∉ T := fun h => by
          have := hT h; simp at this
        have hjT : j ∉ T := fun h => by
          have := hT h; simp at this
        have h1 := hz ⟨insert i0 T, by rw [Finset.card_insert_of_notMem hiT, hTc]; omega⟩
        have h2 := hz ⟨insert j T, by rw [Finset.card_insert_of_notMem hjT, hTc]; omega⟩
        rw [ind_dot] at h1 h2
        simp only at h1 h2
        rw [Finset.sum_insert hiT] at h1
        rw [Finset.sum_insert hjT] at h2
        linarith
    have h0 := hz X₀
    rw [ind_dot] at h0
    have : ∑ i ∈ X₀.1, z i = m * z i0 := by
      rw [Finset.sum_congr rfl (fun i _ => hconst i), Finset.sum_const, X₀.2, nsmul_eq_mul]
    rw [this] at h0
    have hz0 : z i0 = 0 := by
      have hmR : (m : ℝ) ≠ 0 := by positivity
      exact (mul_eq_zero.mp h0).resolve_left hmR
    funext j
    rw [hconst j, hz0]; rfl
  have hinj : ∀ z, Sg *ᵥ z = 0 → z = 0 := by
    intro z hz
    apply hzero
    have hF := F_eq p z z
    rw [← hSg, hz, zero_dotProduct] at hF
    have hnn : ∀ x ∈ (Finset.univ : Finset (Action d m)), 0 ≤ p x * ((ind x ⬝ᵥ z) * (ind x ⬝ᵥ z)) :=
      fun x _ => mul_nonneg (hp x).le (mul_self_nonneg _)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hF.symm
    intro x
    have hx := this x (Finset.mem_univ _)
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd h (hp x).ne'
    · exact mul_self_eq_zero.mp h
  have hdet : IsUnit Sg.det := by
    rw [isUnit_iff_ne_zero]
    intro h
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    exact hv (hinj v hv0)
  -- main computation
  set w := Sg⁻¹ *ᵥ ind X₀ with hw
  have hSgw : Sg *ᵥ w = ind X₀ := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hkey : ∑ x, p x * (ind x ⬝ᵥ w) = 1 := by
    have h2 := F_eq p w (fun _ => (1 : ℝ))
    rw [← hSg, hSgw, ind_one] at h2
    simp only [ind_one] at h2
    have h3 : ∑ x, p x * ((ind x ⬝ᵥ w) * m) = (m : ℝ) * ∑ x, p x * (ind x ⬝ᵥ w) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
    rw [h3] at h2
    have hmR : (m : ℝ) ≠ 0 := by positivity
    have : (m : ℝ) * (∑ x, p x * (ind x ⬝ᵥ w) - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hmR
    · linarith
  unfold expect lossEst
  rw [← hpdef, ← hSg, ← hw]
  simp only [dotProduct_smul, smul_eq_mul]
  calc ∑ x, p x * (Y * (ind x ⬝ᵥ w)) = Y * ∑ x, p x * (ind x ⬝ᵥ w) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
    _ = Y := by rw [hkey, mul_one]
