-- Prove2me | solution 1 for MvFormalGroup.Hom.eq_of_forall_subst_curve_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/3716bcfc-adbc-5ffa-9aab-8327c801cfb0

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_Hom_eq_of_forall_subst_curve_eq

set_option autoImplicit false

universe u

namespace HomExtSol

open MvPowerSeries Finsupp

variable {R : Type u} [CommRing R] {d : ℕ}

def deg (β : Fin d →₀ ℕ) : ℕ := ∑ j, β j
def wt (K : ℕ) (β : Fin d →₀ ℕ) : ℕ := ∑ j, β j * K ^ (j : ℕ)

theorem le_deg (β : Fin d →₀ ℕ) (j : Fin d) : β j ≤ deg β :=
  Finset.single_le_sum (f := fun j => β j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

theorem eq_of_wt_eq {K : ℕ} {α β : Fin d →₀ ℕ} (hα : ∀ j, α j < K) (hβ : ∀ j, β j < K)
    (h : wt K α = wt K β) : α = β := by
  have hinj := (finFunctionFinEquiv (m := K) (n := d)).injective
  have e : finFunctionFinEquiv (fun j => (⟨α j, hα j⟩ : Fin K)) = finFunctionFinEquiv (fun j => (⟨β j, hβ j⟩ : Fin K)) := by
    apply Fin.ext
    rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
    exact h
  have := hinj e
  ext j
  have := congrFun this j
  simpa using this

theorem wt_lt_pow {K : ℕ} {α : Fin d →₀ ℕ} (hK : deg α < K) : wt K α < K ^ d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp [wt]
  · calc wt K α ≤ ∑ j, α j * K ^ (d - 1) := by
          unfold wt
          refine Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _ ?_
          exact Nat.pow_le_pow_right (by omega) (by omega)
      _ = deg α * K ^ (d - 1) := by rw [deg, Finset.sum_mul]
      _ < K * K ^ (d - 1) := Nat.mul_lt_mul_of_lt_of_le hK le_rfl (Nat.pow_pos (by omega))
      _ = K ^ d := by rw [← pow_succ']; congr 1; omega

theorem weight_eq (K : ℕ) (β : Fin d →₀ ℕ) :
    (∑ j : Fin d, (K ^ d + K ^ (j : ℕ)) * β j) = K ^ d * deg β + wt K β := by
  simp only [add_mul, Finset.sum_add_distrib, deg, wt, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem eq_zero_of_forall_subst_X_pow (D : MvPowerSeries (Fin d) R)
    (h : ∀ n : Fin d → ℕ, (∀ j, 0 < n j) →
      subst (fun j => (X () : MvPowerSeries Unit R) ^ (n j)) D = 0) : D = 0 := by
  classical
  by_contra hD

  have hex : ∃ m, ∃ β : Fin d →₀ ℕ, coeff β D ≠ 0 ∧ deg β = m := by
    obtain ⟨β, hβ⟩ : ∃ β, coeff β D ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hD (MvPowerSeries.ext fun β => by rw [hall β, map_zero])
    exact ⟨_, β, hβ, rfl⟩
  let m := Nat.find hex
  obtain ⟨α, hα, hαm⟩ := Nat.find_spec hex
  have hmin : ∀ β : Fin d →₀ ℕ, coeff β D ≠ 0 → m ≤ deg β := fun β hβ =>
    Nat.find_min' hex ⟨β, hβ, rfl⟩

  set K := m + 1 with hK
  let n : Fin d → ℕ := fun j => K ^ d + K ^ (j : ℕ)
  have hn : ∀ j, 0 < n j := fun j => Nat.add_pos_left (Nat.pow_pos (by omega)) _
  have hγ : HasSubst (fun j => (X () : MvPowerSeries Unit R) ^ (n j)) :=
    hasSubst_of_constantCoeff_zero fun j => by
      rw [map_pow, constantCoeff_X, zero_pow (hn j).ne']

  set M : ℕ := K ^ d * m + wt K α with hM
  have key : ∀ β : Fin d →₀ ℕ, coeff β D ≠ 0 → (∑ j : Fin d, (K ^ d + K ^ (j : ℕ)) * β j) = M → β = α := by
    intro β hβ hw
    rw [weight_eq] at hw
    have hdeg : deg β = m := by
      have h1 := hmin β hβ
      by_contra hne
      have h2 : m + 1 ≤ deg β := by omega
      have : K ^ d * (m + 1) ≤ K ^ d * deg β := Nat.mul_le_mul_left _ h2
      have hlt := wt_lt_pow (K := K) (α := α) (by rw [hαm]; omega)
      rw [mul_add, mul_one] at this
      omega
    rw [hdeg] at hw
    have hwt : wt K β = wt K α := by omega
    exact eq_of_wt_eq (fun j => by have := le_deg β j; omega) (fun j => by have := le_deg α j; omega) hwt
  have hcoeff : coeff (single () M) (subst (fun j => (X () : MvPowerSeries Unit R) ^ (n j)) D) = coeff α D := by
    rw [coeff_subst hγ]
    have hterm : ∀ β : Fin d →₀ ℕ,
        coeff β D • coeff (single () M) (β.prod fun j e => ((X () : MvPowerSeries Unit R) ^ n j) ^ e) =
          if β = α then coeff α D else 0 := by
      intro β
      rw [Finsupp.prod_pow]
      simp_rw [← pow_mul]
      rw [Finset.prod_pow_eq_pow_sum, coeff_X_pow]
      by_cases hβ : coeff β D = 0
      · by_cases hβα : β = α
        · subst hβα; simp [hβ]
        · simp [hβ, hβα]
      · by_cases hw : (∑ j, n j * β j) = M
        · have := key β hβ hw
          subst this
          simp [hw]
        · have hne : β ≠ α := by
            rintro rfl
            apply hw
            rw [weight_eq, hαm]
          rw [if_neg, if_neg hne, smul_zero]
          intro hs
          exact hw ((Finsupp.single_injective ()) hs).symm
    simp_rw [hterm]
    rw [finsum_eq_single _ α (fun β hβ => if_neg hβ), if_pos rfl]
  rw [h n hn, map_zero] at hcoeff
  exact hα hcoeff.symm

end HomExtSol

open HomExtSol in
theorem solution
    {R : Type u} [CommRing R] {d d' : ℕ} (Φ : MvFormalGroup d R) (Φ' : MvFormalGroup d' R)
    (φ ψ : Φ.Hom Φ')
    (h : ∀ γ : Fin d → PowerSeries R, (∀ j, PowerSeries.constantCoeff (γ j) = 0) →
      ∀ k, MvPowerSeries.subst γ (φ.toPowerSeries k) = MvPowerSeries.subst γ (ψ.toPowerSeries k)) :
    φ = ψ := by
  ext k : 2

  have hD : φ.toPowerSeries k - ψ.toPowerSeries k = 0 := by
    refine eq_zero_of_forall_subst_X_pow _ fun n hn => ?_
    have hγ : MvPowerSeries.HasSubst (fun j => (MvPowerSeries.X () : MvPowerSeries Unit R) ^ (n j)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => by
        rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow (hn j).ne']
    have := h (fun j => (PowerSeries.X : PowerSeries R) ^ (n j)) (fun j => by
      rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (hn j).ne']) k
    rw [← MvPowerSeries.coe_substAlgHom hγ, map_sub, sub_eq_zero, MvPowerSeries.coe_substAlgHom hγ]
    exact this
  exact sub_eq_zero.mp hD

end S_MvFormalGroup_Hom_eq_of_forall_subst_curve_eq
end P2MW
export P2MW.S_MvFormalGroup_Hom_eq_of_forall_subst_curve_eq (solution)
