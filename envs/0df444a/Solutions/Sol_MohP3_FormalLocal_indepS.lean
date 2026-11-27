-- Prove2me | solution 1 for MohP3.FormalLocal.indepS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:21:49.707101+00:00
-- url     : https://prove2.me/submissions/edca7aa6-dc1b-44b1-b865-ae9654eb47e8

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
public import Theorems.Thm_MohP3_FormalLocal_ooS_mod_inj
public import Theorems.Thm_MohP3_FormalLocal_order_vvS
public import Theorems.Thm_MohP3_FormalLocal_vvS_ne_zero
public import Theorems.Thm_MohP3_FormalLocal_order_eq_coe
public import Theorems.Thm_MohP3_FormalLocal_order_exp8
public import Theorems.Thm_MohP3_FormalLocal_exp8_ne_zero

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (p : Fin 8 → PowerSeries k) (hs : ∑ i, exp8 k (p i) * vvS k i = 0) :
    ∀ i, p i = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, hi0⟩ := hcon
  set w : Fin 8 → PowerSeries k := fun i => exp8 k (p i) * vvS k i with hw
  set S : Finset (Fin 8) := Finset.univ.filter (fun i => p i ≠ 0) with hSdef
  have hS : S.Nonempty := ⟨i0, by simp [hSdef, hi0]⟩
  have hwne : ∀ i ∈ S, w i ≠ 0 := by
    intro i hi
    simp [hSdef] at hi
    exact mul_ne_zero (exp8_ne_zero k hi) (vvS_ne_zero k i)
  have hord : ∀ i ∈ S, (w i).order = ((8 * (p i).order.toNat + ooS i : ℕ) : ℕ∞) := by
    intro i hi
    simp [hSdef] at hi
    rw [hw]
    simp only
    rw [PowerSeries.order_mul, order_exp8 k hi, order_vvS]
    push_cast
    ring
  obtain ⟨m, hmS, hmin⟩ := S.exists_min_image (fun i => (w i).order.toNat) hS
  set d := (w m).order.toNat with hd
  have hmod : ∀ i ∈ S, (w i).order.toNat % 8 = ooS i % 8 := by
    intro i hi
    rw [hord i hi, ENat.toNat_coe]
    omega
  have key : PowerSeries.coeff d (∑ i, w i) = PowerSeries.coeff d (w m) := by
    rw [map_sum, Finset.sum_eq_single m]
    · intro b _ hbm
      by_cases hb : b ∈ S
      · have h1 : d ≤ (w b).order.toNat := hmin b hb
        have h2 : (w b).order.toNat ≠ d :=
          fun he => hbm (ooS_mod_inj (by rw [← hmod b hb, ← hmod m hmS, he]))
        refine PowerSeries.coeff_of_lt_order d ?_
        rw [order_eq_coe k (hwne b hb)]
        exact_mod_cast lt_of_le_of_ne h1 (Ne.symm h2)
      · have hp0 : p b = 0 := by simpa [hSdef] using hb
        simp [hw, hp0]
    · intro hm
      exact absurd (Finset.mem_univ m) hm
  rw [hs] at key
  simp at key
  exact (PowerSeries.coeff_order (hwne m hmS)) key.symm
end MohP3.FormalLocal
