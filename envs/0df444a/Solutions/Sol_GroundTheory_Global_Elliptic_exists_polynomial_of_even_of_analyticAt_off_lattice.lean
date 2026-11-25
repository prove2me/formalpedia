-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.exists_polynomial_of_even_of_analyticAt_off_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:35.449802+00:00
-- url     : https://prove2.me/submissions/bbcc49bb-31eb-48b1-ac57-fd8353b1a0bc

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Theorems.Thm_GroundTheory_Global_Elliptic_isPeriodic_weierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassP_eq_zpow_mul
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_weierstrassP_laurent
import Theorems.Thm_GroundTheory_Global_Elliptic_lt_meromorphicOrderAt_of_eventuallyEq
import Theorems.Thm_GroundTheory_Global_Elliptic_even_of_meromorphicOrderAt_eq
import Theorems.Thm_GroundTheory_Global_Elliptic_exists_eventuallyEq_const_of_analyticAt_off_lattice
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
section
open Complex Filter Topology Set Polynomial
open scoped PeriodPair
noncomputable section
namespace GroundTheory.Global
namespace Elliptic
variable {L : PeriodPair}
private lemma coe_add_one_le_of_lt {o : ℤ} {x : WithTop ℤ} (h : (o : WithTop ℤ) < x) :
    ((o + 1 : ℤ) : WithTop ℤ) ≤ x := by
  cases x with
  | top => exact le_top
  | coe m =>
    have : o < m := by exact_mod_cast h
    exact_mod_cast (by omega : o + 1 ≤ m)
end Elliptic
end GroundTheory.Global
end
end

set_option autoImplicit false
open Complex Filter Topology Set Polynomial
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (n : ℕ) {g : ℂ → ℂ}
    (hg : Meromorphic g) (hp : IsPeriodic L g) (he : ∀ z, g (-z) = g z)
    (han : ∀ z ∉ L.lattice, AnalyticAt ℂ g z)
    (hn : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt g 0) :
    ∃ P : ℂ[X], g =ᶠ[codiscrete ℂ] fun z ↦ P.eval (℘[L] z) := by
  induction n using Nat.strong_induction_on generalizing g with
  | _ n ih =>
  by_cases h0 : 0 ≤ meromorphicOrderAt g 0
  · obtain ⟨c, hc⟩ := exists_eventuallyEq_const_of_analyticAt_off_lattice hg hp han h0
    exact ⟨C c, by simpa using hc⟩
  push Not at h0
  obtain ⟨o, ho⟩ : ∃ o : ℤ, meromorphicOrderAt g 0 = o := by
    cases h : meromorphicOrderAt g 0 with
    | top => rw [h] at h0; exact absurd h0 (not_lt.2 le_top)
    | coe o => exact ⟨o, rfl⟩
  rw [ho] at h0 hn
  have ho0 : o < 0 := by exact_mod_cast h0
  have hno : -(n : ℤ) ≤ o := by exact_mod_cast hn
  obtain ⟨r, hr⟩ := even_of_meromorphicOrderAt_eq (hg 0) he ho
  obtain ⟨k, hk⟩ : ∃ k : ℕ, o = -2 * k := ⟨(-r).toNat, by omega⟩
  have hk1 : 1 ≤ k := by omega
  obtain ⟨u, hu, hu0, hgu⟩ := (meromorphicOrderAt_eq_int_iff (hg 0)).1 ho
  have hv := analyticAt_weierstrassP_laurent (L := L)
  have hdiff : (fun z ↦ g z - u 0 * ℘[L] z ^ k) =ᶠ[𝓝[≠] 0] fun z ↦ (z - 0) ^ o *
      (u z - u 0 * (z ^ 2 * L.weierstrassPExcept 0 z + 1) ^ k) := by
    filter_upwards [hgu, self_mem_nhdsWithin] with z h1 h2
    have h2' : z ≠ 0 := h2
    rw [h1, weierstrassP_eq_zpow_mul h2', mul_pow, ← zpow_natCast (z ^ (-2 : ℤ)), ← zpow_mul,
      hk, sub_zero, smul_eq_mul]
    ring
  have hlt := lt_meromorphicOrderAt_of_eventuallyEq
    (hu.sub (analyticAt_const.mul (hv.pow k))) (by simp) hdiff
  obtain ⟨P, hP⟩ := ih (2 * k - 1) (by omega) (g := fun z ↦ g z - u 0 * ℘[L] z ^ k)
    (fun z ↦ by have := hg z; have := L.meromorphic_weierstrassP z; fun_prop)
    (fun z l hl ↦ by simp only [hp z l hl, isPeriodic_weierstrassP z l hl])
    (fun z ↦ by simp only [he, L.weierstrassP_neg])
    (fun z hz ↦ by
      have := han z hz
      have := L.analyticOnNhd_weierstrassP z hz
      fun_prop)
    (by
      have e : ((-((2 * k - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) = ((o + 1 : ℤ) : WithTop ℤ) := by
        congr 1; omega
      rw [e]
      exact coe_add_one_le_of_lt hlt)
  refine ⟨P + C (u 0) * X ^ k, ?_⟩
  filter_upwards [hP] with z hz
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  rw [← hz]
  ring
end GroundTheory.Global.Elliptic
