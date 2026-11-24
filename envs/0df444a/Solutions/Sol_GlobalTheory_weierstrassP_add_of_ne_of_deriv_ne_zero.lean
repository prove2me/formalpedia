-- Prove2me | solution 1 for GlobalTheory.weierstrassP_add_of_ne_of_deriv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:44:30.863982+00:00
-- url     : https://prove2.me/submissions/c140d31a-bb2a-4108-b80c-2041cd9f0545

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Theorems.Thm_GlobalTheory_countable_periodLattice
import Theorems.Thm_GlobalTheory_eqOn_compl_of_countable
import Theorems.Thm_GlobalTheory_eventually_notMem_periodLattice
import Theorems.Thm_GlobalTheory_hasDerivAt_weierstrassP
import Theorems.Thm_GlobalTheory_hasDerivAt_derivWeierstrassP
import Theorems.Thm_GlobalTheory_eventuallyEq_of_weierstrass_system
import Theorems.Thm_GlobalTheory_weierstrass_system_add_const
import Theorems.Thm_GlobalTheory_countable_add_mem_periodLattice
import Theorems.Thm_GlobalTheory_analyticAt_weierstrassP_add
import Theorems.Thm_GlobalTheory_exists_weierstrassP_eq_and_derivWeierstrassP_eq
import Theorems.Thm_GlobalTheory_chord_algebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Bornology
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hne : ℘[L] z ≠ ℘[L] w) (hq : ℘'[L] w ≠ 0) :
    ℘[L] (z + w) = ((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)) ^ 2 / 4 - ℘[L] z - ℘[L] w ∧
    ℘'[L] (z + w) = -((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w) * (℘[L] (z + w) - ℘[L] z) +
      ℘'[L] z) := by
  set p := ℘[L] w with hp
  set q := ℘'[L] w with hq'
  let s : ℂ → ℂ := fun t ↦ (℘'[L] t - q) / (℘[L] t - p)
  let F : ℂ → ℂ := fun t ↦ s t ^ 2 / 4 - ℘[L] t - p
  let G : ℂ → ℂ := fun t ↦ -(s t * (F t - ℘[L] t) + ℘'[L] t)
  have alg : ∀ t ∉ L.lattice, ℘[L] t - p ≠ 0 → _ := fun t ht ht' ↦
    chord_algebra (s := s t) ht' rfl (L.derivWeierstrassP_sq t ht) (L.derivWeierstrassP_sq w hw)
  have hev : ∀ᶠ t in 𝓝 z, t ∉ L.lattice ∧ ℘[L] t - p ≠ 0 :=
    (eventually_notMem_periodLattice L hz).and
      (((hasDerivAt_weierstrassP L hz).continuousAt.sub continuousAt_const).eventually_ne
        (sub_ne_zero.mpr hne))
  have sys : ∀ᶠ t in 𝓝 z, HasDerivAt F (G t) t ∧ HasDerivAt G (6 * F t ^ 2 - L.g₂ / 2) t := by
    filter_upwards [hev] with t ⟨ht, ht'⟩
    obtain ⟨e1, e2, -⟩ := alg t ht ht'
    have d1 := hasDerivAt_weierstrassP L ht
    have d2 := hasDerivAt_derivWeierstrassP L ht
    have ds : HasDerivAt s (2 * (℘[L] t - F t)) t := by
      refine ((d2.sub_const q).div (d1.sub_const p) ht').congr_deriv ?_
      rw [div_eq_iff (pow_ne_zero 2 ht'), e2]
      simp only [F]
      linear_combination ℘'[L] t * e1
    have dF : HasDerivAt F (G t) t := by
      refine ((((ds.pow 2).div_const 4).sub d1).sub_const p).congr_deriv ?_
      simp only [G]
      ring
    refine ⟨dF, ?_⟩
    refine ((ds.mul (dF.sub d1)).add d2).neg.congr_deriv ?_
    simp only [G, F, e2, Pi.sub_apply]
    ring
  obtain ⟨u, hu, hu1, hu2⟩ := exists_weierstrassP_eq_and_derivWeierstrassP_eq L (x := F z) (y := G z) (by
    obtain ⟨-, e2, e3⟩ := alg z hz (sub_ne_zero.mpr hne)
    rw [e3, e2]
    simp only [G, F]
    ring)
  obtain ⟨c, rfl⟩ : ∃ c, u = z + c := ⟨u - z, by ring⟩
  have loc := eventuallyEq_of_weierstrass_system (weierstrass_system_add_const L c hu) sys hu1 hu2
  have glob : Set.EqOn (fun t ↦ 4 * (℘[L] (t + c) + ℘[L] t + p) * (℘[L] t - p) ^ 2)
      (fun t ↦ (℘'[L] t - q) ^ 2) ((L.lattice : Set ℂ) ∪ {t | t + c ∈ L.lattice})ᶜ := by
    refine eqOn_compl_of_countable
      ((countable_periodLattice L).union (countable_add_mem_periodLattice L c))
      (fun t ht ↦ ?_) (fun t ht ↦ ?_) (z := z) (by rintro (h | h); exacts [hz h, hu h]) ?_
    · have := analyticAt_weierstrassP_add L c (z := t) fun h ↦ ht (.inr h)
      have := L.analyticOnNhd_weierstrassP t fun h ↦ ht (.inl h)
      fun_prop
    · have := L.analyticOnNhd_derivWeierstrassP t fun h ↦ ht (.inl h)
      fun_prop
    · filter_upwards [loc, hev] with t ht ⟨_, ht'⟩
      rw [ht]
      simp only [F, s]
      field_simp
      ring
  have hc : -w + c ∈ L.lattice := by
    by_contra hc
    have := glob (x := -w) (by rintro (h | h); exacts [hw (by simpa using h), hc h])
    simp only [weierstrassP_neg, derivWeierstrassP_neg, ← hp, ← hq'] at this
    exact hq (pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination -this / 4))
  have e : z + c = z + w + (⟨_, hc⟩ : L.lattice) := by simp
  rw [e, weierstrassP_add_coe] at hu1
  rw [e, derivWeierstrassP_add_coe] at hu2
  exact ⟨hu1, by rw [hu2, hu1]⟩
end GlobalTheory
