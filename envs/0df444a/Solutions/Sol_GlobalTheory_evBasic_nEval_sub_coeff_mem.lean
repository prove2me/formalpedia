-- Prove2me | solution 1 for GlobalTheory.evBasic_nEval_sub_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:06:11.979308+00:00
-- url     : https://prove2.me/submissions/1a027501-3d8a-4599-a5c6-3a882c583f56

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_FormalChartAtZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvBasicNEvalSubCoeffMem
import Theorems.Thm_GlobalTheory_evBasic_tEval_eq_sum
import Theorems.Thm_GlobalTheory_evBasic_nEval_eq_tEval
import Theorems.Thm_GlobalTheory_evBasic_exists_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory
variable {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : Type} [CommRing S] [Algebra R₀ S]
namespace GlobalTheory
theorem _root_.solution (f : MvPowerSeries ι R₀) (a : ι → S)
    (ha : ∀ i, IsNilpotent (a i)) :
    nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a) := by
  obtain ⟨N, hNpos, hN⟩ := evBasic_exists_pow a ha
  rw [evBasic_nEval_eq_tEval f a N hN, evBasic_tEval_eq_sum]
  have h0 : (0 : ι → ℕ) ∈ Fintype.piFinset (fun _ : ι => Finset.range N) :=
    Fintype.mem_piFinset.mpr fun _ => Finset.mem_range.mpr hNpos
  rw [← Finset.add_sum_erase _ _ h0]
  have hc : algebraMap R₀ S (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (0 : ι → ℕ)) f) *
      ∏ i, a i ^ (0 : ι → ℕ) i = algebraMap R₀ S (MvPowerSeries.coeff 0 f) := by
    have hz : Finsupp.equivFunOnFinite.symm (0 : ι → ℕ) = 0 := by
      ext i
      rfl
    simp [hz]
  rw [hc, add_sub_cancel_left]
  refine Ideal.sum_mem _ fun e he => ?_
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact Finset.ne_of_mem_erase he (funext hcon)
  refine Ideal.mul_mem_left _ _ ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _
    (Ideal.subset_span (Set.mem_range_self i) : a i ∈ Ideal.span (Set.range a)) _ (Nat.pos_of_ne_zero hi))
end GlobalTheory
