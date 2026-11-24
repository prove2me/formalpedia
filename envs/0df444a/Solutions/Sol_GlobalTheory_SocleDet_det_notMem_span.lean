-- Prove2me | solution 1 for GlobalTheory.SocleDet.det_notMem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:19:40.210467+00:00
-- url     : https://prove2.me/submissions/b4451d24-966f-4e0a-99b2-8fca1ef03a08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Theorems.Thm_GlobalTheory_SocleDet_det_mul_mem
import Theorems.Thm_GlobalTheory_SocleDet_det_sub_det_mem
import Theorems.Thm_GlobalTheory_SocleDet_coeff_eq_zero_of_mem_span_pow
import Theorems.Thm_GlobalTheory_SocleDet_mem_span_X_of_mul_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SocleDet
open Matrix
namespace GlobalTheory.SocleDet
theorem _root_.solution (k : Type) [Field k] (g N : ℕ) (f : Fin g → MvPowerSeries (Fin g) k)
    (a : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k))
    (hf : ∀ i, f i = ∑ j, a i j * MvPowerSeries.X j)
    (hN : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin g) k) ^ N ∈ Ideal.span (Set.range f)) :
    a.det ∉ Ideal.span (Set.range f) := by
  intro hdet
  set x : Fin g → MvPowerSeries (Fin g) k := fun i => MvPowerSeries.X i with hx
  have hN' : ∀ i, x i ^ (N + 1) ∈ Ideal.span (Set.range f) := fun i => by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ (hN i)
  choose b hb using fun i => Ideal.mem_span_range_iff_exists_fun.1 (hN' i)
  set I : Ideal (MvPowerSeries (Fin g) k) := Ideal.span ((fun i => x i ^ (N + 1)) '' Set.univ)
    with hI
  have hxI : ∀ i, x i ^ (N + 1) ∈ I := fun i => Ideal.subset_span ⟨i, trivial, rfl⟩
  let B : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k) := Matrix.of b
  have hBf : ∀ i, (B *ᵥ f) i = x i ^ (N + 1) := hb
  have haf : a *ᵥ x = f := funext fun i => (hf i).symm
  obtain ⟨u, hu⟩ := Ideal.mem_span_range_iff_exists_fun.1 hdet
  have h1 : (B * a).det ∈ I := by
    rw [det_mul, ← hu, Finset.mul_sum]
    refine I.sum_mem fun j _ => ?_
    rw [mul_left_comm]
    exact I.mul_mem_left _ (det_mul_mem I B f j fun r => hBf r ▸ hxI r)
  have h2 := det_sub_det_mem I x mem_span_X_of_mul_X (B * a) (diagonal fun i => x i ^ N)
    (by
      funext i
      rw [← mulVec_mulVec, haf, hBf, mulVec_diagonal, pow_succ])
    (fun r => by rw [← mulVec_mulVec, haf, hBf]; exact hxI r)
  have h3 : ∏ i, x i ^ N ∈ I := by
    simpa [det_diagonal] using I.add_mem h2 h1
  have h4 : ∏ i, x i ^ N = MvPowerSeries.monomial (∑ i, Finsupp.single i N) (1 : k) := by
    simp only [hx, MvPowerSeries.X_pow_eq]
    rw [MvPowerSeries.prod_monomial]
    simp
  have h5 := coeff_eq_zero_of_mem_span_pow (N + 1) Set.univ _ h3 (∑ i, Finsupp.single i N)
    (fun j _ => by simp [Finsupp.finsetSum_apply, Finsupp.single_apply])
  rw [h4, MvPowerSeries.coeff_monomial_same] at h5
  exact one_ne_zero h5
end GlobalTheory.SocleDet
