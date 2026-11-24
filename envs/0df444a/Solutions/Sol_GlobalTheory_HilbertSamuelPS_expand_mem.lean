-- Prove2me | solution 1 for GlobalTheory.HilbertSamuelPS.expand_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:30:44.141391+00:00
-- url     : https://prove2.me/submissions/dd40a503-1fad-4f40-9f23-5aa933157cb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open GlobalTheory.HilbertSamuelPS
open MvPowerSeries
namespace GlobalTheory.HilbertSamuelPS
theorem _root_.solution {D : ℕ} {A : Type} [CommRing A] [Algebra ℂ A] (x : Fin D → A) (c : Fin D → ℂ)
    (F G : Submodule ℂ A) (m : ℕ)
    (hG : ∀ (f : Fin m → A) (a : Fin D → ℕ), (∀ l, f l ∈ F) → (∀ i, a i < m) →
      (∏ l, f l) * ∏ i, x i ^ a i ∈ G)
    (g : A) (hg : g ∈ F) (a : Fin D → ℕ) (ha : ∀ d, a d < m) :
    g ^ m * ∏ d, (x d - algebraMap ℂ A (c d)) ^ a d ∈ G := by
  have key : ∀ b : Fin D → ℕ, (∀ d, b d < m) → g ^ m * ∏ d, x d ^ b d ∈ G := fun b hb => by
    simpa [Finset.prod_const] using hG (fun _ => g) b (fun _ => hg) hb
  have hexp : ∀ d, (x d - algebraMap ℂ A (c d)) ^ a d = ∑ j ∈ Finset.range (a d + 1),
      ((-c d) ^ (a d - j) * ((a d).choose j : ℂ)) • x d ^ j := by
    intro d
    rw [sub_eq_add_neg, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    simp only [map_mul, map_pow, map_neg, map_natCast]
    ring
  simp_rw [hexp]
  rw [Finset.prod_univ_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun b hb => ?_
  rw [Fintype.mem_piFinset] at hb
  have hb' : ∀ d, b d < m := fun d =>
    lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp (hb d))) (ha d)
  have : ∏ d, ((-c d) ^ (a d - b d) * ((a d).choose (b d) : ℂ)) • x d ^ b d =
      (∏ d, ((-c d) ^ (a d - b d) * ((a d).choose (b d) : ℂ))) • ∏ d, x d ^ b d := by
    simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod, map_mul]
  rw [this, mul_smul_comm]
  exact G.smul_mem _ (key b hb')
end GlobalTheory.HilbertSamuelPS
