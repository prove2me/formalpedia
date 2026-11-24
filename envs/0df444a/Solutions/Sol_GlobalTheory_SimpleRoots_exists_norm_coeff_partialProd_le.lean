-- Prove2me | solution 1 for GlobalTheory.SimpleRoots.exists_norm_coeff_partialProd_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:16:06.713803+00:00
-- url     : https://prove2.me/submissions/f15800ac-deaf-42a8-9f80-bb0594a25b79

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsConnectedUnramifiedCoverOfIrreducible
import Theorems.Thm_GlobalTheory_SimpleRoots_card_roots_map
import Theorems.Thm_GlobalTheory_SimpleRoots_exists_norm_root_le
import Theorems.Thm_GlobalTheory_SimpleRoots_norm_coeff_prod_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.SimpleRoots
open Polynomial
variable {d : ℕ}
namespace GlobalTheory.SimpleRoots
theorem _root_.solution {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    (u : Set ((Fin d → ℂ) × ℂ)) :
    ∃ (C : ℝ) (m : ℕ), ∀ k x, ‖(partialProd p u x).coeff k‖ ≤ C * (1 + ‖x‖) ^ m := by
  classical
  obtain ⟨C₀, m₀, hC₀, hroot⟩ := exists_norm_root_le hp
  refine ⟨(1 + C₀) ^ p.natDegree, m₀ * p.natDegree, fun k x => ?_⟩
  set R := C₀ * (1 + ‖x‖) ^ m₀ with hR
  have ht : 1 ≤ (1 + ‖x‖) ^ m₀ := one_le_pow₀ (by linarith [norm_nonneg x])
  have hR0 : 0 ≤ R := mul_nonneg hC₀ (by linarith)
  have hbound := norm_coeff_prod_le
    ((p.map (MvPolynomial.eval x)).roots.filter fun y => (x, y) ∈ u) hR0
    (fun y hy => hroot x y ((Polynomial.mem_roots (hp.map _).ne_zero).mp
      (Multiset.mem_of_mem_filter hy))) k
  have hcard : Multiset.card ((p.map (MvPolynomial.eval x)).roots.filter fun y => (x, y) ∈ u) ≤
      p.natDegree := by
    rw [← card_roots_map hp x]
    exact Multiset.card_le_card (Multiset.filter_le _ _)
  have h1R : 1 + R ≤ (1 + C₀) * (1 + ‖x‖) ^ m₀ := by
    rw [hR]; nlinarith
  calc ‖(partialProd p u x).coeff k‖ ≤ (1 + R) ^ Multiset.card
          ((p.map (MvPolynomial.eval x)).roots.filter fun y => (x, y) ∈ u) := hbound
    _ ≤ (1 + R) ^ p.natDegree := pow_le_pow_right₀ (by linarith) hcard
    _ ≤ ((1 + C₀) * (1 + ‖x‖) ^ m₀) ^ p.natDegree := pow_le_pow_left₀ (by linarith) h1R _
    _ = (1 + C₀) ^ p.natDegree * (1 + ‖x‖) ^ (m₀ * p.natDegree) := by rw [mul_pow, ← pow_mul]
end GlobalTheory.SimpleRoots
