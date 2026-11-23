-- Prove2me | solution 1 for GlobalTheory.JR.Unram.exists_basis_antifixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:32.712207+00:00
-- url     : https://prove2.me/submissions/43105d51-516e-478b-a669-94bfdfc7a248

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
namespace Unram
theorem _root_.solution (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [h : Unram F E] :
    ∃ (b : Module.Basis (Fin 2) F E) (d : F), b 0 = 1 ∧ star (b 1) = - b 1 ∧ b 1 * b 1 = algebraMap F E d ∧ d ≠ 0 := by
  have : CharZero F := h.charZero
  have hsmul : ∀ (c : F) (z : E), star (c • z) = c • star z := by
    intro c z
    rw [Algebra.smul_def, Algebra.smul_def, star_mul, h.star_fix, mul_comm]
  obtain ⟨y, hy⟩ := h.star_ne
  set u : E := y - star y with hu
  have hsu : star u = -u := by rw [hu, star_sub, star_star, neg_sub]
  have hu0 : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have key : ∀ s t : F, star (s • (1 : E) + t • u) = s • 1 + t • u → t = 0 := by
    intro s t hst
    rw [star_add, hsmul, hsmul, star_one, hsu, smul_neg, add_right_inj] at hst
    have h2 : (2 : F) • (t • u) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hst]
      exact neg_add_cancel _
    rcases smul_eq_zero.mp h2 with h2 | h2
    · exact absurd h2 two_ne_zero
    · exact (smul_eq_zero.mp h2).resolve_right hu0
  have hli : LinearIndependent F ![(1 : E), u] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := key s t (by rw [hst, star_zero])
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero] at hst
    exact (smul_eq_zero.mp hst).resolve_right one_ne_zero
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [Fintype.card_fin, h.finrank_eq]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = u := by simp [b]
  have hsum := b.sum_repr (u * u)
  rw [Fin.sum_univ_two, hb0, hb1] at hsum
  have hfix : star (b.repr (u * u) 0 • (1 : E) + b.repr (u * u) 1 • u) =
      b.repr (u * u) 0 • 1 + b.repr (u * u) 1 • u := by
    rw [hsum, star_mul, hsu, neg_mul_neg]
  have h1 := key _ _ hfix
  rw [h1, zero_smul, add_zero] at hsum
  refine ⟨b, b.repr (u * u) 0, hb0, by rw [hb1, hsu], ?_, ?_⟩
  · rw [hb1, Algebra.algebraMap_eq_smul_one]
    exact hsum.symm
  · intro hd
    rw [hd, zero_smul] at hsum
    exact mul_self_ne_zero.mpr hu0 hsum.symm
end Unram
end GlobalTheory.JR
