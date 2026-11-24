-- Prove2me | solution 1 for GlobalTheory.AdicNoeth.exists_leading_generators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:09:28.432746+00:00
-- url     : https://prove2.me/submissions/e384b0f8-b59a-4002-9a4e-477cc46daa01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGradedRingKernelLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsNoetherianRingOfIsAdicComplete
import Theorems.Thm_GlobalTheory_AdicNoeth_isNoetherianRing_graded
import Theorems.Thm_GlobalTheory_mem_reesShiftIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial
namespace GlobalTheory.AdicNoeth
private lemma coeff_mul_monomial_eq_ite {R : Type} [CommRing R] (p : R[X]) (d n : ℕ) (r : R) :
    (p * monomial d r).coeff n = if d ≤ n then p.coeff (n - d) * r else 0 := by
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]
end GlobalTheory.AdicNoeth
end

set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.AdicNoeth
namespace GlobalTheory.AdicNoeth
theorem _root_.solution {R : Type} [CommRing R] (I : Ideal R) (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] (J : Ideal R) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → R) (d : ι → ℕ), (∀ i, f i ∈ J) ∧
      ∀ (n : ℕ) (g : R), g ∈ J → g ∈ I ^ n →
        ∃ c : ι → R, (∀ i, c i ∈ I ^ (n - d i)) ∧ g - ∑ i, c i * f i ∈ I ^ (n + 1) := by
  classical
  have := isNoetherianRing_graded I hI
  let lf : {p : ℕ × R // p.2 ∈ J ∧ p.2 ∈ I ^ p.1} → reesAlgebra I ⧸ reesShiftIdeal I := fun x =>
    Ideal.Quotient.mk (reesShiftIdeal I) ⟨monomial x.1.1 x.1.2, reesAlgebra.monomial_mem.mpr x.2.2⟩
  obtain ⟨s, hsS, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (Set.range lf)).mp
    (IsNoetherian.noetherian (Submodule.span (reesAlgebra I ⧸ reesShiftIdeal I) (Set.range lf)))
  have hpre : ∀ q : s, ∃ x, lf x = q := fun q => hsS q.2
  choose pre hpre using hpre
  refine ⟨s, inferInstance, fun q => (pre q).1.2, fun q => (pre q).1.1, fun q => (pre q).2.1, ?_⟩
  intro n g hgJ hgn
  have hs : (↑s : Set (reesAlgebra I ⧸ reesShiftIdeal I)) = Set.range fun q : s => (q : reesAlgebra I ⧸ reesShiftIdeal I) := by
    ext x; simp
  have hmem : lf ⟨(n, g), hgJ, hgn⟩ ∈ Submodule.span (reesAlgebra I ⧸ reesShiftIdeal I)
      (Set.range fun q : s => (q : reesAlgebra I ⧸ reesShiftIdeal I)) := by
    rw [← hs, ← hspan]
    exact Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
  choose p hp using fun q => Ideal.Quotient.mk_surjective (I := reesShiftIdeal I) (c q)
  have hz : (⟨monomial n g, reesAlgebra.monomial_mem.mpr hgn⟩ : reesAlgebra I) -
      ∑ q : s, p q * ⟨monomial (pre q).1.1 (pre q).1.2, reesAlgebra.monomial_mem.mpr (pre q).2.2⟩
      ∈ reesShiftIdeal I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum]
    have hq : ∀ q : s, Ideal.Quotient.mk (reesShiftIdeal I) (p q *
        ⟨monomial (pre q).1.1 (pre q).1.2, reesAlgebra.monomial_mem.mpr (pre q).2.2⟩) =
        c q • (q : reesAlgebra I ⧸ reesShiftIdeal I) := by
      intro q
      rw [map_mul, hp q, smul_eq_mul]
      exact congrArg _ (hpre q)
    simp only [hq, hc]
    exact sub_self _
  rw [mem_reesShiftIdeal] at hz
  refine ⟨fun q => if (pre q).1.1 ≤ n then ((p q : reesAlgebra I) : R[X]).coeff (n - (pre q).1.1)
    else 0, ?_, ?_⟩
  · intro q
    dsimp only
    split_ifs
    · exact (mem_reesAlgebra_iff I _).mp (p q).2 _
    · exact zero_mem _
  · convert hz n using 1
    simp only [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
      coeff_sub, finsetSum_coeff, coeff_mul_monomial_eq_ite, ite_mul, zero_mul]
    rw [coeff_monomial, if_pos rfl]
end GlobalTheory.AdicNoeth
