-- Prove2me | solution 1 for GlobalTheory.map_minpoly_dvd_of_aeval_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:40:34.307158+00:00
-- url     : https://prove2.me/submissions/f051f551-8183-4faa-9bbe-d8a3e35f2f5a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsIntegralIffMemSpanOneTmulIntegralClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F F' L : Type} [Field F] [Field F'] [Algebra F F']
    [Field L] [Algebra F L] {l : L} (hl : IsIntegral F l) {q : F'[X]}
    (hq : aeval ((1 : F') ⊗ₜ[F] l) q = 0) : (minpoly F l).map (algebraMap F F') ∣ q := by
  obtain ⟨p, hp⟩ : ∃ p, p = (minpoly F l).map (algebraMap F F') := ⟨_, rfl⟩
  rw [← hp]
  have hpm : p.Monic := hp ▸ (minpoly.monic hl).map _
  have hp0 : aeval ((1 : F') ⊗ₜ[F] l) p = 0 := by
    rw [hp, aeval_map_algebraMap]
    have := aeval_algHom_apply (Algebra.TensorProduct.includeRight (R := F) (A := F') (B := L)) l
      (minpoly F l)
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hr : aeval ((1 : F') ⊗ₜ[F] l) (q %ₘ p) = 0 := by
    rw [aeval_modByMonic_eq_self_of_root hp0, hq]
  have hdeg : (q %ₘ p).degree < ((minpoly F l).natDegree : ℕ) := by
    have h5 : p.degree = ((minpoly F l).natDegree : ℕ) := by
      rw [hp, (minpoly.monic hl).degree_map, degree_eq_natDegree (minpoly.ne_zero hl)]
    exact h5 ▸ degree_modByMonic_lt q hpm
  have hli : LinearIndependent F'
      (fun i : Fin (minpoly F l).natDegree => (1 : F') ⊗ₜ[F] (l ^ (i : ℕ))) :=
    Module.Flat.linearIndependent_one_tmul (R := F) (S := F') (linearIndependent_pow (K := F) l)
  rw [← modByMonic_eq_zero_iff_dvd hpm]
  by_contra hne
  have hnd : (q %ₘ p).natDegree < (minpoly F l).natDegree :=
    (natDegree_lt_iff_degree_lt hne).2 hdeg
  rw [aeval_eq_sum_range' hnd, Finset.sum_range] at hr
  simp only [Algebra.TensorProduct.tmul_pow, one_pow] at hr
  have h4 : (q %ₘ p).coeff (q %ₘ p).natDegree = 0 :=
    Fintype.linearIndependent_iff.1 hli (fun i => (q %ₘ p).coeff i) hr ⟨_, hnd⟩
  exact hne (leadingCoeff_eq_zero.1 h4)
end GlobalTheory
