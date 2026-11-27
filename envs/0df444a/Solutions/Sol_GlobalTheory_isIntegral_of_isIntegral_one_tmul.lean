-- Prove2me | solution 1 for GlobalTheory.isIntegral_of_isIntegral_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:58.184784+00:00
-- url     : https://prove2.me/submissions/63ef4164-487c-44c5-91d3-12d11d7cd632

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsIntegralIffMemSpanOneTmulIntegralClosure
import Theorems.Thm_GlobalTheory_mem_range_of_map_eq_of_isLocalHom
import Theorems.Thm_GlobalTheory_map_minpoly_dvd_of_aeval_one_tmul

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
theorem _root_.solution {R R' F F' : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsLocalHom (algebraMap R R')]
    [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F']
    [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F']
    {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra R L] [IsScalarTower R F L]
    {l : L} (h : IsIntegral R' ((1 : F') ⊗ₜ[F] l)) : IsIntegral R l := by
  have hl : IsIntegral F l := Algebra.IsIntegral.isIntegral l
  obtain ⟨q, hqm, hq⟩ := h
  have hq' : aeval ((1 : F') ⊗ₜ[F] l) (q.map (algebraMap R' F')) = 0 := by
    rw [aeval_map_algebraMap]
    exact hq
  have hd := map_minpoly_dvd_of_aeval_one_tmul hl hq'
  have hlift := integralClosure.mem_lifts_of_monic_of_dvd_map F' hqm
    ((minpoly.monic hl).map _) hd
  have hlift2 : minpoly F l ∈ lifts (algebraMap R F) := by
    rw [lifts_iff_coeff_lifts] at hlift ⊢
    intro n
    obtain ⟨⟨y, hy⟩, hy2⟩ := hlift n
    obtain ⟨r', hr'⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := R') (K := F') hy
    rw [coeff_map] at hy2
    exact mem_range_of_map_eq_of_isLocalHom _ r' (hr'.trans hy2)
  obtain ⟨g, hg, -, hgm⟩ := lifts_and_degree_eq_and_monic hlift2 (minpoly.monic hl)
  refine ⟨g, hgm, ?_⟩
  have := minpoly.aeval F l
  rw [← hg, aeval_map_algebraMap] at this
  exact this
end GlobalTheory
