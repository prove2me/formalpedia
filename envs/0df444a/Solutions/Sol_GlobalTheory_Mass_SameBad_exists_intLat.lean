-- Prove2me | solution 1 for GlobalTheory.Mass.SameBad.exists_intLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:45:44.00903+00:00
-- url     : https://prove2.me/submissions/dacc360c-89a0-49c5-9816-d8d51ba489a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteHermitianIsometricOfSameBadPrimes
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_Mass_LocWitt_star_int
import Theorems.Thm_GlobalTheory_MaxLatStruct_star_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_StandardSymmetricSums_star_int
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SameBad
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.SameBad
theorem _root_.solution [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) : ∃ M : Submodule (𝓞 K) V, IsIntLat h M := by
  let b := Module.finBasis K V
  obtain ⟨N, hN⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
    (fun p : Fin (Module.finrank K V) × Fin (Module.finrank K V) => h (b p.1) (b p.2))
  have N0 : algebraMap (𝓞 K) K N ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero N.2
  let b' := b.unitsSMul fun _ => Units.mk0 _ N0
  have hb' : ∀ i, b' i = algebraMap (𝓞 K) K N • b i := fun i => by
    simp [b', Module.Basis.unitsSMul_apply, Units.smul_def]
  refine ⟨Submodule.span (𝓞 K) (Set.range b'), ⟨Submodule.fg_span (Set.finite_range _), ?_⟩, ?_⟩
  · rw [Submodule.span_span_of_tower, b'.span_eq]
  · intro x hx y hy
    induction hx using Submodule.span_induction with
    | zero => simp
    | add x x' _ _ h1 h2 => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ h1 h2
    | smul a x _ h1 =>
      obtain ⟨t, ht⟩ := LocWitt.star_int a
      rw [← algebraMap_smul K a x, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, ← ht,
        algebraMap_smul]
      exact Submodule.smul_mem _ _ h1
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | zero => simp
      | add y y' _ _ h1 h2 => rw [map_add]; exact Submodule.add_mem _ h1 h2
      | smul a y _ h1 =>
        rw [← algebraMap_smul K a y, map_smul, algebraMap_smul]
        exact Submodule.smul_mem _ _ h1
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        obtain ⟨t, ht⟩ := LocWitt.star_int (K := K) N
        obtain ⟨r, hr⟩ := hN (i, j)
        rw [hb', hb', h.map_smulₛₗ, LinearMap.smul_apply, map_smul, starRingEnd_apply, ← ht,
          algebraMap_smul, algebraMap_smul]
        refine Submodule.smul_mem _ _ ?_
        exact Submodule.mem_one.2 ⟨r, hr⟩
end GlobalTheory.Mass.SameBad
