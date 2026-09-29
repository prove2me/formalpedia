-- Prove2me | solution 1 for IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/db350717-f446-5be7-b430-849f83b2c2cb

import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact

open IsDedekindDomain

namespace M4aP3B
namespace Rows
namespace CompactDenominator

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact_impl
    {C : Set (FiniteAdeleRing R K)} (hC : IsCompact C) :
    ∃ s : R, s ≠ 0 ∧ ∀ y ∈ C, ∀ v : HeightOneSpectrum R,
      (algebraMap R (FiniteAdeleRing R K) s * y) v ∈ v.adicCompletionIntegers K := by
  classical
  let U : R → Set (FiniteAdeleRing R K) := fun s =>
    {y | algebraMap R (FiniteAdeleRing R K) s * y ∈ NumberField.AdelicLevel.integralFiniteAdeles R K}
  have hopen : ∀ s ∈ {s : R | s ≠ 0}, IsOpen (U s) := fun s _ =>
    (NumberField.AdelicLevel.isOpen_integralFiniteAdeles R K).preimage (continuous_const_mul _)
  have hcover : C ⊆ ⋃ s ∈ {s : R | s ≠ 0}, U s := fun y _ => by
    obtain ⟨s, hs0, hs⟩ := NumberField.AdelicBox.exists_mul_mem_integralFiniteAdeles R K y
    exact Set.mem_biUnion hs0 hs
  obtain ⟨T, hTsub, hTfin, hCT⟩ := hC.elim_finite_subcover_image hopen hcover
  refine ⟨∏ s ∈ hTfin.toFinset, s,
    Finset.prod_ne_zero_iff.mpr fun s hs => hTsub (hTfin.mem_toFinset.mp hs), fun y hy v => ?_⟩
  obtain ⟨s, hsT, hys⟩ := Set.mem_iUnion₂.mp (hCT hy)
  rw [← Finset.prod_erase_mul _ _ (hTfin.mem_toFinset.mpr hsT), map_mul, mul_assoc,
    NumberField.AdelicBox.algebraMap_mul_apply]
  exact mul_mem (NumberField.AdelicBox.algebraMap_mem_adicCompletionIntegers R K v _) (hys v)

theorem gate_empty : ∃ s : R, s ≠ 0 ∧ ∀ y ∈ (∅ : Set (FiniteAdeleRing R K)), ∀ v : HeightOneSpectrum R,
      (algebraMap R (FiniteAdeleRing R K) s * y) v ∈ v.adicCompletionIntegers K :=
  ⟨1, one_ne_zero, fun _ h => h.elim⟩

end M4aP3B.Rows.CompactDenominator

#print axioms M4aP3B.Rows.CompactDenominator.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact_impl
#print axioms M4aP3B.Rows.CompactDenominator.gate_empty

theorem solution
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : Set (IsDedekindDomain.FiniteAdeleRing R K)} (hC : IsCompact C) :
    ∃ s : R, s ≠ 0 ∧ ∀ y ∈ C, ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      (algebraMap R (IsDedekindDomain.FiniteAdeleRing R K) s * y) v
        ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v := by
  first
    | exact M4aP3B.Rows.CompactDenominator.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact_impl R K hC
    | (apply M4aP3B.Rows.CompactDenominator.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact_impl <;> assumption)

end S_IsDedekindDomain_FiniteAdeleRing_exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
end P2MW
export P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact (solution)
