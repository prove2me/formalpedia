-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.exists_trace_unit_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:33:50.872068+00:00
-- url     : https://prove2.me/submissions/b4ee5acc-52a5-410e-b422-9fab3d9e5a0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtension
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_intMap_spec
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_intMap_injective
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_mul_ne
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_irreducible
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_pow_ne
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_map_maximalIdeal
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_mem_range_of_val_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}
open scoped nonZeroDivisors
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ)
    (hB : ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O,
      algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i)) :
    ∃ y : K'.O, ∃ a : K.O, IsUnit a ∧
      @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.O := (intMap hU).toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K.O K'.O K'.E := IsScalarTower.of_algebraMap_eq fun a => (intMap_spec hU a).symm
  have hmap : ∀ a : K.O, algebraMap K.O K'.O a = intMap hU a := fun _ => rfl

  obtain ⟨u, hu⟩ := hB
  haveI hfin : Module.Finite K.O K'.O := by
    classical
    refine ⟨⟨Finset.univ.image u, eq_top_iff.2 fun y _ => ?_⟩⟩
    obtain ⟨a, ha⟩ := hu y
    have hy : y = ∑ i, a i • u i := by
      apply IsFractionRing.injective K'.O K'.E
      rw [ha, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, hmap, intMap_spec]
    rw [hy]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  haveI : FaithfulSMul K.O K'.O :=
    (faithfulSMul_iff_algebraMap_injective K.O K'.O).2 (intMap_injective hU)
  haveI : Module.Free K.O K'.O := Module.free_of_finite_type_torsion_free'

  haveI : IsLocalization (Algebra.algebraMapSubmonoid K'.O K.O⁰) K'.E := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
    have hϖ0 : algebraMap K.O K.E ϖ ≠ 0 := by simpa using hϖ.ne_zero
    have hφϖ : φ (algebraMap K.O K.E ϖ) ≠ 0 := by simpa using hϖ0
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      obtain ⟨r, hr, rfl⟩ := hy
      refine IsUnit.mk0 _ ?_
      change algebraMap K'.O K'.E (intMap hU r) ≠ 0
      rw [intMap_spec]
      simpa using nonZeroDivisors.ne_zero hr
    · intro z
      by_cases hz : z = 0
      · exact ⟨⟨0, 1⟩, by simp [hz]⟩
      obtain ⟨s, hs⟩ := mem_range_of_val_nonneg K'
        (z * φ (algebraMap K.O K.E ϖ) ^ (-(val K'.O z)).toNat) (by
          rw [val_mul_ne K' hz (pow_ne_zero _ hφϖ), val_pow_ne K' hφϖ, hU.2.2.1, val_irreducible K hϖ]
          omega)
      refine ⟨⟨s, ⟨algebraMap K.O K'.O (ϖ ^ (-(val K'.O z)).toNat),
        Algebra.mem_algebraMapSubmonoid_of_mem
          ⟨_, pow_mem (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) _⟩⟩⟩, ?_⟩
      change z * algebraMap K'.O K'.E (intMap hU (ϖ ^ (-(val K'.O z)).toNat)) = algebraMap K'.O K'.E s
      rw [hs, intMap_spec, map_pow, map_pow]
    · intro x y h
      exact ⟨1, by rw [IsFractionRing.injective K'.O K'.E h]⟩

  have hpS : Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O) =
      IsLocalRing.maximalIdeal K'.O := map_maximalIdeal hU
  haveI hmax : (Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)).IsMaximal := by
    rw [hpS]; infer_instance
  letI : Field (K.O ⧸ IsLocalRing.maximalIdeal K.O) := Ideal.Quotient.field _
  letI : Field (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) :=
    Ideal.Quotient.field _
  haveI : Finite (K'.O ⧸ IsLocalRing.maximalIdeal K'.O) := K'.fin
  haveI : Finite (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) :=
    Finite.of_equiv _ (Ideal.quotEquivOfEq hpS).symm.toEquiv
  haveI : Finite (K.O ⧸ IsLocalRing.maximalIdeal K.O) := K.fin
  haveI : FiniteDimensional (K.O ⧸ IsLocalRing.maximalIdeal K.O)
      (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) := inferInstance
  haveI : Algebra.IsSeparable (K.O ⧸ IsLocalRing.maximalIdeal K.O)
      (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) := inferInstance
  obtain ⟨z, hz⟩ := Algebra.trace_surjective (K.O ⧸ IsLocalRing.maximalIdeal K.O)
    (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) 1
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have htr := Algebra.trace_quotient_mk (R := K.O) (S := K'.O) y
  rw [hz] at htr
  refine ⟨y, Algebra.trace K.O K'.O y, ?_, ?_⟩
  · by_contra h
    have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal K.O) (Algebra.trace K.O K'.O y) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
    rw [h0] at htr
    exact one_ne_zero htr
  · exact Algebra.trace_localization K.O K.O⁰ (Rₘ := K.E) (Sₘ := K'.E) y
end GlobalTheory.UnitLemma.Unr
