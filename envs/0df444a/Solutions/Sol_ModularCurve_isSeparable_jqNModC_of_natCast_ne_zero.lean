-- Prove2me | solution 1 for ModularCurve.isSeparable_jqNModC_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4523a04a-fd3d-5bed-9dfe-590d8b000590

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_modularPolynomialData
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

p2m_open "ModularCurve P2MW.S_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero.ModularCurve"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC qExpand qExpand_single qExpand_one_apply qExpand_qExpand isSeparable_jqNModC_of_modularPolynomialData exists_modularPolynomialData_evalSymm"
p2m_open "ModularCurve"

namespace SepAllLevels

open IntermediateField

section Generic

variable {k L L' : Type*} [Field k] [Field L] [Field L'] [Algebra k L] [Algebra k L']

theorem algebraMap_comp_inclusion_of_le {F E : IntermediateField k L} (h : F ≤ E) :
    (algebraMap E L).comp (IntermediateField.inclusion h).toRingHom = algebraMap F L :=
  RingHom.ext fun _ => rfl

theorem isSeparable_of_intermediateField_le {F E : IntermediateField k L} (h : F ≤ E) {x : L}
    (hx : IsSeparable F x) : IsSeparable E x := by
  have h0 : Polynomial.aeval x ((minpoly F x).map (IntermediateField.inclusion h).toRingHom) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, algebraMap_comp_inclusion_of_le h]
    exact minpoly.aeval F x
  exact Polynomial.Separable.of_dvd (Polynomial.Separable.map hx) (minpoly.dvd E x h0)

theorem isSeparable_map_algHom (σ : L →ₐ[k] L') (F : IntermediateField k L) {x : L}
    (hx : IsSeparable F x) : IsSeparable (F.map σ) (σ x) := by
  have hc : (algebraMap (F.map σ) L').comp (F.equivMap σ).toAlgHom.toRingHom
      = σ.toRingHom.comp (algebraMap F L) :=
    RingHom.ext fun _ => rfl
  have h0 := Polynomial.map_aeval_eq_aeval_map hc (minpoly F x) x
  rw [minpoly.aeval, map_zero] at h0
  exact Polynomial.Separable.of_dvd (Polynomial.Separable.map hx) (minpoly.dvd _ _ h0.symm)

end Generic

section QExpandAlg

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

theorem algebraMap_laurentSeries_apply_eq_single (c : K) :
    algebraMap K (LaurentSeries K) c = HahnSeries.single 0 c := by
  have h1 : algebraMap K (PowerSeries K) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

def qExpandAlg' : LaurentSeries K →ₐ[K] LaurentSeries K where
  __ := qExpand K N
  commutes' r := by
    show qExpand K N (algebraMap K (LaurentSeries K) r) = algebraMap K (LaurentSeries K) r
    rw [algebraMap_laurentSeries_apply_eq_single, qExpand_single, mul_zero]

@[scoped simp] theorem qExpandAlg'_apply (f : LaurentSeries K) : qExpandAlg' K N f = qExpand K N f := rfl

end QExpandAlg

section Main

variable (K : Type*) [Field K]

local notation "KJ" => IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))

theorem isSeparable_jqNModC_mul (a b : ℕ) [NeZero a] [NeZero b]
    (ha : IsSeparable KJ (jqNModC K a)) (hb : IsSeparable KJ (jqNModC K b)) :
    IsSeparable KJ (jqNModC K (a * b)) := by

  have hmap : IntermediateField.map (qExpandAlg' K a) KJ
      = IntermediateField.adjoin K ({jqNModC K a} : Set (LaurentSeries K)) := by
    have h := IntermediateField.adjoin_map K ({jqModC K} : Set (LaurentSeries K)) (qExpandAlg' K a)
    rw [Set.image_singleton, qExpandAlg'_apply] at h
    exact h
  have e : qExpandAlg' K a (jqNModC K b) = jqNModC K (a * b) := by
    rw [qExpandAlg'_apply, jqNModC, jqNModC, qExpand_qExpand]
  have hab : IsSeparable (IntermediateField.adjoin K ({jqNModC K a} : Set (LaurentSeries K)))
      (jqNModC K (a * b)) := by
    have h := isSeparable_of_intermediateField_le (le_of_eq hmap) (isSeparable_map_algHom (qExpandAlg' K a) KJ hb)
    rwa [e] at h

  haveI : Algebra.IsSeparable KJ (IntermediateField.adjoin KJ ({jqNModC K a} : Set (LaurentSeries K))) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (F := KJ) (E := LaurentSeries K)
      (x := jqNModC K a)).mpr ha
  have hle : IntermediateField.adjoin K ({jqNModC K a} : Set (LaurentSeries K))
      ≤ (IntermediateField.adjoin KJ ({jqNModC K a} : Set (LaurentSeries K))).restrictScalars K :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
      (IntermediateField.mem_adjoin_simple_self KJ (jqNModC K a)))
  have hE : IsSeparable (IntermediateField.adjoin KJ ({jqNModC K a} : Set (LaurentSeries K)))
      (jqNModC K (a * b)) :=
    isSeparable_of_intermediateField_le hle hab
  exact IsSeparable.of_algebra_isSeparable_of_isSeparable (F := KJ)
    (E := IntermediateField.adjoin KJ ({jqNModC K a} : Set (LaurentSeries K))) (K := LaurentSeries K) hE

theorem isSeparable_jqNModC_one : IsSeparable KJ (jqNModC K 1) := by
  have e : jqNModC K 1 = algebraMap KJ (LaurentSeries K)
      ⟨jqModC K, IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩ := by
    show qExpand K 1 (jqModC K) = jqModC K
    exact qExpand_one_apply _
  rw [e]
  exact isSeparable_algebraMap _

theorem isSeparable_jqNModC (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) : IsSeparable KJ (jqNModC K M) := by

  suffices h : ∀ n : ℕ, ∀ _ : NeZero n, (n : K) ≠ 0 → IsSeparable KJ (jqNModC K n) from h M inferInstance hM
  intro n
  induction n using Nat.recOnMul with
  | zero => intro hz h0; exact absurd (by simp) h0
  | one => intro _ _; exact isSeparable_jqNModC_one K
  | prime p hp =>
    intro _ hpK
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨d, hd⟩ := exists_modularPolynomialData_evalSymm p
    exact isSeparable_jqNModC_of_modularPolynomialData K d hd hpK
  | mul a b iha ihb =>
    intro hab h0
    have ha0 : (a : K) ≠ 0 := fun h => h0 (by rw [Nat.cast_mul, h, zero_mul])
    have hb0 : (b : K) ≠ 0 := fun h => h0 (by rw [Nat.cast_mul, h, mul_zero])
    haveI : NeZero a := ⟨fun h => ha0 (by rw [h, Nat.cast_zero])⟩
    haveI : NeZero b := ⟨fun h => hb0 (by rw [h, Nat.cast_zero])⟩
    have := isSeparable_jqNModC_mul K a b (iha inferInstance ha0) (ihb inferInstance hb0)

    convert this

end Main

end SepAllLevels
p2m_reactivate "P2MW.S_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero.ModularCurve.SepAllLevels"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero.ModularCurve.SepAllLevels P2MW.S_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero.ModularCurve.SepAllLevels P2MW.S_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero.ModularCurve"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero.ModularCurve in
theorem solution (K : Type*) [Field K] (M : ℕ) [NeZero M]
    (hM : (M : K) ≠ 0) :
    IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K M) :=
  ModularCurve.SepAllLevels.isSeparable_jqNModC K M hM

end S_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
end P2MW
export P2MW.S_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero (solution)
