-- Prove2me | solution 1 for ModularCurve.exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/0030f06a-3dc4-52df-84ef-ceb74adf12dd

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange mem_laurentBaseChange_iff"
namespace LaurentBaseChangeSpanAux
p2m_open "ModularCurve"

variable (L : Type) [Field L] [CharZero L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

noncomputable def algF₀ : Algebra ↥F₀ (LaurentSeries L) :=
  ((coeffEmb L).comp (algebraMap ↥F₀ (LaurentSeries ℚ))).toAlgebra

attribute [local instance] algF₀

theorem algebraMap_F₀_apply (f : ↥F₀) :
    algebraMap ↥F₀ (LaurentSeries L) f = coeffEmb L (f : LaurentSeries ℚ) := rfl

noncomputable def ratConst (r : ℚ) : ↥F₀ :=
  ⟨HahnSeries.single 0 r, by
    rw [← ModularCurve.algebraMap_laurentSeries_eq_single ℚ r]
    exact IntermediateField.algebraMap_mem F₀ r⟩

theorem C_ratCast (r : ℚ) :
    (HahnSeries.C (algebraMap ℚ L r) : LaurentSeries L) =
      algebraMap ↥F₀ (LaurentSeries L) (ratConst F₀ r) := by
  rw [algebraMap_F₀_apply, HahnSeries.C_apply]
  change _ = coeffEmb L (HahnSeries.single 0 r)
  rw [coeffEmb, coeffMap_single]

variable {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ L)

noncomputable def M : Submodule ↥F₀ (LaurentSeries L) :=
  Submodule.span ↥F₀ (Set.range fun i => (HahnSeries.C (b i) : LaurentSeries L))

theorem C_mem_M (c : L) : (HahnSeries.C c : LaurentSeries L) ∈ M L F₀ b := by
  have hc : c = ∑ i, (b.repr c i) • b i := (b.sum_repr c).symm
  rw [hc, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def, map_mul, C_ratCast L F₀, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem one_mem_M : (1 : LaurentSeries L) ∈ M L F₀ b := by
  simpa using C_mem_M L F₀ b 1

theorem mul_mem_M (x y : LaurentSeries L) (hx : x ∈ M L F₀ b) (hy : y ∈ M L F₀ b) :
    x * y ∈ M L F₀ b := by

  refine Submodule.span_induction (p := fun x _ => ∀ y, y ∈ M L F₀ b → x * y ∈ M L F₀ b) ?_ ?_ ?_ ?_ hx y hy
  · rintro _ ⟨i, rfl⟩ y hy
    refine Submodule.span_induction (p := fun y _ => HahnSeries.C (b i) * y ∈ M L F₀ b) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨j, rfl⟩
      rw [← map_mul]
      exact C_mem_M L F₀ b _
    · simp
    · intro u v _ _ hu hv
      rw [mul_add]; exact add_mem hu hv
    · intro f u _ hu
      rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hu
  · intro y _; simp
  · intro u v _ _ hu hv y hy
    rw [add_mul]; exact add_mem (hu y hy) (hv y hy)
  · intro f u _ hu y hy
    rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ (hu y hy)

noncomputable def D : Subalgebra ↥F₀ (LaurentSeries L) :=
  (M L F₀ b).toSubalgebra (one_mem_M L F₀ b) (mul_mem_M L F₀ b)

theorem mem_D_iff (x : LaurentSeries L) : x ∈ D L F₀ b ↔ x ∈ M L F₀ b := Iff.rfl

theorem isField_D : IsField ↥(D L F₀ b) := by
  haveI : Module.Finite ↥F₀ ↥(D L F₀ b) := by
    change Module.Finite ↥F₀ ↥(M L F₀ b)
    exact Module.Finite.span_of_finite _ (Set.finite_range _)
  haveI : Algebra.IsIntegral ↥F₀ ↥(D L F₀ b) := Algebra.IsIntegral.of_finite _ _
  exact isField_of_isIntegral_of_isField' (Field.toIsField ↥F₀)

noncomputable def Dfield : Subfield (LaurentSeries L) :=
  { (D L F₀ b).toSubring with
    inv_mem' := by
      intro x hx
      rcases eq_or_ne x 0 with rfl | hx0
      · simpa using (D L F₀ b).zero_mem
      · obtain ⟨y, hy⟩ := (isField_D L F₀ b).mul_inv_cancel
          (show (⟨x, hx⟩ : ↥(D L F₀ b)) ≠ 0 from fun h => hx0 (congrArg Subtype.val h))
        have hxy : x * (y : LaurentSeries L) = 1 := congrArg Subtype.val hy
        have : x⁻¹ = y := by
          rw [inv_eq_of_mul_eq_one_right hxy]
        rw [this]; exact y.2 }

theorem laurentBaseChange_le_D : ∀ y, y ∈ laurentBaseChange L F₀ → y ∈ D L F₀ b := by
  intro y hy
  rw [mem_laurentBaseChange_iff] at hy
  have h : Subfield.closure (Set.range (algebraMap L (LaurentSeries L)) ∪
      (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)))) ≤ Dfield L F₀ b := by
    rw [Subfield.closure_le]
    rintro z (⟨c, rfl⟩ | ⟨f, hf, rfl⟩)
    · change algebraMap L (LaurentSeries L) c ∈ M L F₀ b
      rw [ModularCurve.algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply]
      exact C_mem_M L F₀ b c
    · change coeffEmb L f ∈ M L F₀ b
      have : coeffEmb L f = algebraMap ↥F₀ (LaurentSeries L) ⟨f, hf⟩ := rfl
      rw [this]
      exact Subalgebra.algebraMap_mem (D L F₀ b) _
  exact h hy

end ModularCurve.LaurentBaseChangeSpanAux

open ModularCurve.LaurentBaseChangeSpanAux in
theorem solution
    (L : Type) [Field L] [CharZero L] [FiniteDimensional ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (y : LaurentSeries L) (hy : y ∈ ModularCurve.laurentBaseChange L F₀) :
    ∃ (n : ℕ) (c : Fin n → L) (f : Fin n → LaurentSeries ℚ), (∀ i, f i ∈ F₀) ∧
      y = ∑ i, HahnSeries.single 0 (c i) * ModularCurve.coeffEmb L (f i) := by
  letI := algF₀ L F₀
  let b := Module.finBasis ℚ L
  have hyM : y ∈ M L F₀ b := laurentBaseChange_le_D L F₀ b y hy
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ↥F₀).mp hyM
  refine ⟨Module.finrank ℚ L, fun i => b i, fun i => ((g i : ↥F₀) : LaurentSeries ℚ), fun i => (g i).2, ?_⟩
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, algebraMap_F₀_apply, mul_comm, HahnSeries.C_apply]

end S_ModularCurve_exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange
end P2MW
export P2MW.S_ModularCurve_exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange (solution)
