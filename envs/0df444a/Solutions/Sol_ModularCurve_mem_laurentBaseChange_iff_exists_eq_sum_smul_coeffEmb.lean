-- Prove2me | solution 1 for ModularCurve.mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/20ee4c28-1526-5644-b0cb-c4fe79472206

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb

set_option autoImplicit false

open scoped BigOperators

namespace SpanE96

open ModularCurve

variable {L : Type} [Field L] [CharZero L]
  {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ L)
  (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

noncomputable def φ : ↥F₀ →+* LaurentSeries L := (coeffEmb L).comp F₀.toSubfield.subtype

@[scoped simp] theorem φ_apply (h : ↥F₀) : φ F₀ (L := L) h = coeffEmb L (h : LaurentSeries ℚ) := rfl

@[reducible] noncomputable def modF₀ : Module ↥F₀ (LaurentSeries L) := Module.compHom _ (φ F₀ (L := L))

noncomputable def T : @Submodule ↥F₀ (LaurentSeries L) _ _ (modF₀ F₀) :=
  @Submodule.span ↥F₀ (LaurentSeries L) _ _ (modF₀ F₀) (Set.range fun i => HahnSeries.C (b i))

theorem smul_def' (a : ↥F₀) (x : LaurentSeries L) :
    @HSMul.hSMul ↥F₀ (LaurentSeries L) (LaurentSeries L) (@instHSMul _ _ (modF₀ F₀).toSMul) a x
      = coeffEmb L (a : LaurentSeries ℚ) * x := rfl

theorem mem_T_iff (f : LaurentSeries L) :
    f ∈ T b F₀ ↔ ∃ h : ι → ↥F₀, f = ∑ i, (b i) • coeffEmb L ((h i : ↥F₀) : LaurentSeries ℚ) := by
  letI := modF₀ F₀ (L := L)
  unfold T
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_def', mul_comm, HahnSeries.C_mul_eq_smul]
  · rintro ⟨h, rfl⟩
    refine ⟨h, Finset.sum_congr rfl fun i _ => ?_⟩
    rw [smul_def', mul_comm, HahnSeries.C_mul_eq_smul]

theorem algebraMap_eq_C (ℓ : L) : algebraMap L (LaurentSeries L) ℓ = HahnSeries.C ℓ := by
  rw [HahnSeries.algebraMap_apply']; simp

theorem coeffEmb_C (q : ℚ) : coeffEmb L (HahnSeries.C q) = HahnSeries.C (algebraMap ℚ L q) := by
  ext n; simp

theorem algebraMap_eq_C_rat (q : ℚ) : algebraMap ℚ (LaurentSeries ℚ) q = HahnSeries.C q := by
  rw [HahnSeries.algebraMap_apply']; simp

noncomputable def cst (q : ℚ) : ↥F₀ := ⟨HahnSeries.C q, by rw [← algebraMap_eq_C_rat]; exact F₀.algebraMap_mem q⟩

@[scoped simp] theorem coe_cst (q : ℚ) : ((cst F₀ q : ↥F₀) : LaurentSeries ℚ) = HahnSeries.C q := rfl

theorem C_mem_T (ℓ : L) : HahnSeries.C ℓ ∈ T b F₀ := by
  letI := modF₀ F₀ (L := L)
  have e1 : ∀ i, (cst F₀ (b.repr ℓ i)) • (HahnSeries.C (b i) : LaurentSeries L) = HahnSeries.C ((b.repr ℓ i) • b i) := by
    intro i
    rw [smul_def', coe_cst, coeffEmb_C, ← map_mul, Algebra.smul_def]
  have hℓ : (HahnSeries.C ℓ : LaurentSeries L) = ∑ i, (cst F₀ (b.repr ℓ i)) • (HahnSeries.C (b i) : LaurentSeries L) := by
    simp_rw [e1]
    rw [← map_sum (HahnSeries.C : L →+* LaurentSeries L) (fun i => b.repr ℓ i • b i) Finset.univ, b.sum_repr]
  rw [hℓ]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem one_mem_T : (1 : LaurentSeries L) ∈ T b F₀ := by
  simpa using C_mem_T b F₀ (1 : L)

theorem mul_mem_T {s t : LaurentSeries L} (hs : s ∈ T b F₀) (ht : t ∈ T b F₀) : s * t ∈ T b F₀ := by
  letI := modF₀ F₀ (L := L)
  unfold T at hs ht ⊢
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction ht using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      rw [← map_mul]
      exact C_mem_T b F₀ _
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      rw [smul_def', mul_left_comm, ← smul_def']
      exact Submodule.smul_mem _ _ hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_def', mul_assoc, ← smul_def']
    exact Submodule.smul_mem _ _ hx

theorem inv_mem_T {s : LaurentSeries L} (hs : s ∈ T b F₀) : s⁻¹ ∈ T b F₀ := by
  classical
  letI := modF₀ F₀ (L := L)
  by_cases hs0 : s = 0
  · rw [hs0, inv_zero]; exact Submodule.zero_mem _

  letI instT : Module ↥F₀ ↥(T b F₀) := (T b F₀).module
  haveI : FiniteDimensional ↥F₀ ↥(T b F₀) := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  let m : ↥(T b F₀) →ₗ[↥F₀] ↥(T b F₀) :=
    { toFun := fun x => ⟨s * x, mul_mem_T b F₀ hs x.2⟩
      map_add' := fun x y => Subtype.ext (mul_add _ _ _)
      map_smul' := fun a x => by
        apply Subtype.ext
        show s * (coeffEmb L (a : LaurentSeries ℚ) * (x : LaurentSeries L)) =
          coeffEmb L (a : LaurentSeries ℚ) * (s * x)
        ring }
  have hinj : Function.Injective m := by
    intro x y hxy
    have : s * x = s * y := congrArg (fun z : ↥(T b F₀) => (z : LaurentSeries L)) hxy
    exact Subtype.ext (mul_left_cancel₀ hs0 this)
  obtain ⟨x, hx⟩ := LinearMap.surjective_of_injective hinj ⟨1, one_mem_T b F₀⟩
  have hx' : s * x = 1 := congrArg (fun z : ↥(T b F₀) => (z : LaurentSeries L)) hx
  rw [inv_eq_of_mul_eq_one_right hx']
  exact x.2

theorem exists_intermediateField : ∃ S : IntermediateField L (LaurentSeries L), (S : Set (LaurentSeries L)) = T b F₀ := by
  letI := modF₀ F₀ (L := L)
  refine ⟨{ carrier := T b F₀, mul_mem' := mul_mem_T b F₀, one_mem' := one_mem_T b F₀,
            add_mem' := fun hx hy => Submodule.add_mem _ hx hy, zero_mem' := Submodule.zero_mem _,
            algebraMap_mem' := fun ℓ => by rw [algebraMap_eq_C]; exact C_mem_T b F₀ ℓ,
            inv_mem' := fun _ hx => inv_mem_T b F₀ hx }, rfl⟩

theorem laurentBaseChange_eq : (laurentBaseChange L F₀ : Set (LaurentSeries L)) = T b F₀ := by
  letI := modF₀ F₀ (L := L)
  obtain ⟨S, hS⟩ := exists_intermediateField b F₀
  apply le_antisymm
  ·
    have hle : laurentBaseChange L F₀ ≤ S := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [hS]

      have h1 := Submodule.smul_mem (T b F₀) (⟨x, hx⟩ : ↥F₀) (one_mem_T b F₀)
      rw [smul_def', mul_one] at h1
      exact h1
    intro f hf
    have := hle hf
    rwa [← SetLike.mem_coe, hS] at this
  ·
    intro f hf
    rw [SetLike.mem_coe, mem_T_iff] at hf
    obtain ⟨h, rfl⟩ := hf
    refine IntermediateField.sum_mem _ fun i _ => ?_
    rw [← HahnSeries.C_mul_eq_smul, ← algebraMap_eq_C]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (coeffEmb_mem_laurentBaseChange L (h i).2)

end SpanE96
p2m_reactivate "P2MW.S_ModularCurve_mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb.SpanE96"

theorem solution
    (L : Type) [Field L] [CharZero L]
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ L)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (f : LaurentSeries L) :
    f ∈ ModularCurve.laurentBaseChange L F₀ ↔
      ∃ h : ι → ↥F₀, f = ∑ i, (b i) • ModularCurve.coeffEmb L ((h i : ↥F₀) : LaurentSeries ℚ) := by
  have h := SpanE96.laurentBaseChange_eq b F₀
  rw [← SetLike.mem_coe, h]
  exact SpanE96.mem_T_iff b F₀ f

end S_ModularCurve_mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb
end P2MW
export P2MW.S_ModularCurve_mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb (solution)
