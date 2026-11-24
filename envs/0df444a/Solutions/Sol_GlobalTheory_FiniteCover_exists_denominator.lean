-- Prove2me | solution 1 for GlobalTheory.FiniteCover.exists_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:08:03.829048+00:00
-- url     : https://prove2.me/submissions/a974b04d-724e-41e9-8a5b-e480200d936a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCommonMultiple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.FiniteCover
namespace GlobalTheory.FiniteCover
theorem _root_.solution {A C F F' ι : Type*} [CommRing A] [IsDomain A] [CommRing C] [IsDomain C]
    [Field F] [Field F'] [Algebra A C] [Module.Finite A C] [Algebra A F] [IsFractionRing A F]
    [Algebra C F'] [IsFractionRing C F'] [Algebra F F'] [Algebra A F'] [IsScalarTower A F F']
    [IsScalarTower A C F'] [Fintype ι] (e : Basis ι F F') :
    ∃ c : A, c ≠ 0 ∧
      (∀ j (y : C), ∃ a : A, algebraMap A F a = algebraMap A F c * e.repr (algebraMap C F' y) j) ∧
      ∀ j, ∃ y : C, algebraMap C F' y = algebraMap A F c • e j := by
  classical
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := C)
  obtain ⟨c₁, hc₁⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A)
    (fun p : ι × Fin n => e.repr (algebraMap C F' (g p.2)) p.1)
  have h2 : ∀ j, ∃ c : A, c ≠ 0 ∧ ∃ y : C, algebraMap C F' y = algebraMap A F c • e j := by
    intro j
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := C) (e j)
    have hinj : Function.Injective (algebraMap A C) := by
      have : Function.Injective (algebraMap A F') := by
        rw [IsScalarTower.algebraMap_eq A F F']
        exact (algebraMap F F').injective.comp (IsFractionRing.injective A F)
      rw [IsScalarTower.algebraMap_eq A C F'] at this
      exact Function.Injective.of_comp this
    have hal : IsAlgebraic A q := (Algebra.IsIntegral.isIntegral (R := A) q).isAlgebraic
    obtain ⟨c, hc, z, hz⟩ := hal.exists_nonzero_dvd hq
    refine ⟨c, hc, z * p, ?_⟩
    have hq' : algebraMap C F' q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    rw [← hpq, Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A C F', hz, map_mul, map_mul]
    field_simp
  choose c₂ hc₂ y₂ hy₂ using h2
  refine ⟨c₁ * ∏ j, c₂ j, mul_ne_zero (nonZeroDivisors.coe_ne_zero c₁)
    (Finset.prod_ne_zero_iff.2 fun j _ => hc₂ j), fun j y => ?_, fun j => ?_⟩
  · have hy : y ∈ Submodule.span A (Set.range g) := hg ▸ Submodule.mem_top
    suffices h : ∃ a : A, algebraMap A F a = algebraMap A F c₁ * e.repr (algebraMap C F' y) j by
      obtain ⟨a, ha⟩ := h
      exact ⟨a * ∏ j, c₂ j, by rw [map_mul, map_mul, ha]; ring⟩
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      obtain ⟨a, ha⟩ := hc₁ (j, k)
      exact ⟨a, by rw [ha, Algebra.smul_def]⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, map_add, map_add, Finsupp.add_apply, ha, hb, mul_add]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨r * a, ?_⟩
      have : algebraMap C F' (r • x) = algebraMap A F r • algebraMap C F' x := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, ha]
      ring
  · refine ⟨(c₁ * ∏ k ∈ Finset.univ.erase j, c₂ k : A) • y₂ j, ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), ← mul_assoc, map_mul (algebraMap A F) _ (c₂ j),
      mul_smul (algebraMap A F _), ← hy₂, Algebra.smul_def, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
end GlobalTheory.FiniteCover
