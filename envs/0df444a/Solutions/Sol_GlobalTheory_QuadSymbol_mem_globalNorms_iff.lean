-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.mem_globalNorms_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:55.666797+00:00
-- url     : https://prove2.me/submissions/e74cb8d6-b2f6-451d-86a3-f2862179f02a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace GlobalTheory.QuadSymbol
section Local
variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable {K L}
open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable (K L : Type) [Field K] [Field L] [Algebra K L] in
variable {K L} in
private theorem isUnit_of_isUnit_norm' {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    [Module.Free A S] [Module.Finite A S] {z : S} (h : IsUnit (Algebra.norm A z)) : IsUnit z := by
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det] at h
  obtain ⟨u, hu⟩ := h
  have h2 : ((u * u⁻¹ : (Module.End A S)ˣ) : Module.End A S) 1 = 1 := by simp
  rw [Units.val_mul, Module.End.mul_apply, hu] at h2
  exact IsUnit.of_mul_eq_one _ (by simpa using h2)
end Local
section Global
variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
end Global
end GlobalTheory.QuadSymbol
namespace GlobalTheory.Published
open GlobalTheory.QuadSymbol
end GlobalTheory.Published
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open GlobalTheory GlobalTheory.QuadSymbol
variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable {K L}
open NumberField IsDedekindDomain
open scoped TensorProduct
variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable {K L}
namespace GlobalTheory.QuadSymbol
namespace _root_.GlobalTheory.QuadSymbol
theorem _root_.solution [FiniteDimensional K L] {x : Kˣ} :
    x ∈ _root_.GlobalTheory.QuadSymbol.globalNorms K L ↔ ∃ z : L, Algebra.norm K z = x := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, congrArg Units.val hu⟩
  · rintro ⟨z, hz⟩
    have hu : IsUnit z := isUnit_of_isUnit_norm' (A := K) (by rw [hz]; exact x.isUnit)
    exact ⟨hu.unit, Units.ext (by simp [hz])⟩
end _root_.GlobalTheory.QuadSymbol
end GlobalTheory.QuadSymbol
