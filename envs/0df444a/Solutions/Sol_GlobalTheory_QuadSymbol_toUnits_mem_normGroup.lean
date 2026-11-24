-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.toUnits_mem_normGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:56:29.725292+00:00
-- url     : https://prove2.me/submissions/69387760-8847-4230-b071-e9a91b9f5630

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Theorems.Thm_GlobalTheory_QuadSymbol_mem_normGroup_iff
import Theorems.Thm_GlobalTheory_QuadSymbol_mem_globalNorms_iff
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
private theorem norm_one_tmul_eq_algebraMap_norm [FiniteDimensional K L] {A : Type} [CommRing A] [Algebra K A]
    (z : L) : Algebra.norm A ((1 : A) ⊗ₜ[K] z) = algebraMap K A (Algebra.norm K z) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  ext w
  simp
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
theorem _root_.solution [FiniteDimensional K L] (A : Type) [CommRing A]
    [Algebra K A] {x : Kˣ} (hx : x ∈ _root_.GlobalTheory.QuadSymbol.globalNorms K L) :
    _root_.GlobalTheory.QuadSymbol.toUnits K A x ∈ _root_.GlobalTheory.QuadSymbol.normGroup K L A := by
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.QuadSymbol.mem_globalNorms_iff.mp hx
  refine _root_.GlobalTheory.QuadSymbol.mem_normGroup_iff.mpr ⟨(1 : A) ⊗ₜ[K] z, ?_⟩
  rw [norm_one_tmul_eq_algebraMap_norm, hz]
  rfl
end _root_.GlobalTheory.QuadSymbol
end GlobalTheory.QuadSymbol
