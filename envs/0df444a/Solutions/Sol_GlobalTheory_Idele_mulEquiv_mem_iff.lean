-- Prove2me | solution 1 for GlobalTheory.Idele.mulEquiv_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:54.329808+00:00
-- url     : https://prove2.me/submissions/d353cd5a-4fef-433b-8874-5eb9652c7b24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_mulEquiv_mk_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk

set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors IsDedekindDomain.FiniteAdeleRing
noncomputable section
open GlobalTheory GlobalTheory.Idele
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace GlobalTheory.Idele
theorem _root_.solution (t : 𝔸ᶠ[R, K]ˣ) {I J I' : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : J = t • I) (hle : I ≤ I') {x y : K}
    (hxy : mulEquiv t hI h (Submodule.Quotient.mk x) = Submodule.Quotient.mk y) :
    y ∈ t • I' ↔ x ∈ I' := by
  have hI' : I' ≠ 0 := fun h0 => hI (le_antisymm (h0 ▸ hle) (FractionalIdeal.zero_le I))
  have := mulEquiv_mk_mul t hI hI' h rfl (c := 1) (fun z hz => by simpa using hle hz) hxy
  rw [one_mul, one_mul] at this
  rw [← FractionalIdeal.mem_coe, ← FractionalIdeal.mem_coe, ← Submodule.Quotient.mk_eq_zero,
    ← Submodule.Quotient.mk_eq_zero, ← this, LinearEquiv.map_eq_zero_iff]
end GlobalTheory.Idele
