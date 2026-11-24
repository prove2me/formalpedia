-- Prove2me | solution 1 for GlobalTheory.Idele.mulEquiv_mk_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:37:21.589774+00:00
-- url     : https://prove2.me/submissions/2984f598-8ee7-4929-ad9b-224c142b935c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_mulEquiv_mk_eq_mk_iff
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
theorem _root_.solution (t : 𝔸ᶠ[R, K]ˣ) {I J I' J' : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (hI' : I' ≠ 0) (h : J = t • I) (h' : J' = t • I') {c : K} (hc : ∀ z ∈ I, c * z ∈ I') {x y : K}
    (hxy : mulEquiv t hI h (Submodule.Quotient.mk x) = Submodule.Quotient.mk y) :
    mulEquiv t hI' h' (Submodule.Quotient.mk (c * x)) = Submodule.Quotient.mk (c * y) := by
  rw [mulEquiv_mk_eq_mk_iff] at hxy ⊢
  intro v
  subst h h'
  have key : ∀ z ∈ localIdeal v I, algebraMap K (v.adicCompletion K) c * z ∈ localIdeal v I' := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨z, hz, rfl⟩ := hz
      exact Submodule.subset_span ⟨c * z, hc z hz, map_mul _ _ _⟩
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | smul a b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hb
  have ht := idele_apply_ne_zero t v
  have h1 := hxy v
  rw [← mul_div_cancel₀ (_ - _) ht, mul_mem_localIdeal_smul] at h1 ⊢
  convert key _ h1 using 1
  rw [map_mul, map_mul]
  ring
end GlobalTheory.Idele
