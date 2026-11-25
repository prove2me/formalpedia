-- Prove2me | solution 1 for GlobalTheory.GradedBezoutCount.ringKrullDim_quotient_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:17:39.251246+00:00
-- url     : https://prove2.me/submissions/9a938323-094c-4ba0-9125-c4ed20753d34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientLeOne
import Theorems.Thm_GlobalTheory_GradedBezoutCount_sub_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open scoped BigOperators
open GlobalTheory
open GlobalTheory.GradedBezoutCount
open GradedBezout
variable {K T : Type*} [Field K] [CommRing T] [Algebra K T] {𝒜 : ℕ → Submodule K T}
  [GradedAlgebra 𝒜]
namespace GlobalTheory.GradedBezoutCount
theorem _root_.solution {P : Ideal T} (ψ : T →ₐ[K] K) {t : T} (ht : t ∈ 𝒜 1)
    (htP : t ∉ P) (h : ∀ e, ∀ y ∈ 𝒜 e, ψ y = 0 → y ∈ P) : ringKrullDim (T ⧸ P) ≤ 1 := by
  have h0 : ψ t ≠ 0 := fun h0 => htP (h 1 t ht h0)
  let π : K[X] →ₐ[K] T ⧸ P := aeval (Ideal.Quotient.mk P t)
  have hsurj : Function.Surjective π := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mkₐ K P y ∈ π.range
    induction y using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rw [map_zero]; exact zero_mem _
    | @homogeneous e y =>
      obtain ⟨h1, h2⟩ := sub_smul_mem ψ ht y.2
      have h3 : Ideal.Quotient.mkₐ K P _ = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (h e _ h1 h2)
      rw [map_sub, map_smul, map_smul, sub_eq_zero] at h3
      refine ⟨((ψ t ^ e)⁻¹ * ψ y) • X ^ e, ?_⟩
      have h4 := congrArg ((ψ t ^ e)⁻¹ • ·) h3
      simp only [smul_smul, inv_mul_cancel₀ (pow_ne_zero e h0), one_smul] at h4
      rw [h4]
      simp [π]
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  refine (ringKrullDim_le_of_surjective π.toRingHom hsurj).trans_eq ?_
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp
end GlobalTheory.GradedBezoutCount
