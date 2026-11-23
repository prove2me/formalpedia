-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:49:01.41284+00:00
-- url     : https://prove2.me/submissions/91fb034a-3eb3-4d3b-b90b-23700bbfe148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Theorems.Thm_GlobalTheory_GaloisDescent_exists_ringEquiv_of_isTranscendenceBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Cardinal
open GlobalTheory GlobalTheory.GaloisDescent
open MvPolynomial Cardinal
namespace GlobalTheory.GaloisDescent
namespace _root_.GlobalTheory.GaloisDescent
theorem _root_.solution {K L : Type*} [Field K] [Field L] [Algebra K L]
    [PerfectField K] [IsAlgClosed L] (x : L) (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) :
    x ∈ Set.range (algebraMap K L) := by
  by_cases halg : IsAlgebraic K x
  · have hxA : x ∈ algebraicClosure K L := mem_algebraicClosure_iff.2 halg
    have hfix : ∀ f : Gal(algebraicClosure K L/K), f ⟨x, hxA⟩ = ⟨x, hxA⟩ := by
      intro f
      obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (algebraicClosure K L) L
      obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis hs hs
        (MvPolynomial.mapEquiv s (f : algebraicClosure K L ≃+* algebraicClosure K L))
      have hτA : ∀ a : algebraicClosure K L, τ (a : L) = (f a : L) := fun a => by
        simpa using hτ (MvPolynomial.C a)
      let σ : L ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := τ) (fun k => by
        simpa using hτA (algebraMap K (algebraicClosure K L) k))
      apply Subtype.ext
      rw [← hτA]
      exact hx σ
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hfix
    exact ⟨k, congrArg Subtype.val hk⟩
  · classical
    have hind : AlgebraicIndepOn K id {x} :=
      (algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set L))).2 halg
    obtain ⟨t, hxt, ht⟩ := exists_isTranscendenceBasis_superset hind
    let i : t := ⟨x, hxt rfl⟩
    let φ : MvPolynomial t K ≃ₐ[K] MvPolynomial t K := AlgEquiv.ofAlgHom
      (aeval fun j => if j = i then X j + 1 else X j) (aeval fun j => if j = i then X j - 1 else X j)
      (MvPolynomial.algHom_ext fun j => by by_cases h : j = i <;> simp [h])
      (MvPolynomial.algHom_ext fun j => by by_cases h : j = i <;> simp [h])
    obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis ht ht φ.toRingEquiv
    have hτx : τ x = x + 1 := by simpa [φ, i] using hτ (X i)
    let σ : L ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := τ) (fun k => by simpa [φ] using hτ (C k))
    have h1 := hx σ
    have h2 : τ x = x := h1
    rw [hτx] at h2
    simp at h2
end _root_.GlobalTheory.GaloisDescent
end GlobalTheory.GaloisDescent
