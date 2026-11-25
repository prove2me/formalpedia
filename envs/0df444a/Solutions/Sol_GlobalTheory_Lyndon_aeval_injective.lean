-- Prove2me | solution 1 for GlobalTheory.Lyndon.aeval_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:52:03.221223+00:00
-- url     : https://prove2.me/submissions/6f2bbed6-0577-4378-8bc0-c5945de61aaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_factors_unique
import Theorems.Thm_GlobalTheory_Lyndon_exists_sorted
import Theorems.Thm_GlobalTheory_Lyndon_repr_prod_self
import Theorems.Thm_GlobalTheory_Lyndon_le_of_repr_prod_ne_zero
import Theorems.Thm_GlobalTheory_Lyndon_monomial_eq_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Shuffle
open GlobalTheory.Lyndon
variable {A : Type} [LinearOrder A]
open ShuffleAlgebra
variable (K : Type) [Field K]
namespace GlobalTheory.Lyndon
theorem _root_.solution [CharZero K] : Function.Injective
    (MvPolynomial.aeval (fun l : {w : List A // IsLyndon w} => word K l.1) :
      MvPolynomial {w : List A // IsLyndon w} K →ₐ[K] ShuffleAlgebra K A) := by
  classical
  choose Λ hΛ hΛs using fun d : {w : List A // IsLyndon w} →₀ ℕ =>
    exists_sorted ((Finsupp.toMultiset d).map Subtype.val)
  have hfac : ∀ d, IsFactors (Λ d) := fun d => ⟨fun l hl => by
    have : l ∈ (Finsupp.toMultiset d).map Subtype.val := by
      rw [← hΛ]; exact Multiset.mem_coe.2 hl
    obtain ⟨y, _, rfl⟩ := Multiset.mem_map.1 this
    exact y.2, hΛs d⟩
  have hinj : ∀ d d', (Λ d).flatten = (Λ d').flatten → d = d' := fun d d' h => by
    have h1 := factors_unique _ (hfac d) _ (hfac d') h
    have h2 : (Finsupp.toMultiset d).map Subtype.val =
        (Finsupp.toMultiset d').map Subtype.val := by rw [← hΛ, ← hΛ, h1]
    exact Multiset.toFinsupp.symm.injective
      (Multiset.map_injective Subtype.val_injective h2)
  have hmon : ∀ d, MvPolynomial.aeval (fun l : {w : List A // IsLyndon w} => word K l.1)
      (MvPolynomial.monomial d (1 : K)) = ((Λ d).map (word K)).prod := fun d => by
    rw [monomial_eq_prod, map_multiset_prod, ← Multiset.prod_coe, ← Multiset.map_coe, hΛ,
      Multiset.map_map, Multiset.map_map]
    simp
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hne
  obtain ⟨d₀, hd₀, hmax⟩ := p.support.exists_max_image (fun d => (Λ d).flatten)
    (MvPolynomial.support_nonempty.2 hne)
  have hsum : p = ∑ d ∈ p.support, p.coeff d • MvPolynomial.monomial d (1 : K) := by
    conv_lhs => rw [p.as_sum]
    simp [MvPolynomial.smul_monomial]
  rw [hsum, map_sum] at hp
  have h1 := congrArg (fun x => (wordBasis K A).repr x (Λ d₀).flatten) hp
  simp only [map_smul, hmon, map_sum, Finsupp.finsetSum_apply, Finsupp.smul_apply, map_zero,
    Finsupp.zero_apply, smul_eq_mul] at h1
  rw [Finset.sum_eq_single d₀] at h1
  · exact mul_ne_zero (MvPolynomial.mem_support_iff.1 hd₀) (repr_prod_self K _) h1
  · intro d hd hdne
    by_contra h
    have h2 := (le_of_repr_prod_ne_zero K (hfac d) (right_ne_zero_of_mul h)).2
    exact hdne (hinj _ _ (le_antisymm (hmax d hd) h2))
  · exact fun h => absurd hd₀ h
end GlobalTheory.Lyndon
