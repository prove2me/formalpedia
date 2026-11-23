-- Prove2me | solution 1 for GlobalTheory.Published.IsArtinMap.unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:19.550185+00:00
-- url     : https://prove2.me/submissions/17c890b5-2d9a-4b6a-ac63-0268823cb4fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
namespace GlobalTheory.Published
namespace IsArtinMap
theorem _root_.solution {H : IntermediateField K ℂ} (hH : IsUnramifiedAbelian H)
    {f g : ClassGroup (𝓞 K) →* (H ≃ₐ[K] H)} (hf : IsArtinMap f) (hg : IsArtinMap g) : f = g := by
  have := hH.1
  have : NumberField H := NumberField.of_module_finite K H
  ext1 c
  obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective c
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp at hI
  | h₂ x hx =>
    obtain rfl : x = 1 := isUnit_iff_eq_one.mp hx
    change f (ClassGroup.mk0 1) = g (ClassGroup.mk0 1)
    simp
  | h₃ a p ha hp ih =>
    have ha' : a ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero ha
    have hp' : p ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hp.ne_zero
    change f (ClassGroup.mk0 (⟨p, hp'⟩ * ⟨a, ha'⟩)) = g (ClassGroup.mk0 (⟨p, hp'⟩ * ⟨a, ha'⟩))
    rw [map_mul, map_mul, map_mul, ih ha']
    congr 1
    have : p.IsPrime := Ideal.isPrime_of_prime hp
    obtain ⟨⟨P, hP, hPp⟩⟩ := (inferInstance : Nonempty (p.primesOver (𝓞 H)))
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp.ne_zero P
    have := hH.2.2 P hP0
    have e := AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt (hf ⟨p, hp'⟩ P hP hPp)
      (hg ⟨p, hp'⟩ P hP hPp) (Ideal.primeCompl_le_nonZeroDivisors P)
    apply AlgEquiv.coe_ringEquiv_injective
    apply RingEquiv.toRingHom_injective
    refine IsFractionRing.ringHom_ext (A := 𝓞 H) fun x => ?_
    exact congrArg (fun y : 𝓞 H => (y : H)) (DFunLike.congr_fun e x)
end IsArtinMap
end GlobalTheory.Published
