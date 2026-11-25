-- Prove2me | solution 1 for GlobalTheory.DualCokernel.eq_zero_of_extZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:51.695866+00:00
-- url     : https://prove2.me/submissions/d23d8fce-cb9e-4519-8639-b694ca999edf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R]
variable [IsLocalRing R]
variable [IsNoetherianRing R]
namespace GlobalTheory.DualCokernel
theorem _root_.solution {M : Type} [AddCommGroup M] [Module R M] (h : ExtZero (R := R) M 0)
    (x : M) (hx : ∀ p : Ideal R, p.IsPrime → p ≠ maximalIdeal R → ∃ s, s ∉ p ∧ s • x = 0) :
    x = 0 := by
  by_contra h0
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x h0
  by_cases hm : P = maximalIdeal R
  · subst hm
    obtain ⟨-, f, hf⟩ := (isAssociatedPrime_iff_exists_injective_linearMap _ _).1 hP
    have h1 : Subsingleton (ModuleCat.of R (R ⧸ maximalIdeal R) ⟶ ModuleCat.of R M) :=
      Ext.addEquiv₀.subsingleton_congr.mp h
    have h2 : f = 0 := congrArg ModuleCat.Hom.hom (h1.elim (ModuleCat.ofHom f) 0)
    have : Nontrivial (R ⧸ maximalIdeal R) := Ideal.Quotient.nontrivial_iff.mpr
      (maximalIdeal.isMaximal R).ne_top
    exact one_ne_zero (hf (a₁ := 1) (a₂ := 0) (by simp [h2]))
  · obtain ⟨s, hs, hsx⟩ := hx P hP.isPrime hm
    exact hs (hle (by simpa [Submodule.mem_colon_singleton] using hsx))
end GlobalTheory.DualCokernel
