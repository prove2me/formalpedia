-- Prove2me | solution 1 for GlobalTheory.Published.ComplexMultiplicationJSt.oneOrbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:05:38.635801+00:00
-- url     : https://prove2.me/submissions/b601666a-ac82-4800-8879-531386f15f6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_ExistsMemIdealInvariants
import Theorems.Thm_GlobalTheory_GaloisDescent_exists_algEquiv_extend
import Theorems.Thm_GlobalTheory_Published_exists_isIdealLattice


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
namespace GlobalTheory.Published
namespace ComplexMultiplicationJSt
theorem _root_.solution (h : ComplexMultiplicationJSt) :
    IdealInvariantsOneOrbitSt := by
  intro K _ _ _ _ h2 𝔞 L hL
  obtain ⟨H, art, hH, -, hgen, hact⟩ := h K h2
  have hjH : (latticeCurve L).j ∈ H := by
    rw [← hgen 𝔞 L hL]
    exact IntermediateField.mem_adjoin_simple_self K _
  have : FiniteDimensional K H := hH.1.1
  have : IsAbelianGalois K H := hH.1.2.1
  refine ⟨?_, ?_⟩
  · have hx : IsIntegral K (⟨_, hjH⟩ : H) := IsIntegral.of_finite K _
    exact (IntermediateField.isIntegral_iff.mp hx).isAlgebraic
  · ext x
    constructor
    · rintro ⟨ρ, rfl⟩
      obtain ⟨c, hc⟩ : ∃ c, ClassGroup.mk K c = art.symm (ρ.restrictNormal H) :=
        ClassGroup.induction (R := 𝓞 K) K (P := fun d => ∃ c, ClassGroup.mk K c = d)
          (fun c => ⟨c, rfl⟩) _
      obtain ⟨L', hL'⟩ := exists_isIdealLattice h2 (c⁻¹ * 𝔞)
      refine ⟨c⁻¹ * 𝔞, L', hL', ?_⟩
      have key := hact 𝔞 c L L' hL hL' ⟨_, hjH⟩ rfl
      rw [hc, art.apply_symm_apply] at key
      show _ = ρ (latticeCurve L).j
      rw [← key]
      exact AlgEquiv.restrictNormal_commutes ρ H ⟨_, hjH⟩
    · rintro ⟨𝔠, L'', hc, rfl⟩
      obtain ⟨ρ, hρ⟩ :=
        GlobalTheory.GaloisDescent.exists_algEquiv_extend (L := ℂ) (art (ClassGroup.mk K (𝔞 * 𝔠⁻¹)))
      refine ⟨ρ, ?_⟩
      have hL'' : IsIdealLattice ((𝔞 * 𝔠⁻¹)⁻¹ * 𝔞) L'' := by
        rwa [show (𝔞 * 𝔠⁻¹)⁻¹ * 𝔞 = 𝔠 by group]
      show ρ (latticeCurve L).j = _
      rw [← hact 𝔞 _ L L'' hL hL'' ⟨_, hjH⟩ rfl]
      exact hρ ⟨_, hjH⟩
end ComplexMultiplicationJSt
end GlobalTheory.Published
