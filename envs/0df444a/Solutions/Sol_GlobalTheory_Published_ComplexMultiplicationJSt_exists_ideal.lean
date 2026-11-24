-- Prove2me | solution 1 for GlobalTheory.Published.ComplexMultiplicationJSt.exists_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:38:52.831832+00:00
-- url     : https://prove2.me/submissions/a91ea75f-217e-4a64-bacc-118b8e617c98

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
open NumberField
open scoped nonZeroDivisors IntermediateField
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
namespace GlobalTheory.Published
namespace _root_.GlobalTheory.Published.ComplexMultiplicationJSt
theorem _root_.solution
    (h : _root_.GlobalTheory.Published.ComplexMultiplicationJSt) [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (ρ : ℂ →ₐ[K] ℂ) :
    ∃ 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∀ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L L' : PeriodPair),
      _root_.GlobalTheory.Published.IsIdealLattice 𝔞 L → _root_.GlobalTheory.Published.IsIdealLattice (𝔟⁻¹ * 𝔞) L' →
        ρ (_root_.GlobalTheory.latticeCurve L).j = (_root_.GlobalTheory.latticeCurve L').j := by
  obtain ⟨H, art, hH, -, hgen, hact⟩ := h K h2
  haveI := hH.1.1
  haveI := hH.1.2.1
  obtain ⟨𝔟, h𝔟⟩ : ∃ 𝔟, ClassGroup.mk K 𝔟 = art.symm (ρ.restrictNormal' H) :=
    ClassGroup.induction K (P := fun c => ∃ 𝔟, ClassGroup.mk K 𝔟 = c) (fun 𝔟 => ⟨𝔟, rfl⟩) _
  refine ⟨𝔟, fun 𝔞 L L' hL hL' => ?_⟩
  have hj : (_root_.GlobalTheory.latticeCurve L).j ∈ H := by
    rw [← hgen 𝔞 L hL]
    exact IntermediateField.mem_adjoin_simple_self K _
  have key := hact 𝔞 𝔟 L L' hL hL' ⟨_, hj⟩ rfl
  rw [h𝔟, MulEquiv.apply_symm_apply] at key
  rw [← key]
  exact (AlgHom.restrictNormal_commutes ρ H ⟨_, hj⟩).symm
end _root_.GlobalTheory.Published.ComplexMultiplicationJSt
end GlobalTheory.Published
