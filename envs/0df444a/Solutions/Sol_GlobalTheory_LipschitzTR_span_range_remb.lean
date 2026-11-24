-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.span_range_remb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:46:54.95754+00:00
-- url     : https://prove2.me/submissions/38fcd4af-6678-44d4-a773-eb8ddf3ea5a8

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsZLatticeFractionalIdealRealLatticeImage
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
open GlobalTheory GlobalTheory.LipschitzTR
namespace GlobalTheory.LipschitzTR
theorem _root_.solution (F : Type) [Field F] [NumberField F] :
    Submodule.span ℝ (Set.range (remb F)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hli := (linearIndependent_monoidHom F ℝ).comp
    (fun τ : F →+* ℝ => (τ : F →* ℝ)) (fun τ₁ τ₂ h => by
      ext a; exact congrArg (fun g : F →* ℝ => g a) h)
  have hsum : ∀ a : F, ∑ τ : F →+* ℝ, f (EuclideanSpace.single τ 1) * τ a = 0 := by
    intro a
    have h1 : f (remb F a) = 0 := hle (Submodule.subset_span ⟨a, rfl⟩)
    have h2 : remb F a = ∑ τ : F →+* ℝ, τ a • EuclideanSpace.single τ (1 : ℝ) := by
      ext σ
      simp [EuclideanSpace.single_apply, Pi.single_apply]
    rw [h2, map_sum] at h1
    simpa [mul_comm] using h1
  have hcoef := Fintype.linearIndependent_iff.mp hli (fun τ => f (EuclideanSpace.single τ 1))
    (by
      funext a
      simpa [Finset.sum_apply] using hsum a)
  apply hf0
  apply LinearMap.ext
  intro x
  have hx : x = ∑ τ : F →+* ℝ, x τ • EuclideanSpace.single τ (1 : ℝ) := by
    ext σ
    simp [EuclideanSpace.single_apply, Pi.single_apply]
  rw [hx, map_sum]
  simp [hcoef]
end GlobalTheory.LipschitzTR
