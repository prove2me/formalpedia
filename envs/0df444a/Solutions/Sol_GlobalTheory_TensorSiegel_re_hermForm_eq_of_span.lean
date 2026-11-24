-- Prove2me | solution 1 for GlobalTheory.TensorSiegel.re_hermForm_eq_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:27:41.098863+00:00
-- url     : https://prove2.me/submissions/75577c53-3e72-4dc3-9d8e-1ad3bca497ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.PTheta Matrix
open scoped Kronecker
noncomputable section
open GlobalTheory GlobalTheory.TensorSiegel
namespace GlobalTheory.TensorSiegel
theorem _root_.solution {g : ℕ} (H H' : Matrix (Fin g) (Fin g) ℂ) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤)
    (h : ∀ z ∈ s, ∀ w ∈ s, (hermForm H z w).im = (hermForm H' z w).im) (z w : Fin g → ℂ) :
    (hermForm H z w).re = (hermForm H' z w).re := by
  have h1 : ∀ z ∈ s, ∀ w, (hermForm H z w).im = (hermForm H' z w).im := by
    intro z hz w
    have hw : w ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw => exact h z hz w hw
    | zero => simp [hermForm]
    | add w w' _ _ e e' =>
      simp only [hermForm, star_add, mulVec_add, dotProduct_add, Complex.add_im] at e e' ⊢
      rw [e, e']
    | smul c w _ e =>
      simp only [hermForm, star_smul, mulVec_smul, dotProduct_smul, Complex.smul_im] at e ⊢
      rw [e]
  have h2 : ∀ z w, (hermForm H z w).im = (hermForm H' z w).im := by
    intro z w
    have hz : z ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => exact h1 z hz w
    | zero => simp [hermForm]
    | add z z' _ _ e e' =>
      simp only [hermForm, add_dotProduct, Complex.add_im] at e e' ⊢
      rw [e, e']
    | smul c z _ e =>
      simp only [hermForm, smul_dotProduct, Complex.smul_im] at e ⊢
      rw [e]
  have := h2 (Complex.I • z) w
  simpa [hermForm, smul_dotProduct] using this
end GlobalTheory.TensorSiegel
