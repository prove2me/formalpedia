-- Prove2me | solution 1 for GlobalTheory.TensorSiegel.im_realForm_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:41:16.765033+00:00
-- url     : https://prove2.me/submissions/ce1c3ece-b557-4f05-9855-8487d1ada33a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd
import Theorems.Thm_GlobalTheory_TensorSiegel_im_realForm
import Theorems.Thm_GlobalTheory_im_mulVec_ofRealVec_add
import Theorems.Thm_GlobalTheory_re_mulVec_ofRealVec_add


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
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.TensorSiegel
theorem _root_.solution (T : Matrix ι ι ℂ) (M N : Matrix ι ι ℝ)
    (h1 : (T.map Complex.im)ᵀ * M = N) (h2 : M * T.map Complex.im = N)
    (h3 : N * T.map Complex.re = (T.map Complex.re)ᵀ * N) (m n m' n' : ι → ℝ) :
    ((T *ᵥ ofRealVec m + ofRealVec n) ⬝ᵥ (M.map Complex.ofReal) *ᵥ
      star (T *ᵥ ofRealVec m' + ofRealVec n')).im = m ⬝ᵥ N *ᵥ n' - n ⬝ᵥ N *ᵥ m' := by
  have e : ∀ (A : Matrix ι ι ℝ) (a b : ι → ℝ), (A *ᵥ a) ⬝ᵥ b = a ⬝ᵥ Aᵀ *ᵥ b := fun A a b => by
    rw [dotProduct_mulVec, vecMul_transpose]
  rw [im_realForm]
  simp only [im_mulVec_ofRealVec_add, re_mulVec_ofRealVec_add]
  rw [e, mulVec_mulVec, h1, mulVec_mulVec, h2, add_dotProduct, e, mulVec_add, dotProduct_add,
    mulVec_mulVec, mulVec_mulVec, h3]
  ring
end GlobalTheory.TensorSiegel
