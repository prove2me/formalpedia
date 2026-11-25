-- Prove2me | solution 1 for GlobalTheory.SectionBasis.sHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:32:33.085422+00:00
-- url     : https://prove2.me/submissions/90ff7725-6dfb-4294-adeb-8c3b8a374af4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct
variable {K Ω K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field K'] [Algebra K K'] {D N : ℕ}
namespace GlobalTheory.SectionBasis
theorem _root_.solution (j0 : Fin (N + 1)) (x : Fin N → Ω) (q : MvPolynomial (TVar D N) K) :
    sHom j0 x q = algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (aeval (polyImg j0 x) q) := by
  have : (sHom j0 x : MvPolynomial (TVar D N) K →ₐ[K] OmS Ω D N) =
      (IsScalarTower.toAlgHom K (MvPolynomial (SVar D N) Ω) (OmS Ω D N)).comp
        (aeval (polyImg j0 x)) := by
    refine MvPolynomial.algHom_ext fun p => ?_
    simp only [sHom, aeval_X, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    rfl
  rw [this]
  rfl
end GlobalTheory.SectionBasis
