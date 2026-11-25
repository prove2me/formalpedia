-- Prove2me | solution 1 for GlobalTheory.SectionBasis.exists_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:47:01.049067+00:00
-- url     : https://prove2.me/submissions/9232f3db-072b-460a-93e6-526f0ce2c444

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic
import Theorems.Thm_GlobalTheory_SectionBasis_sHom_eq
import Theorems.Thm_GlobalTheory_SectionBasis_exists_dvd_of_algebraic

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
theorem _root_.solution (j0 : Fin (N + 1)) (x : Fin N → Ω)
    [Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N)]
    [FiniteDimensional (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N)]
    (hL : ∀ q : MvPolynomial (TVar D N) K, algebraMap (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) (algebraMap (MvPolynomial (TVar D N) K) _ q) = sHom j0 x q)
    (f : MvPolynomial (SVar D N) Ω) (hf : f ≠ 0) :
    ∃ q : MvPolynomial (TVar D N) K, q ≠ 0 ∧ f ∣ aeval (polyImg j0 x) q := by
  exact exists_dvd_of_algebraic (F := FractionRing (MvPolynomial (TVar D N) K)) (L := OmS Ω D N)
    (aeval (R := K) (polyImg (D := D) j0 x)).toRingHom (algebraMap _ _) (IsFractionRing.injective _ _)
    (fun q => (hL q).trans (sHom_eq j0 x q)) f hf
end GlobalTheory.SectionBasis
