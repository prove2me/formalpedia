-- Prove2me | solution 1 for GlobalTheory.GenSep.OverGauss.eval_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:30:18.793974+00:00
-- url     : https://prove2.me/submissions/0abc4300-fbf0-4060-9daa-e89d1a32ccf8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.GenSep
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {Ω : Type} [Field Ω] [Algebra K Ω]
  {D N : ℕ}
variable {K' : Type} [Field K'] (φ : MvPolynomial (Fin (D + 1) × Fin N) (la.adicCompletionIntegers K) →+* K')
  (κ : la.adicCompletion K →+* K') (x : Fin N → Ω)
variable {la φ κ x}
namespace GlobalTheory.GenSep
namespace OverGauss
theorem _root_.solution (hκ : ∀ o : la.adicCompletionIntegers K, κ o = φ (C o))
    {F : Type} [Field F] {w : AddValuation F (WithTop ℤ)} {ι : Ω →+* F} {e : K' →+* F}
    (h : OverGauss la φ κ x w ι e) (P : MvPolynomial (Fin (D + 1) × Fin N) (𝓞 K)) :
    eval₂ (ι.comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) (fun p => e (φ (X p))) P =
      e (φ (MvPolynomial.map (algebraMap (𝓞 K) (la.adicCompletionIntegers K)) P)) := by
  have : eval₂Hom (ι.comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) (fun p => e (φ (X p))) =
      e.comp (φ.comp (MvPolynomial.map (algebraMap (𝓞 K) (la.adicCompletionIntegers K)))) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => by simp)
    simp only [coe_eval₂Hom, eval₂_C, RingHom.comp_apply, map_C, h.2.2.1, ← hκ]
    rfl
  exact DFunLike.congr_fun this P
end OverGauss
end GlobalTheory.GenSep
