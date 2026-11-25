-- Prove2me | solution 1 for GlobalTheory.GenSep.OverGauss.gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:02:11.900444+00:00
-- url     : https://prove2.me/submissions/aa691a66-3ee0-4d1b-b662-d83693da6ae4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax
import Theorems.Thm_GlobalTheory_GenSep_gauss_one
import Theorems.Thm_GlobalTheory_GenSep_algebraMap_mem_max
import Theorems.Thm_GlobalTheory_GenSep_OverGauss_eval_eq

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
theorem _root_.solution (hκ : ∀ o : la.adicCompletionIntegers K, κ o = φ (C o)) (htr : Algebra.trdeg K Ω = D)
    {F : Type} [Field F] {w : AddValuation F (WithTop ℤ)} {ι : Ω →+* F} {e : K' →+* F}
    (h : OverGauss la φ κ x w ι e) (j0 : Fin N) (hx : x j0 ≠ 0) (hint : ∀ k, 0 ≤ w (ι (x k / x j0)))
    (P : MvPolynomial (Fin (D + 1) × Fin N) Ω) :
    (aeval (subst x j0) P = 0 → eval₂ ι (fun p => e (φ (X p))) P = 0) ∧
    ∀ α ∈ (aeval (subst x j0) P).support,
      (∀ β ∈ (aeval (subst x j0) P).support,
        w (ι ((aeval (subst x j0) P).coeff α)) ≤ w (ι ((aeval (subst x j0) P).coeff β))) →
      w (eval₂ ι (fun p => e (φ (X p))) P) = w (ι ((aeval (subst x j0) P).coeff α)) := by
  refine gauss_one la htr x j0 hx w ι _ (fun Q => ?_) (fun Q => ?_) h.2.2.2 hint P
  · rw [h.eval_eq hκ, h.2.1]
    simp only [coeff_map, algebraMap_mem_max]
  · rw [h.eval_eq hκ]
    exact h.1 _
end OverGauss
end GlobalTheory.GenSep
