-- Prove2me | solution 1 for GlobalTheory.GenSep.free_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:42:31.749324+00:00
-- url     : https://prove2.me/submissions/6851e14e-8141-4e8a-94a7-ade00474f3ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax
import Theorems.Thm_GlobalTheory_GenSep_card_free
import Theorems.Thm_GlobalTheory_GenSep_subst_mem
import Theorems.Thm_GlobalTheory_GenSep_aeval_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_indep_u
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_residueTrdeg


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
set_option maxHeartbeats 1000000
namespace GlobalTheory.GenSep
theorem _root_.solution (htr : Algebra.trdeg K Ω = D) (x : Fin N → Ω) (j0 : Fin N) (hx : x j0 ≠ 0)
    {F : Type} [Field F] [Algebra Ω F] (w : AddValuation F (WithTop ℤ)) (u : Fin (D + 1) × Fin N → F)
    (hu : ∀ p, u p ∈ vRing w)
    (h0 : ∀ P : MvPolynomial (Fin (D + 1) × Fin N) (𝓞 K),
      0 < w (eval₂ ((algebraMap Ω F).comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) u P) ↔
        ∀ α, P.coeff α ∈ la.asIdeal)
    (h1 : ∀ a : 𝓞 K, 0 ≤ w (((algebraMap Ω F).comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) a))
    (hrel : ∀ i : Fin D, ∑ k, u (i.succ, k) * algebraMap Ω F (x k) = 0)
    (hint : ∀ k, x k / x j0 ∈ ((vRing w).comap (algebraMap Ω F)).toSubring) :
    letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω F)
    AlgebraicIndependent (ResidueField ((vRing w).comap (algebraMap Ω F)))
      (fun s : Free D N j0 => residue (vRing w) ⟨u s.1, hu s.1⟩) :=
  (ReciprocityTheory.MultiplicativeHeights.Closed.residueTrdeg K Ω F D htr (Free D N j0) (fun s => u s.1) (vRing w)
    (fun s => hu s.1) (Fin (D + 1) × Fin N) (fun p => ⟨u p, hu p⟩) (subst x j0)
    (fun p α => subst_mem x j0 hint p α)
    (card_free j0) (aeval_subst x j0 hx u hrel) (ValuationResidueLemmas.indep_u (K := K) (Ω := Ω) w la (fun p => ⟨u p, hu p⟩) h0 h1)).2.2
end GlobalTheory.GenSep
