-- Prove2me | solution 1 for GlobalTheory.GenSep.gauss_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:52:28.343734+00:00
-- url     : https://prove2.me/submissions/86e3ab02-9c57-48c3-b920-20778aaf5af3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax
import Theorems.Thm_GlobalTheory_GenSep_aeval_subst
import Theorems.Thm_GlobalTheory_GenSep_free_indep
import Theorems.Thm_GlobalTheory_PlaceRestrict_val_aeval_eq_coeff


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
    {F : Type} [Field F] (w : AddValuation F (WithTop ℤ)) (ι : Ω →+* F) (u : Fin (D + 1) × Fin N → F)
    (h0 : ∀ P : MvPolynomial (Fin (D + 1) × Fin N) (𝓞 K),
      0 < w (eval₂ (ι.comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) u P) ↔ ∀ α, P.coeff α ∈ la.asIdeal)
    (h1 : ∀ P : MvPolynomial (Fin (D + 1) × Fin N) (𝓞 K),
      0 ≤ w (eval₂ (ι.comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) u P))
    (hrel : ∀ i : Fin D, ∑ k, u (i.succ, k) * ι (x k) = 0) (hint : ∀ k, 0 ≤ w (ι (x k / x j0)))
    (P : MvPolynomial (Fin (D + 1) × Fin N) Ω) :
    (aeval (subst x j0) P = 0 → eval₂ ι u P = 0) ∧
    ∀ α ∈ (aeval (subst x j0) P).support,
      (∀ β ∈ (aeval (subst x j0) P).support,
        w (ι ((aeval (subst x j0) P).coeff α)) ≤ w (ι ((aeval (subst x j0) P).coeff β))) →
      w (eval₂ ι u P) = w (ι ((aeval (subst x j0) P).coeff α)) := by
  letI : Algebra Ω F := ι.toAlgebra
  have hu : ∀ p, u p ∈ vRing w := fun p => by
    have := h1 (X p)
    rw [eval₂_X] at this
    exact this
  have hs := aeval_subst x j0 hx u hrel
  have hP : eval₂ ι u P = aeval (fun s : Free D N j0 => u s.1) (aeval (subst x j0) P) := by
    have h : (aeval (fun s : Free D N j0 => u s.1)).comp (aeval (subst x j0)) = aeval (R := Ω) u :=
      algHom_ext fun p => by rw [AlgHom.comp_apply, aeval_X, aeval_X, hs]
    have h2 := DFunLike.congr_fun h P
    rw [AlgHom.comp_apply] at h2
    rw [h2, aeval_def]
    rfl
  have RT := free_indep la htr x j0 hx w u hu h0 (fun a => by
    have := h1 (C a)
    rw [eval₂_C] at this
    exact this) hrel (fun k => hint k)
  refine ⟨fun h => by rw [hP, h, map_zero], fun α hα hmin => ?_⟩
  rw [hP]
  exact GlobalTheory.PlaceRestrict.val_aeval_eq_coeff (Ω := Ω) w (fun s : Free D N j0 => u s.1) (fun s => hu s.1) RT
    (aeval (subst x j0) P) α hα hmin
end GlobalTheory.GenSep
