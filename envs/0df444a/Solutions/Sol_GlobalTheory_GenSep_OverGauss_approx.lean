-- Prove2me | solution 1 for GlobalTheory.GenSep.OverGauss.approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:23:36.924825+00:00
-- url     : https://prove2.me/submissions/fdc7f2f8-bccb-4ffc-b390-1cda064d9862

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


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
    (h : OverGauss la φ κ x w ι e) {ϖ : la.adicCompletionIntegers K}
    (hϖ : ϖ ∈ maximalIdeal (la.adicCompletionIntegers K)) (n : ℤ) {c : la.adicCompletion K} {a : K}
    {o : la.adicCompletionIntegers K}
    (hc : c - algebraMap K (la.adicCompletion K) a = ((ϖ ^ n.natAbs : la.adicCompletionIntegers K) : la.adicCompletion K) * o) :
    (n : WithTop ℤ) ≤ w (e (κ c) - ι (algebraMap K Ω a)) := by
  classical
  rw [h.2.2.1, ← map_sub, ← map_sub, hc, map_mul, map_mul, hκ, hκ]
  have h1 : ((1 : ℤ) : WithTop ℤ) ≤ w (e (φ (C ϖ))) := by
    have : 0 < w (e (φ (C ϖ))) := (h.2.1 _).2 fun α => by
      rw [coeff_C]; split_ifs
      · exact hϖ
      · exact Ideal.zero_mem _
    induction hh : w (e (φ (C ϖ))) using WithTop.recTopCoe with
    | top => exact le_top
    | coe m =>
      rw [hh] at this
      have : (0 : ℤ) < m := by exact_mod_cast this
      exact WithTop.coe_le_coe.2 (by omega)
  have h2 : ∀ m : ℕ, ((m : ℤ) : WithTop ℤ) ≤ w (e (φ (C (ϖ ^ m)))) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, map_mul, map_mul, map_mul]
      exact le_mul_of w ih h1 (by push_cast; omega)
  exact le_mul_of w (b := 0) (h2 _) (h.1 _) (by omega)
end OverGauss
end GlobalTheory.GenSep
