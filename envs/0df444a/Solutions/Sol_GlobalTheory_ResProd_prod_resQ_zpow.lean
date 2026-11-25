-- Prove2me | solution 1 for GlobalTheory.ResProd.prod_resQ_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:07:45.337902+00:00
-- url     : https://prove2.me/submissions/927b0d01-05f0-41c9-8f1d-35a257bb14e3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ProdResQZpow
import Theorems.Thm_GlobalTheory_ResProd_vE_eq_neg_log
import Theorems.Thm_GlobalTheory_ResProd_place_eq_zpow
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_PlacesInt_resQ_eq_absNorm
import Theorems.Thm_GlobalTheory_HL_PlacesInt_val_le_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.ResProd
namespace GlobalTheory.ResProd
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ ϖ : ∀ p, 𝒪[(A.loc p).Fp], (∀ p, Irreducible (ϖ p)) → ∀ x : F, x ≠ 0 → {p | vE (A.L p) (ϖ p) (algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF x)) ≠ 0}.Finite ∧ ∏ᶠ p, (resQ (ϖ p) : ℝ) ^ vE (A.L p) (ϖ p) (algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF x)) = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  intro F E _ _ _ _ _ sig A ϖ hϖ x hx

  have key : ∀ p, vE (A.L p) (ϖ p) (algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF x)) =
      -WithZero.log (p.valuation F x) := fun p => by
    haveI := (A.loc p).lf
    exact vE_eq_neg_log p (A.L p) (A.loc p).ιF (A.loc p).dense
      (GlobalTheory.HL.PlacesInt.val_le_iff (A.loc p)) (hϖ p) hx
  have hterm : ∀ p, (resQ (ϖ p) : ℝ) ^ vE (A.L p) (ϖ p)
      (algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF x)) =
      (NumberField.FinitePlace.equivHeightOneSpectrum.symm p x)⁻¹ := fun p => by
    rw [key, GlobalTheory.HL.PlacesInt.resQ_eq_absNorm (A.loc p) (ϖ p) (hϖ p), place_eq_zpow p hx, zpow_neg]
  have hfin : (Function.mulSupport fun w : NumberField.FinitePlace F => w x).Finite :=
    NumberField.FinitePlace.hasFiniteMulSupport hx
  constructor
  · refine (hfin.image NumberField.FinitePlace.equivHeightOneSpectrum).subset ?_
    intro p hp
    refine ⟨NumberField.FinitePlace.equivHeightOneSpectrum.symm p, ?_, by simp⟩
    simp only [Set.mem_setOf_eq, key] at hp
    rw [Function.mem_mulSupport, place_eq_zpow p hx]
    intro h1
    have hgt : (1 : ℝ) < Ideal.absNorm p.asIdeal := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
    rw [zpow_eq_one_iff_right₀ (by positivity) hgt.ne'] at h1
    exact hp (by rw [h1, neg_zero])
  · simp_rw [hterm]
    rw [finprod_inv_distrib,
      finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm (f := fun w => w x),
      NumberField.FinitePlace.prod_eq_inv_abs_norm hx]
    push_cast
    simp
end GlobalTheory.ResProd
