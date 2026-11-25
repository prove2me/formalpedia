-- Prove2me | solution 1 for GlobalTheory.IdealResProd.discr_and_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:49.971906+00:00
-- url     : https://prove2.me/submissions/bf4b4b50-5817-48d9-a5f1-8d73527f8897

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AbsNormEqFinprod
import Theorems.Thm_GlobalTheory_IdealResProd_val_unit
import Theorems.Thm_GlobalTheory_IdealResProd_mem_pow_iff
import Theorems.Thm_GlobalTheory_IdealResProd_le_pow_iff
import Theorems.Thm_GlobalTheory_IdealResProd_val_lt_one
import Theorems.Thm_GlobalTheory_IdealResProd_vE_eq_count
import Theorems.Thm_GlobalTheory_IdealResProd_absNorm_eq_finprod
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_PlacesInt_integers_local
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
open GlobalTheory GlobalTheory.IdealResProd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
variable {p : HeightOneSpectrum (𝓞 F)}
namespace GlobalTheory.IdealResProd
theorem _root_.solution : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ ϖ : ∀ p, 𝒪[(A.loc p).Fp], (∀ p, Irreducible (ϖ p)) → (∀ c : ∀ p, ((A.loc p).Fp)ˣ, (∀ p, Submodule.span (A.L p).O ((fun x : 𝓞 F => (A.loc p).ιE (algebraMap F E x)) '' (differentIdeal ℤ (𝓞 F) : Set (𝓞 F))) = Submodule.span (A.L p).O {algebraMap (A.loc p).Fp (A.loc p).Ep (c p)}) → ∏ᶠ p, (resQ (ϖ p) : ℝ) ^ vE (A.L p) (ϖ p) (algebraMap (A.loc p).Fp (A.loc p).Ep (c p)) = |(NumberField.discr F : ℝ)|) ∧ ∀ g : ℕ, g ≠ 0 → (∀ p : HeightOneSpectrum (𝓞 F), (g : 𝓞 F) ∈ p.asIdeal → ∃ u : (𝒪[(A.loc p).Fp])ˣ, (g : (A.loc p).Fp) = ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) * (ϖ p : (A.loc p).Fp)) → ∏ᶠ p : HeightOneSpectrum (𝓞 F), (if (g : 𝓞 F) ∈ p.asIdeal then (resQ (ϖ p) : ℝ) else 1) = (g : ℝ) ^ Module.finrank ℚ F := by
  intro F E _ _ _ _ _ sig A ϖ hϖ
  have hq : ∀ p, resQ (ϖ p) = Ideal.absNorm p.asIdeal := fun p => (GlobalTheory.HL.PlacesInt.integers_local A).2.2.2 p _ (hϖ p)
  refine ⟨fun c hc => ?_, fun g hg hu => ?_⟩
  · have hI : differentIdeal ℤ (𝓞 F) ≠ 0 := by
      intro h
      have := absNorm_differentIdeal F (𝓞 F)
      rw [h, map_zero] at this
      exact discr_ne_zero F (Int.natAbs_eq_zero.1 this.symm)
    have := absNorm_eq_finprod _ hI
    rw [absNorm_differentIdeal F (𝓞 F), Nat.cast_natAbs, Int.cast_abs] at this
    rw [← this]
    refine finprod_congr fun p => ?_
    rw [vE_eq_count (A.loc p) (A.L p) (hϖ p) _ hI (c p).ne_zero (hc p), zpow_natCast, hq]
  · have hg' : (g : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hg
    have hI : Ideal.span {(g : 𝓞 F)} ≠ 0 := by simpa using hg
    have := absNorm_eq_finprod _ hI
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Nat.cast_pow] at this
    rw [← this]
    refine finprod_congr fun p => ?_
    have key := le_pow_iff (p := p) _ hI
    simp only [Ideal.span_singleton_le_iff_mem] at key
    split_ifs with h
    · obtain ⟨u, hu⟩ := hu p h
      obtain ⟨h0, h1⟩ := val_lt_one (hϖ p)
      have a := (key 1).1 (by simpa using h)
      have b : ¬ (g : 𝓞 F) ∈ p.asIdeal ^ 2 := by
        rw [mem_pow_iff (A.loc p) (hϖ p)]
        have e : (A.loc p).ιF ((g : 𝓞 F) : F) = (g : (A.loc p).Fp) := by simp
        rw [e, hu, map_mul, val_unit, one_mul, not_le]
        calc _ < valuation (A.loc p).Fp (ϖ p) ^ 1 := pow_lt_pow_right_of_lt_one₀ h0 h1 (by norm_num)
          _ = _ := pow_one _
      rw [key] at b
      have : (Associates.mk p.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 F)})).factors = 1 := by omega
      rw [this, pow_one, hq]
    · have b : ¬ (g : 𝓞 F) ∈ p.asIdeal ^ 1 := by simpa using h
      rw [key] at b
      have : (Associates.mk p.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 F)})).factors = 0 := by omega
      rw [this, pow_zero]
end GlobalTheory.IdealResProd
