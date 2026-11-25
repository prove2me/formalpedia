-- Prove2me | solution 1 for GlobalTheory.IdealResProd.vE_eq_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:55.836804+00:00
-- url     : https://prove2.me/submissions/d27a06e3-9ed6-4626-a45b-0d2581fbe888

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
import Theorems.Thm_GlobalTheory_IdealResProd_mem_span_iff
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramVal_exists_eq_zpow_mul_unit
import Theorems.Thm_GlobalTheory_UnramVal_vE_zpow_mul_unit
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
theorem _root_.solution (A : LocAt F E sig p) (L : LocE A.Fp A.Ep) {ϖ : 𝒪[A.Fp]} (hϖ : Irreducible ϖ)
    (I : Ideal (𝓞 F)) (hI : I ≠ 0) {c : A.Fp} (hc : c ≠ 0)
    (h : Submodule.span L.O ((fun x : 𝓞 F => A.ιE (algebraMap F E x)) '' (I : Set (𝓞 F))) =
      Submodule.span L.O {algebraMap A.Fp A.Ep c}) :
    vE L ϖ (algebraMap A.Fp A.Ep c) =
      ((Associates.mk p.asIdeal).count (Associates.mk I).factors : ℕ) := by
  haveI := A.lf
  obtain ⟨h0, h1⟩ := val_lt_one hϖ
  have hϖ0 : (ϖ : A.Fp) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  obtain ⟨k, u, rfl⟩ := GlobalTheory.UnramVal.exists_eq_zpow_mul_unit hϖ hc
  rw [GlobalTheory.UnramVal.vE_zpow_mul_unit L hϖ]
  have key : ∀ n : ℕ, n ≤ (Associates.mk p.asIdeal).count (Associates.mk I).factors ↔ (n : ℤ) ≤ k := by
    intro n
    rw [← le_pow_iff I hI]
    have e1 : (n : ℤ) ≤ k ↔ Submodule.span L.O {algebraMap A.Fp A.Ep ((ϖ : A.Fp) ^ k * ((u : 𝒪[A.Fp]) : A.Fp))}
        ≤ Submodule.span L.O {algebraMap A.Fp A.Ep ((ϖ : A.Fp) ^ n)} := by
      rw [Submodule.span_singleton_le_iff_mem, mem_span_iff A L (pow_ne_zero n hϖ0), map_mul, val_unit,
        mul_one, map_zpow₀, map_pow, ← zpow_natCast, zpow_le_zpow_iff_right_of_lt_one₀ h0 h1]
    rw [e1, ← h, Submodule.span_le, Set.image_subset_iff]
    refine forall₂_congr fun x _ => ?_
    rw [mem_pow_iff A hϖ, Set.mem_preimage, A.compat, SetLike.mem_coe,
      mem_span_iff A L (pow_ne_zero n hϖ0), map_pow]
  have hk : 0 ≤ k := by simpa using (key 0).1 (Nat.zero_le _)
  lift k to ℕ using hk
  have a := (key k).2 le_rfl
  have b := (key _).1 le_rfl
  omega
end GlobalTheory.IdealResProd
