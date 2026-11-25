-- Prove2me | solution 1 for GlobalTheory.HL.StrongApprox.approxF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:24:22.559471+00:00
-- url     : https://prove2.me/submissions/e5b52954-7dc9-464e-a890-f1c4f3aa9bc3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
import Theorems.Thm_GlobalTheory_HL_StrongApprox_int_of
import Theorems.Thm_GlobalTheory_HL_StrongApprox_small
import Theorems.Thm_GlobalTheory_HL_StrongApprox_approx
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StrongApprox
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.StrongApprox
theorem _root_.solution (A : Places F E sig) (c : ∀ p, ((A.loc p).Fp)ˣ)
    (hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite)
    (y : ∀ p, (A.loc p).Fp) (hy : {p | y p ∉ 𝒪[(A.loc p).Fp]}.Finite) :
    ∃ x : F, ∀ p, ∃ o : 𝒪[(A.loc p).Fp], (A.loc p).ιF x - y p = c p * o := by

  obtain ⟨r, hr, hr'⟩ := small A hy.toFinset (fun p => (y p)⁻¹) (fun p hp => by
    have hp' : y p ∉ 𝒪[(A.loc p).Fp] := hy.mem_toFinset.mp hp
    exact inv_ne_zero fun h0 => hp' (h0 ▸ zero_mem _))
  have hrK : algebraMap (𝓞 F) F r ≠ 0 := by simpa using hr
  have hz : ∀ p, valuation (A.loc p).Fp ((A.loc p).ιF (algebraMap (𝓞 F) F r) * y p) ≤ 1 := by
    intro p
    rw [Valuation.map_mul]
    by_cases hp : y p ∈ 𝒪[(A.loc p).Fp]
    · exact mul_le_one' (int_of _ r) hp
    · have h1 := hr' p (hy.mem_toFinset.mpr hp)
      have hy0 : y p ≠ 0 := fun h0 => hp (h0 ▸ zero_mem _)
      have hy1 : valuation (A.loc p).Fp (y p) ≠ 0 := by simpa using hy0
      rw [map_inv₀] at h1
      calc _ ≤ (valuation (A.loc p).Fp (y p))⁻¹ * valuation (A.loc p).Fp (y p) := mul_le_mul' h1 le_rfl
        _ = 1 := inv_mul_cancel₀ hy1

  have hr0 : {p : HeightOneSpectrum (𝓞 F) | p.valuation F (algebraMap (𝓞 F) F r) < 1}.Finite := by
    refine (HeightOneSpectrum.Support.finite (𝓞 F) (algebraMap (𝓞 F) F r)⁻¹).subset fun p hp => ?_
    have hp' : p.valuation F (algebraMap (𝓞 F) F r) < 1 := hp
    show 1 < p.valuation F (algebraMap (𝓞 F) F r)⁻¹
    rw [map_inv₀]
    exact one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hrK), hp'⟩
  obtain ⟨h, hh, hh'⟩ := small A (hc.union hr0).toFinset
    (fun p => (A.loc p).ιF (algebraMap (𝓞 F) F r) * c p) (fun p _ => mul_ne_zero (by simpa using hrK) (c p).ne_zero)
  obtain ⟨a, ha⟩ := approx A _ hz h hh
  refine ⟨algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F r, fun p => ?_⟩
  set v := valuation (A.loc p).Fp
  have hrp : (A.loc p).ιF (algebraMap (𝓞 F) F r) ≠ 0 := by simpa using hrK
  have hvr : v ((A.loc p).ιF (algebraMap (𝓞 F) F r)) ≠ 0 := by simpa using hrp
  have hcv : v (c p : (A.loc p).Fp) ≠ 0 := by simpa using (c p).ne_zero

  have key : v ((A.loc p).ιF (algebraMap (𝓞 F) F h)) ≤ v ((A.loc p).ιF (algebraMap (𝓞 F) F r) * c p) := by
    by_cases hp : p ∈ (hc.union hr0).toFinset
    · exact hh' p hp
    · rw [Set.Finite.mem_toFinset, Set.mem_union, not_or] at hp
      obtain ⟨u, hu⟩ := not_not.mp hp.1
      have hu1 : v (c p : (A.loc p).Fp) = 1 := by
        rw [← hu]
        exact (Valuation.integer.integers v).one_of_isUnit u.isUnit
      have hr1 : v ((A.loc p).ιF (algebraMap (𝓞 F) F r)) = 1 := by
        refine le_antisymm (int_of _ r) ?_
        have := (PlacesInt.val_le_iff (A.loc p) 1 (algebraMap (𝓞 F) F r)).2 (not_lt.mp hp.2 |>.trans_eq' (by simp))
        simpa using this
      rw [Valuation.map_mul, hu1, hr1, mul_one]
      exact int_of _ h
  set d := (A.loc p).ιF (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F r) - y p
  have hd : d = -((A.loc p).ιF (algebraMap (𝓞 F) F r) * y p - (A.loc p).ιF (algebraMap (𝓞 F) F a)) *
      ((A.loc p).ιF (algebraMap (𝓞 F) F r))⁻¹ := by
    simp only [d, map_div₀]; field_simp; ring
  have hdv : v d ≤ v (c p : (A.loc p).Fp) := by
    rw [hd, Valuation.map_mul, Valuation.map_neg, map_inv₀]
    have := (ha p).trans key
    rw [Valuation.map_mul] at this
    calc _ ≤ v ((A.loc p).ιF (algebraMap (𝓞 F) F r)) * v (c p : (A.loc p).Fp) *
          (v ((A.loc p).ιF (algebraMap (𝓞 F) F r)))⁻¹ := mul_le_mul' this le_rfl
      _ = v (c p : (A.loc p).Fp) := by field_simp
  refine ⟨⟨(c p : (A.loc p).Fp)⁻¹ * d, ?_⟩, ?_⟩
  · show v ((c p : (A.loc p).Fp)⁻¹ * d) ≤ 1
    rw [Valuation.map_mul, map_inv₀]
    calc _ ≤ (v (c p : (A.loc p).Fp))⁻¹ * v (c p : (A.loc p).Fp) := mul_le_mul' le_rfl hdv
      _ = 1 := inv_mul_cancel₀ hcv
  · show d = c p * ((c p : (A.loc p).Fp)⁻¹ * d)
    rw [← mul_assoc, mul_inv_cancel₀ (c p).ne_zero, one_mul]
end GlobalTheory.HL.StrongApprox
