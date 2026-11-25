-- Prove2me | solution 1 for GlobalTheory.ResProd.vE_eq_neg_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:05:53.255669+00:00
-- url     : https://prove2.me/submissions/41cabfe7-5651-4465-81bc-e6d01af61377

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
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_LocSplit_exists_irreducible
import Theorems.Thm_GlobalTheory_UnramVal_exists_eq_zpow_mul_unit
import Theorems.Thm_GlobalTheory_UnramVal_vE_zpow_mul_unit
import Theorems.Thm_GlobalTheory_UnramVal_zpow_mul_unit_mem_iff
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
theorem _root_.solution {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {E : Type} [CommRing E] [Algebra K E] [TopologicalSpace E] (L : LocE K E)
    (ι : F →+* K) (hd : DenseRange ι)
    (hv : ∀ x y : F, valuation K (ι x) ≤ valuation K (ι y) ↔ p.valuation F x ≤ p.valuation F y)
    {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {x : F} (hx : x ≠ 0) :
    vE L ϖ (algebraMap K E (ι x)) = -WithZero.log (p.valuation F x) := by
  have hιx : ι x ≠ 0 := (map_ne_zero ι).mpr hx
  obtain ⟨k, u, hku⟩ := GlobalTheory.UnramVal.exists_eq_zpow_mul_unit hϖ hιx
  rw [hku, GlobalTheory.UnramVal.vE_zpow_mul_unit L hϖ k u]

  obtain ⟨g, hg⟩ := p.valuation_exists_uniformizer F
  obtain ⟨q, hq, hqg⟩ := GlobalTheory.LocSplit.exists_irreducible p ι hd hv g hg
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.associated_of_irreducible 𝒪[K] hϖ hq
  have h0 : p.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  set n := WithZero.log (p.valuation F x) with hn
  have hvx : p.valuation F x = WithZero.exp n := (WithZero.exp_log h0).symm

  have hone : p.valuation F (x * g ^ n) = 1 := by
    rw [map_mul, map_zpow₀, hvx, hg, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hunit : ∀ v : (𝒪[K])ˣ, valuation K ((v : 𝒪[K]) : K) = 1 := fun v =>
    (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp v.isUnit
  have hϖ0 : valuation K (ϖ : K) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact_mod_cast hϖ.ne_zero
  have hvq : valuation K (ι g) = valuation K (ϖ : K) := by
    rw [← hqg, ← hw]
    push_cast
    rw [map_mul, hunit, mul_one]

  have hvz : valuation K (ι (x * g ^ n)) = 1 := by
    apply le_antisymm
    · simpa using (hv (x * g ^ n) 1).mpr (by rw [hone, map_one])
    · simpa using (hv 1 (x * g ^ n)).mpr (by rw [hone, map_one])
  simp only [map_mul, map_zpow₀, hku, hunit, mul_one, hvq] at hvz
  rw [← zpow_add₀ hϖ0] at hvz

  have hle := (GlobalTheory.UnramVal.zpow_mul_unit_mem_iff hϖ (k + n) 1).mp (by
    rw [Valuation.mem_integer_iff]
    simp only [Units.val_one, OneMemClass.coe_one, mul_one, map_zpow₀, hvz, le_refl])
  have hge := (GlobalTheory.UnramVal.zpow_mul_unit_mem_iff hϖ (-(k + n)) 1).mp (by
    rw [Valuation.mem_integer_iff]
    simp only [Units.val_one, OneMemClass.coe_one, mul_one, map_zpow₀, zpow_neg, map_inv₀, hvz, inv_one,
      le_refl])
  omega
end GlobalTheory.ResProd
