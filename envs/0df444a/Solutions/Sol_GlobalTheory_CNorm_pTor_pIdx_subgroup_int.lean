-- Prove2me | solution 1 for GlobalTheory.CNorm.pTor_pIdx_subgroup_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:50:28.092213+00:00
-- url     : https://prove2.me/submissions/a212dd98-14ca-4cdc-9b18-2084931e7458

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexTopOfGroupFg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CardQuotSpanAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteSpanAlgebraMapOfFreeFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormCoeffMinpolyLeOneOfNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexUnitsOfIsAdicCompleteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
import Theorems.Thm_GlobalTheory_CNorm_pIdx_range_of_injective
import Theorems.Thm_GlobalTheory_CNorm_pIdx_top_of_fg
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution (p : ℕ) (hp : 0 < p) (H : Subgroup (Multiplicative ℤ))
    (hH : H ≠ ⊥) : pTor p H = 1 ∧ pIdx p H = p := by
  have htor : ∀ U : Subgroup (Multiplicative ℤ), pTor p U = 1 := by
    intro U
    unfold pTor
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, U.one_mem, one_pow _⟩⟩⟩
    rw [(pow_eq_one_iff_left hp.ne').1 x.2.2, (pow_eq_one_iff_left hp.ne').1 y.2.2]
  refine ⟨htor H, ?_⟩
  obtain ⟨d, hd⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).1 inferInstance
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hH (by rw [← hd, Subgroup.zpowers_one_eq_bot])
  have hr : H = (zpowersHom (Multiplicative ℤ) d).range := by
    rw [← hd]; rfl
  have hinj : Function.Injective (zpowersHom (Multiplicative ℤ) d) := by
    intro a b h
    simp only [zpowersHom_apply] at h
    have h2 := congrArg Multiplicative.toAdd h
    simp only [toAdd_zpow, smul_eq_mul] at h2
    have hd0 : d.toAdd ≠ 0 := fun h0 => hd1 (by simpa using h0)
    exact Multiplicative.toAdd.injective (mul_right_cancel₀ hd0 h2)
  rw [hr, pIdx_range_of_injective p _ hinj]
  have h := (pIdx_top_of_fg p (Multiplicative ℤ) hp).2
  have hf : Module.finrank ℤ (Additive (Multiplicative ℤ)) = 1 := by
    rw [(AddEquiv.additiveMultiplicative ℤ).toIntLinearEquiv.finrank_eq]
    exact Module.finrank_self ℤ
  rw [h, htor, hf, pow_one, mul_one]
end GlobalTheory.CNorm
