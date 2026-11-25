-- Prove2me | solution 1 for GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:56:17.892915+00:00
-- url     : https://prove2.me/submissions/d5de380d-8e6d-4828-a56c-0b0897cf418c

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
import Theorems.Thm_GlobalTheory_CNorm_pIdx_of_ker_eq_range
import Theorems.Thm_GlobalTheory_CNorm_card_quot_span_algebraMap
import Theorems.Thm_GlobalTheory_CNorm_isAdicComplete_and_card_quotient_adicCompletionIntegers
import Theorems.Thm_GlobalTheory_CNorm_isAdicComplete_span_algebraMap_of_free_finite
import Theorems.Thm_GlobalTheory_CNorm_isIntegral_iff_valued_norm_le_one
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_QNorm_exists_uniformizer_and_residue_representatives
import Theorems.Thm_GlobalTheory_T_subgroupPowRelIndex_units_of_isAdicComplete
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
theorem _root_.solution (p : ℕ) (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (e : ℕ) (L : Type) [Field L] [Algebra (v.adicCompletion F) L]
    [FiniteDimensional (v.adicCompletion F) L] (hp : 0 < p)
    (he : v.valuation F (p : F) = WithZero.exp (-(e : ℤ))) :
    pTor p (⊤ : Subgroup Lˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Lˣ) =
      p * (Ideal.absNorm v.asIdeal ^ e) ^ Module.finrank (v.adicCompletion F) L *
        pTor p (⊤ : Subgroup Lˣ) := by
  letI : Algebra (v.adicCompletionIntegers F) L :=
    ((algebraMap (v.adicCompletion F) L).comp
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).toAlgebra
  haveI : IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  haveI : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap (v.adicCompletion F) L).injective
  have hinjRL : Function.Injective (algebraMap (v.adicCompletionIntegers F) L) :=
    (algebraMap (v.adicCompletion F) L).injective.comp Subtype.val_injective
  haveI : FaithfulSMul (v.adicCompletionIntegers F) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinjRL
  let O : Type := integralClosure (v.adicCompletionIntegers F) L
  haveI : Module.Finite (v.adicCompletionIntegers F) O :=
    IsIntegralClosure.finite (v.adicCompletionIntegers F) (v.adicCompletion F) L O
  haveI : Module.Free (v.adicCompletionIntegers F) O :=
    IsIntegralClosure.module_free (v.adicCompletionIntegers F) (v.adicCompletion F) L O
  have hrank : Module.finrank (v.adicCompletionIntegers F) O =
      Module.finrank (v.adicCompletion F) L :=
    IsIntegralClosure.rank (v.adicCompletionIntegers F) (v.adicCompletion F) L O
  obtain ⟨⟨π₀, -, hπ₀⟩, hval, -⟩ := exists_uniformizer_and_residue_representatives F v
  obtain ⟨hc, hcard⟩ := isAdicComplete_and_card_quotient_adicCompletionIntegers F v
  have hlt : (WithZero.exp (-1) : ℤᵐ⁰) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  let π : v.adicCompletionIntegers F := ⟨algebraMap F (v.adicCompletion F) π₀, by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hπ₀]; exact hlt.le⟩
  have hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1) := hπ₀
  have hπK : (π : v.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hπL : algebraMap (v.adicCompletion F) L π ≠ 0 := by
    simpa using hπK
  have hvp : Valued.v (((p : v.adicCompletionIntegers F)) : v.adicCompletion F) =
      WithZero.exp (-(e : ℤ)) := by
    rw [← he, ← hval]; simp
  have hq : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hπO : algebraMap (v.adicCompletionIntegers F) O π ≠ 0 := by
    intro h
    exact hπL (congrArg Subtype.val h)
  have hcomp := isAdicComplete_span_algebraMap_of_free_finite (v.adicCompletionIntegers F) O π
    (hc π (by rw [hπ]; exact hlt))
  have hc1 : Nat.card (O ⧸ Ideal.span {(p : O)}) =
      (Ideal.absNorm v.asIdeal ^ e) ^ Module.finrank (v.adicCompletion F) L := by
    have := card_quot_span_algebraMap (v.adicCompletionIntegers F) O (p : _)
    rw [map_natCast, hcard _ e hvp, hrank] at this
    exact this
  have hc2 : Nat.card (O ⧸ Ideal.span
      {(p : O) * algebraMap (v.adicCompletionIntegers F) O π}) ≠ 0 := by
    have := card_quot_span_algebraMap (v.adicCompletionIntegers F) O ((p : _) * π)
    rw [map_mul, map_natCast, hcard _ (e + 1) (by
      rw [MulMemClass.coe_mul, map_mul, hvp, hπ, ← WithZero.exp_add]
      congr 1; push_cast; ring)] at this
    rw [this]
    exact pow_ne_zero _ (pow_ne_zero _ hq)
  obtain ⟨u1, u2⟩ := GlobalTheory.T.subgroupPowRelIndex_units_of_isAdicComplete p O _ hp hπO hcomp hc2
  rw [hc1] at u2
  have hN : ∀ x : Lˣ, Valued.v (Algebra.norm (v.adicCompletion F) (x : L)) ≠ 0 := by
    intro x
    rw [Ne, map_eq_zero, Algebra.norm_eq_zero_iff]
    exact x.ne_zero
  let g : Lˣ →* Multiplicative ℤ :=
    { toFun := fun x => Multiplicative.ofAdd
        (WithZero.log (Valued.v (Algebra.norm (v.adicCompletion F) (x : L))))
      map_one' := by simp
      map_mul' := fun x y => by
        rw [Units.val_mul, map_mul, map_mul, WithZero.log_mul (hN x) (hN y), ofAdd_add] }
  have hg : ∀ x : Lˣ, g x = 1 ↔ Valued.v (Algebra.norm (v.adicCompletion F) (x : L)) = 1 := by
    intro x
    change Multiplicative.ofAdd (WithZero.log _) = 1 ↔ _
    rw [ofAdd_eq_one]
    constructor
    · intro h
      rw [← WithZero.exp_log (hN x), h, WithZero.exp_zero]
    · intro h
      rw [h, WithZero.log_one]
  have hmul : ∀ x : Lˣ, Valued.v (Algebra.norm (v.adicCompletion F) (x : L)) *
      Valued.v (Algebra.norm (v.adicCompletion F) ((x⁻¹ : Lˣ) : L)) = 1 := by
    intro x
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  let j : Oˣ →* Lˣ := Units.map ((integralClosure (v.adicCompletionIntegers F) L).val : O →* L)
  refine pIdx_of_ker_eq_range p hp j (Units.map_injective Subtype.val_injective) g ?_ ?_ _
    (pow_ne_zero _ (pow_ne_zero _ hq)) u1 u2
  · ext x
    rw [MonoidHom.mem_ker, hg]
    constructor
    · intro h
      have h' := hmul x
      rw [h, one_mul] at h'
      have i1 := (isIntegral_iff_valued_norm_le_one F v L (x : L)).2 h.le
      have i2 := (isIntegral_iff_valued_norm_le_one F v L ((x⁻¹ : Lˣ) : L)).2 h'.le
      exact ⟨⟨⟨x, i1⟩, ⟨(x⁻¹ : Lˣ), i2⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩,
        Units.ext rfl⟩
    · rintro ⟨u, rfl⟩
      have i1 := (isIntegral_iff_valued_norm_le_one F v L ((j u : Lˣ) : L)).1 (u : O).2
      have i2 := (isIntegral_iff_valued_norm_le_one F v L (((j u)⁻¹ : Lˣ) : L)).1
        ((u⁻¹ : Oˣ) : O).2
      exact eq_one_of_one_le_mul_left i1 i2 (hmul _).ge
  · intro h
    have h1 : g (Units.mk0 _ hπL) = 1 := by
      rw [← Subgroup.mem_bot, ← h]; exact ⟨_, rfl⟩
    rw [hg, Units.val_mk0, Algebra.norm_algebraMap, map_pow, hπ] at h1
    exact (pow_lt_one₀ zero_le' hlt Module.finrank_pos.ne').ne h1
end GlobalTheory.CNorm
