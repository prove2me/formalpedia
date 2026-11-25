-- Prove2me | solution 1 for GlobalTheory.QuadraticValuationIndexTwo.exists_subgroup_index_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:31:39.067793+00:00
-- url     : https://prove2.me/submissions/f9ab3dd4-b8d1-4fbb-9182-c03167f0818e

import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsKum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CyclicKummerNormFixedHilbert90
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PIdxUnitsFiniteExtensionAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSubgroupIndexTwo
import Theorems.Thm_GlobalTheory_QuadraticValuationIndexTwo_exists_mul_conj_iff
import Theorems.Thm_GlobalTheory_QuadraticValuationIndexTwo_exists_valuation_two
import Theorems.Thm_GlobalTheory_CNorm_dif_apply
import Theorems.Thm_GlobalTheory_CNorm_exists_isKum
import Theorems.Thm_GlobalTheory_CNorm_herbrand_prime_order
import Theorems.Thm_GlobalTheory_CNorm_kummer_basic
import Theorems.Thm_GlobalTheory_CNorm_mem_fix
import Theorems.Thm_GlobalTheory_CNorm_nrm_apply
import Theorems.Thm_GlobalTheory_CNorm_pIdx_range_of_injective
import Theorems.Thm_GlobalTheory_CNorm_pIdx_units_finite_extension_adicCompletion
import Theorems.Thm_GlobalTheory_CNorm_pTor_range_of_injective
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_Nm_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CNorm GlobalTheory.QuadSymbol.NormIndex
open GlobalTheory GlobalTheory.QuadraticValuationIndexTwo
namespace GlobalTheory.QuadraticValuationIndexTwo
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (B : Type) [Field B] [Algebra (v.adicCompletion F) B]
    [FiniteDimensional (v.adicCompletion F) B] (d : B) (hd : ¬ IsSquare d) :
    ∃ N : Subgroup Bˣ, N.index = 2 ∧ ∀ x : Bˣ, x ∈ N ↔ Nm d (x : B) := by
  set K := v.adicCompletion F
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have : CharZero B := charZero_of_injective_algebraMap (algebraMap K B).injective
  have hnp : ∀ r : B, r ^ 2 ≠ d := fun r hr => hd ⟨r, by rw [← hr, sq]⟩

  obtain ⟨E, _, _, θ, σ, hK⟩ :=
    GlobalTheory.CNorm.exists_isKum 2 B (-1) d Nat.prime_two (IsPrimitiveRoot.neg_one 0 (by norm_num)) hnp
  have kb := GlobalTheory.CNorm.kummer_basic 2 B E (-1) d θ σ hK
  have : FiniteDimensional B E := kb.1
  let : Algebra K E := ((algebraMap B E).comp (algebraMap K B)).toAlgebra
  have : IsScalarTower K B E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FiniteDimensional K E := Module.Finite.trans B E
  obtain ⟨e, he⟩ := exists_valuation_two F v
  have hB := GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion 2 F v e B (by norm_num) he
  have hE := GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion 2 F v e E (by norm_num) he
  let σ' : Eˣ →* Eˣ := Units.map (σ : E →+* E).toMonoidHom
  let j : Bˣ →* Eˣ := Units.map (algebraMap B E).toMonoidHom
  have hσ' : ∀ y : Eˣ, ((σ' y : Eˣ) : E) = σ (y : E) := fun y => rfl
  have hj' : ∀ x : Bˣ, ((j x : Eˣ) : E) = algebraMap B E (x : B) := fun x => rfl
  have hj : Function.Injective j := fun a b hab =>
    Units.ext ((algebraMap B E).injective (by rw [← hj', ← hj', hab]))
  have hσ'2 : ∀ a, σ'^[2] a = a := fun a => Units.ext (kb.2.2.1 (a : E))

  have hfix : GlobalTheory.CNorm.fix σ' = j.range := by
    ext x
    rw [GlobalTheory.CNorm.mem_fix, MonoidHom.mem_range]
    constructor
    · intro hx
      have hx' : σ (x : E) = x := by rw [← hσ', hx]
      obtain ⟨a, ha⟩ := kb.2.2.2.1 (x : E) hx'
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact x.ne_zero (by rw [ha, map_zero])
      exact ⟨Units.mk0 a ha0, Units.ext (by rw [hj', Units.val_mk0, ha])⟩
    · rintro ⟨b, rfl⟩
      exact Units.ext (by rw [hσ', hj', AlgEquiv.commutes])
  have hnrm : ∀ y : Eˣ, ((GlobalTheory.CNorm.nrm σ' 2 y : Eˣ) : E) = (y : E) * σ y := by
    intro y
    rw [GlobalTheory.CNorm.nrm_apply, Finset.prod_range_succ, Finset.prod_range_one]
    rfl

  have hker : (GlobalTheory.CNorm.nrm σ' 2).ker ≤ (GlobalTheory.CNorm.dif σ').range := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : ∏ i ∈ Finset.range 2, σ^[i] (y : E) = 1 := by
      rw [Finset.prod_range_succ, Finset.prod_range_one]
      have := congrArg Units.val hy
      rw [hnrm] at this
      exact this
    obtain ⟨z, hz0, hz⟩ := kb.2.2.2.2.1 (y : E) h1
    refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
    rw [GlobalTheory.CNorm.dif_apply, Units.val_div_eq_div_val, hσ', Units.val_mk0, hz]
  have hR2 : (GlobalTheory.CNorm.dif σ').range.relIndex (GlobalTheory.CNorm.nrm σ' 2).ker = 1 :=
    Subgroup.relIndex_eq_one.mpr hker
  have hq : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hIE : GlobalTheory.CNorm.pIdx 2 (⊤ : Subgroup Eˣ) ≠ 0 := by
    rw [hE.2]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (pow_ne_zero _ hq))) hE.1

  obtain ⟨-, -, -, -, heq⟩ := GlobalTheory.CNorm.herbrand_prime_order 2 Eˣ σ' Nat.prime_two hσ'2 hIE hE.1
  rw [hfix, hR2, GlobalTheory.CNorm.pIdx_range_of_injective 2 j hj, GlobalTheory.CNorm.pTor_range_of_injective 2 j hj,
    hE.2, hB.2] at heq
  have hrank : Module.finrank K E = Module.finrank K B * 2 := by
    rw [← Module.finrank_mul_finrank K B E, kb.2.1]
  rw [hrank, pow_mul] at heq
  set Q := (Ideal.absNorm v.asIdeal ^ e) ^ Module.finrank K B
  set TE := GlobalTheory.CNorm.pTor 2 (⊤ : Subgroup Eˣ)
  set TB := GlobalTheory.CNorm.pTor 2 (⊤ : Subgroup Bˣ)
  set R := (GlobalTheory.CNorm.nrm σ' 2).range.relIndex j.range
  have hX : Q ^ 2 * TE * TB ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ hq))) hE.1)
      (pow_ne_zero _ hB.1)
  have hR : R = 2 := by
    have h4 : (R * 2) * (Q ^ 2 * TE * TB ^ 2) = 4 * (Q ^ 2 * TE * TB ^ 2) := by
      have e21 : (2 : ℕ) - 1 = 1 := rfl
      rw [e21, pow_one, one_pow, one_mul] at heq
      calc (R * 2) * (Q ^ 2 * TE * TB ^ 2) = R * (2 * Q ^ 2 * TE) * TB ^ 2 := by ring
        _ = TE * (2 * Q * TB) ^ 2 := heq
        _ = 4 * (Q ^ 2 * TE * TB ^ 2) := by ring
    have := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hX) h4
    omega
  refine ⟨(GlobalTheory.CNorm.nrm σ' 2).range.comap j, ?_, ?_⟩
  · rw [Subgroup.index_comap]
    exact hR
  · intro x
    rw [Subgroup.mem_comap, MonoidHom.mem_range, ← exists_mul_conj_iff hK (x : B)]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨(y : E), ?_⟩
      rw [← hnrm, hy, hj']
    · rintro ⟨y, hy⟩
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hy
        exact x.ne_zero ((algebraMap B E).injective (by rw [← hy, map_zero]))
      refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
      rw [hnrm, hj', Units.val_mk0]
      exact hy
end GlobalTheory.QuadraticValuationIndexTwo
