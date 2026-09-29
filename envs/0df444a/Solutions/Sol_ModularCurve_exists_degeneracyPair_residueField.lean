-- Prove2me | solution 1 for ModularCurve.exists_degeneracyPair_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/4be2b5f4-745b-5984-82e5-8856b30eb352

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_heckeAlphaCIntegral_unconditional
import Theorems.Thm_ModularCurve_heckeBetaCIntegral_unconditional
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_relfinrank_modularFunctionFieldFullC_mul_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_degeneracyPair_residueField
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false

open AlgebraicCurve IsLocalRing ModularCurve

namespace DegeneracyPairResidueSol

private theorem fullC_eq_C (k : Type*) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (n : ℕ) [NeZero n] (hℓn : ¬ ℓ ∣ n) :
    modularFunctionFieldFullC k n = modularFunctionFieldC k n := by

  have hF1 : modularFunctionFieldFullC k 1 =
      IntermediateField.adjoin k {(jqModC k : LaurentSeries k)} := by
    apply le_antisymm
    · rw [modularFunctionFieldFullC, IntermediateField.adjoin_le_iff]
      rintro x ⟨d, _, hd, rfl⟩
      obtain rfl : d = 1 := Nat.dvd_one.mp hd
      rw [qExpand_one_apply]
      exact IntermediateField.subset_adjoin k _ (Set.mem_singleton _)
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact jqModC_mem_full k 1

  have hFn : ∀ {m m' : ℕ} [NeZero m] [NeZero m'], m = m' →
      modularFunctionFieldFullC k m = modularFunctionFieldFullC k m' := by
    intro m m' _ _ h
    subst h
    rfl
  have hcast : ((1 * n : ℕ) : k) ≠ 0 := by
    rw [one_mul]
    exact fun h => hℓn ((CharP.cast_eq_zero_iff k ℓ n).mp h)

  have hdeg := (relfinrank_modularFunctionFieldFullC_mul_dedekindPsi k 1 n hcast).1
  rw [hFn (one_mul n), hF1, dedekindPsi_one, mul_one, one_mul] at hdeg

  have hC : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k n) = dedekindPsi n :=
    relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k n ℓ hℓn
  have hle : modularFunctionFieldC k n ≤ modularFunctionFieldFullC k n :=
    modularFunctionFieldC_le_full k n
  have hA0C : IntermediateField.adjoin k {(jqModC k : LaurentSeries k)} ≤
      modularFunctionFieldC k n := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact jqModC_mem k n

  have htower := IntermediateField.relfinrank_mul_relfinrank
    (A := IntermediateField.adjoin k {(jqModC k : LaurentSeries k)})
    (B := modularFunctionFieldC k n) (C := modularFunctionFieldFullC k n) hA0C hle
  rw [hC, hdeg] at htower
  have hψ : dedekindPsi n ≠ 0 := (dedekindPsi_pos n (NeZero.ne n)).ne'
  have h1 : (modularFunctionFieldC k n).relfinrank (modularFunctionFieldFullC k n) = 1 :=
    mul_left_cancel₀ hψ (htower.trans (mul_one _).symm)
  exact le_antisymm
    ((IntermediateField.relfinrank_eq_one_iff (A := modularFunctionFieldC k n)
      (B := modularFunctionFieldFullC k n)).mp h1) hle

private theorem roof_le_C (k : Type*) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (M s : ℕ) [NeZero M] [NeZero s] (hℓ : ¬ ℓ ∣ M * s) :
    charLDegeneracyRoof k M s ≤ modularFunctionFieldC k (M * s) :=
  ((charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k ℓ M s hℓ).trans
    (fullC_eq_C k ℓ (M * s) hℓ)).le

private noncomputable def legsC (k : Type*) [Field k] (M s : ℕ) [NeZero M] [NeZero s]
    (hle : charLDegeneracyRoof k M s ≤ modularFunctionFieldC k (M * s)) :
    Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))) :=
  ![(IntermediateField.inclusion hle).comp (heckeAlphaC k M s),
    (IntermediateField.inclusion hle).comp (heckeBetaC k M s)]

private theorem legsC_zero (k : Type*) [Field k] (M s : ℕ) [NeZero M] [NeZero s]
    (hle : charLDegeneracyRoof k M s ≤ modularFunctionFieldC k (M * s)) :
    legsC k M s hle 0 = (IntermediateField.inclusion hle).comp (heckeAlphaC k M s) :=
  rfl

private theorem legsC_one (k : Type*) [Field k] (M s : ℕ) [NeZero M] [NeZero s]
    (hle : charLDegeneracyRoof k M s ≤ modularFunctionFieldC k (M * s)) :
    legsC k M s hle 1 = (IntermediateField.inclusion hle).comp (heckeBetaC k M s) :=
  rfl

private theorem legsC_coe_zero (k : Type*) [Field k] (M s : ℕ) [NeZero M] [NeZero s]
    (hle : charLDegeneracyRoof k M s ≤ modularFunctionFieldC k (M * s))
    (x : ↥(modularFunctionFieldC k M)) :
    ((legsC k M s hle 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x := by
  have h : legsC k M s hle 0 x = IntermediateField.inclusion hle (heckeAlphaC k M s x) := rfl
  exact (congrArg Subtype.val h).trans
    ((IntermediateField.coe_inclusion hle _).trans (coe_heckeAlphaC (k := k) (N := M) (q := s) x))

private theorem legsC_coe_one (k : Type*) [Field k] (M s : ℕ) [NeZero M] [NeZero s]
    (hle : charLDegeneracyRoof k M s ≤ modularFunctionFieldC k (M * s))
    (x : ↥(modularFunctionFieldC k M)) :
    ((legsC k M s hle 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) =
      qExpand k s x := by
  have h : legsC k M s hle 1 x = IntermediateField.inclusion hle (heckeBetaC k M s x) := rfl
  exact (congrArg Subtype.val h).trans
    ((IntermediateField.coe_inclusion hle _).trans (coe_heckeBetaC (k := k) (N := M) (q := s) x))

private theorem legsC_isIntegral (k : Type*) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (M s : ℕ) [NeZero M] [NeZero s] (hℓ : ¬ ℓ ∣ M * s) (i : Fin 2) :
    (legsC k M s (roof_le_C k ℓ M s hℓ) i).toRingHom.IsIntegral := by
  have hge : modularFunctionFieldC k (M * s) ≤ charLDegeneracyRoof k M s :=
    ((charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k ℓ M s hℓ).trans
      (fullC_eq_C k ℓ (M * s) hℓ)).ge
  have hsurjι : Function.Surjective
      (IntermediateField.inclusion (roof_le_C k ℓ M s hℓ)).toRingHom := fun y =>
    ⟨⟨(y : LaurentSeries k), hge y.2⟩, Subtype.ext rfl⟩
  have hαI : (heckeAlphaC k M s).toRingHom.IsIntegral := heckeAlphaCIntegral_unconditional k M s
  have hβI : (heckeBetaC k M s).toRingHom.IsIntegral := heckeBetaCIntegral_unconditional k M s
  fin_cases i
  · exact RingHom.IsIntegral.trans _ _ hαI (RingHom.isIntegral_of_surjective _ hsurjι)
  · exact RingHom.IsIntegral.trans _ _ hβI (RingHom.isIntegral_of_surjective _ hsurjι)

private theorem exists_pair (k : Type*) [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (M s : ℕ) [NeZero M] [NeZero s] (hℓ : ¬ ℓ ∣ M * s) :
    ∃ (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (_ : ∀ i, (φ i).toRingHom.IsIntegral),
      (∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x) ∧
      (∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x) :=
  ⟨legsC k M s (roof_le_C k ℓ M s hℓ), legsC_isIntegral k ℓ M s hℓ,
    legsC_coe_zero k M s _, legsC_coe_one k M s _⟩

end DegeneracyPairResidueSol

open DegeneracyPairResidueSol in

theorem solution (M s q' : ℕ) [NeZero M] [NeZero s] (hq' : q'.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q') (hq'Ms : ¬ q' ∣ M * s) :
    haveI : NeZero q' := ⟨hq'.ne_zero⟩
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    ∃ (φ : Fin 2 → (↥(modularFunctionFieldC (ResidueField A) M) →ₐ[ResidueField A]
        ↥(modularFunctionFieldC (ResidueField A) (M * s))))
      (_ : ∀ i, (φ i).toRingHom.IsIntegral),
      (∀ x, ((φ 0 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) :
          LaurentSeries (ResidueField A)) = x) ∧
      (∀ x, ((φ 1 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) :
          LaurentSeries (ResidueField A)) = qExpand (ResidueField A) s x) := by
  haveI : Fact q'.Prime := ⟨hq'⟩
  haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
  exact exists_pair (ResidueField A) q' M s hq'Ms

#print axioms solution

end S_ModularCurve_exists_degeneracyPair_residueField
end P2MW
export P2MW.S_ModularCurve_exists_degeneracyPair_residueField (solution)
