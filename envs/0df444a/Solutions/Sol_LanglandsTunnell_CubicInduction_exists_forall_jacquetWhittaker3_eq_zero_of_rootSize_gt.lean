-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ca655d9f-e701-55ba-973a-01adc40fc324

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Mathlib.Topology.Algebra.OpenSubgroup
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_rootSize_bound_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_finiteDimensional_fixedPoints_principalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_finset_localMaximalCompact3_eq_mul_of_level_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

noncomputable section

namespace WhittakerRootSizeVanishing

namespace StableJacquetFunctional

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction Topology

section PrincipalCongruenceSubgroups

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def IsLevel3 (m : ℕ) (κ : LocalGL3 v) : Prop :=
  ∀ i j : Fin 3,
    Valued.v (gl3Entry v κ i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))

private theorem isLevel3_iff (m : ℕ) (κ : LocalGL3 v) :
    IsLevel3 v m κ ↔ ∀ i j : Fin 3,
      Valued.v (gl3Entry v κ i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
        WithZero.exp (-(m : ℤ)) :=
  Iff.rfl

private theorem isLevel3_iff_sub_one (m : ℕ) (κ : LocalGL3 v) :
    IsLevel3 v m κ ↔ ∀ i j : Fin 3,
      Valued.v (((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) i j) ≤ WithZero.exp (-(m : ℤ)) :=
  Iff.rfl

private theorem isLevel3_one (m : ℕ) : IsLevel3 v m 1 := by
  intro i j
  simp only [gl3Entry, Units.val_one, sub_self, map_zero]
  exact zero_le

private theorem valued_coe_apply_le_one_of_mem_localMaximalCompact3 {k : LocalGL3 v}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (i j : Fin 3) :
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1 :=
  hk.1 i j

private theorem isLevel3_mul {m : ℕ} {a b : LocalGL3 v} (ha : IsLevel3 v m a) (hb : IsLevel3 v m b)
    (hbK : b ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) : IsLevel3 v m (a * b) := by
  rw [isLevel3_iff_sub_one] at ha hb ⊢
  intro i j
  have hid : ((a * b : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
      ((a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) * (b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) +
        ((b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) := by
    rw [Units.val_mul, sub_mul, one_mul]
    abel
  rw [hid, Matrix.add_apply]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hb i j))
  exact valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l => ha i l) (fun l => hbK.1 l j)

private theorem isLevel3_inv {m : ℕ} {a : LocalGL3 v} (ha : IsLevel3 v m a) (haK : a ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    IsLevel3 v m a⁻¹ := by
  rw [isLevel3_iff_sub_one] at ha ⊢
  intro i j
  have hid : ((a⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
      (1 - (a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) *
        ((a⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
    rw [sub_mul, one_mul, Units.mul_inv]
  rw [hid]
  refine valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l => ?_) (fun l => haK.2 l j)
  rw [← neg_sub, Matrix.neg_apply, Valuation.map_neg]
  exact ha i l

private def levelSubgroup3 (m : ℕ) : Subgroup (LocalGL3 v) where
  carrier := {k | k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ IsLevel3 v m k}
  one_mem' := ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).one_mem, isLevel3_one v m⟩
  mul_mem' := fun {_ _} ⟨haK, ha⟩ ⟨hbK, hb⟩ =>
    ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem haK hbK, isLevel3_mul v ha hb hbK⟩
  inv_mem' := fun {_} ⟨haK, ha⟩ => ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem haK, isLevel3_inv v ha haK⟩

private theorem mem_levelSubgroup3_iff (m : ℕ) (k : LocalGL3 v) :
    k ∈ levelSubgroup3 v m ↔ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ IsLevel3 v m k :=
  Iff.rfl

private theorem mem_localMaximalCompact3_of_mem_levelSubgroup3 {m : ℕ} {k : LocalGL3 v} (hk : k ∈ levelSubgroup3 v m) :
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v :=
  hk.1

private theorem isLevel3_of_mem_levelSubgroup3 {m : ℕ} {k : LocalGL3 v} (hk : k ∈ levelSubgroup3 v m) : IsLevel3 v m k :=
  hk.2

private theorem mem_levelSubgroup3_of_eq_mul {m : ℕ} {s k κ : LocalGL3 v} (hs : s ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (hκ : IsLevel3 v m κ) (h : k = s * κ) : κ ∈ levelSubgroup3 v m := by
  refine (mem_levelSubgroup3_iff v m κ).2 ⟨?_, hκ⟩
  have : κ = s⁻¹ * k := by rw [h, inv_mul_cancel_left]
  rw [this]
  exact (localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem ((localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem hs) hk

private theorem isLevel3_of_le {n m : ℕ} (hnm : n ≤ m) {k : LocalGL3 v} (hk : IsLevel3 v m k) : IsLevel3 v n k := by
  intro i j
  refine le_trans (hk i j) ?_
  rw [WithZero.exp_le_exp]
  omega

private theorem levelSubgroup3_le_of_le {n m : ℕ} (hnm : n ≤ m) : levelSubgroup3 v m ≤ levelSubgroup3 v n :=
  fun k hk => (mem_levelSubgroup3_iff v n k).2
    ⟨((mem_levelSubgroup3_iff v m k).1 hk).1, isLevel3_of_le v hnm ((mem_levelSubgroup3_iff v m k).1 hk).2⟩

private theorem isLevel3_zero_of_mem_localMaximalCompact3 {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    IsLevel3 v 0 k := by
  intro i j
  have h1 : WithZero.exp (-((0 : ℕ) : ℤ)) = 1 := by simp
  rw [h1]
  exact le_trans (Valuation.map_sub _ _ _) (max_le (hk.1 i j) (valued_one_entry_le3 (𝓞 ℚ) ℚ v i j))

private theorem levelSubgroup3_zero : levelSubgroup3 v 0 = localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  ext k
  exact ⟨fun hk => ((mem_levelSubgroup3_iff v 0 k).1 hk).1,
    fun hk => (mem_levelSubgroup3_iff v 0 k).2 ⟨hk, isLevel3_zero_of_mem_localMaximalCompact3 v hk⟩⟩

private theorem mem_levelSubgroup3_zero_iff (k : LocalGL3 v) :
    k ∈ levelSubgroup3 v 0 ↔ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  rw [levelSubgroup3_zero]

private theorem valued_mul_apply_le3_right {C : WithZero (Multiplicative ℤ)}
    {a b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {i j : Fin 3}
    (ha : ∀ l, Valued.v (a i l) ≤ 1) (hb : ∀ l, Valued.v (b l j) ≤ C) :
    Valued.v ((a * b) i j) ≤ C := by
  have hterm : ∀ l, Valued.v (a i l * b l j) ≤ C := fun l => by
    rw [map_mul]
    calc Valued.v (a i l) * Valued.v (b l j) ≤ 1 * Valued.v (b l j) := mul_le_mul_left (ha l) _
      _ = Valued.v (b l j) := one_mul _
      _ ≤ C := hb l
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

private theorem isLevel3_conj {m : ℕ} {k κ : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hκ : IsLevel3 v m κ) : IsLevel3 v m (k * κ * k⁻¹) := by
  rw [isLevel3_iff_sub_one] at hκ ⊢
  intro i j
  have hid : ((k * κ * k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
      (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
        (((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) *
          ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) := by
    rw [Units.val_mul, Units.val_mul, sub_mul, one_mul, mul_sub, ← mul_assoc, Units.mul_inv]
  rw [hid]
  refine valued_mul_apply_le3_right v (fun l => hk.1 i l) (fun l => ?_)
  exact valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l' => hκ l l') (fun l' => hk.2 l' j)

private theorem mul_mul_inv_mem_levelSubgroup3 {m : ℕ} {k κ : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hκ : κ ∈ levelSubgroup3 v m) : k * κ * k⁻¹ ∈ levelSubgroup3 v m :=
  (mem_levelSubgroup3_iff v m _).2
    ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem
        ((localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem hk (mem_localMaximalCompact3_of_mem_levelSubgroup3 v hκ))
        ((localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem hk),
      isLevel3_conj v hk (isLevel3_of_mem_levelSubgroup3 v hκ)⟩

private theorem valued_mul_apply_le3_mul {C C' : WithZero (Multiplicative ℤ)}
    {a b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {i j : Fin 3}
    (ha : ∀ l, Valued.v (a i l) ≤ C) (hb : ∀ l, Valued.v (b l j) ≤ C') :
    Valued.v ((a * b) i j) ≤ C * C' := by
  have hterm : ∀ l, Valued.v (a i l * b l j) ≤ C * C' := fun l => by
    rw [map_mul]
    exact mul_le_mul' (ha l) (hb l)
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

private theorem le_one_of_le_max_mul {M e : WithZero (Multiplicative ℤ)} (he : e < 1) (h : M ≤ max 1 (M * e)) :
    M ≤ 1 := by
  rcases le_or_gt M 1 with hM | hM
  · exact hM
  · exfalso
    have h' : M ≤ M * e := (le_max_iff.1 h).resolve_left (not_le.2 hM)
    obtain ⟨u, rfl⟩ := WithZero.ne_zero_iff_exists.1 (zero_lt_one.trans hM).ne'
    rcases eq_or_ne e 0 with rfl | he0
    · rw [mul_zero] at h'
      exact absurd h' (not_le.2 (WithZero.zero_lt_coe u))
    · obtain ⟨w, rfl⟩ := WithZero.ne_zero_iff_exists.1 he0
      rw [← WithZero.coe_mul, WithZero.coe_le_coe] at h'
      rw [← WithZero.coe_one, WithZero.coe_lt_coe] at he
      exact absurd ((le_mul_iff_one_le_right' _).1 h') (not_le.2 he)

private theorem exp_neg_one_lt_one : WithZero.exp (-((1 : ℕ) : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

private theorem mem_localMaximalCompact3_of_isLevel3 {n : ℕ} (hn : 1 ≤ n) {k : LocalGL3 v} (hk : IsLevel3 v n k) :
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have h1 := isLevel3_of_le v hn hk
  rw [isLevel3_iff_sub_one] at h1
  refine ⟨fun i j => ?_, ?_⟩
  · have hsplit : (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j =
        ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) i j +
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j := by
      simp
    rw [hsplit]
    exact le_trans (Valuation.map_add _ _ _)
      (max_le (le_trans (h1 i j) (exp_neg_one_lt_one).le) (valued_one_entry_le3 (𝓞 ℚ) ℚ v i j))
  · have hid : ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        1 - ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
          ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) := by
      rw [mul_sub, mul_one, Units.inv_mul, sub_sub_cancel]
    have hle : ∀ p : Fin 3 × Fin 3,
        Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) p.1 p.2) ≤
          Finset.univ.sup fun q : Fin 3 × Fin 3 =>
            Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) q.1 q.2) :=
      fun p => Finset.le_sup (f := fun q : Fin 3 × Fin 3 =>
        Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) q.1 q.2)) (Finset.mem_univ p)
    have hbound : ∀ i j, Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
        max 1 ((Finset.univ.sup fun p : Fin 3 × Fin 3 =>
          Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) p.1 p.2)) *
            WithZero.exp (-((1 : ℕ) : ℤ))) := by
      intro i j
      conv_lhs => rw [hid]
      rw [Matrix.sub_apply]
      refine le_trans (Valuation.map_sub _ _ _) (max_le_max (valued_one_entry_le3 (𝓞 ℚ) ℚ v i j) ?_)
      exact valued_mul_apply_le3_mul v (fun l => hle (i, l)) (fun l => h1 l j)
    have hM := le_one_of_le_max_mul (exp_neg_one_lt_one) (Finset.sup_le fun (p : Fin 3 × Fin 3) _ => hbound p.1 p.2)
    exact fun i j => le_trans (hle (i, j)) hM

private theorem mem_levelSubgroup3_of_isLevel3 {n : ℕ} (hn : 1 ≤ n) {k : LocalGL3 v} (hk : IsLevel3 v n k) :
    k ∈ levelSubgroup3 v n :=
  (mem_levelSubgroup3_iff v n k).2 ⟨mem_localMaximalCompact3_of_isLevel3 v hn hk, hk⟩

section Transversal

variable {G : Type*} [Group G]

private def IsTransversal (H H' : Subgroup G) (S : Finset G) : Prop :=
  (∀ s ∈ S, s ∈ H) ∧
    ∀ k ∈ H, ∃! s, s ∈ S ∧ ∃ κ ∈ H', k = s * κ

private theorem sum_eq_of_isTransversal {H H' : Subgroup G} {S S' : Finset G} (hS : IsTransversal H H' S)
    (hS' : IsTransversal H H' S') {φ : G → ℂ}
    (hφ : ∀ s, ∀ κ ∈ H', φ (s * κ) = φ s) :
    ∑ s ∈ S, φ s = ∑ s ∈ S', φ s := by

  have hmatch : ∀ s ∈ S, ∃ s', s' ∈ S' ∧ ∃ κ ∈ H', s = s' * κ :=
    fun s hs => (hS'.2 s (hS.1 s hs)).exists
  refine Finset.sum_bij (fun s hs => (hmatch s hs).choose) (fun s hs => (hmatch s hs).choose_spec.1) ?_ ?_ ?_
  · intro s₁ hs₁ s₂ hs₂ heq
    obtain ⟨κ₁, hκ₁, h₁⟩ := (hmatch s₁ hs₁).choose_spec.2
    obtain ⟨κ₂, hκ₂, h₂⟩ := (hmatch s₂ hs₂).choose_spec.2

    have hu := hS.2 _ (hS'.1 _ (hmatch s₁ hs₁).choose_spec.1)
    exact hu.unique ⟨hs₁, κ₁⁻¹, H'.inv_mem hκ₁, eq_mul_inv_of_mul_eq h₁.symm⟩
      ⟨hs₂, κ₂⁻¹, H'.inv_mem hκ₂, heq.trans (eq_mul_inv_of_mul_eq h₂.symm)⟩
  · intro s' hs'
    obtain ⟨s, ⟨hs, κ, hκ, hsκ⟩, -⟩ := hS.2 s' (hS'.1 s' hs')
    refine ⟨s, hs, ?_⟩
    obtain ⟨κ', hκ', h'⟩ := (hmatch s hs).choose_spec.2

    refine (hS'.2 s' (hS'.1 s' hs')).unique
      ⟨(hmatch s hs).choose_spec.1, κ' * κ, H'.mul_mem hκ' hκ, ?_⟩
      ⟨hs', 1, H'.one_mem, (mul_one s').symm⟩
    rw [hsκ, ← mul_assoc, ← h']
  · intro s hs
    obtain ⟨κ, hκ, h⟩ := (hmatch s hs).choose_spec.2
    exact (congrArg φ h).trans (hφ _ κ hκ)

private theorem isTransversal_image_mul [DecidableEq G] {H H' : Subgroup G} {S : Finset G} (hS : IsTransversal H H' S) {k : G}
    (hk : k ∈ H) : IsTransversal H H' (S.image (fun s => k * s)) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    exact H.mul_mem hk (hS.1 s hs)
  · intro k' hk'
    obtain ⟨s, ⟨hs, κ, hκ, hsκ⟩, huniq⟩ :=
      hS.2 (k⁻¹ * k') (H.mul_mem (H.inv_mem hk) hk')
    refine ⟨k * s, ⟨Finset.mem_image_of_mem _ hs, κ, hκ, ?_⟩, ?_⟩
    · rw [mul_assoc, ← hsκ, mul_inv_cancel_left]
    · rintro t ⟨ht, κ', hκ', hκ'eq⟩
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 ht
      have : s' = s := huniq s' ⟨hs', κ', hκ', by rw [hκ'eq, mul_assoc, inv_mul_cancel_left]⟩
      rw [this]

private theorem isTransversal_image_inv [DecidableEq G] {H H' : Subgroup G} {S : Finset G} (hS : IsTransversal H H' S)
    (hN : ∀ k ∈ H, ∀ κ ∈ H', k * κ * k⁻¹ ∈ H') :
    IsTransversal H H' (S.image (fun s => s⁻¹)) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    exact H.inv_mem (hS.1 s hs)
  · intro k hk
    obtain ⟨s, ⟨hs, κ, hκ, hsκ⟩, huniq⟩ := hS.2 k⁻¹ (H.inv_mem hk)
    refine ⟨s⁻¹, ⟨Finset.mem_image_of_mem _ hs, _,
      hN s (hS.1 s hs) _ (H'.inv_mem hκ), ?_⟩, ?_⟩
    · rw [← inv_inv k, hsκ]
      group
    · rintro t ⟨ht, κ', hκ', hk'⟩
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ht
      have hus : u = s :=
        huniq u ⟨hu, _, hN u⁻¹ (H.inv_mem (hS.1 u hu)) _ (H'.inv_mem hκ'), by rw [hk']; group⟩
      rw [hus]

end Transversal

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def levelAvg (S : Finset (LocalGL3 v)) (f : LocalGL3 v → ℂ) : LocalGL3 v → ℂ :=
  fun g => (S.card : ℂ)⁻¹ * ∑ s ∈ S, f (g * s)

private theorem levelAvg_apply (S : Finset (LocalGL3 v)) (f : LocalGL3 v → ℂ) (g : LocalGL3 v) :
    levelAvg v S f g = (S.card : ℂ)⁻¹ * ∑ s ∈ S, f (g * s) :=
  rfl

private theorem levelAvg_eq_of_isTransversal {H H' : Subgroup (LocalGL3 v)} {S S' : Finset (LocalGL3 v)}
    (hS : IsTransversal H H' S) (hS' : IsTransversal H H' S') {f : LocalGL3 v → ℂ}
    (hf : ∀ κ ∈ H', ∀ g, f (g * κ) = f g) :
    levelAvg v S f = levelAvg v S' f := by
  have hcard : (S.card : ℂ) = S'.card := by
    have h := sum_eq_of_isTransversal hS hS' (φ := fun _ => (1 : ℂ)) (fun _ _ _ => rfl)
    simpa using h
  funext g
  rw [levelAvg_apply, levelAvg_apply, hcard]
  congr 1
  exact sum_eq_of_isTransversal hS hS' (φ := fun s => f (g * s))
    (fun s κ hκ => by simp only [← mul_assoc]; exact hf κ hκ (g * s))

private theorem levelAvg_mul_of_isTransversal {H H' : Subgroup (LocalGL3 v)} {S : Finset (LocalGL3 v)}
    (hS : IsTransversal H H' S) {f : LocalGL3 v → ℂ} (hf : ∀ κ ∈ H', ∀ g, f (g * κ) = f g) {k : LocalGL3 v}
    (hk : k ∈ H) (g : LocalGL3 v) : levelAvg v S f (g * k) = levelAvg v S f g := by
  classical
  have himg : levelAvg v (S.image (fun s => k * s)) f g = levelAvg v S f (g * k) := by
    rw [levelAvg_apply, levelAvg_apply, Finset.card_image_of_injective _ (mul_right_injective k),
      Finset.sum_image (fun _ _ _ _ h => mul_right_injective k h)]
    simp only [mul_assoc]
  rw [← himg, levelAvg_eq_of_isTransversal v (isTransversal_image_mul hS hk) hS hf]

private abbrev IsTransversal3 (n m : ℕ) (S : Finset (LocalGL3 v)) : Prop :=
  IsTransversal (levelSubgroup3 v n) (levelSubgroup3 v m) S

private theorem levelSubgroup3_normalizes (n m : ℕ) :
    ∀ k ∈ levelSubgroup3 v n, ∀ κ ∈ levelSubgroup3 v m, k * κ * k⁻¹ ∈ levelSubgroup3 v m :=
  fun _ hk _ hκ => mul_mul_inv_mem_levelSubgroup3 v (mem_localMaximalCompact3_of_mem_levelSubgroup3 v hk) hκ

private theorem levelAvg_eq_smul_sum (S : Finset (LocalGL3 v)) (f : LocalGL3 v → ℂ) :
    levelAvg v S f = (S.card : ℂ)⁻¹ • ∑ s ∈ S, gl3AmbientRightTranslate (R := ℂ) s f := by
  funext g
  simp [levelAvg, Finset.sum_apply]

private theorem levelAvg_mem_principalSeries3 (S : Finset (LocalGL3 v)) {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) : levelAvg v S f ∈ principalSeries3 v χ := by
  rw [levelAvg_eq_smul_sum]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun s _ => rightTranslate_mem_principalSeries3 hf s))

private noncomputable def levelAvgLin (S : Finset (LocalGL3 v)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ) :=
  (S.card : ℂ)⁻¹ • ∑ s ∈ S,
    (gl3AmbientRightTranslate (R := ℂ) s).restrict (p := principalSeries3 v χ) (q := principalSeries3 v χ)
      (fun _ hf => rightTranslate_mem_principalSeries3 hf s)

private theorem coe_levelAvgLin_apply (S : Finset (LocalGL3 v)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : ↥(principalSeries3 v χ)) :
    ((levelAvgLin v S χ f : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ) = levelAvg v S f := by
  rw [levelAvg_eq_smul_sum]
  simp [levelAvgLin, LinearMap.sum_apply]

end PrincipalCongruenceSubgroups

section StableFunctional

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def HasStableIntegrals (u : LocalGL3 v → ℂ) : Prop :=
  letI := localBorel ℚ v
  ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
    IntegrableOn (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      psiLocal ℚ v (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2))
      (unipotentBall3 v c) (jacquetHaar3 v) ∧
    jacquetTruncated3 v c u = jacquetTruncated3 v c₀ u

private theorem isStable_zero : HasStableIntegrals v 0 := by
  letI := localBorel ℚ v
  refine ⟨0, fun c _ => ⟨?_, ?_⟩⟩
  · simp only [Pi.zero_apply, mul_zero]
    exact integrableOn_zero
  · have h : ∀ c : ℤ, jacquetTruncated3 v c (0 : LocalGL3 v → ℂ) = 0 := fun c => by
      simpa using jacquetTruncated3_smul v c (0 : ℂ) 0
    rw [h, h]

private theorem isStable_add {u u' : LocalGL3 v → ℂ} (hu : HasStableIntegrals v u) (hu' : HasStableIntegrals v u') :
    HasStableIntegrals v (u + u') := by
  letI := localBorel ℚ v
  obtain ⟨c₁, h₁⟩ := hu
  obtain ⟨c₂, h₂⟩ := hu'
  refine ⟨max c₁ c₂, fun c hc => ?_⟩
  have hc₁ : (c₁ : ℤ) ≤ c := le_trans (by exact_mod_cast le_max_left c₁ c₂) hc
  have hc₂ : (c₂ : ℤ) ≤ c := le_trans (by exact_mod_cast le_max_right c₁ c₂) hc
  have hm₁ : (c₁ : ℤ) ≤ ((max c₁ c₂ : ℕ) : ℤ) := by exact_mod_cast le_max_left c₁ c₂
  have hm₂ : (c₂ : ℤ) ≤ ((max c₁ c₂ : ℕ) : ℤ) := by exact_mod_cast le_max_right c₁ c₂
  refine ⟨?_, ?_⟩
  · have hsum : (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        psiLocal ℚ v (-(p.1 + p.2.1)) * (u + u') (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)) =
        (fun p => psiLocal ℚ v (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)) +
        (fun p => psiLocal ℚ v (-(p.1 + p.2.1)) * u' (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)) := by
      funext p
      simp only [Pi.add_apply, mul_add]
    rw [hsum]
    exact (h₁ c hc₁).1.add (h₂ c hc₂).1
  · rw [jacquetTruncated3_add v c u u' (h₁ c hc₁).1 (h₂ c hc₂).1,
      jacquetTruncated3_add v _ u u' (h₁ _ hm₁).1 (h₂ _ hm₂).1, (h₁ c hc₁).2, (h₂ c hc₂).2, (h₁ _ hm₁).2,
      (h₂ _ hm₂).2]

private theorem isStable_smul (a : ℂ) {u : LocalGL3 v → ℂ} (hu : HasStableIntegrals v u) :
    HasStableIntegrals v (a • u) := by
  letI := localBorel ℚ v
  obtain ⟨c₀, h⟩ := hu
  refine ⟨c₀, fun c hc => ⟨?_, ?_⟩⟩
  · have hsc : (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        psiLocal ℚ v (-(p.1 + p.2.1)) * (a • u) (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)) =
        fun p => a * (psiLocal ℚ v (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)) := by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsc]
    exact (h c hc).1.const_mul a
  · rw [jacquetTruncated3_smul, jacquetTruncated3_smul, (h c hc).2]

private theorem eventually_eq_jacquetValue {u : LocalGL3 v → ℂ} (hu : HasStableIntegrals v u) :
    ∃ N : ℕ, ∀ c : ℤ, (N : ℤ) ≤ c → jacquetTruncated3 v c u = jacquetValue v u := by
  obtain ⟨c₀, h⟩ := hu
  have hne : {c₀ : ℕ | ∀ c : ℤ, (c₀ : ℤ) ≤ c → jacquetTruncated3 v c u = jacquetTruncated3 v c₀ u}.Nonempty :=
    ⟨c₀, fun c hc => (h c hc).2⟩
  exact ⟨jacquetLevel v u, fun c hc => Nat.sInf_mem hne c hc⟩

private theorem jacquetValue_add {u u' : LocalGL3 v → ℂ} (hu : HasStableIntegrals v u)
    (hu' : HasStableIntegrals v u') :
    jacquetValue v (u + u') = jacquetValue v u + jacquetValue v u' := by
  obtain ⟨c₁, h₁⟩ := hu
  obtain ⟨c₂, h₂⟩ := hu'
  obtain ⟨N₁, e₁⟩ := eventually_eq_jacquetValue v ⟨c₁, h₁⟩
  obtain ⟨N₂, e₂⟩ := eventually_eq_jacquetValue v ⟨c₂, h₂⟩
  obtain ⟨N₃, e₃⟩ := eventually_eq_jacquetValue v (isStable_add v ⟨c₁, h₁⟩ ⟨c₂, h₂⟩)
  set c : ℕ := max (max c₁ c₂) (max N₁ (max N₂ N₃)) with hc
  have hc₁ : (c₁ : ℤ) ≤ c := by exact_mod_cast le_trans (le_max_left c₁ c₂) (le_max_left _ _)
  have hc₂ : (c₂ : ℤ) ≤ c := by exact_mod_cast le_trans (le_max_right c₁ c₂) (le_max_left _ _)
  have hN₁ : (N₁ : ℤ) ≤ c := by exact_mod_cast le_trans (le_max_left N₁ _) (le_max_right _ _)
  have hN₂ : (N₂ : ℤ) ≤ c := by
    exact_mod_cast le_trans (le_trans (le_max_left N₂ N₃) (le_max_right N₁ _)) (le_max_right _ _)
  have hN₃ : (N₃ : ℤ) ≤ c := by
    exact_mod_cast le_trans (le_trans (le_max_right N₂ N₃) (le_max_right N₁ _)) (le_max_right _ _)
  rw [← e₃ c hN₃, ← e₁ c hN₁, ← e₂ c hN₂]
  exact jacquetTruncated3_add v c u u' (h₁ c hc₁).1 (h₂ c hc₂).1

private theorem jacquetValue_smul (a : ℂ) (u : LocalGL3 v → ℂ) : jacquetValue v (a • u) = a * jacquetValue v u := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [zero_smul, zero_mul]
    have h__ := jacquetTruncated3_smul v (jacquetLevel v (0 : LocalGL3 v → ℂ)) (0 : ℂ) 0
    try simp at h__
    try simp
    exact h__
  · have hlevel : jacquetLevel v (a • u) = jacquetLevel v u := by
      unfold jacquetLevel
      congr 1
      ext c₀
      simp only [Set.mem_setOf_eq, jacquetTruncated3_smul]
      exact forall₂_congr fun c _ => mul_right_inj' ha
    unfold jacquetValue
    rw [hlevel, jacquetTruncated3_smul]

private def HasStableTranslates (u : LocalGL3 v → ℂ) : Prop :=
  ∀ g : LocalGL3 v, HasStableIntegrals v (gl3AmbientRightTranslate (R := ℂ) g u)

private theorem isStableAll_zero : HasStableTranslates v 0 := fun g => by
  rw [map_zero]
  exact isStable_zero v

private theorem isStableAll_add {u u' : LocalGL3 v → ℂ} (hu : HasStableTranslates v u)
    (hu' : HasStableTranslates v u') :
    HasStableTranslates v (u + u') := fun g => by
  rw [map_add]
  exact isStable_add v (hu g) (hu' g)

private theorem isStableAll_smul (a : ℂ) {u : LocalGL3 v → ℂ} (hu : HasStableTranslates v u) :
    HasStableTranslates v (a • u) :=
  fun g => by
  rw [map_smul]
  exact isStable_smul v a (hu g)

private def stableSubspace : Submodule ℂ (LocalGL3 v → ℂ) where
  carrier := {u | HasStableTranslates v u}
  zero_mem' := isStableAll_zero v
  add_mem' hu hu' := isStableAll_add v hu hu'
  smul_mem' a _ hu := isStableAll_smul v a hu

private def whittakerOf (u : LocalGL3 v → ℂ) : LocalGL3 v → ℂ :=
  fun g => jacquetValue v (gl3AmbientRightTranslate (R := ℂ) g u)

private theorem jacquetWhittaker3_eq_whittakerOf (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) : jacquetWhittaker3 v χ Φ = whittakerOf v (cellSectionOf v χ Φ) :=
  rfl

private theorem rightTranslate_comp_rightTranslate (g h : LocalGL3 v) (u : LocalGL3 v → ℂ) :
    gl3AmbientRightTranslate (R := ℂ) g (gl3AmbientRightTranslate (R := ℂ) h u) =
      gl3AmbientRightTranslate (R := ℂ) (g * h) u := by
  funext x
  simp only [gl3AmbientRightTranslate_apply, mul_assoc]

private theorem whittakerOf_rightTranslate (h : LocalGL3 v) (u : LocalGL3 v → ℂ) :
    whittakerOf v (gl3AmbientRightTranslate (R := ℂ) h u) = gl3AmbientRightTranslate (R := ℂ) h (whittakerOf v u) := by
  funext g
  rw [gl3AmbientRightTranslate_apply]
  simp only [whittakerOf]
  rw [rightTranslate_comp_rightTranslate]

private theorem isStableAll_rightTranslate {u : LocalGL3 v → ℂ} (hu : HasStableTranslates v u) (h : LocalGL3 v) :
    HasStableTranslates v (gl3AmbientRightTranslate (R := ℂ) h u) := fun g => by
  rw [rightTranslate_comp_rightTranslate]
  exact hu (g * h)

private theorem whittakerOf_add {u u' : LocalGL3 v → ℂ} (hu : HasStableTranslates v u)
    (hu' : HasStableTranslates v u') :
    whittakerOf v (u + u') = whittakerOf v u + whittakerOf v u' := by
  funext g
  simp only [whittakerOf, Pi.add_apply, map_add]
  exact jacquetValue_add v (hu g) (hu' g)

private theorem whittakerOf_smul (a : ℂ) (u : LocalGL3 v → ℂ) : whittakerOf v (a • u) = a • whittakerOf v u := by
  funext g
  simp only [whittakerOf, Pi.smul_apply, map_smul, smul_eq_mul]
  exact jacquetValue_smul v a _

private def whittakerLinear : stableSubspace v →ₗ[ℂ] (LocalGL3 v → ℂ) where
  toFun u := whittakerOf v u
  map_add' u u' := whittakerOf_add v u.2 u'.2
  map_smul' a u := whittakerOf_smul v a u

private theorem whittakerLinear_apply (u : stableSubspace v) : whittakerLinear v u = whittakerOf v u :=
  rfl

end StableFunctional

section AdmissibleCyclicSubspaces

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem jacquetValue_zero : jacquetValue v (0 : LocalGL3 v → ℂ) = 0 := by
  simpa using jacquetValue_smul v (0 : ℂ) (0 : LocalGL3 v → ℂ)

private theorem whittakerOf_zero : whittakerOf v (0 : LocalGL3 v → ℂ) = 0 := by
  funext g
  simp only [whittakerOf, map_zero, Pi.zero_apply]
  exact jacquetValue_zero v

private theorem whittakerOf_sum {ι : Type*} (S : Finset ι) (f : ι → LocalGL3 v → ℂ)
    (hf : ∀ i ∈ S, HasStableTranslates v (f i)) :
    whittakerOf v (∑ i ∈ S, f i) = ∑ i ∈ S, whittakerOf v (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact whittakerOf_zero v
  | insert a S ha ih =>
    have hS : ∀ i ∈ S, HasStableTranslates v (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum : HasStableTranslates v (∑ i ∈ S, f i) := (stableSubspace v).sum_mem hS
    rw [Finset.sum_insert ha, Finset.sum_insert ha, whittakerOf_add v (hf a (Finset.mem_insert_self a S)) hsum,
      ih hS]

private theorem whittakerOf_levelAvg (S : Finset (LocalGL3 v)) {u : LocalGL3 v → ℂ} (hu : HasStableTranslates v u) :
    whittakerOf v (levelAvg v S u) = levelAvg v S (whittakerOf v u) := by
  rw [levelAvg_eq_smul_sum, levelAvg_eq_smul_sum, whittakerOf_smul,
    whittakerOf_sum v S _ (fun s _ => isStableAll_rightTranslate v hu s)]
  simp only [whittakerOf_rightTranslate]

private theorem levelAvg_eq_self {S : Finset (LocalGL3 v)} (hcard : (S.card : ℂ) ≠ 0) {f : LocalGL3 v → ℂ}
    (hf : ∀ s ∈ S, ∀ g, f (g * s) = f g) : levelAvg v S f = f := by
  funext g
  rw [levelAvg_apply, Finset.sum_congr rfl (fun s hs => hf s hs g), Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hcard, one_mul]

private theorem exists_isTransversal3 (n m : ℕ) (hnm : n ≤ m) (hm : 1 ≤ m) : ∃ S, IsTransversal3 v n m S := by
  obtain ⟨S, hS₁, hS₂⟩ := exists_finset_localMaximalCompact3_eq_mul_of_level_le v n m hnm hm
  refine ⟨S, fun s hs => (mem_levelSubgroup3_iff v n s).2 ⟨(hS₁ s hs).1, (hS₁ s hs).2⟩, fun k hk => ?_⟩
  obtain ⟨hkK, hkn⟩ := (mem_levelSubgroup3_iff v n k).1 hk
  refine (existsUnique_congr fun s => ?_).1 (hS₂ k hkK hkn)
  constructor
  · rintro ⟨hs, κ, hκ, hk⟩
    exact ⟨hs, κ, mem_levelSubgroup3_of_isLevel3 v hm hκ, hk⟩
  · rintro ⟨hs, κ, hκ, hk⟩
    exact ⟨hs, κ, isLevel3_of_mem_levelSubgroup3 v hκ, hk⟩

private theorem card_ne_zero_of_isTransversal3 {n m : ℕ} {S : Finset (LocalGL3 v)} (hS : IsTransversal3 v n m S) :
    (S.card : ℂ) ≠ 0 := by
  obtain ⟨s, ⟨hs, -⟩, -⟩ := hS.2 1 (levelSubgroup3 v n).one_mem
  exact_mod_cast Finset.card_ne_zero.2 ⟨s, hs⟩

private theorem exists_forall_mem_of_isOpen {A : Set (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))} (hA : IsOpen A)
    (h1 : (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) ∈ A) :
    ∃ n : ℕ, ∀ X : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ),
      (∀ i j : Fin 3, Valued.v ((X - 1) i j) ≤ WithZero.exp (-(n : ℤ))) → X ∈ A := by
  classical
  obtain ⟨u, hu, huA⟩ := isOpen_pi_iff'.mp hA _ h1
  have hrow : ∀ i : Fin 3, ∃ w : Fin 3 → Set (v.adicCompletion ℚ),
      (∀ j, IsOpen (w j) ∧ (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j ∈ w j) ∧ Set.univ.pi w ⊆ u i :=
    fun i => isOpen_pi_iff'.mp (hu i).1 _ (hu i).2
  choose w hw hwu using hrow
  have hball : ∀ i j : Fin 3, ∃ ℓ : ℤ,
      {y : v.adicCompletion ℚ | Valued.v (y - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
        WithZero.exp (-ℓ)} ⊆ w i j :=
    fun i j => LanglandsTunnell.CubicInduction.exists_setOf_valued_sub_le_subset_of_isOpen v (hw i j).1 (hw i j).2
  choose ℓ hℓ using hball
  refine ⟨Finset.univ.sup fun i => Finset.univ.sup fun j => (ℓ i j).toNat, fun X hX => ?_⟩
  refine huA fun i _ => hwu i fun j _ => hℓ i j ?_
  have hij : (ℓ i j).toNat ≤ Finset.univ.sup fun i => Finset.univ.sup fun j => (ℓ i j).toNat :=
    le_trans (Finset.le_sup (f := fun j => (ℓ i j).toNat) (Finset.mem_univ j))
      (Finset.le_sup (f := fun i => Finset.univ.sup fun j => (ℓ i j).toNat) (Finset.mem_univ i))
  have hexp : WithZero.exp (-((Finset.univ.sup fun i => Finset.univ.sup fun j => (ℓ i j).toNat : ℕ) : ℤ)) ≤
      WithZero.exp (-ℓ i j) := by
    rw [WithZero.exp_le_exp]
    have := Int.self_le_toNat (ℓ i j)
    omega
  show Valued.v (X i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-ℓ i j)
  rw [← Matrix.sub_apply]
  exact le_trans (hX i j) hexp

private theorem exists_levelSubgroup3_le_of_isOpen (Uv : Subgroup (LocalGL3 v)) (hU : IsOpen (Uv : Set (LocalGL3 v))) :
    ∃ n : ℕ, 1 ≤ n ∧ levelSubgroup3 v n ≤ Uv := by
  obtain ⟨T, hT, hTU⟩ :=
    (Units.isEmbedding_embedProduct (M := Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))).isInducing.isOpen_iff.mp hU
  have h1T : ((1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)),
      MulOpposite.op (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) ∈ T := by
    have h : (1 : LocalGL3 v) ∈ Units.embedProduct _ ⁻¹' T := by
      rw [hTU]
      exact Uv.one_mem
    simpa using h
  obtain ⟨A, B, hA, hB, h1A, h1B, hAB⟩ := isOpen_prod_iff.mp hT _ _ h1T
  obtain ⟨nA, hnA⟩ := exists_forall_mem_of_isOpen v hA h1A
  obtain ⟨nB, hnB⟩ := exists_forall_mem_of_isOpen v (hB.preimage MulOpposite.continuous_op) h1B
  refine ⟨max (max nA nB) 1, le_max_right _ _, fun κ hκ => ?_⟩
  obtain ⟨hκK, hκn⟩ := (mem_levelSubgroup3_iff v _ κ).1 hκ
  have hκA : IsLevel3 v nA κ := isLevel3_of_le v (le_trans (le_max_left nA nB) (le_max_left _ _)) hκn
  have hκB : IsLevel3 v nB κ⁻¹ :=
    isLevel3_of_le v (le_trans (le_max_right nA nB) (le_max_left _ _)) (isLevel3_inv v hκn hκK)
  rw [isLevel3_iff_sub_one] at hκA hκB
  rw [← SetLike.mem_coe, ← hTU]
  exact hAB ⟨hnA _ hκA, hnB _ hκB⟩

private theorem hasStableTranslates_of_mem_cyclic {φ : LocalGL3 v → ℂ} (hφ : HasStableTranslates v φ)
    {G : LocalGL3 v → ℂ} (hG : G ∈ gl3CyclicSubspace φ) : HasStableTranslates v G := by
  have hle : gl3CyclicSubspace φ ≤ stableSubspace v := by
    unfold gl3CyclicSubspace
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact isStableAll_rightTranslate v hφ h
  exact hle hG

private theorem mem_principalSeries3_of_mem_cyclic {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {φ : LocalGL3 v → ℂ}
    (hφ : φ ∈ principalSeries3 v χ) {G : LocalGL3 v → ℂ} (hG : G ∈ gl3CyclicSubspace φ) :
    G ∈ principalSeries3 v χ := by
  have hle : gl3CyclicSubspace φ ≤ principalSeries3 v χ := by
    unfold gl3CyclicSubspace
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact rightTranslate_mem_principalSeries3 hφ h
  exact hle hG

private theorem exists_mem_cyclic_eq_whittakerOf {φ : LocalGL3 v → ℂ} (hφ : HasStableTranslates v φ)
    {F : LocalGL3 v → ℂ} (hF : F ∈ gl3CyclicSubspace (whittakerOf v φ)) :
    ∃ G ∈ gl3CyclicSubspace φ, F = whittakerOf v G := by
  unfold gl3CyclicSubspace at hF
  refine Submodule.span_induction (p := fun F _ => ∃ G ∈ gl3CyclicSubspace φ, F = whittakerOf v G) ?_ ?_ ?_ ?_ hF
  · rintro _ ⟨h, rfl⟩
    refine ⟨gl3AmbientRightTranslate (R := ℂ) h φ, ?_, (whittakerOf_rightTranslate v h φ).symm⟩
    unfold gl3CyclicSubspace
    exact Submodule.subset_span ⟨h, rfl⟩
  · exact ⟨0, Submodule.zero_mem _, (whittakerOf_zero v).symm⟩
  · rintro x y _ _ ⟨G, hG, rfl⟩ ⟨G', hG', rfl⟩
    exact ⟨G + G', Submodule.add_mem _ hG hG', (whittakerOf_add v (hasStableTranslates_of_mem_cyclic v hφ hG)
      (hasStableTranslates_of_mem_cyclic v hφ hG')).symm⟩
  · rintro a x _ ⟨G, hG, rfl⟩
    exact ⟨a • G, Submodule.smul_mem _ a hG, (whittakerOf_smul v a G).symm⟩

private theorem whittakerOf_mem_span_image [DecidableEq (LocalGL3 v → ℂ)] {B₀ : Finset (LocalGL3 v → ℂ)}
    (hB₀ : ∀ b ∈ B₀, HasStableTranslates v b) {E : LocalGL3 v → ℂ}
    (hE : E ∈ Submodule.span ℂ (B₀ : Set (LocalGL3 v → ℂ))) :
    whittakerOf v E ∈ Submodule.span ℂ ((B₀.image (whittakerOf v) : Finset (LocalGL3 v → ℂ)) :
      Set (LocalGL3 v → ℂ)) := by
  refine (Submodule.span_induction (p := fun E _ => HasStableTranslates v E ∧ whittakerOf v E ∈
    Submodule.span ℂ ((B₀.image (whittakerOf v) : Finset (LocalGL3 v → ℂ)) : Set (LocalGL3 v → ℂ)))
    ?_ ?_ ?_ ?_ hE).2
  · intro b hb
    exact ⟨hB₀ b hb, Submodule.subset_span (by
      rw [Finset.coe_image]
      exact Set.mem_image_of_mem _ hb)⟩
  · exact ⟨isStableAll_zero v, by
      rw [whittakerOf_zero]
      exact Submodule.zero_mem _⟩
  · rintro x y _ _ ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨isStableAll_add v hx hy, by
      rw [whittakerOf_add v hx hy]
      exact Submodule.add_mem _ hx' hy'⟩
  · rintro a x _ ⟨hx, hx'⟩
    exact ⟨isStableAll_smul v a hx, by
      rw [whittakerOf_smul]
      exact Submodule.smul_mem _ a hx'⟩

private theorem exists_finset_forall_mem_cyclic_imp_mem_span (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    {φ : LocalGL3 v → ℂ} (hφPS : φ ∈ principalSeries3 v χ) (hφ : HasStableTranslates v φ)
    (Uv : Subgroup (LocalGL3 v)) (hU : IsOpen (Uv : Set (LocalGL3 v))) :
    ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace (whittakerOf v φ),
      (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) := by
  classical
  obtain ⟨n, hn1, hnU⟩ := exists_levelSubgroup3_le_of_isOpen v Uv hU
  haveI := finiteDimensional_fixedPoints_principalSeries3 v χ n
  have hfin : FiniteDimensional ℂ ↥(gl3CyclicSubspace φ ⊓ (principalSeries3 v χ ⊓
      ⨅ k ∈ {k : LocalGL3 v | ∀ i j : Fin 3,
          Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
            ≤ WithZero.exp (-(n : ℤ))},
        LinearMap.ker (gl3AmbientRightTranslate (R := ℂ) k - LinearMap.id))) :=
    Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨B₀, hB₀⟩ := (Submodule.fg_iff_finiteDimensional _).2 hfin
  have hB₀cyc : ∀ b ∈ B₀, b ∈ gl3CyclicSubspace φ := fun b hb =>
    (hB₀ ▸ Submodule.subset_span (Finset.mem_coe.2 hb) : b ∈ gl3CyclicSubspace φ ⊓ _).1
  refine ⟨B₀.image (whittakerOf v), fun F hF hFU => ?_⟩
  obtain ⟨G, hG, rfl⟩ := exists_mem_cyclic_eq_whittakerOf v hφ hF
  have hGPS : G ∈ principalSeries3 v χ := mem_principalSeries3_of_mem_cyclic v hφPS hG
  obtain ⟨m₀, hm₀⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v χ G hGPS
  obtain ⟨S, hS⟩ := exists_isTransversal3 v n (max (max n m₀) 1)
    (le_trans (le_max_left n m₀) (le_max_left _ _)) (le_max_right _ _)
  have hGinv : ∀ κ ∈ levelSubgroup3 v (max (max n m₀) 1), ∀ g : LocalGL3 v, G (g * κ) = G g := by
    intro κ hκ g
    have h := hm₀ κ (isLevel3_of_le v (le_trans (le_max_right n m₀) (le_max_left _ _))
      (isLevel3_of_mem_levelSubgroup3 v hκ))
    have h' := congrFun h g
    rwa [gl3AmbientRightTranslate_apply] at h'
  have hEcyc : levelAvg v S G ∈ gl3CyclicSubspace φ := by
    rw [levelAvg_eq_smul_sum]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun s _ => gl3AmbientRightTranslate_mem_gl3CyclicSubspace φ s hG)
  have hEfix : levelAvg v S G ∈ (principalSeries3 v χ ⊓
      ⨅ k ∈ {k : LocalGL3 v | ∀ i j : Fin 3,
          Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
            ≤ WithZero.exp (-(n : ℤ))},
        LinearMap.ker (gl3AmbientRightTranslate (R := ℂ) k - LinearMap.id)) := by
    refine Submodule.mem_inf.2 ⟨levelAvg_mem_principalSeries3 v S hGPS, ?_⟩
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    intro k hk
    funext g
    rw [gl3AmbientRightTranslate_apply]
    exact levelAvg_mul_of_isTransversal v hS hGinv (mem_levelSubgroup3_of_isLevel3 v hn1 hk) g
  have hEspan : levelAvg v S G ∈ Submodule.span ℂ (B₀ : Set (LocalGL3 v → ℂ)) := by
    rw [hB₀]
    exact Submodule.mem_inf.2 ⟨hEcyc, hEfix⟩
  have hWE : whittakerOf v (levelAvg v S G) = whittakerOf v G := by
    rw [whittakerOf_levelAvg v S (hasStableTranslates_of_mem_cyclic v hφ hG)]
    exact levelAvg_eq_self v (card_ne_zero_of_isTransversal3 v hS) fun s hs g => hFU s (hnU (hS.1 s hs)) g
  rw [← hWE]
  exact whittakerOf_mem_span_image v (fun b hb => hasStableTranslates_of_mem_cyclic v hφ (hB₀cyc b hb)) hEspan

end AdmissibleCyclicSubspaces

end StableJacquetFunctional

namespace JacquetCentralCharacter

open Matrix IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem scalar_eq_diagonal3 (z : (v.adicCompletion ℚ)ˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) z = diagonal3 v (fun _ => z) := by
  apply Units.ext
  change Matrix.scalar (Fin 3) (z : v.adicCompletion ℚ) = _
  rw [diagonal3_coe, Matrix.scalar_apply]

private theorem mul_scalar_eq_scalar_mul (z : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 3) z = Matrix.GeneralLinearGroup.scalar (Fin 3) z * g := by
  apply Units.ext
  change (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) * Matrix.scalar (Fin 3) (z : v.adicCompletion ℚ) =
    Matrix.scalar (Fin 3) (z : v.adicCompletion ℚ) * (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
  exact (Matrix.scalar_commute (z : v.adicCompletion ℚ) (fun r => mul_comm _ r) _).eq.symm

private theorem halfModulus3_const (z : (v.adicCompletion ℚ)ˣ) : halfModulus3 v (fun _ => z) = 1 := by
  have hz : ‖(z : v.adicCompletion ℚ)‖ ≠ 0 := norm_ne_zero_iff.mpr z.ne_zero
  simp only [halfModulus3, div_self hz, Complex.ofReal_one]

private theorem torusChar3_const (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (z : (v.adicCompletion ℚ)ˣ) :
    torusChar3 v χ (fun _ => z) = (((χ 0 * χ 1 * χ 2) z : ℂˣ) : ℂ) := by
  simp only [torusChar3, Fin.prod_univ_three, MonoidHom.mul_apply, Units.val_mul]

private theorem rightTranslate_scalar_mul (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (z : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    gl3AmbientRightTranslate (R := ℂ) (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) (cellSectionOf v χ Φ) =
      (((χ 0 * χ 1 * χ 2) z : ℂˣ) : ℂ) • gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v χ Φ) := by
  funext x
  simp only [gl3AmbientRightTranslate_apply, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, mul_scalar_eq_scalar_mul, mul_assoc, scalar_eq_diagonal3, cellSectionOf_diagonal3_mul,
    torusChar3_const, halfModulus3_const, mul_one]

private theorem jacquetLevel_smul {a : ℂ} (ha : a ≠ 0) (u : LocalGL3 v → ℂ) :
    jacquetLevel v (a • u) = jacquetLevel v u := by
  unfold jacquetLevel
  congr 1
  ext c₀
  simp only [Set.mem_setOf_eq, jacquetTruncated3_smul]
  exact forall₂_congr fun c _ => mul_right_inj' ha

private theorem jacquetValue_smul {a : ℂ} (ha : a ≠ 0) (u : LocalGL3 v → ℂ) :
    jacquetValue v (a • u) = a * jacquetValue v u := by
  unfold jacquetValue
  rw [jacquetLevel_smul v ha, jacquetTruncated3_smul]

private theorem jacquetWhittaker3_scalar_mul (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (z : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    jacquetWhittaker3 v χ Φ (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) =
      (((χ 0 * χ 1 * χ 2) z : ℂˣ) : ℂ) * jacquetWhittaker3 v χ Φ g := by
  rw [jacquetWhittaker3_apply, jacquetWhittaker3_apply, rightTranslate_scalar_mul,
    jacquetValue_smul v (Units.ne_zero _)]

end JacquetCentralCharacter

namespace MembershipUnit

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction Filter Topology

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isOpen_valued_le_exp (n : ℕ) :
    IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (n : ℤ)} := by
  have h : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (n : ℤ)}
      = {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (- -(n : ℤ))} := by
    simp only [sub_zero, neg_neg]
  rw [h]
  exact (isClopen_setOf_valued_sub_le v 0 (-(n : ℤ))).isOpen

private theorem exists_forall_valued_le_of_isCompact {S : Set (v.adicCompletion ℚ)} (hS : IsCompact S) :
    ∃ R : ℤ, ∀ x ∈ S, Valued.v x ≤ WithZero.exp R := by
  have hcov : S ⊆ ⋃ n : ℕ, {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (n : ℤ)} := by
    intro x _
    obtain ⟨n, hn⟩ := exists_valued_le_exp v x
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  have hdir : Directed (· ⊆ ·) fun n : ℕ => {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (n : ℤ)} := by
    intro a b
    refine ⟨max a b, fun x hx => ?_, fun x hx => ?_⟩
    · exact le_trans hx (WithZero.exp_le_exp.mpr (Nat.cast_le.mpr (le_max_left a b)))
    · exact le_trans hx (WithZero.exp_le_exp.mpr (Nat.cast_le.mpr (le_max_right a b)))
  obtain ⟨n, hn⟩ := hS.elim_directed_cover _ (isOpen_valued_le_exp v) hcov hdir
  exact ⟨n, fun x hx => hn hx⟩

private theorem exists_forall_apply_eq_zero_of_exp_lt {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ}
    (hΦc : HasCompactSupport Φ) :
    ∃ R : ℤ, ∀ (q : Fin 3 → v.adicCompletion ℚ) (i : Fin 3), WithZero.exp R < Valued.v (q i) → Φ q = 0 := by
  have hK : IsCompact (tsupport Φ) := hΦc
  have hb : ∀ i : Fin 3, ∃ R : ℤ, ∀ q ∈ tsupport Φ, Valued.v (q i) ≤ WithZero.exp R := by
    intro i
    obtain ⟨R, hR⟩ := exists_forall_valued_le_of_isCompact v (hK.image (continuous_apply i))
    exact ⟨R, fun q hq => hR _ (Set.mem_image_of_mem _ hq)⟩
  choose R hR using hb
  have hRmax : ∀ j : Fin 3, R j ≤ max (R 0) (max (R 1) (R 2)) := by
    intro j
    fin_cases j <;> simp
  refine ⟨max (R 0) (max (R 1) (R 2)), fun q i hi => ?_⟩
  by_contra hq
  have hqs : q ∈ tsupport Φ := subset_tsupport Φ hq
  exact absurd ((hR i q hqs).trans (WithZero.exp_le_exp.mpr (hRmax i))) (not_le.mpr hi)

private theorem eventually_exp_lt_valued_div {n d : LocalGL3 v → v.adicCompletion ℚ} {g : LocalGL3 v}
    (hn : Continuous n)
    (hd : Continuous d) (hng : n g ≠ 0) (hdg : d g = 0) (R : ℤ) :
    ∀ᶠ h in 𝓝 g, d h ≠ 0 → WithZero.exp R < Valued.v (n h / d h) := by
  obtain ⟨t, ht0, ht⟩ := exists_valued_eq_exp v (-R)
  have h1 : ∀ᶠ h in 𝓝 g, Valued.v (n h) = Valued.v (n g) := (hn.tendsto g).eventually (eventually_valued_eq v hng)
  have h2 : ∀ᶠ h in 𝓝 g, Valued.v (d h) < Valued.v (t * n g) := by
    have hlim : Tendsto d (𝓝 g) (𝓝 0) := by simpa [hdg] using hd.tendsto g
    exact hlim.eventually (eventually_valued_lt v (mul_ne_zero ht0 hng))
  filter_upwards [h1, h2] with h hn' hd' hd0
  have hvd : Valued.v (d h) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd0
  rw [Valuation.map_mul, ht] at hd'
  rw [map_div₀, hn', lt_div_iff₀ (lt_of_le_of_ne zero_le' hvd.symm)]
  calc WithZero.exp R * Valued.v (d h) < WithZero.exp R * (WithZero.exp (-R) * Valued.v (n g)) :=
        mul_lt_mul_of_pos_left hd' WithZero.exp_pos
    _ = Valued.v (n g) := by rw [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul]

private theorem eventually_cellSectionOf_eq_of_den {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} {R : ℤ}
    (hR : ∀ (q : Fin 3 → v.adicCompletion ℚ) (i : Fin 3), WithZero.exp R < Valued.v (q i) → Φ q = 0) {g : LocalGL3 v}
    {n d : LocalGL3 v → v.adicCompletion ℚ} (i : Fin 3) (hn : Continuous n) (hd : Continuous d) (hng : n g ≠ 0)
    (hdg : d g = 0) (hratio : ∀ h, cellRatio v h i = n h / d h) (hden : ∀ h, h ∈ bigCell3 v → d h ≠ 0) :
    ∀ᶠ h in 𝓝 g, cellSectionOf v χ Φ h = cellSectionOf v χ Φ g := by
  have hg : g ∉ bigCell3 v := fun hmem => hden g hmem hdg
  rw [cellSectionOf_apply_of_notMem v χ Φ hg]
  filter_upwards [eventually_exp_lt_valued_div v hn hd hng hdg R] with h hh
  by_cases hhB : h ∈ bigCell3 v
  · rw [cellSectionOf_apply_of_mem v χ Φ hhB, hR (cellRatio v h) i (by rw [hratio]; exact hh (hden h hhB)), mul_zero]
  · exact cellSectionOf_apply_of_notMem v χ Φ hhB

private theorem isLocallyConstant_cellSectionOf {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hχ : ∀ i, IsLocallyConstant (χ i)) {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} (hΦ : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) : IsLocallyConstant (cellSectionOf v χ Φ) := by
  obtain ⟨R, hR⟩ := exists_forall_apply_eq_zero_of_exp_lt v hΦc
  have hΦ' := hΦ
  rw [IsLocallyConstant.iff_eventually_eq] at hΦ' ⊢
  intro g
  by_cases hc : cornerEntry v g = 0
  · rcases exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero v hc with h21 | h22
    · exact eventually_cellSectionOf_eq_of_den v hR 0 (continuous_gl3Entry v 2 1) (continuous_cornerEntry v) h21 hc
        (fun h => rfl) (fun h hh => hh.1)
    · exact eventually_cellSectionOf_eq_of_den v hR 1 (continuous_gl3Entry v 2 2) (continuous_cornerEntry v) h22 hc
        (fun h => rfl) (fun h hh => hh.1)
  by_cases hl : lowerMinor v g = 0
  · exact eventually_cellSectionOf_eq_of_den v hR 2 (continuous_outerMinor v) (continuous_lowerMinor v)
      (outerMinor_ne_zero_of_lowerMinor_eq_zero v hc hl) hl (fun h => rfl) (fun h hh => hh.2)
  have hgB : g ∈ bigCell3 v := ⟨hc, hl⟩
  have hcA : ContinuousAt (cornerEntry v) g := (continuous_cornerEntry v).continuousAt
  have hlA : ContinuousAt (lowerMinor v) g := (continuous_lowerMinor v).continuousAt
  have hdA : ContinuousAt (gl3Det v) g := (continuous_gl3Det v).continuousAt
  have hmem : ∀ᶠ h in 𝓝 g, h ∈ bigCell3 v := by
    filter_upwards [hcA.eventually_ne hc, hlA.eventually_ne hl] with h hch hlh
    exact ⟨hch, hlh⟩
  have hval : ∀ᶠ h in 𝓝 g, cellValue v χ h = cellValue v χ g := by
    have hq0 : gl3Det v g / lowerMinor v g ≠ 0 := div_ne_zero (gl3Det_ne_zero v g) hl
    have hq1 : lowerMinor v g / cornerEntry v g ≠ 0 := div_ne_zero hl hc
    have e0 : ∀ᶠ h in nhds g,
        LanglandsTunnell.TateLocal.charExt (χ 0) (gl3Det v h / lowerMinor v h)
          = LanglandsTunnell.TateLocal.charExt (χ 0) (gl3Det v g / lowerMinor v g) :=
      (hdA.div hlA hl).eventually (eventually_charExt_eq v (χ 0) (hχ 0) hq0)
    have e1 : ∀ᶠ h in nhds g,
        LanglandsTunnell.TateLocal.charExt (χ 1) (lowerMinor v h / cornerEntry v h)
          = LanglandsTunnell.TateLocal.charExt (χ 1) (lowerMinor v g / cornerEntry v g) :=
      (hlA.div hcA hc).eventually (eventually_charExt_eq v (χ 1) (hχ 1) hq1)
    have e2 : ∀ᶠ h in nhds g, LanglandsTunnell.TateLocal.charExt (χ 2) (cornerEntry v h)
      = LanglandsTunnell.TateLocal.charExt (χ 2) (cornerEntry v g) :=
      hcA.eventually (eventually_charExt_eq v (χ 2) (hχ 2) hc)
    have e3 : ∀ᶠ h in nhds g, ‖gl3Det v h / lowerMinor v h‖ = ‖gl3Det v g / lowerMinor v g‖ :=
      (hdA.div hlA hl).eventually (eventually_norm_eq v hq0)
    have e4 : ∀ᶠ h in nhds g, ‖cornerEntry v h‖ = ‖cornerEntry v g‖ := hcA.eventually (eventually_norm_eq v hc)
    filter_upwards [e0, e1, e2, e3, e4] with h h0 h1 h2 h3 h4
    simp only [cellValue, h0, h1, h2, h3, h4]
  have hrA : ContinuousAt (cellRatio v) g := by
    rw [continuousAt_pi]
    intro i
    fin_cases i
    · exact ((continuous_gl3Entry v 2 1).continuousAt).div hcA hc
    · exact ((continuous_gl3Entry v 2 2).continuousAt).div hcA hc
    · exact ((continuous_outerMinor v).continuousAt).div hlA hl
  have hΦr : ∀ᶠ h in 𝓝 g, Φ (cellRatio v h) = Φ (cellRatio v g) := hrA.eventually (hΦ' (cellRatio v g))
  filter_upwards [hmem, hval, hΦr] with h h1 h2 h3
  rw [cellSectionOf_apply_of_mem v χ Φ h1, cellSectionOf_apply_of_mem v χ Φ hgB, h2, h3]

private theorem cellSectionOf_mem_principalSeries3 {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hχ : ∀ i, IsLocallyConstant (χ i)) {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ} (hΦ : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) : cellSectionOf v χ Φ ∈ principalSeries3 v χ :=
  ⟨isLocallyConstant_cellSectionOf v hχ hΦ hΦc, cellSectionOf_upperUnipotent3_mul v χ Φ,
    cellSectionOf_diagonal3_mul v χ Φ⟩

end MembershipUnit

namespace PsiLawUnit

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

section PsiLaw

variable (v : HeightOneSpectrum (𝓞 ℚ))

private abbrev Unip3 : Type := v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ

private noncomputable def unipotentShift (p₀ : Unip3 v) : Unip3 v ≃ₜ Unip3 v where
  toFun p := (p.1 + p₀.1, p.2.1 + p₀.2.1, p.2.2 + p₀.2.2 + p.1 * p₀.2.1)
  invFun p := (p.1 - p₀.1, p.2.1 - p₀.2.1, p.2.2 - p₀.2.2 - (p.1 - p₀.1) * p₀.2.1)
  left_inv p := by
    obtain ⟨a, b, d⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  right_inv p := by
    obtain ⟨a, b, d⟩ := p
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  continuous_toFun :=
    (continuous_fst.add continuous_const).prodMk
      (((continuous_fst.comp continuous_snd).add continuous_const).prodMk
        (((continuous_snd.comp continuous_snd).add continuous_const).add (continuous_fst.mul continuous_const)))
  continuous_invFun :=
    (continuous_fst.sub continuous_const).prodMk
      (((continuous_fst.comp continuous_snd).sub continuous_const).prodMk
        (((continuous_snd.comp continuous_snd).sub continuous_const).sub
          ((continuous_fst.sub continuous_const).mul continuous_const)))

private theorem unipotentShift_apply (p₀ p : Unip3 v) :
    unipotentShift v p₀ p = (p.1 + p₀.1, p.2.1 + p₀.2.1, p.2.2 + p₀.2.2 + p.1 * p₀.2.1) :=
  rfl

private theorem preimage_unipotentBall3_unipotentShift {c : ℤ} {p₀ : Unip3 v} (hp₀ : p₀ ∈ unipotentBall3 v c) :
    unipotentShift v p₀ ⁻¹' unipotentBall3 v c = unipotentBall3 v c := by
  ext p
  constructor
  · intro hp
    have hmem := unipotentBall3_mul_mem v (c := c) (p := unipotentShift v p₀ p)
      (p' := (-p₀.1, -p₀.2.1, p₀.1 * p₀.2.1 - p₀.2.2)) hp (unipotentBall3_inv_mem v hp₀)
    convert hmem using 1
    all_goals try rfl
    obtain ⟨a, b, d⟩ := p
    simp only [unipotentShift_apply, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  · intro hp
    exact unipotentBall3_mul_mem v hp hp₀

private theorem isAddHaarMeasure_selfDualHaarAt_rat :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  have hN : (0 : NNReal) < (Ideal.absNorm v.asIdeal : NNReal) := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero h0
  unfold selfDualHaarAt
  exact Measure.IsAddHaarMeasure.nnreal_smul _ (NNReal.rpow_pos hN).ne'

private theorem measurePreserving_unipotentShift (p₀ : Unip3 v) :
    letI := localBorel ℚ v
    MeasurePreserving (unipotentShift v p₀) (jacquetHaar3 v) (jacquetHaar3 v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt_rat v
  have hshape : (unipotentShift v p₀ : Unip3 v → Unip3 v)
      = fun p : Unip3 v => (p₀.1 + p.1, (p₀.2.1, p₀.2.2 + p.1 * p₀.2.1) + p.2) := by
    funext p
    obtain ⟨a, b, d⟩ := p
    simp only [unipotentShift_apply, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  show MeasurePreserving (unipotentShift v p₀)
    ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))
    ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))
  rw [hshape]
  refine MeasurePreserving.skew_product
    (g := fun (a : v.adicCompletion ℚ) (q : v.adicCompletion ℚ × v.adicCompletion ℚ) =>
      (p₀.2.1, p₀.2.2 + a * p₀.2.1) + q)
    (measurePreserving_add_left (selfDualHaarAt ℚ v) p₀.1) ?_ ?_
  · exact (((continuous_const.prodMk (continuous_const.add (continuous_fst.mul continuous_const))).add
      continuous_snd) : Continuous fun q : v.adicCompletion ℚ × (v.adicCompletion ℚ × v.adicCompletion ℚ) =>
        (p₀.2.1, p₀.2.2 + q.1 * p₀.2.1) + q.2).measurable
  · exact Filter.Eventually.of_forall fun a =>
      map_add_left_eq_self ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) (p₀.2.1, p₀.2.2 + a * p₀.2.1)

private theorem jacquetTruncated3_rightTranslate_upperUnipotent3 (c : ℤ) (F : LocalGL3 v → ℂ) {p₀ : Unip3 v}
    (hp₀ : p₀ ∈ unipotentBall3 v c) :
    jacquetTruncated3 v c (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 p₀.1 p₀.2.1 p₀.2.2) F)
      = psiLocal ℚ v (p₀.1 + p₀.2.1) * jacquetTruncated3 v c F := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  set G : Unip3 v → ℂ := fun p =>
    psiLocal ℚ v (-(p.1 + p.2.1)) * F (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2) with hG
  have hint : ∀ p : Unip3 v,
      psiLocal ℚ v (-(p.1 + p.2.1))
          * gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 p₀.1 p₀.2.1 p₀.2.2) F
              (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)
        = psiLocal ℚ v (p₀.1 + p₀.2.1) * G (unipotentShift v p₀ p) := by
    intro p
    simp only [hG, gl3AmbientRightTranslate_apply, unipotentShift_apply, mul_assoc,
      upperUnipotent3_mul_upperUnipotent3]
    rw [← mul_assoc (psiLocal ℚ v (p₀.1 + p₀.2.1)), ← AddChar.map_add_eq_mul]
    congr 2
    ring
  have hleft : jacquetTruncated3 v c (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 p₀.1 p₀.2.1 p₀.2.2) F)
      = ∫ p in unipotentBall3 v c, psiLocal ℚ v (p₀.1 + p₀.2.1) * G (unipotentShift v p₀ p) ∂(jacquetHaar3 v) := by
    unfold jacquetTruncated3
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => hint p)
  have hright : jacquetTruncated3 v c F = ∫ p in unipotentBall3 v c, G p ∂(jacquetHaar3 v) := by
    unfold jacquetTruncated3
    rfl
  rw [hleft, hright, integral_const_mul]
  congr 1
  have hpre := (measurePreserving_unipotentShift v p₀).setIntegral_preimage_emb
    (unipotentShift v p₀).measurableEmbedding G (unipotentBall3 v c)
  rw [preimage_unipotentBall3_unipotentShift v hp₀] at hpre
  exact hpre

private theorem exists_mem_unipotentBall3 (p₀ : Unip3 v) : ∃ k : ℕ, p₀ ∈ unipotentBall3 v k := by
  have hbound : ∀ x : v.adicCompletion ℚ, ∃ n : ℕ, Valued.v x ≤ WithZero.exp (n : ℤ) := by
    intro x
    by_cases hx : Valued.v x = 0
    · exact ⟨0, by rw [hx]; exact zero_le'⟩
    · refine ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
      calc Valued.v x = WithZero.exp (WithZero.log (Valued.v x)) := (WithZero.exp_log hx).symm
        _ ≤ WithZero.exp ((WithZero.log (Valued.v x)).toNat : ℤ) :=
          WithZero.exp_le_exp.mpr (Int.self_le_toNat _)
  obtain ⟨n₁, h₁⟩ := hbound p₀.1
  obtain ⟨n₂, h₂⟩ := hbound p₀.2.1
  obtain ⟨n₃, h₃⟩ := hbound p₀.2.2
  refine ⟨max n₁ (max n₂ n₃), ?_⟩
  simp only [mem_unipotentBall3_iff]
  refine ⟨h₁.trans (WithZero.exp_le_exp.mpr (by omega)), h₂.trans (WithZero.exp_le_exp.mpr (by omega)),
    h₃.trans (WithZero.exp_le_exp.mpr (by omega))⟩

private def Stabilises (u : LocalGL3 v → ℂ) : Prop :=
  ∃ L : ℕ, ∀ c : ℤ, (L : ℤ) ≤ c → jacquetTruncated3 v c u = jacquetTruncated3 v L u

private theorem jacquetValue_rightTranslate_upperUnipotent3 {F : LocalGL3 v → ℂ} (hF : Stabilises v F) (p₀ : Unip3 v) :
    jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 p₀.1 p₀.2.1 p₀.2.2) F)
      = psiLocal ℚ v (p₀.1 + p₀.2.1) * jacquetValue v F := by
  obtain ⟨L, hL⟩ := hF
  obtain ⟨k, hk⟩ := exists_mem_unipotentBall3 v p₀
  set c : ℕ := max L k with hc
  have hkc : ∀ c' : ℤ, (c : ℤ) ≤ c' → p₀ ∈ unipotentBall3 v c' := fun c' hc' =>
    unipotentBall3_mono v (by omega) hk
  have hconst : ∀ c' : ℤ, (c : ℤ) ≤ c' →
      jacquetTruncated3 v c' (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 p₀.1 p₀.2.1 p₀.2.2) F)
        = psiLocal ℚ v (p₀.1 + p₀.2.1) * jacquetTruncated3 v L F := by
    intro c' hc'
    rw [jacquetTruncated3_rightTranslate_upperUnipotent3 v c' F (hkc c' hc'), hL c' (by omega)]
  have hstab' : ∀ c' : ℤ, (c : ℤ) ≤ c' →
      jacquetTruncated3 v c' (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 p₀.1 p₀.2.1 p₀.2.2) F)
        = jacquetTruncated3 v c (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 p₀.1 p₀.2.1 p₀.2.2) F) := by
    intro c' hc'
    rw [hconst c' hc', hconst c le_rfl]
  have h1 := jacquetTruncated3_eq_jacquetValue v
    (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 p₀.1 p₀.2.1 p₀.2.2) F) ⟨c, hstab'⟩
    (c := (c : ℤ)) (by exact_mod_cast jacquetLevel_le v _ hstab')
  have h2 := jacquetTruncated3_eq_jacquetValue v F ⟨L, hL⟩ (c := (c : ℤ))
    (by exact_mod_cast (jacquetLevel_le v F hL).trans (le_max_left L k))
  rw [← h1, hconst c le_rfl, ← h2, hL c (by omega)]

private theorem gl3AmbientRightTranslate_mul (a b : LocalGL3 v) (u : LocalGL3 v → ℂ) :
    gl3AmbientRightTranslate (R := ℂ) (a * b) u
      = gl3AmbientRightTranslate (R := ℂ) a (gl3AmbientRightTranslate (R := ℂ) b u) := by
  funext h
  simp only [gl3AmbientRightTranslate_apply, mul_assoc]

private theorem isGL3PsiWhittakerFn_jacquetValue_translate (u : LocalGL3 v → ℂ)
    (hstab : ∀ g : LocalGL3 v, Stabilises v (gl3AmbientRightTranslate (R := ℂ) g u)) (w : LocalGL3 v) :
    IsGL3PsiWhittakerFn (psiLocal ℚ v)
      fun g : LocalGL3 v => jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (g * w) u) := by
  intro x y z g
  show jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z * g * w) u)
    = psiLocal ℚ v (x + y) * jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (g * w) u)
  have h := jacquetValue_rightTranslate_upperUnipotent3 v (hstab (g * w)) (x, y, z)
  simp only at h
  rw [mul_assoc, gl3AmbientRightTranslate_mul v (upperUnipotent3 x y z) (g * w) u, h]

private theorem isGL3PsiWhittakerFn_jacquetWhittaker3_mul_antidiagonal3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hstab : ∀ g : LocalGL3 v, Stabilises v (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v χ Φ))) :
    IsGL3PsiWhittakerFn (psiLocal ℚ v) fun h : LocalGL3 v => jacquetWhittaker3 v χ Φ (h * antidiagonal3 v) :=
  isGL3PsiWhittakerFn_jacquetValue_translate v (cellSectionOf v χ Φ) hstab (antidiagonal3 v)

private theorem isGL3PsiWhittakerFn_jacquetWhittaker3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hstab : ∀ g : LocalGL3 v, Stabilises v (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v χ Φ))) :
    IsGL3PsiWhittakerFn (psiLocal ℚ v) (jacquetWhittaker3 v χ Φ) := by
  intro x y z g
  have h := jacquetValue_rightTranslate_upperUnipotent3 v (hstab g) (x, y, z)
  simp only at h
  rw [jacquetWhittaker3_apply, jacquetWhittaker3_apply,
    gl3AmbientRightTranslate_mul v (upperUnipotent3 x y z) g (cellSectionOf v χ Φ), h]

private def JacquetIntegrable (u : LocalGL3 v → ℂ) : Prop :=
  ∀ c : ℤ,
    letI := localBorel ℚ v
    IntegrableOn
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        psiLocal ℚ v (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2))
      (unipotentBall3 v c) (jacquetHaar3 v)

private theorem jacquetIntegrable_zero : JacquetIntegrable v 0 := by
  intro c
  letI := localBorel ℚ v
  simp only [Pi.zero_apply, mul_zero]
  exact integrableOn_zero

private theorem jacquetIntegrable_add {u u' : LocalGL3 v → ℂ} (hu : JacquetIntegrable v u) (hu' : JacquetIntegrable v u') :
    JacquetIntegrable v (u + u') := by
  intro c
  letI := localBorel ℚ v
  simp only [Pi.add_apply, mul_add]
  exact (hu c).add (hu' c)

private theorem jacquetTruncated3_add_of_jacquetIntegrable {u u' : LocalGL3 v → ℂ} (hu : JacquetIntegrable v u)
    (hu' : JacquetIntegrable v u') (c : ℤ) :
    jacquetTruncated3 v c (u + u') = jacquetTruncated3 v c u + jacquetTruncated3 v c u' :=
  jacquetTruncated3_add v c u u' (hu c) (hu' c)

private theorem jacquetTruncated3_zero (c : ℤ) : jacquetTruncated3 v c 0 = 0 := by
  simpa using jacquetTruncated3_smul v c (0 : ℂ) (0 : LocalGL3 v → ℂ)

private theorem stabilises_zero : Stabilises v 0 :=
  ⟨0, fun c _ => by rw [jacquetTruncated3_zero, jacquetTruncated3_zero]⟩

private theorem stabilises_add {u u' : LocalGL3 v → ℂ} (hu : JacquetIntegrable v u) (hu' : JacquetIntegrable v u')
    (hs : Stabilises v u) (hs' : Stabilises v u') : Stabilises v (u + u') := by
  obtain ⟨L, hL⟩ := hs
  obtain ⟨L', hL'⟩ := hs'
  refine ⟨max L L', fun c hc => ?_⟩
  rw [jacquetTruncated3_add_of_jacquetIntegrable v hu hu' c,
    jacquetTruncated3_add_of_jacquetIntegrable v hu hu' (max L L' : ℕ), hL c (by omega), hL' c (by omega),
    hL (max L L' : ℕ) (by omega), hL' (max L L' : ℕ) (by omega)]

private theorem jacquetValue_zero : jacquetValue v 0 = 0 := by
  unfold jacquetValue
  exact jacquetTruncated3_zero v _

private theorem jacquetValue_add {u u' : LocalGL3 v → ℂ} (hu : JacquetIntegrable v u) (hu' : JacquetIntegrable v u')
    (hs : Stabilises v u) (hs' : Stabilises v u') :
    jacquetValue v (u + u') = jacquetValue v u + jacquetValue v u' := by
  have hsum : Stabilises v (u + u') := stabilises_add v hu hu' hs hs'
  obtain ⟨L, hL⟩ := hs
  obtain ⟨L', hL'⟩ := hs'
  set c : ℕ := max (max L L') (jacquetLevel v (u + u')) with hc
  have h1 := jacquetTruncated3_eq_jacquetValue v (u + u') hsum (c := (c : ℤ))
    (by exact_mod_cast le_max_right (max L L') (jacquetLevel v (u + u')))
  have h2 := jacquetTruncated3_eq_jacquetValue v u ⟨L, hL⟩ (c := (c : ℤ))
    (by exact_mod_cast (jacquetLevel_le v u hL).trans ((le_max_left L L').trans (le_max_left _ _)))
  have h3 := jacquetTruncated3_eq_jacquetValue v u' ⟨L', hL'⟩ (c := (c : ℤ))
    (by exact_mod_cast (jacquetLevel_le v u' hL').trans ((le_max_right L L').trans (le_max_left _ _)))
  rw [← h1, ← h2, ← h3]
  exact jacquetTruncated3_add_of_jacquetIntegrable v hu hu' c

private theorem jacquetIntegrable_sum {ι : Type*} (s : Finset ι) (f : ι → LocalGL3 v → ℂ)
    (hf : ∀ i ∈ s, JacquetIntegrable v (f i)) : JacquetIntegrable v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jacquetIntegrable_zero v
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact jacquetIntegrable_add v (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem stabilises_sum {ι : Type*} (s : Finset ι) (f : ι → LocalGL3 v → ℂ)
    (hf : ∀ i ∈ s, JacquetIntegrable v (f i)) (hs : ∀ i ∈ s, Stabilises v (f i)) :
    Stabilises v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using stabilises_zero v
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact stabilises_add v (hf a (Finset.mem_insert_self a s))
      (jacquetIntegrable_sum v s f fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (hs a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) fun i hi => hs i (Finset.mem_insert_of_mem hi))

private theorem jacquetValue_sum {ι : Type*} (s : Finset ι) (f : ι → LocalGL3 v → ℂ)
    (hf : ∀ i ∈ s, JacquetIntegrable v (f i)) (hs : ∀ i ∈ s, Stabilises v (f i)) :
    jacquetValue v (∑ i ∈ s, f i) = ∑ i ∈ s, jacquetValue v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jacquetValue_zero v
  | @insert a s ha ih =>
    have hf' : ∀ i ∈ s, JacquetIntegrable v (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hs' : ∀ i ∈ s, Stabilises v (f i) := fun i hi => hs i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      jacquetValue_add v (hf a (Finset.mem_insert_self a s)) (jacquetIntegrable_sum v s f hf')
        (hs a (Finset.mem_insert_self a s)) (stabilises_sum v s f hf' hs'),
      ih hf' hs']

private theorem jacquetIntegrable_and_stabilises_of_exists_forall_le (u : LocalGL3 v → ℂ)
    (h : letI := localBorel ℚ v
      ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
        IntegrableOn
          (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
            psiLocal ℚ v (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2))
          (unipotentBall3 v c) (jacquetHaar3 v) ∧
        jacquetTruncated3 v c u = jacquetTruncated3 v c₀ u) :
    JacquetIntegrable v u ∧ Stabilises v u := by
  obtain ⟨c₀, hc₀⟩ := h
  refine ⟨fun c => ?_, ⟨c₀, fun c hc => (hc₀ c hc).2⟩⟩
  by_cases hc : (c₀ : ℤ) ≤ c
  · exact (hc₀ c hc).1
  · exact (hc₀ c₀ le_rfl).1.mono_set (unipotentBall3_mono v (le_of_lt (not_le.mp hc)))

end PsiLaw

end PsiLawUnit

namespace InvarianceUnit

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem gl3Entry_mul (g k : LocalGL3 v) (i j : Fin 3) :
    gl3Entry v (g * k) i j =
      gl3Entry v g i 0 * gl3Entry v k 0 j + gl3Entry v g i 1 * gl3Entry v k 1 j +
        gl3Entry v g i 2 * gl3Entry v k 2 j := by
  simp only [gl3Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private def rightMinor (g : LocalGL3 v) : v.adicCompletion ℚ :=
  gl3Entry v g 1 1 * gl3Entry v g 2 2 - gl3Entry v g 1 2 * gl3Entry v g 2 1

private theorem cornerEntry_mul_rightMinor (g : LocalGL3 v) :
    cornerEntry v g * rightMinor v g = gl3Entry v g 2 1 * outerMinor v g - gl3Entry v g 2 2 * lowerMinor v g := by
  simp only [cornerEntry, rightMinor, outerMinor, lowerMinor]
  ring

private theorem cornerEntry_mul (g k : LocalGL3 v) :
    cornerEntry v (g * k) =
      cornerEntry v g * gl3Entry v k 0 0 + gl3Entry v g 2 1 * gl3Entry v k 1 0 +
        gl3Entry v g 2 2 * gl3Entry v k 2 0 := by
  simp only [cornerEntry, gl3Entry_mul]

private theorem lowerMinor_mul (g k : LocalGL3 v) :
    lowerMinor v (g * k) =
      lowerMinor v g * (gl3Entry v k 0 0 * gl3Entry v k 1 1 - gl3Entry v k 0 1 * gl3Entry v k 1 0) +
        outerMinor v g * (gl3Entry v k 0 0 * gl3Entry v k 2 1 - gl3Entry v k 0 1 * gl3Entry v k 2 0) +
          rightMinor v g * (gl3Entry v k 1 0 * gl3Entry v k 2 1 - gl3Entry v k 1 1 * gl3Entry v k 2 0) := by
  simp only [lowerMinor, outerMinor, rightMinor, gl3Entry_mul]
  ring

private theorem outerMinor_mul (g k : LocalGL3 v) :
    outerMinor v (g * k) =
      lowerMinor v g * (gl3Entry v k 0 0 * gl3Entry v k 1 2 - gl3Entry v k 0 2 * gl3Entry v k 1 0) +
        outerMinor v g * (gl3Entry v k 0 0 * gl3Entry v k 2 2 - gl3Entry v k 0 2 * gl3Entry v k 2 0) +
          rightMinor v g * (gl3Entry v k 1 0 * gl3Entry v k 2 2 - gl3Entry v k 1 2 * gl3Entry v k 2 0) := by
  simp only [lowerMinor, outerMinor, rightMinor, gl3Entry_mul]
  ring

private theorem gl3Det_mul (g k : LocalGL3 v) : gl3Det v (g * k) = gl3Det v g * gl3Det v k := by
  simp only [gl3Det, Units.val_mul, Matrix.det_mul]

private theorem cellRatio_zero_mul_cornerEntry {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) :
    cellRatio v g 0 * cornerEntry v g = gl3Entry v g 2 1 := by
  show gl3Entry v g 2 1 / cornerEntry v g * cornerEntry v g = gl3Entry v g 2 1
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self hc, mul_one]

private theorem cellRatio_one_mul_cornerEntry {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) :
    cellRatio v g 1 * cornerEntry v g = gl3Entry v g 2 2 := by
  show gl3Entry v g 2 2 / cornerEntry v g * cornerEntry v g = gl3Entry v g 2 2
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self hc, mul_one]

private theorem cellRatio_two_mul_lowerMinor {g : LocalGL3 v} (hl : lowerMinor v g ≠ 0) :
    cellRatio v g 2 * lowerMinor v g = outerMinor v g := by
  show outerMinor v g / lowerMinor v g * lowerMinor v g = outerMinor v g
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self hl, mul_one]

private theorem rightMinor_eq_of_ne_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0) :
    rightMinor v g = (cellRatio v g 0 * cellRatio v g 2 - cellRatio v g 1) * lowerMinor v g := by
  apply mul_left_cancel₀ hc
  rw [cornerEntry_mul_rightMinor, ← cellRatio_zero_mul_cornerEntry v hc, ← cellRatio_one_mul_cornerEntry v hc,
    ← cellRatio_two_mul_lowerMinor v hl]
  ring

private theorem cornerEntry_mul_of_ne_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (k : LocalGL3 v) :
    cornerEntry v (g * k) =
      cornerEntry v g *
        (gl3Entry v k 0 0 + cellRatio v g 0 * gl3Entry v k 1 0 + cellRatio v g 1 * gl3Entry v k 2 0) := by
  rw [cornerEntry_mul, ← cellRatio_zero_mul_cornerEntry v hc, ← cellRatio_one_mul_cornerEntry v hc]
  ring

private theorem gl3Entry_two_one_mul_of_ne_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (k : LocalGL3 v) :
    gl3Entry v (g * k) 2 1 =
      cornerEntry v g *
        (gl3Entry v k 0 1 + cellRatio v g 0 * gl3Entry v k 1 1 + cellRatio v g 1 * gl3Entry v k 2 1) := by
  rw [gl3Entry_mul, ← cellRatio_zero_mul_cornerEntry v hc, ← cellRatio_one_mul_cornerEntry v hc]
  simp only [cornerEntry]
  ring

private theorem gl3Entry_two_two_mul_of_ne_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (k : LocalGL3 v) :
    gl3Entry v (g * k) 2 2 =
      cornerEntry v g *
        (gl3Entry v k 0 2 + cellRatio v g 0 * gl3Entry v k 1 2 + cellRatio v g 1 * gl3Entry v k 2 2) := by
  rw [gl3Entry_mul, ← cellRatio_zero_mul_cornerEntry v hc, ← cellRatio_one_mul_cornerEntry v hc]
  simp only [cornerEntry]
  ring

private theorem lowerMinor_mul_of_ne_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0)
    (k : LocalGL3 v) :
    lowerMinor v (g * k) =
      lowerMinor v g *
        ((gl3Entry v k 0 0 * gl3Entry v k 1 1 - gl3Entry v k 0 1 * gl3Entry v k 1 0) +
          cellRatio v g 2 * (gl3Entry v k 0 0 * gl3Entry v k 2 1 - gl3Entry v k 0 1 * gl3Entry v k 2 0) +
            (cellRatio v g 0 * cellRatio v g 2 - cellRatio v g 1) *
              (gl3Entry v k 1 0 * gl3Entry v k 2 1 - gl3Entry v k 1 1 * gl3Entry v k 2 0)) := by
  rw [lowerMinor_mul, ← cellRatio_two_mul_lowerMinor v hl, rightMinor_eq_of_ne_zero v hc hl]
  ring

private theorem outerMinor_mul_of_ne_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0)
    (k : LocalGL3 v) :
    outerMinor v (g * k) =
      lowerMinor v g *
        ((gl3Entry v k 0 0 * gl3Entry v k 1 2 - gl3Entry v k 0 2 * gl3Entry v k 1 0) +
          cellRatio v g 2 * (gl3Entry v k 0 0 * gl3Entry v k 2 2 - gl3Entry v k 0 2 * gl3Entry v k 2 0) +
            (cellRatio v g 0 * cellRatio v g 2 - cellRatio v g 1) *
              (gl3Entry v k 1 0 * gl3Entry v k 2 2 - gl3Entry v k 1 2 * gl3Entry v k 2 0)) := by
  rw [outerMinor_mul, ← cellRatio_two_mul_lowerMinor v hl, rightMinor_eq_of_ne_zero v hc hl]
  ring

end InvarianceUnit

namespace InvarianceUnit

open Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def shellWeight (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (e : ℤ) (t : v.adicCompletion ℚ) : ℂ :=
  if Valued.v t = WithZero.exp e then charExt ξ t else 0

private theorem shellWeight_of_valued_eq (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {e : ℤ} {t : v.adicCompletion ℚ}
    (ht : Valued.v t = WithZero.exp e) : shellWeight v ξ e t = charExt ξ t := by
  simp [shellWeight, ht]

private theorem shellWeight_of_valued_ne (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {e : ℤ} {t : v.adicCompletion ℚ}
    (ht : Valued.v t ≠ WithZero.exp e) : shellWeight v ξ e t = 0 := by
  simp [shellWeight, ht]

private theorem shellWeight_units_mul (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (e : ℤ) {u : (v.adicCompletion ℚ)ˣ}
    (hu : Valued.v (u : v.adicCompletion ℚ) = 1) (t : v.adicCompletion ℚ) :
    shellWeight v ξ e ((u : v.adicCompletion ℚ) * t) = (ξ u : ℂ) * shellWeight v ξ e t := by
  have hv : Valued.v ((u : v.adicCompletion ℚ) * t) = Valued.v t := by rw [map_mul, hu, one_mul]
  by_cases ht : Valued.v t = WithZero.exp e
  · rw [shellWeight_of_valued_eq v ξ (hv.trans ht), shellWeight_of_valued_eq v ξ ht, charExt_units_mul]
  · rw [shellWeight_of_valued_ne v ξ (hv.symm ▸ ht), shellWeight_of_valued_ne v ξ ht, mul_zero]

private theorem shellWeight_higherUnits_mul (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {c : ℕ}
    (hξ : HasConductorExponentAt ℚ v ξ c) (e : ℤ) {u : (v.adicCompletion ℚ)ˣ} (hu : u ∈ higherUnitsAt ℚ v c)
    (t : v.adicCompletion ℚ) :
    shellWeight v ξ e ((u : v.adicCompletion ℚ) * t) = shellWeight v ξ e t := by
  rw [shellWeight_units_mul v ξ e ((mem_higherUnitsAt_iff ℚ v).mp hu).1, hξ.1 u hu, Units.val_one, one_mul]

private theorem shellWeight_add_of_valued_le (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {c : ℕ}
    (hξ : HasConductorExponentAt ℚ v ξ c) (hc : 1 ≤ c) {e : ℤ} {t s : v.adicCompletion ℚ}
    (ht : Valued.v t = WithZero.exp e) (hs : Valued.v s ≤ WithZero.exp (e - c)) :
    shellWeight v ξ e (t + s) = shellWeight v ξ e t := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at ht
    exact WithZero.exp_ne_zero ht.symm
  have hw : Valued.v (s / t) ≤ WithZero.exp (-(c : ℤ)) := by
    rw [map_div₀, ht, div_le_iff₀ (by simp), ← WithZero.exp_add]
    simpa [sub_eq_add_neg, add_comm] using hs
  have hw1 : Valued.v (s / t) < 1 := by
    refine lt_of_le_of_lt hw ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hu1 : Valued.v (1 + s / t) = 1 := Valuation.map_one_add_of_lt _ hw1
  have hne : (1 + s / t) ≠ 0 := by
    intro h
    rw [h, map_zero] at hu1
    exact zero_ne_one hu1
  set u : (v.adicCompletion ℚ)ˣ := Units.mk0 _ hne with hu_def
  have hu : u ∈ higherUnitsAt ℚ v c := by
    refine (mem_higherUnitsAt_iff ℚ v).mpr ⟨hu1, Or.inr ?_⟩
    simpa [hu_def] using hw
  have hts : t + s = (u : v.adicCompletion ℚ) * t := by
    simp only [hu_def, Units.val_mk0]
    field_simp
  rw [hts, shellWeight_higherUnits_mul v ξ hξ e hu]

private theorem valued_det_le_one_of_entries {M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)}
    (hM : ∀ i j, Valued.v (M i j) ≤ 1) : Valued.v M.det ≤ 1 := by
  rw [Matrix.det_fin_three]
  have h3 : ∀ i j k l m n : Fin 3, Valued.v (M i j * M k l * M m n) ≤ 1 := fun i j k l m n => by
    rw [map_mul, map_mul]
    exact mul_le_one' (mul_le_one' (hM i j) (hM k l)) (hM m n)

  exact Valuation.map_sub_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_sub_le _
    (Valuation.map_sub_le _ (h3 0 0 1 1 2 2) (h3 0 0 1 2 2 1)) (h3 0 1 1 0 2 2)) (h3 0 1 1 2 2 0))
    (h3 0 2 1 0 2 1)) (h3 0 2 1 1 2 0)

private theorem valued_det_eq_one_of_mem_localMaximalCompact3 {k : LocalGL3 v}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) = 1 := by
  obtain ⟨hk₁, hk₂⟩ := (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk
  have hd : Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) ≤ 1 :=
    valued_det_le_one_of_entries v hk₁
  have hd' : Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) ≤ 1 :=
    valued_det_le_one_of_entries v hk₂
  have hprod : Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) *
      Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  refine le_antisymm hd ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ * _ := hprod.symm
    _ ≤ Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) * 1 := mul_le_mul' le_rfl hd'
    _ = _ := mul_one _

private theorem converseCongruenceSet3_mul_mem {a : ℕ} {k k' : LocalGL3 v} (hk : k ∈ converseCongruenceSet3 v a)
    (hk' : k' ∈ converseCongruenceSet3 v a) : k * k' ∈ converseCongruenceSet3 v a := by
  obtain ⟨hkK, h01, h20, h21⟩ := hk
  obtain ⟨hkK', h01', h20', h21'⟩ := hk'
  have hi := ((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hkK).1
  have hi' := ((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hkK').1
  have h2a : WithZero.exp (-(2 * (a : ℤ))) ≤ WithZero.exp (-(a : ℤ)) := by
    rw [WithZero.exp_le_exp]
    omega

  have hL : ∀ {x y : v.adicCompletion ℚ} {d : WithZero (Multiplicative ℤ)},
      Valued.v x ≤ 1 → Valued.v y ≤ d → Valued.v (x * y) ≤ d :=
    fun hx hy => by rw [map_mul]; simpa using mul_le_mul' hx hy
  have hR : ∀ {x y : v.adicCompletion ℚ} {d : WithZero (Multiplicative ℤ)},
      Valued.v x ≤ d → Valued.v y ≤ 1 → Valued.v (x * y) ≤ d :=
    fun hx hy => by rw [map_mul]; simpa using mul_le_mul' hx hy
  refine ⟨mul_mem hkK hkK', ?_, ?_, ?_⟩ <;>
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  · exact Valuation.map_add_le _ (Valuation.map_add_le _ (hL (hi 0 0) h01') (hR h01 (hi' 1 1)))
      (le_trans (hL (hi 0 2) h21') h2a)
  · exact Valuation.map_add_le _ (Valuation.map_add_le _ (hR h20 (hi' 0 0)) (le_trans (hR h21 (hi' 1 0)) h2a))
      (hL (hi 2 2) h20')
  · refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ (hR h21 (hi' 1 1))) (hL (hi 2 2) h21')
    rw [map_mul]
    calc Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0) *
          Valued.v ((k' : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1)
        ≤ WithZero.exp (-(a : ℤ)) * WithZero.exp (-(a : ℤ)) := mul_le_mul' h20 h01'
      _ = WithZero.exp (-(2 * (a : ℤ))) := by rw [← WithZero.exp_add]; ring_nf

private theorem converseCongruenceSet3_inv_mem {a : ℕ} {k : LocalGL3 v} (hk : k ∈ converseCongruenceSet3 v a) :
    k⁻¹ ∈ converseCongruenceSet3 v a := by
  obtain ⟨hkK, h01, h20, h21⟩ := hk
  have hi := ((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hkK).1
  have hdet := valued_det_eq_one_of_mem_localMaximalCompact3 v hkK
  have h2a : WithZero.exp (-(2 * (a : ℤ))) ≤ WithZero.exp (-(a : ℤ)) := by
    rw [WithZero.exp_le_exp]
    omega
  have hL : ∀ {x y : v.adicCompletion ℚ} {d : WithZero (Multiplicative ℤ)},
      Valued.v x ≤ 1 → Valued.v y ≤ d → Valued.v (x * y) ≤ d :=
    fun hx hy => by rw [map_mul]; simpa using mul_le_mul' hx hy
  have hR : ∀ {x y : v.adicCompletion ℚ} {d : WithZero (Multiplicative ℤ)},
      Valued.v x ≤ d → Valued.v y ≤ 1 → Valued.v (x * y) ≤ d :=
    fun hx hy => by rw [map_mul]; simpa using mul_le_mul' hx hy

  have hinv : ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det)⁻¹ •
        (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  have hdinv : Valued.v (((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det)⁻¹) ≤ 1 := by
    rw [map_inv₀, hdet, inv_one]
  refine ⟨inv_mem hkK, ?_, ?_, ?_⟩ <;>
    rw [hinv, Matrix.smul_apply, smul_eq_mul] <;> refine hL hdinv ?_ <;>
    simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one]
  ·
    refine Valuation.map_add_le _ ?_ (le_trans (hL (hi 0 2) h21) h2a)
    rw [Valuation.map_neg]
    exact hR h01 (hi 2 2)
  ·
    exact Valuation.map_sub_le _ (le_trans (hL (hi 1 0) h21) h2a) (hL (hi 1 1) h20)
  ·
    refine Valuation.map_add_le _ ?_ ?_
    · rw [Valuation.map_neg]
      exact hL (hi 0 0) h21
    · rw [map_mul]
      calc Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1) *
            Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0)
          ≤ WithZero.exp (-(a : ℤ)) * WithZero.exp (-(a : ℤ)) := mul_le_mul' h01 h20
        _ = WithZero.exp (-(2 * (a : ℤ))) := by rw [← WithZero.exp_add]; ring_nf

private def converseCongruenceSubgroup3 (a : ℕ) : Subgroup (LocalGL3 v) where
  carrier := converseCongruenceSet3 v a
  one_mem' := one_mem_converseCongruenceSet3 v a
  mul_mem' := converseCongruenceSet3_mul_mem v
  inv_mem' := converseCongruenceSet3_inv_mem v

private theorem mem_converseCongruenceSubgroup3_iff (a : ℕ) (k : LocalGL3 v) :
    k ∈ converseCongruenceSubgroup3 v a ↔ k ∈ converseCongruenceSet3 v a :=
  Iff.rfl

end InvarianceUnit

namespace InvarianceUnit

open Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem rightMinor_mul (g k : LocalGL3 v) :
    rightMinor v (g * k) =
      lowerMinor v g * (gl3Entry v k 0 1 * gl3Entry v k 1 2 - gl3Entry v k 0 2 * gl3Entry v k 1 1) +
        outerMinor v g * (gl3Entry v k 0 1 * gl3Entry v k 2 2 - gl3Entry v k 0 2 * gl3Entry v k 2 1) +
          rightMinor v g * (gl3Entry v k 1 1 * gl3Entry v k 2 2 - gl3Entry v k 1 2 * gl3Entry v k 2 1) := by
  simp only [rightMinor, lowerMinor, outerMinor, gl3Entry_mul]
  ring

private def cellInvariant (g : LocalGL3 v) : v.adicCompletion ℚ :=
  cellRatio v g 1 - cellRatio v g 0 * cellRatio v g 2

private theorem cellRatio_zero (g : LocalGL3 v) : cellRatio v g 0 = gl3Entry v g 2 1 / cornerEntry v g := rfl

private theorem cellRatio_one (g : LocalGL3 v) : cellRatio v g 1 = gl3Entry v g 2 2 / cornerEntry v g := rfl

private theorem cellRatio_two (g : LocalGL3 v) : cellRatio v g 2 = outerMinor v g / lowerMinor v g := rfl

private theorem cellInvariant_eq_of_ne_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0) :
    cellInvariant v g = -(rightMinor v g / lowerMinor v g) := by
  have h := cornerEntry_mul_rightMinor v g
  unfold cellInvariant
  rw [cellRatio_zero, cellRatio_one, cellRatio_two]
  field_simp
  linear_combination h

private theorem charExt_mul_of_ne_zero (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {x y : v.adicCompletion ℚ} (hx : x ≠ 0)
    (_hy : y ≠ 0) : charExt ξ (x * y) = charExt ξ x * charExt ξ y := by
  have hxy : x * y = ((Units.mk0 x hx : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * y := by simp
  rw [hxy, charExt_units_mul, charExt_of_ne_zero ξ hx]

private theorem charExt_one_add_of_valued_le (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {c : ℕ}
    (hξ : HasConductorExponentAt ℚ v ξ c) (hc : 1 ≤ c) {w : v.adicCompletion ℚ}
    (hw : Valued.v w ≤ WithZero.exp (-(c : ℤ))) : charExt ξ (1 + w) = 1 := by
  have hw1 : Valued.v w < 1 := by
    refine lt_of_le_of_lt hw ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hu1 : Valued.v (1 + w) = 1 := Valuation.map_one_add_of_lt _ hw1
  have hne : (1 + w) ≠ 0 := by
    intro h
    rw [h, map_zero] at hu1
    exact zero_ne_one hu1
  have hu : Units.mk0 (1 + w) hne ∈ higherUnitsAt ℚ v c :=
    (mem_higherUnitsAt_iff ℚ v).mpr ⟨hu1, Or.inr (by simpa using hw)⟩
  rw [charExt_of_ne_zero ξ hne, hξ.1 _ hu, Units.val_one]

private theorem hasConductorExponentAt_inv' {ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {c : ℕ}
    (hξ : HasConductorExponentAt ℚ v ξ c) : HasConductorExponentAt ℚ v ξ⁻¹ c := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · show (ξ u)⁻¹ = 1
    rw [hξ.1 u hu, inv_one]
  · obtain ⟨u, hu, hne⟩ := hξ.2 m hm
    refine ⟨u, hu, ?_⟩
    show (ξ u)⁻¹ ≠ 1
    exact fun h => hne (inv_eq_one.mp h)

private theorem norm_eq_one_of_valued_eq_one {x : v.adicCompletion ℚ} (hx : Valued.v x = 1) : ‖x‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def, hx, map_one, NNReal.coe_one]

private def conductorDatum (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ) (r : Fin 3 → v.adicCompletion ℚ) :
    ℂ :=
  (if Valued.v (r 2) ≤ 1 then (1 : ℂ) else 0) *
    (if Valued.v (r 1) ≤ WithZero.exp (-(a₂ : ℤ)) then (1 : ℂ) else 0) *
      shellWeight v (ν 0)⁻¹ (-((a₁ : ℤ) + a₂)) (r 1 - r 0 * r 2) * shellWeight v (ν 1)⁻¹ (-(a₂ : ℤ)) (r 0)

private theorem conductorDatum_support (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ)
    {r : Fin 3 → v.adicCompletion ℚ} (hr : conductorDatum v ν a₁ a₂ r ≠ 0) :
    Valued.v (r 2) ≤ 1 ∧ Valued.v (r 1) ≤ WithZero.exp (-(a₂ : ℤ)) ∧
      Valued.v (r 1 - r 0 * r 2) = WithZero.exp (-((a₁ : ℤ) + a₂)) ∧ Valued.v (r 0) = WithZero.exp (-(a₂ : ℤ)) := by
  unfold conductorDatum at hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra h
    rw [if_neg h] at hr
    simp at hr
  · by_contra h
    rw [if_neg h] at hr
    simp at hr
  · by_contra h
    rw [shellWeight_of_valued_ne v _ h] at hr
    simp at hr
  · by_contra h
    rw [shellWeight_of_valued_ne v _ h] at hr
    simp at hr

private theorem conductorDatum_apply_of_support (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ)
    {r : Fin 3 → v.adicCompletion ℚ} (h2 : Valued.v (r 2) ≤ 1) (h1 : Valued.v (r 1) ≤ WithZero.exp (-(a₂ : ℤ)))
    (hQ : Valued.v (r 1 - r 0 * r 2) = WithZero.exp (-((a₁ : ℤ) + a₂)))
    (h0 : Valued.v (r 0) = WithZero.exp (-(a₂ : ℤ))) :
    conductorDatum v ν a₁ a₂ r = charExt (ν 0)⁻¹ (r 1 - r 0 * r 2) * charExt (ν 1)⁻¹ (r 0) := by
  unfold conductorDatum
  rw [if_pos h2, if_pos h1, shellWeight_of_valued_eq v _ hQ, shellWeight_of_valued_eq v _ h0]
  ring

private def cellSupport (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ) : Set (LocalGL3 v) :=
  {y | y ∈ bigCell3 v ∧ conductorDatum v ν a₁ a₂ (cellRatio v y) ≠ 0}

private theorem cellSectionOf_conductorDatum_eq_zero_of_notMem (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ)
    {y : LocalGL3 v} (hy : y ∉ cellSupport v ν a₁ a₂) : cellSectionOf v ν (conductorDatum v ν a₁ a₂) y = 0 := by
  by_cases hc : y ∈ bigCell3 v
  · have hΦ : conductorDatum v ν a₁ a₂ (cellRatio v y) = 0 := by
      by_contra h
      exact hy ⟨hc, h⟩
    rw [cellSectionOf_apply_of_mem v _ _ hc, hΦ, mul_zero]
  · exact cellSectionOf_apply_of_notMem v _ _ hc

private theorem cellSectionOf_conductorDatum_apply_of_mem (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℕ)
    {y : LocalGL3 v} (hy : y ∈ cellSupport v ν a₁ a₂) :
    cellSectionOf v ν (conductorDatum v ν a₁ a₂) y = cellValue v ν y * conductorDatum v ν a₁ a₂ (cellRatio v y) :=
  cellSectionOf_apply_of_mem v _ _ hy.1

end InvarianceUnit

namespace InvarianceUnit

open Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem exists_eq_mul_one_add_of_valued_sub_le {M E : v.adicCompletion ℚ} (hM : M ≠ 0) {c : ℕ}
    (h : Valued.v (E - M) ≤ Valued.v M * WithZero.exp (-(c : ℤ))) :
    ∃ w : v.adicCompletion ℚ, E = M * (1 + w) ∧ Valued.v w ≤ WithZero.exp (-(c : ℤ)) := by
  refine ⟨(E - M) / M, by field_simp; ring, ?_⟩
  rw [map_div₀, div_le_iff₀ ((Valuation.pos_iff _).mpr hM)]
  simpa [mul_comm] using h

private theorem charExt_ne_zero (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    charExt ξ x ≠ 0 := by
  rw [charExt_of_ne_zero ξ hx]
  exact Units.ne_zero _

private theorem charExt_inv_apply (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (x : v.adicCompletion ℚ) :
    charExt ξ⁻¹ x = (charExt ξ x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [charExt_of_ne_zero _ hx, charExt_of_ne_zero ξ hx]
    show (((ξ (Units.mk0 x hx))⁻¹ : ℂˣ) : ℂ) = _
    rw [Units.val_inv_eq_inv_val]

private theorem charExt_mul_one_add (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {c : ℕ} (hξ : HasConductorExponentAt ℚ v ξ c)
    (hc : 1 ≤ c) {M w : v.adicCompletion ℚ} (hM : M ≠ 0) (hw : Valued.v w ≤ WithZero.exp (-(c : ℤ))) :
    charExt ξ (M * (1 + w)) = charExt ξ M := by
  have h1 : (1 + w) ≠ 0 := by
    intro h
    have := charExt_one_add_of_valued_le v ξ hξ hc hw
    rw [h, charExt_zero] at this
    exact zero_ne_one this
  rw [charExt_mul_of_ne_zero v ξ hM h1, charExt_one_add_of_valued_le v ξ hξ hc hw, mul_one]

private theorem charExt_mul_one_add_of_le (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {c' c : ℕ}
    (hξ : HasConductorExponentAt ℚ v ξ c') (hc' : 1 ≤ c') (hcc : c' ≤ c) {M w : v.adicCompletion ℚ} (hM : M ≠ 0)
    (hw : Valued.v w ≤ WithZero.exp (-(c : ℤ))) : charExt ξ (M * (1 + w)) = charExt ξ M :=
  charExt_mul_one_add v ξ hξ hc' hM (hw.trans (by rw [WithZero.exp_le_exp]; omega))

private theorem valued_one_add_eq_one {w : v.adicCompletion ℚ} {c : ℕ} (hc : 1 ≤ c)
    (hw : Valued.v w ≤ WithZero.exp (-(c : ℤ))) : Valued.v (1 + w) = 1 := by
  refine Valuation.map_one_add_of_lt _ (lt_of_le_of_lt hw ?_)
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

private structure IsOppositeCongruence (a : ℕ) (k : LocalGL3 v) : Prop where
  mem : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v
  h21 : Valued.v (gl3Entry v k 2 1) ≤ WithZero.exp (-(a : ℤ))
  h02 : Valued.v (gl3Entry v k 0 2) ≤ WithZero.exp (-(a : ℤ))
  h01 : Valued.v (gl3Entry v k 0 1) ≤ WithZero.exp (-(2 * (a : ℤ)))

private theorem antidiagonal3_mul_antidiagonal3 : antidiagonal3 v * antidiagonal3 v = 1 := by
  ext i j
  rw [Units.val_mul, antidiagonal3_coe, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem antidiagonal3_mem_localMaximalCompact3 : antidiagonal3 v ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
  have hinv : (antidiagonal3 v)⁻¹ = antidiagonal3 v := inv_eq_of_mul_eq_one_right (antidiagonal3_mul_antidiagonal3 v)
  refine (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mpr ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [antidiagonal3_coe]
    fin_cases i <;> fin_cases j <;> simp
  · rw [hinv, antidiagonal3_coe]
    fin_cases i <;> fin_cases j <;> simp

private theorem gl3Entry_antidiagonal3_mul_mul_antidiagonal3 (k : LocalGL3 v) (i j : Fin 3) :
    gl3Entry v (antidiagonal3 v * k * antidiagonal3 v) i j = gl3Entry v k (Fin.rev i) (Fin.rev j) := by
  simp only [gl3Entry, Units.val_mul, antidiagonal3_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

private theorem isOppositeCongruence_conj {a : ℕ} {k : LocalGL3 v} (hk : k ∈ converseCongruenceSet3 v a) :
    IsOppositeCongruence v a (antidiagonal3 v * k * antidiagonal3 v) := by
  obtain ⟨hkK, h01, h20, h21⟩ := hk
  have hw := antidiagonal3_mem_localMaximalCompact3 v
  refine ⟨mul_mem (mul_mem hw hkK) hw, ?_, ?_, ?_⟩ <;> rw [gl3Entry_antidiagonal3_mul_mul_antidiagonal3]
  · exact h01
  · exact h20
  · exact h21

private theorem gl3Entry_conj_zero_zero (k : LocalGL3 v) :
    gl3Entry v (antidiagonal3 v * k * antidiagonal3 v) 0 0 = gl3Entry v k 2 2 := by
  rw [gl3Entry_antidiagonal3_mul_mul_antidiagonal3]
  rfl

private theorem IsOppositeCongruence.diag_valued {a : ℕ} (ha : 1 ≤ a) {k : LocalGL3 v} (hk : IsOppositeCongruence v a k) :
    Valued.v (gl3Entry v k 0 0) = 1 ∧ Valued.v (gl3Entry v k 1 1) = 1 ∧ Valued.v (gl3Entry v k 2 2) = 1 := by
  have hi := ((mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ v).mp hk.mem).1
  have hdet : Valued.v (gl3Det v k) = 1 := valued_det_eq_one_of_mem_localMaximalCompact3 v hk.mem
  have ha' : WithZero.exp (-(a : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have h2a : WithZero.exp (-(2 * (a : ℤ))) ≤ WithZero.exp (-(a : ℤ)) := by
    rw [WithZero.exp_le_exp]
    omega

  have hL : ∀ {x y : v.adicCompletion ℚ} {d : WithZero (Multiplicative ℤ)},
      Valued.v x ≤ 1 → Valued.v y ≤ d → Valued.v (x * y) ≤ d :=
    fun hx hy => by rw [map_mul]; simpa using mul_le_mul' hx hy
  have hrest : Valued.v (gl3Det v k - gl3Entry v k 0 0 * gl3Entry v k 1 1 * gl3Entry v k 2 2) ≤
      WithZero.exp (-(a : ℤ)) := by
    have hexp : gl3Det v k - gl3Entry v k 0 0 * gl3Entry v k 1 1 * gl3Entry v k 2 2 =
        -(gl3Entry v k 0 0 * (gl3Entry v k 1 2 * gl3Entry v k 2 1)) -
          gl3Entry v k 1 0 * (gl3Entry v k 2 2 * gl3Entry v k 0 1) +
            gl3Entry v k 1 2 * (gl3Entry v k 2 0 * gl3Entry v k 0 1) +
              gl3Entry v k 1 0 * (gl3Entry v k 2 1 * gl3Entry v k 0 2) -
                gl3Entry v k 1 1 * (gl3Entry v k 2 0 * gl3Entry v k 0 2) := by
      simp only [gl3Det, gl3Entry, Matrix.det_fin_three]
      ring
    rw [hexp]
    refine Valuation.map_sub_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_sub_le _ ?_ ?_) ?_)
      ?_) ?_
    · rw [Valuation.map_neg]
      exact hL (hi 0 0) (hL (hi 1 2) hk.h21)
    · exact hL (hi 1 0) (le_trans (hL (hi 2 2) hk.h01) h2a)
    · exact hL (hi 1 2) (le_trans (hL (hi 2 0) hk.h01) h2a)
    · exact hL (hi 1 0) (hL (hi 2 1) hk.h02)
    · exact hL (hi 1 1) (hL (hi 2 0) hk.h02)
  have hlead : Valued.v (gl3Entry v k 0 0 * gl3Entry v k 1 1 * gl3Entry v k 2 2) = 1 := by
    have hrest' : Valued.v (gl3Det v k - gl3Entry v k 0 0 * gl3Entry v k 1 1 * gl3Entry v k 2 2) <
        Valued.v (gl3Det v k) := by
      rw [hdet]
      exact lt_of_le_of_lt hrest ha'
    have := Valuation.map_sub_eq_of_lt_left _ hrest'
    rw [hdet] at this

    simpa using this
  rw [map_mul, map_mul] at hlead
  have h00 := hi 0 0
  have h11 := hi 1 1
  have h22 := hi 2 2
  refine ⟨le_antisymm h00 ?_, le_antisymm h11 ?_, le_antisymm h22 ?_⟩
  · calc (1 : WithZero (Multiplicative ℤ)) = _ := hlead.symm
      _ ≤ Valued.v (gl3Entry v k 0 0) * 1 * 1 := mul_le_mul' (mul_le_mul' le_rfl h11) h22
      _ = _ := by simp
  · calc (1 : WithZero (Multiplicative ℤ)) = _ := hlead.symm
      _ ≤ 1 * Valued.v (gl3Entry v k 1 1) * 1 := mul_le_mul' (mul_le_mul' h00 le_rfl) h22
      _ = _ := by simp
  · calc (1 : WithZero (Multiplicative ℤ)) = _ := hlead.symm
      _ ≤ 1 * 1 * Valued.v (gl3Entry v k 2 2) := mul_le_mul' (mul_le_mul' h00 h11) le_rfl
      _ = _ := by simp

end InvarianceUnit

namespace InvarianceUnit

open IsDedekindDomain NumberField Filter Topology LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

section OpenSubgroupPackaging

private def principalCongruenceSet3 (N : ℕ) : Set (LocalGL3 v) :=
  {k | ∀ i j : Fin 3, Valued.v (gl3Entry v k i j - gl3Entry v 1 i j) ≤ WithZero.exp (-(N : ℤ))}

private theorem mem_principalCongruenceSet3 (N : ℕ) (k : LocalGL3 v) :
    k ∈ principalCongruenceSet3 v N ↔
      ∀ i j : Fin 3, Valued.v (gl3Entry v k i j - gl3Entry v 1 i j) ≤ WithZero.exp (-(N : ℤ)) :=
  Iff.rfl

private theorem gl3Entry_one (i j : Fin 3) : gl3Entry v (1 : LocalGL3 v) i j = if i = j then 1 else 0 := by
  simp only [gl3Entry, Units.val_one, Matrix.one_apply]

private theorem one_mem_principalCongruenceSet3 (N : ℕ) : (1 : LocalGL3 v) ∈ principalCongruenceSet3 v N := by
  intro i j
  simp

private theorem isOpen_principalCongruenceSet3 (N : ℕ) : IsOpen (principalCongruenceSet3 v N) := by
  have hset : principalCongruenceSet3 v N = ⋂ i : Fin 3, ⋂ j : Fin 3,
      (fun k : LocalGL3 v => gl3Entry v k i j) ⁻¹'
        {t : v.adicCompletion ℚ | Valued.v (t - gl3Entry v 1 i j) ≤ WithZero.exp (-(N : ℤ))} := by
    ext k
    simp only [principalCongruenceSet3, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [hset]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isClopen_setOf_valued_sub_le v (gl3Entry v 1 i j) N).isOpen.preimage (continuous_gl3Entry v i j)

private theorem principalCongruenceSet3_mem_nhds_one (N : ℕ) : principalCongruenceSet3 v N ∈ 𝓝 (1 : LocalGL3 v) :=
  (isOpen_principalCongruenceSet3 v N).mem_nhds (one_mem_principalCongruenceSet3 v N)

private def rightStabilizer (W : LocalGL3 v → ℂ) : Subgroup (LocalGL3 v) where
  carrier := {k | ∀ g : LocalGL3 v, W (g * k) = W g}
  one_mem' := by
    intro g
    rw [mul_one]
  mul_mem' := by
    intro a b ha hb g
    rw [← mul_assoc, hb, ha]
  inv_mem' := by
    intro a ha g
    have h := ha (g * a⁻¹)
    rw [inv_mul_cancel_right] at h
    exact h.symm

private theorem mem_rightStabilizer (W : LocalGL3 v → ℂ) (k : LocalGL3 v) :
    k ∈ rightStabilizer v W ↔ ∀ g : LocalGL3 v, W (g * k) = W g :=
  Iff.rfl

private theorem exists_isOpen_subgroup_of_principalCongruenceSet3 (W : LocalGL3 v → ℂ) (N : ℕ)
    (h : ∀ k ∈ principalCongruenceSet3 v N, ∀ g : LocalGL3 v, W (g * k) = W g) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g := by
  refine ⟨rightStabilizer v W, ?_, fun k hk g => (mem_rightStabilizer v W k).mp hk g⟩
  refine Subgroup.isOpen_of_mem_nhds _ (mem_of_superset (principalCongruenceSet3_mem_nhds_one v N) ?_)
  intro k hk
  exact (mem_rightStabilizer v W k).mpr (h k hk)

end OpenSubgroupPackaging

end InvarianceUnit

namespace InvarianceUnit

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

section UniformConstants

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isOpen_box3 (c : Fin 3 → v.adicCompletion ℚ) (k : ℤ) :
    IsOpen {r : Fin 3 → v.adicCompletion ℚ | ∀ i, Valued.v (r i - c i) ≤ WithZero.exp (-k)} := by
  have hset : {r : Fin 3 → v.adicCompletion ℚ | ∀ i, Valued.v (r i - c i) ≤ WithZero.exp (-k)}
      = ⋂ i, (fun r : Fin 3 → v.adicCompletion ℚ => r i) ⁻¹'
          {y : v.adicCompletion ℚ | Valued.v (y - c i) ≤ WithZero.exp (-k)} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [hset]
  exact isOpen_iInter_of_finite fun i =>
    (isClopen_setOf_valued_sub_le v (c i) k).isOpen.preimage (continuous_apply i)

variable {v}

private theorem exists_box_of_hasCompactSupport (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦc : HasCompactSupport Φ) :
    ∃ R : ℕ, ∀ r : Fin 3 → v.adicCompletion ℚ, Φ r ≠ 0 → ∀ i, Valued.v (r i) ≤ WithZero.exp (R : ℤ) := by

  set V : ℕ → Set (Fin 3 → v.adicCompletion ℚ) := fun n =>
    {r | ∀ i, Valued.v (r i - (0 : Fin 3 → v.adicCompletion ℚ) i) ≤ WithZero.exp (-(-(n : ℤ)))} with hV
  have hVopen : ∀ n, IsOpen (V n) := fun n => isOpen_box3 v 0 (-(n : ℤ))
  have hVmem : ∀ (n : ℕ) (r : Fin 3 → v.adicCompletion ℚ),
      r ∈ V n ↔ ∀ i, Valued.v (r i) ≤ WithZero.exp (n : ℤ) := by
    intro n r
    simp only [hV, Set.mem_setOf_eq, Pi.zero_apply, sub_zero, neg_neg]
  have hcover : tsupport Φ ⊆ ⋃ n, V n := by
    intro r _
    choose n hn using fun i => exists_valued_le_exp v (r i)
    refine Set.mem_iUnion.mpr ⟨Finset.univ.sup n, (hVmem _ r).mpr fun i => (hn i).trans ?_⟩
    exact WithZero.exp_le_exp.mpr (Int.ofNat_le.mpr (Finset.le_sup (f := n) (Finset.mem_univ i)))
  obtain ⟨t, ht⟩ := hΦc.elim_finite_subcover V hVopen hcover
  refine ⟨t.sup id, fun r hr i => ?_⟩
  have hrt : r ∈ ⋃ n ∈ t, V n := ht (subset_tsupport Φ hr)
  obtain ⟨n, hn, hrn⟩ := Set.mem_iUnion₂.mp hrt
  refine ((hVmem n r).mp hrn i).trans (WithZero.exp_le_exp.mpr (Int.ofNat_le.mpr ?_))
  exact Finset.le_sup (f := id) hn

private theorem exists_level_forall_eq_of_isLocallyConstant {Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ}
    (hΦ : IsLocallyConstant Φ) (x : Fin 3 → v.adicCompletion ℚ) :
    ∃ m : ℕ, ∀ r' : Fin 3 → v.adicCompletion ℚ,
      (∀ i, Valued.v (r' i - x i) ≤ WithZero.exp (-(m : ℤ))) → Φ r' = Φ x := by
  have hO : {y : Fin 3 → v.adicCompletion ℚ | Φ y = Φ x} ∈ nhds x := (hΦ.isOpen_fiber (Φ x)).mem_nhds rfl
  rw [nhds_pi, Filter.mem_pi] at hO
  obtain ⟨I, -, s, hs, hIs⟩ := hO
  have hball : ∀ i, ∃ j : ℤ, ∀ y : v.adicCompletion ℚ, Valued.v (y - x i) ≤ WithZero.exp (-j) → y ∈ s i := by
    intro i
    obtain ⟨U, hUs, hUo, hxU⟩ := mem_nhds_iff.mp (hs i)
    obtain ⟨j, hj⟩ := exists_setOf_valued_sub_le_subset_of_isOpen v hUo hxU
    exact ⟨j, fun y hy => hUs (hj hy)⟩
  choose j hj using hball
  refine ⟨Finset.univ.sup fun i => (j i).toNat, fun r' hr' => ?_⟩
  refine hIs (Set.mem_pi.mpr fun i _ => hj i (r' i) ((hr' i).trans (WithZero.exp_le_exp.mpr ?_)))
  have h1 : j i ≤ ((j i).toNat : ℤ) := Int.self_le_toNat (j i)
  have h2 : ((j i).toNat : ℤ) ≤ ((Finset.univ.sup fun i => (j i).toNat : ℕ) : ℤ) :=
    Int.ofNat_le.mpr (Finset.le_sup (f := fun i => (j i).toNat) (Finset.mem_univ i))
  omega

private theorem exists_uniform_level_of_isLocallyConstant (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ e : ℕ, ∀ r r' : Fin 3 → v.adicCompletion ℚ,
      (∀ i, Valued.v (r' i - r i) ≤ WithZero.exp (-(e : ℤ))) → Φ r' = Φ r := by
  choose m hm using fun x : Fin 3 → v.adicCompletion ℚ => exists_level_forall_eq_of_isLocallyConstant hΦ x
  set U : (Fin 3 → v.adicCompletion ℚ) → Set (Fin 3 → v.adicCompletion ℚ) := fun x =>
    {r | ∀ i, Valued.v (r i - x i) ≤ WithZero.exp (-(m x : ℤ))} with hU
  have hUnhds : ∀ x ∈ tsupport Φ, U x ∈ nhds x := fun x _ =>
    (isOpen_box3 v x (m x)).mem_nhds fun i => by simp
  obtain ⟨t, -, ht⟩ := hΦc.elim_nhds_subcover U hUnhds
  refine ⟨t.sup m, ?_⟩

  have key : ∀ r ∈ tsupport Φ, ∀ r' : Fin 3 → v.adicCompletion ℚ,
      (∀ i, Valued.v (r' i - r i) ≤ WithZero.exp (-((t.sup m : ℕ) : ℤ))) → Φ r' = Φ r := by
    intro r hr r' hrr'
    obtain ⟨x, hxt, hrx⟩ := Set.mem_iUnion₂.mp (ht hr)
    have hle : WithZero.exp (-((t.sup m : ℕ) : ℤ)) ≤ WithZero.exp (-(m x : ℤ)) :=
      WithZero.exp_le_exp.mpr (neg_le_neg (Int.ofNat_le.mpr (Finset.le_sup (f := m) hxt)))
    have hr'x : ∀ i, Valued.v (r' i - x i) ≤ WithZero.exp (-(m x : ℤ)) := by
      intro i
      calc Valued.v (r' i - x i) = Valued.v ((r' i - r i) + (r i - x i)) := by rw [sub_add_sub_cancel]
        _ ≤ max (Valued.v (r' i - r i)) (Valued.v (r i - x i)) := Valuation.map_add _ _ _
        _ ≤ WithZero.exp (-(m x : ℤ)) := max_le ((hrr' i).trans hle) (hrx i)
    rw [hm x r' hr'x, hm x r hrx]
  intro r r' hrr'
  by_cases hr : r ∈ tsupport Φ
  · exact key r hr r' hrr'
  by_cases hr' : r' ∈ tsupport Φ
  · refine (key r' hr' r fun i => ?_).symm
    rw [← Valuation.map_neg, neg_sub]
    exact hrr' i
  rw [image_eq_zero_of_notMem_tsupport hr, image_eq_zero_of_notMem_tsupport hr']

end UniformConstants

end InvarianceUnit

namespace InvarianceUnit

open Matrix IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

section LevelAlgebra

private theorem valued_le_exp_of_le {x : v.adicCompletion ℚ} {m n : ℤ} (hx : Valued.v x ≤ WithZero.exp m) (h : m ≤ n) :
    Valued.v x ≤ WithZero.exp n :=
  hx.trans (by rw [WithZero.exp_le_exp]; exact h)

private theorem valued_mul_le_exp_add {x y : v.adicCompletion ℚ} {m n : ℤ} (hx : Valued.v x ≤ WithZero.exp m)
    (hy : Valued.v y ≤ WithZero.exp n) : Valued.v (x * y) ≤ WithZero.exp (m + n) := by
  rw [map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

private theorem valued_mul_le_exp_of_le_one_right {x y : v.adicCompletion ℚ} {m : ℤ} (hx : Valued.v x ≤ WithZero.exp m)
    (hy : Valued.v y ≤ 1) : Valued.v (x * y) ≤ WithZero.exp m := by
  rw [map_mul]
  simpa using mul_le_mul' hx hy

private theorem valued_mul_le_exp_of_le_one_left {x y : v.adicCompletion ℚ} {m : ℤ} (hx : Valued.v x ≤ 1)
    (hy : Valued.v y ≤ WithZero.exp m) : Valued.v (x * y) ≤ WithZero.exp m := by
  rw [map_mul]
  simpa using mul_le_mul' hx hy

private theorem valued_mul_le_one {x y : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1) :
    Valued.v (x * y) ≤ 1 := by
  rw [map_mul]
  simpa using mul_le_mul' hx hy

private theorem valued_one_add_eq_one_of_le_exp {w : v.adicCompletion ℚ} {m : ℤ} (hm : m ≤ -1)
    (hw : Valued.v w ≤ WithZero.exp m) : Valued.v (1 + w) = 1 := by
  refine Valuation.map_one_add_of_lt _ (lt_of_le_of_lt hw ?_)
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

private theorem valued_eq_one_of_sub_one_le {x : v.adicCompletion ℚ} {m : ℤ} (hm : m ≤ -1)
    (hx : Valued.v (x - 1) ≤ WithZero.exp m) : Valued.v x = 1 := by
  have h : x = 1 + (x - 1) := by ring
  rw [h]
  exact valued_one_add_eq_one_of_le_exp v hm hx

private theorem ne_zero_of_valued_eq_one' {x : v.adicCompletion ℚ} (hx : Valued.v x = 1) : x ≠ 0 :=
  (Valuation.ne_zero_iff _).mp (by rw [hx]; exact one_ne_zero)

private theorem valued_gl3Entry_diag_sub_one_le {N : ℕ} {k : LocalGL3 v} (hk : k ∈ principalCongruenceSet3 v N) (i : Fin 3) :
    Valued.v (gl3Entry v k i i - 1) ≤ WithZero.exp (-(N : ℤ)) := by
  have h := (mem_principalCongruenceSet3 v N k).mp hk i i
  rwa [gl3Entry_one, if_pos rfl] at h

private theorem valued_gl3Entry_le_of_ne {N : ℕ} {k : LocalGL3 v} (hk : k ∈ principalCongruenceSet3 v N) {i j : Fin 3}
    (hij : i ≠ j) : Valued.v (gl3Entry v k i j) ≤ WithZero.exp (-(N : ℤ)) := by
  have h := (mem_principalCongruenceSet3 v N k).mp hk i j
  rwa [gl3Entry_one, if_neg hij, sub_zero] at h

private theorem valued_gl3Entry_one_le_one (i j : Fin 3) : Valued.v (gl3Entry v (1 : LocalGL3 v) i j) ≤ 1 := by
  rw [gl3Entry_one]
  split_ifs <;> simp

private theorem valued_gl3Entry_le_one_of_mem {N : ℕ} {k : LocalGL3 v} (hk : k ∈ principalCongruenceSet3 v N) (i j : Fin 3) :
    Valued.v (gl3Entry v k i j) ≤ 1 := by
  have h := (mem_principalCongruenceSet3 v N k).mp hk i j
  have hN : WithZero.exp (-(N : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have e : gl3Entry v k i j = (gl3Entry v k i j - gl3Entry v 1 i j) + gl3Entry v 1 i j := by ring
  rw [e]
  exact Valuation.map_add_le _ (h.trans hN) (valued_gl3Entry_one_le_one v i j)

variable (k : LocalGL3 v) (r : Fin 3 → v.adicCompletion ℚ)

private def cornerFactor : v.adicCompletion ℚ :=
  gl3Entry v k 0 0 + r 0 * gl3Entry v k 1 0 + r 1 * gl3Entry v k 2 0

private def entryFactor₁ : v.adicCompletion ℚ :=
  gl3Entry v k 0 1 + r 0 * gl3Entry v k 1 1 + r 1 * gl3Entry v k 2 1

private def entryFactor₂ : v.adicCompletion ℚ :=
  gl3Entry v k 0 2 + r 0 * gl3Entry v k 1 2 + r 1 * gl3Entry v k 2 2

private def lowerFactor : v.adicCompletion ℚ :=
  (gl3Entry v k 0 0 * gl3Entry v k 1 1 - gl3Entry v k 0 1 * gl3Entry v k 1 0) +
    r 2 * (gl3Entry v k 0 0 * gl3Entry v k 2 1 - gl3Entry v k 0 1 * gl3Entry v k 2 0) +
      (r 0 * r 2 - r 1) * (gl3Entry v k 1 0 * gl3Entry v k 2 1 - gl3Entry v k 1 1 * gl3Entry v k 2 0)

private def outerFactor : v.adicCompletion ℚ :=
  (gl3Entry v k 0 0 * gl3Entry v k 1 2 - gl3Entry v k 0 2 * gl3Entry v k 1 0) +
    r 2 * (gl3Entry v k 0 0 * gl3Entry v k 2 2 - gl3Entry v k 0 2 * gl3Entry v k 2 0) +
      (r 0 * r 2 - r 1) * (gl3Entry v k 1 0 * gl3Entry v k 2 2 - gl3Entry v k 1 2 * gl3Entry v k 2 0)

variable {k r}

section Estimates

variable {N R : ℕ} (hk : k ∈ principalCongruenceSet3 v N) (hr : ∀ i, Valued.v (r i) ≤ WithZero.exp (R : ℤ))
include hk hr

private theorem valued_cornerFactor_sub_one_le : Valued.v (cornerFactor v k r - 1) ≤ WithZero.exp ((R : ℤ) - N) := by
  have e : cornerFactor v k r - 1 =
      (gl3Entry v k 0 0 - 1) + r 0 * gl3Entry v k 1 0 + r 1 * gl3Entry v k 2 0 := by
    unfold cornerFactor
    ring
  rw [e]
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
  · exact valued_le_exp_of_le v (valued_gl3Entry_diag_sub_one_le v hk 0) (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 0) (valued_gl3Entry_le_of_ne v hk (by decide))) (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 1) (valued_gl3Entry_le_of_ne v hk (by decide))) (by omega)

private theorem valued_entryFactor₁_sub_le : Valued.v (entryFactor₁ v k r - r 0) ≤ WithZero.exp ((R : ℤ) - N) := by
  have e : entryFactor₁ v k r - r 0 =
      gl3Entry v k 0 1 + r 0 * (gl3Entry v k 1 1 - 1) + r 1 * gl3Entry v k 2 1 := by
    unfold entryFactor₁
    ring
  rw [e]
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
  · exact valued_le_exp_of_le v (valued_gl3Entry_le_of_ne v hk (by decide)) (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 0) (valued_gl3Entry_diag_sub_one_le v hk 1)) (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 1) (valued_gl3Entry_le_of_ne v hk (by decide))) (by omega)

private theorem valued_entryFactor₂_sub_le : Valued.v (entryFactor₂ v k r - r 1) ≤ WithZero.exp ((R : ℤ) - N) := by
  have e : entryFactor₂ v k r - r 1 =
      gl3Entry v k 0 2 + r 0 * gl3Entry v k 1 2 + r 1 * (gl3Entry v k 2 2 - 1) := by
    unfold entryFactor₂
    ring
  rw [e]
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
  · exact valued_le_exp_of_le v (valued_gl3Entry_le_of_ne v hk (by decide)) (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 0) (valued_gl3Entry_le_of_ne v hk (by decide))) (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 1) (valued_gl3Entry_diag_sub_one_le v hk 2)) (by omega)

omit hk hr in

private theorem valued_minor_le_of_ne {a b c d : Fin 3} {a' b' c' d' : Fin 3}
    (h1 : Valued.v (gl3Entry v k a b * gl3Entry v k c d) ≤ WithZero.exp (-(N : ℤ)))
    (h2 : Valued.v (gl3Entry v k a' b' * gl3Entry v k c' d') ≤ WithZero.exp (-(N : ℤ))) :
    Valued.v (gl3Entry v k a b * gl3Entry v k c d - gl3Entry v k a' b' * gl3Entry v k c' d') ≤
      WithZero.exp (-(N : ℤ)) :=
  Valuation.map_sub_le _ h1 h2

omit hr in

private theorem valued_diag_minor_sub_one_le {i j : Fin 3} (hij : i ≠ j) :
    Valued.v (gl3Entry v k i i * gl3Entry v k j j - gl3Entry v k i j * gl3Entry v k j i - 1) ≤
      WithZero.exp (-(N : ℤ)) := by
  have e : gl3Entry v k i i * gl3Entry v k j j - gl3Entry v k i j * gl3Entry v k j i - 1 =
      (gl3Entry v k i i - 1) * gl3Entry v k j j + (gl3Entry v k j j - 1) - gl3Entry v k i j * gl3Entry v k j i := by
    ring
  rw [e]
  have h1 := valued_gl3Entry_le_one_of_mem v hk
  refine Valuation.map_sub_le _ (Valuation.map_add_le _ ?_ ?_) ?_
  · exact valued_mul_le_exp_of_le_one_right v (valued_gl3Entry_diag_sub_one_le v hk i) (h1 j j)
  · exact valued_gl3Entry_diag_sub_one_le v hk j
  · exact valued_mul_le_exp_of_le_one_right v (valued_gl3Entry_le_of_ne v hk hij) (h1 j i)

private theorem valued_ratio_coeff_le : Valued.v (r 0 * r 2 - r 1) ≤ WithZero.exp (2 * (R : ℤ)) := by
  have _hk := hk
  refine Valuation.map_sub_le _ ?_ ?_
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 0) (hr 2)) (by omega)
  · exact valued_le_exp_of_le v (hr 1) (by omega)

private theorem valued_lowerFactor_sub_one_le : Valued.v (lowerFactor v k r - 1) ≤ WithZero.exp (2 * (R : ℤ) - N) := by
  have e : lowerFactor v k r - 1 =
      (gl3Entry v k 0 0 * gl3Entry v k 1 1 - gl3Entry v k 0 1 * gl3Entry v k 1 0 - 1) +
        r 2 * (gl3Entry v k 0 0 * gl3Entry v k 2 1 - gl3Entry v k 0 1 * gl3Entry v k 2 0) +
          (r 0 * r 2 - r 1) * (gl3Entry v k 1 0 * gl3Entry v k 2 1 - gl3Entry v k 1 1 * gl3Entry v k 2 0) := by
    unfold lowerFactor
    ring
  rw [e]
  have h1 := valued_gl3Entry_le_one_of_mem v hk
  have ho : ∀ {a b : Fin 3}, a ≠ b → Valued.v (gl3Entry v k a b) ≤ WithZero.exp (-(N : ℤ)) :=
    fun h => valued_gl3Entry_le_of_ne v hk h
  have hm1 := valued_diag_minor_sub_one_le v hk (by decide : (0 : Fin 3) ≠ 1)
  have hm2 : Valued.v (gl3Entry v k 0 0 * gl3Entry v k 2 1 - gl3Entry v k 0 1 * gl3Entry v k 2 0) ≤
      WithZero.exp (-(N : ℤ)) :=
    valued_minor_le_of_ne v (valued_mul_le_exp_of_le_one_left v (h1 0 0) (ho (by decide)))
      (valued_mul_le_exp_of_le_one_right v (ho (by decide)) (h1 2 0))
  have hm3 : Valued.v (gl3Entry v k 1 0 * gl3Entry v k 2 1 - gl3Entry v k 1 1 * gl3Entry v k 2 0) ≤
      WithZero.exp (-(N : ℤ)) :=
    valued_minor_le_of_ne v (valued_mul_le_exp_of_le_one_right v (ho (by decide)) (h1 2 1))
      (valued_mul_le_exp_of_le_one_left v (h1 1 1) (ho (by decide)))
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
  · exact valued_le_exp_of_le v hm1 (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 2) hm2) (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (valued_ratio_coeff_le v hk hr) hm3) (by omega)

private theorem valued_outerFactor_sub_le : Valued.v (outerFactor v k r - r 2) ≤ WithZero.exp (2 * (R : ℤ) - N) := by
  have e : outerFactor v k r - r 2 =
      (gl3Entry v k 0 0 * gl3Entry v k 1 2 - gl3Entry v k 0 2 * gl3Entry v k 1 0) +
        r 2 * (gl3Entry v k 0 0 * gl3Entry v k 2 2 - gl3Entry v k 0 2 * gl3Entry v k 2 0 - 1) +
          (r 0 * r 2 - r 1) * (gl3Entry v k 1 0 * gl3Entry v k 2 2 - gl3Entry v k 1 2 * gl3Entry v k 2 0) := by
    unfold outerFactor
    ring
  rw [e]
  have h1 := valued_gl3Entry_le_one_of_mem v hk
  have ho : ∀ {a b : Fin 3}, a ≠ b → Valued.v (gl3Entry v k a b) ≤ WithZero.exp (-(N : ℤ)) :=
    fun h => valued_gl3Entry_le_of_ne v hk h
  have hm1 : Valued.v (gl3Entry v k 0 0 * gl3Entry v k 1 2 - gl3Entry v k 0 2 * gl3Entry v k 1 0) ≤
      WithZero.exp (-(N : ℤ)) :=
    valued_minor_le_of_ne v (valued_mul_le_exp_of_le_one_left v (h1 0 0) (ho (by decide)))
      (valued_mul_le_exp_of_le_one_right v (ho (by decide)) (h1 1 0))
  have hm2 := valued_diag_minor_sub_one_le v hk (by decide : (0 : Fin 3) ≠ 2)
  have hm3 : Valued.v (gl3Entry v k 1 0 * gl3Entry v k 2 2 - gl3Entry v k 1 2 * gl3Entry v k 2 0) ≤
      WithZero.exp (-(N : ℤ)) :=
    valued_minor_le_of_ne v (valued_mul_le_exp_of_le_one_right v (ho (by decide)) (h1 2 2))
      (valued_mul_le_exp_of_le_one_right v (ho (by decide)) (h1 2 0))
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
  · exact valued_le_exp_of_le v hm1 (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (hr 2) hm2) (by omega)
  · exact valued_le_exp_of_le v (valued_mul_le_exp_add v (valued_ratio_coeff_le v hk hr) hm3) (by omega)

variable (hN : 2 * R + 1 ≤ N)
include hN

private theorem valued_cornerFactor_eq_one : Valued.v (cornerFactor v k r) = 1 :=
  valued_eq_one_of_sub_one_le v (by omega) (valued_cornerFactor_sub_one_le v hk hr)

private theorem valued_lowerFactor_eq_one : Valued.v (lowerFactor v k r) = 1 :=
  valued_eq_one_of_sub_one_le v (by omega) (valued_lowerFactor_sub_one_le v hk hr)

private theorem cornerFactor_ne_zero : cornerFactor v k r ≠ 0 :=
  ne_zero_of_valued_eq_one' v (valued_cornerFactor_eq_one v hk hr hN)

private theorem lowerFactor_ne_zero : lowerFactor v k r ≠ 0 :=
  ne_zero_of_valued_eq_one' v (valued_lowerFactor_eq_one v hk hr hN)

private theorem valued_div_sub_le {a F ρ : v.adicCompletion ℚ} {t u : ℤ} (hF : Valued.v F = 1)
    (ha : Valued.v (a - ρ) ≤ WithZero.exp t) (hF1 : Valued.v (F - 1) ≤ WithZero.exp u)
    (hρ : Valued.v ρ ≤ WithZero.exp (R : ℤ)) (ht : t ≤ 3 * (R : ℤ) - N) (hu : (R : ℤ) + u ≤ 3 * (R : ℤ) - N) :
    Valued.v (a / F - ρ) ≤ WithZero.exp (3 * (R : ℤ) - N) := by
  have _hk := hk
  have _hr := hr
  have _hN := hN
  have hF0 : F ≠ 0 := ne_zero_of_valued_eq_one' v hF
  have e : a / F - ρ = ((a - ρ) - ρ * (F - 1)) / F := by
    rw [eq_div_iff hF0, sub_mul, div_mul_cancel₀ _ hF0]
    ring
  rw [e, map_div₀, hF, div_one]
  refine Valuation.map_sub_le _ (valued_le_exp_of_le v ha ht) ?_
  exact valued_le_exp_of_le v (valued_mul_le_exp_add v hρ hF1) hu

private theorem valued_entryFactor₁_div_cornerFactor_sub_le :
    Valued.v (entryFactor₁ v k r / cornerFactor v k r - r 0) ≤ WithZero.exp (3 * (R : ℤ) - N) :=
  valued_div_sub_le v hk hr hN (valued_cornerFactor_eq_one v hk hr hN) (valued_entryFactor₁_sub_le v hk hr)
    (valued_cornerFactor_sub_one_le v hk hr) (hr 0) (by omega) (by omega)

private theorem valued_entryFactor₂_div_cornerFactor_sub_le :
    Valued.v (entryFactor₂ v k r / cornerFactor v k r - r 1) ≤ WithZero.exp (3 * (R : ℤ) - N) :=
  valued_div_sub_le v hk hr hN (valued_cornerFactor_eq_one v hk hr hN) (valued_entryFactor₂_sub_le v hk hr)
    (valued_cornerFactor_sub_one_le v hk hr) (hr 1) (by omega) (by omega)

private theorem valued_outerFactor_div_lowerFactor_sub_le :
    Valued.v (outerFactor v k r / lowerFactor v k r - r 2) ≤ WithZero.exp (3 * (R : ℤ) - N) :=
  valued_div_sub_le v hk hr hN (valued_lowerFactor_eq_one v hk hr hN) (valued_outerFactor_sub_le v hk hr)
    (valued_lowerFactor_sub_one_le v hk hr) (hr 2) (by omega) (by omega)

end Estimates

private theorem valued_gl3Det_sub_one_le {N : ℕ} (hk : k ∈ principalCongruenceSet3 v N) :
    Valued.v (gl3Det v k - 1) ≤ WithZero.exp (-(N : ℤ)) := by
  have e' : ∀ i j, (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j = gl3Entry v k i j := fun _ _ => rfl
  have e : gl3Det v k - 1 =
      (gl3Entry v k 0 0 - 1) * gl3Entry v k 1 1 * gl3Entry v k 2 2 +
          (gl3Entry v k 1 1 - 1) * gl3Entry v k 2 2 + (gl3Entry v k 2 2 - 1) -
        gl3Entry v k 0 0 * gl3Entry v k 1 2 * gl3Entry v k 2 1 -
        gl3Entry v k 0 1 * gl3Entry v k 1 0 * gl3Entry v k 2 2 +
        gl3Entry v k 0 1 * gl3Entry v k 1 2 * gl3Entry v k 2 0 +
        gl3Entry v k 0 2 * gl3Entry v k 1 0 * gl3Entry v k 2 1 -
        gl3Entry v k 0 2 * gl3Entry v k 1 1 * gl3Entry v k 2 0 := by
    simp only [gl3Det, Matrix.det_fin_three, e']
    ring
  rw [e]
  have hd := valued_gl3Entry_diag_sub_one_le v hk
  have ho : ∀ {i j : Fin 3}, i ≠ j → Valued.v (gl3Entry v k i j) ≤ WithZero.exp (-(N : ℤ)) :=
    fun h => valued_gl3Entry_le_of_ne v hk h
  have h1 := valued_gl3Entry_le_one_of_mem v hk
  have hR := @valued_mul_le_exp_of_le_one_right v
  have hL := @valued_mul_le_exp_of_le_one_left v
  refine Valuation.map_sub_le _ ?_ ?_
  refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_sub_le _ (Valuation.map_sub_le _
    (Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_) ?_) ?_) ?_) ?_
  · exact hR (hR (hd 0) (h1 1 1)) (h1 2 2)
  · exact hR (hd 1) (h1 2 2)
  · exact hd 2
  · exact hR (hL (h1 0 0) (ho (by decide))) (h1 2 1)
  · exact hR (hR (ho (by decide)) (h1 1 0)) (h1 2 2)
  · exact hR (hR (ho (by decide)) (h1 1 2)) (h1 2 0)
  · exact hR (hR (ho (by decide)) (h1 1 0)) (h1 2 1)
  · exact hR (hR (ho (by decide)) (h1 1 1)) (h1 2 0)

private theorem valued_gl3Det_eq_one_of_mem {N : ℕ} (hN : 1 ≤ N) (hk : k ∈ principalCongruenceSet3 v N) :
    Valued.v (gl3Det v k) = 1 :=
  valued_eq_one_of_sub_one_le v (by omega) (valued_gl3Det_sub_one_le v hk)

private theorem valued_det_le_one (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (hM : ∀ i j, Valued.v (M i j) ≤ 1) :
    Valued.v M.det ≤ 1 := by
  rw [Matrix.det_fin_three]
  have h3 : ∀ a b c d e f : Fin 3, Valued.v (M a b * M c d * M e f) ≤ 1 := fun a b c d e f =>
    valued_mul_le_one v (valued_mul_le_one v (hM a b) (hM c d)) (hM e f)
  exact Valuation.map_sub_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_sub_le _
    (Valuation.map_sub_le _ (h3 0 0 1 1 2 2) (h3 0 0 1 2 2 1)) (h3 0 1 1 0 2 2)) (h3 0 1 1 2 2 0)) (h3 0 2 1 0 2 1))
    (h3 0 2 1 1 2 0)

private theorem valued_adjugate_le_one (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (hM : ∀ i j, Valued.v (M i j) ≤ 1)
    (i j : Fin 3) : Valued.v (M.adjugate i j) ≤ 1 := by
  rw [Matrix.adjugate_apply]
  refine valued_det_le_one v _ fun a b => ?_
  rw [Matrix.updateRow_apply]
  split_ifs with ha
  · rw [Pi.single_apply]
    split_ifs <;> simp
  · exact hM a b

private theorem gl3Entry_inv_eq (i j : Fin 3) :
    gl3Entry v k⁻¹ i j =
      (gl3Det v k)⁻¹ * (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).adjugate i j := by
  show ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j = _
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  rfl

private theorem valued_gl3Entry_inv_le_one {N : ℕ} (hN : 1 ≤ N) (hk : k ∈ principalCongruenceSet3 v N) (i j : Fin 3) :
    Valued.v (gl3Entry v k⁻¹ i j) ≤ 1 := by
  rw [gl3Entry_inv_eq v, map_mul, map_inv₀, valued_gl3Det_eq_one_of_mem v hN hk, inv_one, one_mul]
  exact valued_adjugate_le_one v _ (fun a b => valued_gl3Entry_le_one_of_mem v hk a b) i j

private theorem gl3Entry_inv_sub_one (i j : Fin 3) :
    gl3Entry v k⁻¹ i j - gl3Entry v 1 i j =
      gl3Entry v k⁻¹ i 0 * (gl3Entry v 1 0 j - gl3Entry v k 0 j) +
        gl3Entry v k⁻¹ i 1 * (gl3Entry v 1 1 j - gl3Entry v k 1 j) +
          gl3Entry v k⁻¹ i 2 * (gl3Entry v 1 2 j - gl3Entry v k 2 j) := by
  have hmat : (k⁻¹ : LocalGL3 v).val * ((1 : LocalGL3 v).val - k.val) =
      (k⁻¹ : LocalGL3 v).val - (1 : LocalGL3 v).val := by
    rw [Matrix.mul_sub, Units.val_one, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h := congrFun (congrFun hmat i) j
  rw [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three] at h
  simp only [Matrix.sub_apply] at h
  exact h.symm

private theorem inv_mem_principalCongruenceSet3 {N : ℕ} (hN : 1 ≤ N) (hk : k ∈ principalCongruenceSet3 v N) :
    k⁻¹ ∈ principalCongruenceSet3 v N := by
  refine (mem_principalCongruenceSet3 v N _).mpr fun i j => ?_
  rw [gl3Entry_inv_sub_one]
  have hk' := (mem_principalCongruenceSet3 v N k).mp hk
  have hterm : ∀ l : Fin 3,
      Valued.v (gl3Entry v k⁻¹ i l * (gl3Entry v 1 l j - gl3Entry v k l j)) ≤ WithZero.exp (-(N : ℤ)) := by
    intro l
    refine valued_mul_le_exp_of_le_one_left v (valued_gl3Entry_inv_le_one v hN hk i l) ?_
    rw [Valuation.map_sub_swap]
    exact hk' l j
  exact Valuation.map_add_le _ (Valuation.map_add_le _ (hterm 0) (hterm 1)) (hterm 2)

private theorem antidiagonal3_mul_mul_antidiagonal3_mem {N : ℕ} (hk : k ∈ principalCongruenceSet3 v N) :
    antidiagonal3 v * k * antidiagonal3 v ∈ principalCongruenceSet3 v N := by
  refine (mem_principalCongruenceSet3 v N _).mpr fun i j => ?_
  rw [gl3Entry_antidiagonal3_mul_mul_antidiagonal3]
  have h := (mem_principalCongruenceSet3 v N k).mp hk (Fin.rev i) (Fin.rev j)
  have e : gl3Entry v 1 (Fin.rev i) (Fin.rev j) = gl3Entry v 1 i j := by
    rw [gl3Entry_one, gl3Entry_one]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h' => hij (Fin.rev_inj.mp h')), if_neg hij]
  rw [e] at h
  exact h

end LevelAlgebra

end InvarianceUnit

namespace InvarianceUnit

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

section Smoothness

private theorem charExt_mul_eq_of_valued_sub_one_le (ξ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {c : ℕ}
    (hξ : HasConductorExponentAt ℚ v ξ c) {M u : v.adicCompletion ℚ} (hM : M ≠ 0)
    (hu : Valued.v (u - 1) ≤ WithZero.exp (-((c : ℤ) + 1))) : charExt ξ (M * u) = charExt ξ M := by
  have hu1 : Valued.v u = 1 := valued_eq_one_of_sub_one_le v (by omega) hu
  have hu0 : u ≠ 0 := ne_zero_of_valued_eq_one' v hu1
  rw [charExt_mul_of_ne_zero v ξ hM hu0]
  suffices h : charExt ξ u = 1 by rw [h, mul_one]
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    rw [charExt_of_ne_zero ξ hu0, (hasConductorExponentAt_zero_iff (K := ℚ) (v := v)).mp hξ (Units.mk0 u hu0) hu1,
      Units.val_one]
  · have hw : Valued.v (u - 1) ≤ WithZero.exp (-(c : ℤ)) := valued_le_exp_of_le v hu (by omega)
    have h := charExt_one_add_of_valued_le v ξ hξ (by omega) hw
    have e : (1 : v.adicCompletion ℚ) + (u - 1) = u := by ring
    rwa [e] at h

variable {v}

private theorem cornerEntry_mul_eq {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (k : LocalGL3 v) :
    cornerEntry v (g * k) = cornerEntry v g * cornerFactor v k (cellRatio v g) :=
  cornerEntry_mul_of_ne_zero v hc k

private theorem gl3Entry_two_one_mul_eq {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (k : LocalGL3 v) :
    gl3Entry v (g * k) 2 1 = cornerEntry v g * entryFactor₁ v k (cellRatio v g) :=
  gl3Entry_two_one_mul_of_ne_zero v hc k

private theorem gl3Entry_two_two_mul_eq {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (k : LocalGL3 v) :
    gl3Entry v (g * k) 2 2 = cornerEntry v g * entryFactor₂ v k (cellRatio v g) :=
  gl3Entry_two_two_mul_of_ne_zero v hc k

private theorem lowerMinor_mul_eq {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0) (k : LocalGL3 v) :
    lowerMinor v (g * k) = lowerMinor v g * lowerFactor v k (cellRatio v g) :=
  lowerMinor_mul_of_ne_zero v hc hl k

private theorem outerMinor_mul_eq {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0) (k : LocalGL3 v) :
    outerMinor v (g * k) = lowerMinor v g * outerFactor v k (cellRatio v g) :=
  outerMinor_mul_of_ne_zero v hc hl k

private theorem cellRatio_mul_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (k : LocalGL3 v) :
    cellRatio v (g * k) 0 = entryFactor₁ v k (cellRatio v g) / cornerFactor v k (cellRatio v g) := by
  rw [cellRatio_zero, gl3Entry_two_one_mul_eq hc k, cornerEntry_mul_eq hc k, mul_div_mul_left _ _ hc]

private theorem cellRatio_mul_one {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (k : LocalGL3 v) :
    cellRatio v (g * k) 1 = entryFactor₂ v k (cellRatio v g) / cornerFactor v k (cellRatio v g) := by
  rw [cellRatio_one, gl3Entry_two_two_mul_eq hc k, cornerEntry_mul_eq hc k, mul_div_mul_left _ _ hc]

private theorem cellRatio_mul_two {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0) (hl : lowerMinor v g ≠ 0) (k : LocalGL3 v) :
    cellRatio v (g * k) 2 = outerFactor v k (cellRatio v g) / lowerFactor v k (cellRatio v g) := by
  rw [cellRatio_two, outerMinor_mul_eq hc hl k, lowerMinor_mul_eq hc hl k, mul_div_mul_left _ _ hl]

variable (v)

private theorem cellSectionOf_mul_eq_of_mem (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (c : Fin 3 → ℕ)
    (hχ : ∀ i, HasConductorExponentAt ℚ v (χ i) (c i)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) {R e N : ℕ}
    (he : ∀ r r' : Fin 3 → v.adicCompletion ℚ,
      (∀ i, Valued.v (r' i - r i) ≤ WithZero.exp (-(e : ℤ))) → Φ r' = Φ r)
    (hN : 2 * R + 1 ≤ N) (hNe : 3 * R + e ≤ N) (hNc : ∀ i, 2 * R + (c i + 1) ≤ N) {k : LocalGL3 v}
    (hk : k ∈ principalCongruenceSet3 v N) {g : LocalGL3 v} (hg : g ∈ bigCell3 v)
    (hr : ∀ i, Valued.v (cellRatio v g i) ≤ WithZero.exp (R : ℤ)) :
    cellSectionOf v χ Φ (g * k) = cellSectionOf v χ Φ g := by
  obtain ⟨hc, hl⟩ := (mem_bigCell3_iff v g).mp hg
  have hF0 : Valued.v (cornerFactor v k (cellRatio v g)) = 1 := valued_cornerFactor_eq_one v hk hr hN
  have hF1 : Valued.v (lowerFactor v k (cellRatio v g)) = 1 := valued_lowerFactor_eq_one v hk hr hN
  have hF0' : cornerFactor v k (cellRatio v g) ≠ 0 := cornerFactor_ne_zero v hk hr hN
  have hF1' : lowerFactor v k (cellRatio v g) ≠ 0 := lowerFactor_ne_zero v hk hr hN
  have hD : Valued.v (gl3Det v k) = 1 := valued_gl3Det_eq_one_of_mem v (by omega) hk
  have hgk : g * k ∈ bigCell3 v := by
    refine (mem_bigCell3_iff v _).mpr ⟨?_, ?_⟩
    · rw [cornerEntry_mul_eq hc k]
      exact mul_ne_zero hc hF0'
    · rw [lowerMinor_mul_eq hc hl k]
      exact mul_ne_zero hl hF1'
  have hΦ : Φ (cellRatio v (g * k)) = Φ (cellRatio v g) := by
    refine he _ _ fun i => ?_
    have h3 : ∀ t : v.adicCompletion ℚ, Valued.v t ≤ WithZero.exp (3 * (R : ℤ) - N) →
        Valued.v t ≤ WithZero.exp (-(e : ℤ)) :=
      fun t ht => valued_le_exp_of_le v ht (by omega)
    fin_cases i
    · show Valued.v (cellRatio v (g * k) 0 - cellRatio v g 0) ≤ WithZero.exp (-(e : ℤ))
      rw [cellRatio_mul_zero hc k]
      exact h3 _ (valued_entryFactor₁_div_cornerFactor_sub_le v hk hr hN)
    · show Valued.v (cellRatio v (g * k) 1 - cellRatio v g 1) ≤ WithZero.exp (-(e : ℤ))
      rw [cellRatio_mul_one hc k]
      exact h3 _ (valued_entryFactor₂_div_cornerFactor_sub_le v hk hr hN)
    · show Valued.v (cellRatio v (g * k) 2 - cellRatio v g 2) ≤ WithZero.exp (-(e : ℤ))
      rw [cellRatio_mul_two hc hl k]
      exact h3 _ (valued_outerFactor_div_lowerFactor_sub_le v hk hr hN)
  have hval : cellValue v χ (g * k) = cellValue v χ g := by
    have hu₁ : Valued.v (gl3Det v k / lowerFactor v k (cellRatio v g) - 1) ≤ WithZero.exp (2 * (R : ℤ) - N) := by
      rw [div_sub_one hF1', map_div₀, hF1, div_one]
      have e : gl3Det v k - lowerFactor v k (cellRatio v g) =
          (gl3Det v k - 1) - (lowerFactor v k (cellRatio v g) - 1) := by ring
      rw [e]
      exact Valuation.map_sub_le _ (valued_le_exp_of_le v (valued_gl3Det_sub_one_le v hk) (by omega))
        (valued_lowerFactor_sub_one_le v hk hr)
    have hu₂ : Valued.v (lowerFactor v k (cellRatio v g) / cornerFactor v k (cellRatio v g) - 1) ≤
        WithZero.exp (2 * (R : ℤ) - N) := by
      rw [div_sub_one hF0', map_div₀, hF0, div_one]
      have e : lowerFactor v k (cellRatio v g) - cornerFactor v k (cellRatio v g) =
          (lowerFactor v k (cellRatio v g) - 1) - (cornerFactor v k (cellRatio v g) - 1) := by ring
      rw [e]
      exact Valuation.map_sub_le _ (valued_lowerFactor_sub_one_le v hk hr)
        (valued_le_exp_of_le v (valued_cornerFactor_sub_one_le v hk hr) (by omega))
    have hu₃ : Valued.v (cornerFactor v k (cellRatio v g) - 1) ≤ WithZero.exp (2 * (R : ℤ) - N) :=
      valued_le_exp_of_le v (valued_cornerFactor_sub_one_le v hk hr) (by omega)
    have hdeep : ∀ i : Fin 3, ∀ {u : v.adicCompletion ℚ}, Valued.v (u - 1) ≤ WithZero.exp (2 * (R : ℤ) - N) →
        Valued.v (u - 1) ≤ WithZero.exp (-((c i : ℤ) + 1)) := by
      intro i u hu
      have := hNc i
      exact valued_le_exp_of_le v hu (by omega)
    have hA : gl3Det v g / lowerMinor v g ≠ 0 := div_ne_zero (gl3Det_ne_zero v g) hl
    have hB : lowerMinor v g / cornerEntry v g ≠ 0 := div_ne_zero hl hc
    have hn₁ : ‖gl3Det v k / lowerFactor v k (cellRatio v g)‖ = 1 :=
      norm_eq_one_of_valued_eq_one v (by rw [map_div₀, hD, hF1, div_one])
    have hn₃ : ‖cornerFactor v k (cellRatio v g)‖ = 1 := norm_eq_one_of_valued_eq_one v hF0
    unfold cellValue
    rw [gl3Det_mul, lowerMinor_mul_eq hc hl k, cornerEntry_mul_eq hc k, mul_div_mul_comm (a := gl3Det v g),
      mul_div_mul_comm (a := lowerMinor v g), charExt_mul_eq_of_valued_sub_one_le v (χ 0) (hχ 0) hA (hdeep 0 hu₁),
      charExt_mul_eq_of_valued_sub_one_le v (χ 1) (hχ 1) hB (hdeep 1 hu₂),
      charExt_mul_eq_of_valued_sub_one_le v (χ 2) (hχ 2) hc (hdeep 2 hu₃), norm_mul, norm_mul, hn₁, hn₃, mul_one,
      mul_one]
  rw [cellSectionOf_apply_of_mem v χ Φ hgk, cellSectionOf_apply_of_mem v χ Φ hg, hval, hΦ]

private theorem exists_level_cellSectionOf_mul_eq (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (c : Fin 3 → ℕ)
    (hχ : ∀ i, HasConductorExponentAt ℚ v (χ i) (c i)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ N : ℕ, ∀ k ∈ principalCongruenceSet3 v N, ∀ g : LocalGL3 v,
      cellSectionOf v χ Φ (g * k) = cellSectionOf v χ Φ g := by
  obtain ⟨R, hR⟩ := exists_box_of_hasCompactSupport Φ hΦc
  obtain ⟨e, he⟩ := exists_uniform_level_of_isLocallyConstant Φ hΦ hΦc
  have hcD : ∀ i, c i ≤ c 0 + c 1 + c 2 := by
    intro i
    fin_cases i
    · show c 0 ≤ c 0 + c 1 + c 2
      omega
    · show c 1 ≤ c 0 + c 1 + c 2
      omega
    · show c 2 ≤ c 0 + c 1 + c 2
      omega
  have key : ∀ k' ∈ principalCongruenceSet3 v (3 * R + e + (c 0 + c 1 + c 2 + 1)), ∀ g' : LocalGL3 v,
      cellSectionOf v χ Φ g' ≠ 0 → cellSectionOf v χ Φ (g' * k') = cellSectionOf v χ Φ g' := by
    intro k' hk' g' hne
    have hg' : g' ∈ bigCell3 v := by
      by_contra h
      exact hne (cellSectionOf_apply_of_notMem v χ Φ h)
    have hΦne : Φ (cellRatio v g') ≠ 0 := by
      rw [cellSectionOf_apply_of_mem v χ Φ hg'] at hne
      exact right_ne_zero_of_mul hne
    exact cellSectionOf_mul_eq_of_mem v χ c hχ Φ he (by omega) (by omega)
      (fun i => by have := hcD i; omega) hk' hg' (hR _ hΦne)
  refine ⟨3 * R + e + (c 0 + c 1 + c 2 + 1), fun k hk g => ?_⟩
  by_cases h0 : cellSectionOf v χ Φ g = 0
  · by_contra hne
    have h1 : cellSectionOf v χ Φ (g * k) ≠ 0 := fun h => hne (by rw [h, h0])
    have h2 := key k⁻¹ (inv_mem_principalCongruenceSet3 v (by omega) hk) (g * k) h1
    rw [mul_inv_cancel_right g k] at h2
    exact h1 (h2.symm.trans h0)
  · exact key k hk g h0

private theorem exists_level_jacquetWhittaker3_mul_antidiagonal3_mul_eq (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (c : Fin 3 → ℕ) (hχ : ∀ i, HasConductorExponentAt ℚ v (χ i) (c i)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ N : ℕ, ∀ k ∈ principalCongruenceSet3 v N, ∀ g : LocalGL3 v,
      jacquetWhittaker3 v χ Φ (g * k * antidiagonal3 v) = jacquetWhittaker3 v χ Φ (g * antidiagonal3 v) := by
  obtain ⟨N, hN⟩ := exists_level_cellSectionOf_mul_eq v χ c hχ Φ hΦ hΦc
  refine ⟨N, fun k hk g => ?_⟩
  rw [jacquetWhittaker3_apply, jacquetWhittaker3_apply]
  have hfun : gl3AmbientRightTranslate (R := ℂ) (g * k * antidiagonal3 v) (cellSectionOf v χ Φ) =
      gl3AmbientRightTranslate (R := ℂ) (g * antidiagonal3 v) (cellSectionOf v χ Φ) := by
    funext y
    rw [gl3AmbientRightTranslate_apply, gl3AmbientRightTranslate_apply]
    have hw := antidiagonal3_mul_antidiagonal3 v
    have hy : y * (g * k * antidiagonal3 v) =
        y * (g * antidiagonal3 v) * (antidiagonal3 v * k * antidiagonal3 v) := by
      calc y * (g * k * antidiagonal3 v)
          = y * (g * ((antidiagonal3 v * antidiagonal3 v) * k) * antidiagonal3 v) := by rw [hw, one_mul]
        _ = y * (g * antidiagonal3 v) * (antidiagonal3 v * k * antidiagonal3 v) := by simp only [mul_assoc]
    rw [hy, hN _ (antidiagonal3_mul_mul_antidiagonal3_mem v hk) _]
  rw [hfun]

private theorem exists_isOpen_subgroup_jacquetWhittaker3_mul_antidiagonal3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (c : Fin 3 → ℕ) (hχ : ∀ i, HasConductorExponentAt ℚ v (χ i) (c i)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v,
      jacquetWhittaker3 v χ Φ (g * k * antidiagonal3 v) = jacquetWhittaker3 v χ Φ (g * antidiagonal3 v) := by
  obtain ⟨N, hN⟩ := exists_level_jacquetWhittaker3_mul_antidiagonal3_mul_eq v χ c hχ Φ hΦ hΦc
  exact exists_isOpen_subgroup_of_principalCongruenceSet3 v
    (fun h => jacquetWhittaker3 v χ Φ (h * antidiagonal3 v)) N hN

end Smoothness

end InvarianceUnit

namespace InvarianceUnit

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem exists_isOpen_subgroup_jacquetWhittaker3_of_isLocallyConstant (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, IsLocallyConstant (χ i)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v,
      jacquetWhittaker3 v χ Φ (g * k * antidiagonal3 v) = jacquetWhittaker3 v χ Φ (g * antidiagonal3 v) := by
  choose c hc using fun i => exists_hasConductorExponentAt_of_continuous ℚ v (χ i) (hχ i).continuous
  exact exists_isOpen_subgroup_jacquetWhittaker3_mul_antidiagonal3 v χ c hc Φ hΦ hΦc

end InvarianceUnit

namespace GaugeFlipUnit

open Matrix IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

section GaugeFlip

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem coe_mul_antidiagonal3_apply_zero (k : LocalGL3 v) (i : Fin 3) :
    ((k * antidiagonal3 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 0 =
      (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 2 := by
  simp [Units.val_mul, antidiagonal3_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem coe_mul_antidiagonal3_apply_one (k : LocalGL3 v) (i : Fin 3) :
    ((k * antidiagonal3 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 1 =
      (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 1 := by
  simp [Units.val_mul, antidiagonal3_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem coe_mul_antidiagonal3_apply_two (k : LocalGL3 v) (i : Fin 3) :
    ((k * antidiagonal3 v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 2 =
      (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i 0 := by
  simp [Units.val_mul, antidiagonal3_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem lastRowSup_mul_antidiagonal3 (k : LocalGL3 v) : lastRowSup (k * antidiagonal3 v) = lastRowSup k := by
  simp only [lastRowSup, coe_mul_antidiagonal3_apply_zero, coe_mul_antidiagonal3_apply_one,
    coe_mul_antidiagonal3_apply_two]
  ac_rfl

private theorem bottomMinor_mul_antidiagonal3_zero_one (k : LocalGL3 v) :
    bottomMinor (k * antidiagonal3 v) 0 1 = -bottomMinor k 1 2 := by
  simp only [bottomMinor, coe_mul_antidiagonal3_apply_zero, coe_mul_antidiagonal3_apply_one]
  ring

private theorem bottomMinor_mul_antidiagonal3_zero_two (k : LocalGL3 v) :
    bottomMinor (k * antidiagonal3 v) 0 2 = -bottomMinor k 0 2 := by
  simp only [bottomMinor, coe_mul_antidiagonal3_apply_zero, coe_mul_antidiagonal3_apply_two]
  ring

private theorem bottomMinor_mul_antidiagonal3_one_two (k : LocalGL3 v) :
    bottomMinor (k * antidiagonal3 v) 1 2 = -bottomMinor k 0 1 := by
  simp only [bottomMinor, coe_mul_antidiagonal3_apply_one, coe_mul_antidiagonal3_apply_two]
  ring

private theorem minorSup_mul_antidiagonal3 (k : LocalGL3 v) : minorSup (k * antidiagonal3 v) = minorSup k := by
  simp only [minorSup, bottomMinor_mul_antidiagonal3_zero_one, bottomMinor_mul_antidiagonal3_zero_two,
    bottomMinor_mul_antidiagonal3_one_two, norm_neg]
  ac_rfl

private theorem detSize_mul_antidiagonal3 (k : LocalGL3 v) : detSize (k * antidiagonal3 v) = detSize k := by
  rw [detSize, detSize, Units.val_mul, Matrix.det_mul, norm_mul, antidiagonal3_coe]
  simp [Matrix.det_fin_three]

end GaugeFlip

end GaugeFlipUnit

section RootSizeTransport

open Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal NumberField.StandardAddChar LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem lastRowSup_nonneg (g : LocalGL3 v) : 0 ≤ lastRowSup g :=
  le_max_of_le_right (norm_nonneg _)

private theorem minorSup_nonneg (g : LocalGL3 v) : 0 ≤ minorSup g :=
  le_max_of_le_right (norm_nonneg _)

private theorem detSize_nonneg (g : LocalGL3 v) : 0 ≤ detSize g :=
  norm_nonneg _

private theorem rootProduct_nonneg (g : LocalGL3 v) :
    0 ≤ (detSize g * lastRowSup g / minorSup g ^ 2) * (minorSup g / lastRowSup g ^ 2) :=
  mul_nonneg
    (div_nonneg (mul_nonneg (detSize_nonneg v g) (lastRowSup_nonneg v g)) (pow_nonneg (minorSup_nonneg v g) 2))
    (div_nonneg (minorSup_nonneg v g) (pow_nonneg (lastRowSup_nonneg v g) 2))

private theorem rootSizes_mul_antidiagonal3_inv (g : LocalGL3 v) :
    detSize (g * (antidiagonal3 v)⁻¹) = detSize g ∧ lastRowSup (g * (antidiagonal3 v)⁻¹) = lastRowSup g ∧
      minorSup (g * (antidiagonal3 v)⁻¹) = minorSup g := by
  have h₁ := GaugeFlipUnit.detSize_mul_antidiagonal3 v (g * (antidiagonal3 v)⁻¹)
  have h₂ := GaugeFlipUnit.lastRowSup_mul_antidiagonal3 v (g * (antidiagonal3 v)⁻¹)
  have h₃ := GaugeFlipUnit.minorSup_mul_antidiagonal3 v (g * (antidiagonal3 v)⁻¹)
  rw [inv_mul_cancel_right] at h₁ h₂ h₃
  exact ⟨h₁.symm, h₂.symm, h₃.symm⟩

private theorem exists_rootSize_bound (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i))
    (hωu : ∀ u : (v.adicCompletion ℚ)ˣ, ‖(((χ 0 * χ 1 * χ 2) u : ℂˣ) : ℂ)‖ = 1)
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ g : LocalGL3 v,
      (¬ (detSize g * lastRowSup g / minorSup g ^ 2 ≤ B ∧ minorSup g / lastRowSup g ^ 2 ≤ B) →
        jacquetWhittaker3 v χ Φ g = 0) ∧
      (detSize g * lastRowSup g / minorSup g ^ 2 ≤ B ∧ minorSup g / lastRowSup g ^ 2 ≤ B →
        ‖jacquetWhittaker3 v χ Φ g‖ ≤
          C / ((detSize g * lastRowSup g / minorSup g ^ 2) * (minorSup g / lastRowSup g ^ 2)) ^ t) := by
  have hφ : StableJacquetFunctional.HasStableTranslates v (cellSectionOf v χ Φ) :=
    fun g => exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v χ hχ Φ ⟨hΦ, hΦc⟩ g
  have hstab : ∀ g : LocalGL3 v,
      PsiLawUnit.Stabilises v (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v χ Φ)) := fun g =>
    (PsiLawUnit.jacquetIntegrable_and_stabilises_of_exists_forall_le v _
      (exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v χ hχ Φ ⟨hΦ, hΦc⟩ g)).2
  have hφPS : cellSectionOf v χ Φ ∈ principalSeries3 v χ :=
    MembershipUnit.cellSectionOf_mem_principalSeries3 v hχ hΦ hΦc
  obtain ⟨W', hW'⟩ : ∃ W' : LocalGL3 v → ℂ, W' = fun h : LocalGL3 v => jacquetWhittaker3 v χ Φ (h * antidiagonal3 v) :=
    ⟨_, rfl⟩
  have hW'eq : W' = StableJacquetFunctional.whittakerOf v
      (gl3AmbientRightTranslate (R := ℂ) (antidiagonal3 v) (cellSectionOf v χ Φ)) := by
    rw [StableJacquetFunctional.whittakerOf_rightTranslate, ← StableJacquetFunctional.jacquetWhittaker3_eq_whittakerOf,
      hW']
    rfl
  have hψv : psiLoc (stdAddChar ℚ) v ≠ 1 := by
    rw [psiLoc_stdAddChar]
    exact psiLocal_ne_one ℚ v
  have hWpsi : IsGL3PsiWhittakerFn (psiLoc (stdAddChar ℚ) v) W' := by
    rw [psiLoc_stdAddChar, hW']
    exact PsiLawUnit.isGL3PsiWhittakerFn_jacquetWhittaker3_mul_antidiagonal3 v χ Φ hstab
  have hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W' (g * k) = W' g := by
    obtain ⟨Uv, hUo, hUk⟩ :=
      InvarianceUnit.exists_isOpen_subgroup_jacquetWhittaker3_of_isLocallyConstant v χ hχ Φ hΦ hΦc
    exact ⟨Uv, hUo, fun k hk g => by rw [hW']; exact hUk k hk g⟩
  have hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W',
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)) := by
    intro Uv hU
    rw [hW'eq]
    exact StableJacquetFunctional.exists_finset_forall_mem_cyclic_imp_mem_span v χ
      (rightTranslate_mem_principalSeries3 hφPS _)
      (StableJacquetFunctional.isStableAll_rightTranslate v hφ _) Uv hU
  have hcen : ∀ (z : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v),
      W' (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = (((χ 0 * χ 1 * χ 2) z : ℂˣ) : ℂ) * W' g := by
    intro z g
    rw [hW']
    show jacquetWhittaker3 v χ Φ (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g * antidiagonal3 v) =
      (((χ 0 * χ 1 * χ 2) z : ℂˣ) : ℂ) * jacquetWhittaker3 v χ Φ (g * antidiagonal3 v)
    rw [mul_assoc]
    exact JacquetCentralCharacter.jacquetWhittaker3_scalar_mul v χ Φ z (g * antidiagonal3 v)
  obtain ⟨B, t, C, hB⟩ := exists_rootSize_bound_of_isGL3PsiWhittakerFn (stdAddChar ℚ) v hψv W' hWpsi hsm hadm
    (χ 0 * χ 1 * χ 2) hωu hcen
  refine ⟨B, t, C, fun g => ?_⟩
  obtain ⟨hd, hl, hm⟩ := rootSizes_mul_antidiagonal3_inv v g
  have hWg : jacquetWhittaker3 v χ Φ g = W' (g * (antidiagonal3 v)⁻¹) := by
    rw [hW']
    show jacquetWhittaker3 v χ Φ g = jacquetWhittaker3 v χ Φ (g * (antidiagonal3 v)⁻¹ * antidiagonal3 v)
    rw [inv_mul_cancel_right]
  have h := hB (g * (antidiagonal3 v)⁻¹)
  rw [hd, hl, hm] at h
  rw [hWg]
  exact h

end RootSizeTransport

end WhittakerRootSizeVanishing

open LanglandsTunnell.CubicInduction WhittakerRootSizeVanishing in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i))
    (hωu : ∀ u : (v.adicCompletion ℚ)ˣ, ‖(((χ 0 * χ 1 * χ 2) u : ℂˣ) : ℂ)‖ = 1)
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ B : ℝ, ∀ g : LocalGL3 v,
      ¬ (detSize g * lastRowSup g / minorSup g ^ 2 ≤ B ∧ minorSup g / lastRowSup g ^ 2 ≤ B) →
        jacquetWhittaker3 v χ Φ g = 0 := by
  obtain ⟨B, t, C, hB⟩ := exists_rootSize_bound v χ hχ hωu Φ hΦ hΦc
  exact ⟨B, fun g hg => (hB g).1 hg⟩

end

end S_LanglandsTunnell_CubicInduction_exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt (solution)
