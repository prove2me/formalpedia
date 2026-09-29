-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.middleDatum_compare_of_primalMiddleDatum_of_dualMiddleDatum_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/8125c09c-6358-58e9-bdbb-bd2da93c994a

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Mathlib
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_tsum_torus_apply_mul_eval_eq_of_mem_gl3CyclicSubspace
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_middleDatum_compare_of_primalMiddleDatum_of_dualMiddleDatum_of_ne_zero
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

open LanglandsTunnell.CubicInduction

noncomputable section

namespace Ws1
namespace Middle
namespace Laurent1

open Finset Polynomial

def LRep1 (q : ℕ) (f : ℂ → ℂ) : Prop :=
  ∃ (P : Polynomial ℂ) (M : ℕ), ∀ s : ℂ, f s * ((q : ℂ) ^ (-s)) ^ M = P.eval ((q : ℂ) ^ (-s))

section Atoms

variable {q : ℕ} (hq : 1 < q)
include hq

theorem qC_ne_zero : (q : ℂ) ≠ 0 := by exact_mod_cast (lt_trans zero_lt_one hq).ne'

theorem x_ne_zero (s : ℂ) : (q : ℂ) ^ (-s) ≠ 0 := by
  intro h; exact qC_ne_zero hq ((Complex.cpow_eq_zero_iff _ _).mp h).1

theorem cpow_ne_zero' (w : ℂ) : (q : ℂ) ^ w ≠ 0 := by
  intro h; exact qC_ne_zero hq ((Complex.cpow_eq_zero_iff _ _).mp h).1

theorem qs_eq_inv (s : ℂ) : (q : ℂ) ^ s = ((q : ℂ) ^ (-s))⁻¹ := by
  rw [Complex.cpow_neg, inv_inv]

theorem qs_mul_x (s : ℂ) : (q : ℂ) ^ s * (q : ℂ) ^ (-s) = 1 := by
  rw [qs_eq_inv hq, inv_mul_cancel₀ (x_ne_zero hq s)]

theorem q_one_sub (s : ℂ) : (q : ℂ) ^ (1 - s) = (q : ℂ) * (q : ℂ) ^ (-s) := by
  rw [sub_eq_add_neg, Complex.cpow_add _ _ (qC_ne_zero hq), Complex.cpow_one]

theorem q_neg_add (a s : ℂ) : (q : ℂ) ^ (-(s + a)) = (q : ℂ) ^ (-a) * (q : ℂ) ^ (-s) := by
  rw [show -(s + a) = -a + -s by ring, Complex.cpow_add _ _ (qC_ne_zero hq)]

theorem q_neg_sub (a s : ℂ) : (q : ℂ) ^ (-(a - s)) = (q : ℂ) ^ (-a) * ((q : ℂ) ^ (-s))⁻¹ := by
  rw [show -(a - s) = -a + s by ring, Complex.cpow_add _ _ (qC_ne_zero hq)]
  congr 1
  exact qs_eq_inv hq s

theorem q_natMul_sub (n : ℕ) (a s : ℂ) :
    (q : ℂ) ^ ((n : ℂ) * (a - s)) = ((q : ℂ) ^ a) ^ n * ((q : ℂ) ^ (-s)) ^ n := by
  rw [Complex.cpow_nat_mul, sub_eq_add_neg, Complex.cpow_add _ _ (qC_ne_zero hq), mul_pow]

theorem qs_pow (j : ℕ) (s : ℂ) : ((q : ℂ) ^ s) ^ j = (q : ℂ) ^ ((j : ℂ) * s) := by
  rw [Complex.cpow_nat_mul]

end Atoms

section Closure

variable {q : ℕ} (hq : 1 < q)
include hq

private theorem _root_.Ws1.Middle.Laurent1.congr {f g : ℂ → ℂ} (hfg : ∀ s, f s = g s) (hf : LRep1 q f) : LRep1 q g := by
  obtain ⟨P, M, h⟩ := hf
  exact ⟨P, M, fun s => by rw [← hfg]; exact h s⟩

p2m_export "Ws1.Middle.Laurent1" "congr"
theorem const (c : ℂ) : LRep1 q (fun _ => c) :=
  ⟨Polynomial.C c, 0, fun s => by simp⟩

theorem x : LRep1 q (fun s => (q : ℂ) ^ (-s)) :=
  ⟨Polynomial.X, 0, fun s => by simp⟩

theorem xinv : LRep1 q (fun s => (q : ℂ) ^ s) :=
  ⟨1, 1, fun s => by rw [pow_one, qs_mul_x hq, Polynomial.eval_one]⟩

theorem xinv' : LRep1 q (fun s => ((q : ℂ) ^ (-s))⁻¹) :=
  congr hq (fun s => qs_eq_inv hq s) (xinv hq)

theorem add {f g : ℂ → ℂ} (hf : LRep1 q f) (hg : LRep1 q g) : LRep1 q (fun s => f s + g s) := by
  obtain ⟨P, M, hP⟩ := hf
  obtain ⟨Q, N, hQ⟩ := hg
  refine ⟨P * Polynomial.X ^ N + Q * Polynomial.X ^ M, M + N, fun s => ?_⟩
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow,
    Polynomial.eval_X, ← hP s, ← hQ s]
  ring

private theorem _root_.Ws1.Middle.Laurent1.mul {f g : ℂ → ℂ} (hf : LRep1 q f) (hg : LRep1 q g) : LRep1 q (fun s => f s * g s) := by
  obtain ⟨P, M, hP⟩ := hf
  obtain ⟨Q, N, hQ⟩ := hg
  refine ⟨P * Q, M + N, fun s => ?_⟩
  rw [Polynomial.eval_mul, ← hP s, ← hQ s]
  ring

p2m_export "Ws1.Middle.Laurent1" "mul"
theorem neg {f : ℂ → ℂ} (hf : LRep1 q f) : LRep1 q (fun s => -f s) := by
  obtain ⟨P, M, hP⟩ := hf
  exact ⟨-P, M, fun s => by rw [Polynomial.eval_neg, ← hP s]; ring⟩

theorem sub {f g : ℂ → ℂ} (hf : LRep1 q f) (hg : LRep1 q g) : LRep1 q (fun s => f s - g s) :=
  congr hq (fun s => by ring) (add hq hf (neg hq hg))

theorem smul (c : ℂ) {f : ℂ → ℂ} (hf : LRep1 q f) : LRep1 q (fun s => c * f s) :=
  mul hq (const hq c) hf

theorem pow {f : ℂ → ℂ} (hf : LRep1 q f) (n : ℕ) : LRep1 q (fun s => f s ^ n) := by
  induction n with
  | zero => exact congr hq (fun s => by rw [pow_zero]) (const hq 1)
  | succ n ih => exact congr hq (fun s => by rw [pow_succ]) (mul hq ih hf)

theorem sum {ι : Type*} (T : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ T, LRep1 q (f i)) :
    LRep1 q (fun s => ∑ i ∈ T, f i s) := by
  classical
  induction T using Finset.induction_on with
  | empty => exact congr hq (fun s => by rw [Finset.sum_empty]) (const hq 0)
  | insert a T ha ih =>
    refine congr hq (fun s => by rw [Finset.sum_insert ha]) (add hq (hf a (Finset.mem_insert_self a T)) ?_)
    exact ih fun i hi => hf i (Finset.mem_insert_of_mem hi)

theorem prod {ι : Type*} (T : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ T, LRep1 q (f i)) :
    LRep1 q (fun s => ∏ i ∈ T, f i s) := by
  classical
  induction T using Finset.induction_on with
  | empty => exact congr hq (fun s => by rw [Finset.prod_empty]) (const hq 1)
  | insert a T ha ih =>
    refine congr hq (fun s => by rw [Finset.prod_insert ha]) (mul hq (hf a (Finset.mem_insert_self a T)) ?_)
    exact ih fun i hi => hf i (Finset.mem_insert_of_mem hi)

theorem polyEval (D : Polynomial ℂ) {g : ℂ → ℂ} (hg : LRep1 q g) : LRep1 q (fun s => D.eval (g s)) := by
  refine congr hq (fun s => (Polynomial.eval_eq_sum_range (g s)).symm) ?_
  exact sum hq _ fun i _ => smul hq _ (pow hq hg i)

theorem mvEval₂ (P : MvPolynomial (Fin 2) ℂ) {g₁ g₂ : ℂ → ℂ} (hg₁ : LRep1 q g₁) (hg₂ : LRep1 q g₂) :
    LRep1 q (fun s => MvPolynomial.eval ![g₁ s, g₂ s] P) := by
  induction P using MvPolynomial.induction_on with
  | C a => exact congr hq (fun s => (MvPolynomial.eval_C a).symm) (const hq a)
  | add p r hp hr => exact congr hq (fun s => (map_add _ p r).symm) (add hq hp hr)
  | mul_X p i hp =>
    refine congr hq (fun s => (by rw [map_mul, MvPolynomial.eval_X])) (mul hq hp ?_)
    fin_cases i
    · exact congr hq (fun s => by simp) hg₁
    · exact congr hq (fun s => by simp) hg₂

theorem cx_zpow (c : ℂ) (hc : c ≠ 0) (N : ℤ) : LRep1 q (fun s => (c * (q : ℂ) ^ (-s)) ^ N) := by
  rcases Int.eq_nat_or_neg N with ⟨n, rfl | rfl⟩
  · exact congr hq (fun s => by rw [zpow_natCast]) (pow hq (smul hq c (x hq)) n)
  · refine ⟨Polynomial.C (c⁻¹ ^ n), n, fun s => ?_⟩
    show (c * (q : ℂ) ^ (-s)) ^ (-(n : ℤ)) * ((q : ℂ) ^ (-s)) ^ n = Polynomial.eval ((q : ℂ) ^ (-s)) (Polynomial.C (c⁻¹ ^ n))
    rw [zpow_neg, zpow_natCast, Polynomial.eval_C, mul_pow, mul_inv, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ (x_ne_zero hq s)), mul_one, inv_pow]

theorem cxinv_zpow (c : ℂ) (hc : c ≠ 0) (N : ℤ) : LRep1 q (fun s => (c * ((q : ℂ) ^ (-s))⁻¹) ^ N) := by
  rcases Int.eq_nat_or_neg N with ⟨n, rfl | rfl⟩
  · exact congr hq (fun s => by rw [zpow_natCast]) (pow hq (smul hq c (xinv' hq)) n)
  · refine congr hq (fun s => ?_) (pow hq (smul hq c⁻¹ (x hq)) n)
    rw [zpow_neg, zpow_natCast, ← inv_pow, mul_inv, inv_inv]

theorem q_one_sub' : LRep1 q (fun s => (q : ℂ) ^ (1 - s)) :=
  congr hq (fun s => (q_one_sub hq s).symm) (smul hq _ (x hq))

theorem q_neg_add' (a : ℂ) : LRep1 q (fun s => (q : ℂ) ^ (-(s + a))) :=
  congr hq (fun s => (q_neg_add hq a s).symm) (smul hq _ (x hq))

theorem q_neg_sub' (a : ℂ) : LRep1 q (fun s => (q : ℂ) ^ (-(a - s))) :=
  congr hq (fun s => (q_neg_sub hq a s).symm) (smul hq _ (xinv' hq))

theorem q_natMul_sub' (n : ℕ) (a : ℂ) : LRep1 q (fun s => (q : ℂ) ^ ((n : ℂ) * (a - s))) :=
  congr hq (fun s => (q_natMul_sub hq n a s).symm) (smul hq _ (pow hq (x hq) n))

end Closure

section Extract

variable {q : ℕ} (hq : 1 < q)
include hq

theorem exists_poly {f : ℂ → ℂ} (hf : LRep1 q f) :
    ∃ (m : Polynomial ℂ) (M : ℕ), ∀ s : ℂ, m.eval ((q : ℂ) ^ (-s)) = ((q : ℂ) ^ (-s)) ^ M * f s := by
  obtain ⟨P, M, h⟩ := hf
  exact ⟨P, M, fun s => by rw [← h s, mul_comm]⟩

theorem exists_poly_zpow {f : ℂ → ℂ} (hf : LRep1 q f) (M : ℕ) :
    ∃ (m : Polynomial ℂ) (k : ℤ), ∀ s : ℂ,
      m.eval ((q : ℂ) ^ (-s)) * (q : ℂ) ^ ((k : ℂ) * s) = ((q : ℂ) ^ (-s)) ^ M * f s := by
  obtain ⟨P, Mf, h⟩ := hf
  rcases Nat.lt_or_ge M Mf with hlt | hle
  swap
  · refine ⟨P * Polynomial.X ^ (M - Mf), 0, fun s => ?_⟩
    rw [Int.cast_zero, zero_mul, Complex.cpow_zero, mul_one, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, ← h s, mul_assoc, ← pow_add, Nat.add_sub_cancel' hle, mul_comm]
  · refine ⟨P, ((Mf - M : ℕ) : ℤ), fun s => ?_⟩
    rw [Int.cast_natCast, ← qs_pow hq, ← h s]
    have hx := x_ne_zero hq s
    have : ((q : ℂ) ^ (-s)) ^ Mf = ((q : ℂ) ^ (-s)) ^ M * ((q : ℂ) ^ (-s)) ^ (Mf - M) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [this, qs_eq_inv hq s, inv_pow, mul_assoc, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx), mul_one, mul_comm]

theorem poly_ne_zero {f : ℂ → ℂ} {m : Polynomial ℂ} {M : ℕ}
    (h : ∀ s : ℂ, m.eval ((q : ℂ) ^ (-s)) = ((q : ℂ) ^ (-s)) ^ M * f s) {s₀ : ℂ} (hs₀ : f s₀ ≠ 0) : m ≠ 0 := by
  intro hm
  have := h s₀
  rw [hm, Polynomial.eval_zero] at this
  exact (mul_ne_zero (pow_ne_zero _ (x_ne_zero hq s₀)) hs₀) this.symm

end Extract

section Roots

theorem exists_forall_eval_ne_zero_of_norm_lt (Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ < δ → Q.eval z ≠ 0 := by
  classical
  set S : Finset ℂ := Q.roots.toFinset.filter (fun r => r ≠ 0) with hS
  by_cases hne : S.Nonempty
  · refine ⟨S.inf' hne (fun r => ‖r‖), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro r hr
      exact norm_pos_iff.mpr (Finset.mem_filter.mp hr).2
    · intro z hz0 hz hQz
      have hzS : z ∈ S := Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ).mpr hQz), hz0⟩
      exact (not_lt.mpr (Finset.inf'_le _ hzS)) hz
  · refine ⟨1, one_pos, fun z hz0 _ hQz => hne ⟨z, ?_⟩⟩
    exact Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ).mpr hQz), hz0⟩

theorem exists_forall_eval_ne_zero_of_lt_norm (Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ∃ B : ℝ, ∀ z : ℂ, B < ‖z‖ → Q.eval z ≠ 0 := by
  classical
  set S : Finset ℂ := Q.roots.toFinset with hS
  by_cases hne : S.Nonempty
  · refine ⟨S.sup' hne (fun r => ‖r‖), fun z hz hQz => ?_⟩
    have hzS : z ∈ S := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ).mpr hQz)
    exact (not_lt.mpr (Finset.le_sup' (fun r => ‖r‖) hzS)) hz
  · exact ⟨0, fun z _ hQz => hne ⟨z, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ).mpr hQz)⟩⟩

end Roots

section Far

variable {q : ℕ} (hq : 1 < q)
include hq

theorem norm_cpow (s : ℂ) : ‖(q : ℂ) ^ s‖ = (q : ℝ) ^ s.re :=
  Complex.norm_natCast_cpow_of_pos (lt_trans zero_lt_one hq) s

theorem tendsto_rpow_neg : Filter.Tendsto (fun σ : ℝ => (q : ℝ) ^ (-σ)) Filter.atTop (nhds 0) := by
  have hN : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < (q : ℝ) := lt_trans zero_lt_one hN
  have h := tendsto_rpow_atTop_of_base_lt_one ((q : ℝ))⁻¹ (by linarith [inv_pos.mpr hN0]) (inv_lt_one_of_one_lt₀ hN)
  refine h.congr fun σ => ?_
  rw [Real.inv_rpow hN0.le, Real.rpow_neg hN0.le]

theorem exists_forall_eval_cmul_q_one_sub_ne_zero (D : Polynomial ℂ) (hD : D ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → D.eval (c * (q : ℂ) ^ (1 - s)) ≠ 0 := by
  obtain ⟨δ, hδ, hDδ⟩ := exists_forall_eval_ne_zero_of_norm_lt D hD
  have hN : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < (q : ℝ) := lt_trans zero_lt_one hN
  have hc0 : 0 < ‖c‖ * (q : ℝ) := mul_pos (norm_pos_iff.mpr hc) hN0
  obtain ⟨σ, hσ⟩ := Filter.eventually_atTop.mp ((tendsto_rpow_neg hq).eventually (gt_mem_nhds (div_pos hδ hc0)))
  refine ⟨σ, fun s hs => hDδ _ (mul_ne_zero hc (cpow_ne_zero' hq _)) ?_⟩
  rw [norm_mul, norm_cpow hq, Complex.sub_re, Complex.one_re,
    show (1 : ℝ) - s.re = 1 + (-s.re) by ring, Real.rpow_add hN0, Real.rpow_one]
  calc ‖c‖ * ((q : ℝ) * (q : ℝ) ^ (-s.re)) = (‖c‖ * (q : ℝ)) * (q : ℝ) ^ (-s.re) := by ring
    _ ≤ (‖c‖ * (q : ℝ)) * (q : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)) hc0.le
    _ < (‖c‖ * (q : ℝ)) * (δ / (‖c‖ * (q : ℝ))) := mul_lt_mul_of_pos_left (hσ σ le_rfl) hc0
    _ = δ := by field_simp

theorem exists_forall_eval_cmul_qs_ne_zero (D : Polynomial ℂ) (hD : D ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → D.eval (c * (q : ℂ) ^ s) ≠ 0 := by
  obtain ⟨B, hDB⟩ := exists_forall_eval_ne_zero_of_lt_norm D hD
  have hN : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < (q : ℝ) := lt_trans zero_lt_one hN
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hB1 : 0 < (max B 1)⁻¹ * ‖c‖ := mul_pos (inv_pos.mpr (lt_of_lt_of_le one_pos (le_max_right _ _))) hc0
  obtain ⟨σ, hσ⟩ := Filter.eventually_atTop.mp ((tendsto_rpow_neg hq).eventually (gt_mem_nhds hB1))
  refine ⟨σ, fun s hs => hDB _ ?_⟩
  rw [norm_mul, norm_cpow hq]
  have hpos : 0 < (q : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos hN0 _
  have h1 : (q : ℝ) ^ (-s.re) < (max B 1)⁻¹ * ‖c‖ :=
    lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)) (hσ σ le_rfl)

  have h2 : max B 1 < ‖c‖ * ((q : ℝ) ^ (-s.re))⁻¹ := by
    have hm : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    rw [lt_mul_inv_iff₀ hpos]
    calc max B 1 * (q : ℝ) ^ (-s.re) < max B 1 * ((max B 1)⁻¹ * ‖c‖) := mul_lt_mul_of_pos_left h1 hm
      _ = ‖c‖ := by field_simp
  rw [Real.rpow_neg hN0.le, inv_inv] at h2
  exact lt_of_le_of_lt (le_max_left _ _) h2

end Far

section Cancel

variable {q : ℕ} (hq : 1 < q)
include hq

theorem q_intMul (k : ℤ) : LRep1 q (fun s => (q : ℂ) ^ ((k : ℂ) * s)) := by
  refine congr hq (fun s => ?_) (cxinv_zpow hq 1 one_ne_zero k)
  rw [one_mul, ← qs_eq_inv hq s, Complex.cpow_int_mul]

theorem exists_x_eq (z : ℂ) (hz : z ≠ 0) : ∃ s : ℂ, (q : ℂ) ^ (-s) = z := by
  have hlog : Complex.log (q : ℂ) ≠ 0 := by
    rw [← Complex.natCast_log]
    exact_mod_cast (Real.log_pos (by exact_mod_cast hq : (1 : ℝ) < q)).ne'
  refine ⟨-(Complex.log z / Complex.log (q : ℂ)), ?_⟩
  rw [Complex.cpow_def_of_ne_zero (qC_ne_zero hq), neg_neg, mul_div_cancel₀ _ hlog, Complex.exp_log hz]

theorem cancel {f H : ℂ → ℂ} (hf : LRep1 q f) (hH : LRep1 q H) {s₀ : ℂ} (hH0 : H s₀ ≠ 0)
    (hfH : ∀ s : ℂ, f s * H s = 0) : ∀ s : ℂ, f s = 0 := by
  obtain ⟨Pf, Mf, hPf⟩ := hf
  obtain ⟨PH, MH, hPH⟩ := hH
  have hPH0 : PH ≠ 0 := by
    intro h
    have := hPH s₀
    rw [h, Polynomial.eval_zero] at this
    exact (mul_ne_zero hH0 (pow_ne_zero _ (x_ne_zero hq s₀))) this
  have hR : Pf * PH = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ ((Set.finite_singleton (0 : ℂ)).infinite_compl)
    intro z hz
    obtain ⟨s, rfl⟩ := exists_x_eq hq z hz
    show Polynomial.IsRoot (Pf * PH) ((q : ℂ) ^ (-s))
    rw [Polynomial.IsRoot, Polynomial.eval_mul, ← hPf s, ← hPH s]
    calc f s * ((q : ℂ) ^ (-s)) ^ Mf * (H s * ((q : ℂ) ^ (-s)) ^ MH)
        = (f s * H s) * (((q : ℂ) ^ (-s)) ^ Mf * ((q : ℂ) ^ (-s)) ^ MH) := by ring
      _ = 0 := by rw [hfH s, zero_mul]
  intro s
  rcases mul_eq_zero.mp hR with h | h
  · have := hPf s
    rw [h, Polynomial.eval_zero] at this
    exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ (x_ne_zero hq s))
  · exact absurd h hPH0

theorem cancel_eq {f g H : ℂ → ℂ} (hf : LRep1 q f) (hg : LRep1 q g) (hH : LRep1 q H) {s₀ : ℂ} (hH0 : H s₀ ≠ 0)
    (hfgH : ∀ s : ℂ, f s * H s = g s * H s) : ∀ s : ℂ, f s = g s := by
  have := cancel hq (sub hq hf hg) hH hH0 (fun s => by rw [sub_mul, hfgH s, sub_self])
  intro s
  exact sub_eq_zero.mp (this s)

end Cancel

end Ws1.Middle.Laurent1

namespace Ws25
namespace LShift

section Matrices

variable {K : Type*} [Field K]

theorem weylPrime3_mul_iotaGL_diagUnits2 (α β : Kˣ) :
    (weylPrime3 : GL (Fin 3) K) * iotaGL (diagUnits2 α β) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) β * iotaGL (diagUnits2 (α * β⁻¹) β⁻¹) * weylPrime3 := by
  apply Units.ext
  have h2 : (β : K) ≠ 0 := β.ne_zero
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnits2, Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, weylPrime3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.GeneralLinearGroup.scalar, h2]
  field_simp

theorem longWeyl3_mul_scalar (z : Kˣ) :
    (longWeyl3 : GL (Fin 3) K) * Matrix.GeneralLinearGroup.scalar (Fin 3) z =
      Matrix.GeneralLinearGroup.scalar (Fin 3) z * longWeyl3 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longWeyl3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.GeneralLinearGroup.scalar]

theorem longWeyl3_mul_iotaGL_diagUnits2_one (β : Kˣ) :
    (longWeyl3 : GL (Fin 3) K) * iotaGL (diagUnits2 1 β) = iotaGL (diagUnits2 1 β) * longWeyl3 := by
  apply Units.ext
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnits2, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, longWeyl3, Matrix.mul_apply, Fin.sum_univ_three]

theorem iotaGL_mul_scalar (g : GL (Fin 2) K) (z : Kˣ) :
    iotaGL g * Matrix.GeneralLinearGroup.scalar (Fin 3) z = Matrix.GeneralLinearGroup.scalar (Fin 3) z * iotaGL g := by
  apply Units.ext
  simp only [Units.val_mul, coe_iotaGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.GeneralLinearGroup.scalar, mul_comm]

theorem diagUnits2_mul (a b c d : Kˣ) : diagUnits2 a b * diagUnits2 c d = diagUnits2 (a * c) (b * d) := by
  apply Units.ext
  simp only [Units.val_mul, coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem scalarPi_eq_diagUnits2 (π : K) (hπ : π ≠ 0) :
    scalarPi π hπ = diagUnits2 (Units.mk0 π hπ) (Units.mk0 π hπ) := by
  apply Units.ext
  show (!![π, 0; 0, π] : Matrix (Fin 2) (Fin 2) K) = _
  rw [coe_diagUnits2, Units.val_mk0]

def diagUnits2Hom : Kˣ × Kˣ →* GL (Fin 2) K where
  toFun p := diagUnits2 p.1 p.2
  map_one' := by
    apply Units.ext
    simp only [coe_diagUnits2, Prod.fst_one, Prod.snd_one, Units.val_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' p q := by
    show diagUnits2 (p.1 * q.1) (p.2 * q.2) = diagUnits2 p.1 p.2 * diagUnits2 q.1 q.2
    rw [diagUnits2_mul]

theorem diagUnits2_zpow (a b : Kˣ) (n : ℤ) : diagUnits2 a b ^ n = diagUnits2 (a ^ n) (b ^ n) := by
  have := (map_zpow (diagUnits2Hom (K := K)) (a, b) n).symm
  simpa [diagUnits2Hom] using this

theorem scalarPi_zpow (π : K) (hπ : π ≠ 0) (n : ℤ) :
    scalarPi π hπ ^ n = diagUnits2 (Units.mk0 π hπ ^ n) (Units.mk0 π hπ ^ n) := by
  rw [scalarPi_eq_diagUnits2, diagUnits2_zpow]

theorem diagUnitGL2_eq_diagUnits2 (u : Kˣ) : diagUnitGL2 u = diagUnits2 u 1 := by
  apply Units.ext
  rw [coe_diagUnitGL2, coe_diagUnits2, Units.val_one]

theorem torus_eq (π : K) (hπ : π ≠ 0) (n₁ n₂ : ℤ) :
    scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁) =
      diagUnits2 (Units.mk0 π hπ ^ (n₁ + n₂)) (Units.mk0 π hπ ^ n₂) := by
  rw [scalarPi_zpow, diagUnitGL2_eq_diagUnits2, diagUnits2_mul, mul_one, ← zpow_add, add_comm]

theorem torus_weylPrime3_scalarPi_zpow (π : K) (hπ : π ≠ 0) (n₁ n₂ ℓ : ℤ) :
    iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) * (weylPrime3 : GL (Fin 3) K) *
        iotaGL (scalarPi π hπ ^ ℓ) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 π hπ ^ ℓ) *
        iotaGL (scalarPi π hπ ^ (n₂ - ℓ) * diagUnitGL2 (Units.mk0 π hπ ^ (n₁ + ℓ))) * weylPrime3 := by
  rw [torus_eq, torus_eq, scalarPi_zpow, mul_assoc, weylPrime3_mul_iotaGL_diagUnits2, mul_inv_cancel,
    ← mul_assoc, ← mul_assoc, iotaGL_mul_scalar, mul_assoc (Matrix.GeneralLinearGroup.scalar _ _), ← map_mul,
    diagUnits2_mul, mul_one, ← zpow_neg, ← zpow_add]
  congr 2
  · congr 1 <;> ring_nf

theorem torus_mul_diagUnits2_one_inv (π : K) (hπ : π ≠ 0) (n₁ n₂ ℓ : ℤ) :
    iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) * iotaGL (diagUnits2 1 (Units.mk0 π hπ ^ ℓ)⁻¹) =
      iotaGL (scalarPi π hπ ^ (n₂ - ℓ) * diagUnitGL2 (Units.mk0 π hπ ^ (n₁ + ℓ))) := by
  rw [← map_mul, torus_eq, torus_eq, diagUnits2_mul, mul_one, ← zpow_neg, ← zpow_add]
  congr 2
  · congr 1 <;> ring_nf

theorem torus_longWeyl3_weylPrime3_scalarPi_zpow (π : K) (hπ : π ≠ 0) (n₁ n₂ ℓ : ℤ) :
    iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) * ((longWeyl3 : GL (Fin 3) K) * weylPrime3) *
        iotaGL (scalarPi π hπ ^ ℓ) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 π hπ ^ ℓ) *
        iotaGL (scalarPi π hπ ^ (n₂ - ℓ) * diagUnitGL2 (Units.mk0 π hπ ^ (n₁ + ℓ))) * (longWeyl3 * weylPrime3) := by
  have hB : (weylPrime3 : GL (Fin 3) K) * iotaGL (scalarPi π hπ ^ ℓ) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 π hπ ^ ℓ) * iotaGL (diagUnits2 1 (Units.mk0 π hπ ^ ℓ)⁻¹) *
        weylPrime3 := by
    rw [scalarPi_zpow, weylPrime3_mul_iotaGL_diagUnits2, mul_inv_cancel]
  calc iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) * ((longWeyl3 : GL (Fin 3) K) * weylPrime3) *
        iotaGL (scalarPi π hπ ^ ℓ)
      = iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) * longWeyl3 *
          ((weylPrime3 : GL (Fin 3) K) * iotaGL (scalarPi π hπ ^ ℓ)) := by simp only [mul_assoc]
    _ = iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) *
          ((longWeyl3 : GL (Fin 3) K) * Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 π hπ ^ ℓ)) *
          iotaGL (diagUnits2 1 (Units.mk0 π hπ ^ ℓ)⁻¹) * weylPrime3 := by rw [hB]; simp only [mul_assoc]
    _ = (iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) *
          Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 π hπ ^ ℓ)) *
          ((longWeyl3 : GL (Fin 3) K) * iotaGL (diagUnits2 1 (Units.mk0 π hπ ^ ℓ)⁻¹)) * weylPrime3 := by
        rw [longWeyl3_mul_scalar]; simp only [mul_assoc]
    _ = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 π hπ ^ ℓ) *
          (iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) * iotaGL (diagUnits2 1 (Units.mk0 π hπ ^ ℓ)⁻¹)) *
          (longWeyl3 * weylPrime3) := by
        rw [iotaGL_mul_scalar, longWeyl3_mul_iotaGL_diagUnits2_one]; simp only [mul_assoc]
    _ = _ := by rw [torus_mul_diagUnits2_one_inv]

end Matrices

section Arrays

variable {K : Type*} [Field K]

theorem apply_torus_weylPrime3_scalarPi_zpow (W : GL (Fin 3) K → ℂ) (ω : Kˣ →* ℂˣ)
    (hω : ∀ (z : Kˣ) (g : GL (Fin 3) K), W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (π : K) (hπ : π ≠ 0) (c : GL (Fin 3) K) (n₁ n₂ ℓ : ℤ) :
    W (iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) * (weylPrime3 * iotaGL (scalarPi π hπ ^ ℓ) * c)) =
      ((ω (Units.mk0 π hπ ^ ℓ) : ℂˣ) : ℂ) *
        W (iotaGL (scalarPi π hπ ^ (n₂ - ℓ) * diagUnitGL2 (Units.mk0 π hπ ^ (n₁ + ℓ))) * (weylPrime3 * c)) := by
  rw [show iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) * (weylPrime3 * iotaGL (scalarPi π hπ ^ ℓ) * c)
      = (iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) * weylPrime3 * iotaGL (scalarPi π hπ ^ ℓ)) * c by
        simp only [mul_assoc],
    torus_weylPrime3_scalarPi_zpow, mul_assoc, mul_assoc, hω, ← mul_assoc]

theorem apply_torus_longWeyl3_weylPrime3_scalarPi_zpow (W : GL (Fin 3) K → ℂ) (ω : Kˣ →* ℂˣ)
    (hω : ∀ (z : Kˣ) (g : GL (Fin 3) K), W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (π : K) (hπ : π ≠ 0) (c : GL (Fin 3) K) (n₁ n₂ ℓ : ℤ) :
    W (iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) *
        (longWeyl3 * weylPrime3 * iotaGL (scalarPi π hπ ^ ℓ) * c)) =
      ((ω (Units.mk0 π hπ ^ ℓ) : ℂˣ) : ℂ) *
        W (iotaGL (scalarPi π hπ ^ (n₂ - ℓ) * diagUnitGL2 (Units.mk0 π hπ ^ (n₁ + ℓ))) * (longWeyl3 * weylPrime3 * c)) := by
  rw [show iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) * (longWeyl3 * weylPrime3 * iotaGL (scalarPi π hπ ^ ℓ) * c)
      = (iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁)) * (longWeyl3 * weylPrime3) * iotaGL (scalarPi π hπ ^ ℓ)) * c by
        simp only [mul_assoc],
    torus_longWeyl3_weylPrime3_scalarPi_zpow, mul_assoc, mul_assoc, hω, ← mul_assoc]

end Arrays

end Ws25.LShift

namespace Ws1
namespace Middle
namespace Compare

open scoped ENNReal NNReal

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev Fv : Type := v.adicCompletion ℚ

abbrev G2 : Type := GL (Fin 2) (v.adicCompletion ℚ)

abbrev K2 : Subgroup (G2 v) := AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤

theorem isLocalLevelOne_top_of_integral {m : Matrix (Fin 2) (Fin 2) (Fv v)}
    (h : ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : Fv v)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_K2_iff (k : G2 v) :
    k ∈ K2 v ↔ (∀ i j, (k : Matrix (Fin 2) (Fin 2) (Fv v)) i j ∈ v.adicCompletionIntegers ℚ) ∧
      ∀ i j, ((k⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) i j ∈ v.adicCompletionIntegers ℚ := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral v h1, isLocalLevelOne_top_of_integral v h2⟩

theorem mem_K2_of_entries {k : G2 v}
    (h : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) (Fv v)) i j) ≤ 1)
    (h' : ∀ i j, Valued.v (((k⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) i j) ≤ 1) : k ∈ K2 v :=
  (mem_K2_iff v k).mpr ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h i j),
    fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h' i j)⟩

def lowerUnipotentGL2 (x : Fv v) : G2 v :=
  ⟨!![1, 0; x, 1], !![1, 0; -x, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_lowerUnipotentGL2 (x : Fv v) :
    ((lowerUnipotentGL2 v x : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![1, 0; x, 1] := rfl

theorem coe_inv_lowerUnipotentGL2 (x : Fv v) :
    (((lowerUnipotentGL2 v x)⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![1, 0; -x, 1] := rfl

theorem coe_inv_unipotentGL2 (x : Fv v) :
    (((unipotentGL2 x : G2 v)⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![1, -x; 0, 1] := rfl

theorem unipotentGL2_mem_K2 {y : Fv v} (hy : Valued.v y ≤ 1) : (unipotentGL2 y : G2 v) ∈ K2 v := by
  refine mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
  · rw [unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp [hy]
  · rw [coe_inv_unipotentGL2]
    fin_cases i <;> fin_cases j <;> simp [hy, Valuation.map_neg]

theorem lowerUnipotentGL2_mem_K2 {x : Fv v} (hx : Valued.v x ≤ 1) : lowerUnipotentGL2 v x ∈ K2 v := by
  refine mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
  · rw [coe_lowerUnipotentGL2]
    fin_cases i <;> fin_cases j <;> simp [hx]
  · rw [coe_inv_lowerUnipotentGL2]
    fin_cases i <;> fin_cases j <;> simp [hx, Valuation.map_neg]

theorem w0_mem_K2 {w₀ : G2 v} (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (Fv v)) = !![0, 1; 1, 0]) : w₀ ∈ K2 v := by
  have hinv : ((w₀⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![0, 1; 1, 0] := by
    rw [Matrix.coe_units_inv, hw₀]
    refine Matrix.inv_eq_left_inv ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine mem_K2_of_entries v (fun i j => ?_) (fun i j => ?_)
  · rw [hw₀]; fin_cases i <;> fin_cases j <;> simp
  · rw [hinv]; fin_cases i <;> fin_cases j <;> simp

def w0 : G2 v :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_w0 : ((w0 v : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![0, 1; 1, 0] := rfl

section Cyc

variable {v} {W₃ : LocalGL3 v → ℂ}

theorem law_of_mem_gl3CyclicSubspace {θ : AddChar (Fv v) ℂ}
    (hW₃law : IsGL3PsiWhittakerFn θ W₃) {W : LocalGL3 v → ℂ} (hW : W ∈ gl3CyclicSubspace W₃) :
    IsGL3PsiWhittakerFn θ W := by
  have hle : gl3CyclicSubspace W₃ ≤ gl3PsiWhittakerFnSpace (Fv v) ℂ θ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    exact rightTranslate_mem_gl3PsiWhittakerFnSpace θ h ((mem_gl3PsiWhittakerFnSpace_iff θ _).mpr hW₃law)
  exact (mem_gl3PsiWhittakerFnSpace_iff θ _).mp (hle hW)

theorem central_of_mem_gl3CyclicSubspace {ω : (Fv v)ˣ →* ℂˣ}
    (hω : ∀ (z : (Fv v)ˣ) (g : LocalGL3 v),
      W₃ (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W₃ g)
    {W : LocalGL3 v → ℂ} (hW : W ∈ gl3CyclicSubspace W₃) :
    ∀ (z : (Fv v)ˣ) (g : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g := by
  refine Submodule.span_induction (p := fun W _ => ∀ (z : (Fv v)ˣ) (g : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩ z g
    simp only [gl3AmbientRightTranslate_apply]
    rw [mul_assoc, hω]
  · intro z g; simp
  · intro f g _ _ hf hg z x
    simp only [Pi.add_apply]
    rw [hf, hg]; ring
  · intro a f _ hf z x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]; ring

theorem smooth_of_mem_gl3CyclicSubspace
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v,
      W₃ (g * k) = W₃ g)
    {W : LocalGL3 v → ℂ} (hW : W ∈ gl3CyclicSubspace W₃) :
    ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v,
      W (g * k) = W g := by
  refine Submodule.span_induction (p := fun W _ =>
      ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v,
        W (g * k) = W g) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩
    obtain ⟨Uv, hUv, hinv⟩ := hW₃sm
    let φ : LocalGL3 v →* LocalGL3 v := (MulAut.conj h⁻¹).toMonoidHom
    refine ⟨Uv.comap φ, ?_, ?_⟩
    · have hφ : Continuous φ := by
        change Continuous fun x : LocalGL3 v => h⁻¹ * x * h⁻¹⁻¹
        exact (continuous_const.mul continuous_id).mul continuous_const
      exact hUv.preimage hφ
    · intro k hk g
      have hk' : h⁻¹ * k * h ∈ Uv := by
        have := hk
        rw [Subgroup.mem_comap] at this
        simpa [φ] using this
      simp only [gl3AmbientRightTranslate_apply]
      have : g * k * h = g * h * (h⁻¹ * k * h) := by group
      rw [this, hinv _ hk']
  · obtain ⟨Uv, hUv, _⟩ := hW₃sm
    exact ⟨Uv, hUv, fun k _ g => rfl⟩
  · rintro f g _ _ ⟨U₁, hU₁, h₁⟩ ⟨U₂, hU₂, h₂⟩
    refine ⟨U₁ ⊓ U₂, ?_, fun k hk x => ?_⟩
    · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
    · simp only [Pi.add_apply]
      rw [h₁ k (Subgroup.mem_inf.mp hk).1, h₂ k (Subgroup.mem_inf.mp hk).2]
  · rintro a f _ ⟨U, hU, h⟩
    exact ⟨U, hU, fun k hk x => by simp only [Pi.smul_apply, smul_eq_mul]; rw [h k hk]⟩

end Cyc

theorem weylPrime3_mul_iotaGL_w0 : (weylPrime3 : LocalGL3 v) * iotaGL (w0 v) = longWeyl3 * weylPrime3 := by
  apply Units.ext
  simp only [Units.val_mul, coe_iotaGL, coe_w0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, longWeyl3, weylPrime3, Matrix.mul_apply, Fin.sum_univ_three]

theorem scalarPi_mul_comm {ϖ : v.adicCompletionIntegers ℚ} (hπ : (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 0) (g : G2 v) :
    scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ * g = g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ := by
  apply Units.ext
  simp only [Units.val_mul, UnramifiedWhittaker.scalarPi, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem merge (V : LocalGL3 v → ℂ) (hVK : ∀ k ∈ K2 v, ∀ g : LocalGL3 v, V (g * iotaGL k) = V g) :
    (fun x : LocalGL3 v => V (x * (longWeyl3 * weylPrime3))) = fun x : LocalGL3 v => V (x * weylPrime3) := by
  funext x
  rw [← weylPrime3_mul_iotaGL_w0, ← mul_assoc, hVK _ (w0_mem_K2 v (coe_w0 v))]

theorem mergeL (V : LocalGL3 v → ℂ) (hVK : ∀ k ∈ K2 v, ∀ g : LocalGL3 v, V (g * iotaGL k) = V g)
    {ϖ : v.adicCompletionIntegers ℚ} (hπ : (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) ≠ 0) (ℓ : ℤ) :
    (fun x : LocalGL3 v => V (x * (longWeyl3 * weylPrime3 * iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ ℓ)))) =
      fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ ℓ))) := by
  funext x
  have hc : iotaGL (w0 v) * iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ ℓ) =
      iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ ℓ) * (iotaGL (w0 v) : LocalGL3 v) := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact ((Commute.symm (scalarPi_mul_comm v hπ (w0 v))).zpow_right ℓ).eq
  rw [← weylPrime3_mul_iotaGL_w0, mul_assoc (weylPrime3 : LocalGL3 v), hc, ← mul_assoc (weylPrime3 : LocalGL3 v),
    ← mul_assoc x, hVK _ (w0_mem_K2 v (coe_w0 v))]

theorem selfDualHaarAt_real_integers_eq_one :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} = 1 := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := ⟨rfl⟩
  have hset : {x : v.adicCompletion ℚ | Valued.v x ≤ 1} =
      (integersPositiveCompacts ℚ v : Set (v.adicCompletion ℚ)) := by
    rw [coe_integersPositiveCompacts]; ext x
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 ℚ) ℚ v (x := x)).symm
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2) with hc
  have hdef : selfDualHaarAt ℚ v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) := rfl
  have hc1 : c = 1 := by rw [hc, addCharLevel_psiLocal_rat]; simp
  rw [Measure.real, hset, hdef, Measure.smul_apply, Measure.addHaarMeasure_self, hc1]
  simp

theorem reindex (A B : ℤ × ℤ → ℂ) (c : ℂ) (ℓ : ℕ)
    (hBA : ∀ n : ℤ × ℤ, B n = c * A (n.1 + ℓ, n.2 - ℓ))
    (N : ℤ) (D₁ D₂ : Polynomial ℂ) (P : MvPolynomial (Fin 2) ℂ) (r : ℝ)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N ∨ n.2 < N) → A n = 0)
    (hXY : ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ => ‖A (N + (m.1 : ℤ), N + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ, A (N + (m.1 : ℤ), N + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (D₁.eval X * D₂.eval Y) =
        MvPolynomial.eval ![X, Y] P) :
    (∀ n : ℤ × ℤ, (n.1 < N - ℓ ∨ n.2 < N - ℓ) → B n = 0) ∧
    ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ => ‖B (N - ℓ + (m.1 : ℤ), N - ℓ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ, B (N - ℓ + (m.1 : ℤ), N - ℓ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (D₁.eval X * D₂.eval Y) =
        MvPolynomial.eval ![X, Y] (MvPolynomial.C c * MvPolynomial.X 1 ^ (2 * ℓ) * P) := by
  refine ⟨fun n hn => ?_, fun X Y hX hY => ?_⟩
  · rw [hBA]
    rcases hn with h | h
    · rw [hsupp _ (Or.inl (by simp only; omega)), mul_zero]
    · rw [hsupp _ (Or.inr (by simp only; omega)), mul_zero]
  obtain ⟨hS, hT⟩ := hXY X Y hX hY

  set g : ℕ × ℕ → ℂ := fun m => B (N - ℓ + (m.1 : ℤ), N - ℓ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2 with hg
  set f : ℕ × ℕ → ℂ := fun m => A (N + (m.1 : ℤ), N + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2 with hf
  set i : ℕ × ℕ → ℕ × ℕ := fun m => (m.1, m.2 + 2 * ℓ) with hi
  have hinj : Function.Injective i := by
    intro a b h
    simp only [hi, Prod.mk.injEq] at h
    exact Prod.ext h.1 (by omega)
  have hgi : ∀ m : ℕ × ℕ, g (i m) = (c * Y ^ (2 * ℓ)) * f m := by
    intro m
    simp only [hg, hf, hi, hBA]
    have : (N - ℓ + (m.1 : ℤ) + ℓ, N - ℓ + ((m.2 + 2 * ℓ : ℕ) : ℤ) - ℓ) = (N + (m.1 : ℤ), N + (m.2 : ℤ)) := by
      ext <;> push_cast <;> ring
    rw [this, pow_add]
    ring
  have hsupport : Function.support g ⊆ Set.range i := by
    intro m hm
    by_contra hrange
    apply hm
    simp only [hg, hBA]
    have hlt : m.2 < 2 * ℓ := by
      by_contra hge
      exact hrange ⟨(m.1, m.2 - 2 * ℓ), by simp only [hi]; ext <;> simp <;> omega⟩
    rw [hsupp _ (Or.inr (by simp only; push_cast; omega)), mul_zero, zero_mul, zero_mul]
  have hsupport' : Function.support (fun m => ‖g m‖) ⊆ Set.range i := by
    intro m hm
    apply hsupport
    intro h0
    exact hm (by simp only [h0, norm_zero])
  constructor
  ·
    have h1 : Summable (fun m => ‖g (i m)‖) := by
      simp_rw [hgi, norm_mul]
      exact hS.mul_left _
    have hz : ∀ m ∉ Set.range i, ‖g m‖ = 0 := fun m hm => by
      by_contra h
      exact hm (hsupport' h)
    exact (hinj.summable_iff hz).mp h1
  ·
    have h2 : ∑' m, g m = ∑' m, g (i m) := (hinj.tsum_eq hsupport).symm
    rw [show (∑' m : ℕ × ℕ, B (N - ℓ + (m.1 : ℤ), N - ℓ + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) = ∑' m, g m from rfl, h2]
    simp_rw [hgi]
    rw [tsum_mul_left, mul_assoc, show (∑' m, f m) = ∑' m : ℕ × ℕ, A (N + (m.1 : ℤ), N + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2
      from rfl, hT]
    simp only [map_mul, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one]

theorem core {A₁ B₁ A₂ B₂ Dn Nm Nmℓ cP cD wNP wDP wND wDD ρ ε : ℂ}
    (h1 : A₁ * (Dn * Dn * wDP) = B₁ * cP * (Nm * Dn * wDP + wNP * Nm * Dn))
    (h2 : A₂ * (Dn * Dn * wDD) = B₂ * cD * (Nmℓ * Dn * wDD + wND * Nmℓ * Dn))
    (hNum : Nmℓ = ρ * Nm)
    (hsc : cD * ρ * ((wDD + wND) * wDP) = ε ^ 2 * cP * ((wDP + wNP) * wDD)) :
    (A₂ * B₁ - ε ^ 2 * A₁ * B₂) * (Dn * Dn * wDP * wDD) = 0 := by
  subst hNum
  linear_combination (B₁ * wDP) * h2 - (ε ^ 2 * B₂ * wDD) * h1 + (B₁ * B₂ * Dn * Nm) * hsc

theorem inv_mul_inv_helper (A B : ℂ) : (A * B⁻¹)⁻¹ = B * A⁻¹ := by
  rw [mul_inv, inv_inv, mul_comm]

theorem num_shift (X Y c : ℂ) (hX : X ≠ 0) (hY : Y ≠ 0) (N : ℤ) (ℓ : ℕ) (P : MvPolynomial (Fin 2) ℂ) :
    X ^ (N - ℓ) * Y ^ (N - ℓ) * MvPolynomial.eval ![X, Y] (MvPolynomial.C c * MvPolynomial.X 1 ^ (2 * ℓ) * P) =
      (c * X ^ (-(ℓ : ℤ)) * Y ^ (ℓ : ℤ)) * (X ^ N * Y ^ N * MvPolynomial.eval ![X, Y] P) := by
  simp only [map_mul, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_fin_one]
  rw [zpow_sub₀ hX, zpow_sub₀ hY, zpow_neg]
  simp only [zpow_natCast]
  field_simp
  ring

theorem scalar_core (cK m₁ Ji e₁ e₂ A xx om a₁ a₂ ε : ℂ) (hA : A ≠ 0) (hx : xx ≠ 0) (hom : om ≠ 0)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hε : ε ≠ 0) (ℓ : ℕ) :
    cK * 1 * m₁ ^ 2 * Ji * ((A * a₁⁻¹) ^ ℓ)⁻¹ * ε * (A * xx) ^ ℓ * e₁ * e₂ *
        (om ^ ℓ * ((a₁ * A⁻¹ * (A * A * xx)) ^ ℓ)⁻¹ * ((a₂ * A⁻¹)⁻¹ * om⁻¹ * xx⁻¹) ^ ℓ) =
      ε ^ 2 * (cK * 1 ^ 2 * 1 * m₁ ^ 2 * Ji * ε⁻¹ * A⁻¹ ^ ℓ * ((a₂ * A⁻¹ * xx) ^ ℓ)⁻¹ * e₁ * e₂) := by
  have e1 : a₁ * A⁻¹ * (A * A * xx) = a₁ * A * xx := by field_simp
  rw [e1]
  simp only [mul_pow, inv_pow, mul_inv, inv_inv]
  field_simp

end Ws1.Middle.Compare

open Ws1.Middle.Compare in
set_option maxHeartbeats 16000000 in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W) (hW1 : W 1 = 1)
    (hmult : HasWhittakerMultOne ψv W)
    (hirr : ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ B ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ t))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωu : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hω : ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ωv t : ℂˣ) : ℂ) * W h)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)))
    (V : LocalGL3 v → ℂ) (hVmem : V ∈ gl3CyclicSubspace W)
    (hVK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, V (g * iotaGL k) = V g)
    (hVdK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v,
      dualWhittakerFn3 V (g * iotaGL k) = dualWhittakerFn3 V g)
    (a₁ a₂ u : ℂ) (cK : ℝ) (ha : a₁ * a₂ ≠ 0) (hcK : 0 < cK)
    (m₁P m₂P : Polynomial ℂ) (kP : ℤ) (m₁d m₂d : Polynomial ℂ) (kd : ℤ) :
    letI := localBorel ℚ v
    (
      ∀ (Nb : ℤ) (Db₁ Db₂ : Polynomial ℂ) (Pb : MvPolynomial (Fin 2) ℂ) (rb : ℝ),
        (
        let A : ℤ × ℤ → ℂ := fun n =>
          (fun x : LocalGL3 v => V (x * (longWeyl3 * weylPrime3))) (iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
              diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)))
        (
          Db₁.eval 0 ≠ 0 ∧ Db₂.eval 0 ≠ 0 ∧ 0 < rb ∧
          (∀ n : ℤ × ℤ, (n.1 < Nb ∨ n.2 < Nb) → A n = 0) ∧
          ∀ X Y : ℂ, ‖X‖ < rb → ‖Y‖ < rb →
            Summable (fun m : ℕ × ℕ => ‖A (Nb + (m.1 : ℤ), Nb + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
            (∑' m : ℕ × ℕ, A (Nb + (m.1 : ℤ), Nb + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (Db₁.eval X * Db₂.eval Y) =
              MvPolynomial.eval ![X, Y] Pb)
        ) →
      ∀ (Nt : ℤ) (Dt₁ Dt₂ : Polynomial ℂ) (Pt : MvPolynomial (Fin 2) ℂ) (rt : ℝ),
        (
        let A : ℤ × ℤ → ℂ := fun n =>
          (fun x : LocalGL3 v => V (x * weylPrime3)) (iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
              diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)))
        (
          Dt₁.eval 0 ≠ 0 ∧ Dt₂.eval 0 ≠ 0 ∧ 0 < rt ∧
          (∀ n : ℤ × ℤ, (n.1 < Nt ∨ n.2 < Nt) → A n = 0) ∧
          ∀ X Y : ℂ, ‖X‖ < rt → ‖Y‖ < rt →
            Summable (fun m : ℕ × ℕ => ‖A (Nt + (m.1 : ℤ), Nt + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
            (∑' m : ℕ × ℕ, A (Nt + (m.1 : ℤ), Nt + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (Dt₁.eval X * Dt₂.eval Y) =
              MvPolynomial.eval ![X, Y] Pt)
        ) →
      ∀ s : ℂ,
        m₁P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kP : ℂ) * s) *
            ((Db₁.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Db₂.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * (Dt₁.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Dt₂.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * ((Ideal.absNorm v.asIdeal : ℂ))) =
          m₂P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (((cK : ℂ) * (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) ^ 2 * (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) ^ 2 * ((((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹))⁻¹) * ε⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((ℓ : ℂ) / 2)) * ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (-(ℓ : ℤ)) *
    E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)))) *
            (((((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ Nb * (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) ^ Nb * MvPolynomial.eval ![((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s), ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s] Pb) * (Dt₁.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Dt₂.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * ((Ideal.absNorm v.asIdeal : ℂ)) +
              ((1 : ℂ)) * ((((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ Nt * (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) ^ Nt * MvPolynomial.eval ![((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s), ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s] Pt) * (Db₁.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Db₂.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)))) →
    (
      ∀ (Nb : ℤ) (Db₁ Db₂ : Polynomial ℂ) (Pb : MvPolynomial (Fin 2) ℂ) (rb : ℝ),
        (
        let A : ℤ × ℤ → ℂ := fun n =>
          (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
              diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)))
        (
          Db₁.eval 0 ≠ 0 ∧ Db₂.eval 0 ≠ 0 ∧ 0 < rb ∧
          (∀ n : ℤ × ℤ, (n.1 < Nb ∨ n.2 < Nb) → A n = 0) ∧
          ∀ X Y : ℂ, ‖X‖ < rb → ‖Y‖ < rb →
            Summable (fun m : ℕ × ℕ => ‖A (Nb + (m.1 : ℤ), Nb + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
            (∑' m : ℕ × ℕ, A (Nb + (m.1 : ℤ), Nb + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (Db₁.eval X * Db₂.eval Y) =
              MvPolynomial.eval ![X, Y] Pb)
        ) →
      ∀ (Nt : ℤ) (Dt₁ Dt₂ : Polynomial ℂ) (Pt : MvPolynomial (Fin 2) ℂ) (rt : ℝ),
        (
        let A : ℤ × ℤ → ℂ := fun n =>
          (fun x : LocalGL3 v => V (x * (longWeyl3 * weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ))))) (iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
              diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)))
        (
          Dt₁.eval 0 ≠ 0 ∧ Dt₂.eval 0 ≠ 0 ∧ 0 < rt ∧
          (∀ n : ℤ × ℤ, (n.1 < Nt ∨ n.2 < Nt) → A n = 0) ∧
          ∀ X Y : ℂ, ‖X‖ < rt → ‖Y‖ < rt →
            Summable (fun m : ℕ × ℕ => ‖A (Nt + (m.1 : ℤ), Nt + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2‖) ∧
            (∑' m : ℕ × ℕ, A (Nt + (m.1 : ℤ), Nt + (m.2 : ℤ)) * X ^ m.1 * Y ^ m.2) * (Dt₁.eval X * Dt₂.eval Y) =
              MvPolynomial.eval ![X, Y] Pt)
        ) →
      ∀ s : ℂ,
        m₁d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kd : ℂ) * s) *
            ((Db₁.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Db₂.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * (Dt₁.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Dt₂.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹)) =
          m₂d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (((cK : ℂ) * (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) ^ 2 * ((((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹))⁻¹ * (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹) ^ ℓ)⁻¹) * ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) *
    E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)))) *
            (((((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ Nb * (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) ^ Nb * MvPolynomial.eval ![((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s), ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s] Pb) * (Dt₁.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Dt₂.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) +
              ((1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) * ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) * ((((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ Nt * (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) ^ Nt * MvPolynomial.eval ![((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s), ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s] Pt) * (Db₁.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) * Db₂.eval (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s)))) →
    ∀ s : ℂ, m₁d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kd : ℂ) * s) * m₂P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
      ε ^ 2 * (m₁P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kP : ℂ) * s)) * m₂d.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := localBorel ℚ v
  intro hP hD

  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hNcpow : ∀ w : ℂ, (Ideal.absNorm v.asIdeal : ℂ) ^ w ≠ 0 := fun w h => hN0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have ha₁ : a₁ ≠ 0 := left_ne_zero_of_mul ha
  have ha₂ : a₂ ≠ 0 := right_ne_zero_of_mul ha
  have hA1 : (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) ≠ 0 := mul_ne_zero ha₁ (hNcpow _)
  have hA2 : (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) ≠ 0 := mul_ne_zero ha₂ (hNcpow _)
  have hω0 : ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _

  have hψne : ψv ≠ 1 := by
    intro h
    apply LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ v
    ext a
    have h' := congrArg (fun χ : AddChar (v.adicCompletion ℚ) ℂ => χ (-a)) h
    simp only [AddChar.one_apply] at h'
    rw [hψinv, AddChar.inv_apply, neg_neg] at h'
    rw [h', AddChar.one_apply]

  have hVω := central_of_mem_gl3CyclicSubspace hω hVmem
  have hΦmem : (fun x : LocalGL3 v => V (x * weylPrime3)) ∈ gl3CyclicSubspace W :=
    gl3AmbientRightTranslate_mem_gl3CyclicSubspace W weylPrime3 hVmem
  have hΦsm := smooth_of_mem_gl3CyclicSubspace hsm hΦmem
  obtain ⟨N, D₁, D₂, P, r, hD₁, hD₂, hr, hsupp, hXY⟩ :=
    LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_tsum_torus_apply_mul_eval_eq_of_mem_gl3CyclicSubspace
      v ψv hψne W hW hsm hadm ωv hω hπ hϖ _ hΦmem hΦsm

  have h1 := hP N D₁ D₂ P r (by rw [merge v V hVK]; exact ⟨hD₁, hD₂, hr, hsupp, hXY⟩) N D₁ D₂ P r
    ⟨hD₁, hD₂, hr, hsupp, hXY⟩

  set c : ℂ := ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ)) : ℂˣ) : ℂ) with hc
  have hBA : ∀ n : ℤ × ℤ,
      (fun x : LocalGL3 v => V (x * (weylPrime3 * iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (ℓ : ℤ)))))
        (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1))) =
      c * (fun x : LocalGL3 v => V (x * weylPrime3))
        (iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (n.1 + ℓ, n.2 - ℓ).2 *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ (n.1 + ℓ, n.2 - ℓ).1))) := by
    intro n
    have := Ws25.LShift.apply_torus_weylPrime3_scalarPi_zpow V ωv hVω (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ 1 n.1 n.2 (ℓ : ℤ)
    simp only [mul_one] at this
    exact this
  obtain ⟨hsuppℓ, hXYℓ⟩ := reindex _ _ c ℓ hBA N D₁ D₂ P r hsupp hXY
  have h2 := hD (N - ℓ) D₁ D₂ (MvPolynomial.C c * MvPolynomial.X 1 ^ (2 * ℓ) * P) r ⟨hD₁, hD₂, hr, hsuppℓ, hXYℓ⟩
    (N - ℓ) D₁ D₂ (MvPolynomial.C c * MvPolynomial.X 1 ^ (2 * ℓ) * P) r
    (by rw [mergeL v V hVK hπ]; exact ⟨hD₁, hD₂, hr, hsuppℓ, hXYℓ⟩)

  have hq : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hneg : (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)) = ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2))⁻¹ := Complex.cpow_neg _ _
  have hA0 : (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) ≠ 0 := hNcpow _
  have hXD : ∀ s : ℂ, ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s) = ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s) := fun s => by rw [hneg, mul_inv, inv_inv]; ring
  have hYD : ∀ s : ℂ, ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹) * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s = ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s := fun s => by rw [hneg, inv_mul_inv_helper]
  have hμ₀ : (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) = 1 := by
    have h := selfDualHaarAt_real_integers_eq_one v
    rw [h]; simp
  have hcω : c = ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) ^ ℓ := by
    rw [hc, map_zpow, Units.val_zpow_eq_zpow_val, zpow_natCast]

  have key : ∀ s : ℂ, (Polynomial.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) m₁d * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kd : ℂ) * s) * Polynomial.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) m₂P - ε ^ 2 * (Polynomial.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) m₁P * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kP : ℂ) * s)) * Polynomial.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) m₂d) * ((Polynomial.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) D₁ * Polynomial.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) D₂) * (Polynomial.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) D₁ * Polynomial.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) D₂) * (Ideal.absNorm v.asIdeal : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹)) = 0 := by
    intro s
    have e1 := h1 s
    have e2 := h2 s
    rw [hXD s, hYD s] at e2
    have hx0 : (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) ≠ 0 := hNcpow _
    have hX0 : ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s) ≠ 0 := mul_ne_zero (mul_ne_zero hA1 (hNcpow _)) (hNcpow _)
    have hY0 : ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s ≠ 0 := mul_ne_zero (mul_ne_zero (inv_ne_zero (mul_ne_zero hA2 (hNcpow _))) (inv_ne_zero hω0)) (hNcpow _)

    have hNm := num_shift (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) c hX0 hY0 N ℓ P

    have hw : ((1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) + (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) * ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) * (Ideal.absNorm v.asIdeal : ℂ) = ((Ideal.absNorm v.asIdeal : ℂ) + (1 : ℂ)) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) := by
      field_simp

    have hcc : (((cK : ℂ) * (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) ^ 2 * ((((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹))⁻¹ * (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹) ^ ℓ)⁻¹) * ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) *
    E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)))) * (c * (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ (-(ℓ : ℤ)) * (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) ^ (ℓ : ℤ)) = ε ^ 2 * (((cK : ℂ) * (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) ^ 2 * (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) ^ 2 * ((((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹))⁻¹) * ε⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((ℓ : ℂ) / 2)) * ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (-(ℓ : ℤ)) *
    E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)))) := by
      rw [hμ₀, hcω]
      by_cases hε : ε = 0
      · simp [hε]
      have hxs : (Ideal.absNorm v.asIdeal : ℂ) ^ s = ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by rw [Complex.cpow_neg, inv_inv]
      have h1s : (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s) = (Ideal.absNorm v.asIdeal : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) := by
        rw [sub_eq_add_neg, Complex.cpow_add _ _ hN0, Complex.cpow_one]
      have hℓ2 : (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) = ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ ℓ := by
        rw [Complex.cpow_nat_mul, sub_eq_add_neg, Complex.cpow_add _ _ hN0]
      have hℓ1 : (Ideal.absNorm v.asIdeal : ℂ) ^ (-((ℓ : ℂ) / 2)) = ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2))⁻¹ ^ ℓ := by
        rw [show (-((ℓ : ℂ) / 2)) = (ℓ : ℂ) * (-((1 : ℂ) / 2)) by ring, Complex.cpow_nat_mul, Complex.cpow_neg]
      have hhalf : (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) = (Ideal.absNorm v.asIdeal : ℂ) := by
        rw [← Complex.cpow_add _ _ hN0, add_halves, Complex.cpow_one]
      set a₁' : ℂ := (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) with ha₁'
      set a₂' : ℂ := (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) with ha₂'
      set e₁ : ℂ := Polynomial.eval (a₁' * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) E with he₁
      set e₂ : ℂ := Polynomial.eval (a₂'⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s))) Ed with he₂
      set m₁ : ℂ := ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) with hm₁
      set om : ℂ := ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) with hom
      rw [hℓ2, hℓ1, hneg, h1s, hxs]
      simp only [zpow_neg, zpow_natCast]
      set A : ℂ := (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) with hA
      set xx : ℂ := (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) with hxx
      set Ji : ℂ := ((1 : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * a₁' * a₂'⁻¹))⁻¹ with hJi
      rw [← hhalf]
      linear_combination scalar_core (cK : ℂ) m₁ Ji e₁ e₂ A xx om a₁' a₂' ε hA0 hx0 hω0 hA1 hA2 hε ℓ
    have hsc : (((cK : ℂ) * (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) ^ 2 * ((((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹))⁻¹ * (((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u))⁻¹) ^ ℓ)⁻¹) * ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s)) *
    E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)))) * (c * (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) ^ (-(ℓ : ℤ)) * (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) ^ (ℓ : ℤ)) *
        (((1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) + (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) * ((Ideal.absNorm v.asIdeal : ℂ))⁻¹) * (Ideal.absNorm v.asIdeal : ℂ)) = ε ^ 2 * (((cK : ℂ) * (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) ^ 2 * (((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * ((((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) {e : (v.adicCompletion ℚ)ˣ | Valued.v (e : v.adicCompletion ℚ) = 1}).toReal : ℝ) : ℂ) ^ 2 * ((((selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹))⁻¹) * ε⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((ℓ : ℂ) / 2)) * ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 : ℂ)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (-(ℓ : ℤ)) *
    E.eval ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s + 1 / 2))) * Ed.eval ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 / 2 - s)))) * (((Ideal.absNorm v.asIdeal : ℂ) + (1 : ℂ)) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹)) := by
      rw [hcc, hw, mul_assoc]
    exact core e1 e2 hNm hsc

  have hf : Ws1.Middle.Laurent1.LRep1 (Ideal.absNorm v.asIdeal) (fun s : ℂ => Polynomial.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) m₁d * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kd : ℂ) * s) * Polynomial.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) m₂P - ε ^ 2 * (Polynomial.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) m₁P * (Ideal.absNorm v.asIdeal : ℂ) ^ ((kP : ℂ) * s)) * Polynomial.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) m₂d) :=
    Ws1.Middle.Laurent1.sub hq
      (Ws1.Middle.Laurent1.mul hq (Ws1.Middle.Laurent1.mul hq (Ws1.Middle.Laurent1.polyEval hq m₁d (Ws1.Middle.Laurent1.x hq))
        (Ws1.Middle.Laurent1.q_intMul hq kd)) (Ws1.Middle.Laurent1.polyEval hq m₂P (Ws1.Middle.Laurent1.x hq)))
      (Ws1.Middle.Laurent1.mul hq (Ws1.Middle.Laurent1.mul hq (Ws1.Middle.Laurent1.const hq (ε ^ 2))
        (Ws1.Middle.Laurent1.mul hq (Ws1.Middle.Laurent1.polyEval hq m₁P (Ws1.Middle.Laurent1.x hq))
          (Ws1.Middle.Laurent1.q_intMul hq kP))) (Ws1.Middle.Laurent1.polyEval hq m₂d (Ws1.Middle.Laurent1.x hq)))
  have hXl : Ws1.Middle.Laurent1.LRep1 (Ideal.absNorm v.asIdeal) (fun s : ℂ => ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) :=
    Ws1.Middle.Laurent1.smul hq _ (Ws1.Middle.Laurent1.q_one_sub' hq)
  have hYl : Ws1.Middle.Laurent1.LRep1 (Ideal.absNorm v.asIdeal) (fun s : ℂ => ((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) :=
    Ws1.Middle.Laurent1.smul hq _ (Ws1.Middle.Laurent1.xinv hq)
  have hH : Ws1.Middle.Laurent1.LRep1 (Ideal.absNorm v.asIdeal) (fun s : ℂ => (Polynomial.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) D₁ * Polynomial.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) D₂) * (Polynomial.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) D₁ * Polynomial.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) D₂) * (Ideal.absNorm v.asIdeal : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹)) :=
    Ws1.Middle.Laurent1.mul hq (Ws1.Middle.Laurent1.mul hq (Ws1.Middle.Laurent1.mul hq
      (Ws1.Middle.Laurent1.mul hq (Ws1.Middle.Laurent1.polyEval hq D₁ hXl) (Ws1.Middle.Laurent1.polyEval hq D₂ hYl))
      (Ws1.Middle.Laurent1.mul hq (Ws1.Middle.Laurent1.polyEval hq D₁ hXl) (Ws1.Middle.Laurent1.polyEval hq D₂ hYl)))
      (Ws1.Middle.Laurent1.const hq _)) (Ws1.Middle.Laurent1.const hq _)

  have hne : ∀ D : Polynomial ℂ, D.eval 0 ≠ 0 → D ≠ 0 := fun D hD h => hD (by rw [h, Polynomial.eval_zero])
  obtain ⟨σ₁, hσ₁⟩ := Ws1.Middle.Laurent1.exists_forall_eval_cmul_q_one_sub_ne_zero hq D₁ (hne _ hD₁)
    ((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) (mul_ne_zero hA1 (hNcpow _))
  obtain ⟨σ₂, hσ₂⟩ := Ws1.Middle.Laurent1.exists_forall_eval_cmul_qs_ne_zero hq D₂ (hne _ hD₂)
    (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹) (mul_ne_zero (inv_ne_zero (mul_ne_zero hA2 (hNcpow _))) (inv_ne_zero hω0))
  have hw0 : (1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_comm]
    intro h
    have h1 : (Ideal.absNorm v.asIdeal : ℂ) = 1 := inv_eq_one.mp h
    have : (Ideal.absNorm v.asIdeal : ℕ) = 1 := by exact_mod_cast h1
    omega
  set s₀ : ℂ := ((max σ₁ σ₂ + 1 : ℝ) : ℂ) with hs₀
  have hre : s₀.re = max σ₁ σ₂ + 1 := by rw [hs₀, Complex.ofReal_re]
  have hH0 : (fun s : ℂ => (Polynomial.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) D₁ * Polynomial.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) D₂) * (Polynomial.eval (((a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (-u)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2))) * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 - s)) D₁ * Polynomial.eval (((a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ u) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((1 : ℂ) / 2)))⁻¹ * ((ωv (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)⁻¹ * (Ideal.absNorm v.asIdeal : ℂ) ^ s) D₂) * (Ideal.absNorm v.asIdeal : ℂ) * (1 - ((Ideal.absNorm v.asIdeal : ℂ))⁻¹)) s₀ ≠ 0 := by
    have h₁ := hσ₁ s₀ (by rw [hre]; linarith [le_max_left σ₁ σ₂])
    have h₂ := hσ₂ s₀ (by rw [hre]; linarith [le_max_right σ₁ σ₂])
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h₁ h₂) (mul_ne_zero h₁ h₂)) hN0) hw0
  have hzero := Ws1.Middle.Laurent1.cancel hq hf hH hH0 key
  intro s
  exact sub_eq_zero.mp (hzero s)

end

end S_LanglandsTunnell_CubicInduction_middleDatum_compare_of_primalMiddleDatum_of_dualMiddleDatum_of_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_middleDatum_compare_of_primalMiddleDatum_of_dualMiddleDatum_of_ne_zero (solution)
