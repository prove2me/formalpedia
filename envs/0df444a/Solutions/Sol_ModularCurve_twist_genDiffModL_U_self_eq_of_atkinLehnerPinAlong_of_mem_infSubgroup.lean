-- Prove2me | solution 1 for ModularCurve.twist_genDiffModL_U_self_eq_of_atkinLehnerPinAlong_of_mem_infSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/167a0db0-0fdf-5785-bd7c-0b758a4b1a55

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Theorems.Thm_ModularCurve_IsInfReductionMap_comp_baseChange_genU_self_eq_genDiffModL_comp
import Theorems.Thm_ModularCurve_diffQExp_qExpFunctionFieldC_injective
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one
import Theorems.Thm_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm
import Theorems.Thm_ModularFormClass_qExpansion_heckeU_eq_heckeU
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_CuspForm_stableD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_twist_genDiffModL_U_self_eq_of_atkinLehnerPinAlong_of_mem_infSubgroup
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one FreyPackage.ModMCarrier.coe_rescaleLin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one"
p2m_attr_erase "simp" "Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm TensorProduct
open CongruenceSubgroup

namespace TwistUpEngine

variable {M N : ℕ}

def cocycle (N p a b j j' t : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(N * a + j * (N * p)) * (j' + 1) - b - j * N, a * t - a * b - j * N * a * j' - j * p * b;
     (N * p) * (p * j' + p - 1), N * a - p * N * a * j' - p ^ 2 * b]

theorem det_cocycle (N p a b j j' t : ℤ) (h1 : N * a - p * b = 1) (h2 : p * t = b + j * N - N * a * j') :
    (cocycle N p a b j j' t).det = 1 := by
  rw [cocycle, Matrix.det_fin_two_of]
  linear_combination (N * a - p * b + 1) * h1 - N * a * (j' * p + p - 1) * h2

def cocycleSL (N p a b j j' t : ℤ) (h1 : N * a - p * b = 1) (h2 : p * t = b + j * N - N * a * j') :
    SL(2, ℤ) :=
  ⟨cocycle N p a b j j' t, det_cocycle N p a b j j' t h1 h2⟩

theorem cocycleSL_apply_10 (N p a b j j' t : ℤ) (h1 : N * a - p * b = 1)
    (h2 : p * t = b + j * N - N * a * j') :
    (cocycleSL N p a b j j' t h1 h2 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (N * p) * (p * j' + p - 1) := by
  simp [cocycleSL, cocycle]

theorem cocycleSL_apply_11 (N p a b j j' t : ℤ) (h1 : N * a - p * b = 1)
    (h2 : p * t = b + j * N - N * a * j') :
    (cocycleSL N p a b j j' t h1 h2 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = N * a - p * N * a * j' - p ^ 2 * b := by
  simp [cocycleSL, cocycle]

lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

variable [NeZero M] (W : ModularForm.AtkinLehnerDatum M N) {p : ℕ}

theorem heckeMatrix_mul_alGL (hR : W.R = p) (hp : p ≠ 0) (j j' : ℕ) (t : ℤ)
    (h2 : (p : ℤ) * t = W.b + (j : ℤ) * N - (N : ℤ) * W.a * j') :
    ModularForm.heckeMatrix p j * W.alGL =
      (Matrix.SpecialLinearGroup.mapGL ℝ
          (cocycleSL N p W.a W.b j j' t (by rw [← W.bezout, hR]) h2) : GL (Fin 2) ℝ) *
        (W.alGL * ModularForm.heckeMatrix p j') := by
  have h1 : (N : ℤ) * W.a - p * W.b = 1 := by rw [← W.bezout, hR]
  have h1R : (N : ℝ) * W.a - p * W.b = 1 := by exact_mod_cast h1
  have h2R : (p : ℝ) * t = W.b + (j : ℝ) * N - (N : ℝ) * W.a * j' := by exact_mod_cast h2
  refine Matrix.GeneralLinearGroup.ext fun i k => ?_
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularForm.val_heckeMatrix hp,
    ModularForm.AtkinLehnerDatum.alGL_coe, mapGL_coe_eq, Matrix.map_apply,
    ModularForm.AtkinLehnerDatum.mat, cocycleSL, cocycle, hR]
  fin_cases i <;> fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, eq_intCast] <;>
    push_cast
  · linear_combination (-((N : ℝ) * (W.a + j * p))) * h1R + (-((N : ℝ) * W.a)) * h2R
  · linear_combination (-((N : ℝ) * j + W.b)) * h1R + (-((N : ℝ) * W.a * (j' + 1))) * h2R
  · linear_combination (-((N : ℝ) * p ^ 2)) * h1R
  · linear_combination (-((N : ℝ) * p)) * h1R

omit [NeZero M] in

theorem cocycleSL_mem_Gamma0 (hR : W.R = p) (j j' : ℕ) (t : ℤ)
    (h2 : (p : ℤ) * t = W.b + (j : ℤ) * N - (N : ℤ) * W.a * j') :
    cocycleSL N p W.a W.b j j' t (by rw [← W.bezout, hR]) h2 ∈ Gamma0 M := by
  rw [Gamma0_mem]
  show ((((cocycleSL N p W.a W.b j j' t _ h2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M) = 0
  rw [cocycleSL_apply_10]
  have hM : ((N : ℤ) * p : ℤ) = (M : ℤ) := by rw [W.hM, hR]; push_cast; ring
  rw [hM]
  push_cast
  simp

omit [NeZero M] in

theorem cocycleSL_apply_11_mod (hR : W.R = p) (j j' : ℕ) (t : ℤ)
    (h2 : (p : ℤ) * t = W.b + (j : ℤ) * N - (N : ℤ) * W.a * j') :
    ((((cocycleSL N p W.a W.b j j' t (by rw [← W.bezout, hR]) h2 : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = (p : ZMod N) := by
  rw [cocycleSL_apply_11]
  have h1 : (N : ℤ) * W.a - p * W.b = 1 := by rw [← W.bezout, hR]
  have h1' : ((N : ZMod N)) * (W.a : ZMod N) - (p : ZMod N) * (W.b : ZMod N) = 1 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ZMod N)) h1
  rw [ZMod.natCast_self, zero_mul, zero_sub] at h1'
  push_cast
  rw [ZMod.natCast_self]
  linear_combination (p : ZMod N) * h1'

def sigmaIdx (p : ℕ) (j : ℕ) : ℕ := ((W.b + (j : ℤ) * N) % (p : ℤ)).toNat

def tauIdx (p : ℕ) (j' : ℕ) : ℕ := ((((j' : ℤ) - W.b) * W.a) % (p : ℤ)).toNat

omit [NeZero M] in
lemma cast_toNat_emod (x : ℤ) (hp : 0 < p) : ((((x % (p : ℤ)).toNat : ℕ)) : ℤ) = x % p :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne'))

omit [NeZero M] in
lemma toNat_emod_lt (x : ℤ) (hp : 0 < p) : (x % (p : ℤ)).toNat < p := by
  have h : ((((x % (p : ℤ)).toNat : ℕ)) : ℤ) < p := by
    rw [cast_toNat_emod x hp]
    exact Int.emod_lt_of_pos _ (by exact_mod_cast hp)
  exact_mod_cast h

omit [NeZero M] in
lemma modEq_of_eq {a b n : ℤ} (h : a = b) : a ≡ b [ZMOD n] := h ▸ Int.ModEq.refl a

omit [NeZero M] in
lemma sigmaIdx_lt (hp : 0 < p) (j : ℕ) : sigmaIdx W p j < p := toNat_emod_lt _ hp

omit [NeZero M] in
lemma tauIdx_lt (hp : 0 < p) (j' : ℕ) : tauIdx W p j' < p := toNat_emod_lt _ hp

omit [NeZero M] in
lemma sigmaIdx_modEq (hp : 0 < p) (j : ℕ) :
    ((sigmaIdx W p j : ℕ) : ℤ) ≡ W.b + (j : ℤ) * N [ZMOD p] := by
  rw [sigmaIdx, cast_toNat_emod _ hp]
  exact Int.mod_modEq _ _

omit [NeZero M] in
lemma tauIdx_modEq (hp : 0 < p) (j' : ℕ) :
    ((tauIdx W p j' : ℕ) : ℤ) ≡ ((j' : ℤ) - W.b) * W.a [ZMOD p] := by
  rw [tauIdx, cast_toNat_emod _ hp]
  exact Int.mod_modEq _ _

omit [NeZero M] in

lemma Na_modEq_one (hR : W.R = p) : (N : ℤ) * W.a ≡ 1 [ZMOD p] := by
  have h1 : (N : ℤ) * W.a - p * W.b = 1 := by rw [← W.bezout, hR]
  rw [Int.modEq_iff_dvd]
  exact ⟨-W.b, by linear_combination -h1⟩

omit [NeZero M] in
lemma tauIdx_sigmaIdx (hR : W.R = p) (hp : 0 < p) {j : ℕ} (hj : j < p) :
    tauIdx W p (sigmaIdx W p j) = j := by
  have h : ((tauIdx W p (sigmaIdx W p j) : ℕ) : ℤ) = j := by
    have hmod : ((tauIdx W p (sigmaIdx W p j) : ℕ) : ℤ) ≡ j [ZMOD p] := by
      refine (tauIdx_modEq W hp _).trans ?_
      have h1 := ((sigmaIdx_modEq W hp j).sub_right W.b).mul_right W.a
      refine h1.trans ?_
      have h2 := (Na_modEq_one W hR).mul_left (j : ℤ)
      refine (Int.ModEq.trans ?_ h2).trans (by rw [mul_one])
      exact modEq_of_eq (by ring)
    have := hmod
    rw [Int.ModEq, tauIdx, cast_toNat_emod _ hp, Int.emod_emod_of_dvd _ (dvd_refl _),
      ← cast_toNat_emod _ hp, ← tauIdx] at this
    rw [this]
    exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hj)
  exact_mod_cast h

omit [NeZero M] in
lemma sigmaIdx_tauIdx (hR : W.R = p) (hp : 0 < p) {j' : ℕ} (hj' : j' < p) :
    sigmaIdx W p (tauIdx W p j') = j' := by
  have h : ((sigmaIdx W p (tauIdx W p j') : ℕ) : ℤ) = j' := by
    have hmod : ((sigmaIdx W p (tauIdx W p j') : ℕ) : ℤ) ≡ j' [ZMOD p] := by
      refine (sigmaIdx_modEq W hp _).trans ?_
      have h1 := ((tauIdx_modEq W hp j').mul_right (N : ℤ)).add_left W.b
      refine h1.trans ?_
      have h2 := ((Na_modEq_one W hR).mul_left ((j' : ℤ) - W.b)).add_left W.b
      refine (Int.ModEq.trans ?_ h2).trans (modEq_of_eq (by ring))
      exact modEq_of_eq (by ring)
    have := hmod
    rw [Int.ModEq, sigmaIdx, cast_toNat_emod _ hp, Int.emod_emod_of_dvd _ (dvd_refl _),
      ← cast_toNat_emod _ hp, ← sigmaIdx] at this
    rw [this]
    exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hj')
  exact_mod_cast h

omit [NeZero M] in

lemma exists_witness (hR : W.R = p) (hp : 0 < p) (j : ℕ) :
    ∃ t : ℤ, (p : ℤ) * t = W.b + (j : ℤ) * N - (N : ℤ) * W.a * (sigmaIdx W p j : ℕ) := by
  have hmod : (N : ℤ) * W.a * (sigmaIdx W p j : ℕ) ≡ W.b + (j : ℤ) * N [ZMOD p] := by
    have h1 := (Na_modEq_one W hR).mul_right ((sigmaIdx W p j : ℕ) : ℤ)
    rw [one_mul] at h1
    exact h1.trans (sigmaIdx_modEq W hp j)
  obtain ⟨t, ht⟩ := (Int.modEq_iff_dvd.mp hmod)
  exact ⟨t, by linear_combination -ht⟩

theorem alSlash_heckeU (hR : W.R = p) (hp : p.Prime) (k : ℤ) (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
      ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ)) : ZMod N) = (p : ZMod N) →
        F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = F) :
    ModularForm.alSlash W k (ModularForm.heckeU k p F) =
      ModularForm.heckeU k p (ModularForm.alSlash W k F) := by
  have hp0 : 0 < p := hp.pos
  simp only [ModularForm.alSlash_def, ModularForm.heckeU_def, SlashAction.sum_slash,
    ← SlashAction.slash_mul]
  refine Finset.sum_nbij' (sigmaIdx W p) (tauIdx W p) (fun j _ => ?_) (fun j' _ => ?_)
    (fun j hj => tauIdx_sigmaIdx W hR hp0 (Finset.mem_range.mp hj))
    (fun j' hj' => sigmaIdx_tauIdx W hR hp0 (Finset.mem_range.mp hj')) (fun j _ => ?_)
  · exact Finset.mem_range.mpr (sigmaIdx_lt W hp0 j)
  · exact Finset.mem_range.mpr (tauIdx_lt W hp0 j')
  · obtain ⟨t, ht⟩ := exists_witness W hR hp0 j
    rw [heckeMatrix_mul_alGL W hR hp.ne_zero j (sigmaIdx W p j) t ht, SlashAction.slash_mul,
      hF _ (cocycleSL_mem_Gamma0 W hR j _ t ht) (cocycleSL_apply_11_mod W hR j _ t ht)]

end TwistUpEngine

namespace TwistUpForms

open CohCarrier

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

abbrev Γ (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem_GammaH : ModularGroup.T ∈ GammaH M H := by
  rw [mem_GammaH_iff]
  have hT0 : ModularGroup.T ∈ Gamma0 M := by
    rw [Gamma0_mem]; simp [ModularGroup.T]
  refine ⟨hT0, ?_⟩
  have : gamma0Units M ⟨ModularGroup.T, hT0⟩ = 1 := by
    ext
    rw [val_gamma0Units]
    show ((ModularGroup.T 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    simp [ModularGroup.T]
  rw [this]
  exact one_mem H

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ M H).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem T_mem_GammaH]
  exact AddSubgroup.mem_zmultiples _

theorem mem_GammaH_of_unitsMap_eq {R : ℕ} (hR : R ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap hR u = 1 → u ∈ H)
    {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 M) {u : (ZMod M)ˣ} (hu : u ∈ H)
    (h : ZMod.unitsMap hR (gamma0Units M ⟨δ, hδ⟩) = ZMod.unitsMap hR u) :
    δ ∈ GammaH M H := by
  rw [mem_GammaH_iff]
  refine ⟨hδ, ?_⟩
  have hker : gamma0Units M ⟨δ, hδ⟩ * u⁻¹ ∈ H :=
    hHp _ (by rw [map_mul, map_inv, h, mul_inv_cancel])
  simpa using H.mul_mem hker hu

theorem neg_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : -γ ∈ Gamma0 M := by
  rw [Gamma0_mem] at hγ ⊢
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, hγ, neg_zero]

theorem gamma0Units_neg {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    gamma0Units M ⟨-γ, neg_mem_Gamma0 hγ⟩ = -gamma0Units M ⟨γ, hγ⟩ := by
  ext
  rw [Units.val_neg, val_gamma0Units, val_gamma0Units]
  show (((-γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = -(((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M)
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]

theorem unitsMap_neg {R : ℕ} (hR : R ∣ M) (u : (ZMod M)ˣ) :
    ZMod.unitsMap hR (-u) = -ZMod.unitsMap hR u := by
  ext
  rw [ZMod.unitsMap_val, Units.val_neg, Units.val_neg, ZMod.unitsMap_val, ZMod.cast_neg hR]

theorem slash_neg_one_two (F : UpperHalfPlane → ℂ) :
    F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = F := by
  ext τ
  have h := ModularForm.SL_slash_apply (k := 2) F (-1 : SL(2, ℤ)) τ
  change (F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ = _ at h
  rw [h, ModularGroup.SL_neg_smul, one_smul, ModularGroup.denom_apply]
  simp [Matrix.SpecialLinearGroup.coe_neg]
  all_goals norm_num

variable [NeZero M]

omit [NeZero M] in

theorem slash_eq_self_of_apply_11 {p : ℕ} [Fact p.Prime] (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (d : (ZMod M)ˣ)
    (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)
    (g : CuspForm (GammaH M H) 2) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (h11 : ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ)) : ZMod (M / p)) = (p : ZMod (M / p))) :
    ⇑g ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑g := by
  have hu : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (gamma0Units M ⟨γ, hγ⟩) =
      ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d := by
    ext
    rw [ZMod.unitsMap_val, val_gamma0Units, hd]
    show ((((((γ : SL(2, ℤ)) 1 1 : ℤ)) : ZMod M)).cast : ZMod (M / p)) = (p : ZMod (M / p))
    rw [ZMod.cast_intCast (Nat.div_dvd_of_dvd hpM)]
    exact h11
  rcases hdH with h | h
  · obtain ⟨u, hu', hue⟩ := (ModularCurve.mem_infSubgroup_iff p M H hpM _).mp h
    have hmem : γ ∈ GammaH M H :=
      mem_GammaH_of_unitsMap_eq (Nat.div_dvd_of_dvd hpM) hHp hγ hu' (hu.trans hue.symm)
    exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hmem)
  · obtain ⟨u, hu', hue⟩ := (ModularCurve.mem_infSubgroup_iff p M H hpM _).mp h
    have hmem : -γ ∈ GammaH M H := by
      refine mem_GammaH_of_unitsMap_eq (Nat.div_dvd_of_dvd hpM) hHp (neg_mem_Gamma0 hγ) hu' ?_
      rw [gamma0Units_neg hγ, unitsMap_neg, hu, hue]
    have e : γ = (-1 : SL(2, ℤ)) * (-γ) := by rw [neg_one_mul, neg_neg]
    rw [e, map_mul, SlashAction.slash_mul, slash_neg_one_two,
      SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hmem)]

theorem R_eq {p : ℕ} [Fact p.Prime] (hpM : p ∣ M) (Wd : ModularForm.AtkinLehnerDatum M (M / p)) :
    Wd.R = p := by
  have hN : M / p ≠ 0 := (Nat.div_ne_zero_iff_of_dvd hpM).mpr ⟨NeZero.ne M, (Fact.out : p.Prime).ne_zero⟩
  have h1 : M = (M / p) * p := (Nat.div_mul_cancel hpM).symm
  have h2 : (M / p) * Wd.R = (M / p) * p := by rw [← Wd.hM, ← h1]
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN) h2

theorem map_heckeU {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (p : ℕ) (P : PowerSeries A) :
    (PowerSeries.heckeU p P).map φ = PowerSeries.heckeU p (P.map φ) := by
  ext n
  simp [PowerSeries.coeff_map, PowerSeries.coeff_heckeU]

theorem heckeU_pin {p : ℕ} [Fact p.Prime] (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ) (d : (ZMod M)ˣ)
    (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)
    (f : CuspForm (GammaH M H) 2) (D : ℕ) (pfW : PowerSeries ↥(integralClosure ℤ ℂ))
    (hpfW : pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f))) :
    (PowerSeries.heckeU p pfW).map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1
        ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e (CuspForm.heckeULinH 2 p f))) := by
  have hp : p.Prime := Fact.out
  have hR : Wd.R = p := R_eq hpM Wd
  have hU : CuspForm.StableU M H 2 p := CuspForm.stableU M H 2 hp hpM
  set g : CuspForm (GammaH M H) 2 := CuspForm.diamondLinH 2 e ((D : ℂ) • f) with hg
  obtain ⟨X, hX⟩ :=
    CuspForm.exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one Wd H hHp 2 g

  have hfun1 : (D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f) = ⇑X := by
    rw [hX, hg, map_smul, CuspForm.IsGLPos.coe_smul, ModularForm.alSlash_smul]
  have hcomm : CuspForm.diamondLinH 2 e (CuspForm.heckeULinH 2 p f) =
      CuspForm.heckeULinH 2 p (CuspForm.diamondLinH 2 e f) :=
    ((CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm M H 2).2.2.2.1 p hp hpM e f).symm
  have hF : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
      ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ)) : ZMod (M / p)) = (p : ZMod (M / p)) →
        ⇑g ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑g :=
    fun γ hγ h11 => slash_eq_self_of_apply_11 hpM hHp d hd hdH g γ hγ h11
  have hfun2 : (D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e (CuspForm.heckeULinH 2 p f)) =
      ModularForm.heckeU 2 p ⇑X := by
    rw [hcomm, ← ModularForm.alSlash_smul, ← CuspForm.IsGLPos.coe_smul, ← map_smul, ← map_smul,
      CuspForm.coe_heckeULinH_apply 2 hU, ← hg, TwistUpEngine.alSlash_heckeU Wd hR hp 2 ⇑g hF, hX]
  rw [map_heckeU, hpfW, hfun1, hfun2,
    ModularFormClass.qExpansion_heckeU_eq_heckeU X one_mem_strictPeriods hp.ne_zero]

end TwistUpForms

namespace TwistUpDiff

open ModularCurve HahnSeries

theorem coeff_ofPowerSeries_of_neg {R : Type*} [CommRing R] (P : PowerSeries R) {n : ℤ} (hn : n < 0) :
    (ofPowerSeries ℤ R P).coeff n = 0 := by
  rw [ofPowerSeries_apply, embDomain_notin_range]
  rintro ⟨m, hm⟩
  have : (0 : ℤ) ≤ n := by rw [← hm]; exact Int.natCast_nonneg m
  omega

theorem qDecimate_ofPowerSeries (K : Type*) [Field K] (p : ℕ) [NeZero p] (P : PowerSeries K) :
    qDecimate K p (ofPowerSeries ℤ K P) = ofPowerSeries ℤ K (PowerSeries.heckeU p P) := by
  ext n
  rw [coeff_qDecimate]
  rcases lt_or_ge n 0 with hn | hn
  · rw [coeff_ofPowerSeries_of_neg P (by
        have : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
        nlinarith), coeff_ofPowerSeries_of_neg _ hn]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [show ((p : ℤ) * (m : ℤ) : ℤ) = ((p * m : ℕ) : ℤ) by push_cast; ring,
      ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, PowerSeries.coeff_heckeU]

end TwistUpDiff

end

open scoped TensorProduct MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K] (S : Set ℕ)

    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (hrange : LinearMap.range ρinf = ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)

    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)

    (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)

    (φ : ↥(integralClosure ℤ ℂ) →+* K) (hφ : φ (p : ↥(integralClosure ℤ ℂ)) = 0)

    (W : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) ≃ₗ[K] ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))
    (hW :
      ∀ (f : CuspForm (CohCarrier.GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D)
          (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) →
          ∀ ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p), ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
              ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
                ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩) →
            (D : K) • ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
              HahnSeries.ofPowerSeries ℤ K (pfW.map φ))

    (hspan : Submodule.span K {ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) |
        ∃ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D) (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) ∧
          ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
            ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
              ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)} = ⊤)
    :

      (∀ (ω ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)), ((ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U p Fact.out hpM) ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) →
        ((W ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U p Fact.out hpM) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])) := by
  classical

  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro ω ω' hω'

  have hG : ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U p Fact.out hpM) =
      ModularCurve.frobPushDiffModL K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p :=
    ModularCurve.genDiffModL_U_self K p M H hpM S Fact.out hpM
  by_cases hC : ∃ C : Ω[ModularCurve.qExpFunctionFieldC K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K] →ₗ[K]
      Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K],
      ModularCurve.IsFrobPushDiff K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p C
  swap
  ·
    rw [hG, ModularCurve.frobPushDiffModL_of_not hC, LinearMap.zero_apply] at hω'
    rw [hG, ModularCurve.frobPushDiffModL_of_not hC, LinearMap.zero_apply]
    have : ω' = 0 := Subtype.ext (by rw [hω']; rfl)
    rw [this, map_zero]
    rfl

  have hpin : ModularCurve.IsFrobPushDiff K
      (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p
      (ModularCurve.frobPushDiffModL K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) :=
    ModularCurve.isFrobPushDiff_frobPushDiffModL hC
  have hΘG : ∀ y : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K],
      ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
        (ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U p Fact.out hpM) y) =
      ModularCurve.qDecimate K p (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) y) := fun y => by
    rw [hG]; exact hpin y

  have hC4 := ModularCurve.IsInfReductionMap.comp_baseChange_genU_self_eq_genDiffModL_comp p M hpM hpM2 H
    hHp K S hρinf

  have hstab : ∀ x ∈ ModularCurve.ssPolarDifferentials K
      (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p,
      ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U p Fact.out hpM) x ∈
        ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p := by
    intro x hx
    rw [← hrange] at hx ⊢
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    exact LinearMap.mem_range.mpr ⟨_, LinearMap.congr_fun hC4 y⟩
  set G' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) →ₗ[K]
      ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) :=
    (ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U p Fact.out hpM)).restrict hstab with hG'

  have hinj := ModularCurve.diffQExp_qExpFunctionFieldC_injective K
    (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) TwistUpForms.T_mem_GammaH
  have hDK : ∀ D : ℕ, ¬ p ∣ D → (D : K) ≠ 0 := fun D hD h0 => hD ((CharP.cast_eq_zero_iff K p D).mp h0)

  have key : Set.EqOn
      ((W : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) →ₗ[K]
          ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) ∘ₗ G')
      (G' ∘ₗ (W : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) →ₗ[K]
          ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)))
      {ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) |
        ∃ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D) (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) ∧
          ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
            ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
              ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)} := by
    rintro x ⟨f, hf, D, hD, pfW, hpfW, hx⟩
    apply Subtype.ext
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hG',
      LinearMap.coe_restrict_apply]

    have hf₂ : CuspForm.heckeULinH 2 p f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) :=
      CuspForm.heckeRingH_apply_mem_twoCuspIntegralSet
        (CuspForm.heckeGenH_mem_heckeRingH S 2 (CohCarrier.Gen.U p Fact.out hpM)) hf
    have E1 : (((ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U p Fact.out hpM)).restrict hstab x :
        ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) :
          Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
        ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
          ⟨CuspForm.heckeULinH 2 p f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf₂⟩) := by
      rw [LinearMap.coe_restrict_apply, hx]
      have h := LinearMap.congr_fun hC4
        ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
          ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul] at h
      rw [← h]
      rfl
    have P2 := hW (CuspForm.heckeULinH 2 p f) hf₂ D hD (PowerSeries.heckeU p pfW)
      (TwistUpForms.heckeU_pin hpM hHp Wd e d hd hdH f D pfW hpfW) _ E1
    have P1 := hW f hf D hD pfW hpfW x hx
    apply hinj
    rw [hΘG]
    have h3 : (D : K) • ModularCurve.qDecimate K p
        (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
          ((W x : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) :
            Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])) =
        HahnSeries.ofPowerSeries ℤ K ((PowerSeries.heckeU p pfW).map φ) := by
      rw [← LinearMap.map_smul, P1, TwistUpDiff.qDecimate_ofPowerSeries, TwistUpForms.map_heckeU]
    calc _ = (D : K)⁻¹ • ((D : K) • ModularCurve.diffQExp _ _) := (inv_smul_smul₀ (hDK D hD) _).symm
      _ = (D : K)⁻¹ • ((D : K) • ModularCurve.qDecimate K p (ModularCurve.diffQExp _ _)) := by rw [P2, h3]
      _ = _ := inv_smul_smul₀ (hDK D hD) _

  have hWG := LinearMap.ext_on hspan key
  have hωG : ω' = G' ω := Subtype.ext (by rw [hG', LinearMap.coe_restrict_apply]; exact hω')
  rw [hωG]
  have h := congrArg Subtype.val (LinearMap.congr_fun hWG ω)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  rw [h, hG', LinearMap.coe_restrict_apply]

end S_ModularCurve_twist_genDiffModL_U_self_eq_of_atkinLehnerPinAlong_of_mem_infSubgroup
end P2MW
export P2MW.S_ModularCurve_twist_genDiffModL_U_self_eq_of_atkinLehnerPinAlong_of_mem_infSubgroup (solution)
