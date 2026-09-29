-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral22_schwartz_clearedFE_of_principalSeries2_of_forall_torusZeta_fe_ed2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/62caa89a-c812-505d-9359-20cae3dcb936

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral22_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral22_dual_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
import Theorems.Thm_RatFunc_X_zpow_mul_div_eq_of_forall_lt_re_mul_eval_cpow_neg_eq
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_clearedFE_of_principalSeries2_of_forall_torusZeta_fe_ed2
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.mem_sigmaCentralizer_iff"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace DSGlue

def IsLaurent (g : ℂ → ℂ) : Prop :=
  ∃ (K : ℕ) (F : Polynomial ℂ), ∀ u : ℂ, u ≠ 0 → g u * u ^ K = F.eval u

theorem IsLaurent.const (a : ℂ) : IsLaurent (fun _ => a) :=
  ⟨0, Polynomial.C a, fun u _ => by simp⟩

theorem IsLaurent.pow (n : ℕ) : IsLaurent (fun u => u ^ n) :=
  ⟨0, Polynomial.X ^ n, fun u _ => by simp⟩

theorem IsLaurent.eval (P : Polynomial ℂ) : IsLaurent (fun u => P.eval u) :=
  ⟨0, P, fun u _ => by simp⟩

theorem IsLaurent.zpow (n : ℤ) : IsLaurent (fun u => u ^ n) := by
  refine ⟨n.natAbs, Polynomial.X ^ (n + n.natAbs).toNat, fun u hu => ?_⟩
  have h0 : 0 ≤ n + n.natAbs := by omega
  rw [Polynomial.eval_pow, Polynomial.eval_X, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hu,
    Int.toNat_of_nonneg h0]

theorem IsLaurent.add {f g : ℂ → ℂ} (hf : IsLaurent f) (hg : IsLaurent g) :
    IsLaurent (fun u => f u + g u) := by
  obtain ⟨K, F, hF⟩ := hf
  obtain ⟨L, G, hG⟩ := hg
  refine ⟨K + L, F * Polynomial.X ^ L + G * Polynomial.X ^ K, fun u hu => ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← hF u hu, ← hG u hu]
  ring

theorem IsLaurent.sub {f g : ℂ → ℂ} (hf : IsLaurent f) (hg : IsLaurent g) :
    IsLaurent (fun u => f u - g u) := by
  obtain ⟨K, F, hF⟩ := hf
  obtain ⟨L, G, hG⟩ := hg
  refine ⟨K + L, F * Polynomial.X ^ L - G * Polynomial.X ^ K, fun u hu => ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← hF u hu, ← hG u hu]
  ring

theorem IsLaurent.mul {f g : ℂ → ℂ} (hf : IsLaurent f) (hg : IsLaurent g) :
    IsLaurent (fun u => f u * g u) := by
  obtain ⟨K, F, hF⟩ := hf
  obtain ⟨L, G, hG⟩ := hg
  refine ⟨K + L, F * G, fun u hu => ?_⟩
  rw [Polynomial.eval_mul, ← hF u hu, ← hG u hu]
  ring

theorem IsLaurent.sum (n : ℕ) (f : ℕ → ℂ → ℂ) (h : ∀ i, IsLaurent (f i)) :
    IsLaurent (fun u => ∑ i ∈ Finset.range n, f i u) := by
  induction n with
  | zero => exact ⟨0, 0, fun u _ => by simp⟩
  | succ n ih =>
    obtain ⟨K, F, hF⟩ := ih
    obtain ⟨L, G, hG⟩ := h n
    refine ⟨K + L, F * Polynomial.X ^ L + G * Polynomial.X ^ K, fun u hu => ?_⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← hF u hu, ← hG u hu, Finset.sum_range_succ]
    ring

theorem IsLaurent.eval_inv (P : Polynomial ℂ) : IsLaurent (fun u => P.eval u⁻¹) := by
  obtain ⟨K, F, hF⟩ := IsLaurent.sum (P.natDegree + 1) (fun i u => P.coeff i * u ^ (-(i : ℤ)))
    (fun i => (IsLaurent.const (P.coeff i)).mul (IsLaurent.zpow (-(i : ℤ))))
  refine ⟨K, F, fun u hu => ?_⟩
  rw [← hF u hu]
  show P.eval u⁻¹ * u ^ K = (∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * u ^ (-(i : ℤ))) * u ^ K
  rw [Polynomial.eval_eq_sum_range]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zpow_neg, zpow_natCast, inv_pow]

theorem IsLaurent.eq_zero_of_infinite {g : ℂ → ℂ} (hg : IsLaurent g)
    (hinf : {u : ℂ | u ≠ 0 ∧ g u = 0}.Infinite) : ∀ u : ℂ, u ≠ 0 → g u = 0 := by
  obtain ⟨K, F, hF⟩ := hg
  have hF0 : F = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine hinf.mono fun u hu => ?_
    obtain ⟨hu0, hgu⟩ := hu
    show F.IsRoot u
    rw [Polynomial.IsRoot, ← hF u hu0, hgu, zero_mul]
  intro u hu
  have h := hF u hu
  rw [hF0, Polynomial.eval_zero] at h
  exact (mul_eq_zero.1 h).resolve_right (pow_ne_zero _ hu)

theorem puncturedDisc_infinite (R : ℝ) (hR : 0 < R) : {u : ℂ | u ≠ 0 ∧ ‖u‖ < R}.Infinite := by
  refine ((Set.infinite_image_iff Complex.ofReal_injective.injOn).2 (Set.Ioo_infinite hR)).mono ?_
  rintro u ⟨t, ⟨ht0, htR⟩, rfl⟩
  exact ⟨by exact_mod_cast ht0.ne', by rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]⟩

theorem zpow_form (x : ℂ) (n : ℤ) (s : ℂ) : x ^ ((n : ℂ) * s) = (x ^ (-s)) ^ (-n) := by
  rw [← Complex.cpow_int_mul]; congr 1; push_cast; ring

theorem zpow_form' (x : ℂ) (n : ℤ) (s : ℂ) : x ^ ((n : ℂ) * -s) = (x ^ (-s)) ^ n :=
  Complex.cpow_int_mul x n (-s)

theorem inv_form (x : ℂ) (s : ℂ) : x ^ s = (x ^ (-s))⁻¹ := by
  rw [Complex.cpow_neg, inv_inv]

theorem sq_form (x : ℂ) (s : ℂ) : x ^ (-(2 : ℂ) * s) = (x ^ (-s)) ^ 2 := by
  rw [show -(2 : ℂ) * s = ((2 : ℕ) : ℂ) * -s by push_cast; ring]
  exact Complex.cpow_nat_mul x 2 (-s)

theorem sq_form' (x : ℂ) (s : ℂ) : x ^ ((2 : ℂ) * s) = ((x ^ (-s))⁻¹) ^ 2 := by
  rw [show (2 : ℂ) * s = ((2 : ℕ) : ℂ) * s by push_cast; ring, Complex.cpow_nat_mul, inv_form x s]

theorem natCast_cpow_ne_zero (N : ℕ) (hN : N ≠ 0) (z : ℂ) : (N : ℂ) ^ z ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hN)]; exact Complex.exp_ne_zero _

theorem exists_eq_cpow_neg (q : ℝ) (hq : 1 < q) (σ₀ : ℝ) (z : ℂ) (hz : z ≠ 0) (hzR : ‖z‖ < q ^ (-σ₀)) :
    ∃ s : ℂ, σ₀ < s.re ∧ (q : ℂ) ^ (-s) = z := by
  have hq0 : 0 < q := one_pos.trans hq
  have hlogq : 0 < Real.log q := Real.log_pos hq
  refine ⟨-(Complex.log z) / (Real.log q : ℂ), ?_, ?_⟩
  · have hre : (-(Complex.log z) / (Real.log q : ℂ)).re = -Real.log ‖z‖ / Real.log q := by
      rw [Complex.div_ofReal_re, Complex.neg_re, Complex.log_re]
    rw [hre, lt_div_iff₀ hlogq]
    have h1 : Real.log ‖z‖ < -σ₀ * Real.log q := by
      have := Real.log_lt_log (norm_pos_iff.2 hz) hzR
      rwa [Real.log_rpow hq0] at this
    linarith
  · rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hq0.ne'), (Complex.ofReal_log hq0.le).symm]
    have hne : ((Real.log q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlogq.ne'
    rw [show ((Real.log q : ℝ) : ℂ) * -(-Complex.log z / (Real.log q : ℂ)) = Complex.log z by field_simp]
    exact Complex.exp_log hz

theorem exists_eq_natCast_cpow_neg (N : ℕ) (hN : 1 < N) (σ₀ : ℝ) (z : ℂ) (hz : z ≠ 0)
    (hzR : ‖z‖ < (N : ℝ) ^ (-σ₀)) : ∃ s : ℂ, σ₀ < s.re ∧ (N : ℂ) ^ (-s) = z := by
  obtain ⟨s, hs, h⟩ := exists_eq_cpow_neg (N : ℝ) (by exact_mod_cast hN) σ₀ z hz hzR
  exact ⟨s, hs, by exact_mod_cast h⟩

end DSGlue

end

open DSGlue in

theorem Delta2p.clearedFE_of_laurentFE_of_forall_lt_re
    (N : ℕ) (hN : 1 < N) (c Γc : ℂ) (hc : c ≠ 0) (k : ℤ)
    (P Pd Q Qd P₁ P₂ : Polynomial ℂ) (m md m₁ m₂ : ℤ) (σ σ' : ℝ)
    (hA1 : ∀ s : ℂ, σ < s.re →
      (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)) * (1 - c * (N : ℂ) ^ (-(2 : ℂ) * s)) =
        (N : ℂ) ^ ((m₁ : ℂ) * s) * P₁.eval ((N : ℂ) ^ (-s)) * Q.eval ((N : ℂ) ^ (-s)))
    (hA2 : ∀ s : ℂ, σ' < s.re →
      (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s)) * (1 - c⁻¹ * (N : ℂ) ^ (-(2 : ℂ)) * (N : ℂ) ^ (-(2 : ℂ) * s)) =
        (N : ℂ) ^ ((m₂ : ℂ) * s) * P₂.eval ((N : ℂ) ^ (-s)) * Qd.eval ((N : ℂ) ^ (-s)))
    (hcore : ∀ s : ℂ,
      (N : ℂ) ^ ((m₂ : ℂ) * s) * P₂.eval ((N : ℂ) ^ (-s)) * (1 - c * (N : ℂ) ^ ((2 : ℂ) * s)) =
        (Γc * (N : ℂ) ^ ((k : ℂ) * s)) *
          ((N : ℂ) ^ ((m₁ : ℂ) * (-s)) * P₁.eval ((N : ℂ) ^ s)) *
          (1 - c⁻¹ * (N : ℂ) ^ (-(2 : ℂ)) * (N : ℂ) ^ (-(2 : ℂ) * s))) :
    ∀ s : ℂ,
      ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) * ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) * Q.eval ((N : ℂ) ^ s) =
        ((Polynomial.C Γc).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((k : ℂ) * s)) *
          ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) * Qd.eval ((N : ℂ) ^ (-s)) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)

  have hA1' : ∀ w : ℂ, w ≠ 0 →
      w ^ (-m) * P.eval w * (1 - c * w ^ 2) = w ^ (-m₁) * P₁.eval w * Q.eval w := by
    have hL : IsLaurent (fun w : ℂ =>
        w ^ (-m) * P.eval w * (1 - c * w ^ 2) - w ^ (-m₁) * P₁.eval w * Q.eval w) :=
      (((IsLaurent.zpow (-m)).mul (IsLaurent.eval P)).mul
        ((IsLaurent.const 1).sub ((IsLaurent.const c).mul (IsLaurent.pow 2)))).sub
        (((IsLaurent.zpow (-m₁)).mul (IsLaurent.eval P₁)).mul (IsLaurent.eval Q))
    have hZ : {w : ℂ | w ≠ 0 ∧
        w ^ (-m) * P.eval w * (1 - c * w ^ 2) - w ^ (-m₁) * P₁.eval w * Q.eval w = 0}.Infinite := by
      refine (puncturedDisc_infinite ((N : ℝ) ^ (-σ)) (Real.rpow_pos_of_pos hNpos _)).mono fun w hw => ?_
      obtain ⟨hw0, hwR⟩ := hw
      refine ⟨hw0, ?_⟩
      obtain ⟨s, hs, hsw⟩ := exists_eq_natCast_cpow_neg N hN σ w hw0 hwR
      have h := hA1 s hs
      rw [zpow_form (N : ℂ) m s, zpow_form (N : ℂ) m₁ s, sq_form (N : ℂ) s, hsw] at h
      exact sub_eq_zero.2 h
    intro w hw
    exact sub_eq_zero.1 (IsLaurent.eq_zero_of_infinite hL hZ w hw)
  have hA2' : ∀ w : ℂ, w ≠ 0 →
      w ^ (-md) * Pd.eval w * (1 - c⁻¹ * (N : ℂ) ^ (-(2 : ℂ)) * w ^ 2) = w ^ (-m₂) * P₂.eval w * Qd.eval w := by
    have hL : IsLaurent (fun w : ℂ =>
        w ^ (-md) * Pd.eval w * (1 - c⁻¹ * (N : ℂ) ^ (-(2 : ℂ)) * w ^ 2) - w ^ (-m₂) * P₂.eval w * Qd.eval w) :=
      (((IsLaurent.zpow (-md)).mul (IsLaurent.eval Pd)).mul
        ((IsLaurent.const 1).sub ((IsLaurent.const (c⁻¹ * (N : ℂ) ^ (-(2 : ℂ)))).mul (IsLaurent.pow 2)))).sub
        (((IsLaurent.zpow (-m₂)).mul (IsLaurent.eval P₂)).mul (IsLaurent.eval Qd))
    have hZ : {w : ℂ | w ≠ 0 ∧
        w ^ (-md) * Pd.eval w * (1 - c⁻¹ * (N : ℂ) ^ (-(2 : ℂ)) * w ^ 2) - w ^ (-m₂) * P₂.eval w * Qd.eval w = 0}.Infinite := by
      refine (puncturedDisc_infinite ((N : ℝ) ^ (-σ')) (Real.rpow_pos_of_pos hNpos _)).mono fun w hw => ?_
      obtain ⟨hw0, hwR⟩ := hw
      refine ⟨hw0, ?_⟩
      obtain ⟨s, hs, hsw⟩ := exists_eq_natCast_cpow_neg N hN σ' w hw0 hwR
      have h := hA2 s hs
      rw [zpow_form (N : ℂ) md s, zpow_form (N : ℂ) m₂ s, sq_form (N : ℂ) s, hsw] at h
      exact sub_eq_zero.2 h
    intro w hw
    exact sub_eq_zero.1 (IsLaurent.eq_zero_of_infinite hL hZ w hw)

  have key : ∀ v : ℂ, v ≠ 0 →
      v ^ (-md) * Pd.eval v * Q.eval v⁻¹ - Γc * v ^ (-k) * (v ^ m * P.eval v⁻¹) * Qd.eval v = 0 := by
    have hL : IsLaurent (fun v : ℂ =>
        v ^ (-md) * Pd.eval v * Q.eval v⁻¹ - Γc * v ^ (-k) * (v ^ m * P.eval v⁻¹) * Qd.eval v) :=
      (((IsLaurent.zpow (-md)).mul (IsLaurent.eval Pd)).mul (IsLaurent.eval_inv Q)).sub
        ((((IsLaurent.const Γc).mul (IsLaurent.zpow (-k))).mul
          ((IsLaurent.zpow m).mul (IsLaurent.eval_inv P))).mul (IsLaurent.eval Qd))
    obtain ⟨Hp, hHp0, hHpev⟩ : ∃ Hp : Polynomial ℂ, Hp ≠ 0 ∧
        ∀ w : ℂ, Hp.eval w = (w ^ 2 - c) * (1 - c⁻¹ * (N : ℂ) ^ (-(2 : ℂ)) * w ^ 2) := by
      refine ⟨(Polynomial.X ^ 2 - Polynomial.C c) * (1 - Polynomial.C (c⁻¹ * (N : ℂ) ^ (-(2 : ℂ))) * Polynomial.X ^ 2),
        mul_ne_zero (Polynomial.X_pow_sub_C_ne_zero two_pos c) ?_, fun w => ?_⟩
      · intro h
        have := congr_arg (Polynomial.eval 0) h
        simp at this
      · simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_C, Polynomial.eval_one]
    have hZ : {v : ℂ | v ≠ 0 ∧
        v ^ (-md) * Pd.eval v * Q.eval v⁻¹ - Γc * v ^ (-k) * (v ^ m * P.eval v⁻¹) * Qd.eval v = 0}.Infinite := by
      refine (((puncturedDisc_infinite ((N : ℝ) ^ (-(0 : ℝ))) (Real.rpow_pos_of_pos hNpos _)).diff
        (Polynomial.finite_setOf_isRoot hHp0)).mono fun v hv => ?_)
      obtain ⟨⟨hv0, hvR⟩, hvroot⟩ := hv
      refine ⟨hv0, ?_⟩
      obtain ⟨s, -, hsv⟩ := exists_eq_natCast_cpow_neg N hN 0 v hv0 hvR
      have E2 := hA2' v hv0
      have EC := hcore s
      rw [zpow_form (N : ℂ) m₂ s, zpow_form (N : ℂ) k s, zpow_form' (N : ℂ) m₁ s, sq_form (N : ℂ) s,
        sq_form' (N : ℂ) s, inv_form (N : ℂ) s, hsv] at EC
      have E1 := hA1' v⁻¹ (inv_ne_zero hv0)
      simp only [inv_zpow', neg_neg] at E1
      have hprod : (v ^ (-md) * Pd.eval v * Q.eval v⁻¹ - Γc * v ^ (-k) * (v ^ m * P.eval v⁻¹) * Qd.eval v) *
          ((1 - c * v⁻¹ ^ 2) * (1 - c⁻¹ * (N : ℂ) ^ (-(2 : ℂ)) * v ^ 2)) = 0 := by
        linear_combination (Q.eval v⁻¹ * (1 - c * v⁻¹ ^ 2)) * E2 + (Q.eval v⁻¹ * Qd.eval v) * EC -
          (Γc * v ^ (-k) * Qd.eval v * (1 - c⁻¹ * (N : ℂ) ^ (-(2 : ℂ)) * v ^ 2)) * E1
      have hH : (1 - c * v⁻¹ ^ 2) * (1 - c⁻¹ * (N : ℂ) ^ (-(2 : ℂ)) * v ^ 2) ≠ 0 := by
        intro h0
        apply hvroot
        show Hp.IsRoot v
        have hD1 : (1 - c * v⁻¹ ^ 2) * v ^ 2 = v ^ 2 - c := by
          rw [inv_pow, sub_mul, one_mul, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hv0), mul_one]
        rw [Polynomial.IsRoot, hHpev, ← hD1]
        calc (1 - c * v⁻¹ ^ 2) * v ^ 2 * (1 - c⁻¹ * (N : ℂ) ^ (-(2 : ℂ)) * v ^ 2)
            = v ^ 2 * ((1 - c * v⁻¹ ^ 2) * (1 - c⁻¹ * (N : ℂ) ^ (-(2 : ℂ)) * v ^ 2)) := by ring
          _ = 0 := by rw [h0, mul_zero]
      exact (mul_eq_zero.1 hprod).resolve_right hH
    intro v hv
    exact IsLaurent.eq_zero_of_infinite hL hZ v hv

  intro s
  have hv0 : (N : ℂ) ^ (-s) ≠ 0 := natCast_cpow_ne_zero N (by omega) _
  have E := key ((N : ℂ) ^ (-s)) hv0
  rw [Polynomial.eval_one, Polynomial.eval_C, zpow_form (N : ℂ) md s, zpow_form' (N : ℂ) m s,
    zpow_form (N : ℂ) k s, inv_form (N : ℂ) s]
  linear_combination E

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)

    (Φ₂ : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂)

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (E : Fin 2 → ℂ) (e : Fin 2 → ℤ)
    (hfe0 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((μ 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((μ 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((μ 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((μ 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 0 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    (hfe1 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((μ 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((μ 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((μ 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((μ 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 1 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 → Qd ≠ 0 →

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  w₂ g * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →
            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g) *
                    (∫ u : p.adicCompletion ℚ × p.adicCompletion ℚ, Φ₂ u *
                      NumberField.StandardAddChar.psiLocal ℚ p
                        (u.1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)
                    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →

            (∀ s : ℂ, σ₂ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                (s + 1 / 2)
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p))
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  w₂ g * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →
            (∀ s : ℂ, σ₃ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                (s + 1 / 2)
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p))
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g) *
                    (∫ u : p.adicCompletion ℚ × p.adicCompletion ℚ, Φ₂ u *
                      NumberField.StandardAddChar.psiLocal ℚ p
                        (u.1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)
                    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ,
              ((1 : Polynomial ℂ)).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                  Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
                ((Polynomial.C ((((μ 0 (-1) : ℂˣ) : ℂ) * ((μ 1 (-1) : ℂˣ) : ℂ)) * (E 0 * E 1))).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-(e 0 + e 1) : ℤ) : ℂ) * s)) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by
  intro μ₂ _iμ₂ μN₂ _iμN₂ w₂ hw₂ P Pd Q Qd m md σ₂ σ₃ hQ hQd hint hintd hrat hratd

  obtain ⟨ϖ, hϖ⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer ℚ p
  have hϖ' : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) := hϖ
  have hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖ'; exact WithZero.zero_ne_coe hϖ'

  obtain ⟨m₁, P₁, σ₄, h₁⟩ :=
    LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral22_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
      p (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) (by simpa using hϖ')
      μ hμ σ hσ h01 φ hφ Φ₂ hΦ₂ θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral w₀p hw₀p wJ hwJ E e hfe0 hfe1 μ₂ μN₂ w₂ hw₂

  obtain ⟨m₂, P₂, σ₅, h₂⟩ :=
    LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral22_dual_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
      p hπ hϖ' μ hμ σ hσ h01 φ hφ Φ₂ hΦ₂ θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral w₀p hw₀p wJ hwJ E e hfe0 hfe1 μ₂ μN₂ w₂ hw₂

  have hcore := LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe
      p hπ hϖ' μ hμ σ hσ h01 φ hφ Φ₂ hΦ₂ θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral w₀p hw₀p wJ hwJ E e hfe0 hfe1 μ₂ μN₂ w₂ hw₂ P₁ P₂ m₁ m₂ σ₄ σ₅
      (fun s hs => by simpa only [Units.val_mk0] using (h₁ s hs).2) (fun s hs => (h₂ s hs).2)

  set c : ℂ := ((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) *
      ((μ 0 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) *
      ((μ 1 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) with hc_def
  have hc : c ≠ 0 := by
    rw [hc_def]
    exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (Units.ne_zero _)
  have hN1 : 1 < Ideal.absNorm p.asIdeal := by
    have h0 : Ideal.absNorm p.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot
    have h1' : Ideal.absNorm p.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact p.isPrime.ne_top
    omega
  have hA1 : ∀ s : ℂ, max σ₂ σ₄ < s.re →
      (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (1 - c * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ) * s)) =
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((m₁ : ℂ) * s) * P₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
    intro s hs
    have hs₂ : σ₂ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs₄ : σ₄ < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have e1 := hrat s hs₂
    have e2 := (h₁ s hs₄).2
    rw [← e1, ← e2]; ring
  have hA2 : ∀ s : ℂ, max σ₃ σ₅ < s.re →
      (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (1 - c⁻¹ * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ)) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ) * s)) =
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((m₂ : ℂ) * s) * P₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
    intro s hs
    have hs₃ : σ₃ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs₅ : σ₅ < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have e1 := hratd s hs₃
    have e2 := (h₂ s hs₅).2
    rw [← e1, ← e2]; ring
  have hglue := Delta2p.clearedFE_of_laurentFE_of_forall_lt_re (Ideal.absNorm p.asIdeal) hN1 c
      ((((μ 0 (-1) : ℂˣ) : ℂ) * ((μ 1 (-1) : ℂˣ) : ℂ)) * (E 0 * E 1)) hc (-(e 0 + e 1))
      P Pd Q Qd P₁ P₂ m md m₁ m₂ (max σ₂ σ₄) (max σ₃ σ₅)
      (by exact_mod_cast hA1) (by exact_mod_cast hA2) (by exact_mod_cast hcore)
  exact_mod_cast hglue

end S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_clearedFE_of_principalSeries2_of_forall_torusZeta_fe_ed2
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_clearedFE_of_principalSeries2_of_forall_torusZeta_fe_ed2 (solution)
