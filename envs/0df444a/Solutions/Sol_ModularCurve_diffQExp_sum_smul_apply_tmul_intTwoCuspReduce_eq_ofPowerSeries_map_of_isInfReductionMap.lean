-- Prove2me | solution 1 for ModularCurve.diffQExp_sum_smul_apply_tmul_intTwoCuspReduce_eq_ofPowerSeries_map_of_isInfReductionMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c2ab2c4b-2844-57e1-b20f-635be96b9f90

import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_diffQExp_sum_smul_apply_tmul_intTwoCuspReduce_eq_ofPowerSeries_map_of_isInfReductionMap

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

namespace Ws47
namespace LB

theorem one_mem_strictPeriods_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CohCarrier.GammaH M H)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  have hT := Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) (ModularCurve.translation_mem_GammaH M H)
  convert hT using 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.upperRightHom, ModularGroup.T] <;> rfl

theorem analyticAt_cuspFunction_one_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {k : ℤ}
    (f : CuspForm (CohCarrier.GammaH M H) k) : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ⇑f) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods_gammaH M H)

theorem qExpansion_coe_sum_smul (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {k : ℤ} {n : ℕ}
    (c : Fin n → ℂ) (f : Fin n → CuspForm (CohCarrier.GammaH M H) k) :
    UpperHalfPlane.qExpansion 1 (⇑(∑ i, c i • f i)) = ∑ i, c i • UpperHalfPlane.qExpansion 1 (⇑(f i)) := by
  classical
  induction n with
  | zero => simp [UpperHalfPlane.qExpansion_zero]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, CuspForm.coe_add,
      UpperHalfPlane.qExpansion_add (analyticAt_cuspFunction_one_gammaH M H _) (analyticAt_cuspFunction_one_gammaH M H _),
      ih (fun i => c i.castSucc) (fun i => f i.castSucc)]
    congr 1
    rw [show (⇑(c (Fin.last n) • f (Fin.last n)) : UpperHalfPlane → ℂ) = c (Fin.last n) • ⇑(f (Fin.last n)) from by ext z; rfl,
      UpperHalfPlane.qExpansion_smul (analyticAt_cuspFunction_one_gammaH M H _)]

theorem eq_sum_smul_map_of_map_eq_qExpansion_sum_smul (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {n : ℕ}
    (f : Fin n → CuspForm (CohCarrier.GammaH M H) 2) (pf : Fin n → PowerSeries ℤ)
    (hpf : ∀ i, ModularCurve.IsIntegralQExp (⇑(f i)) (pf i)) (a : Fin n → ↥(integralClosure ℤ ℂ))
    (pg : PowerSeries ↥(integralClosure ℤ ℂ))
    (hpg : pg.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 (⇑(∑ i, ((a i : ℂ)) • f i))) :
    pg = ∑ i, a i • (pf i).map (Int.castRingHom ↥(integralClosure ℤ ℂ)) := by
  have hinj : Function.Injective (PowerSeries.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ)) := fun P Q h => by
    ext m
    have := congrArg (PowerSeries.coeff m) h
    simp only [PowerSeries.coeff_map] at this
    exact this
  apply hinj
  rw [hpg, qExpansion_coe_sum_smul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← (hpf i)]
  ext m
  simp only [PowerSeries.coeff_map, map_smul, PowerSeries.coeff_smul, smul_eq_mul, Algebra.smul_def]
  simp

theorem eq_sum_C_mul_map_of_map_eq_qExpansion_sum_smul (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {n : ℕ}
    (f : Fin n → CuspForm (CohCarrier.GammaH M H) 2) (pf : Fin n → PowerSeries ℤ)
    (hpf : ∀ i, ModularCurve.IsIntegralQExp (⇑(f i)) (pf i)) (a : Fin n → ↥(integralClosure ℤ ℂ))
    (pg : PowerSeries ↥(integralClosure ℤ ℂ))
    (hpg : pg.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 (⇑(∑ i, ((a i : ℂ)) • f i))) :
    pg = ∑ i, PowerSeries.C (a i) * (pf i).map (Int.castRingHom ↥(integralClosure ℤ ℂ)) := by
  rw [eq_sum_smul_map_of_map_eq_qExpansion_sum_smul M H f pf hpf a pg hpg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PowerSeries.smul_eq_C_mul]

theorem ofPowerSeries_map_sum_smul (K : Type*) [Field K] {n : ℕ} (φ : ↥(integralClosure ℤ ℂ) →+* K)
    (a : Fin n → ↥(integralClosure ℤ ℂ)) (pf : Fin n → PowerSeries ℤ) :
    HahnSeries.ofPowerSeries ℤ K ((∑ i, a i • (pf i).map (Int.castRingHom ↥(integralClosure ℤ ℂ))).map φ) =
      ∑ i, φ (a i) • ModularCurve.intSeriesC K (pf i) := by
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmm : PowerSeries.map φ (PowerSeries.map (Int.castRingHom ↥(integralClosure ℤ ℂ)) (pf i)) =
      PowerSeries.map (Int.castRingHom K) (pf i) := by
    ext m; simp [PowerSeries.coeff_map]
  rw [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, hmm, map_mul, HahnSeries.ofPowerSeries_C,
    HahnSeries.C_mul_eq_smul]
  rfl

end Ws47.LB

namespace Ws47
namespace LB

noncomputable def atkinLehnerDatum_of_not_sq_dvd (p M : ℕ) [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) :
    ModularForm.AtkinLehnerDatum M p where
  R := M / p
  hM := (Nat.mul_div_cancel' hpM).symm
  a := Nat.gcdA p (M / p)
  b := - Nat.gcdB p (M / p)
  bezout := by
    have hcop : Nat.Coprime p (M / p) := by
      refine (Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr ?_
      intro h; apply hpM2
      obtain ⟨k, hk⟩ := h
      exact ⟨k, by rw [pow_two, mul_assoc, ← hk, Nat.mul_div_cancel' hpM]⟩
    have h := Nat.gcd_eq_gcd_ab p (M / p)
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.cast_one] at h
    linear_combination -h

theorem exists_isIntegralQExp
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (g : CuspForm (CohCarrier.GammaH M H) 2) (hg : g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    ∃ pg : PowerSeries ℤ, ModularCurve.IsIntegralQExp (⇑g) pg := by
  classical
  have hc : ∀ n, ModularFormClass.qCoeff (⇑g) n ∈ (⊥ : Subring ℂ) := fun n =>
    (hg 1 (CuspForm.heckeRingH M H 2).one_mem (atkinLehnerDatum_of_not_sq_dvd p M hpM hpM2) n).1
  have hc' : ∀ n, ∃ z : ℤ, (z : ℂ) = ModularFormClass.qCoeff (⇑g) n := fun n => by
    obtain ⟨z, hz⟩ := Subring.mem_bot.mp (hc n)
    exact ⟨z, hz⟩
  choose z hz using hc'
  refine ⟨PowerSeries.mk z, ?_⟩
  show (PowerSeries.mk z).map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑g
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast, hz]
  rfl

end Ws47.LB

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (K : Type*) [Field K] [CharP K p] [Algebra (ZMod p) K]
    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (φ : ↥(integralClosure ℤ ℂ) →+* K)
    {n : ℕ} (a : Fin n → ↥(integralClosure ℤ ℂ)) (f : Fin n → CuspForm (CohCarrier.GammaH M H) 2)
    (hf : ∀ i, f i ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pg : PowerSeries ↥(integralClosure ℤ ℂ))
    (hpg : pg.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 (⇑(∑ i, ((a i : ℂ)) • f i))) :
    ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
        (∑ i, φ (a i) • ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
          ⟨f i, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ (hf i)⟩)) =
      HahnSeries.ofPowerSeries ℤ K (pg.map φ) := by
  classical

  have hex : ∀ i, ∃ pf : PowerSeries ℤ, ModularCurve.IsIntegralQExp (⇑(f i)) pf := fun i =>
    Ws47.LB.exists_isIntegralQExp p M H hpM hpM2 (f i) (hf i)
  choose pf hpf using hex
  have hread : ∀ i, ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
      (ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
        ⟨f i, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ (hf i)⟩)) = ModularCurve.intSeriesC K (pf i) :=
    fun i => hρinf (f i) (hf i) (pf i) (hpf i)

  rw [map_sum]
  simp_rw [LinearMap.map_smul_of_tower, hread]

  rw [Ws47.LB.eq_sum_smul_map_of_map_eq_qExpansion_sum_smul M H f pf hpf a pg hpg,
    Ws47.LB.ofPowerSeries_map_sum_smul K φ a pf]

end S_ModularCurve_diffQExp_sum_smul_apply_tmul_intTwoCuspReduce_eq_ofPowerSeries_map_of_isInfReductionMap
end P2MW
export P2MW.S_ModularCurve_diffQExp_sum_smul_apply_tmul_intTwoCuspReduce_eq_ofPowerSeries_map_of_isInfReductionMap (solution)
