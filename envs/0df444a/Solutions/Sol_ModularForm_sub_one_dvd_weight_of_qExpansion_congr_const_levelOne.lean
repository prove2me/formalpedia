-- Prove2me | solution 1 for ModularForm.sub_one_dvd_weight_of_qExpansion_congr_const_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6eda34ed-d2f4-5df4-8e1b-a7890f8850da

import Theorems.Thm_EisensteinSeries_ramanujan_system_qExpansion_int
import Theorems.Thm_ModularForm_exists_isWeightedHomogeneous_aeval_eq_map_qExpansion_levelOne
import Theorems.Thm_MvPolynomial_squarefree_of_isWeightedHomogeneous_of_aeval_eq_one
import Theorems.Thm_MvPolynomial_ker_aeval_eq_span_sub_one_of_squarefree_of_isWeightedHomogeneous
import Theorems.Thm_ModularCurve_StarBank_eisInt_series
import Theorems.Thm_ModularCurve_StarBank_eisInt_not_dvd_num
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_sub_one_dvd_weight_of_qExpansion_congr_const_levelOne
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

open scoped MatrixGroups

namespace ModularForm
p2m_export "ModularForm" "mk IsGLPos.coe_smul coe_smul E ext E₄ E₆ exists_isWeightedHomogeneous_aeval_eq_map_qExpansion_levelOne"
namespace WeightCongruenceProof
p2m_open "ModularForm"

open MvPolynomial

section Graded

variable {K : Type*} [CommRing K]

lemma isWeightedHomogeneous_zmod_of_nat {m : ℕ} {φ : MvPolynomial (Fin 2) K} {n : ℕ}
    (h : φ.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) n) :
    φ.IsWeightedHomogeneous (fun i => (((![4, 6] : Fin 2 → ℕ) i : ℕ) : ZMod m)) (n : ZMod m) := by
  intro d hd
  have h1 := h hd
  rw [Finsupp.weight_apply] at h1 ⊢
  rw [← h1, Finsupp.sum, Finsupp.sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [nsmul_eq_mul]

lemma weightedHomogeneousComponent_zero_mul {M : Type*} [AddCommMonoid M] [DecidableEq M]
    (w : Fin 2 → M) {B : MvPolynomial (Fin 2) K} (hB : B.IsWeightedHomogeneous w 0)
    (Ψ : MvPolynomial (Fin 2) K) :
    weightedHomogeneousComponent w 0 (B * Ψ) = B * weightedHomogeneousComponent w 0 Ψ := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hd
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases hBp : coeff p.1 B = 0
    · simp [hBp]
    · have hp1 : Finsupp.weight w p.1 = 0 := hB hBp
      have hsum : p.1 + p.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hp2 : Finsupp.weight w p.2 = 0 := by
        have := congrArg (Finsupp.weight w) hsum
        rw [map_add, hp1, zero_add, hd] at this
        exact this
      rw [if_pos hp2]
  · symm
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases hBp : coeff p.1 B = 0
    · simp [hBp]
    · have hp1 : Finsupp.weight w p.1 = 0 := hB hBp
      have hsum : p.1 + p.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hp2 : Finsupp.weight w p.2 ≠ 0 := by
        intro hp2
        have := congrArg (Finsupp.weight w) hsum
        rw [map_add, hp1, zero_add, hp2] at this
        exact hd this.symm
      rw [if_neg hp2, mul_zero]

end Graded

noncomputable def PZ : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -24 * ∑ d ∈ n.divisors, (d : ℤ)

noncomputable def QZ : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3

noncomputable def RZ : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5

lemma map_X_mul_derivative {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (F : PowerSeries R) :
    PowerSeries.map φ (PowerSeries.X * PowerSeries.derivative R F) =
      PowerSeries.X * PowerSeries.derivative S (PowerSeries.map φ F) := by
  ext n
  cases n with
  | zero => simp [PowerSeries.coeff_zero_X_mul]
  | succ n =>
    simp [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_map]

lemma coeff_one_QZ_cube_sub_RZ_sq : PowerSeries.coeff 1 (QZ ^ 3 - RZ ^ 2) = 1728 := by
  have hQ0 : PowerSeries.constantCoeff QZ = 1 := by simp [QZ]
  have hR0 : PowerSeries.constantCoeff RZ = 1 := by simp [RZ]
  have hQ1 : PowerSeries.coeff 1 QZ = 240 := by simp [QZ, PowerSeries.coeff_mk]
  have hR1 : PowerSeries.coeff 1 RZ = -504 := by simp [RZ, PowerSeries.coeff_mk]
  rw [map_sub, PowerSeries.coeff_one_pow, PowerSeries.coeff_one_pow, hQ0, hR0, hQ1, hR1]
  norm_num

theorem main {ℓ : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) {k : ℤ} (f : ModularForm 𝒮ℒ k)
    {T : PowerSeries ℤ} (hT : T.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑f)
    (hdvd : ∀ n : ℕ, 1 ≤ n → (ℓ : ℤ) ∣ T.coeff n)
    (h0 : ¬ (ℓ : ℤ) ∣ PowerSeries.constantCoeff T) :
    ((ℓ - 1 : ℕ) : ℤ) ∣ k := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩

  set red : PowerSeries ℤ →+* PowerSeries (ZMod ℓ) := PowerSeries.map (Int.castRingHom (ZMod ℓ))
    with hred
  set v : Fin 2 → PowerSeries (ZMod ℓ) := ![red QZ, red RZ] with hv
  set ε := MvPolynomial.aeval (R := ZMod ℓ) v with hε
  set c : ZMod ℓ := ((PowerSeries.constantCoeff T : ℤ) : ZMod ℓ) with hc_def
  have hc : c ≠ 0 := by
    rwa [hc_def, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

  have hk0 : 0 ≤ k := by
    by_contra hk
    push Not at hk
    have hf0 : (⇑f : UpperHalfPlane → ℂ) = 0 := ModularFormClass.levelOne_neg_weight_eq_zero hk f
    have h1 : PowerSeries.constantCoeff (T.map (Int.castRingHom ℂ)) = 0 := by
      rw [hT, hf0, UpperHalfPlane.qExpansion_zero]; simp
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, eq_intCast, Int.cast_eq_zero] at h1
    exact h0 (h1 ▸ dvd_zero _)

  have hTred : red T = PowerSeries.C c := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hred, hc_def, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    · rw [hred, PowerSeries.coeff_map, PowerSeries.coeff_C, if_neg hn.ne', eq_intCast,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).2 (hdvd n hn)]
  obtain ⟨Φ, hΦh, hΦ⟩ :=
    ModularForm.exists_isWeightedHomogeneous_aeval_eq_map_qExpansion_levelOne hℓ h5 f hT
  change ε Φ = red T at hΦ
  rw [hTred] at hΦ

  have hk3 : 3 ≤ ℓ - 1 := by omega
  obtain ⟨TA, hTA, hTA0, hTAdvd⟩ := ModularCurve.StarBank.eisInt_series (ℓ := ℓ) h5 hk3
  have hnum : ¬ (ℓ : ℤ) ∣ (bernoulli (ℓ - 1)).num := ModularCurve.StarBank.eisInt_not_dvd_num h5
  have hTA' : TA.map (Int.castRingHom ℂ) =
      UpperHalfPlane.qExpansion 1 ⇑(((bernoulli (ℓ - 1)).num : ℂ) • ModularForm.E hk3) := by
    rw [hTA, IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
  obtain ⟨ΦA, hΦAh, hΦA⟩ :=
    ModularForm.exists_isWeightedHomogeneous_aeval_eq_map_qExpansion_levelOne hℓ h5 _ hTA'
  change ε ΦA = red TA at hΦA
  set a : ZMod ℓ := (((bernoulli (ℓ - 1)).num : ℤ) : ZMod ℓ) with ha_def
  have ha : a ≠ 0 := by rwa [ha_def, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hTAred : red TA = PowerSeries.C a := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hred, ha_def, PowerSeries.coeff_zero_eq_constantCoeff_apply, hTA0]
    · rw [hred, PowerSeries.coeff_map, PowerSeries.coeff_C, if_neg hn.ne', eq_intCast,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).2 (hTAdvd n hn)]
  rw [hTAred] at hΦA
  have htoNat : (((ℓ - 1 : ℕ) : ℤ)).toNat = ℓ - 1 := Int.toNat_natCast _
  rw [htoNat] at hΦAh
  set A : MvPolynomial (Fin 2) (ZMod ℓ) := MvPolynomial.C a⁻¹ * ΦA with hA_def
  have hAh : A.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) (ℓ - 1) := by
    rw [hA_def]
    exact hΦAh.C_mul _
  have hA1 : ε A = 1 := by
    rw [hA_def, map_mul, hΦA, MvPolynomial.algHom_C, PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self_apply, ← map_mul, inv_mul_cancel₀ ha, map_one]

  obtain ⟨hRP, hRQ, hRR⟩ := EisensteinSeries.ramanujan_system_qExpansion_int PZ QZ RZ rfl rfl rfl
  have hP' : 12 * (PowerSeries.X * PowerSeries.derivative (ZMod ℓ) (red PZ)) =
      red PZ ^ 2 - red QZ := by
    have := congrArg red hRP
    simpa [hred, map_X_mul_derivative, map_ofNat] using this
  have hQ' : 3 * (PowerSeries.X * PowerSeries.derivative (ZMod ℓ) (red QZ)) =
      red PZ * red QZ - red RZ := by
    have := congrArg red hRQ
    simpa [hred, map_X_mul_derivative, map_ofNat] using this
  have hR' : 2 * (PowerSeries.X * PowerSeries.derivative (ZMod ℓ) (red RZ)) =
      red PZ * red RZ - red QZ ^ 2 := by
    have := congrArg red hRR
    simpa [hred, map_X_mul_derivative, map_ofNat] using this
  have hP0 : PowerSeries.constantCoeff (red PZ) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hred, PowerSeries.coeff_map, PZ,
      PowerSeries.coeff_mk]; simp
  have hQ0 : PowerSeries.constantCoeff (red QZ) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hred, PowerSeries.coeff_map, QZ,
      PowerSeries.coeff_mk]; simp
  have hR0 : PowerSeries.constantCoeff (red RZ) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hred, PowerSeries.coeff_map, RZ,
      PowerSeries.coeff_mk]; simp
  have h1728 : (1728 : ZMod ℓ) ≠ 0 := by
    intro h
    have h' : ((1728 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have h23 : ℓ ∣ 2 ^ 6 * 3 ^ 3 := by norm_num; exact h'
    rcases (Nat.Prime.dvd_mul hℓ).1 h23 with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hℓ.dvd_of_dvd_pow h2); omega
    · have := Nat.le_of_dvd (by norm_num) (hℓ.dvd_of_dvd_pow h3); omega
  have hQR : red QZ ^ 3 ≠ red RZ ^ 2 := by
    intro h
    have h1 : PowerSeries.coeff 1 (red (QZ ^ 3 - RZ ^ 2)) = 0 := by
      rw [map_sub, map_pow, map_pow, h, sub_self, map_zero]
    rw [hred, PowerSeries.coeff_map, coeff_one_QZ_cube_sub_RZ_sq, eq_intCast] at h1
    exact h1728 (by exact_mod_cast h1)

  have hsq : Squarefree A :=
    MvPolynomial.squarefree_of_isWeightedHomogeneous_of_aeval_eq_one (K := ZMod ℓ) (ℓ := ℓ) h5
      hP0 hQ0 hR0 hQR hP' hQ' hR' hAh hA1
  have hN : 0 < ℓ - 1 := by omega
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (ZMod ℓ) (ℓ - 1)
  have hker : RingHom.ker ε.toRingHom = Ideal.span {A - 1} :=
    MvPolynomial.ker_aeval_eq_span_sub_one_of_squarefree_of_isWeightedHomogeneous hN hζ
      hQ0 hR0 hQR hAh hsq hA1

  have hmem : Φ - MvPolynomial.C c ∈ Ideal.span {A - 1} := by
    rw [← hker, RingHom.mem_ker]
    change ε (Φ - MvPolynomial.C c) = 0
    rw [map_sub, hΦ, MvPolynomial.algHom_C, PowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply,
      sub_self]
  obtain ⟨Ψ, hΨ⟩ := Ideal.mem_span_singleton'.1 hmem

  set w' : Fin 2 → ZMod (ℓ - 1) := fun i => (((![4, 6] : Fin 2 → ℕ) i : ℕ) : ZMod (ℓ - 1))
    with hw'
  have hAw' : (A - 1).IsWeightedHomogeneous w' 0 := by
    have h1 : A.IsWeightedHomogeneous w' ((ℓ - 1 : ℕ) : ZMod (ℓ - 1)) :=
      isWeightedHomogeneous_zmod_of_nat hAh
    rw [ZMod.natCast_self] at h1
    have h2 : (1 : MvPolynomial (Fin 2) (ZMod ℓ)).IsWeightedHomogeneous w' 0 :=
      isWeightedHomogeneous_one _ _
    exact (weightedHomogeneousSubmodule (ZMod ℓ) w' 0).sub_mem h1 h2
  have hΦw' : Φ.IsWeightedHomogeneous w' ((k.toNat : ℕ) : ZMod (ℓ - 1)) :=
    isWeightedHomogeneous_zmod_of_nat hΦh

  suffices hdiv : (ℓ - 1) ∣ k.toNat by
    have : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0
    rw [← this]
    exact_mod_cast hdiv
  by_contra hndvd
  haveI : NeZero (ℓ - 1) := ⟨by omega⟩
  have hkne : ((k.toNat : ℕ) : ZMod (ℓ - 1)) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hcomp := congrArg (weightedHomogeneousComponent w' 0) hΨ
  rw [mul_comm, weightedHomogeneousComponent_zero_mul w' hAw', map_sub,
    hΦw'.weightedHomogeneousComponent_ne 0 hkne.symm,
    (isWeightedHomogeneous_C w' c).weightedHomogeneousComponent_same, zero_sub] at hcomp

  have heval := congrArg ε hcomp
  rw [map_mul, map_sub, hA1, map_one, sub_self, zero_mul, map_neg, MvPolynomial.algHom_C,
    PowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply] at heval
  have : PowerSeries.constantCoeff (-(PowerSeries.C c) : PowerSeries (ZMod ℓ)) = 0 := by
    rw [← heval]; simp
  simp at this
  exact hc this

end ModularForm.WeightCongruenceProof

theorem solution {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) {k : ℤ} (f : ModularForm 𝒮ℒ k) {T : PowerSeries ℤ}
    (hT : T.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑f)
    (hdvd : ∀ n : ℕ, 1 ≤ n → (ℓ : ℤ) ∣ T.coeff n)
    (h0 : ¬ (ℓ : ℤ) ∣ PowerSeries.constantCoeff T) :
    ((ℓ - 1 : ℕ) : ℤ) ∣ k :=
  ModularForm.WeightCongruenceProof.main hℓ h5 f hT hdvd h0

end S_ModularForm_sub_one_dvd_weight_of_qExpansion_congr_const_levelOne
end P2MW
export P2MW.S_ModularForm_sub_one_dvd_weight_of_qExpansion_congr_const_levelOne (solution)
