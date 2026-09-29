-- Prove2me | solution 1 for ModularCurve.qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/20de4268-38fd-5141-98e0-ce98cadab83f

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_CuspForm_ModPForms
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_modularFunctionFieldC_algHom_ext
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_kaehlerRankOne_modularFunctionFieldC_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_isQExpansionDiffAlong_qExpansionDiffAlong
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_smul_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 8000000

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map.ModularCurve AlgebraicCurve IntermediateField"

namespace ModularCurve
p2m_export "ModularCurve" "charLDegeneracyRoof modularFunctionFieldC_le_charLDegeneracyRoof heckeAlphaC coe_heckeAlphaC heckeBetaC coe_heckeBetaC jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_C qExpand_one_apply qExpand_congr qExpand_qExpand dedekindPsi thetaL thetaL_apply qExpansionDiffAlong modularFunctionFieldFullC jqModCd_mem_full jqModC_mem_full coeff_jqModC_neg_one qTwist qTwist_coeff qTwist_single qTwist_one_apply qTwist_qExpand jGeomGen thetaJ qexpOfWeight theta_coeff charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul modularFunctionFieldC_eq_modularFunctionFieldFullC finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi dedekindPsi_mul_of_coprime dedekindPsi_prime dedekindPsi_pos exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd modularFunctionFieldC_algHom_ext isSeparable_jqNModC_of_natCast_ne_zero kaehlerRankOne_modularFunctionFieldC_of_isSeparable_jqNModC isQExpansionDiffAlong_qExpansionDiffAlong qExpansionDiffAlong_smul_map"
namespace CharQHeckeDiff
p2m_open "ModularCurve"

section Laurent

variable {K : Type*} [Field K]

theorem thetaL_coeff (f : LaurentSeries K) (n : ℤ) :
    (thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [thetaL_apply, theta_coeff, zsmul_eq_mul]

theorem thetaL_qExpand (m : ℕ) [NeZero m] (x : LaurentSeries K) :
    thetaL K (qExpand K m x) = (m : K) • qExpand K m (thetaL K x) := by
  ext n
  rw [thetaL_coeff, HahnSeries.coeff_smul, smul_eq_mul]
  by_cases hn : (m : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hn
    rw [qExpand_coeff_mul, qExpand_coeff_mul, thetaL_coeff]
    push_cast
    ring
  · rw [qExpand_coeff_of_not_dvd m _ hn, qExpand_coeff_of_not_dvd m _ hn, mul_zero, mul_zero]

theorem qTwist_qExpand_of_pow_eq_one (m : ℕ) [NeZero m] {u : Kˣ} (hu : u ^ m = 1)
    (x : LaurentSeries K) : qTwist u (qExpand K m x) = qExpand K m x := by
  rw [qTwist_qExpand, zpow_natCast, hu, qTwist_one_apply]

theorem sum_qTwist_coeff (ℓ : ℕ) [Fact ℓ.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (x : LaurentSeries K) (k : ℤ) :
    (∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) x).coeff k =
      if (ℓ : ℤ) ∣ k then (ℓ : K) * x.coeff k else 0 := by
  have hcoeff : (∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) x).coeff k =
      (∑ b ∈ Finset.range ℓ, (((ζ : Kˣ) ^ k : Kˣ) : K) ^ b) * x.coeff k := by
    rw [HahnSeries.coeff_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [qTwist_coeff]
    congr 1
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      mul_comm]
  rw [hcoeff]
  have hζu : IsPrimitiveRoot ζ ℓ := (IsPrimitiveRoot.coe_units_iff).mp hζ
  by_cases hk : (ℓ : ℤ) ∣ k
  · rw [if_pos hk]
    obtain ⟨m, rfl⟩ := hk
    have h1 : ((ζ ^ ((ℓ : ℤ) * m) : Kˣ) : K) = 1 := by
      rw [zpow_mul, zpow_natCast, hζu.pow_eq_one, one_zpow, Units.val_one]
    rw [h1]
    simp
  · rw [if_neg hk]
    have hne : ((ζ ^ k : Kˣ) : K) ≠ 1 := by
      intro h1
      apply hk
      have h2 : (ζ : Kˣ) ^ k = 1 := Units.val_eq_one.mp h1
      exact (hζu.zpow_eq_one_iff_dvd k).mp h2
    have hgeom : (∑ b ∈ Finset.range ℓ, (((ζ : Kˣ) ^ k : Kˣ) : K) ^ b) = 0 := by
      have hmul := geom_sum_mul (((ζ ^ k : Kˣ) : K)) ℓ
      have hpow : (((ζ ^ k : Kˣ) : K)) ^ ℓ = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
          zpow_natCast, hζu.pow_eq_one, one_zpow, Units.val_one]
      rw [hpow, sub_self] at hmul
      exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hne)
    rw [hgeom, zero_mul]

theorem natCast_ne_zero_of_isPrimitiveRoot (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) ℓ) : (ℓ : K) ≠ 0 := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  exact (hζ.neZero' (n := ℓ)).out

end Laurent

section Degrees

variable (K : Type*) [Field K]

abbrev A0 : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))

theorem finrank_adjoin_mk_eq_relfinrank (X : IntermediateField K (LaurentSeries K))
    (x : LaurentSeries K) (hx : x ∈ X) :
    Module.finrank (IntermediateField.adjoin K ({(⟨x, hx⟩ : ↥X)} : Set ↥X)) X =
      IntermediateField.relfinrank (IntermediateField.adjoin K ({x} : Set (LaurentSeries K))) X := by
  have hle : IntermediateField.adjoin K ({x} : Set (LaurentSeries K)) ≤ X :=
    adjoin_simple_le_iff.mpr hx
  rw [relfinrank_eq_finrank_of_le hle]
  set A' : IntermediateField K ↥X := IntermediateField.adjoin K ({(⟨x, hx⟩ : ↥X)} : Set ↥X)
  have hlift : lift A' = IntermediateField.adjoin K ({x} : Set (LaurentSeries K)) :=
    IntermediateField.lift_adjoin_simple K X ⟨x, hx⟩
  let i : A' ≃+* IntermediateField.adjoin K ({x} : Set (LaurentSeries K)) :=
    ((liftAlgEquiv A').trans (equivOfEq hlift)).toRingEquiv
  let jj : X ≃+* extendScalars hle :=
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  refine Algebra.finrank_eq_of_equiv_equiv i jj ?_
  refine RingHom.ext fun a => Subtype.ext ?_
  rfl

theorem relfinrank_A0_fullC (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    IntermediateField.relfinrank (A0 K) (modularFunctionFieldFullC K M) = dedekindPsi M := by
  rw [← finrank_adjoin_mk_eq_relfinrank K (modularFunctionFieldFullC K M) (jqModC K)
    (jqModC_mem_full K M)]
  exact finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K M hM

variable (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime]

theorem not_ringChar_dvd (M : ℕ) (hM : (M : K) ≠ 0) : ¬ ringChar K ∣ M := fun h =>
  hM ((ringChar.spec K M).mpr h)

theorem modularFunctionFieldC_eq_fullC (hN : (N : K) ≠ 0) :
    modularFunctionFieldC K N = modularFunctionFieldFullC K N :=
  haveI : CharP K (ringChar K) := ringChar.charP K
  modularFunctionFieldC_eq_modularFunctionFieldFullC K (ringChar K) N (not_ringChar_dvd K N hN)

theorem roof_eq_fullC (hN : (N : K) ≠ 0) (hℓK : (ℓ : K) ≠ 0) :
    charLDegeneracyRoof K N ℓ = modularFunctionFieldFullC K (N * ℓ) := by
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩
  refine charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul K (ringChar K) N ℓ ?_
  apply not_ringChar_dvd K (N * ℓ)
  push_cast
  exact mul_ne_zero hN hℓK

theorem A0_le : A0 K ≤ modularFunctionFieldC K N :=
  adjoin_simple_le_iff.mpr (jqModC_mem K N)

theorem relfinrank_roof (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (hℓK : (ℓ : K) ≠ 0) :
    IntermediateField.relfinrank (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) = ℓ + 1 := by
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩
  have h1 : IntermediateField.relfinrank (A0 K) (modularFunctionFieldC K N) = dedekindPsi N := by
    rw [modularFunctionFieldC_eq_fullC K N hN]; exact relfinrank_A0_fullC K N hN
  have h2 : IntermediateField.relfinrank (A0 K) (charLDegeneracyRoof K N ℓ) = dedekindPsi (N * ℓ) := by
    rw [roof_eq_fullC K N ℓ hN hℓK]
    refine relfinrank_A0_fullC K (N * ℓ) ?_
    push_cast; exact mul_ne_zero hN hℓK
  have hmul := relfinrank_mul_relfinrank (A0_le K N)
    (modularFunctionFieldC_le_charLDegeneracyRoof K N ℓ)
  rw [h1, h2, dedekindPsi_mul_of_coprime N ℓ
    ((Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ.out).mpr hℓN))),
    dedekindPsi_prime hℓ.out] at hmul
  exact Nat.eq_of_mul_eq_mul_left (dedekindPsi_pos N (NeZero.ne N)) hmul

theorem finrank_along_alpha (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (hℓK : (ℓ : K) ≠ 0) :
    letI := algebraAlong (heckeAlphaC K N ℓ)
    Module.finrank (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) = ℓ + 1 := by
  letI := algebraAlong (heckeAlphaC K N ℓ)
  letI : Module (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) := Algebra.toModule
  rw [← relfinrank_roof K N ℓ hN hℓN hℓK,
    relfinrank_eq_finrank_of_le (modularFunctionFieldC_le_charLDegeneracyRoof K N ℓ)]
  symm
  let jj : extendScalars (modularFunctionFieldC_le_charLDegeneracyRoof K N ℓ) ≃+*
      charLDegeneracyRoof K N ℓ :=
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  refine Algebra.finrank_eq_of_equiv_equiv (R₀ := modularFunctionFieldC K N)
    (S₀ := extendScalars (modularFunctionFieldC_le_charLDegeneracyRoof K N ℓ))
    (R₁ := modularFunctionFieldC K N) (S₁ := charLDegeneracyRoof K N ℓ) (RingEquiv.refl _) jj ?_
  refine RingHom.ext fun a => Subtype.ext ?_
  rfl

end Degrees

section AtkinLehner

variable (K : Type*) [Field K] (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime]

abbrev jF : modularFunctionFieldC K N := ⟨jqModC K, jqModC_mem K N⟩
abbrev jNF : modularFunctionFieldC K N := ⟨jqNModC K N, jqNModC_mem K N⟩

theorem exists_atkinLehner (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (hℓK : (ℓ : K) ≠ 0) :
    ∃ w : charLDegeneracyRoof K N ℓ ≃ₐ[K] charLDegeneracyRoof K N ℓ,
      (∀ f, w (heckeAlphaC K N ℓ f) = heckeBetaC K N ℓ f) ∧
      (∀ f, w (heckeBetaC K N ℓ f) = heckeAlphaC K N ℓ f) := by
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩
  obtain ⟨σ, hσ⟩ := exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd K N ℓ hℓ.out hℓN hN hℓK
  let e : charLDegeneracyRoof K N ℓ ≃ₐ[K] modularFunctionFieldFullC K (N * ℓ) :=
    equivOfEq (roof_eq_fullC K N ℓ hN hℓK)
  let w : charLDegeneracyRoof K N ℓ ≃ₐ[K] charLDegeneracyRoof K N ℓ := e.trans (σ.trans e.symm)
  have hval_e : ∀ x, (e x : LaurentSeries K) = x := fun _ => rfl
  have hval_esymm : ∀ y, (e.symm y : LaurentSeries K) = y := fun _ => rfl
  have h1 := (hσ 1 inferInstance (one_dvd N))
  have hNd := (hσ N inferInstance dvd_rfl)

  have hσj : (σ ⟨jqModC K, jqModC_mem_full K (N * ℓ)⟩ : LaurentSeries K) = qExpand K ℓ (jqModC K) := by
    have hx : (⟨jqModC K, jqModC_mem_full K (N * ℓ)⟩ : modularFunctionFieldFullC K (N * ℓ)) =
        ⟨qExpand K 1 (jqModC K), jqModCd_mem_full K (N * ℓ) (Dvd.dvd.mul_right (one_dvd N) ℓ)⟩ :=
      Subtype.ext (qExpand_one_apply _).symm
    rw [hx, h1.1]
    exact qExpand_congr (one_mul ℓ) _
  have hmemjℓ : qExpand K ℓ (jqModC K) ∈ modularFunctionFieldFullC K (N * ℓ) :=
    jqModCd_mem_full K (N * ℓ) (Dvd.intro_left N rfl)
  have hmemjN : jqNModC K N ∈ modularFunctionFieldFullC K (N * ℓ) :=
    jqModCd_mem_full K (N * ℓ) (Dvd.intro ℓ rfl)
  have hqq : qExpand K ℓ (jqNModC K N) = qExpand K (N * ℓ) (jqModC K) := by
    show qExpand K ℓ (qExpand K N (jqModC K)) = qExpand K (N * ℓ) (jqModC K)
    rw [qExpand_qExpand, qExpand_congr (mul_comm ℓ N)]
  have hmemjNℓ : qExpand K ℓ (jqNModC K N) ∈ modularFunctionFieldFullC K (N * ℓ) := by
    rw [hqq]; exact jqModCd_mem_full K (N * ℓ) dvd_rfl
  have hσjℓ : (σ ⟨qExpand K ℓ (jqModC K), hmemjℓ⟩ : LaurentSeries K) = jqModC K := by
    have hx : (⟨qExpand K ℓ (jqModC K), hmemjℓ⟩ : modularFunctionFieldFullC K (N * ℓ)) =
        ⟨qExpand K (1 * ℓ) (jqModC K), jqModCd_mem_full K (N * ℓ) (Nat.mul_dvd_mul_right (one_dvd N) ℓ)⟩ :=
      Subtype.ext (qExpand_congr (one_mul ℓ).symm _)
    rw [hx, h1.2]
    exact qExpand_one_apply _
  have hσjN : (σ ⟨jqNModC K N, hmemjN⟩ : LaurentSeries K) = qExpand K ℓ (jqNModC K N) := by
    have hx : (⟨jqNModC K N, hmemjN⟩ : modularFunctionFieldFullC K (N * ℓ)) =
        ⟨qExpand K N (jqModC K), jqModCd_mem_full K (N * ℓ) (Dvd.dvd.mul_right (dvd_refl N) ℓ)⟩ :=
      Subtype.ext rfl
    rw [hx, hNd.1, hqq]
  have hσjNℓ : (σ ⟨qExpand K ℓ (jqNModC K N), hmemjNℓ⟩ : LaurentSeries K) = jqNModC K N := by
    have hx : (⟨qExpand K ℓ (jqNModC K N), hmemjNℓ⟩ : modularFunctionFieldFullC K (N * ℓ)) =
        ⟨qExpand K (N * ℓ) (jqModC K), jqModCd_mem_full K (N * ℓ) (Nat.mul_dvd_mul_right (dvd_refl N) ℓ)⟩ :=
      Subtype.ext hqq
    rw [hx, hNd.2]
    rfl
  refine ⟨w, ?_, ?_⟩
  · have key : (w : charLDegeneracyRoof K N ℓ →ₐ[K] charLDegeneracyRoof K N ℓ).comp (heckeAlphaC K N ℓ) =
        heckeBetaC K N ℓ := by
      refine modularFunctionFieldC_algHom_ext K N ?_ ?_
      · refine Subtype.ext ?_
        show ((e.symm (σ (e (heckeAlphaC K N ℓ (jF K N))))) : LaurentSeries K) = qExpand K ℓ (jqModC K)
        rw [hval_esymm, ← hσj]
        rfl
      · refine Subtype.ext ?_
        show ((e.symm (σ (e (heckeAlphaC K N ℓ (jNF K N))))) : LaurentSeries K) = qExpand K ℓ (jqNModC K N)
        rw [hval_esymm, ← hσjN]
        rfl
    intro f
    exact congrArg (fun g : modularFunctionFieldC K N →ₐ[K] charLDegeneracyRoof K N ℓ => g f) key
  · have key : (w : charLDegeneracyRoof K N ℓ →ₐ[K] charLDegeneracyRoof K N ℓ).comp (heckeBetaC K N ℓ) =
        heckeAlphaC K N ℓ := by
      refine modularFunctionFieldC_algHom_ext K N ?_ ?_
      · refine Subtype.ext ?_
        show ((e.symm (σ (e (heckeBetaC K N ℓ (jF K N))))) : LaurentSeries K) = jqModC K
        rw [hval_esymm, ← hσjℓ]
        rfl
      · refine Subtype.ext ?_
        show ((e.symm (σ (e (heckeBetaC K N ℓ (jNF K N))))) : LaurentSeries K) = jqNModC K N
        rw [hval_esymm, ← hσjNℓ]
        rfl
    intro f
    exact congrArg (fun g : modularFunctionFieldC K N →ₐ[K] charLDegeneracyRoof K N ℓ => g f) key

end AtkinLehner

section Trace

variable (K : Type*) [Field K] (N ℓ : ℕ)

def Lβ (_K : Type*) [Field _K] (_N _ℓ : ℕ) : Type _ := LaurentSeries _K

scoped instance instFieldLβ : Field (Lβ K N ℓ) := inferInstanceAs (Field (LaurentSeries K))

def toLβ : LaurentSeries K ≃+* Lβ K N ℓ := RingEquiv.refl _

variable [NeZero N] [hℓ : Fact ℓ.Prime]

scoped instance algFLβ : Algebra (modularFunctionFieldC K N) (Lβ K N ℓ) :=
  ((toLβ K N ℓ).toRingHom.comp ((qExpand K ℓ).comp
    (algebraMap (modularFunctionFieldC K N) (LaurentSeries K)))).toAlgebra

theorem algebraMap_FLβ (f : modularFunctionFieldC K N) :
    algebraMap (modularFunctionFieldC K N) (Lβ K N ℓ) f = toLβ K N ℓ (qExpand K ℓ (f : LaurentSeries K)) :=
  rfl

abbrev Ebar : Type _ := AlgebraicClosure (Lβ K N ℓ)

abbrev ιE : LaurentSeries K →+* Ebar K N ℓ :=
  (algebraMap (Lβ K N ℓ) (Ebar K N ℓ)).comp (toLβ K N ℓ).toRingHom

omit [NeZero N] hℓ in
theorem ιE_injective : Function.Injective (ιE K N ℓ) :=
  (algebraMap (Lβ K N ℓ) (Ebar K N ℓ)).injective.comp (toLβ K N ℓ).injective

theorem algebraMap_FE (f : modularFunctionFieldC K N) :
    algebraMap (modularFunctionFieldC K N) (Ebar K N ℓ) f = ιE K N ℓ (qExpand K ℓ (f : LaurentSeries K)) := by
  rw [IsScalarTower.algebraMap_apply (modularFunctionFieldC K N) (Lβ K N ℓ) (Ebar K N ℓ), algebraMap_FLβ]
  rfl

def embInf :
    letI := algebraAlong (heckeAlphaC K N ℓ)
    charLDegeneracyRoof K N ℓ →ₐ[modularFunctionFieldC K N] Ebar K N ℓ :=
  letI := algebraAlong (heckeAlphaC K N ℓ)
  { (ιE K N ℓ).comp ((qExpand K ℓ).comp (algebraMap (charLDegeneracyRoof K N ℓ) (LaurentSeries K))) with
    commutes' := fun f => by
      rw [algebraMap_FE]
      rfl }

theorem embInf_apply (x : charLDegeneracyRoof K N ℓ) :
    embInf K N ℓ x = ιE K N ℓ (qExpand K ℓ (x : LaurentSeries K)) := rfl

def embTwist (w : charLDegeneracyRoof K N ℓ ≃ₐ[K] charLDegeneracyRoof K N ℓ)
    (hwα : ∀ f, w (heckeAlphaC K N ℓ f) = heckeBetaC K N ℓ f) (u : Kˣ) (hu : u ^ ℓ = 1) :
    letI := algebraAlong (heckeAlphaC K N ℓ)
    charLDegeneracyRoof K N ℓ →ₐ[modularFunctionFieldC K N] Ebar K N ℓ :=
  letI := algebraAlong (heckeAlphaC K N ℓ)
  { (ιE K N ℓ).comp ((qTwist u).comp ((algebraMap (charLDegeneracyRoof K N ℓ) (LaurentSeries K)).comp
      (w : charLDegeneracyRoof K N ℓ →+* charLDegeneracyRoof K N ℓ))) with
    commutes' := fun f => by
      rw [algebraMap_FE]
      show ιE K N ℓ (qTwist u ((w (heckeAlphaC K N ℓ f) : charLDegeneracyRoof K N ℓ) : LaurentSeries K)) = _
      rw [hwα, coe_heckeBetaC, qTwist_qExpand_of_pow_eq_one ℓ hu] }

theorem embTwist_apply (w : charLDegeneracyRoof K N ℓ ≃ₐ[K] charLDegeneracyRoof K N ℓ)
    (hwα : ∀ f, w (heckeAlphaC K N ℓ f) = heckeBetaC K N ℓ f) (u : Kˣ) (hu : u ^ ℓ = 1)
    (x : charLDegeneracyRoof K N ℓ) :
    embTwist K N ℓ w hwα u hu x = ιE K N ℓ (qTwist u ((w x : charLDegeneracyRoof K N ℓ) : LaurentSeries K)) :=
  rfl

omit [NeZero N] hℓ in
theorem zeta_pow_pow (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (b : ℕ) : (ζ ^ b) ^ ℓ = 1 := by
  have hζu : IsPrimitiveRoot ζ ℓ := (IsPrimitiveRoot.coe_units_iff).mp hζ
  rw [← pow_mul, mul_comm, pow_mul, hζu.pow_eq_one, one_pow]

def emb (w : charLDegeneracyRoof K N ℓ ≃ₐ[K] charLDegeneracyRoof K N ℓ)
    (hwα : ∀ f, w (heckeAlphaC K N ℓ f) = heckeBetaC K N ℓ f) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (i : Fin (ℓ + 1)) :
    letI := algebraAlong (heckeAlphaC K N ℓ)
    charLDegeneracyRoof K N ℓ →ₐ[modularFunctionFieldC K N] Ebar K N ℓ :=
  Fin.cases (embInf K N ℓ) (fun b : Fin ℓ => embTwist K N ℓ w hwα (ζ ^ (b : ℕ)) (zeta_pow_pow K ℓ ζ hζ b)) i

theorem emb_zero (w : charLDegeneracyRoof K N ℓ ≃ₐ[K] charLDegeneracyRoof K N ℓ)
    (hwα : ∀ f, w (heckeAlphaC K N ℓ f) = heckeBetaC K N ℓ f) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    emb K N ℓ w hwα ζ hζ 0 = embInf K N ℓ := rfl

theorem emb_succ (w : charLDegeneracyRoof K N ℓ ≃ₐ[K] charLDegeneracyRoof K N ℓ)
    (hwα : ∀ f, w (heckeAlphaC K N ℓ f) = heckeBetaC K N ℓ f) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (b : Fin ℓ) :
    emb K N ℓ w hwα ζ hζ b.succ = embTwist K N ℓ w hwα (ζ ^ (b : ℕ)) (zeta_pow_pow K ℓ ζ hζ b) := rfl

theorem emb_injective (w : charLDegeneracyRoof K N ℓ ≃ₐ[K] charLDegeneracyRoof K N ℓ)
    (hwα : ∀ f, w (heckeAlphaC K N ℓ f) = heckeBetaC K N ℓ f)
    (hwβ : ∀ f, w (heckeBetaC K N ℓ f) = heckeAlphaC K N ℓ f)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    Function.Injective (emb K N ℓ w hwα ζ hζ) := by
  have hζu : IsPrimitiveRoot ζ ℓ := (IsPrimitiveRoot.coe_units_iff).mp hζ

  have hβj : ((w (heckeBetaC K N ℓ (jF K N)) : charLDegeneracyRoof K N ℓ) : LaurentSeries K) = jqModC K := by
    rw [hwβ]; rfl
  have hnot : ¬ (ℓ : ℤ) ∣ -1 := by
    intro h
    have h1 : (ℓ : ℤ) ∣ 1 := (dvd_neg).mp h
    have h2 : ℓ ∣ 1 := by exact_mod_cast h1
    exact hℓ.out.one_lt.ne' (Nat.dvd_one.mp h2)
  have hInf : (qExpand K ℓ ((heckeBetaC K N ℓ (jF K N) : charLDegeneracyRoof K N ℓ) : LaurentSeries K)).coeff (-1)
      = 0 := by
    rw [coe_heckeBetaC]
    exact qExpand_coeff_of_not_dvd ℓ _ hnot
  have hTw : ∀ b : ℕ, (qTwist (ζ ^ b) ((w (heckeBetaC K N ℓ (jF K N)) : charLDegeneracyRoof K N ℓ) :
      LaurentSeries K)).coeff (-1) = (((ζ ^ b) ^ (-1 : ℤ) : Kˣ) : K) := by
    intro b
    rw [hβj, qTwist_coeff, coeff_jqModC_neg_one, mul_one]
  intro i i' hii'
  have hval := congrArg (fun s => s (heckeBetaC K N ℓ (jF K N))) hii'
  beta_reduce at hval
  induction i using Fin.cases with
  | zero =>
    induction i' using Fin.cases with
    | zero => rfl
    | succ b' =>
      exfalso
      rw [emb_zero, emb_succ, embInf_apply, embTwist_apply] at hval
      have h := congrArg (fun s : LaurentSeries K => s.coeff (-1)) (ιE_injective K N ℓ hval)
      beta_reduce at h
      rw [hInf, hTw] at h
      exact (Units.ne_zero _) h.symm
  | succ b =>
    induction i' using Fin.cases with
    | zero =>
      exfalso
      rw [emb_zero, emb_succ, embInf_apply, embTwist_apply] at hval
      have h := congrArg (fun s : LaurentSeries K => s.coeff (-1)) (ιE_injective K N ℓ hval)
      beta_reduce at h
      rw [hInf, hTw] at h
      exact (Units.ne_zero _) h
    | succ b' =>
      rw [emb_succ, emb_succ, embTwist_apply, embTwist_apply] at hval
      have h := congrArg (fun s : LaurentSeries K => s.coeff (-1)) (ιE_injective K N ℓ hval)
      beta_reduce at h
      rw [hTw, hTw, Units.val_inj, zpow_neg, zpow_neg, inv_inj, zpow_one, zpow_one] at h
      have hbb : (b : ℕ) = b' := hζu.pow_inj b.2 b'.2 h
      rw [Fin.ext hbb]

theorem isSeparable_and_bijective (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N)
    (w : charLDegeneracyRoof K N ℓ ≃ₐ[K] charLDegeneracyRoof K N ℓ)
    (hwα : ∀ f, w (heckeAlphaC K N ℓ f) = heckeBetaC K N ℓ f)
    (hwβ : ∀ f, w (heckeBetaC K N ℓ f) = heckeAlphaC K N ℓ f)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    letI := algebraAlong (heckeAlphaC K N ℓ)
    Algebra.IsSeparable (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) ∧
      Function.Bijective (emb K N ℓ w hwα ζ hζ) := by
  letI := algebraAlong (heckeAlphaC K N ℓ)
  letI : Module (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) := Algebra.toModule
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_isPrimitiveRoot ℓ ζ hζ
  have hfr := finrank_along_alpha K N ℓ hN hℓN hℓK
  haveI : FiniteDimensional (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact Nat.succ_pos ℓ)
  haveI : Algebra.IsAlgebraic (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) :=
    Algebra.IsAlgebraic.of_finite _ _
  have hinj := emb_injective K N ℓ w hwα hwβ ζ hζ
  have hle : Nat.card (charLDegeneracyRoof K N ℓ →ₐ[modularFunctionFieldC K N] Ebar K N ℓ) ≤ ℓ + 1 := by
    rw [← Field.finSepDegree_eq_of_isAlgClosed (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ)
      (Ebar K N ℓ), ← hfr]
    exact Field.finSepDegree_le_finrank _ _
  have hge : ℓ + 1 ≤ Nat.card (charLDegeneracyRoof K N ℓ →ₐ[modularFunctionFieldC K N] Ebar K N ℓ) := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  have hcard : Nat.card (charLDegeneracyRoof K N ℓ →ₐ[modularFunctionFieldC K N] Ebar K N ℓ) = ℓ + 1 :=
    le_antisymm hle hge
  refine ⟨?_, ?_⟩
  · rw [← Field.finSepDegree_eq_finrank_iff, hfr,
      Field.finSepDegree_eq_of_isAlgClosed (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) (Ebar K N ℓ)]
    exact hcard
  · rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_fin, Fintype.card_eq_nat_card, hcard]

theorem qExpand_trace (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N)
    (w : charLDegeneracyRoof K N ℓ ≃ₐ[K] charLDegeneracyRoof K N ℓ)
    (hwα : ∀ f, w (heckeAlphaC K N ℓ f) = heckeBetaC K N ℓ f)
    (hwβ : ∀ f, w (heckeBetaC K N ℓ f) = heckeAlphaC K N ℓ f)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (y : charLDegeneracyRoof K N ℓ) :
    letI := algebraAlong (heckeAlphaC K N ℓ)
    qExpand K ℓ ((Algebra.trace (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) y :
        modularFunctionFieldC K N) : LaurentSeries K) =
      qExpand K ℓ (y : LaurentSeries K) +
        ∑ b : Fin ℓ, qTwist (ζ ^ (b : ℕ)) ((w y : charLDegeneracyRoof K N ℓ) : LaurentSeries K) := by
  letI := algebraAlong (heckeAlphaC K N ℓ)
  letI : Module (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) := Algebra.toModule
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_isPrimitiveRoot ℓ ζ hζ
  have hfr := finrank_along_alpha K N ℓ hN hℓN hℓK
  haveI : FiniteDimensional (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact Nat.succ_pos ℓ)
  obtain ⟨hsep, hbij⟩ := isSeparable_and_bijective K N ℓ hN hℓN w hwα hwβ ζ hζ
  haveI := hsep
  apply ιE_injective K N ℓ
  have htr := trace_eq_sum_embeddings (Ebar K N ℓ) (K := modularFunctionFieldC K N)
    (L := charLDegeneracyRoof K N ℓ) (x := y)
  rw [algebraMap_FE] at htr
  rw [htr, ← Fintype.sum_bijective _ hbij (fun i => emb K N ℓ w hwα ζ hζ i y) (fun σ => σ y)
    (fun _ => rfl), Fin.sum_univ_succ, map_add, map_sum]
  rfl

end Trace

section KaehlerGeneric

variable {K F R L : Type*} [Field K] [Field F] [Field R] [Algebra K F] [Algebra K R]
  [Field L] [Algebra K L]

theorem D_ne_zero_of_thetaL_ne_zero (σ : F →ₐ[K] LaurentSeries L) (x : F)
    (hx : thetaL L (σ x) ≠ 0) : KaehlerDifferential.D K F x ≠ 0 := by
  intro h0
  have h1 := (isQExpansionDiffAlong_qExpansionDiffAlong σ).1 x
  rw [h0, map_zero] at h1
  exact hx h1.symm

variable [Algebra F R] [IsScalarTower K F R]

theorem exists_D_eq_smul_map [Algebra.IsSeparable F R] (x : F)
    (hspan : ∀ ω : Ω[F⁄K], ∃ c : F, c • KaehlerDifferential.D K F x = ω) (b : R) :
    ∃ h : R, KaehlerDifferential.D K R b =
      h • KaehlerDifferential.map K K F R (KaehlerDifferential.D K F x) := by
  haveI : Algebra.FormallyEtale F R := Algebra.FormallyEtale.of_isSeparable F R
  have hsurj : Function.Surjective (KaehlerDifferential.mapBaseChange K F R) := fun z => by
    obtain ⟨t, ht⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F R).surjective z
    exact ⟨t, by rw [← ht, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply]⟩
  have hall : ∀ t : TensorProduct F R (Ω[F⁄K]), ∃ h : R,
      KaehlerDifferential.mapBaseChange K F R t =
        h • KaehlerDifferential.map K K F R (KaehlerDifferential.D K F x) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, zero_smul]⟩
    | tmul r ω =>
      obtain ⟨c, rfl⟩ := hspan ω
      refine ⟨r * algebraMap F R c, ?_⟩
      rw [KaehlerDifferential.mapBaseChange_tmul, map_smul, ← IsScalarTower.algebraMap_smul R c,
        smul_smul]
    | add x y hx hy =>
      obtain ⟨h₁, h₁e⟩ := hx
      obtain ⟨h₂, h₂e⟩ := hy
      exact ⟨h₁ + h₂, by rw [map_add, h₁e, h₂e, add_smul]⟩
  obtain ⟨t, ht⟩ := hsurj (KaehlerDifferential.D K R b)
  obtain ⟨h, hh⟩ := hall t
  exact ⟨h, by rw [← ht, hh]⟩

theorem thetaL_eq_of_D_eq_smul_map (σ : R →ₐ[K] LaurentSeries L) {x : F} {b h : R}
    (hD : KaehlerDifferential.D K R b =
      h • KaehlerDifferential.map K K F R (KaehlerDifferential.D K F x)) :
    thetaL L (σ b) = σ h * thetaL L (σ (algebraMap F R x)) := by
  have h1 := (isQExpansionDiffAlong_qExpansionDiffAlong σ).1 b
  rw [hD, qExpansionDiffAlong_smul_map, (isQExpansionDiffAlong_qExpansionDiffAlong _).1 x] at h1
  exact h1.symm

theorem qExpansionDiffAlong_smul_D (σ : F →ₐ[K] LaurentSeries L) (f x : F) :
    qExpansionDiffAlong σ (f • KaehlerDifferential.D K F x) = σ f * thetaL L (σ x) := by
  rw [(isQExpansionDiffAlong_qExpansionDiffAlong σ).2, (isQExpansionDiffAlong_qExpansionDiffAlong σ).1]

end KaehlerGeneric

section Main

variable {K : Type*} [Field K]

theorem qTwist_smul (u : Kˣ) (c : K) (x : LaurentSeries K) : qTwist u (c • x) = c • qTwist u x := by
  ext k
  rw [qTwist_coeff, HahnSeries.coeff_smul, HahnSeries.coeff_smul, qTwist_coeff, smul_eq_mul, smul_eq_mul]
  ring

theorem qExpand_smul (m : ℕ) [NeZero m] (c : K) (x : LaurentSeries K) :
    qExpand K m (c • x) = c • qExpand K m x := by
  rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, map_mul, qExpand_C]

theorem thetaL_jqModC_ne_zero (K : Type*) [Field K] : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff (-1)) h
  beta_reduce at h1
  rw [thetaL_coeff, coeff_jqModC_neg_one, HahnSeries.coeff_zero, mul_one] at h1
  norm_num at h1

variable (K) (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime]

omit hℓ in

theorem exists_eq_smul_D_jF (hN : (N : K) ≠ 0) (ω : Ω[modularFunctionFieldC K N⁄K]) :
    ∃ f : modularFunctionFieldC K N,
      f • KaehlerDifferential.D K (modularFunctionFieldC K N) (jF K N) = ω := by
  have hsep := isSeparable_jqNModC_of_natCast_ne_zero K N hN
  obtain ⟨_, hfin⟩ := kaehlerRankOne_modularFunctionFieldC_of_isSeparable_jqNModC K N hsep
  have hDne := D_ne_zero_of_thetaL_ne_zero (modularFunctionFieldC K N).val (jF K N)
    (thetaL_jqModC_ne_zero K)
  exact (finrank_eq_one_iff_of_nonzero' _ hDne).mp hfin ω

theorem qExpand_trace_mul_pow_weight (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) ℓ) (m : ℕ) (G : modularFunctionFieldC K N)
    (w : charLDegeneracyRoof K N ℓ ≃ₐ[K] charLDegeneracyRoof K N ℓ)
    (hwα : ∀ f, w (heckeAlphaC K N ℓ f) = heckeBetaC K N ℓ f)
    (hwβ : ∀ f, w (heckeBetaC K N ℓ f) = heckeAlphaC K N ℓ f)
    (h : charLDegeneracyRoof K N ℓ)
    (hD : letI := algebraAlong (heckeAlphaC K N ℓ)
      haveI := isScalarTower_along (heckeAlphaC K N ℓ)
      KaehlerDifferential.D K (charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jF K N)) =
        h • KaehlerDifferential.map K K (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ)
          (KaehlerDifferential.D K (modularFunctionFieldC K N) (jF K N))) :
    letI := algebraAlong (heckeAlphaC K N ℓ)
    qExpand K ℓ (((Algebra.trace (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ)
        (heckeBetaC K N ℓ G * h ^ m) : modularFunctionFieldC K N) : LaurentSeries K) *
        thetaL K (jqModC K) ^ m) =
      HahnSeries.C ((ℓ : K) ^ m) * qExpand K ℓ (qExpand K ℓ ((G : LaurentSeries K) * thetaL K (jqModC K) ^ m)) +
        HahnSeries.C ((ℓ : K)⁻¹ ^ m) *
          ∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) ((G : LaurentSeries K) * thetaL K (jqModC K) ^ m) := by
  letI := algebraAlong (heckeAlphaC K N ℓ)
  letI : Module (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) := Algebra.toModule
  haveI := isScalarTower_along (heckeAlphaC K N ℓ)
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_isPrimitiveRoot ℓ ζ hζ
  have hE1 : (h : LaurentSeries K) * thetaL K (jqModC K) = HahnSeries.C (ℓ : K) * qExpand K ℓ (thetaL K (jqModC K)) := by
    have h1 := thetaL_eq_of_D_eq_smul_map (charLDegeneracyRoof K N ℓ).val hD
    have e1 : (charLDegeneracyRoof K N ℓ).val (heckeBetaC K N ℓ (jF K N)) = qExpand K ℓ (jqModC K) := rfl
    have e2 : (charLDegeneracyRoof K N ℓ).val
        (algebraMap (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) (jF K N)) = jqModC K := rfl
    rw [e1, e2, thetaL_qExpand, ← HahnSeries.C_mul_eq_smul] at h1
    exact h1.symm
  have hE2 : ((w h : charLDegeneracyRoof K N ℓ) : LaurentSeries K) *
      (HahnSeries.C (ℓ : K) * qExpand K ℓ (thetaL K (jqModC K))) = thetaL K (jqModC K) := by
    have h1 := thetaL_eq_of_D_eq_smul_map ((charLDegeneracyRoof K N ℓ).val.comp w.toAlgHom) hD
    have e1 : ((charLDegeneracyRoof K N ℓ).val.comp w.toAlgHom) (heckeBetaC K N ℓ (jF K N)) = jqModC K := by
      show ((w (heckeBetaC K N ℓ (jF K N)) : charLDegeneracyRoof K N ℓ) : LaurentSeries K) = _
      rw [hwβ]; rfl
    have e2 : ((charLDegeneracyRoof K N ℓ).val.comp w.toAlgHom)
          (algebraMap (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) (jF K N)) = qExpand K ℓ (jqModC K) := by
      show ((w (heckeAlphaC K N ℓ (jF K N)) : charLDegeneracyRoof K N ℓ) : LaurentSeries K) = _
      rw [hwα]; rfl
    rw [e1, e2, thetaL_qExpand, ← HahnSeries.C_mul_eq_smul] at h1
    exact h1.symm
  have hC : HahnSeries.C (ℓ : K)⁻¹ * HahnSeries.C (ℓ : K) = (1 : LaurentSeries K) := by
    rw [← map_mul, inv_mul_cancel₀ hℓK, map_one]
  have hE2' : ((w h : charLDegeneracyRoof K N ℓ) : LaurentSeries K) * qExpand K ℓ (thetaL K (jqModC K)) =
      HahnSeries.C (ℓ : K)⁻¹ * thetaL K (jqModC K) := by
    linear_combination (HahnSeries.C (ℓ : K)⁻¹) * hE2 -
      (((w h : charLDegeneracyRoof K N ℓ) : LaurentSeries K) * qExpand K ℓ (thetaL K (jqModC K))) * hC
  have hE1m : (h : LaurentSeries K) ^ m * thetaL K (jqModC K) ^ m =
      HahnSeries.C ((ℓ : K) ^ m) * qExpand K ℓ (thetaL K (jqModC K) ^ m) := by
    rw [← mul_pow, hE1, mul_pow, ← map_pow, ← map_pow]
  have hE2m : ((w h : charLDegeneracyRoof K N ℓ) : LaurentSeries K) ^ m * qExpand K ℓ (thetaL K (jqModC K) ^ m) =
      HahnSeries.C ((ℓ : K)⁻¹ ^ m) * thetaL K (jqModC K) ^ m := by
    rw [map_pow, ← mul_pow, hE2', mul_pow, ← map_pow]
  have hT1 := qExpand_trace K N ℓ hN hℓN w hwα hwβ ζ hζ (heckeBetaC K N ℓ G * h ^ m)
  have hyval : ((heckeBetaC K N ℓ G * h ^ m : charLDegeneracyRoof K N ℓ) : LaurentSeries K) =
      qExpand K ℓ (G : LaurentSeries K) * (h : LaurentSeries K) ^ m := by
    rw [IntermediateField.coe_mul, IntermediateField.coe_pow, coe_heckeBetaC]
  have hwyval : ((w (heckeBetaC K N ℓ G * h ^ m) : charLDegeneracyRoof K N ℓ) : LaurentSeries K) =
      (G : LaurentSeries K) * ((w h : charLDegeneracyRoof K N ℓ) : LaurentSeries K) ^ m := by
    rw [map_mul, map_pow, IntermediateField.coe_mul, IntermediateField.coe_pow, hwβ, coe_heckeAlphaC]
  have hTC : ∀ (u : Kˣ) (c : K), qTwist u (HahnSeries.C c) = HahnSeries.C c := by
    intro u c
    rw [HahnSeries.C_apply, qTwist_single, zpow_zero, Units.val_one, one_mul]
  have hTV : ∀ b : ℕ, qTwist (ζ ^ b) (qExpand K ℓ (thetaL K (jqModC K) ^ m)) = qExpand K ℓ (thetaL K (jqModC K) ^ m) :=
    fun b => qTwist_qExpand_of_pow_eq_one ℓ (zeta_pow_pow K ℓ ζ hζ b) _
  rw [map_mul, hT1, hyval, hwyval,
    Fin.sum_univ_eq_sum_range
      (fun b => qTwist (ζ ^ b) ((G : LaurentSeries K) * ((w h : charLDegeneracyRoof K N ℓ) : LaurentSeries K) ^ m)) ℓ,
    add_mul, Finset.sum_mul, Finset.mul_sum, map_pow]
  congr 1
  · calc qExpand K ℓ (qExpand K ℓ (G : LaurentSeries K) * (h : LaurentSeries K) ^ m) * qExpand K ℓ (thetaL K (jqModC K)) ^ m
        = qExpand K ℓ (qExpand K ℓ (G : LaurentSeries K)) *
            qExpand K ℓ ((h : LaurentSeries K) ^ m * thetaL K (jqModC K) ^ m) := by
          rw [map_mul, map_mul, ← map_pow, mul_assoc]
      _ = HahnSeries.C ((ℓ : K) ^ m) * qExpand K ℓ (qExpand K ℓ ((G : LaurentSeries K) * thetaL K (jqModC K) ^ m)) := by
          rw [hE1m, map_mul, qExpand_C, map_mul, map_mul]; ring
  · refine Finset.sum_congr rfl fun b _ => ?_
    calc qTwist (ζ ^ b) ((G : LaurentSeries K) * ((w h : charLDegeneracyRoof K N ℓ) : LaurentSeries K) ^ m) *
          qExpand K ℓ (thetaL K (jqModC K)) ^ m
        = qTwist (ζ ^ b) ((G : LaurentSeries K) *
            (((w h : charLDegeneracyRoof K N ℓ) : LaurentSeries K) ^ m * qExpand K ℓ (thetaL K (jqModC K) ^ m))) := by
          rw [← map_pow, ← hTV b, ← map_mul, mul_assoc, hTV b]
      _ = HahnSeries.C ((ℓ : K)⁻¹ ^ m) * qTwist (ζ ^ b) ((G : LaurentSeries K) * thetaL K (jqModC K) ^ m) := by
          rw [hE2m, map_mul, map_mul, hTC, map_mul]; ring

theorem coeff_trace_mul_pow_weight (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) ℓ) (m : ℕ) (G : modularFunctionFieldC K N)
    (h : charLDegeneracyRoof K N ℓ)
    (hD : letI := algebraAlong (heckeAlphaC K N ℓ)
      haveI := isScalarTower_along (heckeAlphaC K N ℓ)
      KaehlerDifferential.D K (charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jF K N)) =
        h • KaehlerDifferential.map K K (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ)
          (KaehlerDifferential.D K (modularFunctionFieldC K N) (jF K N))) (n : ℤ) :
    letI := algebraAlong (heckeAlphaC K N ℓ)
    haveI := isScalarTower_along (heckeAlphaC K N ℓ)
    (((Algebra.trace (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ)
        (heckeBetaC K N ℓ G * h ^ m) : modularFunctionFieldC K N) : LaurentSeries K) *
        thetaL K (jqModC K) ^ m).coeff n =
      (ℓ : K) ^ m * (if (ℓ : ℤ) ∣ n then ((G : LaurentSeries K) * thetaL K (jqModC K) ^ m).coeff (n / ℓ) else 0) +
        (ℓ : K)⁻¹ ^ m * (ℓ : K) * ((G : LaurentSeries K) * thetaL K (jqModC K) ^ m).coeff ((ℓ : ℤ) * n) := by
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_isPrimitiveRoot ℓ ζ hζ
  obtain ⟨w, hwα, hwβ⟩ := exists_atkinLehner K N ℓ hN hℓN hℓK
  have hV := qExpand_trace_mul_pow_weight K N ℓ hN hℓN ζ hζ m G w hwα hwβ h hD
  set f := (G : LaurentSeries K) * thetaL K (jqModC K) ^ m with hf
  have hc := congrArg (fun s : LaurentSeries K => s.coeff ((ℓ : ℤ) * n)) hV
  beta_reduce at hc
  rw [qExpand_coeff_mul, HahnSeries.coeff_add, HahnSeries.C_mul_eq_smul, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
    HahnSeries.coeff_smul, qExpand_coeff_mul, sum_qTwist_coeff ℓ ζ hζ, if_pos (Dvd.intro n rfl), smul_eq_mul, smul_eq_mul] at hc
  rw [hc]
  congr 1
  · congr 1
    by_cases hn : (ℓ : ℤ) ∣ n
    · obtain ⟨k, rfl⟩ := hn
      rw [if_pos (Dvd.intro k rfl), qExpand_coeff_mul, Int.mul_ediv_cancel_left _ (by exact_mod_cast hℓ.out.ne_zero)]
    · rw [if_neg hn, qExpand_coeff_of_not_dvd ℓ _ hn]
  · ring

end Main

end ModularCurve.CharQHeckeDiff
p2m_reactivate "P2MW.S_ModularCurve_qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map.ModularCurve P2MW.S_ModularCurve_qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map.ModularCurve.CharQHeckeDiff"
p2m_reactivate "P2MW.S_ModularCurve_qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map.ModularCurve"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map.ModularCurve AlgebraicCurve ModularCurve.CharQHeckeDiff in

theorem HFNSol.coeff_ofPowerSeries_of_neg {K : Type} [Field K] (ψ : PowerSeries K) {k : ℤ} (hk : k < 0) :
    (HahnSeries.ofPowerSeries ℤ K ψ).coeff k = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  exact HahnSeries.embDomain_notin_range (by
    rintro ⟨a, ha⟩
    simp at ha
    omega)

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map.ModularCurve AlgebraicCurve ModularCurve.CharQHeckeDiff in
theorem solution
    (K : Type) [Field K] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (m : ℕ) (hm : 1 ≤ m) (G : ↥(modularFunctionFieldC K N)) (φ : PowerSeries K)
    (hφ : HahnSeries.ofPowerSeries ℤ K φ = qexpOfWeight K (m : ℤ) ((G : ↥(modularFunctionFieldC K N)) : LaurentSeries K))
    (h : ↥(charLDegeneracyRoof K N ℓ))
    (hD : letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
      haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ)
      KaehlerDifferential.D K ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jGeomGen K N))
        = h • KaehlerDifferential.map K K ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
            (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N))) :
    letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
    HahnSeries.ofPowerSeries ℤ K (ModPForms.heckePS (2 * (m : ℤ)) ℓ φ)
      = qexpOfWeight K (m : ℤ)
          (HahnSeries.C ((ℓ : K) ^ (m - 1)) *
            (((Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ G * h ^ m) : ↥(modularFunctionFieldC K N)) : LaurentSeries K))) := by
  letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
  haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ)
  have hℓ : Fact ℓ.Prime := inferInstance
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_isPrimitiveRoot ℓ ζ hζ

  have hD' : KaehlerDifferential.D K (charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jF K N)) =
      h • KaehlerDifferential.map K K (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ)
        (KaehlerDifferential.D K (modularFunctionFieldC K N) (jF K N)) := hD
  set f : LaurentSeries K := (G : LaurentSeries K) * thetaL K (jqModC K) ^ m with hf
  have hfφ : HahnSeries.ofPowerSeries ℤ K φ = f := by
    rw [hφ, hf, qexpOfWeight, thetaJ, zpow_natCast]
  have hfneg : ∀ k : ℤ, k < 0 → f.coeff k = 0 := fun k hk => by
    rw [← hfφ]; exact HFNSol.coeff_ofPowerSeries_of_neg φ hk
  have hfnat : ∀ k : ℕ, f.coeff (k : ℤ) = PowerSeries.coeff k φ := fun k => by
    rw [← hfφ, HahnSeries.ofPowerSeries_apply_coeff]
  have hcoef := coeff_trace_mul_pow_weight K N ℓ hN hℓN ζ hζ m G h hD'
  rw [qexpOfWeight, thetaJ, zpow_natCast, mul_assoc, HahnSeries.C_mul_eq_smul]
  apply HahnSeries.ext
  funext n
  rw [HahnSeries.coeff_smul, smul_eq_mul, hcoef n]

  have harith : ∀ A B : K, (ℓ : K) ^ (m - 1) * ((ℓ : K) ^ m * A + (ℓ : K)⁻¹ ^ m * (ℓ : K) * B)
      = (ℓ : K) ^ (2 * m - 1) * A + B := by
    intro A B
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hx : (ℓ : K)⁻¹ ^ (m' + 1) * (ℓ : K) = (ℓ : K)⁻¹ ^ m' := by
      rw [pow_succ, mul_assoc, inv_mul_cancel₀ hℓK, mul_one]
    have hy : (ℓ : K) ^ m' * (ℓ : K)⁻¹ ^ m' = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hℓK, one_pow]
    rw [show m' + 1 - 1 = m' by omega, show 2 * (m' + 1) - 1 = m' + (m' + 1) by omega, mul_add, hx]
    congr 1
    · rw [← mul_assoc, ← pow_add]
    · rw [← mul_assoc, hy, one_mul]
  rw [harith]
  rcases lt_or_ge n 0 with hn | hn
  ·
    have hℓpos : (0 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ.out.pos
    rw [HFNSol.coeff_ofPowerSeries_of_neg _ hn, hfneg _ (Int.mul_neg_of_pos_of_neg hℓpos hn), add_zero]
    split_ifs with hd
    · obtain ⟨k, rfl⟩ := hd
      have hk : k < 0 := by
        by_contra hk
        push_neg at hk
        have := Int.mul_nonneg hℓpos.le hk
        omega
      rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hℓ.out.ne_zero), hfneg k hk, mul_zero]
    · rw [mul_zero]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, ModPForms.heckePS, PowerSeries.coeff_mk,
      show ((ℓ : ℤ) * (k : ℤ)) = ((ℓ * k : ℕ) : ℤ) by push_cast; ring, hfnat, mul_comm ℓ k, add_comm]
    congr 1
    by_cases hd : ℓ ∣ k
    · rw [if_pos hd, if_pos (Int.natCast_dvd_natCast.mpr hd), show ((k : ℤ) / (ℓ : ℤ)) = ((k / ℓ : ℕ) : ℤ) by simp,
        hfnat, show (2 * (m : ℤ) - 1) = ((2 * m - 1 : ℕ) : ℤ) by omega, zpow_natCast]
    · rw [if_neg hd, if_neg (fun h' => hd (Int.natCast_dvd_natCast.mp h')), mul_zero]

#print axioms solution

end
p2m_reactivate "P2MW.S_ModularCurve_qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map.ModularCurve P2MW.S_ModularCurve_qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map.ModularCurve.CharQHeckeDiff"

end S_ModularCurve_qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map
end P2MW
export P2MW.S_ModularCurve_qexpOfWeight_trace_heckeBetaC_mul_pow_eq_heckePS_of_eq_smul_map (solution)
