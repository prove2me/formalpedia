-- Prove2me | solution 1 for ModularCurve.exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/9e5199de-0acd-54a0-b65d-2bc4b4c07ce2

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDiamondModL
import Definitions.Def_ModularCurve_TateSlots
import Theorems.Thm_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum
import Theorems.Thm_ModularCurve_c4_tateLaurent
import Theorems.Thm_ModularCurve_c6_tatePowerSeries
import Theorems.Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4
import Theorems.Thm_ModularCurve_qExpansion_E6_eq_map_mk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace W769

p2m_open "UpperHalfPlane~I"
open ModularForm CongruenceSubgroup ModularCurve HahnSeries
open scoped MatrixGroups ModularForm

variable (M : ℕ) [NeZero M]

local notation "Γᴳ" => ((CohCarrier.GammaH M ⊥ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

local notation "Γ₁ᴳ" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem le_Gamma1 : Γᴳ ≤ Γ₁ᴳ := Subgroup.map_mono (ModularCurve.GammaH_bot M).le

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γᴳ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (ModularCurve.translation_mem_GammaH M ⊥)]
  exact AddSubgroup.mem_zmultiples 1

structure FB where

  B : ZMod M → ModularForm Γ₁ᴳ 2

  D : ZMod M → ModularForm Γ₁ᴳ 4

  b : ZMod M → PowerSeries ℤ

  d : ZMod M → PowerSeries ℤ
  hb : ∀ c : ZMod M, IsIntegralQExp (B c) (b c)
  hd : ∀ c : ZMod M, IsIntegralQExp (D c) (d c)
  hB : ∀ (c : ZMod M) (γ : SL(2, ℤ)), γ ∈ Gamma0 M →
    (⇑(B c) : ℍ → ℂ) ∣[(2 : ℤ)] γ = ⇑(B (c * ((γ 0 0 : ℤ) : ZMod M)))
  hD : ∀ (c : ZMod M) (γ : SL(2, ℤ)), γ ∈ Gamma0 M →
    (⇑(D c) : ℍ → ℂ) ∣[(4 : ℤ)] γ = ⇑(D (c * ((γ 0 0 : ℤ) : ZMod M)))

variable {M}
variable (X : FB M)

variable (M) in

def E4Γ : ModularForm Γᴳ 4 := restrictForm (Subgroup.map_le_range _ _) E₄
variable (M) in

def E6Γ : ModularForm Γᴳ 6 := restrictForm (Subgroup.map_le_range _ _) E₆

def BΓ (c : ZMod M) : ModularForm Γᴳ 2 := restrictForm (le_Gamma1 M) (X.B c)

def DΓ (c : ZMod M) : ModularForm Γᴳ 4 := restrictForm (le_Gamma1 M) (X.D c)

def f6 (c : ZMod M) : ModularForm Γᴳ 6 := ((BΓ X c).mul (E4Γ M)).mcast (by norm_num)

variable (M) in
theorem coe_E4Γ : (⇑(E4Γ M) : ℍ → ℂ) = E₄ := rfl
variable (M) in
theorem coe_E6Γ : (⇑(E6Γ M) : ℍ → ℂ) = E₆ := rfl
theorem coe_BΓ (c : ZMod M) : (⇑(BΓ X c) : ℍ → ℂ) = X.B c := rfl
theorem coe_DΓ (c : ZMod M) : (⇑(DΓ X c) : ℍ → ℂ) = X.D c := rfl
theorem coe_f6 (c : ZMod M) : (⇑(f6 X c) : ℍ → ℂ) = ⇑(X.B c) * E₄ := rfl

variable (M) in
theorem isIntegralQExp_E4Γ : IsIntegralQExp (E4Γ M) eisenstein4 := by
  rw [IsIntegralQExp, coe_E4Γ]; exact ModularCurve.qExpansion_E4_eq_map_eisenstein4.symm

variable (M) in
theorem isIntegralQExp_E6Γ : IsIntegralQExp (E6Γ M) eisenstein6 := by
  rw [IsIntegralQExp, coe_E6Γ, eisenstein6]; exact ModularCurve.qExpansion_E6_eq_map_mk.symm

theorem isIntegralQExp_DΓ (c : ZMod M) : IsIntegralQExp (DΓ X c) (X.d c) := X.hd c

theorem isIntegralQExp_f6 (c : ZMod M) : IsIntegralQExp (f6 X c) (X.b c * eisenstein4) := by
  rw [IsIntegralQExp, show (⇑(f6 X c) : ℍ → ℂ) = ⇑((BΓ X c).mul (E4Γ M)) from rfl,
    ModularForm.qExpansion_mul one_pos (one_mem_strictPeriods M), map_mul, coe_BΓ, coe_E4Γ,
    ModularCurve.qExpansion_E4_eq_map_eisenstein4, X.hb c]

theorem E4_slash (γ : SL(2, ℤ)) : (E₄ : ℍ → ℂ) ∣[(4 : ℤ)] γ = E₄ := by
  rw [ModularForm.SL_slash]; exact SlashInvariantFormClass.slash_action_eq E₄ _ ⟨γ, rfl⟩

theorem E6_slash (γ : SL(2, ℤ)) : (E₆ : ℍ → ℂ) ∣[(6 : ℤ)] γ = E₆ := by
  rw [ModularForm.SL_slash]; exact SlashInvariantFormClass.slash_action_eq E₆ _ ⟨γ, rfl⟩

theorem f6_slash (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(f6 X c) : ℍ → ℂ) ∣[(6 : ℤ)] γ = ⇑(f6 X (c * ((γ 0 0 : ℤ) : ZMod M))) := by
  rw [coe_f6, coe_f6, show (6 : ℤ) = 2 + 4 from rfl, ModularForm.mul_slash_SL2, X.hB c γ hγ, E4_slash]

theorem D_slash (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(DΓ X c) : ℍ → ℂ) ∣[(4 : ℤ)] γ = ⇑(DΓ X (c * ((γ 0 0 : ℤ) : ZMod M))) := by
  rw [coe_DΓ, coe_DΓ]; exact X.hD c γ hγ

section Field

variable (K : Type*) [Field K]

local notation "F̄" => qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)

omit X in
theorem natCast_ne_zero {ζ : K} (hζ : IsPrimitiveRoot ζ M) : (M : K) ≠ 0 := by
  haveI := hζ.neZero'; exact NeZero.ne (M : K)

omit X in
theorem natCast_laurent_ne_zero {ζ : K} (hζ : IsPrimitiveRoot ζ M) : (M : LaurentSeries K) ≠ 0 := by
  rw [← map_natCast (algebraMap K (LaurentSeries K)) M]
  exact (map_ne_zero_iff _ (algebraMap K (LaurentSeries K)).injective).mpr (natCast_ne_zero K hζ)

omit X in
theorem algebraMap_laurent_eq_C (r : K) : algebraMap K (LaurentSeries K) r = HahnSeries.C r := by
  show HahnSeries.ofPowerSeries ℤ K (algebraMap K (PowerSeries K) r) = _
  simp

omit X in
theorem intSeriesC_eisenstein4 : intSeriesC K eisenstein4 = (tateLaurent K).c₄ :=
  (ModularCurve.c4_tateLaurent K).symm

omit X in
theorem intSeriesC_eisenstein6 : intSeriesC K eisenstein6 = -(tateLaurent K).c₆ := by
  rw [tateLaurent, WeierstrassCurve.map_c₆, ModularCurve.c6_tatePowerSeries, map_neg, neg_neg]; rfl

omit X in
theorem constantCoeff_eisenstein4 : PowerSeries.constantCoeff eisenstein4 = 1 := by
  simp [eisenstein4]

omit X in
theorem intSeriesC_ne_zero_of_constantCoeff {p : PowerSeries ℤ}
    (hp : PowerSeries.constantCoeff p = 1) : intSeriesC K p ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : LaurentSeries K => z.coeff 0) h
  simp only [intSeriesC, HahnSeries.coeff_zero] at h1
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hp, map_one] at h1
  exact one_ne_zero h1

omit X in
theorem intSeriesC_eisenstein4_ne_zero : intSeriesC K eisenstein4 ≠ 0 :=
  intSeriesC_ne_zero_of_constantCoeff K constantCoeff_eisenstein4

omit X in
theorem intSeriesC_eisenstein6_ne_zero : intSeriesC K eisenstein6 ≠ 0 :=
  intSeriesC_ne_zero_of_constantCoeff K constantCoeff_eisenstein6

def β (c : ZMod M) : F̄ :=
  ⟨intSeriesC K (X.b c * eisenstein4) / intSeriesC K eisenstein6,
    div_mem_qExpFunctionFieldC (f6 X c) (E6Γ M) (isIntegralQExp_f6 X c)
      (isIntegralQExp_E6Γ M) (intSeriesC_eisenstein6_ne_zero K)⟩

def δ (c : ZMod M) : F̄ :=
  ⟨intSeriesC K (X.d c) / intSeriesC K eisenstein4,
    div_mem_qExpFunctionFieldC (DΓ X c) (E4Γ M) (isIntegralQExp_DΓ X c)
      (isIntegralQExp_E4Γ M) (intSeriesC_eisenstein4_ne_zero K)⟩

@[scoped simp] theorem coe_β (c : ZMod M) :
    ((β X K c : F̄) : LaurentSeries K) = intSeriesC K (X.b c * eisenstein4) / intSeriesC K eisenstein6 :=
  rfl

@[scoped simp] theorem coe_δ (c : ZMod M) :
    ((δ X K c : F̄) : LaurentSeries K) = intSeriesC K (X.d c) / intSeriesC K eisenstein4 := rfl

local notation "ι" => algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))

omit X in
theorem coe_algebraMap (r : K) : ((ι r : F̄) : LaurentSeries K) = algebraMap K (LaurentSeries K) r := rfl

def w₁ (ζ : K) (t : (ZMod M)ˣ) : F̄ :=
  ι (-((M : K)⁻¹ ^ 3)) * ∑ c : ZMod M, ι (ζ ^ ((t : ZMod M) * c).val) * β X K c

def w₂ (ζ : K) (t : (ZMod M)ˣ) : F̄ :=
  ι ((M : K)⁻¹ ^ 5) * ∑ c : ZMod M, ι (ζ ^ ((t : ZMod M) * c).val) * δ X K c

variable {K}

omit X in
theorem unit_ne_zero (hM : 2 ≤ M) (t : (ZMod M)ˣ) : (t : ZMod M) ≠ 0 := by
  haveI : Nontrivial (ZMod M) := ZMod.nontrivial_iff.mpr (by omega)
  exact t.ne_zero

theorem coe_w₁ {ζ : K} (hζ : IsPrimitiveRoot ζ M) (hM : 2 ≤ M)
    (hK : ∀ s : ZMod M, s ≠ 0 →
      (M : LaurentSeries K) ^ 3 * (1 + 12 * (toricPoint K 1 (ζ ^ s.val)).1) =
        ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (X.b c))
    (t : (ZMod M)ˣ) :
    ((w₁ X K ζ t : F̄) : LaurentSeries K) =
      (tateLaurent K).c₄ * (1 + 12 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1) /
        (tateLaurent K).c₆ := by
  have hid := hK (t : ZMod M) (unit_ne_zero hM t)
  have e : ∀ (r : K) (x : LaurentSeries K), r • x = algebraMap K (LaurentSeries K) r * x := by
    intro r x
    rw [algebraMap_laurent_eq_C]
    exact HahnSeries.C_mul_eq_smul.symm
  simp only [e] at hid
  have hMne := natCast_laurent_ne_zero K hζ
  set Y : LaurentSeries K := 1 + 12 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 with hY
  have hcoe : ((w₁ X K ζ t : F̄) : LaurentSeries K) =
      algebraMap K (LaurentSeries K) (-((M : K)⁻¹ ^ 3)) *
        ∑ c : ZMod M, algebraMap K (LaurentSeries K) (ζ ^ ((t : ZMod M) * c).val) *
          (intSeriesC K (X.b c * eisenstein4) / intSeriesC K eisenstein6) := by
    simp only [w₁, IntermediateField.coe_mul, IntermediateField.coe_sum, coe_algebraMap, coe_β]
  have hsum : ∑ c : ZMod M, algebraMap K (LaurentSeries K) (ζ ^ ((t : ZMod M) * c).val) *
      (intSeriesC K (X.b c * eisenstein4) / intSeriesC K eisenstein6) =
      (M : LaurentSeries K) ^ 3 * Y * ((tateLaurent K).c₄ / -(tateLaurent K).c₆) := by
    rw [hid, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [intSeriesC_mul, intSeriesC_eisenstein4 K, intSeriesC_eisenstein6 K]
    ring
  rw [hcoe, hsum, map_neg, map_pow, map_inv₀, map_natCast, div_neg, mul_neg, neg_mul_neg, ← mul_assoc,
    ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hMne, one_pow, one_mul, mul_div_assoc', mul_comm Y]

theorem coe_w₂ {ζ : K} (hζ : IsPrimitiveRoot ζ M) (hM : 2 ≤ M)
    (hK : ∀ s : ZMod M, s ≠ 0 →
      (M : LaurentSeries K) ^ 5 *
          ((toricPoint K 1 (ζ ^ s.val)).1 + 6 * (toricPoint K 1 (ζ ^ s.val)).1 ^ 2 +
            2 * (tateLaurent K).a₄) =
        ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (X.d c))
    (t : (ZMod M)ˣ) :
    ((w₂ X K ζ t : F̄) : LaurentSeries K) =
      ((toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 +
          6 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 ^ 2 + 2 * (tateLaurent K).a₄) /
        (tateLaurent K).c₄ := by
  have hid := hK (t : ZMod M) (unit_ne_zero hM t)
  have e : ∀ (r : K) (x : LaurentSeries K), r • x = algebraMap K (LaurentSeries K) r * x := by
    intro r x
    rw [algebraMap_laurent_eq_C]
    exact HahnSeries.C_mul_eq_smul.symm
  simp only [e] at hid
  have hMne := natCast_laurent_ne_zero K hζ
  set Y : LaurentSeries K := (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 +
      6 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 ^ 2 + 2 * (tateLaurent K).a₄ with hY
  have hcoe : ((w₂ X K ζ t : F̄) : LaurentSeries K) =
      algebraMap K (LaurentSeries K) ((M : K)⁻¹ ^ 5) *
        ∑ c : ZMod M, algebraMap K (LaurentSeries K) (ζ ^ ((t : ZMod M) * c).val) *
          (intSeriesC K (X.d c) / intSeriesC K eisenstein4) := by
    simp only [w₂, IntermediateField.coe_mul, IntermediateField.coe_sum, coe_algebraMap, coe_δ]
  have hsum : ∑ c : ZMod M, algebraMap K (LaurentSeries K) (ζ ^ ((t : ZMod M) * c).val) *
      (intSeriesC K (X.d c) / intSeriesC K eisenstein4) =
      (M : LaurentSeries K) ^ 5 * Y / (tateLaurent K).c₄ := by
    rw [hid, Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [intSeriesC_eisenstein4 K]
    ring
  rw [hcoe, hsum, map_pow, map_inv₀, map_natCast, mul_div_assoc, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ hMne, one_pow, one_mul]

variable {ρ : Gamma0 M →*
  (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))}

set_option maxHeartbeats 3200000 in

theorem ρ_β (hρ : IsDiamondPullbackModL K M ⊥ ρ) (γ : Gamma0 M) (c : ZMod M) :
    ρ γ (β X K (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M))) = β X K c := by
  apply Subtype.ext
  rw [coe_β]
  exact hρ.coe_apply_eq γ (f := f6 X c) (g := E6Γ M)
    (f₁ := f6 X (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M))) (g₁ := E6Γ M)
    (pf := X.b c * eisenstein4) (pg := eisenstein6)
    (pf₁ := X.b (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M)) * eisenstein4) (pg₁ := eisenstein6)
    (isIntegralQExp_f6 X c) (isIntegralQExp_E6Γ M)
    (isIntegralQExp_f6 X (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M))) (isIntegralQExp_E6Γ M)
    (f6_slash X c γ γ.2).symm (by rw [coe_E6Γ, E6_slash]) (intSeriesC_eisenstein6_ne_zero K)
    (coe_β X K (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M)))

set_option maxHeartbeats 3200000 in

theorem ρ_δ (hρ : IsDiamondPullbackModL K M ⊥ ρ) (γ : Gamma0 M) (c : ZMod M) :
    ρ γ (δ X K (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M))) = δ X K c := by
  apply Subtype.ext
  rw [coe_δ]
  exact hρ.coe_apply_eq γ (f := DΓ X c) (g := E4Γ M)
    (f₁ := DΓ X (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M))) (g₁ := E4Γ M)
    (pf := X.d c) (pg := eisenstein4)
    (pf₁ := X.d (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M))) (pg₁ := eisenstein4)
    (isIntegralQExp_DΓ X c) (isIntegralQExp_E4Γ M)
    (isIntegralQExp_DΓ X (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M))) (isIntegralQExp_E4Γ M)
    (D_slash X c γ γ.2).symm (by rw [coe_E4Γ, E4_slash]) (intSeriesC_eisenstein4_ne_zero K)
    (coe_δ X K (c * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M)))

omit X in

theorem coe_gamma0Units_inv (γ : Gamma0 M) :
    (((CohCarrier.gamma0Units M γ)⁻¹ : (ZMod M)ˣ) : ZMod M) = (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) :=
  rfl

omit X in

theorem sum_reindex (ζ : K) (G : ZMod M → F̄) (t : ZMod M) (u : (ZMod M)ˣ) :
    ∑ c : ZMod M, ι (ζ ^ (t * c).val) * G (c * (u : ZMod M)) =
      ∑ c : ZMod M, ι (ζ ^ ((t * (u⁻¹ : (ZMod M)ˣ)) * c).val) * G c := by
  have h : ∀ c : ZMod M, ι (ζ ^ (t * c).val) * G (c * (u : ZMod M)) =
      (fun x => ι (ζ ^ ((t * (u⁻¹ : (ZMod M)ˣ)) * x).val) * G x) (Units.mulRight u c) := by
    intro c
    show _ = ι (ζ ^ ((t * (u⁻¹ : (ZMod M)ˣ)) * (c * (u : ZMod M))).val) * G (c * (u : ZMod M))
    congr 4
    rw [mul_assoc, ← mul_assoc ((u⁻¹ : (ZMod M)ˣ) : ZMod M), mul_comm ((u⁻¹ : (ZMod M)ˣ) : ZMod M) c,
      mul_assoc c, Units.inv_mul, mul_one]
  rw [Finset.sum_congr rfl fun c _ => h c]
  exact Equiv.sum_comp (Units.mulRight u) (fun x => ι (ζ ^ ((t * (u⁻¹ : (ZMod M)ˣ)) * x).val) * G x)

theorem ρ_w₁ (hρ : IsDiamondPullbackModL K M ⊥ ρ) (ζ : K) (γ : Gamma0 M) (t : (ZMod M)ˣ) :
    ρ γ (w₁ X K ζ t) = w₁ X K ζ (t * (CohCarrier.gamma0Units M γ)⁻¹) := by
  have key : ∀ c : ZMod M, ρ γ (β X K c) =
      β X K (c * ((CohCarrier.gamma0Units M γ : (ZMod M)ˣ) : ZMod M)) := by
    intro c
    have h := ρ_β X (K := K) hρ γ (c * ((CohCarrier.gamma0Units M γ : (ZMod M)ˣ) : ZMod M))
    rwa [mul_assoc, ← coe_gamma0Units_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      mul_one] at h
  rw [w₁, map_mul, AlgEquiv.commutes, map_sum]
  simp_rw [map_mul, AlgEquiv.commutes, key]
  rw [sum_reindex ζ (fun c => β X K c) (t : ZMod M) (CohCarrier.gamma0Units M γ), w₁, Units.val_mul]

theorem ρ_w₂ (hρ : IsDiamondPullbackModL K M ⊥ ρ) (ζ : K) (γ : Gamma0 M) (t : (ZMod M)ˣ) :
    ρ γ (w₂ X K ζ t) = w₂ X K ζ (t * (CohCarrier.gamma0Units M γ)⁻¹) := by
  have key : ∀ c : ZMod M, ρ γ (δ X K c) =
      δ X K (c * ((CohCarrier.gamma0Units M γ : (ZMod M)ˣ) : ZMod M)) := by
    intro c
    have h := ρ_δ X (K := K) hρ γ (c * ((CohCarrier.gamma0Units M γ : (ZMod M)ˣ) : ZMod M))
    rwa [mul_assoc, ← coe_gamma0Units_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      mul_one] at h
  rw [w₂, map_mul, AlgEquiv.commutes, map_sum]
  simp_rw [map_mul, AlgEquiv.commutes, key]
  rw [sum_reindex ζ (fun c => δ X K c) (t : ZMod M) (CohCarrier.gamma0Units M γ), w₂, Units.val_mul]

end Field

end W769
p2m_reactivate "P2MW.S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq.W769"

open ModularCurve WeierstrassCurve
open scoped MatrixGroups ModularForm

universe u in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (K : Type u) [Field K] (M : ℕ) (hM : 2 ≤ M) (ζ : K) (hζ : IsPrimitiveRoot ζ M) :
    ∃ w₁ w₂ : (ZMod M)ˣ → qExpFunctionFieldC K (CohCarrier.GammaH M ⊥),
      (∀ t : (ZMod M)ˣ, (w₁ t : LaurentSeries K) =
        (tateLaurent K).c₄ * (1 + 12 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1) /
          (tateLaurent K).c₆) ∧
      (∀ t : (ZMod M)ˣ, (w₂ t : LaurentSeries K) =
        ((toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 +
            6 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 ^ 2 + 2 * (tateLaurent K).a₄) /
          (tateLaurent K).c₄) ∧
      ∀ (ρ : CongruenceSubgroup.Gamma0 M →*
          (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
            qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))),
        IsDiamondPullbackModL K M ⊥ ρ →
        ∀ (γ : CongruenceSubgroup.Gamma0 M) (t : (ZMod M)ˣ),
          ρ γ (w₁ t) = w₁ (t * (CohCarrier.gamma0Units M γ)⁻¹) ∧
            ρ γ (w₂ t) = w₂ (t * (CohCarrier.gamma0Units M γ)⁻¹) := by
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨B, D, b, d, hb, hd, hslash, hK⟩ :=
    ModularCurve.exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum M
  let X : W769.FB M := ⟨B, D, b, d, hb, hd, fun c γ hγ => (hslash c γ hγ).1, fun c γ hγ => (hslash c γ hγ).2⟩
  have hK₁ := fun s hs => (hK K ζ hζ s hs).1
  have hK₂ := fun s hs => (hK K ζ hζ s hs).2
  exact ⟨W769.w₁ X K ζ, W769.w₂ X K ζ,
    fun t => W769.coe_w₁ X hζ hM hK₁ t, fun t => W769.coe_w₂ X hζ hM hK₂ t,
    fun ρ hρ γ t => ⟨W769.ρ_w₁ X hρ ζ γ t, W769.ρ_w₂ X hρ ζ γ t⟩⟩

end
p2m_reactivate "P2MW.S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq.W769"

end S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq
end P2MW
export P2MW.S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq (solution)
