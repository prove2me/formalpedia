-- Prove2me | solution 1 for ModularCurve.XOneP.ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/8b20b14d-8e8b-5389-b377-f4b97fff9c97

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_apply_eq_qExpansion_coeff_atkinLehnerSlash_and_slash_mul_eq_apply_aut_gamma1_mul
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
import Theorems.Thm_ModularCurve_exists_isDiamondAut
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0
import Theorems.Thm_ModularCurve_exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul
import Theorems.Thm_ModularCurve_coeffMap_injective
import Theorems.Thm_ModularCurve_coeffEmb_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul

set_option autoImplicit false

open scoped MatrixGroups ModularForm

namespace Conj6

open ModularCurve

section Laurent

variable {L : Type} [Field L] [CharZero L]

@[scoped simp] theorem coeffMap_coeff {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : LaurentSeries R) (n : ℤ) :
    (coeffMap f x).coeff n = f (x.coeff n) := rfl

theorem coeffMap_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (x : LaurentSeries R) : coeffMap g (coeffMap f x) = coeffMap (g.comp f) x := by
  ext n; rfl

theorem algebraMap_laurent_eq_C (c : L) : algebraMap L (LaurentSeries L) c = HahnSeries.C c := by
  rw [show algebraMap L (LaurentSeries L) c = HahnSeries.ofPowerSeries ℤ L (PowerSeries.C c) from rfl,
    HahnSeries.ofPowerSeries_C]

theorem coeffMap_C' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : R) :
    coeffMap f (HahnSeries.C c) = HahnSeries.C (f c) := by
  ext n
  simp only [coeffMap_coeff, HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs <;> simp

theorem coeffMap_algebraMap' (f : L →+* L) (c : L) :
    coeffMap f (algebraMap L (LaurentSeries L) c) = algebraMap L (LaurentSeries L) (f c) := by
  rw [algebraMap_laurent_eq_C, algebraMap_laurent_eq_C, coeffMap_C']

theorem coeffMap_aut_coeffEmb (s : L ≃ₐ[ℚ] L) (y : LaurentSeries ℚ) :
    coeffMap (s.toAlgHom.toRingHom) (coeffEmb L y) = coeffEmb L y := by
  ext n
  simp only [coeffMap_coeff, coeffEmb_coeff]
  exact s.commutes (y.coeff n)

end Laurent

section Ss

variable {L : Type} [Field L] [CharZero L] {K : IntermediateField L (LaurentSeries L)}
  (s : L ≃ₐ[ℚ] L) (Ss : ↥K ≃+* ↥K)
  (hSs : ∀ x : ↥K, ((Ss x : ↥K) : LaurentSeries L) = coeffMap (s.toAlgHom.toRingHom) ((x : ↥K) : LaurentSeries L))

include hSs

theorem Ss_algebraMap (c : L) : Ss (algebraMap L ↥K c) = algebraMap L ↥K (s c) := by
  apply Subtype.ext
  rw [hSs]
  exact coeffMap_algebraMap' _ c

theorem Ss_symm_algebraMap (c : L) : Ss.symm (algebraMap L ↥K c) = algebraMap L ↥K (s.symm c) := by
  apply Ss.injective
  rw [RingEquiv.apply_symm_apply, Ss_algebraMap s Ss hSs, AlgEquiv.apply_symm_apply]

theorem Ss_coeffEmb (y : LaurentSeries ℚ) (hy : coeffEmb L y ∈ K) : Ss ⟨coeffEmb L y, hy⟩ = ⟨coeffEmb L y, hy⟩ := by
  apply Subtype.ext
  rw [hSs]
  exact coeffMap_aut_coeffEmb s y

theorem Ss_symm_coeffEmb (y : LaurentSeries ℚ) (hy : coeffEmb L y ∈ K) : Ss.symm ⟨coeffEmb L y, hy⟩ = ⟨coeffEmb L y, hy⟩ := by
  apply Ss.injective
  rw [RingEquiv.apply_symm_apply, Ss_coeffEmb s Ss hSs]

noncomputable def Lam (σ : ↥K ≃ₐ[L] ↥K) : ↥K →ₐ[L] ↥K where
  toFun x := Ss (σ (Ss.symm x))
  map_one' := by simp
  map_mul' x y := by simp
  map_zero' := by simp
  map_add' x y := by simp
  commutes' c := by
    rw [Ss_symm_algebraMap s Ss hSs, AlgEquiv.commutes, Ss_algebraMap s Ss hSs, AlgEquiv.apply_symm_apply]

theorem Lam_apply (σ : ↥K ≃ₐ[L] ↥K) (x : ↥K) : Lam s Ss hSs σ x = Ss (σ (Ss.symm x)) := rfl

end Ss

section Diamond

variable (N : ℕ) [NeZero N] (L : Type) [Field L] [CharZero L]

theorem exists_isBaseChangeAutOf_diamondAut (d : ℕ) :
    ∃ τ : ↥(laurentBaseChange L (x1FunctionField N)) ≃ₐ[L] ↥(laurentBaseChange L (x1FunctionField N)),
      IsBaseChangeAutOf L (diamondAut N d) τ := by
  obtain ⟨τ, hτ⟩ := exists_algEquiv_laurentBaseChange_cover L (x1FunctionField N) (diamondAut N d).toRingEquiv
  exact ⟨τ, fun y => hτ y⟩

private theorem _root_.Conj6.pinned_apply_coeffEmb (d : ℕ)
    (θ : ↥(laurentBaseChange L (x1FunctionField N)) ≃ₐ[L] ↥(laurentBaseChange L (x1FunctionField N)))
    (hθ : ∀ (x x' : ↥(laurentBaseChange L (x1FunctionField N))), (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥(laurentBaseChange L (x1FunctionField N))) : LaurentSeries L) =
          ((baseChangeAut L (diamondAut N d) x' : ↥(laurentBaseChange L (x1FunctionField N))) : LaurentSeries L))
    (z : x1FunctionField N) :
    θ ⟨coeffEmb L (z : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L z.2⟩ =
      ⟨coeffEmb L ((diamondAut N d z : x1FunctionField N) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L (diamondAut N d z).2⟩ := by
  apply Subtype.ext
  rw [hθ _ ⟨coeffEmb L (z : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L z.2⟩ rfl]
  exact isBaseChangeAutOf_baseChangeAut (exists_isBaseChangeAutOf_diamondAut N L d) z

p2m_export "Conj6" "pinned_apply_coeffEmb"
end Diamond

section Gen

noncomputable def embK (N : ℕ) (L : Type) [Field L] [CharZero L] :
    ↥(x1FunctionField N) →+* ↥(laurentBaseChange L (x1FunctionField N)) where
  toFun z := ⟨coeffEmb L (z : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L z.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem coe_embK (N : ℕ) (L : Type) [Field L] [CharZero L] (z : ↥(x1FunctionField N)) :
    ((embK N L z : ↥(laurentBaseChange L (x1FunctionField N))) : LaurentSeries L) = coeffEmb L (z : LaurentSeries ℚ) := rfl

end Gen

section Ext

variable (N : ℕ) [NeZero N] (L : Type) [Field L] [CharZero L]

local notation "KB" => laurentBaseChange L (x1FunctionField N)

theorem algHom_ext_of_ratios (Φ Ψ : ↥KB →ₐ[L] ↥KB)
    (h : ∀ (r : LaurentSeries ℚ) (hr : r ∈ intFormRatiosC ℚ (CongruenceSubgroup.Gamma1 N)),
      Φ ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (intFormRatiosC_subset ℚ _ hr)⟩ =
        Ψ ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (intFormRatiosC_subset ℚ _ hr)⟩) :
    Φ = Ψ := by

  let α : ↥(x1FunctionField N) →+* ↥KB := Φ.toRingHom.comp (embK N L)
  let β : ↥(x1FunctionField N) →+* ↥KB := Ψ.toRingHom.comp (embK N L)
  have hz : ∀ z : ↥(x1FunctionField N), Φ (embK N L z) = Ψ (embK N L z) := by
    rintro ⟨z, hz⟩
    change α ⟨z, hz⟩ = β ⟨z, hz⟩
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx => exact h x hx
    | algebraMap c =>
      have : (⟨algebraMap ℚ (LaurentSeries ℚ) c, (x1FunctionField N).algebraMap_mem c⟩ : ↥(x1FunctionField N))
          = ((c : ℚ) : ↥(x1FunctionField N)) := by
        apply Subtype.ext; simp
      rw [this, map_ratCast, map_ratCast]
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, _⟩ : ↥(x1FunctionField N)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add, map_add, ihx, ihy]
    | inv x hx ih =>
      have : (⟨x⁻¹, _⟩ : ↥(x1FunctionField N)) = (⟨x, hx⟩ : ↥(x1FunctionField N))⁻¹ := rfl
      rw [this, map_inv₀, map_inv₀, ih]
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, _⟩ : ↥(x1FunctionField N)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, map_mul, ihx, ihy]

  apply IntermediateField.algHom_ext_of_eq_adjoin L (S := KB)
    (s := ⇑(coeffEmb L) '' (x1FunctionField N : Set (LaurentSeries ℚ))) rfl
  rintro _ ⟨z, hz0, rfl⟩
  exact hz ⟨z, hz0⟩

end Ext

end Conj6
p2m_reactivate "P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6"

namespace Conj6

open ModularCurve

section Qc

noncomputable def Qc (F : UpperHalfPlane → ℂ) : LaurentSeries ℂ :=
  HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 F)

abbrev Γ1 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods_Γ1 {N : ℕ} : (1 : ℝ) ∈ (Γ1 N).strictPeriods := by simp [Γ1]

theorem Qc_coe_smul {N : ℕ} {k : ℤ} (c : ℂ) (F : ModularForm (Γ1 N) k) :
    Qc (⇑(c • F) : UpperHalfPlane → ℂ) = HahnSeries.C c * Qc (⇑F : UpperHalfPlane → ℂ) := by
  rw [Qc, Qc, ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_Γ1 c F,
    PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C]

theorem Qc_of_eq_smul {N : ℕ} {k : ℤ} (G : UpperHalfPlane → ℂ) (c : ℂ) (F : ModularForm (Γ1 N) k)
    (h : G = c • (⇑F : UpperHalfPlane → ℂ)) : Qc G = HahnSeries.C c * Qc (⇑F : UpperHalfPlane → ℂ) := by
  rw [h, ← ModularForm.IsGLPos.coe_smul, Qc_coe_smul]

theorem Qc_eq_zero_iff {N : ℕ} {k : ℤ} (F : ModularForm (Γ1 N) k) : Qc (⇑F : UpperHalfPlane → ℂ) = 0 ↔ F = 0 := by
  rw [Qc, map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective,
    ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_Γ1 F]

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (P : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R P) = HahnSeries.ofPowerSeries ℤ S (P.map f) := by
  ext n
  simp only [coeffMap_coeff]
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · exact map_zero f
  · rw [PowerSeries.coeff_map]

end Qc
p2m_reactivate "P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6"

end Conj6
p2m_reactivate "P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6"

namespace Conj6

open ModularCurve

namespace RHS

abbrev Γ1 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

abbrev MF (N : ℕ) (k : ℤ) := ModularForm (Γ1 N) k

variable {N : ℕ}

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ1 N).strictPeriods := by
  simp [Γ1]

theorem Qc_coe_smul {k : ℤ} (c : ℂ) (F : MF N k) :
    Qc (⇑(c • F) : UpperHalfPlane → ℂ) = HahnSeries.C c * Qc (⇑F : UpperHalfPlane → ℂ) := by
  rw [Qc, Qc, ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c,
    PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C]

theorem Qc_coe_eq_zero_iff {k : ℤ} (F : MF N k) : Qc (⇑F : UpperHalfPlane → ℂ) = 0 ↔ F = 0 := by
  rw [Qc, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods F]
  exact ⟨fun h => HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩

theorem Qc_coe_eq_intSeriesC {k : ℤ} {F : MF N k} {r : PowerSeries ℤ} (h : IsIntegralQExp F r) :
    Qc (⇑F : UpperHalfPlane → ℂ) = intSeriesC ℂ r := by
  rw [Qc, intSeriesC, ← h]

theorem Qc_eq_of_coe_eq_smul {k : ℤ} (F : MF N k) {a : ℂ} (ha : a ≠ 0) {A : UpperHalfPlane → ℂ}
    (h : (⇑F : UpperHalfPlane → ℂ) = a • A) :
    Qc A = HahnSeries.C a⁻¹ * Qc (⇑F : UpperHalfPlane → ℂ) := by
  have hA : A = (⇑(a⁻¹ • F) : UpperHalfPlane → ℂ) := by
    rw [ModularForm.IsGLPos.coe_smul, h, inv_smul_smul₀ ha]
  rw [hA, Qc_coe_smul]

theorem coeffEmb_intSeriesC (r : PowerSeries ℤ) : coeffEmb ℂ (intSeriesC ℚ r) = intSeriesC ℂ r := by
  ext k
  simp only [coeffEmb, coeffMap_coeff, intSeriesC]
  rcases lt_or_ge k 0 with hk | hk
  · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hk, ModularCurve.ofPowerSeries_coeff_of_neg _ hk, map_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_map]
    simp

theorem intSeriesC_ne_zero_iff (r : PowerSeries ℤ) : intSeriesC ℂ r ≠ 0 ↔ intSeriesC ℚ r ≠ 0 := by
  rw [← coeffEmb_intSeriesC]
  exact map_ne_zero_iff _ (ModularCurve.coeffEmb_injective ℂ)

theorem coeffEmb_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (r : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap L (LaurentSeries L) (algebraMap ℚ L r) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single]

theorem coeffEmb_complex_algebraMap (r : ℚ) :
    coeffEmb ℂ (algebraMap ℚ (LaurentSeries ℚ) r) = HahnSeries.C (algebraMap ℚ ℂ r) := by
  rw [coeffEmb_algebraMap, algebraMap_laurentSeries_eq_single]
  rfl

theorem ringHom_algebraMap_rat {L : Type*} [Field L] [CharZero L] (ι : L →+* ℂ) (q : ℚ) :
    ι (algebraMap ℚ L q) = algebraMap ℚ ℂ q :=
  RingHom.congr_fun (Subsingleton.elim (ι.comp (algebraMap ℚ L)) (algebraMap ℚ ℂ)) q

theorem coeffMap_algebraMap_eq_C {L : Type*} [Field L] (ι : L →+* ℂ) (c : L) :
    coeffMap ι (algebraMap L (LaurentSeries L) c) = HahnSeries.C (ι c) := by
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single]
  rfl

section Diamond

variable (N : ℕ) [NeZero N] (L : Type) [Field L] [CharZero L]

theorem exists_isBaseChangeAutOf_diamondAut (d : ℕ) :
    ∃ τ : ↥(laurentBaseChange L (x1FunctionField N)) ≃ₐ[L] ↥(laurentBaseChange L (x1FunctionField N)),
      IsBaseChangeAutOf L (diamondAut N d) τ := by
  obtain ⟨τ, hτ⟩ := exists_algEquiv_laurentBaseChange_cover L (x1FunctionField N) (diamondAut N d).toRingEquiv
  exact ⟨τ, fun y => hτ y⟩

theorem pinned_apply_coeffEmb (d : ℕ)
    (θ : ↥(laurentBaseChange L (x1FunctionField N)) ≃ₐ[L] ↥(laurentBaseChange L (x1FunctionField N)))
    (hθ : ∀ (x x' : ↥(laurentBaseChange L (x1FunctionField N))), (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥(laurentBaseChange L (x1FunctionField N))) : LaurentSeries L) =
          ((baseChangeAut L (diamondAut N d) x' : ↥(laurentBaseChange L (x1FunctionField N))) : LaurentSeries L))
    (z : x1FunctionField N) :
    θ ⟨coeffEmb L (z : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L z.2⟩ =
      ⟨coeffEmb L ((diamondAut N d z : x1FunctionField N) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange L (diamondAut N d z).2⟩ := by
  apply Subtype.ext
  rw [hθ _ ⟨coeffEmb L (z : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L z.2⟩ rfl]
  exact isBaseChangeAutOf_baseChangeAut (exists_isBaseChangeAutOf_diamondAut N L d) z

end Diamond
p2m_reactivate "P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6"

theorem coe_algebraMap_mul {L : Type*} [Field L] {K : IntermediateField L (LaurentSeries L)} (c : L) (y : ↥K) :
    ((algebraMap L ↥K c * y : ↥K) : LaurentSeries L) = algebraMap L (LaurentSeries L) c * (y : LaurentSeries L) := by
  rw [MulMemClass.coe_mul]
  rfl

theorem dilate_slash_smul (k : ℤ) (p : ℕ) (a : ℂ) (F : UpperHalfPlane → ℂ) (γ : SL(2, ℤ)) :
    (fun τ : UpperHalfPlane => ((a • F) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) =
      a • fun τ : UpperHalfPlane => (F ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ) := by
  funext τ
  rw [ModularForm.SL_smul_slash, Pi.smul_apply, Pi.smul_apply]

end RHS
p2m_reactivate "P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6"

open RHS in

theorem rhs_identity
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) (L : Type) [Field L] [CharZero L]
    (σ θ : ↥(laurentBaseChange L (x1FunctionField (M * p))) ≃ₐ[L] ↥(laurentBaseChange L (x1FunctionField (M * p))))
    (ι : L →+* ℂ) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1)
    (hW : ∀ (k : ℤ) (f g : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ),
          ModularCurve.IsIntegralQExp f pf → ModularCurve.IsIntegralQExp g pg → ModularCurve.intSeriesC ℚ pg ≠ 0 →
          ∀ x : ↥(laurentBaseChange L (x1FunctionField (M * p))),
            (x : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg) →
          ∃ (φf φg : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (Df Dg : ℤ), Df ≠ 0 ∧ Dg ≠ 0 ∧
            (⇑φf : UpperHalfPlane → ℂ) = (Df : ℂ) • (fun τ : UpperHalfPlane => ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∧
            (⇑φg : UpperHalfPlane → ℂ) = (Dg : ℂ) • (fun τ : UpperHalfPlane => ((⇑g : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∧
            (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (r : Fin n → PowerSeries ℤ),
              (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧ φf = ∑ i, (ι (c i)) • F i) ∧
            (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (r : Fin n → PowerSeries ℤ),
              (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧ φg = ∑ i, (ι (c i)) • F i) ∧
            ModularCurve.coeffMap ι ((σ x : ↥(laurentBaseChange L (x1FunctionField (M * p)))) : LaurentSeries L) * HahnSeries.C (Df : ℂ) *
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φg : UpperHalfPlane → ℂ)) =
              HahnSeries.C (Dg : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φf : UpperHalfPlane → ℂ)))
    (b' : ℕ) (hb' : b'.Coprime (M * p))
    (hθ : ∀ (x x' : ↥(laurentBaseChange L (x1FunctionField (M * p)))), (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥(laurentBaseChange L (x1FunctionField (M * p)))) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) b') x' : ↥(laurentBaseChange L (x1FunctionField (M * p)))) : LaurentSeries L))
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 (M * p)) (hδ00 : ((δ 0 0 : ℤ) : ZMod (M * p)) = (b' : ZMod (M * p)))
    {k : ℤ} (f g : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ)
    (hf : ModularCurve.IsIntegralQExp f pf) (hg : ModularCurve.IsIntegralQExp g pg) (hg0 : ModularCurve.intSeriesC ℚ pg ≠ 0)
    (x : ↥(laurentBaseChange L (x1FunctionField (M * p))))
    (hx : (x : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg)) :
    ModularCurve.coeffMap ι ((σ (θ x) : ↥(laurentBaseChange L (x1FunctionField (M * p)))) : LaurentSeries L)
        * Qc (fun τ : UpperHalfPlane => (((⇑g : UpperHalfPlane → ℂ) ∣[k] δ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))
      = Qc (fun τ : UpperHalfPlane => (((⇑f : UpperHalfPlane → ℂ) ∣[k] δ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp.ne_zero⟩

  set z₀ : ↥(x1FunctionField (M * p)) :=
    ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ with hz₀
  have hx' : x = ⟨coeffEmb L (z₀ : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L z₀.2⟩ := Subtype.ext hx

  have hθx : θ x = ⟨coeffEmb L ((diamondAut (M * p) b' z₀ : ↥(x1FunctionField (M * p))) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange L (diamondAut (M * p) b' z₀).2⟩ := by
    rw [hx']
    exact RHS.pinned_apply_coeffEmb (M * p) L b' θ hθ z₀
  set y : LaurentSeries ℚ := ((diamondAut (M * p) b' z₀ : ↥(x1FunctionField (M * p))) : LaurentSeries ℚ) with hy

  have hD : IsDiamondAut (M * p) b' (diamondAut (M * p) b') :=
    isDiamondAut_diamondAut (exists_isDiamondAut (M * p) hb')
  have h2 : coeffEmb ℂ y * Qc ((⇑g : UpperHalfPlane → ℂ) ∣[k] δ) = Qc ((⇑f : UpperHalfPlane → ℂ) ∣[k] δ) :=
    hD.2 k f g pf pg hf hg hg0 δ hδ hδ00

  obtain ⟨D₁, f₁, p₁, hD₁, hf₁, hf₁eq⟩ := exists_isIntegralQExp_smul_slash_of_mem_Gamma0 (M * p) f hf δ hδ
  obtain ⟨D₂, g₁, p₂, hD₂, hg₁, hg₁eq⟩ := exists_isIntegralQExp_smul_slash_of_mem_Gamma0 (M * p) g hg δ hδ
  have hD₁C : (D₁ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hD₁
  have hD₂C : (D₂ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hD₂
  have hQf : Qc ((⇑f : UpperHalfPlane → ℂ) ∣[k] δ) = HahnSeries.C (D₁ : ℂ)⁻¹ * intSeriesC ℂ p₁ := by
    rw [Qc_eq_of_coe_eq_smul f₁ hD₁C hf₁eq, Qc_coe_eq_intSeriesC hf₁]
  have hQg : Qc ((⇑g : UpperHalfPlane → ℂ) ∣[k] δ) = HahnSeries.C (D₂ : ℂ)⁻¹ * intSeriesC ℂ p₂ := by
    rw [Qc_eq_of_coe_eq_smul g₁ hD₂C hg₁eq, Qc_coe_eq_intSeriesC hg₁]

  have hg_ne : g ≠ 0 := by
    intro h0
    apply hg0
    have hq : UpperHalfPlane.qExpansion 1 (⇑g : UpperHalfPlane → ℂ) = 0 := by
      rw [h0, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero]
    have hpg : pg = 0 := by
      ext n
      have := hg.coeff n
      rw [hq, map_zero, Int.cast_eq_zero] at this
      rw [this, map_zero]
    rw [hpg, intSeriesC_zero]
  have hP₂ : intSeriesC ℂ p₂ ≠ 0 := by
    rw [← Qc_coe_eq_intSeriesC hg₁, Ne, Qc_coe_eq_zero_iff]
    intro h0
    apply hg_ne
    have hsl : (⇑g : UpperHalfPlane → ℂ) ∣[k] δ = 0 := by
      have h' := hg₁eq
      rw [h0, ModularForm.coe_zero] at h'
      exact (smul_eq_zero.mp h'.symm).resolve_left hD₂C
    have hcoe : (⇑g : UpperHalfPlane → ℂ) = 0 := by
      calc (⇑g : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[k] δ) ∣[k] δ⁻¹ := by
            rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
        _ = 0 := by rw [hsl, SlashAction.zero_slash]
    exact DFunLike.ext' (hcoe.trans ModularForm.coe_zero.symm)
  have hP₂Q : intSeriesC ℚ p₂ ≠ 0 := (intSeriesC_ne_zero_iff p₂).mp hP₂

  obtain ⟨q, hq⟩ : ∃ q : ℚ, algebraMap ℚ ℂ q = (D₂ : ℂ) / (D₁ : ℂ) :=
    ⟨(D₂ : ℚ) / (D₁ : ℚ), by rw [eq_ratCast, Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]⟩
  have hC₁ : HahnSeries.C (D₁ : ℂ) ≠ (0 : LaurentSeries ℂ) := HahnSeries.C_ne_zero hD₁C
  have hC₂ : HahnSeries.C (D₂ : ℂ) ≠ (0 : LaurentSeries ℂ) := HahnSeries.C_ne_zero hD₂C
  have hy_eq : y = algebraMap ℚ (LaurentSeries ℚ) q * (intSeriesC ℚ p₁ / intSeriesC ℚ p₂) := by
    apply ModularCurve.coeffEmb_injective ℂ
    rw [hQf, hQg, map_inv₀, map_inv₀] at h2
    rw [map_mul, coeffEmb_complex_algebraMap, hq, map_div₀ (coeffEmb ℂ), coeffEmb_intSeriesC, coeffEmb_intSeriesC,
      map_div₀]
    calc coeffEmb ℂ y
        = coeffEmb ℂ y * ((HahnSeries.C (D₂ : ℂ))⁻¹ * HahnSeries.C (D₂ : ℂ)) *
            (intSeriesC ℂ p₂ * (intSeriesC ℂ p₂)⁻¹) := by
          rw [inv_mul_cancel₀ hC₂, mul_inv_cancel₀ hP₂, mul_one, mul_one]
      _ = coeffEmb ℂ y * ((HahnSeries.C (D₂ : ℂ))⁻¹ * intSeriesC ℂ p₂) *
            (HahnSeries.C (D₂ : ℂ) * (intSeriesC ℂ p₂)⁻¹) := by ring
      _ = (HahnSeries.C (D₁ : ℂ))⁻¹ * intSeriesC ℂ p₁ * (HahnSeries.C (D₂ : ℂ) * (intSeriesC ℂ p₂)⁻¹) := by rw [h2]
      _ = HahnSeries.C (D₂ : ℂ) / HahnSeries.C (D₁ : ℂ) * (intSeriesC ℂ p₁ / intSeriesC ℂ p₂) := by ring

  set x₁ : ↥(laurentBaseChange L (x1FunctionField (M * p))) :=
    ⟨coeffEmb L (intSeriesC ℚ p₁ / intSeriesC ℚ p₂),
      coeffEmb_mem_laurentBaseChange L (div_mem_qExpFunctionFieldC f₁ g₁ hf₁ hg₁ hP₂Q)⟩ with hx₁
  have hθx' : θ x = algebraMap L ↥(laurentBaseChange L (x1FunctionField (M * p))) (algebraMap ℚ L q) * x₁ := by
    apply Subtype.ext
    rw [hθx, coe_algebraMap_mul]
    change coeffEmb L y =
      algebraMap L (LaurentSeries L) (algebraMap ℚ L q) * coeffEmb L (intSeriesC ℚ p₁ / intSeriesC ℚ p₂)
    rw [hy_eq, map_mul, coeffEmb_algebraMap L q]
  have hιq : ι (algebraMap ℚ L q) = (D₂ : ℂ) / (D₁ : ℂ) := by
    rw [ringHom_algebraMap_rat, hq]

  obtain ⟨φf, φg, Df, Dg, hDf, hDg, hφf, hφg, -, -, hWeq⟩ := hW k f₁ g₁ p₁ p₂ hf₁ hg₁ hP₂Q x₁ rfl
  have hDfC : (Df : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hDf
  have hDgC : (Dg : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hDg
  have hCf : HahnSeries.C (Df : ℂ) ≠ (0 : LaurentSeries ℂ) := HahnSeries.C_ne_zero hDfC
  have hCg : HahnSeries.C (Dg : ℂ) ≠ (0 : LaurentSeries ℂ) := HahnSeries.C_ne_zero hDgC

  have hφf' : (⇑φf : UpperHalfPlane → ℂ) = ((Df : ℂ) * (D₁ : ℂ)) •
      fun τ : UpperHalfPlane => (((⇑f : UpperHalfPlane → ℂ) ∣[k] δ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ) := by
    rw [hφf, hf₁eq, dilate_slash_smul, smul_smul]
  have hφg' : (⇑φg : UpperHalfPlane → ℂ) = ((Dg : ℂ) * (D₂ : ℂ)) •
      fun τ : UpperHalfPlane => (((⇑g : UpperHalfPlane → ℂ) ∣[k] δ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ) := by
    rw [hφg, hg₁eq, dilate_slash_smul, smul_smul]
  have hQAf := Qc_eq_of_coe_eq_smul φf (mul_ne_zero hDfC hD₁C) hφf'
  have hQAg := Qc_eq_of_coe_eq_smul φg (mul_ne_zero hDgC hD₂C) hφg'

  change coeffMap ι ((σ x₁ : ↥(laurentBaseChange L (x1FunctionField (M * p)))) : LaurentSeries L) *
      HahnSeries.C (Df : ℂ) * Qc (⇑φg : UpperHalfPlane → ℂ) = HahnSeries.C (Dg : ℂ) * Qc (⇑φf : UpperHalfPlane → ℂ) at hWeq
  rw [hθx', map_mul σ, AlgEquiv.commutes, coe_algebraMap_mul, map_mul (coeffMap ι), coeffMap_algebraMap_eq_C, hιq,
    hQAf, hQAg, map_inv₀, map_inv₀, map_mul HahnSeries.C, map_mul HahnSeries.C, map_div₀]

  refine mul_left_cancel₀ (mul_ne_zero hCf hC₁) ?_
  calc HahnSeries.C (Df : ℂ) * HahnSeries.C (D₁ : ℂ) *
        (HahnSeries.C (D₂ : ℂ) / HahnSeries.C (D₁ : ℂ) *
          coeffMap ι ((σ x₁ : ↥(laurentBaseChange L (x1FunctionField (M * p)))) : LaurentSeries L) *
          ((HahnSeries.C (Dg : ℂ) * HahnSeries.C (D₂ : ℂ))⁻¹ * Qc (⇑φg : UpperHalfPlane → ℂ)))
      = (coeffMap ι ((σ x₁ : ↥(laurentBaseChange L (x1FunctionField (M * p)))) : LaurentSeries L) *
            HahnSeries.C (Df : ℂ) * Qc (⇑φg : UpperHalfPlane → ℂ)) *
          (HahnSeries.C (D₁ : ℂ) / HahnSeries.C (D₁ : ℂ)) *
          (HahnSeries.C (D₂ : ℂ) * (HahnSeries.C (Dg : ℂ) * HahnSeries.C (D₂ : ℂ))⁻¹) := by ring
    _ = HahnSeries.C (Dg : ℂ) * Qc (⇑φf : UpperHalfPlane → ℂ) * 1 *
          (HahnSeries.C (D₂ : ℂ) * (HahnSeries.C (Dg : ℂ) * HahnSeries.C (D₂ : ℂ))⁻¹) := by rw [hWeq, div_self hC₁]
    _ = Qc (⇑φf : UpperHalfPlane → ℂ) *
          ((HahnSeries.C (Dg : ℂ) * HahnSeries.C (D₂ : ℂ)) * (HahnSeries.C (Dg : ℂ) * HahnSeries.C (D₂ : ℂ))⁻¹) := by
          ring
    _ = Qc (⇑φf : UpperHalfPlane → ℂ) := by rw [mul_inv_cancel₀ (mul_ne_zero hCg hC₂), mul_one]
    _ = HahnSeries.C (Df : ℂ) * HahnSeries.C (D₁ : ℂ) *
          ((HahnSeries.C (Df : ℂ) * HahnSeries.C (D₁ : ℂ))⁻¹ * Qc (⇑φf : UpperHalfPlane → ℂ)) := by
          rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero hCf hC₁), one_mul]

end Conj6
p2m_reactivate "P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6"

namespace Conj6

open ModularCurve

namespace LHS

abbrev Γ1 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods {N : ℕ} : (1 : ℝ) ∈ (Γ1 N).strictPeriods := by
  simp [Γ1]

theorem Qc_coe_smul {N : ℕ} {k : ℤ} (c : ℂ) (F : ModularForm (Γ1 N) k) :
    Qc (⇑(c • F) : UpperHalfPlane → ℂ) = HahnSeries.C c * Qc (⇑F : UpperHalfPlane → ℂ) := by
  rw [Qc, Qc, ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c,
    PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C]

theorem Qc_of_eq_smul {N : ℕ} {k : ℤ} (G : UpperHalfPlane → ℂ) (c : ℂ) (F : ModularForm (Γ1 N) k)
    (h : G = c • (⇑F : UpperHalfPlane → ℂ)) : Qc G = HahnSeries.C c * Qc (⇑F : UpperHalfPlane → ℂ) := by
  rw [h, ← ModularForm.IsGLPos.coe_smul, Qc_coe_smul]

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (P : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R P) = HahnSeries.ofPowerSeries ℤ S (P.map f) := by
  ext n
  simp only [coeffMap_coeff]
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · exact map_zero f
  · rw [PowerSeries.coeff_map]

theorem castHom_natCast_eq {M p : ℕ} (δ00 : ℤ) (b' : ℕ) (h : ((δ00 : ℤ) : ZMod (M * p)) = (b' : ZMod (M * p)))
    (q : ℕ) (hq : q ∣ M * p) : ((δ00 : ℤ) : ZMod q) = (b' : ZMod q) := by
  have := congrArg (ZMod.castHom hq (ZMod q)) h
  rwa [map_intCast, map_natCast] at this

end LHS
p2m_reactivate "P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6"

open LHS in

theorem lhs_identity
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L] (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (σ : ↥(laurentBaseChange L (x1FunctionField (M * p))) ≃ₐ[L] ↥(laurentBaseChange L (x1FunctionField (M * p))))
    (ι : L →+* ℂ) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1)
    (hW : ∀ (k : ℤ) (f g : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ),
          ModularCurve.IsIntegralQExp f pf → ModularCurve.IsIntegralQExp g pg → ModularCurve.intSeriesC ℚ pg ≠ 0 →
          ∀ x : ↥(laurentBaseChange L (x1FunctionField (M * p))),
            (x : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg) →
          ∃ (φf φg : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (Df Dg : ℤ), Df ≠ 0 ∧ Dg ≠ 0 ∧
            (⇑φf : UpperHalfPlane → ℂ) = (Df : ℂ) • (fun τ : UpperHalfPlane => ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∧
            (⇑φg : UpperHalfPlane → ℂ) = (Dg : ℂ) • (fun τ : UpperHalfPlane => ((⇑g : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∧
            (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (r : Fin n → PowerSeries ℤ),
              (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧ φf = ∑ i, (ι (c i)) • F i) ∧
            (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (r : Fin n → PowerSeries ℤ),
              (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧ φg = ∑ i, (ι (c i)) • F i) ∧
            ModularCurve.coeffMap ι ((σ x : ↥(laurentBaseChange L (x1FunctionField (M * p)))) : LaurentSeries L) * HahnSeries.C (Df : ℂ) *
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φg : UpperHalfPlane → ℂ)) =
              HahnSeries.C (Dg : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φf : UpperHalfPlane → ℂ)))
    (s : L ≃ₐ[ℚ] L) (b : ℕ) (hb : b.Coprime p) (hs : s ζ = ζ ^ b) (b' : ℕ)
    (hb'M : ((b' : ZMod M) = 1)) (hb'p : ((b' : ZMod p) = (b : ZMod p)))
    (Ss : ↥(laurentBaseChange L (x1FunctionField (M * p))) ≃+* ↥(laurentBaseChange L (x1FunctionField (M * p))))
    (hSs : ∀ x : ↥(laurentBaseChange L (x1FunctionField (M * p))),
      ((Ss x : ↥(laurentBaseChange L (x1FunctionField (M * p)))) : LaurentSeries L) =
        ModularCurve.coeffMap (s.toAlgHom.toRingHom) ((x : ↥(laurentBaseChange L (x1FunctionField (M * p)))) : LaurentSeries L))
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 (M * p)) (hδ00 : ((δ 0 0 : ℤ) : ZMod (M * p)) = (b' : ZMod (M * p)))
    {k : ℤ} (hk : Even k) (f g : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ)
    (hf : ModularCurve.IsIntegralQExp f pf) (hg : ModularCurve.IsIntegralQExp g pg) (hg0 : ModularCurve.intSeriesC ℚ pg ≠ 0)
    (x : ↥(laurentBaseChange L (x1FunctionField (M * p))))
    (hx : (x : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg)) :
    ModularCurve.coeffMap ι ((Ss (σ x) : ↥(laurentBaseChange L (x1FunctionField (M * p)))) : LaurentSeries L)
        * Qc (fun τ : UpperHalfPlane => (((⇑g : UpperHalfPlane → ℂ) ∣[k] δ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))
      = Qc (fun τ : UpperHalfPlane => (((⇑f : UpperHalfPlane → ℂ) ∣[k] δ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) := by
  classical

  obtain ⟨φf, φg, Df, Dg, hDf, hDg, hφf, hφg, -, -, hrel⟩ := hW k f g pf pg hf hg hg0 x hx
  obtain ⟨Ff, hFf⟩ := ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul p M hpM f γ hγ hγp
  obtain ⟨Fg, hFg⟩ := ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul p M hpM g γ hγ hγp
  have hQφf : Qc (⇑φf : UpperHalfPlane → ℂ) = HahnSeries.C (Df : ℂ) * Qc (⇑Ff : UpperHalfPlane → ℂ) :=
    Qc_of_eq_smul _ _ Ff (by rw [hφf, hFf])
  have hQφg : Qc (⇑φg : UpperHalfPlane → ℂ) = HahnSeries.C (Dg : ℂ) * Qc (⇑Fg : UpperHalfPlane → ℂ) :=
    Qc_of_eq_smul _ _ Fg (by rw [hφg, hFg])

  have hCf : HahnSeries.C (Df : ℂ) ≠ (0 : LaurentSeries ℂ) := HahnSeries.C_ne_zero (Int.cast_ne_zero.mpr hDf)
  have hCg : HahnSeries.C (Dg : ℂ) ≠ (0 : LaurentSeries ℂ) := HahnSeries.C_ne_zero (Int.cast_ne_zero.mpr hDg)
  have hstar : coeffMap ι ((σ x : ↥(laurentBaseChange L (x1FunctionField (M * p)))) : LaurentSeries L)
      * Qc (⇑Fg : UpperHalfPlane → ℂ) = Qc (⇑Ff : UpperHalfPlane → ℂ) := by
    have h1 := hrel
    rw [show HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φg : UpperHalfPlane → ℂ)) = Qc ⇑φg from rfl,
      show HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φf : UpperHalfPlane → ℂ)) = Qc ⇑φf from rfl,
      hQφg, hQφf] at h1
    apply mul_left_cancel₀ (mul_ne_zero hCf hCg)
    linear_combination h1

  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hδM : ((δ 0 0 : ℤ) : ZMod M) = 1 := by
    rw [castHom_natCast_eq (M := M) (p := p) (δ 0 0) b' hδ00 M (dvd_mul_right M p), hb'M]
  have hδp : ((δ 0 0 : ℤ) : ZMod p) = (b : ZMod p) := by
    rw [castHom_natCast_eq (M := M) (p := p) (δ 0 0) b' hδ00 p (dvd_mul_left p M), hb'p]

  choose zf hzf hzf' using fun n =>
    ModularCurve.exists_apply_eq_qExpansion_coeff_atkinLehnerSlash_and_slash_mul_eq_apply_aut_gamma1_mul
      p M hpM hk f hf γ hγ hγp L ζ hζ ι s b hb hs δ hδ hδp hδM n
  choose zg hzg hzg' using fun n =>
    ModularCurve.exists_apply_eq_qExpansion_coeff_atkinLehnerSlash_and_slash_mul_eq_apply_aut_gamma1_mul
      p M hpM hk g hg γ hγ hγp L ζ hζ ι s b hb hs δ hδ hδp hδM n
  set Zf : LaurentSeries L := HahnSeries.ofPowerSeries ℤ L (PowerSeries.mk zf) with hZfdef
  set Zg : LaurentSeries L := HahnSeries.ofPowerSeries ℤ L (PowerSeries.mk zg) with hZgdef
  have hZf : coeffMap ι Zf = Qc (⇑Ff : UpperHalfPlane → ℂ) := by
    rw [hZfdef, coeffMap_ofPowerSeries, Qc, hFf]
    congr 1
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact hzf n
  have hZg : coeffMap ι Zg = Qc (⇑Fg : UpperHalfPlane → ℂ) := by
    rw [hZgdef, coeffMap_ofPowerSeries, Qc, hFg]
    congr 1
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact hzg n
  have hZf' : coeffMap (ι.comp s.toAlgHom.toRingHom) Zf
      = Qc (fun τ : UpperHalfPlane => (((⇑f : UpperHalfPlane → ℂ) ∣[k] δ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) := by
    rw [hZfdef, coeffMap_ofPowerSeries, Qc]
    congr 1
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact (hzf' n).symm
  have hZg' : coeffMap (ι.comp s.toAlgHom.toRingHom) Zg
      = Qc (fun τ : UpperHalfPlane => (((⇑g : UpperHalfPlane → ℂ) ∣[k] δ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) := by
    rw [hZgdef, coeffMap_ofPowerSeries, Qc]
    congr 1
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact (hzg' n).symm

  have hprod : ((σ x : ↥(laurentBaseChange L (x1FunctionField (M * p)))) : LaurentSeries L) * Zg = Zf := by
    apply ModularCurve.coeffMap_injective ι.injective
    rw [map_mul, hZg, hZf]
    exact hstar

  have h2 := congrArg (coeffMap (ι.comp s.toAlgHom.toRingHom)) hprod
  rw [map_mul, hZg', hZf'] at h2
  rw [hSs, coeffMap_coeffMap]
  exact h2

end Conj6
p2m_reactivate "P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6"

namespace Conj6

open ModularCurve

section NonVanish

theorem coe_ne_zero_of_intSeriesC_ne_zero {N : ℕ} {k : ℤ} (g : ModularForm (Γ1 N) k) (pg : PowerSeries ℤ)
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : (⇑g : UpperHalfPlane → ℂ) ≠ 0 := by
  intro h0
  apply hg0
  have hg' : g = 0 := DFunLike.coe_injective (h0.trans ModularForm.coe_zero.symm)
  have hpg : pg = 0 := by
    have h1 := hg
    rw [IsIntegralQExp, hg', ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero] at h1
    ext n
    have := congrArg (PowerSeries.coeff n) h1
    rw [PowerSeries.coeff_map, map_zero, eq_intCast] at this
    rw [map_zero]
    exact_mod_cast this
  rw [hpg, intSeriesC_zero]

theorem slash_ne_zero {k : ℤ} (f : UpperHalfPlane → ℂ) (hf : f ≠ 0) (α : SL(2, ℤ)) : f ∣[k] α ≠ 0 := by
  intro h
  apply hf
  have : f = (f ∣[k] α) ∣[k] α⁻¹ := by rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
  rw [this, h, SlashAction.zero_slash]

theorem comp_heckeDiag_ne_zero (p : ℕ) (hp : p ≠ 0) (F : UpperHalfPlane → ℂ) (hF : F ≠ 0) :
    (fun τ : UpperHalfPlane => F (ModularForm.heckeDiagMatrix p • τ)) ≠ 0 := by
  intro h
  apply hF
  funext τ
  let τ' : UpperHalfPlane := ⟨(τ : ℂ) / p, by
    rw [Complex.div_natCast_im]; exact div_pos τ.im_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp))⟩
  have hτ : ModularForm.heckeDiagMatrix p • τ' = τ := by
    apply UpperHalfPlane.ext
    rw [ModularForm.coe_heckeDiagMatrix_smul hp]
    show (p : ℂ) * ((τ : ℂ) / p) = τ
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hp)]
  have := congrFun h τ'
  rw [hτ] at this
  simpa using this

theorem mul_mem_Gamma0_and_dvd {M p : ℕ} (δ γ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 (M * p))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) :
    δ * γ ∈ CongruenceSubgroup.Gamma0 M ∧ (p : ℤ) ∣ (δ * γ) 1 1 := by
  have hδ10 : ((M * p : ℕ) : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hδ)
  have hγ10 : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  have hM : (M : ℤ) ∣ δ 1 0 := (Int.natCast_dvd_natCast.mpr (dvd_mul_right M p)).trans hδ10
  have hp : (p : ℤ) ∣ δ 1 0 := (Int.natCast_dvd_natCast.mpr (dvd_mul_left p M)).trans hδ10
  have h10 : (δ * γ) 1 0 = δ 1 0 * γ 0 0 + δ 1 1 * γ 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : (δ * γ) 1 1 = δ 1 0 * γ 0 1 + δ 1 1 * γ 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem, h10]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_add (dvd_mul_of_dvd_left hM _) (dvd_mul_of_dvd_right hγ10 _))
  · rw [h11]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hγp _)

theorem slash_slash_fun {k : ℤ} (f : UpperHalfPlane → ℂ) (δ γ : SL(2, ℤ)) (p : ℕ) :
    (fun τ : UpperHalfPlane => ((f ∣[k] δ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) =
      fun τ : UpperHalfPlane => (f ∣[k] (δ * γ)) (ModularForm.heckeDiagMatrix p • τ) := by
  funext τ
  rw [SlashAction.slash_mul]

theorem Qc_slash_slash_ne_zero (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ}
    (g : ModularForm (Γ1 (M * p)) k) (hg : (⇑g : UpperHalfPlane → ℂ) ≠ 0)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 (M * p)) :
    Qc (fun τ : UpperHalfPlane => (((⇑g : UpperHalfPlane → ℂ) ∣[k] δ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ≠ 0 := by
  obtain ⟨hδγ, hδγp⟩ := mul_mem_Gamma0_and_dvd δ γ hδ hγ hγp
  obtain ⟨F, hF⟩ := ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul p M hpM g (δ * γ) hδγ hδγp
  rw [slash_slash_fun, ← hF, Ne, Qc_eq_zero_iff]
  intro hF0
  have : (⇑F : UpperHalfPlane → ℂ) ≠ 0 := by
    rw [hF]
    exact comp_heckeDiag_ne_zero p (Fact.out : p.Prime).ne_zero _ (slash_ne_zero _ hg _)
  exact this (by rw [hF0, ModularForm.coe_zero])

end NonVanish
p2m_reactivate "P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6"

theorem exists_delta (N : ℕ) [NeZero N] (b' : ℕ) (hb' : b'.Coprime N) :
    ∃ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 N ∧ ((δ 0 0 : ℤ) : ZMod N) = (b' : ZMod N) := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hb'
  refine ⟨⟨!![(b' : ℤ), -v; (N : ℤ), u], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination huv
  · rw [CongruenceSubgroup.Gamma0_mem]
    simp
  · simp

section Main

theorem isIntegralQExp_mul' {N : ℕ} {a b : ℤ} {f : ModularForm (Γ1 N) a} {g : ModularForm (Γ1 N) b} {r t : PowerSeries ℤ}
    (hf : IsIntegralQExp f r) (hg : IsIntegralQExp g t) : IsIntegralQExp (f.mul g) (r * t) := by
  rw [IsIntegralQExp, map_mul, hf, hg, ModularForm.coe_mul,
    ← ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_Γ1 f g]

theorem main
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (σ : ↥K ≃ₐ[L] ↥K)
    (hWσ : ∃ (ι : L →+* ℂ) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M ∧ (p : ℤ) ∣ γ 1 1 ∧
        ∀ (k : ℤ) (f g : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ),
          ModularCurve.IsIntegralQExp f pf → ModularCurve.IsIntegralQExp g pg → ModularCurve.intSeriesC ℚ pg ≠ 0 →
          ∀ x : ↥K, (x : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg) →
          ∃ (φf φg : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (Df Dg : ℤ), Df ≠ 0 ∧ Dg ≠ 0 ∧
            (⇑φf : UpperHalfPlane → ℂ) = (Df : ℂ) • (fun τ : UpperHalfPlane => ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∧
            (⇑φg : UpperHalfPlane → ℂ) = (Dg : ℂ) • (fun τ : UpperHalfPlane => ((⇑g : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∧
            (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (r : Fin n → PowerSeries ℤ),
              (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧ φf = ∑ i, (ι (c i)) • F i) ∧
            (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (r : Fin n → PowerSeries ℤ),
              (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧ φg = ∑ i, (ι (c i)) • F i) ∧
            ModularCurve.coeffMap ι ((σ x : ↥K) : LaurentSeries L) * HahnSeries.C (Df : ℂ) *
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φg : UpperHalfPlane → ℂ)) =
              HahnSeries.C (Dg : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φf : UpperHalfPlane → ℂ))) :
    (∀ (s : L ≃ₐ[ℚ] L) (b : ℕ), b.Coprime p → s ζ = ζ ^ b →
        ∀ (b' : ℕ), b'.Coprime (M * p) → ((b' : ZMod M) = 1) → ((b' : ZMod p) = (b : ZMod p)) →
        ∀ (Ss : ↥K ≃+* ↥K),
          (∀ x : ↥K, ((Ss x : ↥K) : LaurentSeries L) =
            ModularCurve.coeffMap (s.toAlgHom.toRingHom) ((x : ↥K) : LaurentSeries L)) →
        ∀ (θb' : ↥K ≃ₐ[L] ↥K),
          (∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
          (x : LaurentSeries L) = (x' : LaurentSeries L) →
            ((θb' x : ↥K) : LaurentSeries L) =
              ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) b') x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) →
          ∀ x : ↥K, ((Ss (σ (Ss.symm x)) : ↥K) : LaurentSeries L) = ((σ (θb' x) : ↥K) : LaurentSeries L)) := by
  classical
  intro s b hb hs b' hb' hb'M hb'p Ss hSs θ hθ
  subst hK
  haveI hp : Fact p.Prime := inferInstance
  haveI : NeZero (M * p) := ⟨mul_ne_zero (NeZero.ne M) hp.out.ne_zero⟩
  obtain ⟨ι, γ, hγ, hγp, hW⟩ := hWσ
  obtain ⟨δ, hδ, hδ00⟩ := exists_delta (M * p) b' hb'

  suffices H : Lam s Ss hSs σ = σ.toAlgHom.comp θ.toAlgHom by
    intro x
    have hx := AlgHom.congr_fun H x
    change Ss (σ (Ss.symm x)) = σ (θ x) at hx
    exact congrArg Subtype.val hx
  apply algHom_ext_of_ratios (M * p) L
  intro r hr
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hr
  change Ss (σ (Ss.symm _)) = σ (θ _)
  rw [Ss_symm_coeffEmb s Ss hSs]

  have hf₂ : IsIntegralQExp (f.mul g) (pf * pg) := isIntegralQExp_mul' hf hg
  have hg₂ : IsIntegralQExp (g.mul g) (pg * pg) := isIntegralQExp_mul' hg hg
  have hg₂0 : intSeriesC ℚ (pg * pg) ≠ 0 := by rw [intSeriesC_mul]; exact mul_ne_zero hg0 hg0
  set x : ↥(laurentBaseChange L (x1FunctionField (M * p))) :=
    ⟨coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg),
      coeffEmb_mem_laurentBaseChange L (intFormRatiosC_subset ℚ _ (mem_intFormRatiosC f g hf hg hg0))⟩ with hxdef
  have hx : (x : LaurentSeries L) = coeffEmb L (intSeriesC ℚ (pf * pg) / intSeriesC ℚ (pg * pg)) := by
    rw [hxdef, intSeriesC_mul, intSeriesC_mul, mul_div_mul_right _ _ hg0]
  have hk2 : Even (k + k) := ⟨k, rfl⟩
  have L1 := lhs_identity p M hpM L ζ hζ σ ι γ hγ hγp hW s b hb hs b' hb'M hb'p Ss hSs δ hδ hδ00 hk2
    (f.mul g) (g.mul g) (pf * pg) (pg * pg) hf₂ hg₂ hg₂0 x hx
  have R1 := rhs_identity p M hpM L σ θ ι γ hγ hγp hW b' hb' hθ δ hδ hδ00
    (f.mul g) (g.mul g) (pf * pg) (pg * pg) hf₂ hg₂ hg₂0 x hx
  have hQ := Qc_slash_slash_ne_zero p M hpM (g.mul g) (coe_ne_zero_of_intSeriesC_ne_zero _ _ hg₂ hg₂0) γ hγ hγp δ hδ
  have hcoe : coeffMap ι ((Ss (σ x) : ↥(laurentBaseChange L (x1FunctionField (M * p)))) : LaurentSeries L)
      = coeffMap ι ((σ (θ x) : ↥(laurentBaseChange L (x1FunctionField (M * p)))) : LaurentSeries L) :=
    mul_right_cancel₀ hQ (L1.trans R1.symm)
  exact Subtype.ext (ModularCurve.coeffMap_injective ι.injective hcoe)

end Main
p2m_reactivate "P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6"

end Conj6
p2m_reactivate "P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6"

open scoped MatrixGroups ModularForm in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    [NeZero p]
    (σ : ↥K ≃ₐ[L] ↥K)
    (hWσ : ∃ (ι : L →+* ℂ) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M ∧ (p : ℤ) ∣ γ 1 1 ∧
        ∀ (k : ℤ) (f g : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ),
          ModularCurve.IsIntegralQExp f pf → ModularCurve.IsIntegralQExp g pg → ModularCurve.intSeriesC ℚ pg ≠ 0 →
          ∀ x : ↥K, (x : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg) →
          ∃ (φf φg : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (Df Dg : ℤ), Df ≠ 0 ∧ Dg ≠ 0 ∧
            (⇑φf : UpperHalfPlane → ℂ) = (Df : ℂ) • (fun τ : UpperHalfPlane => ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∧
            (⇑φg : UpperHalfPlane → ℂ) = (Dg : ℂ) • (fun τ : UpperHalfPlane => ((⇑g : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∧
            (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (r : Fin n → PowerSeries ℤ),
              (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧ φf = ∑ i, (ι (c i)) • F i) ∧
            (∃ (n : ℕ) (c : Fin n → L) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (r : Fin n → PowerSeries ℤ),
              (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧ φg = ∑ i, (ι (c i)) • F i) ∧
            ModularCurve.coeffMap ι ((σ x : ↥K) : LaurentSeries L) * HahnSeries.C (Df : ℂ) *
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φg : UpperHalfPlane → ℂ)) =
              HahnSeries.C (Dg : ℂ) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑φf : UpperHalfPlane → ℂ))) :
    (∀ (s : L ≃ₐ[ℚ] L) (b : ℕ), b.Coprime p → s ζ = ζ ^ b →
        ∀ (b' : ℕ), b'.Coprime (M * p) → ((b' : ZMod M) = 1) → ((b' : ZMod p) = (b : ZMod p)) →
        ∀ (Ss : ↥K ≃+* ↥K),
          (∀ x : ↥K, ((Ss x : ↥K) : LaurentSeries L) =
            ModularCurve.coeffMap (s.toAlgHom.toRingHom) ((x : ↥K) : LaurentSeries L)) →
        ∀ (θb' : ↥K ≃ₐ[L] ↥K),
          (∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
          (x : LaurentSeries L) = (x' : LaurentSeries L) →
            ((θb' x : ↥K) : LaurentSeries L) =
              ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) b') x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) →
          ∀ x : ↥K, ((Ss (σ (Ss.symm x)) : ↥K) : LaurentSeries L) = ((σ (θb' x) : ↥K) : LaurentSeries L)) := by
  exact Conj6.main p M hpM L ζ hζ K hK j hj σ hWσ

end S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul (solution)
