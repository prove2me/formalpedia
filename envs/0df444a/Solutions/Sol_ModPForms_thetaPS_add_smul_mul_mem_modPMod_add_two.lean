-- Prove2me | solution 1 for ModPForms.thetaPS_add_smul_mul_mem_modPMod_add_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/ccb3dd42-abb9-59e6-b293-24470d2e1951

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_SwdAlgebra
import Theorems.Thm_ModPForms_smul_thetaPS_sub_smul_mem_modPMod_add_two
import Theorems.Thm_ModPForms_natCast_smul_heckeV_qP_sub_qP_mem_modPMod
import Theorems.Thm_ModPForms_heckeV_mem_modPMod_mul
import Theorems.Thm_ModPForms_modPMod_le_modPMod_of_dvd
import Theorems.Thm_ModPForms_mul_mem_modPMod_add
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_thetaPS_add_smul_mul_mem_modPMod_add_two
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false

open ModPForms UpperHalfPlane

namespace LAW3

open PowerSeries

noncomputable def Pz : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -24 * ∑ d ∈ n.divisors, (d : ℤ)

theorem qP_eq_map (F : Type) [Field F] : SwdAlgebra.qP F = PowerSeries.map (Int.castRingHom F) Pz := rfl

@[scoped simp] theorem coeff_Pz (n : ℕ) : coeff n Pz = if n = 0 then (1 : ℤ) else -24 * ∑ d ∈ n.divisors, (d : ℤ) :=
  coeff_mk _ _

theorem coeff_Pz_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    coeff n Pz = -24 * ((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) := by
  rw [coeff_Pz, if_neg hn, ArithmeticFunction.sigma_one_apply, Nat.cast_sum]

noncomputable def Bz (d : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    (((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) -
      (if d ∣ n then ((ArithmeticFunction.sigma 1 (n / d) : ℕ) : ℤ) else 0) : ℤ)

@[scoped simp] theorem coeff_Bz (d n : ℕ) :
    coeff n (Bz d) = ((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) -
      (if d ∣ n then ((ArithmeticFunction.sigma 1 (n / d) : ℕ) : ℤ) else 0) :=
  coeff_mk _ _

theorem B_eq_map (d : ℕ) (F : Type) [Field F] :
    (PowerSeries.mk fun n : ℕ =>
        ((((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) -
          (if d ∣ n then ((ArithmeticFunction.sigma 1 (n / d) : ℕ) : ℤ) else 0) : ℤ) : F)) =
      PowerSeries.map (Int.castRingHom F) (Bz d) := by
  ext n
  rw [coeff_mk, coeff_map, coeff_Bz, eq_intCast]

theorem heckeV_Pz_sub_Pz (d : ℕ) (hd : d ≠ 0) :
    PowerSeries.heckeV d Pz - Pz = PowerSeries.C (24 : ℤ) * Bz d := by
  ext n
  rw [map_sub, coeff_heckeV, coeff_C_mul, coeff_Bz]
  have hσ0 : ((ArithmeticFunction.sigma 1 0 : ℕ) : ℤ) = 0 := by simp
  by_cases hn : n = 0
  · subst hn
    simp [coeff_Pz]
  · rw [coeff_Pz_of_ne_zero hn]
    by_cases hdn : d ∣ n
    · have hnd : n / d ≠ 0 := by
        obtain ⟨m, rfl⟩ := hdn
        rw [Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hd)]
        rintro rfl
        exact hn (mul_zero d)
      rw [if_pos hdn, if_pos hdn, coeff_Pz_of_ne_zero hnd]
      ring
    · rw [if_neg hdn, if_neg hdn]
      ring

theorem map_heckeV {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (d : ℕ) (X : PowerSeries R) :
    PowerSeries.map g (PowerSeries.heckeV d X) = PowerSeries.heckeV d (PowerSeries.map g X) := by
  ext n
  simp only [coeff_map, coeff_heckeV]
  split_ifs <;> simp

theorem heckeV_heckeV {R : Type} [CommRing R] (a b : ℕ) (ha : a ≠ 0) (X : PowerSeries R) :
    PowerSeries.heckeV a (PowerSeries.heckeV b X) = PowerSeries.heckeV (a * b) X := by
  ext n
  simp only [coeff_heckeV]
  by_cases hab : a * b ∣ n
  · obtain ⟨m, rfl⟩ := hab
    have h1 : a ∣ a * b * m := ⟨b * m, by ring⟩
    have h2 : a * b * m / a = b * m := by
      rw [mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha)]
    have h3 : b ∣ b * m := ⟨m, rfl⟩
    rw [if_pos h1, h2, if_pos h3, if_pos ⟨m, rfl⟩]
    by_cases hb : b = 0
    · subst hb; simp
    · rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hb),
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (mul_ne_zero ha hb))]
  · rw [if_neg hab]
    by_cases h1 : a ∣ n
    · rw [if_pos h1]
      rw [if_neg]
      intro h2
      apply hab
      obtain ⟨m, rfl⟩ := h1
      rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha)] at h2
      exact mul_dvd_mul_left a h2
    · rw [if_neg h1]

theorem heckeV_one' {R : Type} [CommRing R] (X : PowerSeries R) : PowerSeries.heckeV 1 X = X := by
  ext n
  simp [coeff_heckeV]

noncomputable def eis (F : Type) [Field F] (d : ℕ) : PowerSeries F :=
  (d : F) • PowerSeries.heckeV d (SwdAlgebra.qP F) - SwdAlgebra.qP F

theorem eis_one (F : Type) [Field F] : eis F 1 = 0 := by
  simp [eis, heckeV_one']

theorem eis_mul (F : Type) [Field F] (q m : ℕ) (hq : q ≠ 0) :
    eis F (q * m) = eis F q + (q : F) • PowerSeries.heckeV q (eis F m) := by
  simp only [eis, map_sub, LinearMap.map_smul_of_tower, heckeV_heckeV q m hq, Nat.cast_mul, smul_sub,
    mul_smul]
  abel

theorem eis_mem (F : Type) [Field F] : ∀ d : ℕ, d ≠ 0 → eis F d ∈ ModPForms.modPMod d 2 F := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    rcases eq_or_ne d 1 with rfl | hd1
    · rw [eis_one]; exact Submodule.zero_mem _
    ·
      set q := d.minFac with hqdef
      have hqp : q.Prime := Nat.minFac_prime hd1
      haveI : Fact q.Prime := ⟨hqp⟩
      obtain ⟨m, hm⟩ : q ∣ d := Nat.minFac_dvd d
      have hm0 : m ≠ 0 := by rintro rfl; exact hd (by rw [hm, mul_zero])
      haveI : NeZero m := ⟨hm0⟩
      have hmlt : m < d := by
        rw [hm]
        exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hqp.one_lt
      have hEm : eis F m ∈ ModPForms.modPMod m 2 F := ih m hmlt hm0
      have hEq : eis F q ∈ ModPForms.modPMod q 2 F := ModPForms.natCast_smul_heckeV_qP_sub_qP_mem_modPMod q F
      rw [hm, eis_mul F q m hqp.ne_zero]
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
      · exact ModPForms.modPMod_le_modPMod_of_dvd q (q * m) (dvd_mul_right q m) 2 F hEq
      · have := ModPForms.heckeV_mem_modPMod_mul m 2 q hqp.ne_zero F (eis F m) hEm
        rwa [mul_comm m q] at this

theorem natCast_smul_heckeV_qP_sub_qP_mem (d : ℕ) (hd : d ≠ 0) :
    (d : ℚ) • PowerSeries.heckeV d (SwdAlgebra.qP ℚ) - SwdAlgebra.qP ℚ ∈ ModPForms.modPMod d 2 ℚ :=
  eis_mem ℚ d hd

theorem natCast_smul_heckeV_qP_sub_qP_mem' (F : Type) [Field F] (d : ℕ) (hd : d ≠ 0) :
    (d : F) • PowerSeries.heckeV d (SwdAlgebra.qP F) - SwdAlgebra.qP F ∈ ModPForms.modPMod d 2 F :=
  eis_mem F d hd

theorem coeff_eis (F : Type) [Field F] (d n : ℕ) :
    coeff n (eis F d) = (d : F) * (if d ∣ n then ((coeff (n / d) Pz : ℤ) : F) else 0) - ((coeff n Pz : ℤ) : F) := by
  simp only [eis, map_sub, coeff_smul, coeff_heckeV, qP_eq_map, coeff_map, eq_intCast, smul_eq_mul]

theorem ite_coeff_Pz_sub_coeff_Pz (d : ℕ) (hd : d ≠ 0) (n : ℕ) :
    (if d ∣ n then coeff (n / d) Pz else 0) - coeff n Pz = 24 * coeff n (Bz d) := by
  have h := congrArg (coeff n) (heckeV_Pz_sub_Pz d hd)
  rw [map_sub, coeff_heckeV, coeff_C_mul] at h
  exact h

end LAW3
p2m_reactivate "P2MW.S_ModPForms_thetaPS_add_smul_mul_mem_modPMod_add_two.LAW3"

namespace LAW3

open PowerSeries

section Euler
variable {R S : Type} [CommSemiring R] [CommSemiring S]

noncomputable def eul (X : PowerSeries R) : PowerSeries R := PowerSeries.mk fun n => (n : R) * coeff n X

@[scoped simp] theorem coeff_eul (X : PowerSeries R) (n : ℕ) : coeff n (eul X) = (n : R) * coeff n X := coeff_mk _ _

theorem map_eul (g : R →+* S) (X : PowerSeries R) : map g (eul X) = eul (map g X) := by
  ext n; simp [coeff_map]

@[scoped simp] theorem eul_zero : eul (0 : PowerSeries R) = 0 := by
  ext n; simp

end Euler
p2m_reactivate "P2MW.S_ModPForms_thetaPS_add_smul_mul_mem_modPMod_add_two.LAW3"

theorem thetaPS_eq_eul {F : Type} [Field F] (φ : PowerSeries F) : thetaPS φ = eul φ := rfl

theorem hΓ (N : ℕ) : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
    (CongruenceSubgroup.Gamma0 N)).strictPeriods :=
  CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N

theorem lift (N : ℕ) (k : ℤ) (φ : PowerSeries ℚ) (hφ : φ ∈ modPMod N k ℚ) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 N) k,
      ∀ n, ModularFormClass.qCoeff g n = ((coeff n φ : ℚ) : ℂ) := by
  rw [modPMod] at hφ
  induction hφ using Submodule.span_induction with
  | mem φ₀ h =>
    obtain ⟨f, a, hfa, rfl⟩ := h
    exact ⟨f, fun n => by rw [hfa n, coeff_mk]; push_cast; rfl⟩
  | zero =>
    refine ⟨0, fun n => ?_⟩
    have h0 : ⇑(0 : ModularForm (CongruenceSubgroup.Gamma0 N) k) =
        (0 : ℂ) • ⇑(0 : ModularForm (CongruenceSubgroup.Gamma0 N) k) := by simp
    unfold ModularFormClass.qCoeff
    rw [h0, ModularForm.qExpansion_smul one_pos (hΓ N) (0 : ℂ) (0 : ModularForm _ k)]
    simp
  | add x y _ _ hx hy =>
    obtain ⟨g₁, h₁⟩ := hx
    obtain ⟨g₂, h₂⟩ := hy
    refine ⟨g₁ + g₂, fun n => ?_⟩
    unfold ModularFormClass.qCoeff at h₁ h₂ ⊢
    rw [ModularForm.coe_add, ModularForm.qExpansion_add one_pos (hΓ N) g₁ g₂, map_add, h₁, h₂, map_add]
    push_cast; rfl
  | smul c x _ hx =>
    obtain ⟨g₁, h₁⟩ := hx
    refine ⟨(c : ℂ) • g₁, fun n => ?_⟩
    unfold ModularFormClass.qCoeff at h₁ ⊢
    rw [show ⇑((c : ℂ) • g₁) = (c : ℂ) • ⇑g₁ from rfl,
      ModularForm.qExpansion_smul one_pos (hΓ N) (c : ℂ) g₁, map_smul, h₁, smul_eq_mul]
    simp only [map_smul, smul_eq_mul]
    push_cast; rfl

end LAW3
p2m_reactivate "P2MW.S_ModPForms_thetaPS_add_smul_mul_mem_modPMod_add_two.LAW3"

namespace LAW3

open PowerSeries

theorem target_add {F : Type} [Field F] (k : ℤ) (B φ ψ : PowerSeries F) :
    thetaPS (φ + ψ) + (k : F) • (B * (φ + ψ)) =
      (thetaPS φ + (k : F) • (B * φ)) + (thetaPS ψ + (k : F) • (B * ψ)) := by
  rw [thetaPS_eq_eul]; simp only [thetaPS_eq_eul]
  have : eul (φ + ψ) = eul φ + eul ψ := by ext n; simp [mul_add]
  rw [this, mul_add, smul_add]; abel

theorem target_smul {F : Type} [Field F] (k : ℤ) (B : PowerSeries F) (c : F) (φ : PowerSeries F) :
    thetaPS (c • φ) + (k : F) • (B * (c • φ)) = c • (thetaPS φ + (k : F) • (B * φ)) := by
  simp only [thetaPS_eq_eul]
  have : eul (c • φ) = c • eul φ := by ext n; simp only [coeff_eul, map_smul, smul_eq_mul]; ring
  rw [this, mul_smul_comm, smul_add, smul_comm c]

theorem generator (N' : ℕ) [NeZero N'] (d : ℕ) (hd : d ∣ N') (hd3 : d % 3 = 2) (F : Type) [Field F]
    [CharP F 3] (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma0 N') k) (a : ℕ → ℤ)
    (hfa : ∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    thetaPS (PowerSeries.mk fun n => ((a n : ℤ) : F)) + (k : F) •
      (PowerSeries.map (Int.castRingHom F) (Bz d) * PowerSeries.mk fun n => ((a n : ℤ) : F)) ∈
      modPMod N' (k + 2) F := by
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd3

  let A : PowerSeries ℤ := PowerSeries.mk a
  let φQ : PowerSeries ℚ := PowerSeries.map (Int.castRingHom ℚ) A
  have hφQ : φQ ∈ modPMod N' k ℚ := by
    refine Submodule.subset_span ⟨f, a, hfa, ?_⟩
    ext n; simp [φQ, A, coeff_map]
  let P : PowerSeries ℚ := SwdAlgebra.qP ℚ
  have hS : (12 : ℚ) • thetaPS φQ - (k : ℚ) • (P * φQ) ∈ modPMod N' (k + 2) ℚ :=
    ModPForms.smul_thetaPS_sub_smul_mem_modPMod_add_two N' ℚ k φQ hφQ
  have he : (d : ℚ) • heckeV d P - P ∈ modPMod N' 2 ℚ :=
    ModPForms.modPMod_le_modPMod_of_dvd d N' hd 2 ℚ (natCast_smul_heckeV_qP_sub_qP_mem d hd0)
  have hE : ((d : ℚ) • heckeV d P - P) * φQ ∈ modPMod N' (k + 2) ℚ := by
    have := ModPForms.mul_mem_modPMod_add N' 2 k ℚ _ _ he hφQ
    rwa [add_comm] at this

  let Ψ : PowerSeries ℤ := C (1 - (d : ℤ)) * eul A - C (2 * k * (d : ℤ)) * (Bz d * A)
  let ψQ : PowerSeries ℚ := PowerSeries.map (Int.castRingHom ℚ) Ψ
  have hident : heckeV d P - P = (24 : ℚ) • PowerSeries.map (Int.castRingHom ℚ) (Bz d) := by
    have := congrArg (PowerSeries.map (Int.castRingHom ℚ)) (heckeV_Pz_sub_Pz d hd0)
    simp only [map_sub, map_mul, map_C, map_heckeV] at this
    show heckeV d (SwdAlgebra.qP ℚ) - SwdAlgebra.qP ℚ = _
    rw [qP_eq_map, smul_eq_C_mul]
    simpa using this
  have hcombo : (1 - (d : ℚ)) • ((12 : ℚ) • thetaPS φQ - (k : ℚ) • (P * φQ)) -
      (k : ℚ) • (((d : ℚ) • heckeV d P - P) * φQ) = (12 : ℚ) • ψQ := by
    have hV : heckeV d P = P + (24 : ℚ) • PowerSeries.map (Int.castRingHom ℚ) (Bz d) := by
      rw [← hident]; ring
    have hθ : thetaPS φQ = PowerSeries.map (Int.castRingHom ℚ) (eul A) := by
      rw [thetaPS_eq_eul, map_eul]
    rw [hV, hθ]
    simp only [ψQ, Ψ, φQ, map_sub, map_mul, map_C, Int.coe_castRingHom, smul_eq_C_mul]
    push_cast
    simp only [map_ofNat, map_one]
    ring
  have hψQ : ψQ ∈ modPMod N' (k + 2) ℚ := by
    have hmem := Submodule.sub_mem _ (Submodule.smul_mem _ (1 - (d : ℚ)) hS) (Submodule.smul_mem _ (k : ℚ) hE)
    rw [hcombo] at hmem
    have := Submodule.smul_mem _ (12 : ℚ)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ (by norm_num : (12 : ℚ) ≠ 0), one_smul] at this

  obtain ⟨g, hg⟩ := lift N' (k + 2) ψQ hψQ
  have hgZ : ∀ n, ModularFormClass.qCoeff g n = ((coeff n Ψ : ℤ) : ℂ) := by
    intro n; rw [hg n]; simp [ψQ, coeff_map]

  have hmemF : (PowerSeries.mk fun n => ((coeff n Ψ : ℤ) : F)) ∈ modPMod N' (k + 2) F :=
    Submodule.subset_span ⟨g, fun n => coeff n Ψ, hgZ, rfl⟩
  have hΨF : (PowerSeries.mk fun n => ((coeff n Ψ : ℤ) : F)) =
      ((1 : F) - (d : F)) • thetaPS (PowerSeries.mk fun n => ((a n : ℤ) : F)) -
        ((2 : F) * (k : F) * (d : F)) • (PowerSeries.map (Int.castRingHom F) (Bz d) *
          PowerSeries.mk fun n => ((a n : ℤ) : F)) := by
    have e1 : (PowerSeries.mk fun n => ((a n : ℤ) : F)) = PowerSeries.map (Int.castRingHom F) A := by
      ext n; simp [A, coeff_map]
    have e3 : (PowerSeries.mk fun n => ((coeff n Ψ : ℤ) : F)) = PowerSeries.map (Int.castRingHom F) Ψ := by
      ext n; simp [coeff_map]
    rw [e1, e3, thetaPS_eq_eul, ← map_eul]
    simp only [Ψ, map_sub, map_mul, map_C, Int.coe_castRingHom, smul_eq_C_mul]
    push_cast
    ring

  have h3 : (3 : F) = 0 := by
    have := CharP.cast_eq_zero F 3
    push_cast at this; exact this
  have h2F : (2 : F) = -1 := by linear_combination h3
  have hdF : (d : F) = -1 := by
    rw [← Nat.mod_add_div d 3, hd3]
    push_cast
    rw [h3, zero_mul, add_zero, h2F]
  rw [hΨF, hdF, h2F] at hmemF
  have hs1 : ((1 : F) - -1) = -1 := by rw [sub_neg_eq_add, one_add_one_eq_two, h2F]
  have hs2 : (-1 * (k : F) * -1) = k := by ring
  rw [hs1, hs2, neg_one_smul] at hmemF
  have : -thetaPS (PowerSeries.mk fun n => ((a n : ℤ) : F)) -
      (k : F) • (PowerSeries.map (Int.castRingHom F) (Bz d) * PowerSeries.mk fun n => ((a n : ℤ) : F)) =
      -(thetaPS (PowerSeries.mk fun n => ((a n : ℤ) : F)) + (k : F) •
        (PowerSeries.map (Int.castRingHom F) (Bz d) * PowerSeries.mk fun n => ((a n : ℤ) : F))) := by abel
  rw [this] at hmemF
  exact (Submodule.neg_mem_iff _).1 hmemF

end LAW3
p2m_reactivate "P2MW.S_ModPForms_thetaPS_add_smul_mul_mem_modPMod_add_two.LAW3"

open ModPForms LAW3

theorem solution (N' : ℕ) [NeZero N'] (d : ℕ) (hd : d ∣ N')
    (hd3 : d % 3 = 2) (F : Type) [Field F] [CharP F 3] (k : ℤ) (φ : PowerSeries F)
    (hφ : φ ∈ ModPForms.modPMod N' k F) :
    ModPForms.thetaPS φ + (k : F) •
      ((PowerSeries.mk fun n : ℕ =>
          ((((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) -
            (if d ∣ n then ((ArithmeticFunction.sigma 1 (n / d) : ℕ) : ℤ) else 0) : ℤ) : F)) * φ) ∈
      ModPForms.modPMod N' (k + 2) F := by
  rw [LAW3.B_eq_map]
  rw [modPMod] at hφ
  induction hφ using Submodule.span_induction with
  | mem φ₀ h =>
    obtain ⟨f, a, hfa, rfl⟩ := h
    exact LAW3.generator N' d hd hd3 F k f a hfa
  | zero => simp [LAW3.thetaPS_eq_eul]
  | add x y _ _ hx hy => rw [LAW3.target_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [LAW3.target_smul]; exact Submodule.smul_mem _ c hx

end S_ModPForms_thetaPS_add_smul_mul_mem_modPMod_add_two
end P2MW
export P2MW.S_ModPForms_thetaPS_add_smul_mul_mem_modPMod_add_two (solution)
