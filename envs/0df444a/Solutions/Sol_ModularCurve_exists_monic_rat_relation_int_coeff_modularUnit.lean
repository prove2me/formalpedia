-- Prove2me | solution 1 for ModularCurve.exists_monic_rat_relation_int_coeff_modularUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/dffdb50e-96cc-5651-8ffc-774d0638b3e5

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_mem_range_qExpand_of_qTwist_eq
import Theorems.Thm_ModularCurve_PhiGen_mem_range_coeffEmb_of_forall_coeffMap_eq
import Theorems.Thm_ModularCurve_PhiGen_mem_range_coeffEmb_qExpand_of_mem_inter
import Theorems.Thm_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false
noncomputable section
open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "dedekindEtaUnitQ deltaSeries deltaSeriesN modularUnitSeries qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jq ofPowerSeries_coeff_of_neg jqModC jqModC_rat coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand PhiGen.phiProd PhiGen.phiProd_monic PhiGen.phiProd_natDegree PhiGen.phiProd_eval_conj PhiGen.IntCoeffs PhiGen.PhiGenDescends coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut mem_range_qExpand_of_qTwist_eq PhiGen.mem_range_coeffEmb_of_forall_coeffMap_eq PhiGen.mem_range_coeffEmb_qExpand_of_mem_inter PhiGen.mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit"
namespace WQRel
p2m_open "ModularCurve"

variable {K : Type*} [Field K]

theorem coeffMap_qTwist (σ : K →+* K) (u : Kˣ) (f : LaurentSeries K) :
    ModularCurve.coeffMap σ (ModularCurve.qTwist u f) =
      ModularCurve.qTwist (Units.map (σ : K →* K) u) (ModularCurve.coeffMap σ f) := by
  ext k
  rw [ModularCurve.coeffMap_coeff, ModularCurve.qTwist_coeff, ModularCurve.qTwist_coeff,
    ModularCurve.coeffMap_coeff, map_mul]
  congr 1
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀]
  rfl

theorem phiProd_comp_perm (ℓ : ℕ) (conj : Fin (ℓ + 1) → LaurentSeries K)
    (ê : Equiv.Perm (Fin (ℓ + 1))) :
    ModularCurve.PhiGen.phiProd ℓ (conj ∘ ê) = ModularCurve.PhiGen.phiProd ℓ conj := by
  rw [ModularCurve.PhiGen.phiProd, ModularCurve.PhiGen.phiProd]
  exact Equiv.prod_comp ê fun i => Polynomial.X - Polynomial.C (conj i)

theorem map_phiProd (ℓ : ℕ) (conj : Fin (ℓ + 1) → LaurentSeries K)
    (φ : LaurentSeries K →+* LaurentSeries K) :
    (ModularCurve.PhiGen.phiProd ℓ conj).map φ =
      ModularCurve.PhiGen.phiProd ℓ (fun i => φ (conj i)) := by
  rw [ModularCurve.PhiGen.phiProd, ModularCurve.PhiGen.phiProd, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

def succPerm {ℓ : ℕ} (e : Equiv.Perm (Fin ℓ)) : Equiv.Perm (Fin (ℓ + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, e)

@[scoped simp]
theorem succPerm_zero {ℓ : ℕ} (e : Equiv.Perm (Fin ℓ)) : succPerm e 0 = 0 :=
  Equiv.Perm.decomposeFin_symm_apply_zero 0 e

@[scoped simp]
theorem succPerm_succ {ℓ : ℕ} (e : Equiv.Perm (Fin ℓ)) (b : Fin ℓ) :
    succPerm e b.succ = (e b).succ := by
  rw [succPerm, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]

end ModularCurve.WQRel
p2m_reactivate "P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve.WQRel"
p2m_reactivate "P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "dedekindEtaUnitQ deltaSeries deltaSeriesN modularUnitSeries qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jq ofPowerSeries_coeff_of_neg jqModC jqModC_rat coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand PhiGen.phiProd PhiGen.phiProd_monic PhiGen.phiProd_natDegree PhiGen.phiProd_eval_conj PhiGen.IntCoeffs PhiGen.PhiGenDescends coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut mem_range_qExpand_of_qTwist_eq PhiGen.mem_range_coeffEmb_of_forall_coeffMap_eq PhiGen.mem_range_coeffEmb_qExpand_of_mem_inter PhiGen.mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit" namespace PhiGen p2m_export "ModularCurve.PhiGen" "conj phiProd phiProd_monic phiProd_natDegree phiProd_eval_conj IntCoeffs PhiGenDescends mem_range_coeffEmb_of_forall_coeffMap_eq mem_range_coeffEmb_qExpand_of_mem_inter mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit" end ModularCurve.PhiGen
p2m_open_scoped "ModularCurve ModularCurve.PhiGen" in
open ModularCurve.WQRel in

theorem ModularCurve.PhiGen.phiProd_coeff_mem_range_qExpand_of_modularUnit {K : Type*}
    [Field K] [Algebra ℚ K] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (conj : Fin (p + 1) → LaurentSeries K) (hζ : IsPrimitiveRoot (ζ : K) p)
    (hconj0 : conj 0 = ModularCurve.qExpand K p
      (ModularCurve.coeffEmb K (ModularCurve.modularUnitSeries p)))
    (hconjS : ∀ b : Fin p, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ))
      (HahnSeries.C ((p : K) ^ 12) * (ModularCurve.coeffEmb K (ModularCurve.modularUnitSeries p))⁻¹))
    (k : ℕ) :
    (ModularCurve.PhiGen.phiProd p conj).coeff k ∈ Set.range (ModularCurve.qExpand K p) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.out.pos).symm⟩
  have hζu : ζ ^ (m + 1) = (1 : Kˣ) := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hζ.pow_eq_one)
  have hζuz : ζ ^ (((m + 1 : ℕ)) : ℤ) = (1 : Kˣ) := by
    rw [zpow_natCast]; exact hζu
  apply ModularCurve.mem_range_qExpand_of_qTwist_eq (m + 1) ζ hζ
  have hcoeff : ModularCurve.qTwist ζ ((ModularCurve.PhiGen.phiProd (m + 1) conj).coeff k) =
      ((ModularCurve.PhiGen.phiProd (m + 1) conj).map (ModularCurve.qTwist ζ)).coeff k := by
    rw [Polynomial.coeff_map]
  rw [hcoeff, map_phiProd]
  have hfam : (fun i => ModularCurve.qTwist ζ (conj i)) = conj ∘ (succPerm (finRotate (m + 1))) := by
    funext i
    induction i using Fin.cases with
    | zero =>
      simp only [Function.comp_apply, succPerm_zero]
      rw [hconj0, ModularCurve.qTwist_qExpand, hζuz, ModularCurve.qTwist_one_apply]
    | succ b =>
      simp only [Function.comp_apply, succPerm_succ]
      rw [hconjS b, ModularCurve.qTwist_qTwist, hconjS (finRotate (m + 1) b)]
      congr 1
      rw [← pow_succ']
      rcases eq_or_ne b (Fin.last m) with hb | hb
      · subst hb
        rw [show ((Fin.last m : Fin (m + 1)) : ℕ) + 1 = m + 1 from by
            rw [Fin.val_last], hζu]
        rw [show finRotate (m + 1) (Fin.last m) = 0 from by
            rw [finRotate_apply, Fin.last_add_one]]
        rw [Fin.val_zero, pow_zero]
      · rw [finRotate_apply, Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.mpr hb)]
  rw [hfam, phiProd_comp_perm]

p2m_open_scoped "ModularCurve ModularCurve.PhiGen" in
open ModularCurve.WQRel in

theorem ModularCurve.PhiGen.coeffMap_phiProd_coeff_of_modularUnit {K : Type*}
    [Field K] [Algebra ℚ K] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (conj : Fin (p + 1) → LaurentSeries K)
    (hconj0 : conj 0 = ModularCurve.qExpand K p
      (ModularCurve.coeffEmb K (ModularCurve.modularUnitSeries p)))
    (hconjS : ∀ b : Fin p, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ))
      (HahnSeries.C ((p : K) ^ 12) * (ModularCurve.coeffEmb K (ModularCurve.modularUnitSeries p))⁻¹))
    (σ : K →+* K) (hσQ : ∀ a : ℚ, σ (algebraMap ℚ K a) = algebraMap ℚ K a)
    (e : Equiv.Perm (Fin p))
    (hσζ : ∀ b : Fin p, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e b : Fin p) : ℕ))
    (k : ℕ) :
    ModularCurve.coeffMap σ ((ModularCurve.PhiGen.phiProd p conj).coeff k) =
      (ModularCurve.PhiGen.phiProd p conj).coeff k := by
  have hQfix : ModularCurve.coeffMap σ
      (ModularCurve.coeffEmb K (ModularCurve.modularUnitSeries p)) =
      ModularCurve.coeffEmb K (ModularCurve.modularUnitSeries p) := by
    rw [ModularCurve.coeffEmb, ModularCurve.coeffMap_coeffMap]
    exact ModularCurve.coeffMap_congr (RingHom.ext fun c => hσQ c) _
  have hcoeff : ModularCurve.coeffMap σ ((ModularCurve.PhiGen.phiProd p conj).coeff k) =
      ((ModularCurve.PhiGen.phiProd p conj).map (ModularCurve.coeffMap σ)).coeff k := by
    rw [Polynomial.coeff_map]
  rw [hcoeff, map_phiProd]
  have hfam : (fun i => ModularCurve.coeffMap σ (conj i)) = conj ∘ (succPerm e) := by
    funext i
    induction i using Fin.cases with
    | zero =>
      simp only [Function.comp_apply, succPerm_zero]
      rw [hconj0, ModularCurve.coeffSemilinearAut.coeffMap_qExpand, hQfix]
    | succ b =>
      simp only [Function.comp_apply, succPerm_succ]
      rw [hconjS b, coeffMap_qTwist, hconjS (e b)]
      have hunit : Units.map (σ : K →* K) (ζ ^ (b : ℕ)) = ζ ^ ((e b : Fin p) : ℕ) := by
        ext
        rw [Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val,
          Units.val_pow_eq_pow_val]
        exact hσζ b
      rw [hunit]
      congr 1
      rw [map_mul, map_inv₀, hQfix]
      congr 1
      have : (HahnSeries.C ((p : K) ^ 12) : LaurentSeries K) =
          HahnSeries.single (0 : ℤ) ((p : K) ^ 12) := rfl
      rw [this, ModularCurve.coeffMap_single, map_pow, map_natCast]
  rw [hfam, phiProd_comp_perm]

p2m_open_scoped "ModularCurve ModularCurve.PhiGen" in
open ModularCurve.WQRel in

theorem ModularCurve.PhiGen.exists_qExpand_descent_phiProd_modularUnit {K : Type*}
    [Field K] [Algebra ℚ K] [IsGalois ℚ K] [FiniteDimensional ℚ K]
    (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (conj : Fin (p + 1) → LaurentSeries K) (hζ : IsPrimitiveRoot (ζ : K) p)
    (hconj0 : conj 0 = ModularCurve.qExpand K p
      (ModularCurve.coeffEmb K (ModularCurve.modularUnitSeries p)))
    (hconjS : ∀ b : Fin p, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ))
      (HahnSeries.C ((p : K) ^ 12) * (ModularCurve.coeffEmb K (ModularCurve.modularUnitSeries p))⁻¹)) :
    ∃ c : ℕ → LaurentSeries ℚ, ∀ k : ℕ,
      (ModularCurve.PhiGen.phiProd p conj).coeff k =
        ModularCurve.coeffEmb K (ModularCurve.qExpand ℚ p (c k)) := by
  have hζK : (ζ : K) ^ p = 1 := hζ.pow_eq_one
  have hstep : ∀ k : ℕ, ∃ g : LaurentSeries ℚ,
      (ModularCurve.PhiGen.phiProd p conj).coeff k =
        ModularCurve.coeffEmb K (ModularCurve.qExpand ℚ p g) := by
    intro k
    have h1 : (ModularCurve.PhiGen.phiProd p conj).coeff k ∈
        Set.range (ModularCurve.qExpand K p) :=
      ModularCurve.PhiGen.phiProd_coeff_mem_range_qExpand_of_modularUnit p ζ conj hζ
        hconj0 hconjS k
    have h2 : (ModularCurve.PhiGen.phiProd p conj).coeff k ∈
        Set.range (ModularCurve.coeffEmb K) := by
      refine ModularCurve.PhiGen.mem_range_coeffEmb_of_forall_coeffMap_eq ?_ ?_
      · intro c hc
        have hmem : c ∈ IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[ℚ] K)) :=
          fun σ => hc σ.1
        rw [IsGalois.fixedField_top] at hmem
        exact IntermediateField.mem_bot.mp hmem
      · intro σ
        have hpow : (σ ((ζ : K))) ^ p = 1 := by rw [← map_pow, hζK, map_one]
        obtain ⟨a, ha_lt, ha⟩ := hζ.eq_pow_of_pow_eq_one hpow
        have hnd : ¬ p ∣ a := by
          intro hdvd
          have ha0 : a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd ha_lt
          rw [ha0, pow_zero] at ha
          have hσprim : IsPrimitiveRoot (σ ((ζ : K))) p :=
            hζ.map_of_injective (RingHom.injective (σ : K →+* K))
          rw [← ha] at hσprim
          have hp1 : p ∣ 1 := hσprim.dvd_of_pow_eq_one 1 (one_pow 1)
          exact hp.out.one_lt.ne' (Nat.dvd_one.mp hp1)
        have hcop : Nat.Coprime p a :=
          (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd
        have hinj : Function.Injective
            (fun b : Fin p => (⟨a * (b : ℕ) % p, Nat.mod_lt _ hp.out.pos⟩ : Fin p)) := by
          intro b₁ b₂ hb
          have hval : a * (b₁ : ℕ) % p = a * (b₂ : ℕ) % p := congrArg Fin.val hb
          have hmod : (b₁ : ℕ) ≡ (b₂ : ℕ) [MOD p] :=
            Nat.ModEq.cancel_left_of_coprime hcop hval
          exact Fin.ext (by
            rw [← Nat.mod_eq_of_lt b₁.isLt, ← Nat.mod_eq_of_lt b₂.isLt]; exact hmod)
        let e : Equiv.Perm (Fin p) :=
          Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
        have hσζb : ∀ b : Fin p, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e b : Fin p) : ℕ) := by
          intro b
          have h1' : σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ (a * (b : ℕ)) := by
            rw [map_pow, ← ha, ← pow_mul]
          have h2' : (ζ : K) ^ (a * (b : ℕ)) = (ζ : K) ^ (a * (b : ℕ) % p) := by
            conv_lhs => rw [← Nat.div_add_mod (a * (b : ℕ)) p]
            rw [pow_add, pow_mul, hζK, one_pow, one_mul]
          rw [h1', h2']
          rfl
        exact ModularCurve.PhiGen.coeffMap_phiProd_coeff_of_modularUnit p ζ conj
          hconj0 hconjS (σ : K →+* K) (fun q => σ.commutes q) e hσζb k
    exact ModularCurve.PhiGen.mem_range_coeffEmb_qExpand_of_mem_inter h1 h2
  choose c hc using hstep
  exact ⟨c, hc⟩

end
p2m_reactivate "P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve.WQRel"

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "dedekindEtaUnitQ deltaSeries deltaSeriesN modularUnitSeries qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jq ofPowerSeries_coeff_of_neg jqModC jqModC_rat coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand PhiGen.phiProd PhiGen.phiProd_monic PhiGen.phiProd_natDegree PhiGen.phiProd_eval_conj PhiGen.IntCoeffs PhiGen.PhiGenDescends coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut mem_range_qExpand_of_qTwist_eq PhiGen.mem_range_coeffEmb_of_forall_coeffMap_eq PhiGen.mem_range_coeffEmb_qExpand_of_mem_inter PhiGen.mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit"
p2m_open "ModularCurve"

namespace UnitConj

section IntegralCoeffs

variable {K : Type*} [Field K]

def CoeffsIntegral (f : LaurentSeries K) : Prop :=
  ∀ m : ℤ, f.coeff m ∈ integralClosure ℤ K

theorem coeffsIntegral_zero : CoeffsIntegral (0 : LaurentSeries K) := fun _ =>
  Subalgebra.zero_mem _

theorem coeffsIntegral_one : CoeffsIntegral (1 : LaurentSeries K) := by
  intro m
  rw [HahnSeries.coeff_one]
  split
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _

theorem CoeffsIntegral.neg {f : LaurentSeries K} (hf : CoeffsIntegral f) :
    CoeffsIntegral (-f) := by
  intro m
  rw [HahnSeries.coeff_neg]
  exact Subalgebra.neg_mem _ (hf m)

theorem CoeffsIntegral.mul {f g : LaurentSeries K} (hf : CoeffsIntegral f)
    (hg : CoeffsIntegral g) : CoeffsIntegral (f * g) := by
  intro m
  rw [HahnSeries.coeff_mul]
  exact Subalgebra.sum_mem _ fun ij _ => Subalgebra.mul_mem _ (hf ij.1) (hg ij.2)

theorem CoeffsIntegral.qExpand {f : LaurentSeries K} (hf : CoeffsIntegral f)
    (N : ℕ) [NeZero N] : CoeffsIntegral (ModularCurve.qExpand K N f) := by
  intro m
  by_cases hdvd : (N : ℤ) ∣ m
  · obtain ⟨c, rfl⟩ := hdvd
    rw [qExpand_coeff_mul]
    exact hf c
  · rw [qExpand_coeff_of_not_dvd N f hdvd]
    exact Subalgebra.zero_mem _

theorem CoeffsIntegral.qTwist {f : LaurentSeries K} (hf : CoeffsIntegral f)
    (u : Kˣ) (hu : ∀ m : ℤ, ((u ^ m : Kˣ) : K) ∈ integralClosure ℤ K) :
    CoeffsIntegral (ModularCurve.qTwist u f) := by
  intro m
  rw [qTwist_coeff]
  exact Subalgebra.mul_mem _ (hu m) (hf m)

theorem coeffsIntegral_C {a : K} (ha : a ∈ integralClosure ℤ K) : CoeffsIntegral (HahnSeries.C a) := by
  intro m
  rw [HahnSeries.C_apply, HahnSeries.coeff_single]
  split
  · exact ha
  · exact Subalgebra.zero_mem _

theorem intCast_mem_integralClosure (z : ℤ) : (z : K) ∈ integralClosure ℤ K := by
  rw [mem_integralClosure_iff]
  refine ⟨Polynomial.X - Polynomial.C z, Polynomial.monic_X_sub_C z, ?_⟩
  simp

theorem val_mem_integralClosure_of_pow_eq_one {u : Kˣ} {n : ℕ} (hn : n ≠ 0)
    (hu : u ^ n = 1) : (u : K) ∈ integralClosure ℤ K := by
  rw [mem_integralClosure_iff]
  refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, ?_⟩
  have hval : (u : K) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  simp [hval]

theorem zpow_val_mem_integralClosure_of_pow_eq_one {u : Kˣ} {n : ℕ} (hn : n ≠ 0)
    (hu : u ^ n = 1) (m : ℤ) : ((u ^ m : Kˣ) : K) ∈ integralClosure ℤ K := by
  have hrw : u ^ m = u ^ (m % (n : ℤ)).toNat := by
    have h1 : u ^ m = u ^ (m % (n : ℤ)) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv m (n : ℤ)]
      rw [zpow_add, zpow_mul, zpow_natCast, hu, one_zpow, mul_one]
    rw [h1, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg m (by exact_mod_cast hn))]
  rw [hrw, Units.val_pow_eq_pow_val]
  exact Subalgebra.pow_mem _ (val_mem_integralClosure_of_pow_eq_one hn hu) _

theorem coeffsIntegral_coeff_X_sub_C {a : LaurentSeries K}
    (ha : CoeffsIntegral a) (k : ℕ) :
    CoeffsIntegral ((Polynomial.X - Polynomial.C a).coeff k) := by
  match k with
  | 0 =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
      zero_sub]
    exact CoeffsIntegral.neg ha
  | 1 =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_C,
      if_neg (one_ne_zero), sub_zero]
    exact coeffsIntegral_one
  | (k + 2) =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    rw [if_neg (by omega), if_neg (by omega), sub_zero]
    exact coeffsIntegral_zero

theorem coeffsIntegral_coeff_mul {P Q : Polynomial (LaurentSeries K)}
    (hP : ∀ k, CoeffsIntegral (P.coeff k)) (hQ : ∀ k, CoeffsIntegral (Q.coeff k))
    (k : ℕ) : CoeffsIntegral ((P * Q).coeff k) := by
  rw [Polynomial.coeff_mul]
  intro a
  rw [HahnSeries.coeff_sum]
  exact Subalgebra.sum_mem _ fun ij _ => CoeffsIntegral.mul (hP ij.1) (hQ ij.2) a

theorem coeffsIntegral_coeff_prod {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (LaurentSeries K))
    (hP : ∀ i ∈ s, ∀ k, CoeffsIntegral ((P i).coeff k)) :
    ∀ k, CoeffsIntegral ((∏ i ∈ s, P i).coeff k) := by
  induction s using Finset.cons_induction with
  | empty =>
    intro k
    simp only [Finset.prod_empty]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using coeffsIntegral_one
    · rw [Polynomial.coeff_one, if_neg (by omega)]
      exact coeffsIntegral_zero
  | cons a s _ha ih =>
    intro k
    rw [Finset.prod_cons]
    exact coeffsIntegral_coeff_mul (hP a (Finset.mem_cons_self a s))
      (ih fun i hi k => hP i (Finset.mem_cons_of_mem hi) k) k

theorem exists_intCast_eq_of_mem [Algebra ℚ K] {q : ℚ}
    (h : algebraMap ℚ K q ∈ integralClosure ℤ K) : ∃ z : ℤ, q = (z : ℚ) := by
  rw [mem_integralClosure_iff] at h
  obtain ⟨P, hPmonic, hPeval⟩ := h
  have hcomp : algebraMap ℤ K = (algebraMap ℚ K).comp (Int.castRingHom ℚ) :=
    Subsingleton.elim _ _
  rw [hcomp, ← Polynomial.hom_eval₂] at hPeval
  have h0 : Polynomial.eval₂ (Int.castRingHom ℚ) q P = 0 :=
    FaithfulSMul.algebraMap_injective ℚ K (by rw [hPeval, map_zero])
  have hint : IsIntegral ℤ q :=
    ⟨P, hPmonic, by
      rwa [show algebraMap ℤ ℚ = Int.castRingHom ℚ from Subsingleton.elim _ _]⟩
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨z, by rw [← hz]; simp⟩

end IntegralCoeffs
p2m_reactivate "P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve.WQRel"

section UnitIntegral

theorem intCoeffs_single_mul_ofPowerSeries (k : ℤ) (Z : PowerSeries ℤ) :
    PhiGen.IntCoeffs (HahnSeries.single k (1 : ℚ) *
      HahnSeries.ofPowerSeries ℤ ℚ (Z.map (Int.castRingHom ℚ))) := by
  intro m
  rw [HahnSeries.coeff_single_mul, one_mul]
  by_cases hneg : m - k < 0
  · exact ⟨0, by rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hneg, Int.cast_zero]⟩
  · refine ⟨PowerSeries.coeff (m - k).toNat Z, ?_⟩
    have hcast : m - k = (((m - k).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg (not_lt.mp hneg)).symm
    rw [hcast, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
    rfl

theorem deltaSeries_inv_eq : deltaSeries⁻¹ = HahnSeries.single (-1 : ℤ) (1 : ℚ) *
    HahnSeries.ofPowerSeries ℤ ℚ (dedekindEtaUnitInv.map (Int.castRingHom ℚ)) := by
  apply inv_eq_of_mul_eq_one_right
  rw [deltaSeries, dedekindEtaUnitQ]
  calc HahnSeries.single (1 : ℤ) (1 : ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (dedekindEtaUnit.map (Int.castRingHom ℚ)) *
        (HahnSeries.single (-1 : ℤ) (1 : ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (dedekindEtaUnitInv.map (Int.castRingHom ℚ)))
      = (HahnSeries.single (1 : ℤ) (1 : ℚ) * HahnSeries.single (-1 : ℤ) (1 : ℚ)) *
        HahnSeries.ofPowerSeries ℤ ℚ ((dedekindEtaUnit * dedekindEtaUnitInv).map (Int.castRingHom ℚ)) := by
        rw [map_mul, map_mul]; ring
    _ = 1 := by
        rw [HahnSeries.single_mul_single, dedekindEtaUnit_mul_inv, map_one, map_one]
        simp

theorem intCoeffs_deltaSeries : PhiGen.IntCoeffs deltaSeries :=
  intCoeffs_single_mul_ofPowerSeries 1 dedekindEtaUnit

theorem intCoeffs_deltaSeries_inv : PhiGen.IntCoeffs deltaSeries⁻¹ := by
  rw [deltaSeries_inv_eq]
  exact intCoeffs_single_mul_ofPowerSeries (-1) dedekindEtaUnitInv

variable {K : Type*} [Field K] [Algebra ℚ K]

theorem coeffsIntegral_coeffEmb {f : LaurentSeries ℚ} (hf : PhiGen.IntCoeffs f) :
    CoeffsIntegral (coeffEmb K f) := by
  intro m
  obtain ⟨z, hz⟩ := hf m
  rw [coeffEmb_coeff, hz, map_intCast]
  exact intCast_mem_integralClosure z

theorem coeffEmb_qExpand (N : ℕ) [NeZero N] (x : LaurentSeries ℚ) :
    coeffEmb K (ModularCurve.qExpand ℚ N x) = ModularCurve.qExpand K N (coeffEmb K x) := by
  ext k
  by_cases h : (N : ℤ) ∣ k
  · obtain ⟨l, rfl⟩ := h
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

theorem coeffsIntegral_modularUnit : CoeffsIntegral (coeffEmb K (modularUnitSeries p)) := by
  rw [modularUnitSeries, deltaSeriesN, ← map_inv₀, map_mul, coeffEmb_qExpand]
  exact (coeffsIntegral_coeffEmb intCoeffs_deltaSeries).mul
    ((coeffsIntegral_coeffEmb intCoeffs_deltaSeries_inv).qExpand p)

theorem coeffsIntegral_modularUnit_inv : CoeffsIntegral (coeffEmb K (modularUnitSeries p))⁻¹ := by
  rw [← map_inv₀, modularUnitSeries, mul_inv_rev, inv_inv, deltaSeriesN, map_mul, coeffEmb_qExpand]
  exact ((coeffsIntegral_coeffEmb intCoeffs_deltaSeries).qExpand p).mul
    (coeffsIntegral_coeffEmb intCoeffs_deltaSeries_inv)

end UnitIntegral
p2m_reactivate "P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve.WQRel"

section ConjIntegral

variable {K : Type*} [Field K] [Algebra ℚ K] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
  (conj : Fin (p + 1) → LaurentSeries K)

theorem coeffsIntegral_conj (hζ1 : ζ ^ p = 1)
    (hconj0 : conj 0 = ModularCurve.qExpand K p (coeffEmb K (modularUnitSeries p)))
    (hconjS : ∀ b : Fin p, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ))
      (HahnSeries.C ((p : K) ^ 12) * (coeffEmb K (modularUnitSeries p))⁻¹))
    (i : Fin (p + 1)) : CoeffsIntegral (conj i) := by
  induction i using Fin.cases with
  | zero =>
    rw [hconj0]
    exact (coeffsIntegral_modularUnit p).qExpand p
  | succ b =>
    rw [hconjS]
    refine CoeffsIntegral.qTwist ?_ _ fun m => ?_
    · refine (coeffsIntegral_C ?_).mul (coeffsIntegral_modularUnit_inv p)
      exact Subalgebra.pow_mem _ (by exact_mod_cast intCast_mem_integralClosure (K := K) (p : ℤ)) 12
    · refine zpow_val_mem_integralClosure_of_pow_eq_one hp.out.ne_zero ?_ m
      rw [← pow_mul, mul_comm (b : ℕ) p, pow_mul, hζ1, one_pow]

theorem coeffsIntegral_phiProd_coeff (hζ1 : ζ ^ p = 1)
    (hconj0 : conj 0 = ModularCurve.qExpand K p (coeffEmb K (modularUnitSeries p)))
    (hconjS : ∀ b : Fin p, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ))
      (HahnSeries.C ((p : K) ^ 12) * (coeffEmb K (modularUnitSeries p))⁻¹))
    (k : ℕ) : CoeffsIntegral ((PhiGen.phiProd p conj).coeff k) := by
  rw [PhiGen.phiProd]
  exact coeffsIntegral_coeff_prod Finset.univ _
    (fun i _ k => coeffsIntegral_coeff_X_sub_C (coeffsIntegral_conj p ζ conj hζ1 hconj0 hconjS i) k) k

end ConjIntegral
p2m_reactivate "P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve.WQRel"

end UnitConj
p2m_reactivate "P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve.WQRel"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve.WQRel"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit.ModularCurve.WQRel"

p2m_open_scoped "ModularCurve ModularCurve.PhiGen" in

theorem ModularCurve.PhiGen.intCoeffs_of_phiProd_modularUnit_coeff_eq {K : Type*} [Field K] [Algebra ℚ K] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (conj : Fin (p + 1) → LaurentSeries K)
    (hconj0 : conj 0 = ModularCurve.qExpand K p (ModularCurve.coeffEmb K (ModularCurve.modularUnitSeries p)))
    (hconjS : ∀ b : Fin p, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ))
      (HahnSeries.C ((p : K) ^ 12) * (ModularCurve.coeffEmb K (ModularCurve.modularUnitSeries p))⁻¹))
    (c : ℕ → LaurentSeries ℚ)
    (hc : ∀ k : ℕ, (ModularCurve.PhiGen.phiProd p conj).coeff k =
      ModularCurve.coeffEmb K (ModularCurve.qExpand ℚ p (c k)))
    (hζ1 : ζ ^ p = 1) (k : ℕ) : ModularCurve.PhiGen.IntCoeffs (c k) := by
  intro m
  have h1 : algebraMap ℚ K ((c k).coeff m) =
      ((ModularCurve.PhiGen.phiProd p conj).coeff k).coeff ((p : ℤ) * m) := by
    rw [hc k, ModularCurve.coeffEmb_coeff, ModularCurve.qExpand_coeff_mul]
  have h2 := ModularCurve.UnitConj.coeffsIntegral_phiProd_coeff p ζ conj hζ1 hconj0 hconjS k ((p : ℤ) * m)
  rw [← h1] at h2
  exact ModularCurve.UnitConj.exists_intCast_eq_of_mem h2

p2m_open_scoped "ModularCurve ModularCurve.PhiGen" in

theorem ModularCurve.PhiGen.sum_mul_modularUnitSeries_pow_eq_zero_of_phiProd_coeff_eq {K : Type*} [Field K] [Algebra ℚ K] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (conj : Fin (p + 1) → LaurentSeries K)
    (hconj0 : conj 0 = ModularCurve.qExpand K p (ModularCurve.coeffEmb K (ModularCurve.modularUnitSeries p)))
    (c : ℕ → LaurentSeries ℚ)
    (hc : ∀ k : ℕ, (ModularCurve.PhiGen.phiProd p conj).coeff k =
      ModularCurve.coeffEmb K (ModularCurve.qExpand ℚ p (c k))) :
    (∑ k ∈ Finset.range (p + 2), c k * ModularCurve.modularUnitSeries p ^ k = 0) ∧
      c (p + 1) = 1 ∧ ∀ k : ℕ, p + 1 < k → c k = 0 := by
  have hinj : Function.Injective fun g : LaurentSeries ℚ => ModularCurve.coeffEmb K (ModularCurve.qExpand ℚ p g) :=
    (ModularCurve.coeffEmb K).injective.comp (ModularCurve.qExpand_injective (R := ℚ) (N := p))
  have hmonic := ModularCurve.PhiGen.phiProd_monic p conj
  have hdeg := ModularCurve.PhiGen.phiProd_natDegree p conj
  refine ⟨?_, ?_, ?_⟩
  ·
    have hev := ModularCurve.PhiGen.phiProd_eval_conj p conj 0
    rw [Polynomial.eval_eq_sum_range' (n := p + 2) (by omega), hconj0] at hev
    apply hinj
    simp only [map_sum, map_mul, map_pow, map_zero, ModularCurve.UnitConj.coeffEmb_qExpand]
    rw [← hev]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc k, ModularCurve.UnitConj.coeffEmb_qExpand]
  ·
    apply hinj
    show ModularCurve.coeffEmb K (ModularCurve.qExpand ℚ p (c (p + 1))) =
      ModularCurve.coeffEmb K (ModularCurve.qExpand ℚ p 1)
    rw [← hc, map_one, map_one, ← hdeg]
    exact hmonic.coeff_natDegree
  ·
    intro k hk
    apply hinj
    show ModularCurve.coeffEmb K (ModularCurve.qExpand ℚ p (c k)) = ModularCurve.coeffEmb K (ModularCurve.qExpand ℚ p 0)
    rw [← hc, map_zero, map_zero]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

namespace ModularCurve p2m_export "ModularCurve" "dedekindEtaUnitQ deltaSeries deltaSeriesN modularUnitSeries qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jq ofPowerSeries_coeff_of_neg jqModC jqModC_rat coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr coeffEmb coeffEmb_coeff qTwist qTwist_coeff qTwist_one_apply qTwist_qTwist qTwist_qExpand PhiGen.phiProd PhiGen.phiProd_monic PhiGen.phiProd_natDegree PhiGen.phiProd_eval_conj PhiGen.IntCoeffs PhiGen.PhiGenDescends coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut mem_range_qExpand_of_qTwist_eq PhiGen.mem_range_coeffEmb_of_forall_coeffMap_eq PhiGen.mem_range_coeffEmb_qExpand_of_mem_inter PhiGen.mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit" end ModularCurve
p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.solution_impl (p : ℕ) [Fact p.Prime] :
    ∃ (n : ℕ) (S : Fin n → Polynomial ℚ),
      ModularCurve.modularUnitSeries p ^ n + ∑ i : Fin n,
        Polynomial.aeval (ModularCurve.jqModC ℚ) (S i) *
          ModularCurve.modularUnitSeries p ^ (i : ℕ) = 0
      ∧ ∀ (i : Fin n) (k : ℤ), ∃ m : ℤ,
        (Polynomial.aeval (ModularCurve.jqModC ℚ) (S i)).coeff k = (m : ℚ) := by
  classical
  haveI hp : Fact (Nat.Prime p) := ‹Fact p.Prime›
  let K := CyclotomicField p ℚ
  haveI : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  haveI : FiniteDimensional ℚ K := IsCyclotomicExtension.finiteDimensional {p} ℚ K
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p := IsCyclotomicExtension.zeta_spec p ℚ K
  let ζu : Kˣ := (hζ.isUnit hp.out.ne_zero).unit
  have hζu : (ζu : K) = IsCyclotomicExtension.zeta p ℚ K := IsUnit.unit_spec _
  have hζ' : IsPrimitiveRoot (ζu : K) p := by rw [hζu]; exact hζ
  have hζ1 : ζu ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hζu, hζ.pow_eq_one, Units.val_one])

  let conj : Fin (p + 1) → LaurentSeries K :=
    Fin.cases (ModularCurve.qExpand K p (ModularCurve.coeffEmb K (ModularCurve.modularUnitSeries p)))
      (fun b => ModularCurve.qTwist (ζu ^ (b : ℕ))
        (HahnSeries.C ((p : K) ^ 12) * (ModularCurve.coeffEmb K (ModularCurve.modularUnitSeries p))⁻¹))
  have hconj0 : conj 0 = ModularCurve.qExpand K p (ModularCurve.coeffEmb K (ModularCurve.modularUnitSeries p)) := rfl
  have hconjS : ∀ b : Fin p, conj b.succ = ModularCurve.qTwist (ζu ^ (b : ℕ))
      (HahnSeries.C ((p : K) ^ 12) * (ModularCurve.coeffEmb K (ModularCurve.modularUnitSeries p))⁻¹) :=
    fun b => rfl

  obtain ⟨c, hc⟩ := ModularCurve.PhiGen.exists_qExpand_descent_phiProd_modularUnit p ζu conj hζ' hconj0 hconjS
  have hint := ModularCurve.PhiGen.intCoeffs_of_phiProd_modularUnit_coeff_eq p ζu conj hconj0 hconjS c hc hζ1
  obtain ⟨hrel, htop, -⟩ :=
    ModularCurve.PhiGen.sum_mul_modularUnitSeries_pow_eq_zero_of_phiProd_coeff_eq p conj hconj0 c hc
  have hmem : ∀ k : ℕ, c k ∈ Algebra.adjoin ℚ {ModularCurve.jq} := fun k =>
    ModularCurve.PhiGen.mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit p ζu hζ' conj hconj0 hconjS c hc k

  have hS : ∀ k : ℕ, ∃ S : Polynomial ℚ, Polynomial.aeval ModularCurve.jq S = c k := fun k => by
    have h := hmem k
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h
    exact h
  choose S hS using hS
  refine ⟨p + 1, fun i => S i, ?_, ?_⟩
  · rw [Finset.sum_range_succ, htop, one_mul, Finset.sum_range] at hrel
    rw [ModularCurve.jqModC_rat, add_comm]
    simp_rw [hS]
    exact hrel
  · intro i k
    obtain ⟨m, hm⟩ := hint i k
    exact ⟨m, by rw [ModularCurve.jqModC_rat, hS]; exact hm⟩

theorem solution (p : ℕ) [Fact p.Prime] :
    ∃ (n : ℕ) (S : Fin n → Polynomial ℚ), ModularCurve.modularUnitSeries p ^ n + ∑ i : Fin n, Polynomial.aeval (ModularCurve.jqModC ℚ) (S i) * ModularCurve.modularUnitSeries p ^ (i : ℕ) = 0 ∧ ∀ (i : Fin n) (k : ℤ), ∃ m : ℤ, (Polynomial.aeval (ModularCurve.jqModC ℚ) (S i)).coeff k = (m : ℚ) :=
  ModularCurve.solution_impl p

end S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit
end P2MW
export P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit (solution)
