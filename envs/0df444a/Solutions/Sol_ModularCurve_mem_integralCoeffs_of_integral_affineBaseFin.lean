-- Prove2me | solution 1 for ModularCurve.mem_integralCoeffs_of_integral_affineBaseFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7ebfa38d-92d8-54e4-b96e-97380465815b

import Mathlib
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Theorems.Thm_ModularCurve_exists_forall_coeff_smul_mem_and_exists_inv_coeff_mem_of_forall_ord_neg
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin.ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "jqModC map_jqModC jqModC_eq_map_intCast modularFunctionFieldFull coeffMap algebraMap_laurentSeries_eq_single laurentBaseChange modularFunctionFieldBar exists_forall_coeff_smul_mem_and_exists_inv_coeff_mem_of_forall_ord_neg transcendental_jqModC"
p2m_open "ModularCurve"
namespace IntCoeff

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (M : ℕ) [NeZero M]

local notation "Qb" => AlgebraicClosure ℚ
local notation "FB" => modularFunctionFieldBar M

theorem coe_constantsHom (a : A) :
    ((constantsHom M A a : FB) : LaurentSeries Qb) = algebraMap Qb (LaurentSeries Qb) (a : Qb) := rfl

theorem coe_jBar : ((jBar M : FB) : LaurentSeries Qb) = jqModC Qb := by
  show coeffMap (algebraMap ℚ Qb) (jqModC ℚ) = jqModC Qb
  exact map_jqModC _

theorem coe_mem_integralCoeffs_of_mem {c : FB} (hc : c ∈ affineBaseFin M A) :
    (c : LaurentSeries Qb) ∈ integralCoeffs A.toSubring := by
  unfold affineBaseFin at hc
  induction hc using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | rfl
    · rw [coe_constantsHom]; exact constSeries_mem_integralCoeffs A.toSubring ⟨a, a.2⟩
    · rw [coe_jBar]; exact jqModC_mem_integralCoeffs A.toSubring
  | zero => simpa using zero_mem _
  | one => simpa using one_mem _
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

theorem affineBaseFin_le (W : Place Qb FB) (hj : (jBar M : FB) ∈ W.toValuationSubring) :
    affineBaseFin M A ≤ W.toValuationSubring.toSubring := by
  rw [affineBaseFin, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl)
  · exact W.algebraMap_mem' (a : Qb)
  · exact hj

theorem exists_mul_pow_mem {c : FB} (hc : c ∈ affineBaseFin M A) :
    ∃ D : ℕ, ∀ (W : Place Qb FB), (jBar M : FB) ∉ W.toValuationSubring →
      ∀ D' : ℕ, D ≤ D' → c * (jBar M : FB)⁻¹ ^ D' ∈ W.toValuationSubring := by
  unfold affineBaseFin at hc
  induction hc using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | rfl
    · exact ⟨0, fun W hj D' _ => mul_mem (W.algebraMap_mem' (a : Qb))
        (pow_mem ((W.toValuationSubring.mem_or_inv_mem _).resolve_left hj) _)⟩
    · refine ⟨1, fun W hj D' hD' => ?_⟩
      have hj0 : (jBar M : FB) ≠ 0 := fun h => hj (h ▸ zero_mem _)
      obtain ⟨D'', rfl⟩ := Nat.exists_eq_add_of_le hD'
      rw [pow_add, pow_one, ← mul_assoc, mul_inv_cancel₀ hj0, one_mul]
      exact pow_mem ((W.toValuationSubring.mem_or_inv_mem _).resolve_left hj) _
  | zero => exact ⟨0, fun W _ D' _ => by rw [zero_mul]; exact zero_mem _⟩
  | one => exact ⟨0, fun W hj D' _ => by
      rw [one_mul]; exact pow_mem ((W.toValuationSubring.mem_or_inv_mem _).resolve_left hj) _⟩
  | add x y _ _ hx hy =>
    obtain ⟨D₁, h₁⟩ := hx
    obtain ⟨D₂, h₂⟩ := hy
    exact ⟨max D₁ D₂, fun W hj D' hD' => by
      rw [add_mul]
      exact add_mem (h₁ W hj D' ((le_max_left _ _).trans hD')) (h₂ W hj D' ((le_max_right _ _).trans hD'))⟩
  | neg x _ hx =>
    obtain ⟨D, h⟩ := hx
    exact ⟨D, fun W hj D' hD' => by rw [neg_mul]; exact neg_mem (h W hj D' hD')⟩
  | mul x y _ _ hx hy =>
    obtain ⟨D₁, h₁⟩ := hx
    obtain ⟨D₂, h₂⟩ := hy
    refine ⟨D₁ + D₂, fun W hj D' hD' => ?_⟩
    have : x * y * (jBar M : FB)⁻¹ ^ D' = (x * (jBar M : FB)⁻¹ ^ D₁) * (y * (jBar M : FB)⁻¹ ^ (D' - D₁)) := by
      rw [mul_mul_mul_comm, ← pow_add, Nat.add_sub_cancel' (le_of_add_le_left hD')]
    rw [this]
    exact mul_mem (h₁ W hj D₁ le_rfl) (h₂ W hj (D' - D₁) (by omega))

theorem mem_of_monic_root (W : Place Qb FB) (P : Polynomial FB) (hP : P.Monic)
    (hcoef : ∀ i, P.coeff i ∈ W.toValuationSubring) (x : FB) (hx : P.eval x = 0) :
    x ∈ W.toValuationSubring := by
  set O := W.toValuationSubring
  have hlift : P ∈ Polynomial.lifts (algebraMap O FB) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨P.coeff i, hcoef i⟩, rfl⟩
  obtain ⟨Q, hQP, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hP
  have hint : IsIntegral O x := ⟨Q, hQm, by rw [← Polynomial.eval_map, hQP, hx]⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := FB)).mp hint
  rw [← hy]; exact y.2

noncomputable def redT : ↥A.toSubring →+* IsLocalRing.ResidueField A := IsLocalRing.residue A

theorem redT_eq_zero_iff {a : Qb} (ha : a ∈ A) :
    redT A ⟨a, ha⟩ = 0 ↔ ¬IsUnit (⟨a, ha⟩ : A) := by
  show IsLocalRing.residue A ⟨a, ha⟩ = 0 ↔ _
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem coeffRed_eq_zero_iff (x : integralCoeffs A.toSubring) :
    coeffRed A.toSubring (redT A) x = 0 ↔
      ∀ n : ℤ, ¬IsUnit (⟨(x : LaurentSeries Qb).coeff n, x.2 n⟩ : A) := by
  constructor
  · intro h n
    have := congrArg (fun s : LaurentSeries (IsLocalRing.ResidueField A) => s.coeff n) h
    simp only [coeffRed_coeff, HahnSeries.coeff_zero] at this
    exact (redT_eq_zero_iff A (x.2 n)).mp this
  · intro h
    ext n
    rw [coeffRed_coeff, HahnSeries.coeff_zero]
    exact (redT_eq_zero_iff A (x.2 n)).mpr (h n)

theorem isUnit_mk_iff {a : Qb} (ha : a ∈ A) : IsUnit (⟨a, ha⟩ : A) ↔ a ≠ 0 ∧ a⁻¹ ∈ A := by
  constructor
  · intro hu
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    have hw' : a * (w : Qb) = 1 := by
      have := congrArg Subtype.val hw; push_cast at this; exact this
    have ha0 : a ≠ 0 := fun h => by rw [h, zero_mul] at hw'; exact zero_ne_one hw'
    refine ⟨ha0, ?_⟩
    rw [show a⁻¹ = (w : Qb) from (eq_inv_of_mul_eq_one_right hw').symm]
    exact w.2
  · rintro ⟨ha0, hinv⟩
    exact isUnit_iff_exists_inv.mpr ⟨⟨a⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

theorem jqModC_ne_zero' (L : Type*) [Field L] : jqModC L ≠ 0 := fun h =>
  transcendental_jqModC L (h ▸ isAlgebraic_zero)

private theorem redT_mk_eq {x : Qb} (hx : x ∈ A.toSubring) (y : A.toSubring) (h : x = (y : Qb)) :
    redT A ⟨x, hx⟩ = redT A y := by
  subst h; rfl

theorem coeffRed_jqModC' :
    coeffRed A.toSubring (redT A) ⟨jqModC Qb, jqModC_mem_integralCoeffs A.toSubring⟩
      = jqModC (IsLocalRing.ResidueField A) := by
  ext n
  rw [coeffRed_coeff]
  rw [redT_mk_eq A _ (((jqModC ℤ).coeff n : ℤ) : A.toSubring) (by
      show (jqModC Qb).coeff n = (((((jqModC ℤ).coeff n : ℤ) : A.toSubring)) : Qb)
      rw [jqModC_eq_map_intCast (K := Qb), HahnSeries.map_coeff]; simp)]
  rw [map_intCast, jqModC_eq_map_intCast (K := IsLocalRing.ResidueField A), HahnSeries.map_coeff]
  simp

end IntCoeff
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "jqModC map_jqModC jqModC_eq_map_intCast modularFunctionFieldFull coeffMap algebraMap_laurentSeries_eq_single laurentBaseChange modularFunctionFieldBar exists_forall_coeff_smul_mem_and_exists_inv_coeff_mem_of_forall_ord_neg transcendental_jqModC"
p2m_open "ModularCurve"
namespace IntCoeff

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (M : ℕ) [NeZero M]

local notation "Qb" => AlgebraicClosure ℚ
local notation "FB" => modularFunctionFieldBar M

theorem main (e : FB)
    (he : ∃ p : Polynomial (affineBaseFin M A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin M A).subtype e p = 0) :
    (e : LaurentSeries Qb) ∈ integralCoeffs A.toSubring := by
  classical
  rcases eq_or_ne e 0 with rfl | he0
  · intro n; simp
  obtain ⟨p, hpm, hpe⟩ := he

  set P : Polynomial FB := p.map (affineBaseFin M A).subtype with hPdef
  have hPm : P.Monic := hpm.map _
  have hPe : P.eval e = 0 := by rw [hPdef, Polynomial.eval_map]; exact hpe
  have hPc : ∀ i, P.coeff i ∈ affineBaseFin M A := fun i => by
    rw [hPdef, Polynomial.coeff_map]; exact (p.coeff i).2
  have hPdeg : P.natDegree ≠ 0 := by
    intro h0
    have hP1 : P = 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero h0, ← h0, hPm.coeff_natDegree, map_one]
    rw [hP1, Polynomial.eval_one] at hPe
    exact one_ne_zero hPe
  have hj0 : (jBar M : FB) ≠ 0 := by
    intro h
    have := congrArg (fun z : FB => (z : LaurentSeries Qb)) h
    beta_reduce at this
    rw [coe_jBar, ZeroMemClass.coe_zero] at this
    exact jqModC_ne_zero' Qb this

  choose Df hDf using fun i => exists_mul_pow_mem A M (hPc i)
  set D : ℕ := (Finset.range (P.natDegree + 1)).sup Df with hDdef
  have hDi : ∀ i, i ≤ P.natDegree → Df i ≤ D := fun i hi =>
    Finset.le_sup (f := Df) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  set u : FB := (jBar M : FB)⁻¹ with hu
  set f : FB := e * u ^ D with hf
  have hf0 : f ≠ 0 := mul_ne_zero he0 (pow_ne_zero _ (inv_ne_zero hj0))

  have heO : ∀ W : Place Qb FB, (jBar M : FB) ∈ W.toValuationSubring → e ∈ W.toValuationSubring :=
    fun W hjW => mem_of_monic_root M W P hPm (fun i => affineBaseFin_le A M W hjW (hPc i)) e hPe

  have hfO : ∀ W : Place Qb FB, (jBar M : FB) ∉ W.toValuationSubring → f ∈ W.toValuationSubring := by
    intro W hjW
    have huW : u ∈ W.toValuationSubring := (W.toValuationSubring.mem_or_inv_mem _).resolve_left hjW
    let Q : Polynomial FB := P.scaleRoots (u ^ D)
    have hQm : Q.Monic := (Polynomial.monic_scaleRoots_iff (u ^ D)).mpr hPm
    have hQe : Q.eval f = 0 := by
      have h := Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id FB) (p := P) (r := e) (s := u ^ D) hPe
      change Q.eval (u ^ D * e) = 0 at h
      rw [hf, mul_comm]; exact h
    refine mem_of_monic_root M W Q hQm (fun i => ?_) f hQe
    change (P.scaleRoots (u ^ D)).coeff i ∈ W.toValuationSubring
    rw [Polynomial.coeff_scaleRoots]
    by_cases hi : i < P.natDegree
    · have hle : Df i ≤ D * (P.natDegree - i) := by
        calc Df i ≤ D := hDi i hi.le
          _ = D * 1 := (mul_one D).symm
          _ ≤ D * (P.natDegree - i) := Nat.mul_le_mul_left D (by omega)
      rw [← pow_mul]
      exact hDf i W hjW _ hle
    · by_cases hi' : i = P.natDegree
      · subst hi'
        rw [Polynomial.Monic.coeff_natDegree hPm, one_mul]
        exact pow_mem (pow_mem huW _) _
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact zero_mem _

  have hpole : ∀ W : Place Qb FB, W.ord f < 0 → ∃ a : A, 0 < W.ord
      ((jBar M : FB) - algebraMap Qb FB (a : Qb)) := by
    intro W hW
    have hfW : f ∉ W.toValuationSubring := fun h => by
      have := W.ord_nonneg_of_mem h; omega
    have hjW : (jBar M : FB) ∈ W.toValuationSubring := by
      by_contra h; exact hfW (hfO W h)
    have heW := heO W hjW
    have huW : u ∉ W.toValuationSubring := fun h => hfW (mul_mem heW (pow_mem h _))
    refine ⟨0, ?_⟩
    rw [ZeroMemClass.coe_zero, map_zero, sub_zero]
    have h1 : W.ord u < 0 := by
      by_contra h; exact huW (W.mem_of_ord_nonneg (inv_ne_zero hj0) (by omega))
    rw [hu, W.ord_inv] at h1
    omega

  obtain ⟨c, hc0, hcf, n, hn0, hninv⟩ :=
    ModularCurve.exists_forall_coeff_smul_mem_and_exists_inv_coeff_mem_of_forall_ord_neg A M f hf0 hpole

  have hcsm : algebraMap Qb (LaurentSeries Qb) c * (f : LaurentSeries Qb) = c • (f : LaurentSeries Qb) := by
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul]
  set g : FB := algebraMap Qb FB c * e with hgdef
  have hg_eq : ((g : FB) : LaurentSeries Qb) = (c • (f : LaurentSeries Qb)) * (jqModC Qb) ^ D := by
    have hfj : f * (jBar M : FB) ^ D = e := by
      rw [hf, mul_assoc, ← mul_pow, hu, inv_mul_cancel₀ hj0, one_pow, mul_one]
    rw [hgdef, ← hfj, ← hcsm]
    push_cast
    rw [coe_jBar, mul_assoc]
  have hcfI : (c • (f : LaurentSeries Qb)) ∈ integralCoeffs A.toSubring := fun k => hcf k
  have hjI : (jqModC Qb) ^ D ∈ integralCoeffs A.toSubring := pow_mem (jqModC_mem_integralCoeffs A.toSubring) D
  have hgI : ((g : FB) : LaurentSeries Qb) ∈ integralCoeffs A.toSubring := by
    rw [hg_eq]; exact mul_mem hcfI hjI

  have hjred : coeffRed A.toSubring (redT A) ⟨jqModC Qb, jqModC_mem_integralCoeffs A.toSubring⟩ ≠ 0 := by
    rw [coeffRed_jqModC']; exact jqModC_ne_zero' _
  have hprim : coeffRed A.toSubring (redT A) ⟨_, hgI⟩ ≠ 0 := by
    have hmul : (⟨_, hgI⟩ : integralCoeffs A.toSubring)
        = ⟨_, hcfI⟩ * ⟨jqModC Qb, jqModC_mem_integralCoeffs A.toSubring⟩ ^ D := by
      apply Subtype.ext; push_cast; exact hg_eq
    rw [hmul, map_mul, map_pow]
    refine mul_ne_zero ?_ (pow_ne_zero _ hjred)
    intro h0
    have h1 := (coeffRed_eq_zero_iff A ⟨_, hcfI⟩).mp h0 n
    exact h1 ((isUnit_mk_iff A (hcfI n)).mpr ⟨hn0, hninv⟩)

  have hcinv : c⁻¹ ∈ A := by
    by_contra hcinv
    have hcA : c ∈ A := (A.mem_or_inv_mem c).resolve_right hcinv
    have hcu : ¬IsUnit (⟨c, hcA⟩ : A) := fun hu => hcinv ((isUnit_mk_iff A hcA).mp hu).2
    have hcI : algebraMap Qb (LaurentSeries Qb) c ∈ integralCoeffs A.toSubring :=
      constSeries_mem_integralCoeffs A.toSubring ⟨c, hcA⟩
    have hcred : coeffRed A.toSubring (redT A) ⟨_, hcI⟩ = 0 := by
      ext m
      rw [coeffRed_coeff, HahnSeries.coeff_zero]
      by_cases hm : m = 0
      · subst hm
        rw [redT_mk_eq A _ (⟨c, hcA⟩ : A.toSubring) (by
            show (algebraMap Qb (LaurentSeries Qb) c).coeff 0 = c
            rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_same])]
        exact (redT_eq_zero_iff A hcA).mpr hcu
      · rw [redT_mk_eq A _ (0 : A.toSubring) (by
            show (algebraMap Qb (LaurentSeries Qb) c).coeff m = ((0 : A.toSubring) : Qb)
            rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne hm]; rfl), map_zero]

    let Q : Polynomial FB := P.scaleRoots (algebraMap Qb FB c)
    have hQe : Q.eval g = 0 := by
      have h := Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id FB) (p := P) (r := e) (s := algebraMap Qb FB c) hPe
      change Q.eval (algebraMap Qb FB c * e) = 0 at h
      rw [hgdef]; exact h
    have hQdeg : Q.natDegree = P.natDegree := Polynomial.natDegree_scaleRoots _ _
    have hQc : ∀ i, ((Q.coeff i : FB) : LaurentSeries Qb) ∈ integralCoeffs A.toSubring := fun i => by
      change (((P.scaleRoots (algebraMap Qb FB c)).coeff i : FB) : LaurentSeries Qb) ∈ _
      rw [Polynomial.coeff_scaleRoots]
      push_cast
      exact mul_mem (coe_mem_integralCoeffs_of_mem A M (hPc i)) (pow_mem hcI _)
    set G : integralCoeffs A.toSubring := ⟨_, hgI⟩ with hG
    have hrel : ∑ i ∈ Finset.range (P.natDegree + 1),
        (⟨_, hQc i⟩ : integralCoeffs A.toSubring) * G ^ i = 0 := by
      apply Subtype.ext
      push_cast
      rw [Polynomial.eval_eq_sum_range, hQdeg] at hQe
      have h := congrArg (fun z : FB => (z : LaurentSeries Qb)) hQe
      push_cast at h
      exact h
    have hρ := congrArg (coeffRed A.toSubring (redT A)) hrel
    rw [map_sum, map_zero, Finset.sum_range_succ] at hρ
    have hvan : ∑ i ∈ Finset.range P.natDegree,
        coeffRed A.toSubring (redT A) ((⟨_, hQc i⟩ : integralCoeffs A.toSubring) * G ^ i) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi' : i < P.natDegree := Finset.mem_range.mp hi
      have hfac : (⟨_, hQc i⟩ : integralCoeffs A.toSubring)
          = ⟨_, coe_mem_integralCoeffs_of_mem A M (hPc i)⟩ * ⟨_, hcI⟩ ^ (P.natDegree - i) := by
        apply Subtype.ext
        push_cast
        change (((P.scaleRoots (algebraMap Qb FB c)).coeff i : FB) : LaurentSeries Qb) = _
        rw [Polynomial.coeff_scaleRoots]
        push_cast
        rfl
      rw [map_mul, hfac, map_mul, map_pow, hcred, zero_pow (by omega), mul_zero, zero_mul]
    have htop : (⟨_, hQc P.natDegree⟩ : integralCoeffs A.toSubring) = 1 := by
      apply Subtype.ext
      push_cast
      change (((P.scaleRoots (algebraMap Qb FB c)).coeff P.natDegree : FB) : LaurentSeries Qb) = 1
      rw [Polynomial.coeff_scaleRoots, Nat.sub_self, pow_zero, mul_one, hPm.coeff_natDegree]
      rfl
    rw [hvan, zero_add, htop, one_mul, map_pow] at hρ
    exact hprim ((pow_eq_zero_iff hPdeg).mp hρ)

  intro m
  have h1 : ((g : FB) : LaurentSeries Qb).coeff m = c * (e : LaurentSeries Qb).coeff m := by
    rw [hgdef]
    push_cast
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  have h2 : (e : LaurentSeries Qb).coeff m = c⁻¹ * ((g : FB) : LaurentSeries Qb).coeff m := by
    rw [h1, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  rw [h2]
  exact mul_mem hcinv (hgI m)

end IntCoeff
end ModularCurve

open ModularCurve.CharPModel ModularCurve.CharPReduction in
theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : ℕ) [NeZero M]
    (e : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
    (he : ∃ p : Polynomial (affineBaseFin M A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin M A).subtype e p = 0) :
    (e : LaurentSeries (AlgebraicClosure ℚ)) ∈ integralCoeffs A.toSubring :=
  ModularCurve.IntCoeff.main A M e he

end S_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin
end P2MW
export P2MW.S_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin (solution)
