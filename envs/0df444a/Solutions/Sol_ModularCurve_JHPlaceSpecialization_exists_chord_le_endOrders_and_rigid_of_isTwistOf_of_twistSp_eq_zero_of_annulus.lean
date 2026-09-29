-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_twistSp_eq_zero_of_annulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/0d895543-b11f-543b-a6fd-6f8ff45d629c

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf
import Definitions.Def_ModularCurve_JHTwistType
import Definitions.Def_ModularCurve_JHTwistedDatum
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_twistSp_eq_zero_of_annulus
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

namespace AnnulusSlope

def tent (x : ℚ) (d : ℕ) : ℚ := max 0 (1 - |x - d|)

theorem tent_nonneg (x : ℚ) (d : ℕ) : 0 ≤ tent x d := le_max_left _ _

theorem tent_eq_zero_of_ge (x : ℚ) (d : ℕ) (h : (d : ℚ) + 1 ≤ x) : tent x d = 0 := by
  unfold tent; rw [max_eq_left]; rw [abs_of_nonneg (by linarith)]; linarith

theorem tent_eq_zero_of_le (x : ℚ) (d : ℕ) (h : x + 1 ≤ d) : tent x d = 0 := by
  unfold tent; rw [max_eq_left]; rw [abs_of_nonpos (by linarith)]; linarith

theorem sum_tent_top (x : ℚ) (e : ℕ) (h1 : (e : ℚ) < x) (h2 : x ≤ e + 1) :
    (∑ d ∈ Finset.range (e + 2), tent x d = 1) ∧ (∑ d ∈ Finset.range (e + 2), (d : ℚ) * tent x d = x) := by
  have hz : ∀ d ∈ Finset.range e, tent x d = 0 := by
    intro d hd
    have h2 : d + 1 ≤ e := Finset.mem_range.mp hd
    have h3 : (d : ℚ) + 1 ≤ e := by exact_mod_cast h2
    exact tent_eq_zero_of_ge x d (by linarith)
  have he : tent x e = 1 - (x - e) := by
    unfold tent; rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
  have he1 : tent x (e + 1) = x - e := by
    unfold tent; push_cast; rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]; ring
  constructor
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero hz, he, he1]; ring
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero (fun d hd => by rw [hz d hd, mul_zero]), he, he1]
    push_cast; ring

theorem sum_tent_eq_one_and_sum_mul_tent_eq (x : ℚ) (hx : 0 ≤ x) (e : ℕ) (hxe : x ≤ e) :
    (∑ d ∈ Finset.range (e + 1), tent x d = 1) ∧ (∑ d ∈ Finset.range (e + 1), (d : ℚ) * tent x d = x) := by
  induction e with
  | zero =>
    have hx0 : x = 0 := le_antisymm (by exact_mod_cast hxe) hx
    subst hx0
    simp [tent]
  | succ e ih =>
    rcases le_or_gt x (e : ℚ) with h | h
    · obtain ⟨ih1, ih2⟩ := ih h
      have ht : tent x (e + 1) = 0 := tent_eq_zero_of_le x (e + 1) (by push_cast; linarith)
      refine ⟨?_, ?_⟩
      · rw [Finset.sum_range_succ, ih1, ht]; simp
      · rw [Finset.sum_range_succ, ih2, ht]; simp
    · exact sum_tent_top x e h (by exact_mod_cast hxe)

theorem abel_one (a : ℕ → ℤ) (e : ℕ) (he : 1 ≤ e) :
    ∑ d ∈ Finset.Ico 1 e, ((e : ℤ) - d) * (a (d - 1) - 2 * a d + a (d + 1)) = (a e - a 0) - e * (a 1 - a 0) := by
  induction e with
  | zero => omega
  | succ e ih =>
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · simp
    · rw [Finset.sum_Ico_succ_top hpos]
      have : ∑ d ∈ Finset.Ico 1 e, ((((e + 1 : ℕ) : ℤ)) - d) * (a (d - 1) - 2 * a d + a (d + 1)) =
          ∑ d ∈ Finset.Ico 1 e, (((e : ℤ)) - d) * (a (d - 1) - 2 * a d + a (d + 1)) +
            ∑ d ∈ Finset.Ico 1 e, (a (d - 1) - 2 * a d + a (d + 1)) := by
        rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro d _; push_cast; ring
      rw [this, ih hpos]

      have htel : ∀ n : ℕ, 1 ≤ n → ∑ d ∈ Finset.Ico 1 n, (a (d - 1) - 2 * a d + a (d + 1)) = (a n - a (n - 1)) - (a 1 - a 0) := by
        intro n hn
        induction n with
        | zero => omega
        | succ n ihn =>
          rcases Nat.eq_zero_or_pos n with rfl | hn0
          · simp
          · rw [Finset.sum_Ico_succ_top hn0, ihn hn0]
            simp only [Nat.add_sub_cancel]
            push_cast
            ring
      rw [htel e hpos]
      push_cast
      ring

theorem abel_two (a : ℕ → ℤ) (e : ℕ) (he : 1 ≤ e) :
    ∑ d ∈ Finset.Ico 1 e, (d : ℤ) * (a (d - 1) - 2 * a d + a (d + 1)) = e * (a e - a (e - 1)) - (a e - a 0) := by
  induction e with
  | zero => omega
  | succ e ih =>
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · simp
    · rw [Finset.sum_Ico_succ_top hpos, ih hpos]
      push_cast
      ring

end AnnulusSlope

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JHPlaceSpecialization_exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_twistSp_eq_zero_of_annulus.ModularCurve ModularCurve.JHNeronObjectAtP"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "JHNeronObjectAtP.ΓN JHNeronObjectAtP.Fbar JHNeronObjectAtP arithmeticGalois qExpand ssPlacesQExp diamondActionModL infSubgroup ssNodePairsQExp xHFunctionField xHFunctionFieldBar qExpFrobeniusPlaceModL JHPlaceSpecialization.IsAffinePlace JHPlaceSpecialization.Fixed JHPlaceSpecialization JHPlaceSpecialization.IsInftySide JHPlaceSpecialization.IsZeroSide JHPlaceSpecialization.ProlongationDatum JHPlaceSpecialization.TwistVec JHPlaceSpecialization.AnnulusPositionLaw JHPlaceSpecialization.twistChainVal JHPlaceSpecialization.twistCircleDeg JHPlaceSpecialization.twistEndOrderFst JHPlaceSpecialization.twistEndOrderSnd JHPlaceSpecialization.TwistedFibreDatum JHPlaceSpecialization.twistAnnulusDeg JHPlaceSpecialization.twistPosMoment JHPlaceSpecialization.flipParam qExpFrobeniusPlaceModL_bijective JHPlaceSpecialization.den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus"
namespace JHPlaceSpecialization
p2m_export "ModularCurve.JHPlaceSpecialization" "IsAffinePlace Fixed reduceFst reduceSnd IsStrictFst IsStrictSnd TypeDichotomy IsGoodDiv fstDiv sndDiv IsInftySide IsZeroSide ProlongationDatum mk TwistVec AnnulusPositionLaw twistChainVal twistCircleDeg twistEndShareFst twistEndShareSnd twistEndOrderFst twistEndOrderSnd IsTwistOf TwistedFibreDatum twistAnnulusDeg twistPosMoment flipParam twistSpData den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus"
namespace Chord
p2m_open "ModularCurve.JHPlaceSpecialization ModularCurve"

variable {p M : ℕ} {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
variable (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
  (e : ↥SS → ℕ) (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
  (pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ)
  (a : TwistVec ↥SS) (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS)

open Classical in

theorem twistCircleDeg_eq (d : ℕ) :
    twistCircleDeg SS An pos X s d = ∑ V ∈ X.support with V ∈ (An s).dom, (X V : ℚ) * AnnulusSlope.tent (pos s V) d := rfl

open Classical in

theorem twistPosMoment_eq (he : 1 ≤ e s)
    (hpos : ∀ V ∈ X.support, V ∈ (An s).dom → 0 ≤ pos s V ∧ pos s V ≤ e s)
    (hcirc : ∀ d : ℕ, 1 ≤ d → d + 1 ≤ e s →
      twistCircleDeg SS An pos X s d = -((twistChainVal SS e a s (d - 1) - 2 * twistChainVal SS e a s d + twistChainVal SS e a s (d + 1) : ℤ) : ℚ))
    (hintSnd : (twistCircleDeg SS An pos X s (e s)).den = 1) :
    twistPosMoment SS An pos X s = (e s : ℚ) * (twistEndOrderSnd SS e An pos a X s : ℚ) + ((a.aZ' - a.aZ : ℤ) : ℚ) := by

  have hswap : twistPosMoment SS An pos X s = ∑ d ∈ Finset.range (e s + 1), (d : ℚ) * twistCircleDeg SS An pos X s d := by
    unfold twistPosMoment
    simp only [twistCircleDeg_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro V hV
    rw [Finset.mem_filter] at hV
    obtain ⟨h0, h1⟩ := hpos V hV.1 hV.2
    have := (AnnulusSlope.sum_tent_eq_one_and_sum_mul_tent_eq (pos s V) h0 (e s) h1).2
    calc (X V : ℚ) * pos s V = (X V : ℚ) * ∑ d ∈ Finset.range (e s + 1), (d : ℚ) * AnnulusSlope.tent (pos s V) d := by rw [this]
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d _; ring
  rw [hswap, Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < e s)]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  have hmid : ∑ d ∈ Finset.Ico 1 (e s), (d : ℚ) * twistCircleDeg SS An pos X s d =
      ∑ d ∈ Finset.Ico 1 (e s), (d : ℚ) * -((twistChainVal SS e a s (d - 1) - 2 * twistChainVal SS e a s d + twistChainVal SS e a s (d + 1) : ℤ) : ℚ) :=
    Finset.sum_congr rfl (fun d hd => by rw [Finset.mem_Ico] at hd; rw [hcirc d hd.1 hd.2])
  rw [hmid]
  have habel := AnnulusSlope.abel_two (twistChainVal SS e a s) (e s) he
  have hsum : ∑ x ∈ Finset.Ico 1 (e s), (x : ℚ) * -((twistChainVal SS e a s (x - 1) - 2 * twistChainVal SS e a s x + twistChainVal SS e a s (x + 1) : ℤ) : ℚ) =
      -(((e s : ℤ) * (twistChainVal SS e a s (e s) - twistChainVal SS e a s (e s - 1)) - (twistChainVal SS e a s (e s) - twistChainVal SS e a s 0) : ℤ) : ℚ) := by
    rw [← habel]
    push_cast
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro d _; ring
  rw [hsum]

  have hshare : twistCircleDeg SS An pos X s (e s) = (twistEndShareSnd SS e An pos X s : ℚ) := by
    unfold twistEndShareSnd
    rw [if_pos hintSnd]
    exact (Rat.coe_int_num_of_den_eq_one hintSnd).symm
  have hcv_e : twistChainVal SS e a s (e s) = a.aZ' := by
    unfold twistChainVal; rw [if_neg (by omega), if_pos le_rfl]
  have hcv_0 : twistChainVal SS e a s 0 = a.aZ := by
    unfold twistChainVal; rw [if_pos rfl]
  rw [hshare, hcv_e, hcv_0]
  unfold twistEndOrderSnd
  rw [hcv_e]
  push_cast
  ring

open Classical in

theorem mul_twistAnnulusDeg_sub_twistPosMoment_eq (he : 1 ≤ e s)
    (hpos : ∀ V ∈ X.support, V ∈ (An s).dom → 0 ≤ pos s V ∧ pos s V ≤ e s)
    (hcirc : ∀ d : ℕ, 1 ≤ d → d + 1 ≤ e s →
      twistCircleDeg SS An pos X s d = -((twistChainVal SS e a s (d - 1) - 2 * twistChainVal SS e a s d + twistChainVal SS e a s (d + 1) : ℤ) : ℚ))
    (hintFst : (twistCircleDeg SS An pos X s 0).den = 1) :
    (e s : ℚ) * (twistAnnulusDeg SS An X s : ℚ) - twistPosMoment SS An pos X s =
      (e s : ℚ) * (twistEndOrderFst SS e An pos a X s : ℚ) - ((a.aZ' - a.aZ : ℤ) : ℚ) := by

  have hswap : (e s : ℚ) * (twistAnnulusDeg SS An X s : ℚ) - twistPosMoment SS An pos X s =
      ∑ d ∈ Finset.range (e s + 1), ((e s : ℚ) - d) * twistCircleDeg SS An pos X s d := by
    unfold twistPosMoment twistAnnulusDeg
    push_cast
    simp only [twistCircleDeg_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro V hV
    rw [Finset.mem_filter] at hV
    obtain ⟨h0, h1⟩ := hpos V hV.1 hV.2
    obtain ⟨hT1, hT2⟩ := AnnulusSlope.sum_tent_eq_one_and_sum_mul_tent_eq (pos s V) h0 (e s) h1
    calc (e s : ℚ) * (X V : ℚ) - (X V : ℚ) * pos s V
        = (X V : ℚ) * ((e s : ℚ) * ∑ d ∈ Finset.range (e s + 1), AnnulusSlope.tent (pos s V) d -
            ∑ d ∈ Finset.range (e s + 1), (d : ℚ) * AnnulusSlope.tent (pos s V) d) := by rw [hT1, hT2]; ring
      _ = _ := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro d _; ring
  rw [hswap, Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < e s)]
  simp only [Nat.cast_zero, sub_zero, sub_self, zero_mul, add_zero, zero_add]
  have hmid : ∑ d ∈ Finset.Ico 1 (e s), ((e s : ℚ) - d) * twistCircleDeg SS An pos X s d =
      ∑ d ∈ Finset.Ico 1 (e s), ((e s : ℚ) - d) * -((twistChainVal SS e a s (d - 1) - 2 * twistChainVal SS e a s d + twistChainVal SS e a s (d + 1) : ℤ) : ℚ) :=
    Finset.sum_congr rfl (fun d hd => by rw [Finset.mem_Ico] at hd; rw [hcirc d hd.1 hd.2])
  rw [hmid]
  have habel := AnnulusSlope.abel_one (twistChainVal SS e a s) (e s) he
  have hsum : ∑ x ∈ Finset.Ico 1 (e s), ((e s : ℚ) - x) * -((twistChainVal SS e a s (x - 1) - 2 * twistChainVal SS e a s x + twistChainVal SS e a s (x + 1) : ℤ) : ℚ) =
      -(((twistChainVal SS e a s (e s) - twistChainVal SS e a s 0) - (e s : ℤ) * (twistChainVal SS e a s 1 - twistChainVal SS e a s 0) : ℤ) : ℚ) := by
    rw [← habel]
    push_cast
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro d _; ring
  rw [hsum]
  have hshare : twistCircleDeg SS An pos X s 0 = (twistEndShareFst SS An pos X s : ℚ) := by
    unfold twistEndShareFst
    rw [if_pos hintFst]
    exact (Rat.coe_int_num_of_den_eq_one hintFst).symm
  have hcv_e : twistChainVal SS e a s (e s) = a.aZ' := by
    unfold twistChainVal; rw [if_neg (by omega), if_pos le_rfl]
  have hcv_0 : twistChainVal SS e a s 0 = a.aZ := by
    unfold twistChainVal; rw [if_pos rfl]
  rw [hshare, hcv_e, hcv_0]
  unfold twistEndOrderFst
  rw [hcv_0]
  push_cast
  ring

end ModularCurve.JHPlaceSpecialization.Chord

theorem ord_residue_smul_eq_of_residue_ne_zero
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fb : Type*} [Field Fb] [Algebra (ResidueField ↥A) Fb]
    (R : AlgebraicCurve.RegularProlongation A F Fb) (x : Place (ResidueField ↥A) Fb) (f : F)
    (c c' : L) (h : c • f ∈ R.integers) (h' : c' • f ∈ R.integers)
    (hr : R.residue ⟨c • f, h⟩ ≠ 0) (hr' : R.residue ⟨c' • f, h'⟩ ≠ 0) :
    x.ord (R.residue ⟨c • f, h⟩) = x.ord (R.residue ⟨c' • f, h'⟩) := by
  have hc' : c' ≠ 0 := R.smul_const_ne_zero h' hr'
  have hf0 : f ≠ 0 := by
    rintro rfl; apply hr; have : (⟨c • (0 : F), h⟩ : R.integers) = 0 := Subtype.ext (by simp); rw [this, map_zero]

  have hu' : IsUnit (⟨c' • f, h'⟩ : R.integers) := R.isUnit_of_residue_ne_zero hr'
  obtain ⟨w, hw⟩ := hu'
  have hinv : (c' • f)⁻¹ ∈ R.integers := by
    have : ((w⁻¹ : R.integersˣ) : R.integers).1 = (c' • f)⁻¹ := by
      have h1 : ((w : R.integers) : F) = c' • f := congrArg Subtype.val hw
      have h2 : ((w⁻¹ : R.integersˣ) : R.integers).1 * (w : R.integers).1 = 1 := by
        rw [← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]; rfl
      rw [h1] at h2
      exact eq_inv_of_mul_eq_one_left h2
    rw [← this]; exact ((w⁻¹ : R.integersˣ) : R.integers).2
  have hcf : c' • f ≠ 0 := smul_ne_zero hc' hf0
  have hc'F : algebraMap L F c' ≠ 0 := (map_ne_zero _).mpr hc'
  have huA : c / c' ∈ A := by
    rw [← R.algebraMap_mem_iff]
    have : algebraMap L F (c / c') = (c • f) * (c' • f)⁻¹ := by
      rw [Algebra.smul_def, Algebra.smul_def, map_div₀]
      field_simp
    rw [this]; exact mul_mem h hinv
  have hsmul : c • f = algebraMap L F (c / c') * (c' • f) := by
    rw [Algebra.smul_def, Algebra.smul_def, map_div₀]
    field_simp
  have hprod : (⟨c • f, h⟩ : R.integers) = ⟨algebraMap L F (c / c'), (R.algebraMap_mem_iff _).mpr huA⟩ * ⟨c' • f, h'⟩ :=
    Subtype.ext hsmul
  have hres : R.residue ⟨c • f, h⟩ = algebraMap (ResidueField ↥A) Fb (IsLocalRing.residue ↥A ⟨c / c', huA⟩) * R.residue ⟨c' • f, h'⟩ := by
    rw [hprod, map_mul, ← R.residue_algebraMap ⟨c / c', huA⟩]
  have hconst : algebraMap (ResidueField ↥A) Fb (IsLocalRing.residue ↥A ⟨c / c', huA⟩) ≠ 0 := by
    intro h0; apply hr; rw [hres, h0, zero_mul]
  rw [hres, x.ord_mul hconst hr', x.ord_eq_zero_of_isAlgebraic (isAlgebraic_algebraMap _), zero_add]

namespace Ws47
namespace ChordH

section LogVal
variable {L : Type*} [Field L] (A : ValuationSubring L)

def HasLogVal (b x : L) (q : ℚ) : Prop :=
  ∃ (n : ℕ) (m : ℤ), 0 < n ∧ q = (m : ℚ) / (n : ℚ) ∧ A.valuation x ^ n = A.valuation b ^ m

variable {A}

theorem val_ne_zero_of_ne_zero {x : L} (hx : x ≠ 0) : A.valuation x ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr hx

theorem zpow_base_eq_one_iff {b : L} (hb1 : A.valuation b < 1) (k : ℤ) :
    A.valuation b ^ k = 1 ↔ k = 0 := by
  constructor
  · intro h
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · by_contra hn
      have hn' : n ≠ 0 := by exact_mod_cast hn
      have hlt : A.valuation b ^ n < 1 := pow_lt_one₀ zero_le' hb1 hn'
      rw [zpow_natCast] at h
      exact absurd h hlt.ne
    · by_contra hn
      have hn' : n ≠ 0 := by omega
      have hlt : A.valuation b ^ n < 1 := pow_lt_one₀ zero_le' hb1 hn'
      rw [zpow_neg, zpow_natCast, inv_eq_one] at h
      exact absurd h hlt.ne
  · rintro rfl; simp

theorem zpow_base_injective {b : L} (hb0 : b ≠ 0) (hb1 : A.valuation b < 1) {m m' : ℤ}
    (h : A.valuation b ^ m = A.valuation b ^ m') : m = m' := by
  have hvb0 : A.valuation b ≠ 0 := val_ne_zero_of_ne_zero hb0
  have h1 : A.valuation b ^ (m - m') = 1 := by
    rw [zpow_sub₀ hvb0, h, div_self (zpow_ne_zero _ hvb0)]
  have := (zpow_base_eq_one_iff hb1 _).mp h1
  omega

theorem pow_left_inj_val {x y : A.ValueGroup} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = y ^ n) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd h (pow_lt_pow_left₀ hlt zero_le' hn).ne
  · exact heq
  · exact absurd h (pow_lt_pow_left₀ hgt zero_le' hn).ne'

theorem HasLogVal.ne_zero {b x : L} {q : ℚ} (hb0 : b ≠ 0) (h : HasLogVal A b x q) : x ≠ 0 := by
  obtain ⟨n, m, hn, -, h⟩ := h
  rintro rfl
  rw [map_zero, zero_pow (Nat.pos_iff_ne_zero.mp hn)] at h
  exact zpow_ne_zero m (val_ne_zero_of_ne_zero hb0) h.symm

theorem HasLogVal.unique {b x : L} {q q' : ℚ} (hb0 : b ≠ 0) (hb1 : A.valuation b < 1)
    (h : HasLogVal A b x q) (h' : HasLogVal A b x q') : q = q' := by
  obtain ⟨n, m, hn, rfl, h⟩ := h
  obtain ⟨n', m', hn', rfl, h'⟩ := h'
  have key : A.valuation b ^ (m * n') = A.valuation b ^ (m' * n) := by
    rw [zpow_mul, zpow_mul, ← h, ← h', zpow_natCast, zpow_natCast, ← pow_mul, ← pow_mul, mul_comm]
  have := zpow_base_injective hb0 hb1 key
  rw [div_eq_div_iff (by exact_mod_cast hn.ne') (by exact_mod_cast hn'.ne')]
  exact_mod_cast this

theorem HasLogVal.congr {b x y : L} {q : ℚ} (hxy : A.valuation x = A.valuation y)
    (h : HasLogVal A b x q) : HasLogVal A b y q := by
  obtain ⟨n, m, hn, hq, h⟩ := h
  exact ⟨n, m, hn, hq, hxy ▸ h⟩

theorem HasLogVal.congr_q {b x : L} {q q' : ℚ} (hq : q = q') (h : HasLogVal A b x q) : HasLogVal A b x q' :=
  hq ▸ h

theorem HasLogVal.mul {b x y : L} {q r : ℚ} (hb0 : b ≠ 0) (h : HasLogVal A b x q) (h' : HasLogVal A b y r) :
    HasLogVal A b (x * y) (q + r) := by
  have hvb0 : A.valuation b ≠ 0 := val_ne_zero_of_ne_zero hb0
  obtain ⟨n, m, hn, rfl, h⟩ := h
  obtain ⟨n', m', hn', rfl, h'⟩ := h'
  refine ⟨n * n', m * n' + m' * n, Nat.mul_pos hn hn', ?_, ?_⟩
  · push_cast
    field_simp
  · have e1 : A.valuation x ^ (n * n') = A.valuation b ^ (m * n') := by
      rw [pow_mul, h, ← zpow_natCast, ← zpow_mul]
    have e2 : A.valuation y ^ (n * n') = A.valuation b ^ (m' * n) := by
      rw [mul_comm n n', pow_mul, h', ← zpow_natCast, ← zpow_mul]
    rw [map_mul, mul_pow, e1, e2, ← zpow_add₀ hvb0]

theorem HasLogVal.inv {b x : L} {q : ℚ} (h : HasLogVal A b x q) : HasLogVal A b x⁻¹ (-q) := by
  obtain ⟨n, m, hn, rfl, h⟩ := h
  refine ⟨n, -m, hn, by push_cast; ring, ?_⟩
  rw [map_inv₀, inv_pow, h, zpow_neg]

theorem HasLogVal.zpow {b x : L} {q : ℚ} (h : HasLogVal A b x q) (k : ℤ) : HasLogVal A b (x ^ k) (k * q) := by
  obtain ⟨n, m, hn, rfl, h⟩ := h
  refine ⟨n, k * m, hn, by push_cast; ring, ?_⟩
  rw [map_zpow₀, ← zpow_natCast, ← zpow_mul, zpow_mul', zpow_natCast, h, ← zpow_mul, mul_comm m k]

theorem HasLogVal.of_val_eq_one {b x : L} (hx : A.valuation x = 1) : HasLogVal A b x 0 :=
  ⟨1, 0, Nat.one_pos, by simp, by rw [hx, one_pow, zpow_zero]⟩

theorem HasLogVal.finset_prod {ι : Type*} {b : L} (hb0 : b ≠ 0) (s : Finset ι) (x : ι → L) (q : ι → ℚ)
    (h : ∀ i ∈ s, HasLogVal A b (x i) (q i)) : HasLogVal A b (∏ i ∈ s, x i) (∑ i ∈ s, q i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact HasLogVal.of_val_eq_one (map_one _)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul hb0 (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem hasLogVal_intCast_iff {b x : L} (k : ℤ) :
    HasLogVal A b x k ↔ A.valuation x = A.valuation b ^ k := by
  constructor
  · rintro ⟨n, m, hn, hq, h⟩
    have hm : m = k * n := by
      rw [eq_div_iff (by exact_mod_cast hn.ne')] at hq
      exact_mod_cast hq.symm
    apply pow_left_inj_val (Nat.pos_iff_ne_zero.mp hn)
    rw [h, hm, zpow_mul, zpow_natCast]
  · intro h
    exact ⟨1, k, Nat.one_pos, by simp, by rw [pow_one, h]⟩

theorem hasLogVal_natCast_iff {b x : L} (k : ℕ) :
    HasLogVal A b x k ↔ A.valuation x = A.valuation b ^ k := by
  rw [← zpow_natCast]
  exact_mod_cast hasLogVal_intCast_iff (A := A) (b := b) (x := x) (k : ℤ)

end LogVal

section Eval
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem evalAt_eq_iff (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (a : K) :
    v.evalAt f = a ↔ IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = algebraMap K v.ResidueField a := by
  constructor
  · rintro rfl; exact (v.algebraMap_evalAt hv hf).symm
  · intro h; apply v.algebraMap_residueField_injective; rw [v.algebraMap_evalAt hv hf, h]

theorem evalAt_mul' (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  rw [evalAt_eq_iff v hv (mul_mem hf hg), map_mul, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_mul]
  rfl

theorem evalAt_algebraMap' (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  exact v.residueInv_algebraMap a

theorem residue_ne_zero_of_evalAt_ne_zero {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
  intro h0
  apply h
  rw [v.evalAt_of_mem hf, h0, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

theorem evalAt_zero' : v.evalAt (0 : F) = 0 := by
  rw [v.evalAt_of_mem (zero_mem _)]
  have h0 : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
  rw [h0, map_zero, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

theorem isUnit_of_evalAt_ne_zero {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  have hres := residue_ne_zero_of_evalAt_ne_zero v hf h
  by_contra hu
  exact hres ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu))

theorem inv_mem_of_evalAt_ne_zero {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    f⁻¹ ∈ v.toValuationSubring := by
  have hu := isUnit_of_evalAt_ne_zero v hf h
  have h1 : v.toValuationSubring.valuation f = 1 :=
    (v.toValuationSubring.valuation_eq_one_iff ⟨f, hf⟩).mp hu
  rw [← v.toValuationSubring.valuation_le_one_iff, map_inv₀, h1, inv_one]

theorem evalAt_algebraMap_mul_inv (hv : v.IsRational) {z : F} (hz : z ∈ v.toValuationSubring) (hz0 : v.evalAt z ≠ 0) (a : K) :
    v.evalAt (algebraMap K F a * z⁻¹) = a * (v.evalAt z)⁻¹ := by
  have hzi : z⁻¹ ∈ v.toValuationSubring := inv_mem_of_evalAt_ne_zero v hz hz0
  have h1 : v.evalAt z * v.evalAt z⁻¹ = 1 := by
    rw [← evalAt_mul' v hv hz hzi, mul_inv_cancel₀, v.evalAt_one]
    rintro rfl
    exact hz0 (evalAt_zero' v)
  rw [evalAt_mul' v hv (v.algebraMap_mem' a) hzi, evalAt_algebraMap' v, eq_inv_of_mul_eq_one_right h1]

end Eval

section Prolong
variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
variable (R : RegularProlongation A F Fb)

theorem ne_zero_of_admissible {f : F} {c : L} (hc : c • f ∈ R.integers) (hr : R.residue ⟨c • f, hc⟩ ≠ 0) :
    f ≠ 0 := by
  rintro rfl
  apply hr
  have : (⟨c • (0 : F), hc⟩ : R.integers) = 0 := Subtype.ext (smul_zero c)
  rw [this, map_zero]

theorem inv_smul_mem_of_admissible {f : F} {c : L} (hc : c • f ∈ R.integers) (hr : R.residue ⟨c • f, hc⟩ ≠ 0) :
    (c • f)⁻¹ ∈ R.integers := by
  have hu : IsUnit (⟨c • f, hc⟩ : R.integers) := R.isUnit_of_residue_ne_zero hr
  have h1 : R.integers.valuation (c • f) = 1 := (R.integers.valuation_eq_one_iff ⟨c • f, hc⟩).mp hu
  rw [← R.integers.valuation_le_one_iff, map_inv₀, h1, inv_one]

theorem div_mem_of_admissible {f : F} {c c' : L}
    (hc : c • f ∈ R.integers) (hr : R.residue ⟨c • f, hc⟩ ≠ 0) (hc' : c' • f ∈ R.integers) :
    c' / c ∈ A := by
  have hf0 := ne_zero_of_admissible R hc hr
  have hc0 : c ≠ 0 := R.smul_const_ne_zero hc hr
  rw [← R.algebraMap_mem_iff]
  have : algebraMap L F (c' / c) = (c' • f) * (c • f)⁻¹ := by
    rw [Algebra.smul_def, Algebra.smul_def, map_div₀]
    field_simp
  rw [this]
  exact mul_mem hc' (inv_smul_mem_of_admissible R hc hr)

theorem val_eq_of_admissible {f : F} {c c' : L}
    (hc : c • f ∈ R.integers) (hr : R.residue ⟨c • f, hc⟩ ≠ 0)
    (hc' : c' • f ∈ R.integers) (hr' : R.residue ⟨c' • f, hc'⟩ ≠ 0) :
    A.valuation c' = A.valuation c := by
  have hc0 : c ≠ 0 := R.smul_const_ne_zero hc hr
  have hc'0 : c' ≠ 0 := R.smul_const_ne_zero hc' hr'
  have h1 : A.valuation (c' / c) ≤ 1 := (A.valuation_le_one_iff _).mpr (div_mem_of_admissible R hc hr hc')
  have h2 : A.valuation (c / c') ≤ 1 := (A.valuation_le_one_iff _).mpr (div_mem_of_admissible R hc' hr' hc)
  rw [map_div₀] at h1 h2
  have hvc : A.valuation c ≠ 0 := val_ne_zero_of_ne_zero hc0
  have hvc' : A.valuation c' ≠ 0 := val_ne_zero_of_ne_zero hc'0
  rw [div_le_one₀ (zero_lt_iff.mpr hvc)] at h1
  rw [div_le_one₀ (zero_lt_iff.mpr hvc')] at h2
  exact le_antisymm h1 h2

theorem admissible_of_val_eq {f : F} {c c' : L}
    (hc : c • f ∈ R.integers) (hr : R.residue ⟨c • f, hc⟩ ≠ 0) (h : A.valuation c' = A.valuation c) :
    ∃ hc' : c' • f ∈ R.integers, R.residue ⟨c' • f, hc'⟩ ≠ 0 := by
  have hc0 : c ≠ 0 := R.smul_const_ne_zero hc hr
  have hvc : A.valuation c ≠ 0 := val_ne_zero_of_ne_zero hc0
  set u : L := c' / c with hu
  have hvu : A.valuation u = 1 := by rw [hu, map_div₀, h, div_self hvc]
  have huA : u ∈ A := (A.valuation_le_one_iff u).mp hvu.le
  have huunit : IsUnit (⟨u, huA⟩ : A) := (A.valuation_eq_one_iff ⟨u, huA⟩).mpr hvu
  have hmemu : algebraMap L F u ∈ R.integers := (R.algebraMap_mem_iff u).mpr huA
  have hkey : c' • f = algebraMap L F u * (c • f) := by
    rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, hu, div_mul_cancel₀ c' hc0]
  have hc' : c' • f ∈ R.integers := hkey ▸ mul_mem hmemu hc
  refine ⟨hc', ?_⟩
  have hsub : (⟨c' • f, hc'⟩ : R.integers) = ⟨algebraMap L F u, hmemu⟩ * ⟨c • f, hc⟩ := Subtype.ext hkey
  rw [hsub, map_mul]
  refine mul_ne_zero ?_ hr
  have hres : R.residue ⟨algebraMap L F u, hmemu⟩ =
      algebraMap (ResidueField A) Fb (IsLocalRing.residue A ⟨u, huA⟩) := R.residue_algebraMap ⟨u, huA⟩
  rw [hres, map_ne_zero]
  intro h0
  rw [IsLocalRing.residue_eq_zero_iff] at h0
  exact (IsLocalRing.mem_maximalIdeal _).mp h0 huunit

theorem exists_residue_eq_algebraMap_mul {f : F} {c c' : L}
    (hc : c • f ∈ R.integers) (hr : R.residue ⟨c • f, hc⟩ ≠ 0)
    (hc' : c' • f ∈ R.integers) (hr' : R.residue ⟨c' • f, hc'⟩ ≠ 0) :
    ∃ u : ResidueField A, u ≠ 0 ∧
      R.residue ⟨c' • f, hc'⟩ = algebraMap (ResidueField A) Fb u * R.residue ⟨c • f, hc⟩ := by
  have hc0 : c ≠ 0 := R.smul_const_ne_zero hc hr
  have huA : c' / c ∈ A := div_mem_of_admissible R hc hr hc'
  have hmemu : algebraMap L F (c' / c) ∈ R.integers := (R.algebraMap_mem_iff _).mpr huA
  have hkey : c' • f = algebraMap L F (c' / c) * (c • f) := by
    rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, div_mul_cancel₀ c' hc0]
  have hsub : (⟨c' • f, hc'⟩ : R.integers) = ⟨algebraMap L F (c' / c), hmemu⟩ * ⟨c • f, hc⟩ := Subtype.ext hkey
  refine ⟨IsLocalRing.residue A ⟨c' / c, huA⟩, ?_, ?_⟩
  · intro h0
    apply hr'
    rw [hsub, map_mul, R.residue_algebraMap ⟨c' / c, huA⟩, h0, map_zero, zero_mul]
  · rw [hsub, map_mul, R.residue_algebraMap ⟨c' / c, huA⟩]

end Prolong

section Ord
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_algebraMap_eq_zero {a : K} (ha : a ≠ 0) : v.ord (algebraMap K F a) = 0 := by
  have hmem : algebraMap K F a ∈ v.toValuationSubring := v.algebraMap_mem' a
  have hmem' : algebraMap K F a⁻¹ ∈ v.toValuationSubring := v.algebraMap_mem' a⁻¹
  let u : v.toValuationSubringˣ :=
    ⟨⟨_, hmem⟩, ⟨_, hmem'⟩, Subtype.ext (by simp [ha]), Subtype.ext (by simp [ha])⟩
  exact v.ord_coe_unit u

theorem ord_algebraMap_mul {a : K} (ha : a ≠ 0) {f : F} (hf : f ≠ 0) :
    v.ord (algebraMap K F a * f) = v.ord f := by
  rw [v.ord_mul ((map_ne_zero _).mpr ha) hf, ord_algebraMap_eq_zero v ha, zero_add]

theorem ord_smul' {a : K} (ha : a ≠ 0) {f : F} (hf : f ≠ 0) : v.ord (a • f) = v.ord f := by
  rw [Algebra.smul_def, ord_algebraMap_mul v ha hf]

end Ord

section Wide
variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem exists_mem_dom_valuation_pow_eq (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0)
    (hmod1 : A.valuation (An.modulus : L) < 1) {k : ℕ} (hk : 2 ≤ k) :
    ∃ P ∈ An.dom, A.valuation (P.evalAt An.param) ^ k = A.valuation (An.modulus : L) ∧
      A.valuation (P.evalAt An.param) < 1 := by
  have hk0 : 0 < k := by omega
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (An.modulus : L) hk0
  have hvy : A.valuation y ^ k = A.valuation (An.modulus : L) := by rw [← map_pow, hy]
  have hy0 : y ≠ 0 := by rintro rfl; rw [zero_pow hk0.ne'] at hy; exact hmod0 hy.symm
  have hvy0 : A.valuation y ≠ 0 := val_ne_zero_of_ne_zero hy0
  have hvy1 : A.valuation y < 1 := by
    by_contra hle
    push Not at hle
    have h1 : 1 ≤ A.valuation y ^ k := one_le_pow_of_one_le' hle k
    rw [hvy] at h1
    exact (not_lt.mpr h1) hmod1
  have hyA : y ∈ A := (A.valuation_le_one_iff y).mp hvy1.le
  have hymax : (⟨y, hyA⟩ : A) ∈ IsLocalRing.maximalIdeal A := (A.valuation_lt_one_iff ⟨y, hyA⟩).mpr hvy1

  have hmA : (An.modulus : L) / y ∈ A := by
    rw [← A.valuation_le_one_iff, map_div₀, ← hvy, div_le_iff₀ (zero_lt_iff.mpr hvy0), one_mul]
    exact pow_le_of_le_one zero_le' hvy1.le hk0.ne'
  have hmmax : (⟨_, hmA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [A.valuation_lt_one_iff]
    show A.valuation ((An.modulus : L) / y) < 1
    rw [map_div₀, ← hvy, div_lt_iff₀ (zero_lt_iff.mpr hvy0), one_mul]
    calc A.valuation y ^ k = A.valuation y ^ (k - 1) * A.valuation y := by
          rw [← pow_succ]; congr 1; omega
      _ < 1 * A.valuation y := by
          apply mul_lt_mul_of_pos_right _ (zero_lt_iff.mpr hvy0)
          exact pow_lt_one₀ zero_le' hvy1 (by omega)
      _ = A.valuation y := one_mul _
  obtain ⟨P, ⟨hP, hPy⟩, -⟩ := An.existsUnique_evalAt_eq ⟨y, hyA⟩ hymax hy0
    ⟨⟨_, hmA⟩, hmmax, by show (An.modulus : L) = y * ((An.modulus : L) / y); field_simp⟩
  exact ⟨P, hP, by rw [show P.evalAt An.param = y from hPy, hvy], by rw [show P.evalAt An.param = y from hPy]; exact hvy1⟩

theorem annulus_wide (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0)
    (hmod1 : A.valuation (An.modulus : L) < 1) :
    ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param) := by
  obtain ⟨P₂, hP₂, h2, hlt2⟩ := exists_mem_dom_valuation_pow_eq An hmod0 hmod1 (le_refl 2)
  obtain ⟨P₃, hP₃, h3, -⟩ := exists_mem_dom_valuation_pow_eq An hmod0 hmod1 (by norm_num : 2 ≤ 3)
  refine ⟨P₂, hP₂, P₃, hP₃, fun heq => ?_⟩
  rw [heq] at h2 hlt2
  have hw0 : A.valuation (P₃.evalAt An.param) ≠ 0 := by
    intro h0; rw [h0, zero_pow two_ne_zero] at h2; exact hmod0 ((map_eq_zero _).mp h2.symm)
  have : A.valuation (P₃.evalAt An.param) ^ 2 * A.valuation (P₃.evalAt An.param) =
      A.valuation (P₃.evalAt An.param) ^ 2 * 1 := by rw [mul_one, ← pow_succ, h3, h2]
  have h1 := mul_left_cancel₀ (pow_ne_zero 2 hw0) this
  exact absurd h1 hlt2.ne

end Wide

section Sums
variable {α M : Type*} [AddCommGroup M]

theorem sum_filter_support_eq_sum_filter {N : Type*} [Zero N] (D : α →₀ N) (p : α → Prop) [DecidablePred p]
    {β : Type*} [AddCommMonoid β] (g : α → N → β) :
    (D.filter p).sum g = ∑ a ∈ D.support with p a, g a (D a) := by
  rw [Finsupp.sum, Finsupp.support_filter]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mem_filter] at ha
  rw [Finsupp.filter_apply_pos _ _ ha.2]

theorem prod_filter_support_eq_prod_filter {N : Type*} [Zero N] (D : α →₀ N) (p : α → Prop) [DecidablePred p]
    {β : Type*} [CommMonoid β] (g : α → N → β) :
    (D.filter p).prod g = ∏ a ∈ D.support with p a, g a (D a) := by
  rw [Finsupp.prod, Finsupp.support_filter]
  apply Finset.prod_congr rfl
  intro a ha
  rw [Finset.mem_filter] at ha
  rw [Finsupp.filter_apply_pos _ _ ha.2]

theorem sum_filter_sub_sub (E E₀ X : α →₀ ℤ) (p : α → Prop) [DecidablePred p]
    (hE₀ : ∀ a, p a → E₀ a = 0) (g : α → ℚ) :
    (∑ a ∈ (E - E₀ - X).support with p a, ((E - E₀ - X) a : ℚ) * g a) =
      (∑ a ∈ E.support with p a, (E a : ℚ) * g a) - ∑ a ∈ X.support with p a, (X a : ℚ) * g a := by
  have h0 : E₀.filter p = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    exact hE₀
  have key : ∀ (D : α →₀ ℤ), (∑ a ∈ D.support with p a, (D a : ℚ) * g a) = (D.filter p).sum (fun a n => (n : ℚ) * g a) :=
    fun D => (sum_filter_support_eq_sum_filter D p (fun a n => (n : ℚ) * g a)).symm
  rw [key, key, key, Finsupp.filter_sub, Finsupp.filter_sub, h0, sub_zero,
    Finsupp.sum_sub_index (fun a b₁ b₂ => by push_cast; ring)]

theorem sum_filter_sub_sub_int (E E₀ X : α →₀ ℤ) (p : α → Prop) [DecidablePred p]
    (hE₀ : ∀ a, p a → E₀ a = 0) :
    (∑ a ∈ (E - E₀ - X).support with p a, (E - E₀ - X) a) =
      (∑ a ∈ E.support with p a, E a) - ∑ a ∈ X.support with p a, X a := by
  have h0 : E₀.filter p = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    exact hE₀
  have key : ∀ (D : α →₀ ℤ), (∑ a ∈ D.support with p a, D a) = (D.filter p).sum (fun _ n => n) :=
    fun D => (sum_filter_support_eq_sum_filter D p (fun _ n => n)).symm
  rw [key, key, key, Finsupp.filter_sub, Finsupp.filter_sub, h0, sub_zero,
    Finsupp.sum_sub_index (fun a b₁ b₂ => rfl)]

end Sums

section Node
variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem valuation_evalAt_param_mul (An : Annulus A F) {V : Place L F} (hV : V ∈ An.dom) :
    A.valuation (V.evalAt An.param) * A.valuation (V.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) =
      A.valuation (An.modulus : L) := by
  obtain ⟨hrat, hzO, -, hz0, -⟩ := An.mem_dom V hV
  rw [evalAt_algebraMap_mul_inv V hrat hzO hz0, ← map_mul, mul_comm, inv_mul_cancel_right₀ hz0]

theorem hasLogVal_evalAt_param (An : Annulus A F) {b : L} (hb0 : b ≠ 0) {e : ℕ}
    (hmodv : A.valuation (An.modulus : L) = A.valuation b ^ e)
    (pos : Place L F → ℚ)
    (hpos : ∀ V ∈ An.dom, 0 < pos V ∧ pos V < e ∧
      A.valuation (V.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^ (pos V).den = A.valuation b ^ (pos V).num.toNat)
    {V : Place L F} (hV : V ∈ An.dom) :
    HasLogVal A b (V.evalAt An.param) ((e : ℚ) - pos V) := by
  have hvb0 : A.valuation b ≠ 0 := val_ne_zero_of_ne_zero hb0
  obtain ⟨h0, -, hw⟩ := hpos V hV
  have hmul := valuation_evalAt_param_mul An hV
  have hnum0 : 0 ≤ (pos V).num := Rat.num_nonneg.mpr h0.le
  have hnum : ((pos V).num.toNat : ℤ) = (pos V).num := Int.toNat_of_nonneg hnum0
  have hden : 0 < (pos V).den := (pos V).den_pos
  set vz := A.valuation (V.evalAt An.param) with hvz
  set vw := A.valuation (V.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) with hvw
  have hmod0 : A.valuation (An.modulus : L) ≠ 0 := by rw [hmodv]; exact pow_ne_zero _ hvb0
  have hw0 : vw ≠ 0 := by
    intro h; apply hmod0; rw [← hmul, h, mul_zero]
  refine ⟨(pos V).den, (e : ℤ) * (pos V).den - (pos V).num, hden, ?_, ?_⟩
  · have hq := Rat.mul_den_eq_num (pos V)
    rw [eq_div_iff (Nat.cast_ne_zero.mpr hden.ne')]
    push_cast
    linarith
  · apply mul_right_cancel₀ (pow_ne_zero (pos V).den hw0)
    calc vz ^ (pos V).den * vw ^ (pos V).den = (vz * vw) ^ (pos V).den := (mul_pow _ _ _).symm
      _ = A.valuation b ^ ((e : ℤ) * (pos V).den) := by
          rw [hmul, hmodv, ← pow_mul, ← zpow_natCast]; norm_cast
      _ = A.valuation b ^ ((e : ℤ) * (pos V).den - (pos V).num) * A.valuation b ^ ((pos V).num) := by
          rw [← zpow_add₀ hvb0, sub_add_cancel]
      _ = A.valuation b ^ ((e : ℤ) * (pos V).den - (pos V).num) * vw ^ (pos V).den := by
          rw [hw]; congr 1; rw [← zpow_natCast, hnum]

open Classical in

theorem node_package (An : Annulus A F) (R₁ R₂ : RegularProlongation A F Fb) (x₁ x₂ : Place (ResidueField A) Fb)
    {b : L} (hb0 : b ≠ 0) (hb1 : A.valuation b < 1) {e : ℕ} (he : 0 < e)
    (hmodv : A.valuation (An.modulus : L) = A.valuation b ^ e)
    (hatt₂ : ∃ h₂ : An.param ∈ R₂.integers, x₂.ord (R₂.residue ⟨An.param, h₂⟩) = 1 ∧
      ∀ (g : F) (hg : g ∈ R₂.integers), R₂.residue ⟨g, hg⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord g = 0) → ∀ P ∈ An.dom,
        ∃ h : P.evalAt g * (P.evalAt An.param) ^ (-(x₂.ord (R₂.residue ⟨g, hg⟩))) ∈ A, IsUnit (⟨_, h⟩ : A))
    (hatt₁ : ∃ h₁ : algebraMap L F (An.modulus : L) * An.param⁻¹ ∈ R₁.integers, x₁.ord (R₁.residue ⟨_, h₁⟩) = 1 ∧
      ∀ (g : F) (hg : g ∈ R₁.integers), R₁.residue ⟨g, hg⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord g = 0) → ∀ P ∈ An.dom,
        ∃ h : P.evalAt g * (P.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^
          (-(x₁.ord (R₁.residue ⟨g, hg⟩))) ∈ A, IsUnit (⟨_, h⟩ : A))
    (pos : Place L F → ℚ)
    (hpos : ∀ V ∈ An.dom, 0 < pos V ∧ pos V < e ∧
      A.valuation (V.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^ (pos V).den = A.valuation b ^ (pos V).num.toNat)
    (f : F) (c₁ c₂ : L) (h₁ : c₁ • f ∈ R₁.integers) (hr₁ : R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0)
    (h₂ : c₂ • f ∈ R₂.integers) (hr₂ : R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0)
    (D : Divisor L F) (hD : ∀ V ∈ An.dom, D V = V.ord f) :
    ((∑ V ∈ D.support with V ∈ An.dom, D V) = x₂.ord (R₂.residue ⟨c₂ • f, h₂⟩) + x₁.ord (R₁.residue ⟨c₁ • f, h₁⟩)) ∧
    HasLogVal A b (c₂ / c₁)
      ((∑ V ∈ D.support with V ∈ An.dom, (D V : ℚ) * ((e : ℚ) - pos V)) - (e : ℚ) * (x₁.ord (R₁.residue ⟨c₁ • f, h₁⟩) : ℚ)) := by
  classical
  obtain ⟨hz₂, hx₂, hslope₂⟩ := hatt₂
  obtain ⟨hz₁, hx₁, hslope₁⟩ := hatt₁
  have hvb0 : A.valuation b ≠ 0 := val_ne_zero_of_ne_zero hb0
  have hvmod0 : A.valuation (An.modulus : L) ≠ 0 := by rw [hmodv]; exact pow_ne_zero _ hvb0
  have hmod0 : (An.modulus : L) ≠ 0 := fun h0 => hvmod0 (by rw [h0, map_zero])
  have hmod1 : A.valuation (An.modulus : L) < 1 := by rw [hmodv]; exact pow_lt_one₀ zero_le' hb1 he.ne'
  have hc₁0 : c₁ ≠ 0 := R₁.smul_const_ne_zero h₁ hr₁
  have hc₂0 : c₂ ≠ 0 := R₂.smul_const_ne_zero h₂ hr₂
  have hf0 : f ≠ 0 := ne_zero_of_admissible R₁ h₁ hr₁
  set c' : L := c₂ / c₁ with hc'
  have hc'0 : c' ≠ 0 := div_ne_zero hc₂0 hc₁0
  have hh0 : c₂ • f ≠ 0 := smul_ne_zero hc₂0 hf0
  have hkey : (algebraMap L F c')⁻¹ * (c₂ • f) = c₁ • f := by
    have h1 : algebraMap L F c₁ ≠ 0 := (map_ne_zero _).mpr hc₁0
    have h2 : algebraMap L F c₂ ≠ 0 := (map_ne_zero _).mpr hc₂0
    rw [hc', Algebra.smul_def, Algebra.smul_def, map_div₀]
    field_simp
  have hhb : (algebraMap L F c')⁻¹ * (c₂ • f) ∈ R₁.integers := hkey ▸ h₁
  have hsub : (⟨(algebraMap L F c')⁻¹ * (c₂ • f), hhb⟩ : R₁.integers) = ⟨c₁ • f, h₁⟩ := Subtype.ext hkey
  have hresb : R₁.residue ⟨(algebraMap L F c')⁻¹ * (c₂ • f), hhb⟩ ≠ 0 := by rw [hsub]; exact hr₁

  set D' : Divisor L F := D.filter (fun P => P ∈ An.dom) with hD'
  have hD'supp : ∀ P ∈ D'.support, P ∈ An.dom := by
    intro P hP
    rw [hD', Finsupp.support_filter, Finset.mem_filter] at hP
    exact hP.2
  have hD'dom : ∀ P ∈ An.dom, D' P = P.ord (c₂ • f) := by
    intro P hP
    rw [hD', Finsupp.filter_apply_pos _ _ hP, hD P hP, ord_smul' P hc₂0 hf0]
  have hwide := annulus_wide An hmod0 hmod1
  obtain ⟨hmass, hprod⟩ :=
    AlgebraicCurve.Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
      An hmod0 R₂ x₂ hz₂ hx₂ hslope₂ R₁ x₁ hz₁ hx₁ hslope₁ hwide (c₂ • f) hh0 h₂ hr₂ c' hc'0 hhb hresb
      D' hD'supp hD'dom
  rw [hsub] at hmass hprod
  rw [hD', sum_filter_support_eq_sum_filter] at hmass
  rw [hD', prod_filter_support_eq_prod_filter] at hprod
  refine ⟨hmass, ?_⟩

  have hP : HasLogVal A b (∏ V ∈ D.support with V ∈ An.dom, (V.evalAt An.param) ^ (D V))
      (∑ V ∈ D.support with V ∈ An.dom, (D V : ℚ) * ((e : ℚ) - pos V)) := by
    apply HasLogVal.finset_prod hb0
    intro V hV
    rw [Finset.mem_filter] at hV
    exact (hasLogVal_evalAt_param An hb0 hmodv pos hpos hV.2).zpow (D V)
  have hval : A.valuation (∏ V ∈ D.support with V ∈ An.dom, (V.evalAt An.param) ^ (D V)) =
      A.valuation (c' * (An.modulus : L) ^ (x₁.ord (R₁.residue ⟨c₁ • f, h₁⟩))) := by
    rw [map_prod, map_mul, map_zpow₀, ← hprod]
    exact Finset.prod_congr rfl fun V _ => map_zpow₀ _ _ _
  have hπ : HasLogVal A b ((An.modulus : L) ^ (x₁.ord (R₁.residue ⟨c₁ • f, h₁⟩)))
      ((x₁.ord (R₁.residue ⟨c₁ • f, h₁⟩) : ℚ) * (e : ℚ)) := by
    have h0 : HasLogVal A b (An.modulus : L) (e : ℚ) := by
      have := (hasLogVal_natCast_iff (A := A) (b := b) (x := (An.modulus : L)) e).mpr hmodv
      exact_mod_cast this
    have := h0.zpow (x₁.ord (R₁.residue ⟨c₁ • f, h₁⟩))
    exact_mod_cast this
  have hfin := ((hP.congr hval).mul hb0 hπ.inv).congr (y := c')
    (by rw [map_mul, map_mul, map_inv₀, mul_inv_cancel_right₀ (val_ne_zero_of_ne_zero (zpow_ne_zero _ hmod0))])
  refine hfin.congr_q ?_
  ring

end Node

section Bridge
variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem A4_bridge (R₁ R₂ : RegularProlongation A F Fb) {f : F} {c₁ c₂ b : L} (hb0 : b ≠ 0) (hb1 : A.valuation b < 1)
    (h₁ : c₁ • f ∈ R₁.integers) (hr₁ : R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0)
    (h₂ : c₂ • f ∈ R₂.integers) (hr₂ : R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0)
    {q : ℚ} (hq : HasLogVal A b (c₂ / c₁) q) (k : ℤ) :
    q = k ↔ ∀ (c : L) (hc : c • f ∈ R₁.integers), R₁.residue ⟨c • f, hc⟩ ≠ 0 →
      ∃ hc₂ : (c * b ^ k) • f ∈ R₂.integers, R₂.residue ⟨(c * b ^ k) • f, hc₂⟩ ≠ 0 := by
  have hc₁0 : c₁ ≠ 0 := R₁.smul_const_ne_zero h₁ hr₁
  have hvc₁ : A.valuation c₁ ≠ 0 := val_ne_zero_of_ne_zero hc₁0
  constructor
  · rintro rfl
    intro c hc hrc
    have hv : A.valuation (c₂ / c₁) = A.valuation b ^ k := (hasLogVal_intCast_iff k).mp hq
    have hvc : A.valuation c = A.valuation c₁ := val_eq_of_admissible R₁ h₁ hr₁ hc hrc
    apply admissible_of_val_eq R₂ h₂ hr₂
    rw [map_mul, map_zpow₀, hvc, ← hv, map_div₀, ← mul_div_assoc, mul_div_cancel_left₀ _ hvc₁]
  · intro h
    obtain ⟨hc₂', hr₂'⟩ := h c₁ h₁ hr₁
    have hv : A.valuation (c₁ * b ^ k) = A.valuation c₂ := val_eq_of_admissible R₂ h₂ hr₂ hc₂' hr₂'
    have hk : HasLogVal A b (c₂ / c₁) k := by
      rw [hasLogVal_intCast_iff, map_div₀, ← hv, map_mul, map_zpow₀, mul_div_cancel_left₀ _ hvc₁]
    exact hq.unique hb0 hb1 hk

end Bridge

end Ws47.ChordH

set_option maxHeartbeats 3200000 in
open Classical in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hFix : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.Fixed p M H hpM A δ y ∧
        JHPlaceSpecialization.Fixed p M H hpM A δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hreg : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hnv : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hFixFin : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (horientInf : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C))

    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (hAnn : ∀ s : ↥SS, ∃ An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (hVSlope : ∀ An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))) →
      ∀ k : ℕ, (∀ s : ↥SS, e s ∣ k) →
        ∃ (f : ↥(xHFunctionFieldBar M H)) (c : AlgebraicClosure ℚ) (hc : c • f ∈ Rpd.R₁.integers),
          f ≠ 0 ∧ Rpd.R₁.residue ⟨c • f, hc⟩ ≠ 0 ∧
          (∀ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, G V = V.ord f) → Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G) ∧
          (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V) →
            (∀ s ∈ SS, Psp.reduceFst α hα V ≠ s.1) → V.ord f = 0) ∧
          (∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
            v.ord (Rpd.R₁.residue ⟨c • f, hc⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0) ∧
          (∀ s : ↥SS, ∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord f = 0 ∧
            ∃ h : P.evalAt f * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (hFixReadFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → V.ord g = 0) →
        v.ord (Rpd.R₁.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0)
    (hFixReadSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.2) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v → V.ord g = 0) →
        v.ord (Rpd.R₂.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0)

    (hFixRegFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → (∀ s ∈ SS, v ≠ s.1) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → 0 ≤ V.ord g) →
        0 ≤ v.ord (Rpd.R₁.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hFixRegSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → (∀ s ∈ SS, v ≠ s.2) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v → 0 ≤ V.ord g) →
        0 ≤ v.ord (Rpd.R₂.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS,
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
            ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))
    (pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ)
    (hpos : JHPlaceSpecialization.AnnulusPositionLaw SS e An pos)
    (hposσ : ∀ (s : ↥SS), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      pos s ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = pos s V)
    (hposD : ∀ (s : ↥SS) (d : ℕ), 0 < d → d < e s → ∃ V ∈ (An s).dom,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ pos s V = d)

    (dat : JHPlaceSpecialization.TwistedFibreDatum (p := p) (M := M) (H := H) (hpM := hpM) (A := A) SS)

    (hunifFst : ∀ s : ↥SS,
      (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (Finsupp.single (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1 (1 : ℤ) + dat.corrFst s) v = v.ord (dat.unifFst s)) ∧
      (∀ s' ∈ SS, dat.corrFst s s'.1 = 0 ∧ dat.corrFst s s'.2 = 0) ∧ Divisor.degree (dat.corrFst s) = -1)
    (hunifSnd : ∀ s : ↥SS,
      (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (Finsupp.single (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2 (1 : ℤ) + dat.corrSnd s) v = v.ord (dat.unifSnd s)) ∧
      (∀ s' ∈ SS, dat.corrSnd s s'.1 = 0 ∧ dat.corrSnd s s'.2 = 0) ∧ Divisor.degree (dat.corrSnd s) = -1)

    (hu0 : ∀ s : ↥SS, ∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u ∧ IsLocalRing.residue ↥A u = dat.u0 s)

    (hlam : ∀ (s : ↥SS) (h₁ : JHPlaceSpecialization.flipParam SS An s ∈ Rpd.R₁.integers),
      (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.HasValue
        ((Rpd.R₁.residue ⟨_, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) / dat.unifFst s) (dat.lam s : ResidueField ↥A))
    (hmu : ∀ (s : ↥SS) (h₂ : (An s).param ∈ Rpd.R₂.integers),
      (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.HasValue
        ((Rpd.R₂.residue ⟨_, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) / dat.unifSnd s) (dat.mu s : ResidueField ↥A))
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hXst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = X)
    (hXsupp : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
      (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1))
    (a : JHPlaceSpecialization.TwistVec ↥SS)
    (ha : Psp.IsTwistOf α (θ.toAlgHom.comp α) hα hβ δ SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)))
    (hadm : Psp.twistSpData α (θ.toAlgHom.comp α) hα hβ δ SS e An pos dat a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ GluingData.admissible SS)
    (hsp : GluedPic0.mk SS ⟨Psp.twistSpData α (θ.toAlgHom.comp α) hα hβ δ SS e An pos dat a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), hadm⟩ = 0)

    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hQ₁ : ∀ i, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ (Q₁ i)) (hQ₂ : ∀ j, Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ (Q₂ j))
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hE0 : 0 ≤ E)
    (f : ↥(xHFunctionFieldBar M H)) (hf0 : f ≠ 0)
    (hdivf : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) V = V.ord f) :
    ∃ δ' : ℚ,

      (∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c • f, h⟩ ≠ 0 →
        ∀ s : ↥SS, δ' ≤ (e s : ℚ) * ((((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c • f, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : ℤ) : ℚ) + (JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s : ℚ))) ∧

      (∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨c • f, h⟩ ≠ 0 →
        ∀ s : ↥SS, -((e s : ℚ) * ((((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨c • f, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : ℤ) : ℚ) + (JHPlaceSpecialization.twistEndOrderSnd SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s : ℚ))) ≤ δ') ∧

      (δ' = 0 → ∀ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ Rpd.R₁.integers) (c₂ : AlgebraicClosure ℚ) (h₂ : c₂ • f ∈ Rpd.R₂.integers),
        Rpd.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0 →
        ∀ s : ↥SS, (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨c₂ • f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) + JHPlaceSpecialization.twistEndOrderSnd SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s = 0 →
          (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c₁ • f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) + JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s = 0 ∧
          ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1 → E V = 0) ∧

      (δ' = 0 ↔ ∀ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 →
        ∃ h₂ : (c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) • f ∈ Rpd.R₂.integers,
          Rpd.R₂.residue ⟨(c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) • f, h₂⟩ ≠ 0) := by
  classical

  obtain ⟨c₁, hc₁, hr₁⟩ := Rpd.R₁.exists_smul_mem f hf0
  obtain ⟨c₂, hc₂, hr₂⟩ := Rpd.R₂.exists_smul_mem f hf0

  have hO₁ : ∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c • f, h⟩ ≠ 0 → ∀ s : ↥SS,
      (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c • f, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c₁ • f, hc₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
    fun c h hres s => ord_residue_smul_eq_of_residue_ne_zero Rpd.R₁ _ f c c₁ h hc₁ hres hr₁
  have hO₂ : ∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨c • f, h⟩ ≠ 0 → ∀ s : ↥SS,
      (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨c • f, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨c₂ • f, hc₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
    fun c h hres s => ord_residue_smul_eq_of_residue_ne_zero Rpd.R₂ _ f c c₂ h hc₂ hres hr₂

  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hp1 : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).mp hA

  have hE₀dom : ∀ (s : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), V ∈ (An s).dom →
      (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) V = 0 := by
    intro s V hV
    obtain ⟨-, hn1, hn2⟩ := ((hAn s).1 V).mp hV
    have h1 : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ)) V = 0 := by
      rw [Finsupp.finsetSum_apply]
      exact Finset.sum_eq_zero fun i _ => by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact hn1 (hQ₁ i)
    have h2 : (∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) V = 0 := by
      rw [Finsupp.finsetSum_apply]
      exact Finset.sum_eq_zero fun j _ => by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact hn2 (hQ₂ j)
    rw [Finsupp.add_apply, h1, h2, add_zero]

  have hpkg : ∀ s : ↥SS,
      ((∑ V ∈ (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))).support with V ∈ (An s).dom,
          (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) V) =
        (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨c₂ • f, hc₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) +
          (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c₁ • f, hc₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∧
      Ws47.ChordH.HasLogVal A ((p : ℕ) : AlgebraicClosure ℚ) (c₂ / c₁)
        ((∑ V ∈ (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))).support with V ∈ (An s).dom,
            ((E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) V : ℚ) * ((e s : ℚ) - pos s V)) -
          (e s : ℚ) * ((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c₁ • f, hc₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : ℚ)) := by
    intro s
    obtain ⟨-, ⟨u, hu, hmod⟩, -, -, -, hatt₂, hatt₁⟩ := hAn s
    have hmodv : A.valuation (((An s).modulus : ↥A) : AlgebraicClosure ℚ) = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ (e s) := by
      rw [hmod]
      push_cast
      rw [map_mul, map_pow, (A.valuation_eq_one_iff u).mp hu, mul_one]
    exact Ws47.ChordH.node_package (An s) Rpd.R₁ Rpd.R₂ (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1 (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2 hp0 hp1 (he s) hmodv hatt₂ hatt₁
      (pos s) (fun V hV => hpos s V hV) f c₁ c₂ hc₁ hr₁ hc₂ hr₂ _ (fun V _ => hdivf V)

  have hsplitQ : ∀ (s : ↥SS) (g : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ),
      (∑ V ∈ (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))).support with V ∈ (An s).dom,
          ((E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) V : ℚ) * g V) =
        (∑ V ∈ E.support with V ∈ (An s).dom, (E V : ℚ) * g V) - ∑ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support with V ∈ (An s).dom, ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V : ℚ) * g V :=
    fun s g => Ws47.ChordH.sum_filter_sub_sub E _ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) _ (fun V hV => hE₀dom s V hV) g
  have hsplitZ : ∀ (s : ↥SS),
      (∑ V ∈ (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))).support with V ∈ (An s).dom,
          (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) V) =
        (∑ V ∈ E.support with V ∈ (An s).dom, E V) - ∑ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support with V ∈ (An s).dom, (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V :=
    fun s => Ws47.ChordH.sum_filter_sub_sub_int E _ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) _ (fun V hV => hE₀dom s V hV)

  have hκex : ∃ κ : ℚ, (∀ q : ℚ, Ws47.ChordH.HasLogVal A ((p : ℕ) : AlgebraicClosure ℚ) (c₂ / c₁) q → κ = q) ∧
      ((¬ ∃ q : ℚ, Ws47.ChordH.HasLogVal A ((p : ℕ) : AlgebraicClosure ℚ) (c₂ / c₁) q) →
        ((κ = ((a.aZ' - a.aZ : ℤ) : ℚ)) ↔
          (∀ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 →
            ∃ h₂ : (c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) • f ∈ Rpd.R₂.integers,
              Rpd.R₂.residue ⟨(c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) • f, h₂⟩ ≠ 0))) := by
    by_cases hq : ∃ q : ℚ, Ws47.ChordH.HasLogVal A ((p : ℕ) : AlgebraicClosure ℚ) (c₂ / c₁) q
    · obtain ⟨q, hq⟩ := hq
      exact ⟨q, fun q' hq' => hq.unique hp0 hp1 hq', fun h => (h ⟨q, hq⟩).elim⟩
    · by_cases hR : ∀ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 →
            ∃ h₂ : (c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) • f ∈ Rpd.R₂.integers,
              Rpd.R₂.residue ⟨(c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) • f, h₂⟩ ≠ 0
      · exact ⟨((a.aZ' - a.aZ : ℤ) : ℚ), fun q' hq' => (hq ⟨q', hq'⟩).elim, fun _ => iff_of_true rfl hR⟩
      · refine ⟨((a.aZ' - a.aZ : ℤ) : ℚ) + 1, fun q' hq' => (hq ⟨q', hq'⟩).elim, fun _ => iff_of_false (by linarith) hR⟩
  obtain ⟨κ, hκ1, hκ2⟩ := hκex
  have hnode : ∀ s : ↥SS,
      (((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c₁ • f, hc₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) + (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨c₂ • f, hc₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : ℤ) : ℚ) =
          ((JHPlaceSpecialization.twistAnnulusDeg SS An E s : ℤ) : ℚ) - ((JHPlaceSpecialization.twistAnnulusDeg SS An (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s : ℤ) : ℚ) ∧
      (e s : ℚ) * (((JHPlaceSpecialization.twistAnnulusDeg SS An E s : ℤ) : ℚ) - ((JHPlaceSpecialization.twistAnnulusDeg SS An (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s : ℤ) : ℚ)) -
          (JHPlaceSpecialization.twistPosMoment SS An pos E s - JHPlaceSpecialization.twistPosMoment SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s) =
        κ + (e s : ℚ) * (((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c₁ • f, hc₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : ℤ) : ℚ) := by
    intro s
    obtain ⟨hmass, hlog⟩ := hpkg s
    have hq := hκ1 _ hlog
    rw [hsplitQ s] at hq
    rw [hsplitZ s] at hmass
    have hmassQ := congrArg (fun z : ℤ => (z : ℚ)) hmass
    have hlinE : (∑ V ∈ E.support with V ∈ (An s).dom, (E V : ℚ) * ((e s : ℚ) - pos s V)) =
        (e s : ℚ) * (∑ V ∈ E.support with V ∈ (An s).dom, (E V : ℚ)) - ∑ V ∈ E.support with V ∈ (An s).dom, (E V : ℚ) * pos s V := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have hlinX : (∑ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support with V ∈ (An s).dom, ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V : ℚ) * ((e s : ℚ) - pos s V)) =
        (e s : ℚ) * (∑ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support with V ∈ (An s).dom, ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V : ℚ)) - ∑ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support with V ∈ (An s).dom, ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V : ℚ) * pos s V := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    unfold JHPlaceSpecialization.twistAnnulusDeg JHPlaceSpecialization.twistPosMoment
    push_cast at hmassQ ⊢
    refine ⟨by linarith, ?_⟩
    rw [hlinE, hlinX] at hq
    linarith
  have hA4 : (κ = ((a.aZ' - a.aZ : ℤ) : ℚ)) ↔
      (∀ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 →
        ∃ h₂ : (c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) • f ∈ Rpd.R₂.integers,
          Rpd.R₂.residue ⟨(c₁ * ((p : ℕ) : AlgebraicClosure ℚ) ^ (a.aZ' - a.aZ)) • f, h₂⟩ ≠ 0) := by
    by_cases hq : ∃ q : ℚ, Ws47.ChordH.HasLogVal A ((p : ℕ) : AlgebraicClosure ℚ) (c₂ / c₁) q
    · obtain ⟨q, hlog⟩ := hq
      rw [hκ1 q hlog]
      exact Ws47.ChordH.A4_bridge Rpd.R₁ Rpd.R₂ hp0 hp1 hc₁ hr₁ hc₂ hr₂ hlog (a.aZ' - a.aZ)
    · exact hκ2 hq
  have hdomE : ∀ (s : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      Psp.reduceFst α hα V = (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1 → V ∈ E.support → V ∈ (An s).dom := by
    intro s V hred _
    rw [(hAn s).1 V]
    have hs : (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p := (hSS _).mp s.2
    obtain ⟨hss2, hs1⟩ := hs
    obtain ⟨hfix1, hfix2⟩ := hFix _ hss2
    refine ⟨hred, ?_, ?_⟩
    · intro hst
      apply hst.2
      rw [hred, hs1]
      exact hfix2
    · intro hst
      apply hst.2
      have hinj := (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)).1
      have heq : (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2 = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V := by
        apply hinj
        rw [← hs1, ← hred]
        exact hst.1
      rw [← heq]
      exact hfix1

  have hposX : ∀ s : ↥SS, ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support, V ∈ (An s).dom → 0 ≤ pos s V ∧ pos s V ≤ e s := by
    intro s V _ hV
    obtain ⟨h0, h1, -⟩ := hpos s V hV
    exact ⟨h0.le, h1.le⟩
  have hcirc : ∀ (s : ↥SS) (d : ℕ), 1 ≤ d → d + 1 ≤ e s →
      JHPlaceSpecialization.twistCircleDeg SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s d =
        -((JHPlaceSpecialization.twistChainVal SS e a s (d - 1) - 2 * JHPlaceSpecialization.twistChainVal SS e a s d + JHPlaceSpecialization.twistChainVal SS e a s (d + 1) : ℤ) : ℚ) :=
    ha.2.2
  have hint : ∀ s : ↥SS, (JHPlaceSpecialization.twistCircleDeg SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s 0).den = 1 ∧ (JHPlaceSpecialization.twistCircleDeg SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s (e s)).den = 1 :=
    fun s => ⟨ModularCurve.JHPlaceSpecialization.den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus p M H hpM hpM2 hHp A hA θ α hα hβ hα_coe pb hpb δ hδ SS hSS Psp Rpd hFix hTD hmodel hO hreg hnv hθgal hβ_coe hFixFin hLFst hLSnd hUnit hcusp horientInf horient0 e he hAnn An hAn pos hpos hposσ X hXst s 0, ModularCurve.JHPlaceSpecialization.den_twistCircleDeg_eq_one_of_inertiaStable_of_annulus p M H hpM hpM2 hHp A hA θ α hα hβ hα_coe pb hpb δ hδ SS hSS Psp Rpd hFix hTD hmodel hO hreg hnv hθgal hβ_coe hFixFin hLFst hLSnd hUnit hcusp horientInf horient0 e he hAnn An hAn pos hpos hposσ X hXst s (e s)⟩
  have hTW1 : ∀ s : ↥SS, (e s : ℚ) * (JHPlaceSpecialization.twistAnnulusDeg SS An (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s : ℚ) - JHPlaceSpecialization.twistPosMoment SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s =
      (e s : ℚ) * (JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s : ℚ) - ((a.aZ' - a.aZ : ℤ) : ℚ) := fun s =>
    ModularCurve.JHPlaceSpecialization.Chord.mul_twistAnnulusDeg_sub_twistPosMoment_eq SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s (he s) (hposX s) (hcirc s) (hint s).1
  have hTW2 : ∀ s : ↥SS, JHPlaceSpecialization.twistPosMoment SS An pos (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s =
      (e s : ℚ) * (JHPlaceSpecialization.twistEndOrderSnd SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s : ℚ) + ((a.aZ' - a.aZ : ℤ) : ℚ) := fun s =>
    ModularCurve.JHPlaceSpecialization.Chord.twistPosMoment_eq SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s (he s) (hposX s) (hcirc s) (hint s).2

  have hEpos : ∀ s : ↥SS, 0 ≤ JHPlaceSpecialization.twistPosMoment SS An pos E s ∧ JHPlaceSpecialization.twistPosMoment SS An pos E s ≤ (e s : ℚ) * (JHPlaceSpecialization.twistAnnulusDeg SS An E s : ℚ) := by
    intro s
    have hterm : ∀ V ∈ E.support.filter (fun V => V ∈ (An s).dom), 0 ≤ (E V : ℚ) * pos s V ∧ (E V : ℚ) * pos s V ≤ (E V : ℚ) * (e s : ℚ) := by
      intro V hV
      rw [Finset.mem_filter] at hV
      obtain ⟨h0, h1, -⟩ := hpos s V hV.2
      have hEV : (0 : ℚ) ≤ E V := by exact_mod_cast hE0 V
      exact ⟨mul_nonneg hEV h0.le, mul_le_mul_of_nonneg_left h1.le hEV⟩
    unfold JHPlaceSpecialization.twistPosMoment JHPlaceSpecialization.twistAnnulusDeg
    refine ⟨Finset.sum_nonneg (fun V hV => (hterm V hV).1), ?_⟩
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun V hV => by rw [mul_comm (e s : ℚ)]; exact (hterm V hV).2)
  refine ⟨-κ + ((a.aZ' - a.aZ : ℤ) : ℚ), ?_, ?_, ?_, ?_⟩
  ·
    intro c h hres s
    rw [hO₁ c h hres s]
    obtain ⟨h1, h2⟩ := hnode s
    have h3 := hTW1 s
    have h4 := (hEpos s).2
    push_cast at h1 h2 h3 h4 ⊢
    nlinarith [h1, h2, h3, h4]
  ·
    intro c h hres s
    rw [hO₂ c h hres s]
    obtain ⟨h1, h2⟩ := hnode s
    have h3 := hTW2 s
    have h4 := (hEpos s).1
    push_cast at h1 h2 h3 h4 ⊢
    nlinarith [h1, h2, h3, h4]
  ·
    intro hδ c₁' h₁' c₂' h₂' hr₁' hr₂' s hflat
    rw [hO₂ c₂' h₂' hr₂' s] at hflat
    rw [hO₁ c₁' h₁' hr₁' s]
    obtain ⟨h1, h2⟩ := hnode s
    have h3 := hTW1 s
    have h4 := hTW2 s
    obtain ⟨h5, h6⟩ := hEpos s
    have hflatQ : (((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨c₂ • f, hc₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : ℤ) : ℚ) +
        (JHPlaceSpecialization.twistEndOrderSnd SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s : ℚ) = 0 := by exact_mod_cast hflat
    have hmE : JHPlaceSpecialization.twistPosMoment SS An pos E s = 0 := by
      push_cast at h1 h2 h3 h4 hflatQ hδ ⊢
      linear_combination (-1 : ℚ) * h2 + h4 - (e s : ℚ) * h1 + (e s : ℚ) * hflatQ + hδ

    have hEdom : ∀ V ∈ E.support, V ∉ (An s).dom := by
      intro V hV hVd
      have hterm : ∀ W ∈ E.support.filter (fun W => W ∈ (An s).dom), 0 ≤ (E W : ℚ) * pos s W := by
        intro W hW
        rw [Finset.mem_filter] at hW
        exact mul_nonneg (by exact_mod_cast hE0 W) (hpos s W hW.2).1.le
      have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hmE V (Finset.mem_filter.mpr ⟨hV, hVd⟩)
      have hpV := (hpos s V hVd).1
      have hEV : (E V : ℚ) ≠ 0 := by exact_mod_cast Finsupp.mem_support_iff.mp hV
      exact hEV ((mul_eq_zero.mp hz).resolve_right hpV.ne')
    have hdegE : JHPlaceSpecialization.twistAnnulusDeg SS An E s = 0 := by
      unfold JHPlaceSpecialization.twistAnnulusDeg
      apply Finset.sum_eq_zero
      intro V hV
      rw [Finset.mem_filter] at hV
      exact absurd hV.2 (hEdom V hV.1)
    refine ⟨?_, ?_⟩
    · have he0 : (0 : ℚ) < e s := by exact_mod_cast he s
      have hq : (((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c₁ • f, hc₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : ℤ) : ℚ) +
          (JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s : ℚ) = 0 := by
        rw [hdegE] at h1 h2
        push_cast at h1 h2 h3 h4 hflatQ hmE ⊢
        nlinarith [h1, h2, h3, h4, hmE, hδ, he0]
      exact_mod_cast hq
    · intro V hV
      by_contra hEV
      exact hEdom V (Finsupp.mem_support_iff.mpr hEV) (hdomE s V hV (Finsupp.mem_support_iff.mpr hEV))
  ·
    rw [← hA4]
    constructor
    · intro h; linarith
    · intro h; linarith

#print axioms solution

end S_ModularCurve_JHPlaceSpecialization_exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_twistSp_eq_zero_of_annulus
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_chord_le_endOrders_and_rigid_of_isTwistOf_of_twistSp_eq_zero_of_annulus (solution)
