-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_sub_inclusion_mem_nonunits_gauss_gamma0_of_mem_gauss_gamma0_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/d8b61b1d-1891-59be-bba4-d711a837cb12

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
import Theorems.Thm_ModularCurve_exists_qExpFunctionFieldC_infSubgroup_coe_eq_of_charP
import Theorems.Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_sub_inclusion_mem_nonunits_gauss_gamma0_of_mem_gauss_gamma0_mul
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace FloorUnram

open HahnSeries ModularCurve IsLocalRing

theorem coeff_ofPowerSeries_of_neg {R : Type*} [Semiring R] (p : PowerSeries R) {n : ℤ} (hn : n < 0) :
    (ofPowerSeries ℤ R p).coeff n = 0 := by
  rw [ofPowerSeries_apply, embDomain_notin_range]
  rintro ⟨m, hm⟩
  first | omega | (simp at hm; done) | (simp at hm; omega)

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : PowerSeries R) :
    coeffMap f (ofPowerSeries ℤ R p) = ofPowerSeries ℤ S (p.map f) := by
  ext n
  rw [coeffMap_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [coeff_ofPowerSeries_of_neg p hn, coeff_ofPowerSeries_of_neg _ hn, map_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

theorem gaussPresentation_iff_laurent
    {B : Type*} [CommRing B] [IsLocalRing B] {L : Type*} [Field L] (ι : B →+* L)
    (g : LaurentSeries L) :
    (∃ x y : PowerSeries B, y.map (residue B) ≠ 0 ∧
        g * ofPowerSeries ℤ L (y.map ι) = ofPowerSeries ℤ L (x.map ι)) ↔
    (∃ x y : LaurentSeries B, coeffMap (residue B) y ≠ 0 ∧
        g * coeffMap ι y = coeffMap ι x) := by
  constructor
  · rintro ⟨x, y, hy, h⟩
    refine ⟨ofPowerSeries ℤ B x, ofPowerSeries ℤ B y, ?_, ?_⟩
    · rw [coeffMap_ofPowerSeries]
      intro h0
      apply hy
      have h0' : ofPowerSeries ℤ (ResidueField B) (y.map (residue B)) = ofPowerSeries ℤ (ResidueField B) 0 := by
        rw [h0, map_zero]
      exact ofPowerSeries_injective h0'
    · rw [coeffMap_ofPowerSeries, coeffMap_ofPowerSeries]; exact h
  · rintro ⟨X, Y, hY, h⟩
    have hX : X = single X.order 1 * ofPowerSeries ℤ B X.powerSeriesPart :=
      (LaurentSeries.single_order_mul_powerSeriesPart X).symm
    have hY' : Y = single Y.order 1 * ofPowerSeries ℤ B Y.powerSeriesPart :=
      (LaurentSeries.single_order_mul_powerSeriesPart Y).symm
    have hpY : Y.powerSeriesPart.map (residue B) ≠ 0 := by
      intro h0
      apply hY
      rw [hY', map_mul, coeffMap_ofPowerSeries, h0, map_zero, mul_zero]
    have hs : ∀ a : ℤ, single (-a) (1 : L) * single a 1 = 1 := fun a => by
      rw [single_mul_single, neg_add_cancel, one_mul]; rfl
    have key : g * ofPowerSeries ℤ L (Y.powerSeriesPart.map ι) =
        single (X.order - Y.order) 1 * ofPowerSeries ℤ L (X.powerSeriesPart.map ι) := by
      have h1 : g * (single Y.order (1 : L) * ofPowerSeries ℤ L (Y.powerSeriesPart.map ι)) =
          single X.order 1 * ofPowerSeries ℤ L (X.powerSeriesPart.map ι) := by
        have h' := h
        rw [hY', hX] at h'
        rw [map_mul, map_mul, coeffMap_single, coeffMap_single, RingHom.map_one ι,
          coeffMap_ofPowerSeries, coeffMap_ofPowerSeries] at h'
        exact h'
      calc g * ofPowerSeries ℤ L (Y.powerSeriesPart.map ι)
          = (single (-Y.order) (1 : L) * single Y.order 1) * (g * ofPowerSeries ℤ L (Y.powerSeriesPart.map ι)) := by
            rw [hs, one_mul]
        _ = single (-Y.order) (1 : L) * (g * (single Y.order 1 * ofPowerSeries ℤ L (Y.powerSeriesPart.map ι))) := by ring
        _ = single (-Y.order) (1 : L) * (single X.order 1 * ofPowerSeries ℤ L (X.powerSeriesPart.map ι)) := by rw [h1]
        _ = single (X.order - Y.order) 1 * ofPowerSeries ℤ L (X.powerSeriesPart.map ι) := by
            rw [← mul_assoc, single_mul_single, one_mul, neg_add_eq_sub]
    rcases le_or_gt 0 (X.order - Y.order) with hd | hd
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hd
      refine ⟨PowerSeries.X ^ n * X.powerSeriesPart, Y.powerSeriesPart, hpY, ?_⟩
      rw [key, hn, map_mul, map_pow, PowerSeries.map_X, map_mul, ofPowerSeries_X_pow]
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hd.le)
      refine ⟨X.powerSeriesPart, PowerSeries.X ^ n * Y.powerSeriesPart, ?_, ?_⟩
      · rw [map_mul, map_pow, PowerSeries.map_X]
        exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) hpY
      · rw [map_mul, map_pow, PowerSeries.map_X, map_mul, ofPowerSeries_X_pow, ← hn]
        calc g * (single (-(X.order - Y.order)) (1 : L) * ofPowerSeries ℤ L (Y.powerSeriesPart.map ι))
            = single (-(X.order - Y.order)) (1 : L) * (g * ofPowerSeries ℤ L (Y.powerSeriesPart.map ι)) := by ring
          _ = single (-(X.order - Y.order)) (1 : L) *
                (single (X.order - Y.order) 1 * ofPowerSeries ℤ L (X.powerSeriesPart.map ι)) := by rw [key]
          _ = ofPowerSeries ℤ L (X.powerSeriesPart.map ι) := by rw [← mul_assoc, hs, one_mul]

theorem powerSeries_transport {A B L : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [CommRing L] (fA : A →+* L) (fB : B →+* L) (e : A ≃+* B) (he : ∀ a, fB (e a) = fA a)
    (p : PowerSeries A) :
    (p.map (e : A →+* B)).map fB = p.map fA ∧
    ((p.map (e : A →+* B)).map (residue B) ≠ 0 ↔ p.map (residue A) ≠ 0) := by
  have hunit : ∀ a : A, residue B (e a) = 0 ↔ residue A a = 0 := fun a => by
    rw [residue_eq_zero_iff, residue_eq_zero_iff, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, isUnit_map_iff]
  constructor
  · ext n
    simp only [PowerSeries.coeff_map, RingHom.coe_coe, he]
  · rw [not_iff_not]
    simp only [PowerSeries.ext_iff, PowerSeries.coeff_map, map_zero, RingHom.coe_coe, hunit]

theorem mem_nonunits_of_residue_eq_zero {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField ↥A) Fbar]
    (R : AlgebraicCurve.RegularProlongation A F Fbar) (f : F) (hf : f ∈ R.integers)
    (h0 : R.residue ⟨f, hf⟩ = 0) : f ∈ R.integers.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  refine ⟨hf, ?_⟩
  rw [← R.ker_residue, RingHom.mem_ker]
  exact h0

end FloorUnram

set_option maxHeartbeats 6400000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (K₀' : IntermediateField L (LaurentSeries L))
    (hK₀' : K₀' = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M'))))
    (hle₀' : K₀ ≤ K₀')
    (O₀ : ValuationSubring ↥K₀)
    (hO₀ : ∀ f : ↥K₀, f ∈ O₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (O₀' : ValuationSubring ↥K₀')
    (hO₀' : ∀ f : ↥K₀', f ∈ O₀' ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    ∀ f : ↥K₀', f ∈ O₀' → ∃ g : ↥K₀, g ∈ O₀ ∧ f - IntermediateField.inclusion hle₀' g ∈ O₀'.nonunits := by
  classical
  intro f hf
  open IsLocalRing in

  have hAinj : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  let AL : ValuationSubring L :=
    { toSubring := (algebraMap A L).range
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, ha⟩ | ⟨a, ha⟩
        · exact Or.inl ⟨a, ha⟩
        · exact Or.inr ⟨a, ha⟩ }
  have hALmem : ∀ x : L, x ∈ AL ↔ ∃ a : A, algebraMap A L a = x := fun x => Iff.rfl
  let e0 : A →+* ↥AL := (algebraMap A L).codRestrict AL (fun a => (hALmem _).mpr ⟨a, rfl⟩)
  have he0 : Function.Bijective e0 := by
    refine ⟨fun a b h => hAinj (congrArg (fun x : ↥AL => (x : L)) h), fun x => ?_⟩
    obtain ⟨a, ha⟩ := (hALmem x).mp x.2
    exact ⟨a, Subtype.ext ha⟩
  let e : A ≃+* ↥AL := RingEquiv.ofBijective e0 he0
  have he : ∀ a : A, AL.subtype (e a) = algebraMap A L a := fun a => rfl
  have he' : ∀ b : ↥AL, algebraMap A L (e.symm b) = AL.subtype b := fun b => by
    rw [← he, RingEquiv.apply_symm_apply]
  have hq0 : 0 < q := (Fact.out : q.Prime).pos
  haveI hcharP : CharP (IsLocalRing.ResidueField ↥AL) q := by
    apply IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal
    have : ((q : ℕ) : ↥AL) = e (q : A) := by rw [map_natCast]
    rw [this, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff, ← mem_nonunits_iff,
      ← IsLocalRing.mem_maximalIdeal]
    exact hAq

  have hT₀ : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M' := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  have hT₀' : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 (q * M') := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  have hR'ex := ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
    L AL (CongruenceSubgroup.Gamma0 (q * M')) hT₀'
  rw [← hK₀'] at hR'ex
  obtain ⟨R', hR'i, hR'ii, hR'iii⟩ := hR'ex
  have hRex := ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
    L AL (CongruenceSubgroup.Gamma0 M') hT₀
  rw [← hK₀] at hRex
  obtain ⟨R, hRi, hRii, hRiii⟩ := hRex

  have hPB : ∀ (g : LaurentSeries L),
      (∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        g * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) ↔
      (∃ x y : LaurentSeries ↥AL, ModularCurve.coeffMap (IsLocalRing.residue ↥AL) y ≠ 0 ∧
        g * ModularCurve.coeffMap AL.subtype y = ModularCurve.coeffMap AL.subtype x) := by
    intro g
    rw [← FloorUnram.gaussPresentation_iff_laurent AL.subtype g]
    constructor
    · rintro ⟨x, y, hy, h⟩
      obtain ⟨hx1, -⟩ := FloorUnram.powerSeries_transport (algebraMap A L) AL.subtype e he x
      obtain ⟨hy1, hy2⟩ := FloorUnram.powerSeries_transport (algebraMap A L) AL.subtype e he y
      exact ⟨x.map (e : A →+* ↥AL), y.map (e : A →+* ↥AL), hy2.mpr hy, by rw [hx1, hy1]; exact h⟩
    · rintro ⟨x, y, hy, h⟩
      obtain ⟨hx1, -⟩ := FloorUnram.powerSeries_transport AL.subtype (algebraMap A L) e.symm he' x
      obtain ⟨hy1, hy2⟩ := FloorUnram.powerSeries_transport AL.subtype (algebraMap A L) e.symm he' y
      exact ⟨x.map (e.symm : ↥AL →+* A), y.map (e.symm : ↥AL →+* A), hy2.mpr hy, by rw [hx1, hy1]; exact h⟩
  have hOR' : O₀' = R'.integers := by
    ext g; rw [hO₀', hR'i, hPB]
  have hOR : O₀ = R.integers := by
    ext g; rw [hO₀, hRi, hPB]

  have hC : ∀ (u : ↥K₀) (hu : u ∈ R.integers) (hu' : (IntermediateField.inclusion hle₀' u) ∈ R'.integers),
      ((R'.residue ⟨IntermediateField.inclusion hle₀' u, hu'⟩ :
          ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥AL) (CongruenceSubgroup.Gamma0 (q * M')))) :
        LaurentSeries (IsLocalRing.ResidueField ↥AL)) =
      ((R.residue ⟨u, hu⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥AL) (CongruenceSubgroup.Gamma0 M'))) :
        LaurentSeries (IsLocalRing.ResidueField ↥AL)) := by
    intro u hu hu'
    obtain ⟨x, y, hy, hxy⟩ := (hRi u).mp hu
    have h1 := hRiii u hu x y hy hxy
    have h2 := hR'iii (IntermediateField.inclusion hle₀' u) hu' x y hy hxy
    exact mul_right_cancel₀ hy (h2.trans h1.symm)

  haveI : NeZero (q * M') := ⟨Nat.mul_ne_zero hq0.ne' (NeZero.ne M')⟩
  haveI : NeZero (q * M' / q) := ⟨by rw [Nat.mul_div_cancel_left _ hq0]; exact NeZero.ne M'⟩
  have hpM2 : ¬ q ^ 2 ∣ q * M' := by
    rw [pow_two]; exact fun h => hqM' (Nat.dvd_of_mul_dvd_mul_left hq0 h)
  have hGH : ∀ (N : ℕ) (hN : N = M') (H' : Subgroup (ZMod N)ˣ), H' = ⊤ →
      CohCarrier.GammaH N H' = CongruenceSubgroup.Gamma0 M' := by
    rintro N rfl H' rfl; exact CohCarrier.GammaH_top
  have hinf : ModularCurve.infSubgroup q (q * M') ⊤ (Nat.dvd_mul_right q M') = ⊤ := by
    rw [eq_top_iff]
    intro u _
    rw [ModularCurve.mem_infSubgroup_iff]
    obtain ⟨d, hd⟩ := ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd (Nat.dvd_mul_right q M')) u
    exact ⟨d, Subgroup.mem_top d, hd⟩
  have hlevel : CohCarrier.GammaH (q * M' / q) (ModularCurve.infSubgroup q (q * M') ⊤ (Nat.dvd_mul_right q M')) =
      CongruenceSubgroup.Gamma0 M' := hGH _ (Nat.mul_div_cancel_left M' hq0) _ hinf
  have hdrop : ∀ g : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥AL) (CongruenceSubgroup.Gamma0 (q * M'))),
      ∃ g'' : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥AL) (CongruenceSubgroup.Gamma0 M')),
        (g'' : LaurentSeries (IsLocalRing.ResidueField ↥AL)) = (g : LaurentSeries (IsLocalRing.ResidueField ↥AL)) := by
    intro g
    have hg1 : (g : LaurentSeries (IsLocalRing.ResidueField ↥AL)) ∈
        ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥AL) (CohCarrier.GammaH (q * M') ⊤) := by
      rw [CohCarrier.GammaH_top]; exact g.2
    obtain ⟨g', hg'⟩ := ModularCurve.exists_qExpFunctionFieldC_infSubgroup_coe_eq_of_charP q (q * M') ⊤
      (Nat.dvd_mul_right q M') hpM2 (fun u _ => Subgroup.mem_top u) (IsLocalRing.ResidueField ↥AL) ⟨_, hg1⟩
    refine ⟨⟨(g' : LaurentSeries (IsLocalRing.ResidueField ↥AL)), ?_⟩, hg'⟩
    rw [← hlevel]; exact g'.2

  have hfR' : f ∈ R'.integers := hOR' ▸ hf
  obtain ⟨g'', hg''⟩ := hdrop (R'.residue ⟨f, hfR'⟩)
  obtain ⟨w, hw⟩ := R.residue_surjective g''
  have hwO : (w : ↥K₀) ∈ O₀ := hOR.symm ▸ w.2
  have hwR' : IntermediateField.inclusion hle₀' (w : ↥K₀) ∈ R'.integers := by
    rw [← hOR', hO₀']
    exact (hO₀ (w : ↥K₀)).mp hwO
  refine ⟨(w : ↥K₀), hwO, ?_⟩
  have hmem : f - IntermediateField.inclusion hle₀' (w : ↥K₀) ∈ R'.integers := R'.integers.sub_mem hfR' hwR'
  rw [hOR']
  apply FloorUnram.mem_nonunits_of_residue_eq_zero R' _ hmem
  have hsplit : (⟨_, hmem⟩ : ↥R'.integers) = ⟨f, hfR'⟩ - ⟨_, hwR'⟩ := Subtype.ext rfl
  rw [hsplit, map_sub, sub_eq_zero]
  apply Subtype.ext
  rw [hC (w : ↥K₀) w.2 hwR', ← hg'', ← hw]

end S_ModularCurve_FullLevel_exists_sub_inclusion_mem_nonunits_gauss_gamma0_of_mem_gauss_gamma0_mul
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_sub_inclusion_mem_nonunits_gauss_gamma0_of_mem_gauss_gamma0_mul (solution)
