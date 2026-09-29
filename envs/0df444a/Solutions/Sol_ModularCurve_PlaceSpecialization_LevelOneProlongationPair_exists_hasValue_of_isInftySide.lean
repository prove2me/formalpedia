-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_hasValue_of_isInftySide
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/2de14853-13c5-5149-931c-7071bae20a30

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawInfty_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_isInftySide_cuspInftyBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_algebraMap_eq_red
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_hasValue_of_isInftySide
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar"
p2m_attr_erase "simp" "ModularCurve.coe_towerSubstBar"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_hasValue_of_isInftySide.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_hasValue_of_isInftySide.ModularCurve"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor IsCurveOver IsCurveOver.finiteResidue"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "residue_algebraMap HasValue hasValue_algebraMap exists_isUnit_of_ord_eq_zero exists_hasValue_of_surjective ext ResidueField ord ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_o14 {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

p2m_export "AlgebraicCurve.Place" "ord_nonneg_of_mem_o14"

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg_o14 {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_nonneg_o14"

private theorem _root_.AlgebraicCurve.Place.ord_algebraMap_o14 (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (v.hasValue_algebraMap c).ord_eq_zero hc

p2m_export "AlgebraicCurve.Place" "ord_algebraMap_o14"

private theorem _root_.AlgebraicCurve.Place.ne_zero_of_ord_pos_o14 {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  simp at h

p2m_export "AlgebraicCurve.Place" "ne_zero_of_ord_pos_o14"

private theorem _root_.AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_o14 {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  constructor
  · intro hu
    have := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this
  · intro h0
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf0 h0
    exact hu

p2m_export "AlgebraicCurve.Place" "isUnit_iff_ord_eq_zero_o14"

private theorem _root_.AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_o14 {g : F} (hg : g ∈ v.toValuationSubring) (c : K) :
    v.HasValue g c ↔ g = algebraMap K F c ∨ 0 < v.ord (g - algebraMap K F c) := by
  have hcm : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hsub : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem hg hcm

  have key : v.HasValue g c ↔
      IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F c, hsub⟩ = 0 := by
    have hx : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) =
        ⟨g, hg⟩ - algebraMap K v.toValuationSubring c := Subtype.ext (by simp)
    rw [hx, map_sub, sub_eq_zero, v.residue_algebraMap c]
    constructor
    · intro h; exact h.residue_eq
    · intro h; exact ⟨hg, h⟩
  rw [key, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rcases eq_or_ne (g - algebraMap K F c) 0 with h0 | h0
  · have hg' : g = algebraMap K F c := sub_eq_zero.mp h0
    have hz : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) = 0 := Subtype.ext h0
    rw [hz]
    exact ⟨fun _ => Or.inl hg', fun _ => not_isUnit_zero⟩
  · rw [v.isUnit_iff_ord_eq_zero_o14 hsub h0]
    have hnn := v.ord_nonneg_of_mem_o14 hsub
    constructor
    · intro hne
      exact Or.inr (lt_of_le_of_ne hnn (Ne.symm hne))
    · rintro (hEq | hpos)
      · exact absurd (sub_eq_zero.mpr hEq) h0
      · exact ne_of_gt hpos

p2m_export "AlgebraicCurve.Place" "hasValue_iff_eq_or_ord_sub_pos_o14"
end Place
end AlgebraicCurve

namespace Subring p2m_export "Subring" "ext" end Subring
namespace Subring
p2m_open_scoped "Subring" in

private theorem _root_.Subring.inv_mem_of_isUnit_o14 {F : Type*} [Field F] {S : Subring F} {t : F} (h : t ∈ S)
    (hu : IsUnit (⟨t, h⟩ : S)) : t⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : Sˣ) : S).val * t = 1 := by
    have : ((u⁻¹ : Sˣ) : S) * (u : S) = 1 := Units.inv_mul u
    rw [hu] at this
    exact congrArg Subtype.val this
  rw [← (eq_inv_of_mul_eq_one_left h1)]
  exact SetLike.coe_mem _

end Subring
p2m_export "" "Subring.inv_mem_of_isUnit_o14"
namespace ValuationSubring p2m_export "ValuationSubring" "ext zero_mem mem_nonunits_iff mul_mem one_mem mem_or_inv_mem add_mem valuation" end ValuationSubring
namespace ValuationSubring
p2m_open_scoped "ValuationSubring" in

private theorem _root_.ValuationSubring.inv_mem_of_isUnit_o14 {F : Type*} [Field F] {S : ValuationSubring F} {t : F}
    (h : t ∈ S) (hu : IsUnit (⟨t, h⟩ : S)) : t⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : Sˣ) : S).val * t = 1 := by
    have : ((u⁻¹ : Sˣ) : S) * (u : S) = 1 := Units.inv_mul u
    rw [hu] at this
    exact congrArg Subtype.val this
  rw [← (eq_inv_of_mul_eq_one_left h1)]
  exact SetLike.coe_mem _

end ValuationSubring
p2m_export "" "ValuationSubring.inv_mem_of_isUnit_o14"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor IsCurveOver IsCurveOver.finiteResidue"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "residue_algebraMap HasValue hasValue_algebraMap exists_isUnit_of_ord_eq_zero exists_hasValue_of_surjective ext ResidueField ord ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring"
p2m_open "AlgebraicCurve.Place"

private theorem _root_.AlgebraicCurve.Place.hasValue_iff_mem_and_eq_or_ord_sub_pos_o14
    {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Place K L) (g : L) (c : K) :
    v.HasValue g c ↔
      g ∈ v.toValuationSubring ∧ (g = algebraMap K L c ∨ 0 < v.ord (g - algebraMap K L c)) := by
  constructor
  · intro h
    exact ⟨h.mem, (v.hasValue_iff_eq_or_ord_sub_pos_o14 h.mem c).mp h⟩
  · rintro ⟨hg, h⟩
    exact (v.hasValue_iff_eq_or_ord_sub_pos_o14 hg c).mpr h
p2m_export "AlgebraicCurve.Place" "hasValue_iff_mem_and_eq_or_ord_sub_pos_o14"
end Place
end AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence cuspInftyBar isInftySide_cuspInftyBar isCurveOver_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
p2m_open "ModularCurve"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair IsCuspidal IsInftySide redFst redFst_eq_placeInfty_of_forall_ord_le_zero"
p2m_open "ModularCurve.PlaceSpecialization"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₁_apply IsModel R₁ redBar_residue cuspLawInfty_oneSided residue_algebraMap_eq_red"
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

private def _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.FibreSumLawFstAt (R : LevelOneProlongationPair P)
    (S : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop) [DecidablePred S]
    (v : Place k ↥(modularFunctionFieldC k 1)) : Prop :=
  ∀ (g : ↥(modularFunctionFieldBar (1 * q))) (hg : g ∈ R.R₁.integers), R.R₁.residue ⟨g, hg⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), (∀ W, D W = W.ord g) →
      Finsupp.mapDomain P.redFst (D.filter S) v = v.ord (R.residue₁ ⟨g, hg⟩)

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "FibreSumLawFstAt"
set_option maxHeartbeats 6400000 in

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.one_le_ord_residue₁_of_fibreSumLaw_o14 (R : LevelOneProlongationPair P)
    {S : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop} [DecidablePred S]
    {v : Place k ↥(modularFunctionFieldC k 1)} (hlaw : R.FibreSumLawFstAt S v)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hW : S W) (hWv : P.redFst W = v)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf1 : f ∈ R.R₁.integers) (hres : R.R₁.residue ⟨f, hf1⟩ ≠ 0)
    (hnn : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), S W' → P.redFst W' = v → 0 ≤ W'.ord f)
    (hpos : 0 < W.ord f) : 1 ≤ v.ord (R.residue₁ ⟨f, hf1⟩) := by
  classical
  have hf0 : f ≠ 0 := W.ne_zero_of_ord_pos_o14 hpos
  obtain ⟨D, hD, -⟩ :=
    (hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * q)).exists_divisor f hf0
  have hlaw' : Finsupp.mapDomain P.redFst (D.filter S) v = v.ord (R.residue₁ ⟨f, hf1⟩) :=
    hlaw f hf1 hres D hD
  set x : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) := D.filter S with hx
  have hxapp : ∀ W', x W' = if S W' then D W' else 0 := fun W' => by
    rw [hx, Finsupp.filter_apply]
  let g : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℤ := fun W' => if P.redFst W' = v then x W' else 0
  have hgnn : ∀ W', 0 ≤ g W' := by
    intro W'
    show 0 ≤ (if P.redFst W' = v then x W' else 0)
    split_ifs with h1
    · rw [hxapp]
      split_ifs with h2
      · rw [hD]; exact hnn W' h2 h1
      · exact le_refl _
    · exact le_refl _
  have hsum : ∑ W' ∈ x.support, g W' = v.ord (R.residue₁ ⟨f, hf1⟩) := by
    rw [← hlaw']
    unfold Finsupp.mapDomain
    rw [Finsupp.sum_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro W' _
    simp only [g, Finsupp.single_apply]
  have hxW : x W = W.ord f := by rw [hxapp, if_pos hW, hD]
  have hWmem : W ∈ x.support := by rw [Finsupp.mem_support_iff, hxW]; exact ne_of_gt hpos
  have hgW : g W = W.ord f := by
    show (if P.redFst W = v then x W else 0) = W.ord f
    rw [if_pos hWv, hxW]
  have h1 := Finset.single_le_sum (f := g) (s := x.support) (fun W' _ => hgnn W') hWmem
  rw [hsum, hgW] at h1
  omega

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "one_le_ord_residue₁_of_fibreSumLaw_o14"
set_option maxHeartbeats 6400000 in

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.value_mem_of_fibreSumLaw_o14 (R : LevelOneProlongationPair P)
    {S : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop} [DecidablePred S]
    {v : Place k ↥(modularFunctionFieldC k 1)} (hlaw : R.FibreSumLawFstAt S v)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hW : S W) (hWv : P.redFst W = v)
    (r : ↥(modularFunctionFieldBar (1 * q))) (h₁ : r ∈ R.R₁.integers)
    (hrW' : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), S W' → P.redFst W' = v → r ∈ W'.toValuationSubring)
    (c₀ : AlgebraicClosure ℚ) (hc₀ : W.HasValue r c₀) : c₀ ∈ A := by
  classical
  by_contra hnot
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl; exact hnot A.zero_mem
  have hεA : c₀⁻¹ ∈ A := (A.mem_or_inv_mem c₀).resolve_left hnot
  set ε : A := ⟨c₀⁻¹, hεA⟩ with hε
  have hεm : ε ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hnot
    have h := ValuationSubring.inv_mem_of_isUnit_o14 hεA hu
    rwa [inv_inv] at h
  have hredε : red ε = 0 := by
    rw [← R.redBar_residue ε, (IsLocalRing.residue_eq_zero_iff ε).mpr hεm, map_zero]
  have hcε : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (ε : AlgebraicClosure ℚ) ∈
      R.R₁.integers := (R.R₁.algebraMap_mem_iff _).mpr ε.2
  have hg1 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (ε : AlgebraicClosure ℚ) * r - 1 ∈
      R.R₁.integers := sub_mem (mul_mem hcε h₁) (one_mem _)
  have hgsub : (⟨_, hg1⟩ : R.R₁.integers) = ⟨_, hcε⟩ * ⟨r, h₁⟩ - 1 := rfl
  have hresg : R.residue₁ ⟨_, hg1⟩ = -1 := by
    rw [hgsub, map_sub, map_mul, map_one, R.residue_algebraMap_eq_red ε hcε, hredε, map_zero, zero_mul,
      zero_sub]
  have hresg' : R.R₁.residue ⟨_, hg1⟩ ≠ 0 := by
    intro h0
    have : R.residue₁ ⟨_, hg1⟩ = 0 := by rw [residue₁_apply, h0, map_zero]
    rw [hresg] at this
    exact (neg_ne_zero.mpr one_ne_zero) this
  have hordg : v.ord (R.residue₁ ⟨_, hg1⟩) = 0 := by
    rw [hresg, show (-1 : ↥(modularFunctionFieldC k 1)) = algebraMap k ↥(modularFunctionFieldC k 1) (-1) by
      rw [map_neg, map_one]]
    exact v.ord_algebraMap_o14 (-1)
  have hnng : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      S W' → P.redFst W' = v →
        0 ≤ W'.ord (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (ε : AlgebraicClosure ℚ) * r - 1) :=
    fun W' h1 h2 => W'.ord_nonneg_of_mem_o14
      (sub_mem (mul_mem (W'.algebraMap_mem' _) (hrW' W' h1 h2)) (one_mem _))
  have hval1 : W.HasValue (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
      (ε : AlgebraicClosure ℚ) * r) 1 := by
    have h := (W.hasValue_algebraMap (ε : AlgebraicClosure ℚ)).mul hc₀
    rwa [show (ε : AlgebraicClosure ℚ) * c₀ = 1 from inv_mul_cancel₀ hc₀0] at h
  have hposg : 0 < W.ord (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
      (ε : AlgebraicClosure ℚ) * r - 1) := by
    rcases (W.hasValue_iff_eq_or_ord_sub_pos_o14 hval1.mem 1).mp hval1 with hEq | hpos
    · exfalso
      apply hresg'
      have h0 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (ε : AlgebraicClosure ℚ) * r - 1 = 0 := by
        rw [map_one] at hEq; rw [hEq, sub_self]
      have : (⟨_, hg1⟩ : R.R₁.integers) = 0 := Subtype.ext h0
      rw [this, map_zero]
    · rwa [map_one] at hpos
  have h := R.one_le_ord_residue₁_of_fibreSumLaw_o14 hlaw hW hWv _ hg1 hresg' hnng hposg
  rw [hordg] at h
  omega

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "value_mem_of_fibreSumLaw_o14"
set_option maxHeartbeats 6400000 in

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_hasValue_of_fibreSumLaw_o14 (R : LevelOneProlongationPair P)
    {S : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop} [DecidablePred S]
    {v : Place k ↥(modularFunctionFieldC k 1)} (hlaw : R.FibreSumLawFstAt S v)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hW : S W) (hWv : P.redFst W = v)
    (r : ↥(modularFunctionFieldBar (1 * q))) (h₁ : r ∈ R.R₁.integers)
    (hrW' : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), S W' → P.redFst W' = v → r ∈ W'.toValuationSubring) :
    ∃ c : A, W.HasValue r (c : AlgebraicClosure ℚ) ∧ v.HasValue (R.residue₁ ⟨r, h₁⟩) (red c) := by
  classical
  have hrW : r ∈ W.toValuationSubring := hrW' W hW hWv

  haveI := isCurveOver_modularFunctionFieldBar (1 * q)
  haveI : Module.Finite (AlgebraicClosure ℚ) W.ResidueField := IsCurveOver.finiteResidue W
  haveI : Algebra.IsIntegral (AlgebraicClosure ℚ) W.ResidueField := Algebra.IsIntegral.of_finite _ _
  have hrat : Function.Surjective (algebraMap (AlgebraicClosure ℚ) W.ResidueField) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ) (K := W.ResidueField)).2
  obtain ⟨c₀, hc₀, -⟩ := W.exists_hasValue_of_surjective hrat hrW

  have hc₀A : c₀ ∈ A := R.value_mem_of_fibreSumLaw_o14 hlaw hW hWv r h₁ hrW' c₀ hc₀
  obtain ⟨c, hc⟩ : ∃ c : A, (c : AlgebraicClosure ℚ) = c₀ := ⟨⟨c₀, hc₀A⟩, rfl⟩
  subst hc
  refine ⟨c, hc₀, ?_⟩

  have hcR : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) ∈
      R.R₁.integers := (R.R₁.algebraMap_mem_iff _).mpr c.2
  have hs1 : r - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) ∈
      R.R₁.integers := sub_mem h₁ hcR
  have hssub : (⟨_, hs1⟩ : R.R₁.integers) = ⟨r, h₁⟩ - ⟨_, hcR⟩ := rfl
  have hress : R.residue₁ ⟨_, hs1⟩ = R.residue₁ ⟨r, h₁⟩ - algebraMap k ↥(modularFunctionFieldC k 1) (red c) := by
    rw [hssub, map_sub, R.residue_algebraMap_eq_red c hcR]
  by_cases hz : R.residue₁ ⟨_, hs1⟩ = 0
  · have h : R.residue₁ ⟨r, h₁⟩ = algebraMap k ↥(modularFunctionFieldC k 1) (red c) := by
      rw [hress] at hz; exact sub_eq_zero.mp hz
    rw [h]
    exact v.hasValue_algebraMap (red c)
  · have hres' : R.R₁.residue ⟨_, hs1⟩ ≠ 0 := fun h0 => hz (by rw [residue₁_apply, h0, map_zero])
    have hnn : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        S W' → P.redFst W' = v →
          0 ≤ W'.ord (r - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ)) :=
      fun W' h1 h2 => W'.ord_nonneg_of_mem_o14 (sub_mem (hrW' W' h1 h2) (W'.algebraMap_mem' _))
    have hpos : 0 < W.ord (r - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
        (c : AlgebraicClosure ℚ)) := by
      rcases (W.hasValue_iff_eq_or_ord_sub_pos_o14 hrW (c : AlgebraicClosure ℚ)).mp hc₀ with hEq | hpos
      · exfalso
        apply hz
        have h0 : r - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) = 0 := by
          rw [hEq, sub_self]
        have : (⟨_, hs1⟩ : R.R₁.integers) = 0 := Subtype.ext h0
        rw [this, map_zero]
      · exact hpos
    have h1 := R.one_le_ord_residue₁_of_fibreSumLaw_o14 hlaw hW hWv _ hs1 hres' hnn hpos
    rw [hress] at h1
    have hpos' : 0 < v.ord (R.residue₁ ⟨r, h₁⟩ - algebraMap k ↥(modularFunctionFieldC k 1) (red c)) := by
      omega
    rw [v.hasValue_iff_mem_and_eq_or_ord_sub_pos_o14]
    refine ⟨?_, Or.inr hpos'⟩
    have hm : R.residue₁ ⟨r, h₁⟩ - algebraMap k ↥(modularFunctionFieldC k 1) (red c) ∈
        v.toValuationSubring :=
      v.mem_of_ord_nonneg_o14 (v.ne_zero_of_ord_pos_o14 hpos') hpos'.le
    have h := add_mem hm (v.algebraMap_mem' (red c))
    simpa using h

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "exists_hasValue_of_fibreSumLaw_o14"
end LevelOneProlongationPair
end PlaceSpecialization
end ModularCurve

set_option maxHeartbeats 6400000 in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_hasValue_of_isInftySide.ModularCurve _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_hasValue_of_isInftySide.ModularCurve.PlaceSpecialization _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_hasValue_of_isInftySide.ModularCurve.PlaceSpecialization.LevelOneProlongationPair in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hW : P.IsInftySide W)
    (r : ↥(modularFunctionFieldBar (1 * q))) (h₁ : r ∈ R.R₁.integers)
    (hr : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.IsInftySide W' → r ∈ W'.toValuationSubring) :
    ∃ c : A, W.HasValue r (c : AlgebraicClosure ℚ) ∧
      (P.redFst W).HasValue (R.residue₁ ⟨r, h₁⟩) (red c) := by
  classical

  have hcuspW : P.IsCuspidal W := hW.1
  have hcuspC : P.IsInftySide (cuspInftyBar (1 * q)) := isInftySide_cuspInftyBar P
  have hWv : P.redFst W = P.redFst (cuspInftyBar (1 * q)) := by
    rw [P.redFst_eq_placeInfty_of_forall_ord_le_zero W (fun a => hcuspW a),
      P.redFst_eq_placeInfty_of_forall_ord_le_zero (cuspInftyBar (1 * q)) (fun a => hcuspC.1 a)]

  have hlaw : R.FibreSumLawFstAt P.IsInftySide (P.redFst (cuspInftyBar (1 * q))) :=
    fun g hg hres D hD => R.cuspLawInfty_oneSided g hg hres D hD
  obtain ⟨c, hc, hv⟩ :=
    R.exists_hasValue_of_fibreSumLaw_o14 hlaw hW hWv r h₁ (fun W' h _ => hr W' h)
  refine ⟨c, hc, ?_⟩
  rw [hWv]
  exact hv

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_hasValue_of_isInftySide
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_hasValue_of_isInftySide (solution)
