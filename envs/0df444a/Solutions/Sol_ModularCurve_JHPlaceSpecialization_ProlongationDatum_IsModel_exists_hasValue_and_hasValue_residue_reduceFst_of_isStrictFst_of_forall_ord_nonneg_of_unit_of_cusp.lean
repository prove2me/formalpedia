-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.exists_hasValue_and_hasValue_residue_reduceFst_of_isStrictFst_of_forall_ord_nonneg_of_unit_of_cusp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/121aa4c6-fed1-5b4c-8208-81cbf7f5adf2

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_oneSidedDivisorLaw_and_oneSidedCuspLaw_of_isModel_of_unit
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_hasValue_and_hasValue_residue_reduceFst_of_isStrictFst_of_forall_ord_nonneg_of_unit_of_cusp
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_hasValue_and_hasValue_residue_reduceFst_of_isStrictFst_of_forall_ord_nonneg_of_unit_of_cusp.AlgebraicCurve IsLocalRing ModularCurve"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor SemilinearAut SemilinearAut.ofAlgAut IsCurveOver IsCurveOver.finiteResidue"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField ord ord_mul ord_inv ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring residue_algebraMap HasValue hasValue_algebraMap exists_isUnit_of_ord_eq_zero exists_hasValue_of_surjective"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_q25 {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

p2m_export "AlgebraicCurve.Place" "ord_nonneg_of_mem_q25"

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg_q25 {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_nonneg_q25"

private theorem _root_.AlgebraicCurve.Place.ord_algebraMap_q25 (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (v.hasValue_algebraMap c).ord_eq_zero hc

p2m_export "AlgebraicCurve.Place" "ord_algebraMap_q25"

private theorem _root_.AlgebraicCurve.Place.ne_zero_of_ord_pos_q25 {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  simp at h

p2m_export "AlgebraicCurve.Place" "ne_zero_of_ord_pos_q25"

private theorem _root_.AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_q25 {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  constructor
  · intro hu
    have := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this
  · intro h0
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf0 h0
    exact hu

p2m_export "AlgebraicCurve.Place" "isUnit_iff_ord_eq_zero_q25"

private theorem _root_.AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_q25 {g : F} (hg : g ∈ v.toValuationSubring) (c : K) :
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
  · rw [v.isUnit_iff_ord_eq_zero_q25 hsub h0]
    have hnn := v.ord_nonneg_of_mem_q25 hsub
    constructor
    · intro hne
      exact Or.inr (lt_of_le_of_ne hnn (Ne.symm hne))
    · rintro (hEq | hpos)
      · exact absurd (sub_eq_zero.mpr hEq) h0
      · exact ne_of_gt hpos

p2m_export "AlgebraicCurve.Place" "hasValue_iff_eq_or_ord_sub_pos_q25"

theorem div_mem_of_ord_le_q25 {r t : F} (ht : t ≠ 0) (h : v.ord t ≤ v.ord r) :
    r / t ∈ v.toValuationSubring := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · apply v.mem_of_ord_nonneg_q25 (div_ne_zero hr ht)
    rw [div_eq_mul_inv, v.ord_mul hr (inv_ne_zero ht), v.ord_inv]
    omega

theorem tExpansion_coeff_unique_q25 {t : F} (ht : 0 < v.ord t) (r : F) (c c' : ℕ → K)
    (hc : ∀ m : ℕ, (r - ∑ i ∈ Finset.range m, algebraMap K F (c i) * t ^ i) / t ^ m ∈
      v.toValuationSubring)
    (hc' : ∀ m : ℕ, (r - ∑ i ∈ Finset.range m, algebraMap K F (c' i) * t ^ i) / t ^ m ∈
      v.toValuationSubring) :
    c = c' := by
  classical
  have ht0 : t ≠ 0 := v.ne_zero_of_ord_pos_q25 ht
  by_contra hne
  have hex : ∃ m, c m ≠ c' m := by
    by_contra hall
    exact hne (funext fun m => not_not.mp (not_exists.mp hall m))
  obtain ⟨m, hm, hmin⟩ : ∃ m, c m ≠ c' m ∧ ∀ i < m, c i = c' i :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => not_not.mp (Nat.find_min hex hi)⟩
  set e : K := c m - c' m with he
  have he0 : e ≠ 0 := sub_ne_zero.mpr hm

  have hdiff : (r - ∑ i ∈ Finset.range (m + 1), algebraMap K F (c' i) * t ^ i) / t ^ (m + 1) -
      (r - ∑ i ∈ Finset.range (m + 1), algebraMap K F (c i) * t ^ i) / t ^ (m + 1) =
      algebraMap K F e / t := by
    rw [← sub_div]
    have hnum : (r - ∑ i ∈ Finset.range (m + 1), algebraMap K F (c' i) * t ^ i) -
        (r - ∑ i ∈ Finset.range (m + 1), algebraMap K F (c i) * t ^ i) =
        algebraMap K F e * t ^ m := by
      have hs : ∑ i ∈ Finset.range (m + 1), algebraMap K F (c i) * t ^ i -
          ∑ i ∈ Finset.range (m + 1), algebraMap K F (c' i) * t ^ i =
          algebraMap K F e * t ^ m := by
        rw [← Finset.sum_sub_distrib, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add,
          ← sub_mul, ← map_sub]
        intro i hi
        rw [Finset.mem_range] at hi
        rw [hmin i hi, sub_self]
      rw [← hs]; ring
    rw [hnum, pow_succ, mul_comm (t ^ m) t, mul_div_mul_right _ _ (pow_ne_zero m ht0)]
  have hmem : algebraMap K F e / t ∈ v.toValuationSubring := by
    rw [← hdiff]; exact sub_mem (hc' (m + 1)) (hc (m + 1))
  have hord : v.ord (algebraMap K F e / t) < 0 := by
    have hae : algebraMap K F e ≠ 0 := (_root_.map_ne_zero _).mpr he0
    rw [div_eq_mul_inv, v.ord_mul hae (inv_ne_zero ht0), v.ord_inv, v.ord_algebraMap_q25]
    omega
  exact absurd (v.ord_nonneg_of_mem_q25 hmem) (not_le.mpr hord)

end Place
end AlgebraicCurve

namespace Subring p2m_export "Subring" "inclusion ext" end Subring
namespace Subring
p2m_open_scoped "Subring" in

private theorem _root_.Subring.inv_mem_of_isUnit_q25 {F : Type*} [Field F] {S : Subring F} {t : F} (h : t ∈ S)
    (hu : IsUnit (⟨t, h⟩ : S)) : t⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : Sˣ) : S).val * t = 1 := by
    have : ((u⁻¹ : Sˣ) : S) * (u : S) = 1 := Units.inv_mul u
    rw [hu] at this
    exact congrArg Subtype.val this
  rw [← (eq_inv_of_mul_eq_one_left h1)]
  exact SetLike.coe_mem _

end Subring
p2m_export "" "Subring.inv_mem_of_isUnit_q25"
namespace ValuationSubring p2m_export "ValuationSubring" "ext zero_mem mem_nonunits_iff mul_mem one_mem mem_or_inv_mem add_mem valuation inclusion LiesOverPrime" end ValuationSubring
namespace ValuationSubring
p2m_open_scoped "ValuationSubring" in

private theorem _root_.ValuationSubring.inv_mem_of_isUnit_q25 {F : Type*} [Field F] {S : ValuationSubring F} {t : F}
    (h : t ∈ S) (hu : IsUnit (⟨t, h⟩ : S)) : t⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : Sˣ) : S).val * t = 1 := by
    have : ((u⁻¹ : Sˣ) : S) * (u : S) = 1 := Units.inv_mul u
    rw [hu] at this
    exact congrArg Subtype.val this
  rw [← (eq_inv_of_mul_eq_one_left h1)]
  exact SetLike.coe_mem _

end ValuationSubring
p2m_export "" "ValuationSubring.inv_mem_of_isUnit_q25"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor SemilinearAut SemilinearAut.ofAlgAut IsCurveOver IsCurveOver.finiteResidue"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField ord ord_mul ord_inv ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring residue_algebraMap HasValue hasValue_algebraMap exists_isUnit_of_ord_eq_zero exists_hasValue_of_surjective"
p2m_open "AlgebraicCurve.Place"

private theorem _root_.AlgebraicCurve.Place.hasValue_iff_mem_and_eq_or_ord_sub_pos_q25
    {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Place K L) (g : L) (c : K) :
    v.HasValue g c ↔
      g ∈ v.toValuationSubring ∧ (g = algebraMap K L c ∨ 0 < v.ord (g - algebraMap K L c)) := by
  constructor
  · intro h
    exact ⟨h.mem, (v.hasValue_iff_eq_or_ord_sub_pos_q25 h.mem c).mp h⟩
  · rintro ⟨hg, h⟩
    exact (v.hasValue_iff_eq_or_ord_sub_pos_q25 hg c).mpr h
p2m_export "AlgebraicCurve.Place" "hasValue_iff_mem_and_eq_or_ord_sub_pos_q25"
end Place
end AlgebraicCurve

namespace Ws25AlphaH

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_hasValue_and_hasValue_residue_reduceFst_of_isStrictFst_of_forall_ord_nonneg_of_unit_of_cusp.AlgebraicCurve IsLocalRing ModularCurve"
open scoped MatrixGroups Classical

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]
  {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}
  {Psp : JHPlaceSpecialization p M H hpM A} (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
  (α β : ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (hα : α.IsIntegral) (hβ : β.IsIntegral)
  (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

theorem one_le_ord_residue_fst_of_ord_pos
    (hDL1 : ∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, D W = W.ord f) →
        ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) v = v.ord (Rpd.R₁.residue ⟨f, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    {W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)} (hW : Psp.IsStrictFst α β hα hβ δ W)
    (f : ↥(xHFunctionFieldBar M H)) (hf1 : f ∈ Rpd.R₁.integers) (hres : Rpd.R₁.residue ⟨f, hf1⟩ ≠ 0)
    (hnn : ∀ W' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ W' → Psp.reduceFst α hα W' = Psp.reduceFst α hα W → 0 ≤ W'.ord f)
    (hpos : 0 < W.ord f) : 1 ≤ (Psp.reduceFst α hα W).ord (Rpd.R₁.residue ⟨f, hf1⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
  classical
  have hf0 : f ≠ 0 := W.ne_zero_of_ord_pos_q25 hpos
  obtain ⟨D, hD, -⟩ := (hasPrincipalDivisors_xHFunctionFieldBar M H).exists_divisor f hf0
  have hlaw : Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) (Psp.reduceFst α hα W) =
      (Psp.reduceFst α hα W).ord (Rpd.R₁.residue ⟨f, hf1⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) :=
    hDL1 f hf1 hres D hD (Psp.reduceFst α hα W) hW.2
  set x : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := Psp.fstDiv α β hα hβ δ D with hx
  have hxapp : ∀ W', x W' = if Psp.IsStrictFst α β hα hβ δ W' then D W' else 0 := fun W' => by
    rw [hx, JHPlaceSpecialization.fstDiv, Finsupp.filter_apply]
  let g : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℤ := fun W' => if Psp.reduceFst α hα W' = Psp.reduceFst α hα W then x W' else 0
  have hgnn : ∀ W', 0 ≤ g W' := by
    intro W'
    show 0 ≤ (if Psp.reduceFst α hα W' = Psp.reduceFst α hα W then x W' else 0)
    split_ifs with h1
    · rw [hxapp]
      split_ifs with h2
      · rw [hD]; exact hnn W' h2 h1
      · exact le_refl _
    · exact le_refl _
  have hsum : ∑ W' ∈ x.support, g W' = (Psp.reduceFst α hα W).ord (Rpd.R₁.residue ⟨f, hf1⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
    rw [← hlaw]
    unfold Finsupp.mapDomain
    rw [Finsupp.sum_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro W' _
    simp only [g, Finsupp.single_apply]
  have hxW : x W = W.ord f := by rw [hxapp, if_pos hW, hD]
  have hWmem : W ∈ x.support := by rw [Finsupp.mem_support_iff, hxW]; exact ne_of_gt hpos
  have hgW : g W = W.ord f := by
    show (if Psp.reduceFst α hα W = Psp.reduceFst α hα W then x W else 0) = W.ord f
    rw [if_pos rfl, hxW]
  have h1 := Finset.single_le_sum (f := g) (s := x.support) (fun W' _ => hgnn W') hWmem
  rw [hsum, hgW] at h1
  omega

set_option maxHeartbeats 6400000 in

theorem value_mem
    (hDL1 : ∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, D W = W.ord f) →
        ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) v = v.ord (Rpd.R₁.residue ⟨f, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    {W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)} (hW : Psp.IsStrictFst α β hα hβ δ W)
    (r : ↥(xHFunctionFieldBar M H)) (h₁ : r ∈ Rpd.R₁.integers)
    (hrW' : ∀ W' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ W' → Psp.reduceFst α hα W' = Psp.reduceFst α hα W → r ∈ W'.toValuationSubring)
    (c₀ : AlgebraicClosure ℚ) (hc₀ : W.HasValue r c₀) : c₀ ∈ A := by
  classical
  by_contra hnot
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl; exact hnot A.zero_mem
  have hεA : c₀⁻¹ ∈ A := (A.mem_or_inv_mem c₀).resolve_left hnot
  set ε : ↥A := ⟨c₀⁻¹, hεA⟩ with hε
  have hεm : ε ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hnot
    have h := ValuationSubring.inv_mem_of_isUnit_q25 hεA hu
    rwa [inv_inv] at h
  have hredε : IsLocalRing.residue ↥A ε = 0 := (IsLocalRing.residue_eq_zero_iff ε).mpr hεm
  have hcε : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (ε : AlgebraicClosure ℚ) ∈ Rpd.R₁.integers := (Rpd.R₁.algebraMap_mem_iff _).mpr ε.2
  have hg1 : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (ε : AlgebraicClosure ℚ) * r - 1 ∈ Rpd.R₁.integers := sub_mem (mul_mem hcε h₁) (one_mem _)
  have hgsub : (⟨_, hg1⟩ : Rpd.R₁.integers) = ⟨_, hcε⟩ * ⟨r, h₁⟩ - 1 := rfl
  have hresg : Rpd.R₁.residue ⟨_, hg1⟩ = -1 := by
    rw [hgsub, map_sub, map_mul, map_one, Rpd.R₁.residue_algebraMap ε, hredε, map_zero, zero_mul, zero_sub]
  have hresg' : Rpd.R₁.residue ⟨_, hg1⟩ ≠ 0 := by
    rw [hresg]; exact neg_ne_zero.mpr one_ne_zero
  have hordg : (Psp.reduceFst α hα W).ord (Rpd.R₁.residue ⟨_, hg1⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) = 0 := by
    rw [hresg, show ((-1 : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (-1) by rw [map_neg, map_one]]
    exact (Psp.reduceFst α hα W).ord_algebraMap_q25 (-1)
  have hnng : ∀ W' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ W' → Psp.reduceFst α hα W' = Psp.reduceFst α hα W →
        0 ≤ W'.ord (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (ε : AlgebraicClosure ℚ) * r - 1) :=
    fun W' h1 h2 => W'.ord_nonneg_of_mem_q25 (sub_mem (mul_mem (W'.algebraMap_mem' _) (hrW' W' h1 h2)) (one_mem _))
  have hval1 : W.HasValue (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (ε : AlgebraicClosure ℚ) * r) 1 := by
    have h := (W.hasValue_algebraMap (ε : AlgebraicClosure ℚ)).mul hc₀
    rwa [show (ε : AlgebraicClosure ℚ) * c₀ = 1 from inv_mul_cancel₀ hc₀0] at h
  have hposg : 0 < W.ord (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (ε : AlgebraicClosure ℚ) * r - 1) := by
    rcases (W.hasValue_iff_eq_or_ord_sub_pos_q25 hval1.mem 1).mp hval1 with hEq | hpos
    · exfalso
      apply hresg'
      have h0 : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (ε : AlgebraicClosure ℚ) * r - 1 = 0 := by
        rw [map_one] at hEq; rw [hEq, sub_self]
      have : (⟨_, hg1⟩ : Rpd.R₁.integers) = 0 := Subtype.ext h0
      rw [this, map_zero]
    · rwa [map_one] at hpos
  have h := one_le_ord_residue_fst_of_ord_pos Rpd α β hα hβ δ hDL1 hW _ hg1 hresg' hnng hposg
  rw [hordg] at h
  omega

end Ws25AlphaH

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_hasValue_and_hasValue_residue_reduceFst_of_isStrictFst_of_forall_ord_nonneg_of_unit_of_cusp.AlgebraicCurve IsLocalRing ModularCurve"
open scoped MatrixGroups Classical

set_option maxHeartbeats 6400000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS) (hNV : Rpd.NodeValueLaw α β hα hβ δ SS)

    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α β hα hβ δ Q → Psp.IsStrictFst α β hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α β hα hβ δ Q → Psp.IsStrictSnd α β hα hβ δ Q' →
      Psp.reduceSnd β hβ δ Q' = Psp.reduceSnd β hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd β hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α β hα hβ δ W → Psp.reduceSnd β hβ δ W = Psp.reduceSnd β hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd β hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd β hβ δ C) =
            (Psp.reduceSnd β hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd β hβ δ C = w))
    (Qs : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQs : Psp.IsStrictFst α β hα hβ δ Qs)
    (r : ↥(xHFunctionFieldBar M H)) (h₁ : r ∈ Rpd.R₁.integers)
    (hr : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ V →
      Psp.reduceFst α hα V = Psp.reduceFst α hα Qs → 0 ≤ V.ord r) :
    ∃ c : ↥A, Qs.HasValue r (c : AlgebraicClosure ℚ) ∧
      (Psp.reduceFst α hα Qs).HasValue (Rpd.R₁.residue ⟨r, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (IsLocalRing.residue ↥A c) := by
  classical

  obtain ⟨hDL1, -, -, -⟩ :=
    ModularCurve.JHPlaceSpecialization.ProlongationDatum.oneSidedDivisorLaw_and_oneSidedCuspLaw_of_isModel_of_unit
      p M H hpM hpM2 hHp A hA θ α β hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hRL hNV hUnit

  have hrW' : ∀ W' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ W' → Psp.reduceFst α hα W' = Psp.reduceFst α hα Qs →
      r ∈ W'.toValuationSubring := by
    intro W' h1 h2
    rcases eq_or_ne r 0 with h0 | h0
    · rw [h0]; exact zero_mem _
    · exact W'.mem_of_ord_nonneg_q25 h0 (hr W' h1 h2)
  have hrW : r ∈ Qs.toValuationSubring := hrW' Qs hQs rfl

  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := (isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1
  haveI : Module.Finite (AlgebraicClosure ℚ) Qs.ResidueField := IsCurveOver.finiteResidue Qs
  haveI : Algebra.IsIntegral (AlgebraicClosure ℚ) Qs.ResidueField := Algebra.IsIntegral.of_finite _ _
  have hrat : Function.Surjective (algebraMap (AlgebraicClosure ℚ) Qs.ResidueField) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ) (K := Qs.ResidueField)).2
  obtain ⟨c₀, hc₀, -⟩ := Qs.exists_hasValue_of_surjective hrat hrW

  have hc₀A : c₀ ∈ A := Ws25AlphaH.value_mem Rpd α β hα hβ δ hDL1 hQs r h₁ hrW' c₀ hc₀
  obtain ⟨c, hc⟩ : ∃ c : ↥A, (c : AlgebraicClosure ℚ) = c₀ := ⟨⟨c₀, hc₀A⟩, rfl⟩
  subst hc
  refine ⟨c, hc₀, ?_⟩

  have hcR : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ) ∈ Rpd.R₁.integers := (Rpd.R₁.algebraMap_mem_iff _).mpr c.2
  have hs1 : r - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ) ∈ Rpd.R₁.integers := sub_mem h₁ hcR
  have hssub : (⟨_, hs1⟩ : Rpd.R₁.integers) = ⟨r, h₁⟩ - ⟨_, hcR⟩ := rfl
  have hress : Rpd.R₁.residue ⟨_, hs1⟩ = Rpd.R₁.residue ⟨r, h₁⟩ - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A c) := by
    rw [hssub, map_sub, Rpd.R₁.residue_algebraMap c]
  by_cases hz : Rpd.R₁.residue ⟨_, hs1⟩ = 0
  · have h : Rpd.R₁.residue ⟨r, h₁⟩ = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A c) := by
      rw [hress] at hz; exact sub_eq_zero.mp hz
    rw [h]
    exact (Psp.reduceFst α hα Qs).hasValue_algebraMap (IsLocalRing.residue ↥A c)
  · have hnn : ∀ W' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ W' → Psp.reduceFst α hα W' = Psp.reduceFst α hα Qs →
          0 ≤ W'.ord (r - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ)) :=
      fun W' h1 h2 => W'.ord_nonneg_of_mem_q25 (sub_mem (hrW' W' h1 h2) (W'.algebraMap_mem' _))
    have hpos : 0 < Qs.ord (r - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ)) := by
      rcases (Qs.hasValue_iff_eq_or_ord_sub_pos_q25 hrW (c : AlgebraicClosure ℚ)).mp hc₀ with hEq | hpos
      · exfalso
        apply hz
        have h0 : r - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ) = 0 := by
          rw [hEq, sub_self]
        have : (⟨_, hs1⟩ : Rpd.R₁.integers) = 0 := Subtype.ext h0
        rw [this, map_zero]
      · exact hpos
    have h1 := Ws25AlphaH.one_le_ord_residue_fst_of_ord_pos Rpd α β hα hβ δ hDL1 hQs _ hs1 hz hnn hpos
    rw [hress] at h1
    have hpos' : 0 < (Psp.reduceFst α hα Qs).ord ((Rpd.R₁.residue ⟨r, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A c)) := by
      have : ((Rpd.R₁.residue ⟨r, h₁⟩ - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A c) : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) =
          (Rpd.R₁.residue ⟨r, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A c) := rfl
      omega
    rw [(Psp.reduceFst α hα Qs).hasValue_iff_mem_and_eq_or_ord_sub_pos_q25]
    refine ⟨?_, Or.inr hpos'⟩
    have hm : (Rpd.R₁.residue ⟨r, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A c) ∈
        (Psp.reduceFst α hα Qs).toValuationSubring :=
      (Psp.reduceFst α hα Qs).mem_of_ord_nonneg_q25 ((Psp.reduceFst α hα Qs).ne_zero_of_ord_pos_q25 hpos') hpos'.le
    have h := add_mem hm ((Psp.reduceFst α hα Qs).algebraMap_mem' (IsLocalRing.residue ↥A c))
    simpa using h

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_hasValue_and_hasValue_residue_reduceFst_of_isStrictFst_of_forall_ord_nonneg_of_unit_of_cusp
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_hasValue_and_hasValue_residue_reduceFst_of_isStrictFst_of_forall_ord_nonneg_of_unit_of_cusp (solution)
