-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsModel.ord_jFun_sub_eq_one_of_isStrictTypeOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/2fd7d2f9-7cd2-5442-a4fe-f15d1d9a14a5

import Mathlib
import Definitions.Def_ModularCurve_SmoothPointLocalRing
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_integers_residue_jFun_sub_ne_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_integers_snd_residue_jFun_sub_ne_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_redFst_residue_jFun_sub_eq_one
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_not_isStrictType_of_isCuspidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_ord_jFun_sub_eq_one_of_isStrictTypeOne
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_ord_jFun_sub_eq_one_of_isStrictTypeOne.AlgebraicCurve IsLocalRing ModularCurve"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "residue_algebraMap HasValue hasValue_algebraMap exists_isUnit_of_ord_eq_zero ext ord ord_mul ord_inv ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_e15 {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

p2m_export "AlgebraicCurve.Place" "ord_nonneg_of_mem_e15"

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg_e15 {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_nonneg_e15"

private theorem _root_.AlgebraicCurve.Place.ord_algebraMap_e15 (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (v.hasValue_algebraMap c).ord_eq_zero hc

p2m_export "AlgebraicCurve.Place" "ord_algebraMap_e15"

private theorem _root_.AlgebraicCurve.Place.ne_zero_of_ord_pos_e15 {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  simp at h

p2m_export "AlgebraicCurve.Place" "ne_zero_of_ord_pos_e15"

private theorem _root_.AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_e15 {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  constructor
  · intro hu
    have := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this
  · intro h0
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf0 h0
    exact hu

p2m_export "AlgebraicCurve.Place" "isUnit_iff_ord_eq_zero_e15"

theorem hasValue_iff_eq_or_ord_sub_pos_e15 {g : F} (hg : g ∈ v.toValuationSubring) (c : K) :
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
  · rw [v.isUnit_iff_ord_eq_zero_e15 hsub h0]
    have hnn := v.ord_nonneg_of_mem_e15 hsub
    constructor
    · intro hne
      exact Or.inr (lt_of_le_of_ne hnn (Ne.symm hne))
    · rintro (hEq | hpos)
      · exact absurd (sub_eq_zero.mpr hEq) h0
      · exact ne_of_gt hpos

theorem div_mem_of_ord_le_e15 {r t : F} (ht : t ≠ 0) (h : v.ord t ≤ v.ord r) :
    r / t ∈ v.toValuationSubring := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · apply v.mem_of_ord_nonneg_e15 (div_ne_zero hr ht)
    rw [div_eq_mul_inv, v.ord_mul hr (inv_ne_zero ht), v.ord_inv]
    omega

theorem tExpansion_coeff_unique_e15 {t : F} (ht : 0 < v.ord t) (r : F) (c c' : ℕ → K)
    (hc : ∀ m : ℕ, (r - ∑ i ∈ Finset.range m, algebraMap K F (c i) * t ^ i) / t ^ m ∈
      v.toValuationSubring)
    (hc' : ∀ m : ℕ, (r - ∑ i ∈ Finset.range m, algebraMap K F (c' i) * t ^ i) / t ^ m ∈
      v.toValuationSubring) :
    c = c' := by
  classical
  have ht0 : t ≠ 0 := v.ne_zero_of_ord_pos_e15 ht
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
    rw [div_eq_mul_inv, v.ord_mul hae (inv_ne_zero ht0), v.ord_inv, v.ord_algebraMap_e15]
    omega
  exact absurd (v.ord_nonneg_of_mem_e15 hmem) (not_le.mpr hord)

end Place
end AlgebraicCurve

namespace Subring p2m_export "Subring" "ext" end Subring
namespace Subring
p2m_open_scoped "Subring" in

private theorem _root_.Subring.inv_mem_of_isUnit_e15 {F : Type*} [Field F] {S : Subring F} {t : F} (h : t ∈ S)
    (hu : IsUnit (⟨t, h⟩ : S)) : t⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : Sˣ) : S).val * t = 1 := by
    have : ((u⁻¹ : Sˣ) : S) * (u : S) = 1 := Units.inv_mul u
    rw [hu] at this
    exact congrArg Subtype.val this
  rw [← (eq_inv_of_mul_eq_one_left h1)]
  exact SetLike.coe_mem _

end Subring
p2m_export "" "Subring.inv_mem_of_isUnit_e15"
namespace ValuationSubring p2m_export "ValuationSubring" "ext mem_nonunits_iff mul_mem add_mem valuation" end ValuationSubring
namespace ValuationSubring
p2m_open_scoped "ValuationSubring" in

private theorem _root_.ValuationSubring.inv_mem_of_isUnit_e15 {F : Type*} [Field F] {S : ValuationSubring F} {t : F}
    (h : t ∈ S) (hu : IsUnit (⟨t, h⟩ : S)) : t⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : Sˣ) : S).val * t = 1 := by
    have : ((u⁻¹ : Sˣ) : S) * (u : S) = 1 := Units.inv_mul u
    rw [hu] at this
    exact congrArg Subtype.val this
  rw [← (eq_inv_of_mul_eq_one_left h1)]
  exact SetLike.coe_mem _

end ValuationSubring
p2m_export "" "ValuationSubring.inv_mem_of_isUnit_e15"

open ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.LevelOneProlongationPair} (hR : R.IsModel)
    {Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hQ : P.IsStrictTypeOne Q)
    (j₀ : A) (hj₀ : 0 < Q.ord (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ))) :
    Q.ord (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) = 1 ∧
      ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        P.IsStrictTypeOne W → P.redFst W = P.redFst Q → W ≠ Q →
          W.ord (PlaceSpecialization.jFun (q := q) -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) = 0 := by
  classical
  obtain ⟨ht1, hres1⟩ := R.exists_mem_integers_residue_jFun_sub_ne_zero j₀
  obtain ⟨ht2, hres2⟩ := R.exists_mem_integers_snd_residue_jFun_sub_ne_zero j₀
  have hord1 : (P.redFst Q).ord (R.residue₁ ⟨_, ht1⟩) = 1 := R.ord_redFst_residue_jFun_sub_eq_one j₀ hj₀ ht1
  set t := (jFun (q := q) -
    algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (j₀ : AlgebraicClosure ℚ)) with ht_def
  have ht0 : t ≠ 0 := Q.ne_zero_of_ord_pos_e15 hj₀

  have hnn : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.IsStrictTypeOne W → 0 ≤ W.ord t := by
    intro W hW
    by_contra hneg
    push Not at hneg
    have hcusp : P.IsCuspidal W := by
      intro a
      by_contra hpos
      push Not at hpos
      have hja : jFun (q := q) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
          (a : AlgebraicClosure ℚ) ∈ W.toValuationSubring :=
        W.mem_of_ord_nonneg_e15 (W.ne_zero_of_ord_pos_e15 hpos) hpos.le
      have hj : jFun (q := q) ∈ W.toValuationSubring := by
        have := add_mem hja (W.algebraMap_mem' (a : AlgebraicClosure ℚ))
        simpa using this
      have htW : t ∈ W.toValuationSubring := sub_mem hj (W.algebraMap_mem' _)
      exact absurd (W.ord_nonneg_of_mem_e15 htW) (not_le.mpr hneg)
    exact (not_isStrictType_of_isCuspidal P W hcusp).1 hW

  obtain ⟨D, hD, -⟩ := (hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * q)).exists_divisor t ht0
  have hlaw' : Finsupp.mapDomain P.redFst (D.filter P.IsStrictTypeOne) (P.redFst Q) =
      (P.redFst Q).ord (R.residue₁ ⟨_, ht1⟩) := hR.1 t ht1 ht2 hres1 hres2 D hD (P.redFst Q) hQ.2
  rw [hord1] at hlaw'
  set x : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) := D.filter P.IsStrictTypeOne
    with hx
  have hxapp : ∀ W, x W = if P.IsStrictTypeOne W then D W else 0 := fun W => by
    rw [hx, Finsupp.filter_apply]
  have hxnn : ∀ W, 0 ≤ x W := fun W => by
    rw [hxapp]
    split_ifs with h
    · rw [hD]; exact hnn W h
    · exact le_refl _
  let g : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℤ :=
    fun W => if P.redFst W = P.redFst Q then x W else 0
  have hgnn : ∀ W, 0 ≤ g W := fun W => by
    show 0 ≤ (if P.redFst W = P.redFst Q then x W else 0)
    split_ifs
    · exact hxnn W
    · exact le_refl _
  have hsum : ∑ W ∈ x.support, g W = 1 := by
    rw [← hlaw']
    unfold Finsupp.mapDomain
    rw [Finsupp.sum_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro W _
    simp only [g, Finsupp.single_apply]
  have hxQ : x Q = Q.ord t := by rw [hxapp, if_pos hQ, hD]
  have hQmem : Q ∈ x.support := by
    rw [Finsupp.mem_support_iff, hxQ]; exact ne_of_gt hj₀
  have hgQ : g Q = Q.ord t := by
    show (if P.redFst Q = P.redFst Q then x Q else 0) = Q.ord t
    rw [if_pos rfl, hxQ]
  have h1 : Q.ord t ≤ 1 := by
    have h := Finset.single_le_sum (f := g) (s := x.support) (fun W _ => hgnn W) hQmem
    rw [hgQ, hsum] at h
    exact h
  have hQ1 : Q.ord t = 1 := by omega
  refine ⟨hQ1, fun W hW hWv hWQ => ?_⟩
  have hxW : x W = W.ord t := by rw [hxapp, if_pos hW, hD]
  by_contra h0
  have hWmem : W ∈ x.support := by rw [Finsupp.mem_support_iff, hxW]; exact h0
  have hgW : g W = W.ord t := by
    show (if P.redFst W = P.redFst Q then x W else 0) = W.ord t
    rw [if_pos hWv, hxW]
  have hpair : g Q + g W ≤ ∑ W ∈ x.support, g W := by
    rw [← Finset.sum_pair (Ne.symm hWQ)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hQmem
      · exact hWmem
    · intro y _ _
      exact hgnn y
  rw [hsum, hgQ, hgW, hQ1] at hpair
  have h2 := hnn W hW
  omega

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_ord_jFun_sub_eq_one_of_isStrictTypeOne
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_ord_jFun_sub_eq_one_of_isStrictTypeOne (solution)
