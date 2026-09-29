-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.exists_yDepth_eq_pow_of_forall_inertia_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/1ab243fc-0aef-5b99-81ec-cad0a6ae6567

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver
import Theorems.Thm_ValuationSubring_exists_dvr_subring_of_forall_mem_inertiaSubgroupIn
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_exists_yDepth_eq_pow_of_forall_inertia_smul_eq
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_exists_yDepth_eq_pow_of_forall_inertia_smul_eq.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "arithmeticGalois modularFunctionFieldBar ModularPolynomialData modularFunctionFieldFull modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence NodeLocalized.coeffSubring arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple reduceFst"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

theorem natCast_mem_nonunits_of_ringHom_charP {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) :
    ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff]
  have hmem : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
  have hle : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr hmem
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    have hu : IsUnit ((⟨((q : ℕ) : AlgebraicClosure ℚ), hmem⟩ : A)) := (A.valuation_eq_one_iff _).mpr h
    have h2 := hu.map red
    have h3 : red ⟨((q : ℕ) : AlgebraicClosure ℚ), hmem⟩ = ((q : ℕ) : k) := by
      rw [← map_natCast red q]
      congr 1
    rw [h3, CharP.cast_eq_zero k q] at h2
    exact not_isUnit_zero h2

theorem exists_valuation_eq_pow_of_forall_mem_inertiaSubgroupIn
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    {z : AlgebraicClosure ℚ} (hzA : z ∈ A) (hz0 : z ≠ 0)
    (hzfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ z = z) :
    ∃ d : ℕ, A.valuation z = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ d := by
  classical
  obtain ⟨O, hSO, hOA, -, hDVR, hirr, -⟩ :=
    ValuationSubring.exists_dvr_subring_of_forall_mem_inertiaSubgroupIn q A hA {z}
      (fun x hx => by
        rw [Finset.mem_singleton] at hx
        subst hx
        exact ⟨hzA, fun σ hσ => hzfix σ hσ⟩)
  have hzO : z ∈ O := hSO (by simp)
  haveI : IsDiscreteValuationRing O := hDVR
  have hz0' : (⟨z, hzO⟩ : O) ≠ 0 := fun h => hz0 (congrArg Subtype.val h)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hz0' hirr

  refine ⟨n, ?_⟩
  have hvu : A.valuation (((u : O) : O) : AlgebraicClosure ℚ) = 1 := by
    apply le_antisymm
    · exact (A.valuation_le_one_iff _).mpr (hOA (u : O).2)
    · have h1 : A.valuation (((u⁻¹ : Oˣ) : O) : AlgebraicClosure ℚ) ≤ 1 :=
        (A.valuation_le_one_iff _).mpr (hOA ((u⁻¹ : Oˣ) : O).2)
      have hmul : (((u : O) : AlgebraicClosure ℚ)) * (((u⁻¹ : Oˣ) : O) : AlgebraicClosure ℚ) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
      have h2 : A.valuation (((u : O) : AlgebraicClosure ℚ)) * A.valuation (((u⁻¹ : Oˣ) : O) : AlgebraicClosure ℚ) = 1 := by
        rw [← map_mul, hmul, map_one]
      by_contra hlt
      push_neg at hlt
      have := mul_lt_one_of_lt_of_le hlt h1
      exact absurd h2 this.ne
  have h := congrArg (fun t : O => A.valuation (t : AlgebraicClosure ℚ)) hu
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, hvu, mul_one] at h

  convert h using 2
  rfl

end ModularCurve.PlaceSpecialization

p2m_open "ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_exists_yDepth_eq_pow_of_forall_inertia_smul_eq.ModularCurve.PlaceSpecialization"

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} {R : ProlongationTuple P}
    {K : IntermediateField ℚ (AlgebraicClosure ℚ)} {w : Place k (modularFunctionFieldC k N)}
    (c : R.NodeCoordinates K w) (hVI : R.ValueIntegralityLaw w)
    (hK : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K, σ z = z)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : (ϖ : AlgebraicClosure ℚ) ≠ 0)
    (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w)
    (hVrat : V.IsRational)
    (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) :
    ∃ d : ℕ, c.yDepth V = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ d := by
  classical

  set yF : ↥(modularFunctionFieldBar (N * q)) := ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
    with hyF
  have hyO : yF ∈ R.nodeIntegersOver K w := (c.y : ↥(R.nodeIntegersOver K w)).2
  have hyN : yF ∈ R.nodeIntegers w := hyO.1
  have hyV : yF ∈ V.toValuationSubring := R.mem_toValuationSubring_of_mem_nodeIntegers hyN hV

  have hzA : V.evalAt yF ∈ A := hVI yF hyN V hV
  have hzfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (V.evalAt yF) = V.evalAt yF := by
    intro σ hσ
    have h := (ModularCurve.arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver (N * q) K σ
      (hK σ hσ) yF hyO.2).2 V hVrat
    rw [hfix σ hσ] at h
    exact h.symm

  set xF : ↥(modularFunctionFieldBar (N * q)) := ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
    with hxF
  have hxN : xF ∈ R.nodeIntegers w := (c.x : ↥(R.nodeIntegersOver K w)).2.1
  have hxV : xF ∈ V.toValuationSubring := R.mem_toValuationSubring_of_mem_nodeIntegers hxN hV
  obtain ⟨uu, rfl⟩ := hu
  set uF : ↥(modularFunctionFieldBar (N * q)) := ((uu : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
    with huF
  have huV : uF ∈ V.toValuationSubring :=
    R.mem_toValuationSubring_of_mem_nodeIntegers ((uu : ↥(R.nodeIntegersOver K w)).2.1) hV
  have huinvV : (((uu⁻¹ : (↥(R.nodeIntegersOver K w))ˣ) : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
      ∈ V.toValuationSubring :=
    R.mem_toValuationSubring_of_mem_nodeIntegers (((uu⁻¹ : (↥(R.nodeIntegersOver K w))ˣ) : ↥(R.nodeIntegersOver K w)).2.1) hV

  have huunit : IsUnit (⟨uF, huV⟩ : V.toValuationSubring) := by
    refine ⟨⟨⟨uF, huV⟩, ⟨_, huinvV⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      show uF * _ = 1
      rw [huF, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
    · apply Subtype.ext
      show (((uu⁻¹ : (↥(R.nodeIntegersOver K w))ˣ) : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) * uF = 1
      rw [huF, ← Subring.coe_mul, Units.inv_mul, Subring.coe_one]
  have horduF : V.ord uF = 0 := by
    obtain ⟨uV, huV'⟩ := huunit
    have := V.ord_coe_unit uV
    rw [huV'] at this
    exact this
  have hconst : ((R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ) := rfl
  have hxyF : xF * yF = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((ϖ : AlgebraicClosure ℚ) ^ E) * uF := by
    have h := congrArg (fun t : ↥(R.nodeIntegersOver K w) => (t : ↥(modularFunctionFieldBar (N * q)))) hxy
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow] at h
    rw [hxF, hyF, huF, h, hconst, map_pow]
  have hcE0 : ((ϖ : AlgebraicClosure ℚ) ^ E) ≠ 0 := pow_ne_zero _ hϖ0
  have huF0 : uF ≠ 0 := by
    intro h0
    have h1 : (⟨uF, huV⟩ : V.toValuationSubring) = 0 := Subtype.ext h0
    rw [h1] at huunit
    exact not_isUnit_zero huunit
  have hrhs0 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((ϖ : AlgebraicClosure ℚ) ^ E) * uF ≠ 0 :=
    mul_ne_zero ((map_ne_zero _).mpr hcE0) huF0
  have hx0 : xF ≠ 0 := fun h => hrhs0 (by rw [← hxyF, h, zero_mul])
  have hy0 : yF ≠ 0 := fun h => hrhs0 (by rw [← hxyF, h, mul_zero])
  have hord : V.ord xF + V.ord yF = 0 := by
    rw [← V.ord_mul hx0 hy0, hxyF, V.ord_mul ((map_ne_zero _).mpr hcE0) huF0, V.ord_algebraMap, horduF, add_zero]
  have hordy : V.ord yF = 0 := by
    have h1 := V.ord_nonneg_of_mem hxV
    have h2 := V.ord_nonneg_of_mem hyV
    omega
  have hz0 : V.evalAt yF ≠ 0 := V.evalAt_ne_zero hVrat hy0 hordy

  obtain ⟨d, hd⟩ := exists_valuation_eq_pow_of_forall_mem_inertiaSubgroupIn
    (natCast_mem_nonunits_of_ringHom_charP red) hzA hz0 hzfix
  exact ⟨d, hd⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_exists_yDepth_eq_pow_of_forall_inertia_smul_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_exists_yDepth_eq_pow_of_forall_inertia_smul_eq (solution)
