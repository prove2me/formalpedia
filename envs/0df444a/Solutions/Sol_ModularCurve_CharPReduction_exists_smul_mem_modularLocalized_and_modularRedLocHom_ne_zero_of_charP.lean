-- Prove2me | solution 1 for ModularCurve.CharPReduction.exists_smul_mem_modularLocalized_and_modularRedLocHom_ne_zero_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/9004c7fe-776d-5c1e-99ed-bce5fc7bb64e

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_CharPReduction
import Theorems.Thm_ModularCurve_coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized
import Theorems.Thm_ModularCurve_exists_regularProlongation_modularFunctionFieldBar_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPReduction_exists_smul_mem_modularLocalized_and_modularRedLocHom_ne_zero_of_charP
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

private noncomputable def hgcp_pack {A : ValuationSubring (AlgebraicClosure ℚ)}
    (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : x ∈ CharPReduction.integralCoeffs A.toSubring) :
    LaurentSeries A where
  coeff n := ⟨x.coeff n, hx n⟩
  isPWO_support' := x.isPWO_support.mono (fun _ hn h => hn (Subtype.ext h))

private theorem hgcp_coeffMap_pack {A : ValuationSubring (AlgebraicClosure ℚ)}
    (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : x ∈ CharPReduction.integralCoeffs A.toSubring) :
    coeffMap A.subtype (hgcp_pack x hx) = x := by
  ext n
  rfl

private theorem hgcp_coeffMap_subtype_injective (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Function.Injective (coeffMap A.subtype : LaurentSeries A → LaurentSeries (AlgebraicClosure ℚ)) := by
  intro x y h
  ext n
  have hn := congrArg (fun z : LaurentSeries (AlgebraicClosure ℚ) => z.coeff n) h
  simp only [coeffMap_coeff] at hn
  exact hn

private theorem hgcp_redRes_eq {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (r : CharPReduction.modularRing (1 * q) A.toSubring) :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) r =
      coeffMap red (hgcp_pack (r : LaurentSeries (AlgebraicClosure ℚ))
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring r.2)) := by
  ext n
  rfl

private theorem hgcp_coeffMap_red_ne_zero {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    (red : A →+* k) (y : LaurentSeries A) (hy : coeffMap (IsLocalRing.residue A) y ≠ 0) :
    coeffMap red y ≠ 0 := by
  intro h0
  apply hy
  ext n
  have hn : red (y.coeff n) = 0 := by
    have h := congrArg (fun z : LaurentSeries k => z.coeff n) h0
    simpa using h
  have hmem : y.coeff n ∈ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top red) (RingHom.mem_ker.mpr hn)
  simpa using (IsLocalRing.residue_eq_zero_iff (y.coeff n)).mpr hmem

private theorem hgcp_liesOverPrime {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) : A.LiesOverPrime (1 * q) := by
  have hq0 : red (q : A) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero k q
  show ((1 * q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
  rw [ValuationSubring.mem_nonunits_iff, one_mul]
  rcases A.valuation_lt_one_or_eq_one (q : A) with h | h
  · simpa using h
  · exfalso
    have hu : IsUnit (q : A) := (A.valuation_eq_one_iff (q : A)).mpr h
    have hu' := hu.map red
    rw [hq0] at hu'
    exact not_isUnit_zero hu'

private theorem hgcp_core {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k)
    {u v : LaurentSeries (AlgebraicClosure ℚ)} (huv : u * v = 1)
    {r s : CharPReduction.modularRing (1 * q) A.toSubring}
    (hus : u * (s : LaurentSeries (AlgebraicClosure ℚ)) = r)
    (hs : s ∉ CharPReduction.redKer A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring))
    (hr : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) r = 0)
    {x y : LaurentSeries A} (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (hvy : v * coeffMap A.subtype y = coeffMap A.subtype x) : False := by
  have hsne := CharPReduction.redRes_ne_zero_of_notMem hs
  rw [hgcp_redRes_eq] at hsne hr
  have hid : (s : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y =
      (r : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype x := by
    linear_combination (coeffMap A.subtype x) * hus + (u * (s : LaurentSeries (AlgebraicClosure ℚ))) * hvy
      - ((s : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y) * huv
  have hidA : hgcp_pack (s : LaurentSeries (AlgebraicClosure ℚ))
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring s.2) * y =
      hgcp_pack (r : LaurentSeries (AlgebraicClosure ℚ))
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring r.2) * x := by
    apply hgcp_coeffMap_subtype_injective A
    rw [map_mul, map_mul, hgcp_coeffMap_pack, hgcp_coeffMap_pack]
    exact hid
  have hred := congrArg (coeffMap red) hidA
  rw [map_mul, map_mul, hr, zero_mul] at hred
  exact mul_ne_zero hsne (hgcp_coeffMap_red_ne_zero red y hy) hred

private theorem hgcp_norm {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : AlgebraicCurve.RegularProlongation A F Fbar) (f : F) (hf : f ≠ 0)
    {P : F → Prop} (hP : ∀ g : F, g ∈ R.integers → P g) :
    ∃ c : L, c ≠ 0 ∧ ∃ g : F, g = c • f ∧ g * g⁻¹ = 1 ∧ P g ∧ P g⁻¹ := by
  obtain ⟨c, hcf, hres⟩ := R.exists_smul_mem f hf
  have hc : c ≠ 0 := R.smul_const_ne_zero hcf hres
  refine ⟨c, hc, c • f, rfl, mul_inv_cancel₀ (smul_ne_zero hc hf), hP _ hcf, hP _ ?_⟩
  obtain ⟨w, hw⟩ := (R.isUnit_of_residue_ne_zero hres).exists_right_inv
  have h1 : c • f * (w : F) = 1 := congrArg Subtype.val hw
  rw [← eq_inv_of_mul_eq_one_right h1]
  exact w.2

private theorem hgcp_coe_mul_inv {q : ℕ} (g : ↥(modularFunctionFieldBar (1 * q))) (h : g * g⁻¹ = 1) :
    (g : LaurentSeries (AlgebraicClosure ℚ)) *
      ((g⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = 1 := by
  exact_mod_cast h

private theorem hgcp_one_mul_prime (q : ℕ) [Fact q.Prime] : (1 * q).Prime := by
  rw [one_mul]
  exact Fact.out

private theorem hgcp_ne_zero_of_mem {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) {g ginv : LaurentSeries (AlgebraicClosure ℚ)} (hmul : g * ginv = 1)
    (h₁ : g ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    {x y : LaurentSeries A} (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (hvy : ginv * coeffMap A.subtype y = coeffMap A.subtype x) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨g, h₁⟩ ≠ 0 := by
  intro hπ
  obtain ⟨r, s, hs, hgs⟩ := id h₁
  have hspec := CharPReduction.redLoc_spec (⟨g, h₁⟩ : CharPReduction.modularLocalized (1 * q) A.toSubring red) hgs
  have hπ' : CharPReduction.redLoc (⟨g, h₁⟩ : CharPReduction.modularLocalized (1 * q) A.toSubring red) = 0 := hπ
  rw [hπ', zero_mul] at hspec
  exact hgcp_core red hmul hgs hs hspec.symm hy hvy

private theorem hgcp_exists_of_inv_mem {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) {g ginv : LaurentSeries (AlgebraicClosure ℚ)} (hmul : g * ginv = 1)
    (h₂ : ginv ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    {x y : LaurentSeries A} (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (hvy : g * coeffMap A.subtype y = coeffMap A.subtype x) :
    ∃ h₁ : g ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨g, h₁⟩ ≠ 0 := by
  obtain ⟨r, s, hs, hgs⟩ := h₂
  have hmul' : ginv * g = 1 := by rw [mul_comm]; exact hmul
  by_cases hr : r ∈ CharPReduction.redKer A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
  · exact (hgcp_core red hmul' hgs hs (RingHom.mem_ker.mp hr) hy hvy).elim
  · have hgr : g * (r : LaurentSeries (AlgebraicClosure ℚ)) = s := by
      linear_combination (-g) * hgs + (s : LaurentSeries (AlgebraicClosure ℚ)) * hmul
    have h₁ : g ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
      (CharPReduction.mem_localizedAtKer A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)).mpr ⟨s, r, hr, hgr⟩
    refine ⟨h₁, fun hπ => ?_⟩
    have hspec := CharPReduction.redLoc_spec (⟨g, h₁⟩ : CharPReduction.modularLocalized (1 * q) A.toSubring red) hgr
    have hπ' : CharPReduction.redLoc (⟨g, h₁⟩ : CharPReduction.modularLocalized (1 * q) A.toSubring red) = 0 := hπ
    rw [hπ', zero_mul] at hspec
    exact CharPReduction.redRes_ne_zero_of_notMem hs hspec.symm

private theorem hgcp_of_normalised {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (g : ↥(modularFunctionFieldBar (1 * q))) (hgg : g * g⁻¹ = 1)
    {x₁ y₁ x₂ y₂ : LaurentSeries A}
    (hy₁ : coeffMap (IsLocalRing.residue A) y₁ ≠ 0)
    (hvy₁ : (g : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y₁ = coeffMap A.subtype x₁)
    (hy₂ : coeffMap (IsLocalRing.residue A) y₂ ≠ 0)
    (hvy₂ : ((g⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y₂ =
      coeffMap A.subtype x₂) :
    ∃ h₁ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0 := by
  have hmul := hgcp_coe_mul_inv g hgg
  rcases ModularCurve.coe_mem_modularLocalized_or_coe_inv_mem_modularLocalized red g with h₁ | h₂
  · exact ⟨h₁, hgcp_ne_zero_of_mem red hmul h₁ hy₂ hvy₂⟩
  · exact hgcp_exists_of_inv_mem red hmul h₂ hy₁ hvy₁

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0) :
    ∃ (c : AlgebraicClosure ℚ) (_ : c ≠ 0)
      (h₁ : ((c • f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red),
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0 := by
  obtain ⟨R, hR₁, -⟩ :=
    ModularCurve.exists_regularProlongation_modularFunctionFieldBar_self (1 * q) (hgcp_one_mul_prime q) A
      (hgcp_liesOverPrime red)
  obtain ⟨c, hc, g, hg, hgg, ⟨x₁, y₁, hy₁, hvy₁⟩, ⟨x₂, y₂, hy₂, hvy₂⟩⟩ :=
    hgcp_norm R f hf (fun g hg => (hR₁ g).mp hg)
  subst hg
  exact ⟨c, hc, hgcp_of_normalised red _ hgg hy₁ hvy₁ hy₂ hvy₂⟩

end S_ModularCurve_CharPReduction_exists_smul_mem_modularLocalized_and_modularRedLocHom_ne_zero_of_charP
end P2MW
export P2MW.S_ModularCurve_CharPReduction_exists_smul_mem_modularLocalized_and_modularRedLocHom_ne_zero_of_charP (solution)
