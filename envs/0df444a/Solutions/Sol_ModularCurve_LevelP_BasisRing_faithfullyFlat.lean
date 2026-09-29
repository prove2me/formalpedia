-- Prove2me | solution 1 for ModularCurve.LevelP.BasisRing.faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/978f02cc-2a90-5e16-99e3-a97865af6a01

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Theorems.Thm_ModularCurve_LevelP_TorsionPointRing_free_and_finrank_eq
import Theorems.Thm_ModularCurve_LevelP_BasisRing_exists_ringHom_basisData_map_eq
import Theorems.Thm_ModularCurve_exists_isLevelPStructure_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelP_BasisRing_faithfullyFlat
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u v w

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "LevelP.BasisRing exists_isLevelPStructure_of_isAlgClosed"
p2m_open "ModularCurve"

open WeierstrassCurve

theorem faithfullyFlat_of_exists_ringHom_field {B : Type u} {S : Type v} [CommRing B]
    [CommRing S] [Algebra B S] [Module.Flat B S]
    (h : ∀ m : Ideal B, m.IsMaximal →
      ∃ (K : Type w) (_ : Field K) (ψ : S →+* K), m ≤ RingHom.ker (ψ.comp (algebraMap B S))) :
    Module.FaithfullyFlat B S := by
  rw [Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top]
  refine ⟨inferInstance, fun I hI => ?_⟩
  by_contra hne
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
  obtain ⟨K, _, ψ, hker⟩ := h m hm
  have h1 : (1 : S) ∈ Ideal.map (algebraMap B S) m := by
    have hle : I • (⊤ : Submodule B S) ≤ m • ⊤ := Submodule.smul_mono_left hIm
    rw [hI, top_le_iff, Ideal.smul_top_eq_map] at hle
    have h := (hle ▸ Submodule.mem_top : (1 : S) ∈ (Ideal.map (algebraMap B S) m).restrictScalars B)
    exact h
  have h2 : ψ 1 ∈ Ideal.map ψ (Ideal.map (algebraMap B S) m) := Ideal.mem_map_of_mem ψ h1
  rw [Ideal.map_map, map_one] at h2
  have h3 : Ideal.map (ψ.comp (algebraMap B S)) m = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker]; exact hker
  rw [h3] at h2
  exact one_ne_zero ((Submodule.mem_bot K).mp h2)

namespace LevelP
p2m_export "ModularCurve.LevelP" "TorsionPointRing TorsionPointRing.ofBase torsionPtCurve TwoPointRing indepDenom BasisRing BasisRing.algebraMap_eq TorsionPointRing.free_and_finrank_eq BasisRing.exists_ringHom_basisData_map_eq"
p2m_open "ModularCurve.LevelP"

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) {p : ℕ}

theorem one_lt_of_odd_of_ne_one (hp : Odd p) (hp1 : p ≠ 1) : 1 < p := by
  rcases hp with ⟨k, rfl⟩
  omega

namespace TorsionPointRing p2m_export "ModularCurve.LevelP.TorsionPointRing" "ofBase algebraMap_eq free_and_finrank_eq" end TorsionPointRing
p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in
theorem TorsionPointRing.nontrivial [Nontrivial B] (hp : Odd p) (hp1 : p ≠ 1)
    (hpu : IsUnit (p : B)) : Nontrivial (TorsionPointRing W p) :=
  Module.nontrivial_of_finrank_pos (R := B) (by
    rw [(TorsionPointRing.free_and_finrank_eq W hp hp1 hpu).2]
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow two_ne_zero (one_lt_of_odd_of_ne_one hp hp1)))

namespace TorsionPointRing
p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in
private theorem _root_.ModularCurve.LevelP.TorsionPointRing.flat (hp : Odd p) (hp1 : p ≠ 1) (hpu : IsUnit (p : B)) :
    Module.Flat B (TorsionPointRing W p) := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · haveI : Module.Free B (TorsionPointRing W p) := Module.Free.of_subsingleton' B _
    infer_instance
  · haveI := (TorsionPointRing.free_and_finrank_eq W hp hp1 hpu).1
    infer_instance

end TorsionPointRing
p2m_export "ModularCurve.LevelP" "TorsionPointRing.flat"
theorem isUnit_natCast_torsionPointRing (hpu : IsUnit (p : B)) :
    IsUnit (p : TorsionPointRing W p) := by
  simpa using hpu.map (TorsionPointRing.ofBase W p)

namespace TwoPointRing p2m_export "ModularCurve.LevelP.TwoPointRing" "ofBase algebraMap_eq" end TwoPointRing
namespace TwoPointRing
p2m_open_scoped "ModularCurve.LevelP.TwoPointRing" in
variable (p) in
private theorem _root_.ModularCurve.LevelP.TwoPointRing.flat (hp : Odd p) (hp1 : p ≠ 1) (hpu : IsUnit (p : B)) :
    Module.Flat B (TwoPointRing W p) := by
  haveI := TorsionPointRing.flat W hp hp1 hpu
  haveI : Module.Flat (TorsionPointRing W p) (TwoPointRing W p) :=
    TorsionPointRing.flat (torsionPtCurve W p) hp hp1 (isUnit_natCast_torsionPointRing W hpu)
  exact Module.Flat.trans B (TorsionPointRing W p) (TwoPointRing W p)

end TwoPointRing
p2m_export "ModularCurve.LevelP" "TwoPointRing.flat"
namespace BasisRing p2m_export "ModularCurve.LevelP.BasisRing" "ofBase algebraMap_eq exists_ringHom_basisData_map_eq" end BasisRing
p2m_open_scoped "ModularCurve.LevelP.BasisRing" in
variable (p) in

theorem BasisRing.flat' (hp : Odd p) (hp1 : p ≠ 1) (hpu : IsUnit (p : B)) :
    Module.Flat B (BasisRing W p) := by
  haveI := TwoPointRing.flat W p hp hp1 hpu
  haveI : Module.Flat (TwoPointRing W p) (BasisRing W p) :=
    IsLocalization.flat (BasisRing W p) (Submonoid.powers (indepDenom W p))
  exact Module.Flat.trans B (TwoPointRing W p) (BasisRing W p)

p2m_open_scoped "ModularCurve.LevelP.BasisRing" in
variable (p) in

theorem BasisRing.faithfullyFlat' [Fact p.Prime] (hp2 : p ≠ 2) (hpu : IsUnit (p : B))
    (hW : IsUnit W.Δ) : Module.FaithfullyFlat B (BasisRing W p) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  haveI := BasisRing.flat' W p hodd hp1 hpu
  refine faithfullyFlat_of_exists_ringHom_field.{u, u, u} (fun m hm => ?_)
  haveI := hm.isPrime
  let K := AlgebraicClosure m.ResidueField
  let φ : B →+* K := (algebraMap m.ResidueField K).comp (algebraMap B m.ResidueField)
  have hφm : ∀ b ∈ m, φ b = 0 := fun b hb => by
    simp only [φ, RingHom.comp_apply, Ideal.algebraMap_residueField_eq_zero.mpr hb, map_zero]
  have hΔ : (W.map φ).Δ ≠ 0 := by rw [WeierstrassCurve.map_Δ]; exact (hW.map φ).ne_zero
  have hpK : (p : K) ≠ 0 := by simpa using (hpu.map φ).ne_zero
  obtain ⟨D, hD⟩ := exists_isLevelPStructure_of_isAlgClosed (W.map φ) hp2 hpK hΔ
  obtain ⟨ψ, hψ, -⟩ := BasisRing.exists_ringHom_basisData_map_eq W p φ D hD
  refine ⟨K, inferInstance, ψ, fun b hb => ?_⟩
  rw [RingHom.mem_ker, BasisRing.algebraMap_eq, hψ]
  exact hφm b hb

end LevelP

end ModularCurve

end

theorem solution
    {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hpu : IsUnit (p : B)) (hW : IsUnit W.Δ) :
    Module.FaithfullyFlat B (ModularCurve.LevelP.BasisRing W p) :=
  ModularCurve.LevelP.BasisRing.faithfullyFlat' W p hp2 hpu hW

end S_ModularCurve_LevelP_BasisRing_faithfullyFlat
end P2MW
export P2MW.S_ModularCurve_LevelP_BasisRing_faithfullyFlat (solution)
