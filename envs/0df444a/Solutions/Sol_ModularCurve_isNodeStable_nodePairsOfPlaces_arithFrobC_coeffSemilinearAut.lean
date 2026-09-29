-- Prove2me | solution 1 for ModularCurve.isNodeStable_nodePairsOfPlaces_arithFrobC_coeffSemilinearAut
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/68b06735-acae-5c69-af75-14083e8d4875

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Theorems.Thm_ModularCurve_mem_ssJSet_map_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isNodeStable_nodePairsOfPlaces_arithFrobC_coeffSemilinearAut
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_isNodeStable_nodePairsOfPlaces_arithFrobC_coeffSemilinearAut.ModularCurve AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "smulNodePair nodePairsOfPlaces mem_nodePairsOfPlaces_iff ssPlaces jGeomGen jNGeomGen IsCentreOf exists_isCentreOf_of_isRational modularFunctionFieldC coeffSemilinearAut coeffSemilinearAut_smul_jq coeffSemilinearAut_smul_jqN arithFrobC coeffMap coeffMap_coeffMap coeffMap_congr mem_ssJSet_map_of_isAlgClosed"
p2m_open "ModularCurve"
namespace CoeffAutNodeStable

variable {K : Type*} [Field K] (N : ℕ) [NeZero N]

theorem smul_jGeomGen (τ : K ≃+* K) :
    coeffSemilinearAut N τ • jGeomGen K N = jGeomGen K N :=
  coeffSemilinearAut_smul_jq N τ

theorem smul_jNGeomGen (τ : K ≃+* K) :
    coeffSemilinearAut N τ • jNGeomGen K N = jNGeomGen K N :=
  coeffSemilinearAut_smul_jqN N τ

theorem isRational_smul {F : Type*} [Field F] [Algebra K F] (g : SemilinearAut K F)
    {w : Place K F} (hw : w.IsRational) : (g • w).IsRational := by
  intro y
  obtain ⟨a, ha⟩ := hw ((SemilinearAut.smulResidueRingEquiv g w).symm y)
  refine ⟨SemilinearAut.baseAut g a, ?_⟩
  rw [← SemilinearAut.smulResidueRingEquiv_algebraMap, ha, RingEquiv.apply_symm_apply]

theorem isCentreOf_smul (τ : K ≃+* K) {c : K × K} {w : Place K (modularFunctionFieldC K N)}
    (h : IsCentreOf K N c w) :
    IsCentreOf K N (τ c.1, τ c.2) (coeffSemilinearAut N τ • w) := by
  have key : ∀ (f : modularFunctionFieldC K N) (a : K),
      coeffSemilinearAut N τ • f = f →
      (coeffSemilinearAut N τ • w).ord (f - algebraMap K (modularFunctionFieldC K N) (τ a)) =
        w.ord (f - algebraMap K (modularFunctionFieldC K N) a) := by
    intro f a hf
    have hτ : τ a = SemilinearAut.baseAut (coeffSemilinearAut N τ) a := rfl
    rw [hτ, ← SemilinearAut.smul_algebraMap, ← SemilinearAut.ord_smul (coeffSemilinearAut N τ) w,
      smul_sub, hf]
  exact ⟨(key _ _ (smul_jGeomGen N τ)).symm ▸ h.1, (key _ _ (smul_jNGeomGen N τ)).symm ▸ h.2⟩

theorem smul_mem_ssPlaces (q : ℕ) [Fact q.Prime] [CharP K q] [IsAlgClosed K] [DecidableEq K]
    (τ : K ≃+* K) {w : Place K (modularFunctionFieldC K N)}
    (hw : w ∈ ssPlaces q N K) : coeffSemilinearAut N τ • w ∈ ssPlaces q N K := by
  obtain ⟨hrat, haff, hss⟩ := hw
  have hc := isCentreOf_smul N τ (exists_isCentreOf_of_isRational hrat haff)
  refine ⟨isRational_smul (coeffSemilinearAut N τ) hrat, hc.isAffineGeomPlace, ?_⟩
  rw [hc.evalAt_jGeomGen]
  exact mem_ssJSet_map_of_isAlgClosed (τ : K →+* K) _ hss

theorem smul_smul_comm_of_comm {τ τ' : K ≃+* K} (h : ∀ a, τ (τ' a) = τ' (τ a))
    (w : Place K (modularFunctionFieldC K N)) :
    coeffSemilinearAut N τ • (coeffSemilinearAut N τ' • w) =
      coeffSemilinearAut N τ' • (coeffSemilinearAut N τ • w) := by
  rw [← mul_smul, ← mul_smul]
  congr 1
  refine Subtype.ext (Prod.ext ?_ ?_)
  · refine RingEquiv.ext fun x => Subtype.ext ?_
    show coeffMap (τ : K →+* K) (coeffMap (τ' : K →+* K) (x : LaurentSeries K)) =
      coeffMap (τ' : K →+* K) (coeffMap (τ : K →+* K) (x : LaurentSeries K))
    rw [coeffMap_coeffMap, coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext fun a => h a) _
  · exact RingEquiv.ext fun a => h a

theorem smul_arithFrobC_smul (q : ℕ) [Fact q.Prime] [CharP K q] [PerfectField K]
    (τ : K ≃+* K) (w : Place K (modularFunctionFieldC K N)) :
    coeffSemilinearAut N τ • (arithFrobC q K N • w) =
      arithFrobC q K N • (coeffSemilinearAut N τ • w) :=
  smul_smul_comm_of_comm N (τ' := frobeniusEquiv K q) (fun a => by
    rw [frobeniusEquiv_apply, frobeniusEquiv_apply, frobenius_def, frobenius_def, map_pow]) w

end CoeffAutNodeStable
end ModularCurve

end

p2m_open "ModularCurve P2MW.S_ModularCurve_isNodeStable_nodePairsOfPlaces_arithFrobC_coeffSemilinearAut.ModularCurve AlgebraicCurve"

theorem solution
    (q N : ℕ) [NeZero N] [Fact q.Prime] (K : Type*) [Field K] [CharP K q] [IsAlgClosed K]
    [DecidableEq K] (W : Finset (Place K (modularFunctionFieldC K N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N K) (τ : K ≃+* K) :
    SemilinearAut.IsNodeStable (nodePairsOfPlaces (arithFrobC q K N) W)
      (coeffSemilinearAut N τ) := by
  intro s hs
  obtain ⟨w, hw, rfl⟩ := (mem_nodePairsOfPlaces_iff _ _ _).mp hs
  rw [mem_nodePairsOfPlaces_iff]
  refine ⟨coeffSemilinearAut N τ • w, ?_, ?_⟩
  · rw [hW] at hw ⊢
    exact CoeffAutNodeStable.smul_mem_ssPlaces N q τ hw
  · simp only [smulNodePair]
    rw [CoeffAutNodeStable.smul_arithFrobC_smul]

end S_ModularCurve_isNodeStable_nodePairsOfPlaces_arithFrobC_coeffSemilinearAut
end P2MW
export P2MW.S_ModularCurve_isNodeStable_nodePairsOfPlaces_arithFrobC_coeffSemilinearAut (solution)
