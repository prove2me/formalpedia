-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_isMaximal_chartAlgFin_mem_ssJSet_over_of_ssPlaces_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/b09e7f0d-260d-508a-8cc7-c2c656574794

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_isMaximal_chartAlgFin_over_of_ssPlaces_of_eq_two_of_dvd
import Theorems.Thm_ModularCurve_ssJSet_eq_image_algebraMap_of_isAlgClosed
import Theorems.Thm_ModularCurve_mem_ssJSet_map_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_isMaximal_chartAlgFin_mem_ssJSet_over_of_ssPlaces_of_eq_two_of_dvd
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply"
p2m_attr_erase "simp" "ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]

    (hjK : (coeffEmb ↥k₀ jq) ∈ K)
    (hjC : (⟨_, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) :
    ∃ y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
      y.IsMaximal ∧

      algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨π₀, hπ⟩ ∈ y ∧

      (∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
        (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) →+* Ω), RingHom.ker φ = y →
          φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ∈ ModularCurve.ssJSet q Ω) ∧

      (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
            ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        ∀ (hgK : (coeffEmb ↥k₀ g) ∈ K)
          (hgC : (⟨_, hgK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
        ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
          residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
          (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) -
              algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨c, hc⟩ ∈ y) := by
  classical
  obtain ⟨y, hymax, hπy, hover⟩ :=
    ModularCurve.FullLevel.Diamond.exists_isMaximal_chartAlgFin_over_of_ssPlaces_of_eq_two_of_dvd q hq2 M' hqM' ℓg hℓg hℓg12 hℓgM' A hA W hW hle R₀ hR₀ s k₀ π₀ hπ hdvr
      hunif hhens hres hκ H₁ hH₁ K hK j hj hjK hjC
  refine ⟨y, hymax, hπy, ?_, hover⟩

  have hqp : q.Prime := Fact.out
  haveI hκac : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI hκch : CharP (ResidueField ↥A) q := by
    have hq' : ((q : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by norm_cast
    have hmem : (q : ↥A) ∈ maximalIdeal ↥A := by
      rw [← ValuationSubring.coe_mem_nonunits_iff, hq']; exact hA
    have h0 : ((q : ℕ) : ResidueField ↥A) = 0 := by
      rw [← map_natCast (IsLocalRing.residue ↥A), IsLocalRing.residue_eq_zero_iff]; exact hmem
    exact (CharP.charP_iff_prime_eq_zero hqp).mpr h0

  have hmapA : coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq := by
    change (jqModC ↥A).map A.subtype = (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ))
    rw [map_jqModC, map_jqModC]
  have hjqBar : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
    rw [hmapA]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
  obtain ⟨hjint, hjres⟩ := hR₀ (jqModC ↥A) hjqBar
  have helt : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) =
        ⟨coeffMap A.subtype (jqModC ↥A), hjqBar⟩ := Subtype.ext hmapA.symm
  have hgi : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈
        R₀.integers := by rw [helt]; exact hjint
  have hresj : R₀.residue ⟨_, hgi⟩ = jGeomGen (ResidueField ↥A) M' := by
    have h1 : (⟨_, hgi⟩ : ↥R₀.integers) = ⟨_, hjint⟩ := Subtype.ext helt
    rw [h1]
    apply Subtype.ext
    rw [hjres, coe_jGeomGen]
    change (jqModC ↥A).map (IsLocalRing.residue ↥A) = jqModC (ResidueField ↥A)
    exact map_jqModC _

  have hss_s : IsSupersingularPlace q M' (ResidueField ↥A) (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) :=
    (hW _).mp s.2
  have hreg : (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring := by
    rw [hresj]; exact hss_s.2.1.1
  set jval := (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField ↥A) M') with hjval
  have hjval : jval ∈ ssJSet q (ResidueField ↥A) := hss_s.2.2

  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective jval
  obtain ⟨c, hcA, hsub, hm⟩ := hκ (a : AlgebraicClosure ℚ) a.2
  have hcval : residue ↥A ⟨(c : AlgebraicClosure ℚ), hcA⟩ =
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) := by
    rw [hresj]
    show residue ↥A ⟨(c : AlgebraicClosure ℚ), hcA⟩ = jval
    rw [← ha]
    have h1 : a - ⟨(c : AlgebraicClosure ℚ), hcA⟩ = ⟨(a : AlgebraicClosure ℚ) - c, hsub⟩ := Subtype.ext rfl
    have h0 : residue ↥A (a - ⟨(c : AlgebraicClosure ℚ), hcA⟩) = 0 := by
      rw [h1]; exact (IsLocalRing.residue_eq_zero_iff _).mpr hm
    rw [map_sub, sub_eq_zero] at h0
    exact h0.symm

  have hdiff := hover jq (modularFunctionField_le_full M' (jq_mem M')) hgi (fun P h => h) hreg hjK hjC c hcA hcval

  intro Ω _ _ _ _ φ hker
  have hφπ : φ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨π₀, hπ⟩) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact hπy
  have hkill : ∀ x ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), (φ.comp (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j))) x = 0 := by
    intro x hx
    rw [hunif, Ideal.mem_span_singleton] at hx
    obtain ⟨d, rfl⟩ := hx
    rw [RingHom.comp_apply, map_mul, map_mul, hφπ, zero_mul]
  let ι₀ : ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+* Ω := Ideal.Quotient.lift _ (φ.comp (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j))) hkill
  have hι₀ : ∀ x : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ι₀ (residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) x) = φ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) x) := fun x => rfl
  have hφsharp : φ (⟨⟨_, hjK⟩, hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) = ι₀ (residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⟨c, hcA⟩) := by
    rw [hι₀, ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hker]
    exact hdiff

  haveI : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := hres
  let incl : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+* ↥A :=
    { toFun := fun x => ⟨((x : ↥k₀) : AlgebraicClosure ℚ), x.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  haveI hloc : IsLocalHom incl := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hx
    have hb' : ((x : ↥k₀) : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ) = 1 := by
      have := congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) hb
      have h__ := this
      try simp at h__
      try simp
      exact h__
    have hx0 : ((x : ↥k₀) : AlgebraicClosure ℚ) ≠ 0 := by
      intro h; rw [h, zero_mul] at hb'; exact zero_ne_one hb'
    have hbeq : (b : AlgebraicClosure ℚ) = ((x : ↥k₀) : AlgebraicClosure ℚ)⁻¹ := eq_inv_of_mul_eq_one_right hb'
    have hbk : ((x : ↥k₀)⁻¹ : ↥k₀) ∈ A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) := by
      rw [ValuationSubring.mem_comap]
      change (((x : ↥k₀)⁻¹ : ↥k₀) : AlgebraicClosure ℚ) ∈ A
      push_cast
      rw [← hbeq]; exact b.2
    refine isUnit_iff_exists_inv.mpr ⟨⟨(x : ↥k₀)⁻¹, hbk⟩, ?_⟩
    apply Subtype.ext
    change (x : ↥k₀) * (x : ↥k₀)⁻¹ = 1
    exact mul_inv_cancel₀ (fun h => hx0 (by rw [h]; simp))
  have hchar0 : CharP (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) q := by
    have : (q : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hu' := hu.map incl
      have : incl (q : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) = (q : ↥A) := map_natCast incl q
      rw [this] at hu'
      have hmem : (q : ↥A) ∈ maximalIdeal ↥A := by
        have hq' : ((q : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by norm_cast
        rw [← ValuationSubring.coe_mem_nonunits_iff, hq']; exact hA
      exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu'
    have h0 : ((q : ℕ) : ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) = 0 := by
      rw [← map_natCast (IsLocalRing.residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))), IsLocalRing.residue_eq_zero_iff]; exact this
    exact (CharP.charP_iff_prime_eq_zero hqp).mpr h0
  haveI := hchar0
  let e : ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+* ResidueField ↥A := IsLocalRing.ResidueField.map incl
  have he : e (residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⟨c, hcA⟩) = residue ↥A ⟨(c : AlgebraicClosure ℚ), hcA⟩ := rfl
  letI : Algebra (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ResidueField ↥A) := e.toAlgebra
  have himg := ModularCurve.ssJSet_eq_image_algebraMap_of_isAlgClosed q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ResidueField ↥A)
  have hjval' : jval ∈ @ssJSet q (ResidueField ↥A) _ (Classical.decEq _) := by
    convert hjval using 2
    all_goals try rfl
  rw [himg] at hjval'
  obtain ⟨x₀, hx₀, hx₀e⟩ := hjval'
  have hx₀eq : x₀ = residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⟨c, hcA⟩ := by
    apply e.injective
    change algebraMap (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ResidueField ↥A) x₀ = _
    rw [hx₀e, he, hcval, hresj]
  have hc_ss : residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⟨c, hcA⟩ ∈ @ssJSet q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) _ (Classical.decEq _) := hx₀eq ▸ hx₀
  have hφsharp_ss : φ (⟨⟨_, hjK⟩, hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) ∈ ssJSet q Ω := by
    rw [hφsharp]
    exact @ModularCurve.mem_ssJSet_map_of_isAlgClosed q _ _ _ _ _ _ _ _ (Classical.decEq _) _ ι₀ _ hc_ss

  let u : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) →+* LaurentSeries ↥k₀ :=
    (K.toSubalgebra.val.toRingHom).comp (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j).val.toRingHom
  have hu : Function.Injective u := by
    intro a b h
    apply Subtype.ext; apply Subtype.ext; exact h
  have huj : u (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) = coeffEmb ↥k₀ jq := hj
  have husharp : u (⟨⟨_, hjK⟩, hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) = coeffEmb ↥k₀ jq := rfl
  have hjj : AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j =
      (⟨⟨_, hjK⟩, hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) :=
    hu (huj.trans husharp.symm)
  rw [hjj]
  exact hφsharp_ss

end S_ModularCurve_FullLevel_Diamond_exists_isMaximal_chartAlgFin_mem_ssJSet_over_of_ssPlaces_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_isMaximal_chartAlgFin_mem_ssJSet_over_of_ssPlaces_of_eq_two_of_dvd (solution)
