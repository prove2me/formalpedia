-- Prove2me | solution 1 for ModularCurve.FullLevel.mem_ssJSet_of_forall_mem_maximalIdeal_drinfeldRing_mem_chartAlgFin_descent_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/f76a1e9f-1bc5-5fdc-9a93-403afb6510d8

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_FullLevel_exists_jInvariant_sub_mem_maximalIdeal_drinfeldRing_descent_of_eq_three
import Theorems.Thm_ModularCurve_mem_ssJSet_map_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_mem_ssJSet_of_forall_mem_maximalIdeal_drinfeldRing_mem_chartAlgFin_descent_of_eq_three
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

noncomputable section

namespace SSConvDrinfeldCentre

open IsLocalRing ModularCurve

theorem charP_residueField (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime q) : CharP (ResidueField ↥A) q := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr
  have h1 : ((q : ↥A) : AlgebraicClosure ℚ) ∈ A.nonunits := by push_cast; exact hA
  have h2 : (q : ↥A) ∈ maximalIdeal ↥A := ValuationSubring.coe_mem_nonunits_iff.mp h1
  have h3 := (IsLocalRing.residue_eq_zero_iff _).mpr h2
  rwa [map_natCast] at h3

theorem mem_maximalIdeal_of_algebraMap_mem_maximalIdeal
    {L F : Type*} [Field L] [Field F] [Algebra L F]
    (A : ValuationSubring L) (O : ValuationSubring F)
    (hO : ∀ x : L, algebraMap L F x ∈ O ↔ x ∈ A)
    (x : ↥A) (h : ∃ hx : algebraMap L F (x : L) ∈ O, (⟨_, hx⟩ : ↥O) ∈ maximalIdeal ↥O) :
    x ∈ maximalIdeal ↥A := by
  obtain ⟨hx, hmax⟩ := h
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  have hyO : algebraMap L F (y : L) ∈ O := (hO _).mpr y.2
  apply (IsLocalRing.mem_maximalIdeal _).mp hmax
  refine IsUnit.of_mul_eq_one ⟨_, hyO⟩ (Subtype.ext ?_)
  change algebraMap L F (x : L) * algebraMap L F (y : L) = 1
  rw [← map_mul]
  have : (x : L) * (y : L) = ((x * y : ↥A) : L) := rfl
  rw [this, hy]
  simp

theorem exists_ringHom_residueField_comp_eq
    {A : Type*} [CommRing A] [IsLocalRing A]
    {A₀ : Type} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι : A₀ →+* A) [IsLocalHom ι]
    (hres : Function.Surjective ((IsLocalRing.residue A).comp ι))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    {Ω : Type*} [Field Ω] (ψ : A₀ →+* Ω) (hψ : ψ ϖ₀ = 0) :
    ∃ θ : ResidueField A →+* Ω, ∀ b : A₀, θ (IsLocalRing.residue A (ι b)) = ψ b := by

  haveI : IsLocalHom ψ := by
    refine ⟨fun b hb => ?_⟩
    by_contra hnu
    have hbmem : b ∈ maximalIdeal A₀ := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [hϖ₀, Ideal.mem_span_singleton'] at hbmem
    obtain ⟨c, rfl⟩ := hbmem
    rw [map_mul, hψ, mul_zero] at hb
    exact not_isUnit_zero hb

  let ρ : ResidueField A₀ →+* ResidueField A := ResidueField.map ι
  have hρ : Function.Bijective ρ := by
    refine ⟨ρ.injective, fun y => ?_⟩
    obtain ⟨b, hb⟩ := hres y
    exact ⟨IsLocalRing.residue A₀ b, by rw [← hb]; rfl⟩
  let e : ResidueField A₀ ≃+* ResidueField A := RingEquiv.ofBijective ρ hρ
  refine ⟨(ResidueField.lift ψ).comp e.symm.toRingHom, fun b => ?_⟩
  have h1 : e (IsLocalRing.residue A₀ b) = IsLocalRing.residue A (ι b) := rfl
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ← h1, RingEquiv.symm_apply_apply,
    ResidueField.lift_residue_apply]

end SSConvDrinfeldCentre

end

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option linter.unusedVariables false in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))

    (K₀ : Subfield (AlgebraicClosure ℚ)) [Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ)] (hπK₀ : π ∈ K₀)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) =
      (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)))
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})

    (hϖ₀π : ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π)

    (F₀ : Subfield ↥(fieldBar q M'))
    (hF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K₀)

    (hjF₀ : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)

    [Algebra A₀ ↥F₀]
    (hj₀ : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ))
    [Fact ((⟨_, hjF₀⟩ : ↥F₀) ≠ 0)]
    (𝔫 : Ideal ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (h𝔫 : 𝔫.IsMaximal)
    (hϖ : algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∈ 𝔫)
    (s : ↥W)
    (hs : ∀ g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
      (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) → g ∈ 𝔫)
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (φ : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) →+* Ω) (hφ : RingHom.ker φ = 𝔫) :
    φ (TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ∈ ModularCurve.ssJSet q Ω := by
  classical

  haveI hκclosed : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI hκchar : CharP (ResidueField ↥A) q := SSConvDrinfeldCentre.charP_residueField q A hA

  obtain ⟨a, haO, ham⟩ :=
    ModularCurve.FullLevel.exists_jInvariant_sub_mem_maximalIdeal_drinfeldRing_descent_of_eq_three q hq3 M' hqM' A hA W hW hle R₀
      hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀
      hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀ s

  have hcoeC : ((TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) a : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) : ↥F₀) =
      (⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥F₀ a := by
    rw [Subalgebra.coe_sub, TwoChartIntegralModel.coe_jChartFin, Subalgebra.coe_algebraMap]
  have hker : TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) a ∈ 𝔫 := by
    apply hs
    rw [hcoeC]
    exact ⟨haO, ham⟩
  have hφj : φ (TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) = φ (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) a) := by
    have h1 : φ (TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) a) = 0 := by
      rw [← RingHom.mem_ker, hφ]; exact hker
    rwa [RingHom.map_sub, sub_eq_zero] at h1

  have hymap : coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq := by
    change (jqModC ↥A).map A.subtype = (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ))
    rw [map_jqModC, map_jqModC]
  have hymem : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
    rw [hymap]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
  obtain ⟨hjint', hjres'⟩ := hR₀ (jqModC ↥A) hymem
  have hsub : (⟨coeffMap A.subtype (jqModC ↥A), hymem⟩ : ↥(modularFunctionFieldBar M')) =
      ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :=
    Subtype.ext hymap
  have hjint : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
      ↥(modularFunctionFieldBar M')) ∈ R₀.integers := by
    rw [← hsub]; exact hjint'
  have hjres : (R₀.residue ⟨_, hjint⟩ : modularFunctionFieldC (ResidueField ↥A) M') =
      jGeomGen (ResidueField ↥A) M' := by
    have e1 : (⟨(⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')), hjint⟩ : ↥R₀.integers) = ⟨_, hjint'⟩ := Subtype.ext hsub.symm
    rw [e1]
    apply Subtype.ext
    rw [hjres']
    change (jqModC ↥A).map (IsLocalRing.residue ↥A) = jqModC (ResidueField ↥A)
    exact map_jqModC _

  have hsW : IsSupersingularPlace q M' (ResidueField ↥A)
      (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) := (hW s).mp s.2
  obtain ⟨-, ⟨hjO, -⟩, hssκ⟩ := hsW

  obtain ⟨a', ha'⟩ := hres ((s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')).evalAt
    (jGeomGen (ResidueField ↥A) M'))

  obtain ⟨-, hconst⟩ := hSS_over s _ hjint (fun P hP => hP) (by rw [hjres]; exact hjO)
  obtain ⟨ha'O, ha'm⟩ := hconst (ι a') (by rw [hjres]; exact ha')

  have haO' : (((⟨_, hjF₀⟩ : ↥F₀) : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ))
      ∈ OSS s := by
    have : (((⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
        ((⟨_, hjF₀⟩ : ↥F₀) : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) := by
      rw [← hj₀ a]; simp
    rw [← this]; exact haO
  have ham' : (⟨_, haO'⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s) := by
    have e : (⟨_, haO'⟩ : ↥(OSS s)) = ⟨_, haO⟩ := by
      apply Subtype.ext
      change ((⟨_, hjF₀⟩ : ↥F₀) : ↥(fieldBar q M')) - _ = (((⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M'))
      rw [← hj₀ a]; simp
    rw [e]; exact ham
  have hdiff : (ι a' - ι a : ↥A) ∈ maximalIdeal ↥A := by
    apply SSConvDrinfeldCentre.mem_maximalIdeal_of_algebraMap_mem_maximalIdeal A (OSS s) (hSS_A s)
    have hmemO : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a' - ι a : ↥A) : AlgebraicClosure ℚ) ∈ OSS s :=
      (hSS_A s _).mpr (ι a' - ι a).2
    refine ⟨hmemO, ?_⟩

    have e : (⟨_, hmemO⟩ : ↥(OSS s)) = ⟨_, haO'⟩ - ⟨_, ha'O⟩ := by
      apply Subtype.ext
      change algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a' - ι a : ↥A) : AlgebraicClosure ℚ) =
        (((⟨_, hjF₀⟩ : ↥F₀) : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ)) -
        ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) -
          algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a' : ↥A) : AlgebraicClosure ℚ))
      have hjj : (((⟨_, hjF₀⟩ : ↥F₀) : ↥(fieldBar q M'))) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) := rfl
      have hsub' : ((ι a' - ι a : ↥A) : AlgebraicClosure ℚ) = ((ι a' : ↥A) : AlgebraicClosure ℚ) - ((ι a : ↥A) : AlgebraicClosure ℚ) :=
        rfl
      rw [hjj, hsub', RingHom.map_sub]
      ring
    rw [e]
    exact Ideal.sub_mem _ ham' ha'm
  have hresa : IsLocalRing.residue ↥A (ι a) =
      (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')).evalAt (jGeomGen (ResidueField ↥A) M') := by
    rw [← ha', RingHom.comp_apply, eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hdiff
  have hssa : IsLocalRing.residue ↥A (ι a) ∈ ssJSet q (ResidueField ↥A) := by
    rw [hresa]; exact hssκ

  have hψϖ : (φ.comp (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)))) ϖ₀ = 0 := by
    show φ (algebraMap A₀ _ ϖ₀) = 0
    rw [← RingHom.mem_ker, hφ]
    exact hϖ
  obtain ⟨θ, hθ⟩ := SSConvDrinfeldCentre.exists_ringHom_residueField_comp_eq ι hres ϖ₀ hϖ₀ (φ.comp (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)))) hψϖ
  rw [hφj, show φ (algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) a) = θ (IsLocalRing.residue ↥A (ι a)) by rw [hθ]; rfl]
  exact ModularCurve.mem_ssJSet_map_of_isAlgClosed θ _ hssa

end S_ModularCurve_FullLevel_mem_ssJSet_of_forall_mem_maximalIdeal_drinfeldRing_mem_chartAlgFin_descent_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_mem_ssJSet_of_forall_mem_maximalIdeal_drinfeldRing_mem_chartAlgFin_descent_of_eq_three (solution)
