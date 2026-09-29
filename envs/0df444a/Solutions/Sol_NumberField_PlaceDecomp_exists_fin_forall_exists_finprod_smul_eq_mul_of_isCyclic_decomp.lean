-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_isCyclic_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3bbc1be1-2f82-52e8-9f73-98d395988ddc

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_NumberField_PlaceDecomp_exists_carryClassHom_surjective_ker_eq_norms_adicCompletion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_isCyclic_decomp
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open CategoryTheory groupCohomology IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)
    [IsCyclic ↥(NumberField.PlaceDecomp.decomp E F w)] :
    ∃ (n : ℕ) (c : Fin n → (v.adicCompletion E)ˣ), n ≤ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) ∧
      ∀ a : (v.adicCompletion E)ˣ, ∃ (i : Fin n) (b : (w.adicCompletion F)ˣ),
        (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
            w.adicCompletion F) =
          IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F))
            ((a * (c i)⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
  classical

  haveI : Module.Finite E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[E] F) := inferInstance
  haveI : Finite ↥(NumberField.PlaceDecomp.decomp E F w) := inferInstance

  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := ↥(NumberField.PlaceDecomp.decomp E F w))
  have hfin : IsOfFinOrder t := isOfFinOrder_of_finite t
  obtain ⟨Ψ, -, hsurj, hker, hcard⟩ :=
    NumberField.PlaceDecomp.exists_carryClassHom_surjective_ker_eq_norms_adicCompletion E F v w hw t ht hfin

  set Q := Multiplicative (groupCohomology.H2
    (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) with hQ
  have hcardQ : Nat.card Q = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := hcard
  have hQfin : Finite Q := by
    apply Nat.finite_of_card_ne_zero
    rw [hcardQ]
    exact Nat.card_pos.ne'

  let e : Q ≃ Fin (Nat.card Q) := Finite.equivFin Q
  let s : Q → (v.adicCompletion E)ˣ := Function.surjInv hsurj
  have hs : ∀ q, Ψ (s q) = q := Function.surjInv_eq hsurj
  refine ⟨Nat.card Q, fun i => s (e.symm i), le_of_eq hcardQ, fun a => ?_⟩

  have h1 : Ψ (a * (s (e.symm (e (Ψ a))))⁻¹) = 1 := by
    rw [Equiv.symm_apply_apply, map_mul, map_inv, hs, mul_inv_cancel]
  obtain ⟨b, hb⟩ := (hker _).1 h1
  exact ⟨e (Ψ a), b, hb⟩

end S_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_isCyclic_decomp
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_isCyclic_decomp (solution)
