-- Prove2me | solution 1 for NumberField.PlaceDecomp.forall_exists_finprod_smul_eq_and_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fe376a9d-bcaa-53ef-9229-8587cbcf5901

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one
import Theorems.Thm_NumberField_PlaceDecomp_adicCompletionSemialgHom_norm_eq_finprod_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_forall_exists_finprod_smul_eq_and_of_ramificationIdx_eq_one
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_PlaceDecomp_forall_exists_finprod_smul_eq_and_of_ramificationIdx_eq_one.NumberField"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_forall_exists_finprod_smul_eq_and_of_ramificationIdx_eq_one.NumberField.PlaceDecomp"

namespace NumberField p2m_export "NumberField" "place PlaceDecomp.decomp PlaceDecomp.adicCompletionSemialgHom_norm_eq_finprod_smul" namespace PlaceDecomp p2m_export "NumberField.PlaceDecomp" "decomp adicCompletionSemialgHom_norm_eq_finprod_smul" end NumberField.PlaceDecomp
p2m_open_scoped "NumberField NumberField.PlaceDecomp" in

theorem NumberField.PlaceDecomp.coe_finprod_smul_eq_adicCompletionSemialgHom_norm
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 F)) (b : (w.1.adicCompletion F)ˣ) :
    (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w.1), σ • b : (w.1.adicCompletion F)ˣ) : (w.1.adicCompletion F)ˣ) : w.1.adicCompletion F) =
      IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F w
        ((Units.map (Algebra.norm (v.adicCompletion E) : (w.1.adicCompletion F) →* v.adicCompletion E) b : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
  rw [Units.coe_map]
  erw [NumberField.PlaceDecomp.adicCompletionSemialgHom_norm_eq_finprod_smul E F v w (b : w.1.adicCompletion F)]
  rw [← Units.coeHom_apply, MonoidHom.map_finprod _ (Set.toFinite _)]
  rfl

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)
    (he : v.asIdeal.ramificationIdx' w.asIdeal = 1) (m : ℕ) :
    (∀ b : (w.adicCompletion F)ˣ, Valued.v (b : w.adicCompletion F) = 1 →
        (m = 0 ∨ Valued.v ((b : w.adicCompletion F) - 1) ≤ WithZero.exp (-(m : ℤ))) →
        ∃ a : (v.adicCompletion E)ˣ, Valued.v (a : v.adicCompletion E) = 1 ∧
          (m = 0 ∨ Valued.v ((a : v.adicCompletion E) - 1) ≤ WithZero.exp (-(m : ℤ))) ∧
          (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
              w.adicCompletion F) =
            IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F))
              (a : v.adicCompletion E)) ∧
    (∀ a : (v.adicCompletion E)ˣ, Valued.v (a : v.adicCompletion E) = 1 →
        (m = 0 ∨ Valued.v ((a : v.adicCompletion E) - 1) ≤ WithZero.exp (-(m : ℤ))) →
        ∃ b : (w.adicCompletion F)ˣ, Valued.v (b : w.adicCompletion F) = 1 ∧
          (m = 0 ∨ Valued.v ((b : w.adicCompletion F) - 1) ≤ WithZero.exp (-(m : ℤ))) ∧
          (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
              w.adicCompletion F) =
            IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F))
              (a : v.adicCompletion E)) := by

  obtain ⟨wE, rfl⟩ : ∃ wE : v.Extension (𝓞 F), wE.1 = w := ⟨⟨w, hw⟩, rfl⟩
  have hC := LanglandsTunnell.TateLocal.image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one E F v wE he m
  have hN := NumberField.PlaceDecomp.coe_finprod_smul_eq_adicCompletionSemialgHom_norm E F v wE
  refine ⟨fun b hb1 hbm => ?_, fun a ha1 ham => ?_⟩
  · have hb : b ∈ LanglandsTunnell.TateLocal.higherUnitsAt F wE.1 m := ⟨hb1, hbm⟩
    have ha : (Units.map (Algebra.norm (v.adicCompletion E) : (wE.1.adicCompletion F) →* v.adicCompletion E) b) ∈
        LanglandsTunnell.TateLocal.higherUnitsAt E v m := by
      rw [← hC]; exact ⟨b, hb, rfl⟩
    exact ⟨_, ha.1, ha.2, hN b⟩
  · have ha : a ∈ LanglandsTunnell.TateLocal.higherUnitsAt E v m := ⟨ha1, ham⟩
    rw [← hC] at ha
    obtain ⟨b, hb, hba⟩ := ha
    refine ⟨b, hb.1, hb.2, ?_⟩
    rw [hN b, hba]
    rfl

end S_NumberField_PlaceDecomp_forall_exists_finprod_smul_eq_and_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_NumberField_PlaceDecomp_forall_exists_finprod_smul_eq_and_of_ramificationIdx_eq_one (solution)
