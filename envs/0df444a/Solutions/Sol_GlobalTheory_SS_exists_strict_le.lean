-- Prove2me | solution 1 for GlobalTheory.SS.exists_strict_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:52:07.247012+00:00
-- url     : https://prove2.me/submissions/4f8184ab-2d13-4e3c-a7bc-790466d65cae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeronStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOnPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStrictModelOfBirational
import Theorems.Thm_GlobalTheory_SS_StrictLaw_j_notMem_sp
import Theorems.Thm_GlobalTheory_SS_StrictLaw_exists_restrict
import Theorems.Thm_GlobalTheory_SS_StrictLaw_fst_case
import Theorems.Thm_GlobalTheory_SS_StrictLaw_snd_case
import Theorems.Thm_GlobalTheory_SS_StrictLaw_good_isoAt
import Theorems.Thm_GlobalTheory_SS_StrictLaw_shear_fst
import Theorems.Thm_GlobalTheory_SS_StrictLaw_coshear_snd
import Theorems.Thm_GlobalTheory_SS_StrictLaw_shear_snd
import Theorems.Thm_GlobalTheory_SS_Model_le_refl
import Theorems.Thm_GlobalTheory_T_modelMapGenericallyOpenImmersion_calculus
import Theorems.Thm_P2M_GlobalTheory_T_prod_irr_and_weakNeron__58567c23dfd4


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS
open StrictLaw
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, BirLaw M → ∃ N : Model R A, Strict N ∧ N.Le M := by
  intro R K _ _ _ _ _ hSH A _ _ _ M ⟨hM, hs, hι⟩
  obtain ⟨gLe, gComp, gIso, gProd, gBr⟩ := GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hSH
  have hMM := (GlobalTheory.T.prod_irr_and_weakNeron' R K hSH A A).1 M M hM hM
  obtain ⟨hdvr, -, hac, hfr⟩ := hSH
  have hβ := (gBr A A A M M M hM hM hM).2
  have ht : GenIso (M.prod M) (M.prod M) (coshear A true) :=
    gComp _ _ _ _ _ _ _ _ hMM hβ (gComp _ _ _ _ _ _ _ _ hMM (hs true) hβ)
  have hco : ∀ b, GenIso (M.prod M) (M.prod M) (coshear A b) := by
    intro b
    cases b
    · exact gComp _ _ _ _ _ _ _ _ hMM
        (gProd _ _ _ _ _ _ _ _ _ _ hι (gLe A M M hM M.le_refl)) ht
    · exact ht
  choose T hT hTne hTx using fun b => fst_case M hM (shear A b) (shear_fst b) (hs b)
  choose T' hT' hTne' hTx' using fun b => snd_case M hM hMM (shear A b) (coshear A b)
    (shear_fst b) (coshear_snd b) (shear_snd b) (hs b) (hco b)
  have hcl : IsClosed M.sp :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal (IsLocalRing.closedPoint R)).2
      (IsLocalRing.maximalIdeal.isMaximal R) |>.preimage M.Y.hom.continuous
  let W : Set M.Y.left := (T true ∩ T false) ∩ (T' true ∩ T' false)
  have hW : IsOpen W := ((hT _).inter (hT _)).inter ((hT' _).inter (hT' _))
  have hWne : (M.sp ∩ W).Nonempty :=
    hM.2 _ _ ((hT _).inter (hT _)) ((hT' _).inter (hT' _))
      (hM.2 _ _ (hT _) (hT _) (hTne _) (hTne _)) (hM.2 _ _ (hT' _) (hT' _) (hTne' _) (hTne' _))
  let V : M.Y.left.Opens := ⟨M.spᶜ ∪ W, hcl.isOpen_compl.union hW⟩
  obtain ⟨N, i, hi, hj, hr⟩ := exists_restrict M V (by
    rintro _ ⟨a, rfl⟩; exact Or.inl (j_notMem_sp M a))
  have hsp : N.sp = i.left ⁻¹' M.sp := by
    ext x
    show N.Y.hom x = _ ↔ M.Y.hom (i.left x) = _
    rw [← Scheme.Hom.comp_apply, Over.w]
  have hinj := i.left.isOpenEmbedding.injective
  have hN : N.Irr := by
    obtain ⟨x, hx, hxW⟩ := hWne
    obtain ⟨x, rfl⟩ : x ∈ Set.range i.left := hr ▸ Or.inr hxW
    unfold Model.Irr
    rw [hsp]
    exact ⟨⟨x, hx⟩, hM.2.preimage i.left.isOpenEmbedding⟩
  have hLe : N.Le M := ⟨i, hi, hj⟩
  have key : ∀ b, ∀ x ∈ N.sp,
      (∃ z, (pr₁ N N).left z = x ∧ IsoAt (N.prod N) (N.prod N) (shear A b) z) ∧
      ∃ z, (pr₂ N N).left z = x ∧ IsoAt (N.prod N) (N.prod N) (shear A b) z := by
    intro b x hx
    rw [hsp] at hx
    have hxV : i.left x ∈ (V : Set M.Y.left) := hr ▸ ⟨x, rfl⟩
    have hxW : i.left x ∈ W := hxV.resolve_left (fun h => h hx)
    have h1 : i.left x ∈ T b := by cases b; exacts [hxW.1.2, hxW.1.1]
    have h2 : i.left x ∈ T' b := by cases b; exacts [hxW.2.2, hxW.2.1]
    obtain ⟨z, hz, hg⟩ := hTx b _ i.left.isOpenEmbedding.isOpen_range _ hx h1 ⟨x, rfl⟩
    obtain ⟨z', hz', hg'⟩ := hTx' b _ i.left.isOpenEmbedding.isOpen_range _ hx h2 ⟨x, rfl⟩
    obtain ⟨w, hw, -, hw2⟩ := good_isoAt i hj hg
    obtain ⟨w', -, hw', hw2'⟩ := good_isoAt i hj hg'
    exact ⟨⟨w, hinj (hw.trans hz), hw2⟩, w', hinj (hw'.trans hz'), hw2'⟩
  refine ⟨N, ⟨⟨hN, fun b => ?_, ?_⟩, key⟩, hLe⟩
  · obtain ⟨x, hx⟩ := hN.1
    obtain ⟨z, hz, hz'⟩ := (key b x hx).1
    refine ⟨z, ?_, hz'⟩
    show (N.prod N).Y.hom z = _
    rw [← Over.w (pr₁ N N), Scheme.Hom.comp_apply, hz]
    exact hx
  · have h1 := gLe A N M hN hLe
    have h2 := (gIso A A N M (Iso.refl A)).1 h1
    have h3 := gComp _ _ _ _ _ _ _ _ hM h1 (gComp _ _ _ _ _ _ _ _ hM hι h2)
    simpa using h3
end GlobalTheory.SS
