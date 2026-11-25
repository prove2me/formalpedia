-- Prove2me | solution 1 for GlobalTheory.SS.exists_grpObj_of_strict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:37:54.647625+00:00
-- url     : https://prove2.me/submissions/33cdad59-a563-4a29-b6a6-bff41824b6c5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnionTranslatesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGrpObjOfStrictBirationalLaw
import Theorems.Thm_GlobalTheory_SS_StrictGrp_isPullback_j
import Theorems.Thm_GlobalTheory_SS_StrictGrp_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_StrictGrp_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_StrictGrp_twist_comm
import Theorems.Thm_GlobalTheory_SS_StrictGrp_prod_comm
import Theorems.Thm_GlobalTheory_SS_StrictGrp_defAt_transport
import Theorems.Thm_GlobalTheory_SS_StrictGrp_isOpen_defAt
import Theorems.Thm_GlobalTheory_SS_StrictGrp_defAt_generic
import Theorems.Thm_GlobalTheory_SS_StrictGrp_ext_section
import Theorems.Thm_GlobalTheory_SS_StrictGrp_transl_mul
import Theorems.Thm_GlobalTheory_SS_StrictGrp_transl_one
import Theorems.Thm_GlobalTheory_SS_StrictGrp_transl_inv
import Theorems.Thm_GlobalTheory_SS_StrictGrp_pt_transl
import Theorems.Thm_GlobalTheory_SS_StrictGrp_mul_transl
import Theorems.Thm_GlobalTheory_SS_StrictGrp_inv_transl
import Theorems.Thm_GlobalTheory_SS_StrictGrp_exists_section
import Theorems.Thm_GlobalTheory_SS_StrictGrp_geometricallyConnected
import Theorems.Thm_GlobalTheory_SS_StrictGrp_isOpenImmersion_tensor
import Theorems.Thm_GlobalTheory_SS_StrictGrp_mem_range_tensor
import Theorems.Thm_GlobalTheory_SS_CompatCrit_isPullback_j
import Theorems.Thm_GlobalTheory_SS_FinUnion_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_FinUnion_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_FinUnion_transl_one
import Theorems.Thm_GlobalTheory_SS_GI_genIso_calculus
import Theorems.Thm_GlobalTheory_SS_GI_isOpen_defAt
import Theorems.Thm_GlobalTheory_SS_IsoAt_defAt
import Theorems.Thm_GlobalTheory_SS_LawDef_defAt_generic
import Theorems.Thm_GlobalTheory_SS_LawDef_exists_section
import Theorems.Thm_GlobalTheory_SS_LawDef_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_LawDef_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_Model_isPullback_j
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_SectionTranslation_translation_by_section
import Theorems.Thm_GlobalTheory_SS_Translates_isPullback_j
import Theorems.Thm_GlobalTheory_SS_existsUnique_extension_of_forall_defAt
import Theorems.Thm_GlobalTheory_SS_isoAt_id
import Theorems.Thm_GlobalTheory_grpObj_of_dense_open
import Theorems.Thm_GlobalTheory_isOpenImmersion_spMap_of_isDiscreteValuationRing
import Theorems.Thm_P2M_GlobalTheory_T_exists_union_translates__2cfbf1c89070
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory.SS.StrictGrp
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∃ (G : Model R A) (_ : GrpObj G.Y), SmConn G.Y ∧ IsMonHom G.e.hom ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom → ∃ s : 𝟙_ (Over (Sp R)) ⟶ G.Y, spMap (algebraMap R K) ≫ s.left = a.left ≫ G.j := by
  intro R K _ _ _ _ _ hSH A _ _ hA M hM
  obtain ⟨G, hGI, hLe, hcov, hmu⟩ := GlobalTheory.T.exists_union_translates' R K hSH A hA M hM
  have hD := hSH.1
  have hF := hSH.2.2.2
  have hMI : M.Irr := hM.1.1
  have hGs := G.smooth
  have hGp := G.sep
  have hext := GlobalTheory.SS.existsUnique_extension_of_forall_defAt R K
  have hsec := GlobalTheory.SS.SectionTranslation.translation_by_section R K hSH A hA M hM
  obtain ⟨-, hcomp, hinv, -⟩ := GlobalTheory.SS.GI.genIso_calculus R K hSH
  let H : (𝟙_ (Over (Sp K)) ⟶ A) → Prop := fun a => GenIso M M (transl a).hom
  have H1 : H 1 := by
    obtain ⟨y, hy⟩ := hMI.nonempty
    exact ⟨y, hy, transl_one (A := A) ▸ isoAt_id M y⟩
  have Hmul : ∀ a b, H a → H b → H (a * b) := fun a b ha hb => by
    have := hcomp _ _ _ M M M _ _ hMI ha hb
    rwa [transl_mul] at this
  have Hinv : ∀ a, H a → H a⁻¹ := fun a ha => by
    have := (hinv _ _ M M (transl a)).1 ha
    rwa [transl_inv] at this
  have hg : ∀ a, H a → ∃ g : M.Y ⟶ G.Y, IsOpenImmersion g.left ∧ M.j ≫ g.left = (transl a).hom.left ≫ G.j :=
    fun a ha => by
      obtain ⟨g, h₁, h₂⟩ := hLe a ha
      exact ⟨g, h₁, twist_comm h₂⟩
  have hc : ∀ y : G.Y.left, ∃ (a : 𝟙_ (Over (Sp K)) ⟶ A) (g : M.Y ⟶ G.Y) (x : M.Y.left), H a ∧
      IsOpenImmersion g.left ∧ M.j ≫ g.left = (transl a).hom.left ≫ G.j ∧ g.left x = y := fun y => by
    obtain ⟨a, g, ha, h₁, h₂, x, hx⟩ := hcov y
    exact ⟨a, g, x, ha, h₁, twist_comm h₂, hx⟩

  have hT : ∀ c, H c → ∃ T : G.Y ⟶ G.Y, G.j ≫ T.left = (transl c).hom.left ≫ G.j := fun c hc' => by
    refine (hext _ _ G G _ fun y => ?_).exists
    obtain ⟨a, g, x, ha, _, h, rfl⟩ := hc y
    obtain ⟨g', -, h'⟩ := hg _ (Hmul a c ha hc')
    exact defAt_transport h h' (by rw [Category.id_comp, transl_mul]) (isoAt_id M x).defAt

  obtain ⟨m, hm⟩ : ∃ m : (G.prod G).Y ⟶ G.Y, (G.prod G).j ≫ m.left = (μ[A]).left ≫ G.j := by
    refine (hext _ _ (G.prod G) G _ fun z => ?_).exists
    obtain ⟨a, g, x, ha, _, h, hx⟩ := hc ((fst G.Y G.Y).left z)
    obtain ⟨b, g', x', hb, _, h', hx'⟩ := hc ((snd G.Y G.Y).left z)
    obtain ⟨w, rfl⟩ := mem_range_tensor g g' z ⟨x, hx⟩ ⟨x', hx'⟩
    obtain ⟨T, hT⟩ := hT _ (Hmul a b ha hb)
    have := isOpenImmersion_tensor g g'
    exact defAt_transport (M := M.prod M) (G := G.prod G) (f := tensorIso (transl a) (transl b)) (g := g ⊗ₘ g')
      (prod_comm h h') hT (mul_transl a b) (hmu w)

  have hmove : ∀ (s : 𝟙_ (Over (Sp R)) ⟶ M.Y) (c a : 𝟙_ (Over (Sp K)) ⟶ A) (g : M.Y ⟶ G.Y),
      c.left ≫ M.j = spMap (algebraMap R K) ≫ s.left → M.j ≫ g.left = (transl a).hom.left ≫ G.j →
      spMap (algebraMap R K) ≫ (s ≫ g).left = (a * c).left ≫ G.j := fun s c a g h₁ h₂ => by
    rw [Over.comp_left, ← Category.assoc, ← h₁, Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, pt_transl]
  have hsecG : ∀ a, H a → ∃ s : 𝟙_ (Over (Sp R)) ⟶ G.Y, spMap (algebraMap R K) ≫ s.left = a.left ≫ G.j :=
    fun a ha => by
      obtain ⟨s, -⟩ := exists_section hSH M isOpen_univ.isLocallyClosed (by simpa using hMI.nonempty)
      obtain ⟨c, h₁, h₂, -⟩ := hsec s
      obtain ⟨g, -, h₃⟩ := hg _ (Hmul _ _ ha (Hinv _ h₂))
      exact ⟨s ≫ g, by rw [hmove s c _ g h₁ h₃, inv_mul_cancel_right]⟩

  obtain ⟨i, hi⟩ : ∃ i : G.Y ⟶ G.Y, G.j ≫ i.left = (ι[A]).left ≫ G.j := by
    refine (hext _ _ G G _ fun y => ?_).exists
    by_contra hy
    have hys : y ∈ G.sp := by_contra fun h => hy (defAt_generic G G _ h)
    obtain ⟨a, g, x, ha, _, h, rfl⟩ := hc y
    have hxs : x ∈ M.sp := by
      have e : G.Y.hom (g.left x) = M.Y.hom x := by rw [← Scheme.Hom.comp_apply, Over.w g]
      exact e.symm.trans hys
    obtain ⟨s, hs⟩ := exists_section hSH M (S := g.left ⁻¹' {y | DefAt G G (ι[A]) y}ᶜ)
      ((isOpen_defAt G G _).isClosed_compl.preimage g.left.continuous).isLocallyClosed ⟨x, hy, hxs⟩
    obtain ⟨x', hx', hx''⟩ := hM.1.2.2
    obtain ⟨u, hu⟩ := exists_section hSH M (isOpen_defAt M M (ι[A])).isLocallyClosed ⟨x', hx''.defAt, hx'⟩
    obtain ⟨c, hc₁, hc₂, -⟩ := hsec s
    obtain ⟨d, hd₁, hd₂, -⟩ := hsec u
    have He := Hmul _ _ (Hmul _ _ ha hc₂) (Hinv _ hd₂)
    obtain ⟨g₁, _, h₁⟩ := hg _ He
    obtain ⟨g₂, -, h₂⟩ := hg _ (Hinv _ He)
    have e : u ≫ g₁ = s ≫ g := ext_section (K := K) (by
      rw [hmove u d _ g₁ hd₁ h₁, hmove s c _ g hc₁ h, inv_mul_cancel_right])
    have e' : g₁.left (u.left (IsLocalRing.closedPoint R)) = g.left (s.left (IsLocalRing.closedPoint R)) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, e]
    exact hs (e' ▸ defAt_transport h₁ h₂ (inv_transl _) hu)
  obtain ⟨e, he⟩ := hsecG 1 H1
  have := GlobalTheory.isOpenImmersion_spMap_of_isDiscreteValuationRing R K
  obtain ⟨inst, -, -, -, hcomm, hpb⟩ := GlobalTheory.grpObj_of_dense_open (Sp R) (Sp K) (spMap (algebraMap R K)) G.Y A G.j
    (isPullback_j G) m i e (fun φ₂ h => by
      obtain rfl : φ₂ = (G.prod G).j := by
        apply Over.tensorObj_ext
        · exact h.1.trans (prod_j_fst G G).symm
        · exact h.2.trans (prod_j_snd G G).symm
      exact hm) hi (by simpa [Hom.one_def] using he)
  have := hA.geomConnected
  refine ⟨G, inst, ⟨hcomm, hGs, hGp, G.qc, geometricallyConnected hSH G hGI⟩, ?_, hsecG⟩
  obtain ⟨e', h₁, h₂⟩ := grpPullback_iso (isGrpPullback_pullback G.Y (spMap (algebraMap R K))) hpb
  have e₀ : G.e.hom = e'.hom := by
    apply Over.OverMorphism.ext
    apply (isPullback_j G).hom_ext
    · rw [h₂, Model.j, ← Category.assoc, ← Over.comp_left, G.e.hom_inv_id, Over.id_left, Category.id_comp]
    · rw [Over.w, Over.w]
  rw [e₀]
  exact h₁
end GlobalTheory.SS
