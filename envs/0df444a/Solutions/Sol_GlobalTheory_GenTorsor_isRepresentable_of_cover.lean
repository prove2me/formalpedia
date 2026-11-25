-- Prove2me | solution 1 for GlobalTheory.GenTorsor.isRepresentable_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:49:22.584672+00:00
-- url     : https://prove2.me/submissions/5624984b-3b66-4734-8cfb-a5d11a5fbe73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsRepresentableOfCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenTorsor
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.GenTorsor
theorem _root_.solution (F : Scheme.{0}ᵒᵖ ⥤ Type)
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F) (p : F ⟶ yoneda.obj X)
    {J : Type} (W : J → X.Opens) (hW : iSup W = ⊤) (T : J → Scheme.{0})
    (y : ∀ i, F.obj (op (T i))) (π : ∀ i, T i ⟶ W i)
    (hπ : ∀ i, p.app _ (y i) = π i ≫ (W i).ι)
    (h : ∀ i (Z : Scheme.{0}) (x : F.obj (op Z)) (b : Z ⟶ W i), p.app _ x = b ≫ (W i).ι →
      ∃! c : Z ⟶ T i, F.map c.op (y i) = x) : F.IsRepresentable := by
  let G : Sheaf Scheme.zariskiTopology.{0} Type := ⟨F, (isSheaf_iff_isSheaf_of_type _ _).2 hF⟩
  let f : ∀ i, yoneda.obj (T i) ⟶ G.1 := fun i => yonedaEquiv.symm (y i)
  have hp : ∀ i (Z : Scheme.{0}) (c : Z ⟶ T i), p.app _ (F.map c.op (y i)) = c ≫ π i ≫ (W i).ι := by
    intro i Z c
    rw [← hπ]
    exact ConcreteCategory.congr_hom (p.naturality c.op) (y i)
  have hf : ∀ i, IsOpenImmersion.presheaf (f i) := by
    intro i
    have : IsPullback (f i) (yoneda.map (π i)) p (yoneda.map (W i).ι) := by
      apply IsPullback.of_forall_isPullback_app
      rintro ⟨Z⟩
      rw [Types.isPullback_iff]
      refine ⟨?_, ?_, ?_⟩
      · ext c
        exact (hp i Z c).trans (Category.assoc _ _ _).symm
      · rintro c c' ⟨h1, -⟩
        exact (h i Z (F.map (Quiver.Hom.op c) (y i)) (c ≫ π i)
          ((hp i Z c).trans (Category.assoc _ _ _).symm)).unique rfl h1.symm
      · intro x b hb
        obtain ⟨c, hc, -⟩ := h i Z x b hb
        refine ⟨c, hc, ?_⟩
        change c ≫ π i = b
        rw [← cancel_mono (W i).ι, Category.assoc, ← hp, hc]
        exact hb
    exact (MorphismProperty.relative_isStableUnderBaseChange @IsOpenImmersion).of_isPullback this.flip
      (MorphismProperty.relative_map (inferInstanceAs (IsOpenImmersion (W i).ι)))
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) := by
    constructor
    intro Z x
    let q : Z ⟶ X := p.app _ x
    let 𝒰 := Z.openCoverOfIsOpenCover (fun i => q ⁻¹ᵁ W i) (by
      rw [IsOpenCover, ← Scheme.Hom.preimage_iSup, hW]; rfl)
    refine GrothendieckTopology.superset_covering _ ?_ 𝒰.mem_grothendieckTopology
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    obtain ⟨c, hc, -⟩ := h i _ (F.map (q ⁻¹ᵁ W i).ι.op x) (q ∣_ W i) (by
      rw [morphismRestrict_ι]
      exact ConcreteCategory.congr_hom (p.naturality (q ⁻¹ᵁ W i).ι.op) x)
    refine ⟨(Sigma.ι (fun i => yoneda.obj (T i)) i).app _ c, ?_⟩
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app (Sigma.ι_desc f i) _) c).trans hc
  exact Scheme.LocalRepresentability.isRepresentable hf
end GlobalTheory.GenTorsor
