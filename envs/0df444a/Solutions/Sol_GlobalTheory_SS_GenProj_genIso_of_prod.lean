-- Prove2me | solution 1 for GlobalTheory.SS.GenProj.genIso_of_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:52:02.71889+00:00
-- url     : https://prove2.me/submissions/3ff80a96-41d9-44f1-bf52-67f5a2d8f910

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GenericIsomorphismProductModels
import Theorems.Thm_GlobalTheory_SS_GenProj_eq_of_generic
import Theorems.Thm_GlobalTheory_SS_GenProj_exists_openImmersion
import Theorems.Thm_GlobalTheory_SS_GenProj_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_GenProj_exists_lift_j
import Theorems.Thm_GlobalTheory_SS_GenProj_mono_j
import Theorems.Thm_GlobalTheory_SS_Model_j_hom


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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GenProj
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.GenProj
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A A' B B' : Over (Sp K)) [IsIntegral A.left] [IsIntegral (A ⊗ B).left] (M : Model R A) (M' : Model R A') (N : Model R B) (N' : Model R B') (f : A ≅ A') (Θ : A ⊗ B ⟶ A' ⊗ B'), M.Irr → M'.Irr → N.Irr → N'.Irr → Θ ≫ fst A' B' = fst A B ≫ f.hom → GenIso (M.prod N) (M'.prod N') Θ → GenIso M M' f.hom := by
  intro R K _ _ _ _ _ hSH A A' B B' _ _ M M' N N' f Θ _ _ _ _ hΘ ⟨z, hz, U, g, hzU, ⟨hg₁, hg₂⟩, hgo⟩
  have := hSH.2.2.2
  have := M.smooth; have := M'.smooth; have := N.smooth; have := N'.smooth
  have := M.sep; have := M'.sep
  have := mono_j M; have := mono_j M'
  have : IsDominant (spMap (algebraMap R K)) := by
    refine ⟨?_⟩
    show DenseRange (PrimeSpectrum.comap (algebraMap R K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap R K))
  have : IsIso f.hom.left := inferInstanceAs (IsIso ((Over.forget _).map f.hom))
  let π : (M.prod N).Y.left ⟶ M.Y.left := (fst M.Y N.Y).left
  let π' : (M'.prod N').Y.left ⟶ M'.Y.left := (fst M'.Y N'.Y).left
  have : Smooth π := inferInstanceAs (Smooth (pullback.fst M.Y.hom N.Y.hom))
  have : Smooth π' := inferInstanceAs (Smooth (pullback.fst M'.Y.hom N'.Y.hom))
  have hπ : π ≫ M.Y.hom = (M.prod N).Y.hom := Over.w (fst M.Y N.Y)
  have hπ' : π' ≫ M'.Y.hom = (M'.prod N').Y.hom := Over.w (fst M'.Y N'.Y)
  have hj : (M.prod N).j ≫ π = (fst A B).left ≫ M.j := prod_j_fst M N
  have hj' : (M'.prod N').j ≫ π' = (fst A' B').left ≫ M'.j := prod_j_fst M' N'
  have hs : (U.ι ≫ π) ≫ M.Y.hom = (g ≫ π') ≫ M'.Y.hom := by
    rw [Category.assoc, Category.assoc, hπ, hπ', hg₁]
  have H : ∀ (Z : Scheme.{0}) (a : Z ⟶ U.toScheme) (t : Z ⟶ Sp K),
      a ≫ (U.ι ≫ π) ≫ M.Y.hom = t ≫ spMap (algebraMap R K) →
      ∃ c : Z ⟶ A.left, c ≫ M.j = a ≫ U.ι ≫ π ∧ c ≫ f.hom.left ≫ M'.j = a ≫ g ≫ π' := by
    intro Z a t h
    obtain ⟨d, hd⟩ := exists_lift_j (M.prod N) (a ≫ U.ι) t (by rw [← h, ← hπ]; simp only [Category.assoc])
    obtain ⟨d', h₁, h₂⟩ := (isPullback_morphismRestrict (M.prod N).j U).exists_lift a d hd.symm
    refine ⟨d ≫ (fst A B).left, ?_, ?_⟩
    · rw [Category.assoc, ← hj, ← Category.assoc, hd, Category.assoc]
    · have e : Θ.left ≫ (fst A' B').left = (fst A B).left ≫ f.hom.left := by
        rw [← Over.comp_left, hΘ, Over.comp_left]
      rw [← h₁, ← h₂]
      simp only [Category.assoc]
      rw [reassoc_of% hg₂, hj', reassoc_of% e]
  obtain ⟨V, p', h, hp, _, _, hq, hh⟩ := exists_openImmersion (U.ι ≫ π) (g ≫ π') (fun Z a b =>
    ⟨eq_of_generic (spMap (algebraMap R K)) M.Y.hom M'.Y.hom _ _ hs M.j (f.hom.left ≫ M'.j) H a b,
     eq_of_generic (spMap (algebraMap R K)) M'.Y.hom M.Y.hom _ _ hs.symm (f.hom.left ≫ M'.j) M.j
      (fun Z a t h => (H Z a t (by rw [hs, h])).imp fun _ h => h.symm) a b⟩)
  have : Epi p' := Flat.epi_of_flat_of_surjective _
  refine ⟨π z, ?_, V, h, ?_, ⟨?_, ?_⟩, hh⟩
  · show M.Y.hom (π z) = _
    rw [← Scheme.Hom.comp_apply, hπ]; exact hz
  · have : V.ι (p' ⟨z, hzU⟩) = π z := congrArg (fun q : U.toScheme ⟶ M.Y.left => q ⟨z, hzU⟩) hp
    rw [← this]; exact (p' ⟨z, hzU⟩).2
  · rw [← cancel_epi p', reassoc_of% hq, reassoc_of% hp]
    simpa only [Category.assoc] using hs.symm
  · have : Epi (pullback.snd p' (M.j ∣_ V)) := Flat.epi_of_flat_of_surjective _
    have e : pullback.fst p' (M.j ∣_ V) ≫ U.ι ≫ π = (pullback.snd p' (M.j ∣_ V) ≫ (M.j ⁻¹ᵁ V).ι) ≫ M.j := by
      rw [← hp, pullback.condition_assoc, morphismRestrict_ι, Category.assoc]
    obtain ⟨c, hc₁, hc₂⟩ := H _ (pullback.fst p' (M.j ∣_ V)) (pullback.snd p' (M.j ∣_ V) ≫ (M.j ⁻¹ᵁ V).ι ≫ A.hom)
      (by rw [← Category.assoc, e, Category.assoc, M.j_hom]; simp only [Category.assoc])
    rw [e, cancel_mono] at hc₁
    rw [← cancel_epi (pullback.snd p' (M.j ∣_ V)), ← pullback.condition_assoc, hq, ← hc₂, hc₁, Category.assoc]
end GlobalTheory.SS.GenProj
