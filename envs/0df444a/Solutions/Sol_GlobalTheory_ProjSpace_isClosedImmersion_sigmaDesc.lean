-- Prove2me | solution 1 for GlobalTheory.ProjSpace.isClosedImmersion_sigmaDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:05:27.254114+00:00
-- url     : https://prove2.me/submissions/97d7125d-e31e-45e3-8865-8f4f392a4313

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionSigmaDesc
import Theorems.Thm_GlobalTheory_ProjSpace_gradedMap_apply
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_appLinearBase_apply
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ProjSpace.gradedMap_apply
attribute [local simp] GlobalTheory.QCoh.Qcqs.appLinearBase_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply


section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG IsProjOver)
namespace GlobalTheory.ProjSpace
private lemma isClosedEmbedding_sigma_desc_of_pairwise_disjoint_range {ι : Type} [Finite ι] {Z : ι → Type*}
    [∀ i, TopologicalSpace (Z i)] {W : Type*} [TopologicalSpace W] (g : ∀ i, Z i → W)
    (hg : ∀ i, Topology.IsClosedEmbedding (g i))
    (h : Pairwise fun i j => Disjoint (Set.range (g i)) (Set.range (g j))) :
    Topology.IsClosedEmbedding (fun p : Σ i, Z i => g p.1 p.2) := by
  refine .of_continuous_injective_isClosedMap ?_ ?_ ?_
  · exact continuous_sigma fun i => (hg i).continuous
  · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    by_cases hij : i = j
    · subst hij
      obtain rfl := (hg i).injective hxy
      rfl
    · exact absurd hxy ((h hij).ne_of_mem ⟨x, rfl⟩ ⟨y, rfl⟩)
  · intro C hC
    have hC' : (fun p : Σ i, Z i => g p.1 p.2) '' C = ⋃ i, g i '' (_root_.Sigma.mk i ⁻¹' C) := by
      ext w
      simp
    rw [hC']
    exact isClosed_iUnion_of_finite fun i => (hg i).isClosedMap _ (hC.preimage continuous_sigmaMk)
end GlobalTheory.ProjSpace
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG IsProjOver)
open GlobalTheory GlobalTheory.ProjSpace
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
namespace GlobalTheory.ProjSpace
namespace _root_.GlobalTheory.ProjSpace
theorem _root_.solution {ι : Type} [Finite ι]
    {X : ι → Scheme.{0}} {Y : Scheme.{0}}
    (f : ∀ i, X i ⟶ Y) (hf : ∀ i, IsClosedImmersion (f i))
    (h : Pairwise fun i j => Disjoint (Set.range (f i)) (Set.range (f j))) :
    IsClosedImmersion (Sigma.desc f) := by
  have hsurj : SurjectiveOnStalks (Sigma.desc f) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @SurjectiveOnStalks) fun i => (hf i).toSurjectiveOnStalks
  have key : ⇑(Sigma.desc f) ∘ AlgebraicGeometry.sigmaMk X = fun p => f p.1 p.2 := by
    funext ⟨i, x⟩
    rw [Function.comp_apply, AlgebraicGeometry.sigmaMk_mk, ← Scheme.Hom.comp_apply, Sigma.ι_desc]
  have hce : Topology.IsClosedEmbedding (Sigma.desc f) := by
    have e := isClosedEmbedding_sigma_desc_of_pairwise_disjoint_range (fun i => ⇑(f i))
      (fun i => (hf i).isClosedEmbedding) h
    rw [← key] at e
    have hsplit : ⇑(Sigma.desc f) =
        (⇑(Sigma.desc f) ∘ AlgebraicGeometry.sigmaMk X) ∘ (AlgebraicGeometry.sigmaMk X).symm := by
      funext y
      simp
    rw [hsplit]
    exact e.comp (AlgebraicGeometry.sigmaMk X).symm.isClosedEmbedding
  haveI : IsPreimmersion (Sigma.desc f) := (isPreimmersion_iff _).2 ⟨hsurj, hce.isEmbedding⟩
  exact .of_isPreimmersion _ hce.isClosed_range
end _root_.GlobalTheory.ProjSpace
end GlobalTheory.ProjSpace
