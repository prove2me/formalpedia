-- Prove2me | solution 1 for GlobalTheory.geometricallyConnected_genericFibre_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:58:36.261607+00:00
-- url     : https://prove2.me/submissions/bf4befac-7615-4fdd-8726-ecb8c7ded701

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsAffineOpenDisjointImageOfIsConstructible
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedGenericFibreOfDense
import Theorems.Thm_GlobalTheory_GenericConnected_exists_spread
import Theorems.Thm_GlobalTheory_GenericConnected_exists_mem_of_genericPoint_mem
import Theorems.Thm_GlobalTheory_GenericConnected_not_mem_image_inter
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_torusCoord_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.torusCoord_apply



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
open GenericConnected
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X S : Scheme.{0}) [IsIntegral S] [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (Sg : Set S), Dense Sg → (∀ x ∈ Sg, GeometricallyConnected (f.fiberToSpecResidueField x)) → GeometricallyConnected (f.fiberToSpecResidueField (genericPoint S)) := by
  intro X S _ _ f _ _ Sg hSg hc
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have H : IsPullback (fst ≫ f.fiberι _) snd f (y ≫ S.fromSpecResidueField (genericPoint S)) :=
    h.paste_horiz (.of_hasPullback f (S.fromSpecResidueField (genericPoint S)))
  have hy (z : Spec (.of K)) : (y ≫ S.fromSpecResidueField (genericPoint S)) z = genericPoint S := by
    rw [Scheme.Hom.comp_apply]
    exact (S.range_fromSpecResidueField _).le ⟨_, rfl⟩
  generalize y ≫ S.fromSpecResidueField (genericPoint S) = k at H hy
  generalize fst ≫ f.fiberι _ = g at H
  have hne : Nonempty Z := by
    have h1 : genericPoint S ∈ f '' Set.univ := by
      by_contra h0
      obtain ⟨x, hx, hx'⟩ := exists_mem_of_genericPoint_mem (𝟙 S) (C := (f '' Set.univ)ᶜ)
        (f.isConstructible_image .univ).compl hSg ⟨_, h0, rfl⟩
      have := hc x hx'
      have : ConnectedSpace (f.fiber x) :=
        GeometricallyConnected.connectedSpace_of_subsingleton (f.fiberToSpecResidueField x)
      obtain ⟨w⟩ : Nonempty (f.fiber x) := inferInstance
      exact hx ⟨_, trivial, (f.range_fiberι x).le ⟨w, rfl⟩⟩
    obtain ⟨x, -, hx⟩ := h1
    obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback H x (default : PrimeSpectrum K)
      (hx.trans (hy _).symm)
    exact ⟨z⟩
  suffices PreconnectedSpace Z from ⟨hne⟩
  refine ⟨fun U V hU hV hUV ⟨u, _, hu⟩ ⟨v, _, hv⟩ ↦ ?_⟩
  by_contra hemp
  obtain ⟨_, ⟨W, hW : IsAffineOpen W, rfl⟩, hηW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint S)) isOpen_univ
  have : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hr : Set.range k ⊆ Set.range hW.fromSpec := by
    rintro _ ⟨z, rfl⟩
    rw [hW.range_fromSpec, hy]
    exact hηW
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec k hr)
  have hk : Spec.map φ ≫ hW.fromSpec = k := by rw [hφ, IsOpenImmersion.lift_fac]
  algebraize [φ.hom]
  obtain ⟨T, a, _, _, b, π, U', V', hb, hπ, hsup, hinf, hU', hV'⟩ :=
    exists_spread (R := Γ(S, W)) (A := K) hW.fromSpec (p := f) (g := g) (q := snd) (by
      rw [← hk] at H; exact H) ⟨U, hU⟩ ⟨V, hV⟩
      (by ext; simpa using hUV trivial)
      (by ext z; simpa using fun h1 h2 ↦ hemp ⟨z, trivial, h1, h2⟩)
  let t : T ⟶ S := a ≫ hW.fromSpec
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  have : IsNoetherian T := {}
  have : QuasiCompact t := inferInstance
  have : IsLocallyNoetherian (pullback f t) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f t)
  have : CompactSpace ↥(pullback f t) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f t)
  have : IsNoetherian (pullback f t) := {}
  have hcons (O : (pullback f t).Opens) :
      Topology.IsConstructible (pullback.snd f t '' O) :=
    (pullback.snd f t).isConstructible_image
      (IsRetrocompact.isConstructible O.2 fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _)
  have hmem (O : (pullback f t).Opens) (z : Z) (hz : z ∈ π ⁻¹ᵁ O) :
      b (default : PrimeSpectrum K) ∈ pullback.snd f t '' O := by
    refine ⟨π z, hz, ?_⟩
    rw [← Scheme.Hom.comp_apply, hπ, Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim (α := PrimeSpectrum K) _ _
  obtain ⟨x, hx, hx'⟩ := exists_mem_of_genericPoint_mem t ((hcons U').inter (hcons V')) hSg
    ⟨b (default : PrimeSpectrum K), ⟨hmem U' u (hU' ▸ hu), hmem V' v (hV' ▸ hv)⟩, by
      have hbt : b ≫ t = k := by rw [← Category.assoc, hb]; exact hk
      exact (Scheme.Hom.comp_apply b t _).symm.trans ((congr($hbt _)).trans (hy _))⟩
  exact not_mem_image_inter f t x (hc _ hx') U' V' hsup hinf hx
end GlobalTheory
