-- Prove2me | solution 1 for GlobalTheory.CoverO.restrict_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:58:43.130386+00:00
-- url     : https://prove2.me/submissions/5f461193-12d9-4407-8c21-859a686b9f67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechPullOneBijectiveLatticeCover
import Theorems.Thm_GlobalTheory_CoverO_restrict_pull1_bijective_of_adj
import Theorems.Thm_GlobalTheory_CoverO_restrict_cover_affine_pull1_bijective
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_comp
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_eq_of_natTrans
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CoverO
namespace GlobalTheory.CoverO
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (CoefMap.restrict (OAff s) hU.functor.op).pull1 := by
  intro R _ X s J _ _ U hU hinf hcov
  classical
  haveI := Fintype.ofFinite J
  let B : Type := {V : X.affineOpens // ∃ i, V.1 ≤ (U i).1}
  have hne : ∀ V : B, (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).Nonempty := fun V => by
    obtain ⟨i, hi⟩ := V.2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  let σ : B → J := fun V => (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).inf' (hne V) id
  let u : J → B := fun i => ⟨U i, i, le_rfl⟩
  have hσ : ∀ V : B, V.1.1 ≤ (U (σ V)).1 := fun V =>
    Finset.inf'_induction (p := fun i => V.1.1 ≤ (U i).1) (hne V) id
      (fun a ha b hb => by rw [hinf]; exact le_inf ha hb) fun i hi => (Finset.mem_filter.1 hi).2
  have gc : GaloisConnection σ u := fun V i =>
    ⟨fun h => (hσ V).trans (hU h), fun h =>
      Finset.inf'_le (s := Finset.univ.filter fun i : J => V.1.1 ≤ (U i).1) (id : J → J)
        (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)⟩
  let incl : Bᵒᵖ ⥤ AffOp X := (Monotone.functor (f := (Subtype.val : B → X.affineOpens)) fun _ _ h ↦ h).op
  have b1 : Function.Bijective (CoefMap.restrict (OAff s) incl).pull1 :=
    restrict_cover_affine_pull1_bijective R X s J (fun i => (U i).1) hcov
  have b2 := restrict_pull1_bijective_of_adj (incl ⋙ OAff s) gc.monotone_u.functor.op
    gc.monotone_l.functor.op gc.adjunction.op
  have e : ∀ c, (CoefMap.restrict (OAff s) hU.functor.op).pull1 c =
      (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op).pull1
        ((CoefMap.restrict (OAff s) incl).pull1 c) := fun c =>
    (CoefMap.pullCohomologyOne_eq_of_natTrans (CoefMap.restrict (OAff s) hU.functor.op)
      ((CoefMap.restrict (OAff s) incl).comp (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op))
      (𝟙 _) (fun T b => mp_id (OAff s) _ b) c).trans (CoefMap.pullCohomologyOne_comp _ _ c)
  have := b2.comp b1
  exact (funext e : _ = _) ▸ this
end GlobalTheory.CoverO
