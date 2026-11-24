-- Prove2me | solution 1 for GlobalTheory.SS.Height.centre_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:17:59.780624+00:00
-- url     : https://prove2.me/submissions/f5ab1008-870e-41ae-ae82-8b7d9c865744

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperScheme
import Theorems.Thm_GlobalTheory_SS_Height_ext_unique
import Theorems.Thm_GlobalTheory_AffinePointValues_fromSpec_comp
import Theorems.Thm_GlobalTheory_AffinePointValues_specMap_appLE_fromSpec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Height
open IsLocalRing
variable {k K : Type} [Field k] [Field K] [Algebra k K]
namespace GlobalTheory.SS.Height
theorem _root_.solution (Pl : Places k K) (B : Over (Sp k)) [IsProper B.hom]
    (x : Over.mk (spMap (algebraMap k K)) ⟶ B) (b : ∀ i, Sp (Pl.O i) ⟶ B.left)
    (hb : ∀ i, spMap (Pl.O i).subtype ≫ b i = x.left) (U : B.left.Opens) (hU : x.left (closedPoint K) ∈ U) :
    {i | b i (closedPoint (Pl.O i)) ∉ U}.Finite := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := B.left.isBasis_affineOpens.exists_subset_of_mem_open hU U.isOpen
  have hx : ⊤ ≤ x.left ⁻¹ᵁ V := (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of K) x.left hxV).ge
  let ψ : Γ(B.left, V) ⟶ CommRingCat.of K := x.left.appLE V ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  have hψ : Spec.map ψ ≫ hV.fromSpec = x.left := AffinePointValues.specMap_appLE_fromSpec hV _ hx
  let c : CommRingCat.of k ⟶ Γ(B.left, V) := (Scheme.ΓSpecIso (.of k)).inv ≫ B.hom.appLE ⊤ V le_top
  have hc : c ≫ ψ = CommRingCat.ofHom (algebraMap k K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← AffinePointValues.fromSpec_comp hV B.hom le_top, ← Category.assoc, hψ]
    exact Over.w x
  have hft : c.hom.FiniteType := (B.hom.finiteType_appLE (isAffineOpen_top _) hV le_top).comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  letI := c.hom.toAlgebra
  obtain ⟨T, hT⟩ := hft.out
  have hfin : ∀ a : K, {i | a ∉ Pl.O i}.Finite := fun a => by
    by_cases ha : a = 0
    · simp [ha]
    · refine (Pl.fin (Units.mk0 a ha)).subset fun i hi h0 => hi ?_
      exact (Pl.mem i (Units.mk0 a ha)).2 (le_of_eq (Eq.symm h0))
  refine (T.finite_toSet.biUnion fun a _ => hfin (ψ.hom a)).subset fun i hi => ?_
  by_contra hn
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hn
  have hall : ∀ a, ψ.hom a ∈ Pl.O i := fun a => by
    have ha : a ∈ Algebra.adjoin k (T : Set Γ(B.left, V)) := hT ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem a h => exact hn a h
    | algebraMap r => exact (congrArg (fun q => q.hom r) hc) ▸ Pl.const i r
    | add a a' _ _ h h' => rw [map_add]; exact add_mem h h'
    | mul a a' _ _ h h' => rw [map_mul]; exact mul_mem h h'
  have e : b i = Spec.map (CommRingCat.ofHom (ψ.hom.codRestrict (Pl.O i) hall)) ≫ hV.fromSpec := by
    refine ext_unique _ B ?_
    rw [hb, ← hψ, ← Category.assoc, ← Spec.map_comp]
    rfl
  refine hi (hVU ?_)
  rw [e]
  exact hV.range_fromSpec.le ⟨_, rfl⟩
end GlobalTheory.SS.Height
