-- Prove2me | solution 1 for GlobalTheory.QuasiAffineTorus.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:41:39.511846+00:00
-- url     : https://prove2.me/submissions/025bcc8c-b6e5-42bd-a1d4-0efda34a67cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiAffineSubgroupContainingTorusEqTorus
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_exists_weight_decomposition
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_exists_point_of_weights
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_ev_comp
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_ev_const
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_ev_ne_zero
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_eq_of_ev_eq
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_exists_pt_mem_open
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_eq_zero_of_ev
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_exists_const_of_invariant
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_exists_expansion
import Theorems.Thm_GlobalTheory_isIntegral_of_smooth_of_geometricallyConnected
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_GlobalTheory_torusCoord_apply
import Theorems.Thm_GlobalTheory_torusExtension_smooth_geometricallyConnected
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_torus_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.restrictPoints_val
attribute [local simp] GlobalTheory.torusCoord_apply



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.QuasiAffineTorus
open RationalPoint
namespace GlobalTheory.QuasiAffineTorus
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G →  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q → IsAbelianScheme B → ∀ (N : Over (Sp k)) [GrpObj N] (ν : N ⟶ G) (i' : splitTorus (Sp k) X ⟶ N), SmConn N → IsMonHom ν → IsClosedImmersion ν.left → i' ≫ ν = i → (∀ x : N.left, ∃ f : Γ(N.left, ⊤), x ∈ N.left.basicOpen f ∧ IsAffineOpen (N.left.basicOpen f)) → ∀ x : (𝟙_ (Over (Sp k)) ⟶ N), ∃ t : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X), t ≫ i = x ≫ ν := by
  intro k _ _ G _ hG X _ _ _ B _ i q hq hB N _ ν i' hN hν hcl hi haff x
  obtain ⟨hi₀, hq₀, hfl, hsu, haf, hk, -⟩ := hq
  obtain ⟨hcomm, hsm, -, hqc, hgc⟩ := hN
  have := hB.proper
  have : Smooth q.left := (torusExtension_smooth_geometricallyConnected G
    ⟨X, B, hB, q, hq₀, hfl, hsu, inferInstance, i, hi₀, hk⟩).1
  have : Smooth (splitTorus (Sp k) X).hom := (ReciprocityTheory.ChartRestriction.G.H1.torus_dim (Sp k) X).smooth
  have : IsIntegral N.left := isIntegral_of_smooth_of_geometricallyConnected N.hom
  have : CompactSpace N.left := QuasiCompact.compactSpace_of_compactSpace N.hom
  have : N.left.IsQuasiAffine := .of_forall_exists_mem_basicOpen _ fun y =>
    (haff y).imp fun _ h => h.symm
  have : Mono ν := Over.mono_of_mono_left ν
  let τ : (Multiplicative X →* kˣ) →* (𝟙_ (Over (Sp k)) ⟶ N) :=
    MonoidHom.mk' (fun t => torusPt k X t ≫ i') fun s t => by
      rw [← cancel_mono ν]
      simp only [MonObj.mul_comp, Category.assoc, hi, map_mul]
  let E : Γ(N.left, ⊤) →+* ((𝟙_ (Over (Sp k)) ⟶ N) → k) := RingHom.pi fun y => ev y
  have hE : ∀ f, E f = 0 → f = 0 := fun f h => eq_zero_of_ev fun y => congrFun h y
  let A : Subalgebra k ((𝟙_ (Over (Sp k)) ⟶ N) → k) :=
    { E.range.toSubsemiring with
      algebraMap_mem' := fun r => ⟨const N r, funext fun y => ev_const y r⟩ }
  have hA : ∀ (g : N ⟶ N), ∀ f ∈ A, (fun y => f (y ≫ g)) ∈ A := by
    rintro g _ ⟨f, rfl⟩
    exact ⟨g.left.appTop.hom f, rfl⟩
  have htr : ∀ f ∈ A, ∀ t, (fun y => f (τ t * y)) ∈ A := fun f hf t => by
    convert hA ((toUnit N ≫ τ t) * 𝟙 N) f hf using 3 with y
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit N) (𝟙 _),
      Category.id_comp]
  obtain ⟨t, ht⟩ := exists_point_of_weights τ A
    (by
      rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩ h
      rw [← map_mul] at h
      exact (mul_eq_zero.1 (hE _ h)).imp (fun e => by rw [e, map_zero]) fun e => by rw [e, map_zero])
    (fun f hf => by
      convert hA (𝟙 N)⁻¹ f hf using 3 with y
      rw [GrpObj.comp_inv, Category.comp_id])
    (by
      rintro _ ⟨f, rfl⟩ h y
      obtain ⟨r, rfl⟩ := exists_const_of_invariant i q ν i' hk hi f fun s z => by
        obtain ⟨s, rfl⟩ := (torusPt k X).surjective s
        exact h s z
      exact (ev_const y r).trans (ev_const 1 r).symm) x
  refine ⟨torusPt k X t, ?_⟩
  rw [← hi, ← Category.assoc]
  congr 1
  refine eq_of_ev_eq fun f => ?_
  obtain ⟨V, hxV, hV⟩ : ∃ V : N.left.Opens, pt x ∈ V ∧ IsAffineOpen V := by
    obtain ⟨f₀, h₀⟩ := haff (pt x)
    exact ⟨_, h₀⟩
  let U : Over (Sp k) := Over.mk (V.ι ≫ N.hom)
  let j : U ⟶ N := Over.homMk V.ι rfl
  have : IsAffine U.left := hV
  have : LocallyOfFiniteType U.hom := inferInstanceAs (LocallyOfFiniteType (V.ι ≫ N.hom))
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have : IsReduced U.left := isReduced_of_isOpenImmersion V.ι
  obtain ⟨S, a, ha⟩ := exists_expansion (X := X)
    (((fst _ U ≫ i') * (snd _ U ≫ j)).left.appTop.hom f)
  obtain ⟨g, hg, hs⟩ := exists_weight_decomposition τ A
    (fun u : 𝟙_ (Over (Sp k)) ⟶ U => u ≫ j)
    (by
      rintro _ ⟨f, rfl⟩ h
      have h1 : f = 0 := by
        rw [← basicOpen_eq_bot_iff]
        by_contra hne
        obtain ⟨z, hz1, hz2⟩ := nonempty_preirreducible_inter (N.left.basicOpen f).isOpen V.isOpen
          (Set.nonempty_iff_ne_empty.2 fun e => hne (SetLike.coe_injective e)) ⟨_, hxV⟩
        obtain ⟨u, hu⟩ := exists_pt_mem_open (N := U) (j.left ⁻¹ᵁ N.left.basicOpen f).isOpen
          ⟨⟨z, hz2⟩, hz1⟩
        exact ev_ne_zero (u ≫ j) hu (h u)
      rw [h1, map_zero])
    htr (f := E f) ⟨f, rfl⟩ S (fun χ u => ev u (a χ)) fun u s => by
      rw [← ha, ← ev_comp, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
      rfl
  change E f (τ t) = E f x
  rw [hs, Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun χ _ => (ht _ (hg χ).1 _ (hg χ).2).symm
end GlobalTheory.QuasiAffineTorus
