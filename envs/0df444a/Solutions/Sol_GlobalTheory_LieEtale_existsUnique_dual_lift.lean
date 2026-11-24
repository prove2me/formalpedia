-- Prove2me | solution 1 for GlobalTheory.LieEtale.existsUnique_dual_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:22:38.931853+00:00
-- url     : https://prove2.me/submissions/24e239b1-0e93-4793-aa9b-8afa432e586a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTangentLift
import Theorems.Thm_GlobalTheory_exists_isAffineOpen_pair
import Theorems.Thm_GlobalTheory_exists_lift_of_smooth_of_isAffineOpen
import Theorems.Thm_GlobalTheory_lift_ext_of_unramified
import Theorems.Thm_GlobalTheory_range_subset_opens_of_isLocalRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LieEtale
namespace GlobalTheory.LieEtale
theorem _root_.solution {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] {k : Type} [Field k]
    (s : Sp (DualNumber k) ⟶ Y) (x₀ : Sp k ⟶ X)
    (h : x₀ ≫ f = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ s) :
    ∃! x : Sp (DualNumber k) ⟶ X,
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x = x₀ ∧ x ≫ f = s := by
  let π : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hsq : ∀ a b : DualNumber k, a.fst = 0 → b.fst = 0 → a * b = 0 := fun a b ha hb => by
    ext <;> simp [ha, hb]
  have hnil : IsNilpotent (RingHom.ker π.hom) :=
    ⟨2, by
      rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      exact fun a ha b hb => hsq a b ha hb⟩
  have hj : RingHom.ker π.hom ≤ Ideal.jacobson ⊥ := fun a ha =>
    Ideal.mem_sInf.mpr fun {J} hJ => hJ.2.isPrime.mem_of_pow_mem 2 (by
      rw [pow_two, hsq a a ha ha]; exact J.zero_mem)
  refine existsUnique_of_exists_of_unique ?_ fun x₁ x₂ h₁ h₂ =>
    lift_ext_of_unramified f π hπ hj (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  have : IsLocalHom π.hom := ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    exists_isAffineOpen_pair f (x₀ (IsLocalRing.closedPoint k)) (O := ⊤) trivial
  refine exists_lift_of_smooth_of_isAffineOpen f hU hV hVU π s x₀ h
    (range_subset_opens_of_isLocalRing s ?_) (range_subset_opens_of_isLocalRing x₀ hxV) ?_
  · have e : f (x₀ (IsLocalRing.closedPoint k)) = s (Spec.map π (IsLocalRing.closedPoint k)) :=
      congr($h (IsLocalRing.closedPoint k))
    rw [← Spec_closedPoint (f := π), ← e]
    exact hVU hxV
  · intro R A _ _ _ _ _ _ π' hπ' φ
    have hs : Function.Surjective π' := fun c => (hπ c).imp fun b hb => (hπ' b).trans hb
    have hk : IsNilpotent (RingHom.ker (π' : CommRingCat.of (DualNumber k) →+* CommRingCat.of k)) := by
      convert hnil using 2
      exact RingHom.ext hπ'
    exact ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective φ π' hs hk⟩
end GlobalTheory.LieEtale
