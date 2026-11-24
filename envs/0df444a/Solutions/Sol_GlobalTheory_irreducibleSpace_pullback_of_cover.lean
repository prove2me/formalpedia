-- Prove2me | solution 1 for GlobalTheory.irreducibleSpace_pullback_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:33.637907+00:00
-- url     : https://prove2.me/submissions/aa61983b-6e44-4403-8de7-9bd152658948

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpacePullbackFieldOfIrreducibleCover
import Theorems.Thm_GlobalTheory_irreducibleSpace_of_open_cover_meeting
import Theorems.Thm_GlobalTheory_scheme_homOfLE_apply_mk
import Theorems.Thm_GlobalTheory_surjective_spMap_of_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {F : Type} [Field F] {X : Scheme.{0}} (h : X ⟶ Sp F) (k : Type)
    [Field k] (f : F →+* k) (U : X.Opens),
    IsIrreducible (U : Set X) →
    (∀ y ∈ U, ∃ V : X.Opens, V ≤ U ∧ y ∈ V ∧ IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f))) →
    IrreducibleSpace ↑(pullback (U.ι ≫ h) (spMap f)) := by
  intro F _ X h k _ f U hU hV
  haveI := surjective_spMap_of_field f
  set q := pullback.fst (U.ι ≫ h) (spMap f) with hq
  have hqs : Function.Surjective q := q.surjective

  have key : ∀ (V : X.Opens) (hVU : V ≤ U), IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f)) →
      IsOpen (Set.range (pullback.snd (X.homOfLE hVU) q)) ∧
      IsPreirreducible (Set.range (pullback.snd (X.homOfLE hVU) q)) ∧
      ∀ p, U.ι (q p) ∈ V → p ∈ Set.range (pullback.snd (X.homOfLE hVU) q) := by
    intro V hVU hirrV
    refine ⟨(pullback.snd (X.homOfLE hVU) q).isOpenEmbedding.isOpen_range, ?_, ?_⟩
    · let e : pullback (V.ι ≫ h) (spMap f) ≅ pullback (X.homOfLE hVU) q :=
        pullback.congrHom (by rw [← X.homOfLE_ι hVU, Category.assoc]) rfl ≪≫
          (pullbackRightPullbackFstIso (U.ι ≫ h) (spMap f) (X.homOfLE hVU)).symm
      haveI : IrreducibleSpace ↑(pullback (X.homOfLE hVU) q) :=
        (Scheme.homeoOfIso e).surjective.irreducibleSpace (Scheme.homeoOfIso e).continuous
      rw [← Set.image_univ]
      exact (PreirreducibleSpace.isPreirreducible_univ (X := ↑(pullback (X.homOfLE hVU) q))).image _
        (pullback.snd (X.homOfLE hVU) q).continuous.continuousOn
    · intro p hp
      rw [Scheme.Pullback.range_snd]
      refine ⟨⟨U.ι (q p), hp⟩, ?_⟩
      show (X.homOfLE hVU) ⟨U.ι (q p), hp⟩ = q p
      rw [scheme_homOfLE_apply_mk]
      rfl
  have hUne : (U : Set X).Nonempty := hU.nonempty
  obtain ⟨y₀, hy₀⟩ := hUne
  obtain ⟨p₀, -⟩ := hqs ⟨y₀, hy₀⟩
  haveI : Nonempty ↑(pullback (U.ι ≫ h) (spMap f)) := ⟨p₀⟩
  let S : Set (Set ↑(pullback (U.ι ≫ h) (spMap f))) :=
    {W | ∃ (V : X.Opens) (hVU : V ≤ U), IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f)) ∧
      (V : Set X).Nonempty ∧ W = Set.range (pullback.snd (X.homOfLE hVU) q)}
  refine irreducibleSpace_of_open_cover_meeting S ?_ ?_ ?_ ?_
  · rintro W ⟨V, hVU, hi, -, rfl⟩
    exact (key V hVU hi).1
  · rintro W ⟨V, hVU, hi, -, rfl⟩
    exact (key V hVU hi).2.1
  · intro p
    have hyU : U.ι (q p) ∈ U := (q p).2
    obtain ⟨V, hVU, hyV, hi⟩ := hV _ hyU
    exact ⟨_, ⟨V, hVU, hi, ⟨_, hyV⟩, rfl⟩, (key V hVU hi).2.2 p hyV⟩
  · rintro W ⟨V, hVU, hi, ⟨a, ha⟩, rfl⟩ W' ⟨V', hVU', hi', ⟨b, hb⟩, rfl⟩
    obtain ⟨z, hzU, hzV, hzV'⟩ :=
      hU.2 (V : Set X) (V' : Set X) V.isOpen V'.isOpen ⟨a, hVU ha, ha⟩ ⟨b, hVU' hb, hb⟩
    obtain ⟨p, hp⟩ := hqs ⟨z, hzU⟩
    have hpz : U.ι (q p) = z := by rw [hp]; rfl
    exact ⟨p, (key V hVU hi).2.2 p (hpz ▸ hzV), (key V' hVU' hi').2.2 p (hpz ▸ hzV')⟩
end GlobalTheory
