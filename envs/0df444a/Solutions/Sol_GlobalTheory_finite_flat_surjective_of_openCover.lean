-- Prove2me | solution 1 for GlobalTheory.finite_flat_surjective_of_openCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:35:07.573648+00:00
-- url     : https://prove2.me/submissions/657a60dc-5661-49a1-a39d-30818f118b88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteFlatSurjectiveClosedSubschemeOfOpenCover
import Theorems.Thm_GlobalTheory_exists_isPullback_of_factor_iff
import Theorems.Thm_GlobalTheory_of_isPullback_openCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option backward.isDefEq.respectTransparency.types false
namespace GlobalTheory
theorem _root_.solution : ∀ (X T₀ : Scheme.{0}) (p : X ⟶ T₀) (ι : Type) (V : ι → T₀.Opens), iSup V = ⊤ → ∀ (Xi : ι → Scheme.{0}) (m : ∀ i, Xi i ⟶ X) (q : ∀ i, Xi i ⟶ (V i).toScheme), (∀ i, IsPullback (m i) (q i) p (V i).ι) → ∀ (B : Scheme.{0}) (b : B ⟶ X), IsClosedImmersion b → ∀ (A : ι → Scheme.{0}) (a : ∀ i, A i ⟶ Xi i), (∀ i, IsClosedImmersion (a i)) → (∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i), (∃ z : Y ⟶ B, z ≫ b = g ≫ m i) ↔ (∃ z : Y ⟶ A i, z ≫ a i = g)) → (∀ i, IsFinite (a i ≫ q i) ∧ Flat (a i ≫ q i) ∧ Surjective (a i ≫ q i)) → IsFinite (b ≫ p) ∧ Flat (b ≫ p) ∧ Surjective (b ≫ p) := by
  intro X T₀ p ι V hV Xi m q hpb B b hb A a ha hrep hP
  have H : ∀ i, ∃ k : A i ⟶ B, IsPullback k (a i ≫ q i) (b ≫ p) (V i).ι := by
    intro i
    have := ha i
    obtain ⟨k, hk⟩ := exists_isPullback_of_factor_iff (m i) b (a i) (hrep i)
    exact ⟨k, hk.paste_vert (hpb i)⟩
  choose k hk using H
  have hfin : IsZariskiLocalAtTarget @IsFinite.{0} :=
    inferInstance
  have hflat : IsZariskiLocalAtTarget @Flat.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0})
  exact ⟨of_isPullback_openCover @IsFinite _ V hV A k _ hk (fun i => (hP i).1),
    of_isPullback_openCover @Flat _ V hV A k _ hk (fun i => (hP i).2.1),
    of_isPullback_openCover @Surjective _ V hV A k _ hk (fun i => (hP i).2.2)⟩
end GlobalTheory
