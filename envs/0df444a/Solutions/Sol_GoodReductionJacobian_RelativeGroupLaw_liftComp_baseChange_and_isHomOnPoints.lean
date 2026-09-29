-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.liftComp_baseChange_and_isHomOnPoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f8f9ce79-e482-56d4-a15a-26a3ce6b9f88

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_liftComp_baseChange_and_isHomOnPoints

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) :
    (∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
        (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
        (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
        (φ χ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s) (hχ : χ ≫ f = pullback.snd f s ≫ s),
      pullback.lift (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [Category.assoc, hs]; exact pullback.condition) ≫ χ) (pullback.snd f s'')
          (by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs]) ≫
        (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ) =
      pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [Category.assoc, hs]; exact pullback.condition) ≫
        (pullback.lift χ (pullback.snd f s) hχ ≫ φ)) ∧
    (∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ χ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s) (hχ : χ ≫ f = pullback.snd f s ≫ s),
      (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
        pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ =
          (L.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
        pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ χ =
          (L.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ χ, by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ χ, by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      ∀ (ω : pullback f s ⟶ A) (hω : ω ≫ f = pullback.snd f s ≫ s),
        ω = pullback.lift χ (pullback.snd f s) hχ ≫ φ →
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
          pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ ω =
            (L.mul (t' ≫ s)
              ⟨pullback.lift P.1 t' P.2 ≫ ω, by rw [Category.assoc, hω, ← Category.assoc, pullback.lift_snd]⟩
              ⟨pullback.lift Q.1 t' Q.2 ≫ ω, by rw [Category.assoc, hω, ← Category.assoc, pullback.lift_snd]⟩).1)) := by
  refine ⟨?_, ?_⟩
  · intro S' S'' _ _ ψ s s'' hs φ χ hφ hχ
    have key : pullback.lift (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
          (by rw [Category.assoc, hs]; exact pullback.condition) ≫ χ) (pullback.snd f s'')
          (by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs]) ≫
        pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
          (by rw [Category.assoc, hs]; exact pullback.condition) =
        pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
          (by rw [Category.assoc, hs]; exact pullback.condition) ≫ pullback.lift χ (pullback.snd f s) hχ := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst]
      · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    simpa only [Category.assoc] using congrArg (· ≫ φ) key
  · intro S' _ s φ χ hφ hχ Hφ Hχ ω hω hωeq T t' P Q
    subst hωeq
    have liftE : ∀ (R' : T ⟶ A) (hR : R' ≫ f = t' ≫ s),
        pullback.lift R' t' hR ≫ pullback.lift χ (pullback.snd f s) hχ =
          pullback.lift (pullback.lift R' t' hR ≫ χ) t' (by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd]) := by
      intro R' hR
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst]
      · simp only [Category.assoc, pullback.lift_snd]
    rw [← Category.assoc, liftE]
    have step : pullback.lift (pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ χ) t'
          (by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd]) =
        pullback.lift (L.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ χ, by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ χ, by rw [Category.assoc, hχ, ← Category.assoc, pullback.lift_snd]⟩).1 t'
          (L.mul (t' ≫ s) _ _).2 := by
      congr 1
      exact Hχ T t' P Q
    rw [step, Hφ T t' _ _]
    congr 2
    · apply Subtype.ext
      dsimp only
      simpa only [Category.assoc] using (congrArg (· ≫ φ) (liftE P.1 P.2)).symm
    · apply Subtype.ext
      dsimp only
      simpa only [Category.assoc] using (congrArg (· ≫ φ) (liftE Q.1 Q.2)).symm

end S_GoodReductionJacobian_RelativeGroupLaw_liftComp_baseChange_and_isHomOnPoints
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_liftComp_baseChange_and_isHomOnPoints (solution)
