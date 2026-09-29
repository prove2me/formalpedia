-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isHomOnPoints_baseChange_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/fc5d7f27-3394-5513-a1a2-fee9f585c5d6

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isHomOnPoints_baseChange_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) :
    ∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
      (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
      (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
      (φ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s)
      (φ'' : pullback f s'' ⟶ A) (hφ'' : φ'' ≫ f = pullback.snd f s'' ≫ s''),
      φ'' = pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ →
      (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
        pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ =
          (L.mul (t' ≫ s)
            ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
      (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S'')) (P Q : SchemeHomOver (t' ≫ s'') f),
        pullback.lift (L.mul (t' ≫ s'') P Q).1 t' (L.mul (t' ≫ s'') P Q).2 ≫ φ'' =
          (L.mul (t' ≫ s'')
            ⟨pullback.lift P.1 t' P.2 ≫ φ'', by rw [Category.assoc, hφ'', ← Category.assoc, pullback.lift_snd]⟩
            ⟨pullback.lift Q.1 t' Q.2 ≫ φ'', by rw [Category.assoc, hφ'', ← Category.assoc, pullback.lift_snd]⟩).1) := by
  intro S' S'' _ _ ψ s s'' hs φ hφ φ'' hφ'' hG H T t' P Q
  subst hG
  have e : (t' ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ s = t' ≫ s'' := by rw [Category.assoc, hs]
  have liftG : ∀ (R' : T ⟶ A) (hR : R' ≫ f = t' ≫ s''),
      pullback.lift R' t' hR ≫ pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
          (by rw [Category.assoc, hs]; exact pullback.condition) =
        pullback.lift R' (t' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [e]; exact hR) := by
    intro R' hR
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  have gen : ∀ {u v : T ⟶ Spec (CommRingCat.of R)} (huv : v = u) (X Y : SchemeHomOver u f),
      (L.mul u X Y).1 = (L.mul v ⟨X.1, X.2.trans huv.symm⟩ ⟨Y.1, Y.2.trans huv.symm⟩).1 := by
    intro u v huv X Y
    subst huv
    rfl
  rw [← Category.assoc, liftG]
  have step : pullback.lift (L.mul (t' ≫ s'') P Q).1 (t' ≫ Spec.map (CommRingCat.ofHom ψ)) (by rw [e]; exact (L.mul (t' ≫ s'') P Q).2) =
      pullback.lift (L.mul ((t' ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ s) ⟨P.1, P.2.trans e.symm⟩ ⟨Q.1, Q.2.trans e.symm⟩).1
        (t' ≫ Spec.map (CommRingCat.ofHom ψ))
        (L.mul ((t' ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ s) ⟨P.1, P.2.trans e.symm⟩ ⟨Q.1, Q.2.trans e.symm⟩).2 := by
    congr 1
    exact gen e P Q
  rw [step, H T (t' ≫ Spec.map (CommRingCat.ofHom ψ)) ⟨P.1, P.2.trans e.symm⟩ ⟨Q.1, Q.2.trans e.symm⟩, gen e]
  congr 2
  · apply Subtype.ext
    dsimp only
    rw [← Category.assoc (pullback.lift P.1 t' P.2), liftG]
  · apply Subtype.ext
    dsimp only
    rw [← Category.assoc (pullback.lift Q.1 t' Q.2), liftG]

end S_GoodReductionJacobian_RelativeGroupLaw_isHomOnPoints_baseChange_comp
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isHomOnPoints_baseChange_comp (solution)
