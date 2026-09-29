-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.principalSqrt_pi_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/79f6158c-f56e-5656-9b48-da1c077b5831

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_compatible_univ
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi_univ
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_forall_nonempty_pullback_iso_of_isPullback_pi_univ
import Theorems.Thm_AlgebraicGeometry_Polarisation_kernelTrivial_of_forall_kernelTrivial_pullback_of_isPullback_pi_univ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_principalSqrt_pi_of_forall

set_option autoImplicit false

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u v

noncomputable section

namespace ClopenGlueRoot

variable {S' : Type u} [CommRing S'] {X : Scheme.{u}}

theorem mul_val_congr {R₀ : Type u} [CommRing R₀] {B : Scheme.{u}} {b : B ⟶ Spec (CommRingCat.of R₀)} (G : RelativeGroupLaw R₀ b)
    {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R₀)} (h : t₁ = t₂)
    (P Q : SchemeHomOver t₁ b) (P' Q' : SchemeHomOver t₂ b) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (G.mul t₁ P Q).1 = (G.mul t₂ P' Q').1 := by
  subst h
  obtain ⟨p, hp⟩ := P; obtain ⟨p', hp'⟩ := P'; obtain ⟨q, hq⟩ := Q; obtain ⟨q', hq'⟩ := Q'
  simp only at hP hQ
  subst hP; subst hQ; rfl

theorem locIsoOnBase_congr (g : X ⟶ Spec (CommRingCat.of S')) {M M' N N' : X.Modules}
    (eM : M ≅ N) (eM' : M' ≅ N') (h : LocIsoOnBase g M M') : LocIsoOnBase g N N' := by
  intro s
  obtain ⟨U, hs, ⟨e⟩⟩ := h s
  exact ⟨U, hs, ⟨((Scheme.Modules.pullback _).mapIso eM).symm ≪≫ e ≪≫ (Scheme.Modules.pullback _).mapIso eM'⟩⟩

def isoOfTensorIsoUnit (A B B' : X.Modules) (i : A ⊗ B ≅ 𝟙_ _) (i' : A ⊗ B' ≅ 𝟙_ _) : B ≅ B' :=
  (λ_ B).symm ≪≫ (i'.symm ⊗ᵢ Iso.refl B) ≪≫ ((β_ A B') ⊗ᵢ Iso.refl B) ≪≫ α_ B' A B ≪≫ (Iso.refl B' ⊗ᵢ i) ≪≫ ρ_ B'

theorem nonempty_dual_congr {M M' : X.Modules} (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')
    (e : M ≅ M') : Nonempty (Scheme.Modules.dual M ≅ Scheme.Modules.dual M') :=
  ⟨isoOfTensorIsoUnit M' _ _ ((e.symm ⊗ᵢ Iso.refl _) ≪≫ hM.dual_monoidalV2.2.some) hM'.dual_monoidalV2.2.some⟩

theorem nonempty_mumfordBundle_congr (g : X ⟶ Spec (CommRingCat.of S')) (G : RelativeGroupLaw S' g) {M M' : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M') (e : M ≅ M') :
    Nonempty (mumfordBundle g G M ≅ mumfordBundle g G M') := by
  obtain ⟨d⟩ := nonempty_dual_congr hM hM' e
  unfold mumfordBundle
  exact ⟨(Scheme.Modules.pullback _).mapIso e ⊗ᵢ ((Scheme.Modules.pullback _).mapIso d ⊗ᵢ (Scheme.Modules.pullback _).mapIso d)⟩

theorem kernelTrivial_congr (g : X ⟶ Spec (CommRingCat.of S')) (G : RelativeGroupLaw S' g) {M M' : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M') (e : M ≅ M')
    (h : KernelTrivial g G M) : KernelTrivial g G M' := by
  intro R _ t x hx
  obtain ⟨eΛ⟩ := nonempty_mumfordBundle_congr g G hM hM' e
  exact h R t x (locIsoOnBase_congr _ ((Scheme.Modules.pullback _).mapIso eΛ).symm (Iso.refl _) hx)

end ClopenGlueRoot

open ClopenGlueRoot in
theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    {k : ℕ} (C : Fin k → Type u) [∀ i, CommRing (C i)] [∀ i, Algebra S (C i)]
    (hroot : ∀ i, (∀ (L' : RelativeGroupLaw (C i) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))))),
          (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of (C i)))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (C i))))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))).Modules,
            Scheme.Modules.IsInvertible 𝓛₀ ∧
            KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) L' 𝓛₀ ∧
            LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))))
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))))).obj 𝓛)
              (𝓛₀ ⊗ (Scheme.Modules.pullback
                (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) L')).obj 𝓛₀))) :
    (∀ (L' : RelativeGroupLaw (∀ i, C i) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))))),
          (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of (∀ i, C i)))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i))))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i))))).Modules,
            Scheme.Modules.IsInvertible 𝓛₀ ∧
            KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i))))) L' 𝓛₀ ∧
            LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))))
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))))).obj 𝓛)
              (𝓛₀ ⊗ (Scheme.Modules.pullback
                (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i))))) L')).obj 𝓛₀)) := by
  classical
  intro L' hL'

  have hproj : ∀ i, (Pi.evalRingHom C i).comp (algebraMap S (∀ i, C i)) = algebraMap S (C i) := fun i => RingHom.ext fun _ => rfl
  have hcompat : ∀ i, ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of (C i)))
      (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))))),
      (((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))).mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) =
        (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))))
          ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1 := by
    intro i T t' P Q
    rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
    rfl
  have hex := fun i => hroot i (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) (hcompat i)
  choose 𝓛₀ h𝓛₀ hKT hSq using hex

  let u : ∀ i, pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (C i)))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))) := fun i =>
    pullback.lift (pullback.fst f _) (pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)))
      (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hproj])
  have hu1 : ∀ i, u i ≫ pullback.fst f _ = pullback.fst f _ := fun i => pullback.lift_fst _ _ _
  have hu2 : ∀ i, u i ≫ pullback.snd f _ = pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)) :=
    fun i => pullback.lift_snd _ _ _
  have hv : ∀ i, IsPullback (u i) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i)))))
      (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))) := by
    intro i
    have big : IsPullback (u i ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i))))) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) f
        (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)) ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i))))) := by
      rw [hu1, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hproj]
      exact IsPullback.of_hasPullback f _
    exact big.of_right (hu2 i) (IsPullback.of_hasPullback f _)

  have hneg : ∀ i, u i ≫ negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i))))) L' = negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) ≫ u i :=
    fun i => RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_compatible_univ L (∀ i, C i) (C i) (Pi.evalRingHom C i) (hproj i)
      L' (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) hL' (hcompat i) (u i) (hu1 i) (hu2 i)

  obtain ⟨𝓝, h𝓝, e𝓝⟩ := AlgebraicGeometry.Scheme.Modules.exists_isInvertible_forall_nonempty_pullback_iso_of_isPullback_pi_univ
    C (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i))))) (fun i => pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) u hv 𝓛₀ h𝓛₀
  have eN : ∀ i, Nonempty ((Scheme.Modules.pullback (u i)).obj ((Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i, C i))))) L')).obj 𝓝) ≅
      (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))))).obj (𝓛₀ i)) := fun i =>
    ⟨(Scheme.Modules.pullbackComp _ _).app 𝓝 ≪≫ (Scheme.Modules.pullbackCongr (hneg i)).app 𝓝 ≪≫
      ((Scheme.Modules.pullbackComp _ _).app 𝓝).symm ≪≫ (Scheme.Modules.pullback _).mapIso (e𝓝 i).some⟩
  refine ⟨𝓝, h𝓝, ?_, ?_⟩
  ·
    refine AlgebraicGeometry.Polarisation.kernelTrivial_of_forall_kernelTrivial_pullback_of_isPullback_pi_univ C _ L' 𝓝 h𝓝
      (fun i => pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) u hv (fun i => L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) ?_ ?_
    · intro i T t P Q
      apply pullback.hom_ext
      · rw [hL']
        trans ((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))).mul t P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))
        · rw [Category.assoc, hu1]
        rw [hcompat i]
        exact mul_val_congr L (by rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hproj]) _ _ _ _
          (by change P.1 ≫ _ = (P.1 ≫ u i) ≫ _; rw [Category.assoc, hu1])
          (by change Q.1 ≫ _ = (Q.1 ≫ u i) ≫ _; rw [Category.assoc, hu1])
      · rw [(L'.mul _ _ _).2, Category.assoc, hu2 i, ← Category.assoc, ((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))).mul t P Q).2]
    · intro i
      exact kernelTrivial_congr _ _ (h𝓛₀ i) (h𝓝.pullback _) (e𝓝 i).some.symm (hKT i)
  ·
    refine AlgebraicGeometry.Polarisation.locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi_univ C _ _ _
      (fun i => pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (C i))))) u hv fun i => ?_
    refine locIsoOnBase_congr _ ?_ ?_ (hSq i)
    · exact ((Scheme.Modules.pullbackComp (u i) _).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr (hu1 i)).app 𝓛).symm
    · exact ((e𝓝 i).some ⊗ᵢ (eN i).some).symm ≪≫ (Scheme.Modules.pullbackTensorObjIso (u i) _ _).symm

end

end S_GoodReductionJacobian_RelativeGroupLaw_principalSqrt_pi_of_forall
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_principalSqrt_pi_of_forall (solution)
