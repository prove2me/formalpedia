-- Prove2me | solution 1 for GlobalTheory.flat_of_isSchemeTheoreticallyDominant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:03:41.854798+00:00
-- url     : https://prove2.me/submissions/40599462-247a-494d-af1e-d2e0663cc571

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
attribute [instance] PreservesNormalization.isIso_normalizationPullback
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory
theorem _root_.solution {R : Type u} [CommRing R] [IsDomain R]
    (hR : ∀ (A : Type u) [CommRing A] [Algebra R A], Submodule.torsion R A = ⊥ → Module.Flat R A)
    {X N : Scheme.{u}} (j : X ⟶ N) [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    (p : N ⟶ Spec (.of R)) [Flat (j ≫ p)] : Flat p := by
  let K := FractionRing R
  let ι : Spec (.of K) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : IsDominant ι := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)).le.trans bot_le)⟩
  have : IsSchemeTheoreticallyDominant ι := .of_isDominant _
  let j' := pullback.fst (j ≫ p) ι ≫ j
  let c := pullback.snd (j ≫ p) ι
  have hc : j' ≫ p = c ≫ ι := by simpa [j'] using pullback.condition
  refine HasRingHomProperty.iff_exists_appLE (P := @Flat)
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).left |>.mpr fun y ↦ ?_
  obtain ⟨_, ⟨(W : N.Opens), hW, rfl⟩, hy, -⟩ := N.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨W, hW⟩, hy, le_top, ?_⟩
  let φ := (Scheme.ΓSpecIso (.of R)).inv ≫ p.appLE ⊤ W le_top
  suffices φ.hom.Flat by
    rwa [CommRingCat.hom_comp, RingHom.Flat.respectsIso.cancel_left_isIso] at this
  let := φ.hom.toAlgebra
  refine hR _ (eq_bot_iff.mpr fun x ⟨⟨r, hr⟩, hx⟩ ↦ ?_)
  have hφ : φ ≫ j'.app W = CommRingCat.ofHom (algebraMap R K) ≫
      (Scheme.ΓSpecIso (.of K)).inv ≫ c.appLE ⊤ _ le_top := by
    have h1 : p.appLE ⊤ W le_top ≫ j'.app W = (c ≫ ι).appLE ⊤ _ le_top := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      simp only [hc]
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, Category.assoc, h1, Scheme.Hom.comp_appLE]
    rfl
  have hu : IsUnit (j'.app W (φ r)) := by
    rw [← CommRingCat.comp_apply, hφ, CommRingCat.comp_apply]
    exact (IsLocalization.map_units K ⟨r, hr⟩).map _
  apply j'.app_injective W
  have hx' : φ r * x = 0 := hx
  rw [map_zero, ← hu.mul_right_eq_zero, ← map_mul, hx', map_zero]
end GlobalTheory
