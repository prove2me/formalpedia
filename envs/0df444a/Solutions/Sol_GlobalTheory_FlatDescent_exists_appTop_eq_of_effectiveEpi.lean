-- Prove2me | solution 1 for GlobalTheory.FlatDescent.exists_appTop_eq_of_effectiveEpi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:48.151475+00:00
-- url     : https://prove2.me/submissions/afd5873b-2875-4333-bd64-20c3899d8a3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory
open GlobalTheory.FlatDescent
universe u
variable {X Y Z : Scheme.{u}}
namespace GlobalTheory.FlatDescent
theorem _root_.solution (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)) (hs : f.appTop s = g.appTop s) :
    ∃ a : Γ(X, ⊤), p.appTop a = s := by
  let E := RingHom.eqLocus f.appTop.hom g.appTop.hom
  let ι : CommRingCat.of E ⟶ Γ(Y, ⊤) := CommRingCat.ofHom E.subtype
  have hι : ι ≫ f.appTop = ι ≫ g.appTop := by
    ext x
    exact x.2
  have : HasPullback p p := inferInstance
  obtain ⟨u, hu⟩ := IsRegularEpi.exists_of_isKernelPair p h (Y.toSpecΓ ≫ Spec.map ι) (by
    rw [Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp,
      ← Spec.map_comp, hι])
  refine ⟨u.appTop ((Scheme.ΓSpecIso (.of E)).inv ⟨s, hs⟩), ?_⟩
  have h1 : (Scheme.ΓSpecIso (.of E)).inv ≫ u.appTop ≫ p.appTop = ι := by
    rw [← Scheme.Hom.comp_appTop, hu, Scheme.Hom.comp_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp
  exact congr($h1 ⟨s, hs⟩)
end GlobalTheory.FlatDescent
