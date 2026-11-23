-- Prove2me | solution 1 for GlobalTheory.isNilpotent_ker_specMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:37.72351+00:00
-- url     : https://prove2.me/submissions/28421c86-d21f-442a-9c96-ff57fdc3d12d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R R₀ : CommRingCat.{u}} (π : R ⟶ R₀)
    (hπ : IsNilpotent (RingHom.ker π.hom)) : IsNilpotent (Spec.map π).ker := by
  obtain ⟨n, hn⟩ := hπ
  refine ⟨n, Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  have e : RingHom.ker (Spec.map π).appTop.hom =
      (RingHom.ker π.hom).map (Scheme.ΓSpecIso R).inv.hom := by
    have h₁ : (Spec.map π).appTop = (Scheme.ΓSpecIso R).hom ≫ π ≫ (Scheme.ΓSpecIso R₀).inv := by
      simp [← Scheme.ΓSpecIso_naturality_assoc]
    rw [h₁]
    have := Ideal.map_symm (I := RingHom.ker π.hom) (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
    refine Eq.trans ?_ this.symm
    ext x
    simp only [RingHom.mem_ker, CommRingCat.hom_comp, RingHom.comp_apply, Ideal.mem_comap]
    exact map_eq_zero_iff _ (Scheme.ΓSpecIso R₀).symm.commRingCatIsoToRingEquiv.injective
  have e' : (Spec.map π).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (RingHom.ker π.hom).map (Scheme.ΓSpecIso R).inv.hom := by
    rw [← e, Scheme.Hom.ker_apply]; rfl
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, e', ← Ideal.map_pow, hn]
  simp
end GlobalTheory
