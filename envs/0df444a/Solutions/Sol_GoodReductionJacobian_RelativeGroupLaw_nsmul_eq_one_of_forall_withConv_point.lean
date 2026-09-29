-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_one_of_forall_withConv_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c1b6024f-757e-54cb-b64c-31a9e4c27834

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_forall_withConv_point

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar] [Algebra R Kbar] [IsScalarTower R K Kbar]
    {X : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} [IsSeparated gX] (L : RelativeGroupLaw R gX)
    (H : Type u) [CommRing H] [Bialgebra R H]
    [IsReduced (Spec (CommRingCat.of H))] [Flat (Spec.map (CommRingCat.ofHom (algebraMap R H)))]
    [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R H)))]
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R H))) gX)
    (hone : (⟨Spec.map (CommRingCat.ofHom (1 : WithConv (H →ₐ[R] Kbar)).ofConv.toRingHom) ≫ u.1, by
        rw [Category.assoc, u.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2; exact (1 : WithConv (H →ₐ[R] Kbar)).ofConv.comp_algebraMap⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) gX) = L.one _)
    (hmul : ∀ χ χ' : WithConv (H →ₐ[R] Kbar),
      (⟨Spec.map (CommRingCat.ofHom (χ * χ').ofConv.toRingHom) ≫ u.1, by
          rw [Category.assoc, u.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 2; exact (χ * χ').ofConv.comp_algebraMap⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) gX) =
        L.mul _
          ⟨Spec.map (CommRingCat.ofHom χ.ofConv.toRingHom) ≫ u.1, by
            rw [Category.assoc, u.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
            congr 2; exact χ.ofConv.comp_algebraMap⟩
          ⟨Spec.map (CommRingCat.ofHom χ'.ofConv.toRingHom) ≫ u.1, by
            rw [Category.assoc, u.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
            congr 2; exact χ'.ofConv.comp_algebraMap⟩)
    (m : ℕ) (htors : ∀ χ : WithConv (H →ₐ[R] Kbar), χ ^ m = 1) :
    L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap R H))) m u = L.one _ := by
  classical

  let pt : WithConv (H →ₐ[R] Kbar) → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) gX :=
    fun χ => ⟨Spec.map (CommRingCat.ofHom χ.ofConv.toRingHom) ≫ u.1, by
      rw [Category.assoc, u.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2; exact χ.ofConv.comp_algebraMap⟩
  have hpt : ∀ χ, (pt χ).1 = Spec.map (CommRingCat.ofHom χ.ofConv.toRingHom) ≫ u.1 := fun χ => rfl
  have hone' : pt 1 = L.one _ := hone
  have hmul' : ∀ χ χ', pt (χ * χ') = L.mul _ (pt χ) (pt χ') := hmul

  have hpow : ∀ (k : ℕ) (χ : WithConv (H →ₐ[R] Kbar)),
      L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) k (pt χ) = pt (χ ^ k) := by
    intro k χ
    induction k with
    | zero => rw [RelativeGroupLaw.nsmul_zero, pow_zero, hone']
    | succ k ih => rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ, hmul']

  refine AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat K Kbar
    (gY := Spec.map (CommRingCat.ofHom (algebraMap R H))) (gX := gX)
    (L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap R H))) m u) (L.one _) ?_
  intro x

  let r : CommRingCat.of H ⟶ CommRingCat.of Kbar := Spec.preimage x.1
  have hr : Spec.map r = x.1 := Spec.map_preimage x.1
  have hcomm : r.hom.comp (algebraMap R H) = algebraMap R Kbar := by
    have h2 := x.2
    rw [← hr, ← Spec.map_comp] at h2
    have h3 := Spec.map_injective h2
    exact congrArg (fun g => g.hom) h3
  let χ : H →ₐ[R] Kbar := { r.hom with commutes' := fun a => by simpa using congr($hcomm a) }
  have hx : x.1 = Spec.map (CommRingCat.ofHom χ.toRingHom) := by rw [← hr]; rfl

  have e1 : x.1 ≫ (L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap R H))) m u).1 =
      (L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) m (schemeHomOverComp x.1 x.2 u)).1 := by
    rw [← L.nsmul_natural _ _ x.1 x.2 m u, schemeHomOverComp_coe]
  have e2 : schemeHomOverComp x.1 x.2 u = pt (WithConv.toConv χ) := by
    apply Subtype.ext
    rw [schemeHomOverComp_coe, hpt, hx]
  have e3 : x.1 ≫ (L.one (Spec.map (CommRingCat.ofHom (algebraMap R H)))).1 =
      (L.one (Spec.map (CommRingCat.ofHom (algebraMap R Kbar)))).1 := by
    rw [← L.one_natural _ _ x.1 x.2, schemeHomOverComp_coe]
  rw [e1, e2, hpow, htors, hone', e3]

end S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_forall_withConv_point
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_forall_withConv_point (solution)
