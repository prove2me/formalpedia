-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.ideal_le_comap_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:49.139828+00:00
-- url     : https://prove2.me/submissions/ab2e8c55-3dc6-4df5-9361-b262b8821a29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueComapEqVanishingIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace GlobalTheory.QCoh.Qcqs
universe u
open GlobalTheory GlobalTheory.GaloisDescent
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.GaloisDescent
theorem _root_.solution {X Y : Scheme.{u}} (f : Y ⟶ X) {J : X.IdealSheafData}
    {I : Y.IdealSheafData} (h : J.comap f ≤ I) (U : X.affineOpens) (V : Y.affineOpens)
    (e : V.1 ≤ f ⁻¹ᵁ U.1) : J.ideal U ≤ (I.ideal V).comap (f.appLE U V e).hom := by
  intro x hx
  have h1 : (I.subschemeι ≫ f).app U x = 0 :=
    (I.subschemeι ≫ f).ideal_ker_le U (Scheme.IdealSheafData.le_map_iff_comap_le.2 h U hx)
  rw [Ideal.mem_comap, ← I.ker_subschemeι_app V, RingHom.mem_ker, Scheme.Hom.app_eq_appLE,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE,
    CommRingCat.comp_apply, h1, map_zero]
end GlobalTheory.GaloisDescent
