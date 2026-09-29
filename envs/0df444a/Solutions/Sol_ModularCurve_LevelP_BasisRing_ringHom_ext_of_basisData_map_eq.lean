-- Prove2me | solution 1 for ModularCurve.LevelP.BasisRing.ringHom_ext_of_basisData_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/70adf7e8-4e9e-58fa-968e-bb2da6ac2318

import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelP_BasisRing_ringHom_ext_of_basisData_map_eq

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_LevelP_BasisRing_ringHom_ext_of_basisData_map_eq.ModularCurve ModularCurve.LevelP P2MW.S_ModularCurve_LevelP_BasisRing_ringHom_ext_of_basisData_map_eq.ModularCurve.LevelP"

namespace ModularCurve
p2m_export "ModularCurve" "LevelPData LevelPData.yQ LevelPData.xP LevelPData.yP LevelPData.xQ"
namespace LevelP
p2m_export "ModularCurve.LevelP" "PsiRoot PsiRoot.ofBase psiRootX torsionQuadratic TorsionPointRing TorsionPointRing.ofPsiRoot TorsionPointRing.ofBase torsionPtX torsionPtY torsionPtCurve TwoPointRing TwoPointRing.ofOnePoint indepDenom BasisRing BasisRing.ofTwoPoint BasisRing.ofBase basisData"
namespace LpUniq
p2m_open "ModularCurve.LevelP ModularCurve"

open Polynomial

theorem adjoinRoot_ringHom_ext {R S : Type*} [CommRing R] [CommRing S] (f : R[X])
    (g g' : AdjoinRoot f →+* S)
    (h1 : g.comp (AdjoinRoot.of f) = g'.comp (AdjoinRoot.of f)) (h2 : g (AdjoinRoot.root f) = g' (AdjoinRoot.root f)) :
    g = g' := by
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro a
    show g (AdjoinRoot.mk f (C a)) = g' (AdjoinRoot.mk f (C a))
    rw [AdjoinRoot.mk_C]
    exact RingHom.congr_fun h1 a
  · show g (AdjoinRoot.mk f X) = g' (AdjoinRoot.mk f X)
    rw [AdjoinRoot.mk_X]
    exact h2

theorem torsionPointRing_ringHom_ext {B S : Type*} [CommRing B] [CommRing S] (W : WeierstrassCurve B) (p : ℕ)
    (g g' : TorsionPointRing W p →+* S)
    (h0 : g.comp (TorsionPointRing.ofBase W p) = g'.comp (TorsionPointRing.ofBase W p))
    (hx : g (torsionPtX W p) = g' (torsionPtX W p)) (hy : g (torsionPtY W p) = g' (torsionPtY W p)) :
    g = g' := by
  apply adjoinRoot_ringHom_ext (torsionQuadratic W p) g g'
  ·
    show g.comp (TorsionPointRing.ofPsiRoot W p) = g'.comp (TorsionPointRing.ofPsiRoot W p)
    apply adjoinRoot_ringHom_ext (W.preΨ p)
    · show (g.comp (TorsionPointRing.ofPsiRoot W p)).comp (PsiRoot.ofBase W p) =
        (g'.comp (TorsionPointRing.ofPsiRoot W p)).comp (PsiRoot.ofBase W p)
      exact h0
    · show g (TorsionPointRing.ofPsiRoot W p (psiRootX W p)) = g' (TorsionPointRing.ofPsiRoot W p (psiRootX W p))
      exact hx
  · exact hy

end ModularCurve.LevelP.LpUniq

open ModularCurve.LevelP.LpUniq in
theorem solution
    {B : Type*} {A : Type*} [CommRing B] [CommRing A] (W : WeierstrassCurve B) (p : ℕ)
    (φ : B →+* A) (ψ ψ' : BasisRing W p →+* A)
    (hψ : ψ.comp (BasisRing.ofBase W p) = φ) (hψ' : ψ'.comp (BasisRing.ofBase W p) = φ)
    (h : (basisData W p).map ψ = (basisData W p).map ψ') :
    ψ = ψ' := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (indepDenom W p))
  show ψ.comp (BasisRing.ofTwoPoint W p) = ψ'.comp (BasisRing.ofTwoPoint W p)
  apply torsionPointRing_ringHom_ext (torsionPtCurve W p) p
  ·
    show (ψ.comp (BasisRing.ofTwoPoint W p)).comp (TwoPointRing.ofOnePoint W p) =
      (ψ'.comp (BasisRing.ofTwoPoint W p)).comp (TwoPointRing.ofOnePoint W p)
    apply torsionPointRing_ringHom_ext W p
    · show ψ.comp (BasisRing.ofBase W p) = ψ'.comp (BasisRing.ofBase W p)
      rw [hψ, hψ']
    · exact congrArg LevelPData.xP h
    · exact congrArg LevelPData.yP h
  · exact congrArg LevelPData.xQ h
  · exact congrArg LevelPData.yQ h

end S_ModularCurve_LevelP_BasisRing_ringHom_ext_of_basisData_map_eq
end P2MW
export P2MW.S_ModularCurve_LevelP_BasisRing_ringHom_ext_of_basisData_map_eq (solution)
