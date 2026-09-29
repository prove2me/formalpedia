-- Prove2me | solution 1 for MvFormalGroup.Deformation.isShiftBy_zero_and_isShiftBy_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8711af92-ce0a-57da-8976-0fe6d336b658

import Mathlib
import Definitions.Def_MvFormalGroup_IsShiftBy
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_Deformation_isShiftBy_zero_and_isShiftBy_add

set_option autoImplicit false

open IsLocalRing MvFormalGroup

theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))
    {d : ℕ} (F : MvFormalGroup d B) [F.IsComm]
    (w w' : Module.Dual (ResidueField B) V →ₗ[ResidueField B] firstOrderDeformationSpace (F.map (residue B)))
    (G G' G'' : Deformation (F.map (algebraMap B B₁)) B) :
    Deformation.IsShiftBy V ι F 0 G G ∧
      (Deformation.IsShiftBy V ι F w G G' → Deformation.IsShiftBy V ι F w' G' G'' →
        Deformation.IsShiftBy V ι F (w + w') G G'') := by
  classical
  refine ⟨?_, ?_⟩
  ·
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro ξ; simp
    · intro l; simp
  · rintro ⟨n, v, z, zl, hzl, hw, hG⟩ ⟨m, v', z', zl', hzl', hw', hG'⟩
    refine ⟨n + m, Fin.append v v', Fin.append z z', Fin.append zl zl', ?_, ?_, ?_⟩
    · intro i l
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using hzl i l
      · simpa only [Fin.append_right] using hzl' j l
    · intro ξ
      rw [LinearMap.add_apply, hw ξ, hw' ξ, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
    · intro l
      rw [hG' l, hG l, Fin.sum_univ_add, add_assoc]
      simp only [Fin.append_left, Fin.append_right]

end S_MvFormalGroup_Deformation_isShiftBy_zero_and_isShiftBy_add
end P2MW
export P2MW.S_MvFormalGroup_Deformation_isShiftBy_zero_and_isShiftBy_add (solution)
