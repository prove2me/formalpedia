-- Prove2me | solution 1 for HeckeEis.diagElem_comp_comp_red_heckeConj_eq_comp_red_comp_diagElem_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/db9306ac-9344-5d5f-a157-40538a8c9051

import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_diagElem_comp_comp_red_heckeConj_eq_comp_red_comp_diagElem_of_ne_zero

set_option autoImplicit false

theorem solution
    (N q : ℕ) [Fact q.Prime] (K : Type) [CommRing K]
    {Wc : Type} [AddCommGroup Wc] [Module K Wc] (W : Representation K (CuspidalType.GL2 q) Wc)
    (red : CongruenceSubgroup.Gamma0 N →* CuspidalType.GL2 q)
    (hred : red = (Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (CongruenceSubgroup.Gamma0 N).subtype)
    (ℓ : ℕ) [NeZero ℓ] (h : (ℓ : ZMod q) ≠ 0) (u : ↥(HeckeEis.heckeUpper N ℓ)) :
    W (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) ∘ₗ (W.comp red) (HeckeEis.heckeConj N ℓ u) =
      (W.comp red) (u : CongruenceSubgroup.Gamma0 N) ∘ₗ W (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) := by
  subst hred
  have hb : (ℓ : ℤ) ∣
      (((u : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 :=
    (HeckeEis.mem_heckeUpper N ℓ).mp u.2
  have hb2 : ∀ b : ℤ, (ℓ : ℤ) ∣ b → ((b / (ℓ : ℤ) : ℤ) : ZMod q) * (ℓ : ZMod q) = (b : ZMod q) := by
    intro b hb
    have hmul := congrArg (Int.cast : ℤ → ZMod q) (Int.ediv_mul_cancel hb)
    push_cast at hmul
    exact hmul
  have hmap : ∀ s : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) s :
          Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
        ((s : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.castRingHom (ZMod q)) :=
    fun _ => rfl
  set φ := (Matrix.SpecialLinearGroup.toGL.comp
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (CongruenceSubgroup.Gamma0 N).subtype with hφ
  have key : CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h) * φ (HeckeEis.heckeConj N ℓ u) =
      φ (u : CongruenceSubgroup.Gamma0 N) * CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h) := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hφ]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hmap, HeckeEis.coe_heckeConj, HeckeEis.coe_heckeConjSL,
      CuspidalType.diagElem_val, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, HeckeEis.heckeConjMat, Matrix.map_apply, mul_comm]
    exact (mul_comm _ _).trans (hb2 _ hb)
  have hW := congrArg W key
  rw [map_mul, map_mul] at hW
  exact hW

end S_HeckeEis_diagElem_comp_comp_red_heckeConj_eq_comp_red_comp_diagElem_of_ne_zero
end P2MW
export P2MW.S_HeckeEis_diagElem_comp_comp_red_heckeConj_eq_comp_red_comp_diagElem_of_ne_zero (solution)
