-- Prove2me | solution 1 for LieTwoAlg.Equiv.theorem_36_S
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:40:51.734203+00:00
-- url     : https://prove2.me/submissions/76d280e9-60b1-4195-b288-0b8bc9733954

import Definitions.Def_LieTwoAlg_Equiv_Model
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
open LieTwoAlg.Equiv
universe u
variable {k : Type u} [Field k]

private theorem arrow_id (V : TwoVect k) (x : V.V0) : V.arrowK (V.i x) = 0 := by
  apply Subtype.ext
  change V.i x - V.i (V.s (V.i x)) = 0
  rw [V.s_i, sub_self]

private theorem arrow_kernel (V : TwoVect k) (h : LinearMap.ker V.s) :
    V.arrowK h = h := by
  apply Subtype.ext
  have hs : V.s h = 0 := h.property
  change h.val - V.i (V.s h) = h.val
  rw [hs, map_zero, sub_zero]

private theorem arrow_comp (V : TwoVect k) (f g : V.V1) :
    V.arrowK (V.comp f g) = V.arrowK f + V.arrowK g := by
  change V.arrowK (f + g - V.i (V.t f)) = V.arrowK f + V.arrowK g
  rw [map_sub, map_add, arrow_id, sub_zero]

private theorem mixed_val (L : Lie2Data k) (hl : IsLie2 L)
    (x : L.vec.V0) (h : LinearMap.ker L.vec.s) :
    ((toLInf L).l2m x h : LinearMap.ker L.vec.s).val = L.br1 (L.vec.i x) h := by
  have hs : L.vec.s h = 0 := h.property
  change L.br1 (L.vec.i x) h - L.vec.i (L.vec.s (L.br1 (L.vec.i x) h)) =
    L.br1 (L.vec.i x) h
  rw [hl.br_s, L.vec.s_i, hs, map_zero, map_zero, sub_zero]

private theorem arrow_br_left (L : Lie2Data k) (hl : IsLie2 L)
    (x : L.vec.V0) (f : L.vec.V1) :
    L.vec.arrowK (L.br1 (L.vec.i x) f) = (toLInf L).l2m x (L.vec.arrowK f) := by
  change L.vec.arrowK (L.br1 (L.vec.i x) f) =
    L.vec.arrowK (L.br1 (L.vec.i x) (f - L.vec.i (L.vec.s f)))
  rw [map_sub, hl.br_i, map_sub, arrow_id, sub_zero]

private theorem arrow_br_right (L : Lie2Data k) (hl : IsLie2 L)
    (f : L.vec.V1) (x : L.vec.V0) :
    L.vec.arrowK (L.br1 f (L.vec.i x)) = -(toLInf L).l2m x (L.vec.arrowK f) := by
  rw [hl.skew1, map_neg, arrow_br_left L hl]
  rfl

private theorem arrow_J (L : Lie2Data k) (x y z : L.vec.V0) :
    L.vec.arrowK (L.J x y z) = (toLInf L).l3 x y z := rfl

private theorem bracket_kernel (L : Lie2Data k) (hl : IsLie2 L)
    (h h' : LinearMap.ker L.vec.s) :
    L.br1 h h' = L.br1 (L.vec.i (L.vec.t h)) h' := by
  have hsource : L.vec.s h' = 0 := h'.property
  have hc := hl.br_comp h (L.vec.i (L.vec.t h)) (L.vec.i 0) h'
    (L.vec.s_i _).symm (by rw [L.vec.t_i, hsource])
  have hu : L.vec.comp h (L.vec.i (L.vec.t h)) = h := by
    change h.val + L.vec.i (L.vec.t h) - L.vec.i (L.vec.t h) = h.val
    abel
  have hv : L.vec.comp (L.vec.i 0) h' = h' := by
    change L.vec.i 0 + h'.val - L.vec.i (L.vec.t (L.vec.i 0)) = h'.val
    rw [L.vec.t_i, map_zero, zero_add, sub_zero]
  rw [hu, hv] at hc
  simpa only [map_zero, TwoVect.comp, zero_add, sub_zero] using hc

private theorem mixed_differential (L : Lie2Data k) (hl : IsLie2 L)
    (x : L.vec.V0) (h : LinearMap.ker L.vec.s) :
    (toLInf L).d ((toLInf L).l2m x h) = (toLInf L).l2 x ((toLInf L).d h) := by
  change L.vec.t ((toLInf L).l2m x h : LinearMap.ker L.vec.s).val = L.br0 x (L.vec.t h)
  rw [mixed_val L hl, hl.br_t, L.vec.t_i]

private theorem mixed_exchange (L : Lie2Data k) (hl : IsLie2 L)
    (h h' : LinearMap.ker L.vec.s) :
    (toLInf L).l2m ((toLInf L).d h) h' =
      -(toLInf L).l2m ((toLInf L).d h') h := by
  apply Subtype.ext
  change ((toLInf L).l2m (L.vec.t h) h' : LinearMap.ker L.vec.s).val =
    -((toLInf L).l2m (L.vec.t h') h : LinearMap.ker L.vec.s).val
  rw [mixed_val L hl, mixed_val L hl, ← bracket_kernel L hl, ← bracket_kernel L hl]
  exact hl.skew1 h h'

private theorem hom_arrow {L M : Lie2Data k} (F : Lie2Hom L M) (hf : IsLie2Hom F)
    (f : L.vec.V1) :
    M.vec.arrowK (F.F1 f) = (toLInfHom F).φ1 (L.vec.arrowK f) := by
  change M.vec.arrowK (F.F1 f) = M.vec.arrowK (F.F1 (f - L.vec.i (L.vec.s f)))
  rw [map_sub, hf.functor.2.2, map_sub, arrow_id, sub_zero]

private theorem ternary_skew_a (L : Lie2Data k) (hl : IsLie2 L)
    (x y z : L.vec.V0) : (toLInf L).l3 x y z = -(toLInf L).l3 y x z := by
  apply Subtype.ext
  exact hl.J_skew_a x y z

private theorem ternary_skew_b (L : Lie2Data k) (hl : IsLie2 L)
    (x y z : L.vec.V0) : (toLInf L).l3 x y z = -(toLInf L).l3 x z y := by
  apply Subtype.ext
  exact hl.J_skew_b x y z

private theorem ternary_cycle (L : Lie2Data k) (hl : IsLie2 L)
    (x y z : L.vec.V0) : (toLInf L).l3 x y z = (toLInf L).l3 z x y := by
  rw [ternary_skew_b L hl x y z, ternary_skew_a L hl x z y, neg_neg]

private theorem ternary_differential (L : Lie2Data k) (hl : IsLie2 L)
    (x y z : L.vec.V0) : (toLInf L).d ((toLInf L).l3 x y z) =
      -L.br0 (L.br0 x y) z + L.br0 (L.br0 x z) y + L.br0 x (L.br0 y z) := by
  change L.vec.t (L.J x y z - L.vec.i (L.vec.s (L.J x y z))) = _
  rw [map_sub, L.vec.t_i, hl.J_s, hl.J_t]
  abel

private theorem mixed_jacobi (L : Lie2Data k) (hl : IsLie2 L)
    (h : LinearMap.ker L.vec.s) (x y : L.vec.V0) :
    (toLInf L).l3 ((toLInf L).d h) x y =
      -(toLInf L).l2m (L.br0 x y) h -
        (toLInf L).l2m y ((toLInf L).l2m x h) +
        (toLInf L).l2m x ((toLInf L).l2m y h) := by
  have hs : L.vec.s h = 0 := h.property
  have hn := congrArg L.vec.arrowK (hl.J_nat (L.vec.i x) (L.vec.i y) h)
  simp only [arrow_comp, map_add, L.vec.t_i, L.vec.s_i, hl.br_i,
    arrow_br_left L hl, arrow_br_right L hl, arrow_J, arrow_kernel,
    hs, map_zero, zero_add] at hn
  change (toLInf L).l3 (L.vec.t h) x y = _
  rw [← ternary_cycle L hl x y (L.vec.t h)]
  linear_combination (norm := abel) hn

private theorem ternary_coherence (L : Lie2Data k) (hl : IsLie2 L)
    (w x y z : L.vec.V0) :
    -(toLInf L).l2m z ((toLInf L).l3 w x y) -
      (toLInf L).l2m x ((toLInf L).l3 w y z) +
      (toLInf L).l3 (L.br0 w y) x z + (toLInf L).l3 (L.br0 x z) w y =
    -(toLInf L).l2m y ((toLInf L).l3 w x z) -
      (toLInf L).l2m w ((toLInf L).l3 x y z) +
      (toLInf L).l3 (L.br0 w x) y z + (toLInf L).l3 (L.br0 w z) x y +
      (toLInf L).l3 (L.br0 x y) w z + (toLInf L).l3 (L.br0 y z) w x := by
  have hn := congrArg L.vec.arrowK (hl.J_oct w x y z)
  simp only [arrow_comp, map_add, arrow_br_left L hl, arrow_br_right L hl,
    arrow_id, arrow_J, add_zero] at hn
  rw [ternary_skew_a L hl w (L.br0 x z) y,
    ternary_cycle L hl w x (L.br0 y z), ternary_skew_a L hl w (L.br0 x y) z] at hn
  linear_combination (norm := abel) -hn

private theorem object_construction (L : Lie2Data k) (hl : IsLie2 L) : IsLInf (toLInf L) := by
  exact ⟨hl.skew0, ternary_skew_a L hl, ternary_skew_b L hl, mixed_differential L hl,
    mixed_exchange L hl, ternary_differential L hl, mixed_jacobi L hl, ternary_coherence L hl⟩

private theorem hom_kernel {L M : Lie2Data k} (F : Lie2Hom L M) (hf : IsLie2Hom F)
    (h : LinearMap.ker L.vec.s) : ((toLInfHom F).φ1 h : LinearMap.ker M.vec.s).val = F.F1 h := by
  have hs : L.vec.s h = 0 := h.property
  change F.F1 h - M.vec.i (M.vec.s (F.F1 h)) = F.F1 h
  rw [hf.functor.1, hs, map_zero, map_zero, sub_zero]

private theorem arrow_F2 {L M : Lie2Data k} (F : Lie2Hom L M) (x y : L.vec.V0) :
    M.vec.arrowK (F.F2 x y) = (toLInfHom F).φ2 x y := rfl

private theorem hom_mixed {L M : Lie2Data k} (F : Lie2Hom L M)
    (hl : IsLie2 L) (hm : IsLie2 M) (hf : IsLie2Hom F)
    (x : L.vec.V0) (h : LinearMap.ker L.vec.s) :
    (toLInfHom F).φ2 x ((toLInf L).d h) =
      (toLInfHom F).φ1 ((toLInf L).l2m x h) -
        (toLInf M).l2m (F.F0 x) ((toLInfHom F).φ1 h) := by
  have hs : L.vec.s h = 0 := h.property
  have hn := congrArg M.vec.arrowK (hf.F2_nat (L.vec.i x) h)
  simp only [arrow_comp, L.vec.t_i, L.vec.s_i, hs, hf.functor.2.2,
    arrow_br_left M hm, arrow_br_left L hl, hom_arrow F hf,
    arrow_kernel, map_zero, arrow_F2] at hn
  change (toLInfHom F).φ2 x (L.vec.t h) = _
  linear_combination (norm := abel) hn

private theorem hom_ternary {L M : Lie2Data k} (F : Lie2Hom L M)
    (hm : IsLie2 M) (hf : IsLie2Hom F) (x y z : L.vec.V0) :
    -(toLInf M).l2m (F.F0 z) ((toLInfHom F).φ2 x y) +
      (toLInfHom F).φ2 (L.br0 x y) z + (toLInfHom F).φ1 ((toLInf L).l3 x y z) =
      (toLInf M).l3 (F.F0 x) (F.F0 y) (F.F0 z) +
        (toLInf M).l2m (F.F0 x) ((toLInfHom F).φ2 y z) -
        (toLInf M).l2m (F.F0 y) ((toLInfHom F).φ2 x z) +
        (toLInfHom F).φ2 x (L.br0 y z) + (toLInfHom F).φ2 (L.br0 x z) y := by
  have hn := congrArg M.vec.arrowK (hf.square x y z)
  simp only [arrow_comp, map_add, arrow_br_left M hm, arrow_br_right M hm,
    arrow_J, hom_arrow F hf, arrow_F2] at hn
  linear_combination (norm := abel) -hn

private theorem hom_construction {L M : Lie2Data k} (F : Lie2Hom L M)
    (hl : IsLie2 L) (hm : IsLie2 M) (hf : IsLie2Hom F) : IsLInfHom (toLInfHom F) := by
  constructor
  · intro h
    change LinearMap.ker L.vec.s at h
    change M.vec.t ((toLInfHom F).φ1 h : LinearMap.ker M.vec.s).val = F.F0 (L.vec.t h)
    rw [hom_kernel F hf]
    exact hf.functor.2.1 h
  · intro x y
    change L.vec.V0 at x y
    change M.vec.arrowK (F.F2 x y) = -M.vec.arrowK (F.F2 y x)
    rw [hf.skew, map_neg]
  · intro x y
    change L.vec.V0 at x y
    change M.vec.t (F.F2 x y - M.vec.i (M.vec.s (F.F2 x y))) =
      F.F0 (L.br0 x y) - M.br0 (F.F0 x) (F.F0 y)
    rw [map_sub, M.vec.t_i, hf.F2_s, hf.F2_t]
  · exact hom_mixed F hl hm hf
  · exact hom_ternary F hm hf

theorem solution {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) :
    (∀ (L : Lie2Data k), IsLie2 L → IsLInf (toLInf L)) ∧
    (∀ {L M : Lie2Data k} (F : Lie2Hom L M),
      IsLie2 L → IsLie2 M → IsLie2Hom F → IsLInfHom (toLInfHom F)) := by
  exact ⟨object_construction, hom_construction⟩

