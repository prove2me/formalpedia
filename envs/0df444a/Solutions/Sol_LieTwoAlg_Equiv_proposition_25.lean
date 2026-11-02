-- Prove2me | solution 1 for LieTwoAlg.Equiv.proposition_25
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:54:48.519811+00:00
-- url     : https://prove2.me/submissions/fa69a705-3e34-4740-88bc-3c80eeb157d3

import Definitions.Def_LieTwoAlg_Equiv_Model
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
open LieTwoAlg.Equiv
universe u
namespace Lie2Prop25
variable {k : Type u} [Field k]

theorem arrow_id (V : TwoVect k) (x : V.V0) : V.arrowK (V.i x) = 0 := by
  apply Subtype.ext
  change V.i x - V.i (V.s (V.i x)) = 0
  rw [V.s_i, sub_self]

theorem arrow_kernel (V : TwoVect k) (h : LinearMap.ker V.s) :
    V.arrowK h = h := by
  apply Subtype.ext
  have hs : V.s h = 0 := h.property
  change h.val - V.i (V.s h) = h.val
  rw [hs, map_zero, sub_zero]

theorem arrow_comp (V : TwoVect k) (f g : V.V1) :
    V.arrowK (V.comp f g) = V.arrowK f + V.arrowK g := by
  change V.arrowK (f + g - V.i (V.t f)) = V.arrowK f + V.arrowK g
  rw [map_sub, map_add, arrow_id, sub_zero]

theorem arrow_br_left (L : Lie2Data k) (hl : IsLie2 L)
    (x : L.vec.V0) (f : L.vec.V1) :
    L.vec.arrowK (L.br1 (L.vec.i x) f) = (toLInf L).l2m x (L.vec.arrowK f) := by
  change L.vec.arrowK (L.br1 (L.vec.i x) f) =
    L.vec.arrowK (L.br1 (L.vec.i x) (f - L.vec.i (L.vec.s f)))
  rw [map_sub, hl.br_i, map_sub, arrow_id, sub_zero]

theorem arrow_br_right (L : Lie2Data k) (hl : IsLie2 L)
    (f : L.vec.V1) (x : L.vec.V0) :
    L.vec.arrowK (L.br1 f (L.vec.i x)) = -(toLInf L).l2m x (L.vec.arrowK f) := by
  rw [hl.skew1, map_neg, arrow_br_left L hl]
  rfl

theorem arrow_J (L : Lie2Data k) (x y z : L.vec.V0) :
    L.vec.arrowK (L.J x y z) = (toLInf L).l3 x y z := rfl

theorem hom_arrow {L M : Lie2Data k} (F : Lie2Hom L M) (hf : IsLinFunctor (V := L.vec) (W := M.vec) ⟨F.F0, F.F1⟩)
    (f : L.vec.V1) :
    M.vec.arrowK (F.F1 f) = (toLInfHom F).φ1 (L.vec.arrowK f) := by
  change M.vec.arrowK (F.F1 f) = M.vec.arrowK (F.F1 (f - L.vec.i (L.vec.s f)))
  rw [map_sub, hf.2.2, map_sub, arrow_id, sub_zero]

theorem hom_kernel {L M : Lie2Data k} (F : Lie2Hom L M) (hf : IsLinFunctor (V := L.vec) (W := M.vec) ⟨F.F0, F.F1⟩)
    (h : LinearMap.ker L.vec.s) : ((toLInfHom F).φ1 h : LinearMap.ker M.vec.s).val = F.F1 h := by
  have hs : L.vec.s h = 0 := h.property
  change F.F1 h - M.vec.i (M.vec.s (F.F1 h)) = F.F1 h
  rw [hf.1, hs, map_zero, map_zero, sub_zero]

theorem arrow_F2 {L M : Lie2Data k} (F : Lie2Hom L M) (x y : L.vec.V0) :
    M.vec.arrowK (F.F2 x y) = (toLInfHom F).φ2 x y := rfl

theorem hom_mixed {L M : Lie2Data k} (F : Lie2Hom L M)
    (hl : IsLie2 L) (hm : IsLie2 M) (hf : IsLie2Hom F)
    (x : L.vec.V0) (h : LinearMap.ker L.vec.s) :
    (toLInfHom F).φ2 x ((toLInf L).d h) =
      (toLInfHom F).φ1 ((toLInf L).l2m x h) -
        (toLInf M).l2m (F.F0 x) ((toLInfHom F).φ1 h) := by
  have hs : L.vec.s h = 0 := h.property
  have hn := congrArg M.vec.arrowK (hf.F2_nat (L.vec.i x) h)
  simp only [arrow_comp, L.vec.t_i, L.vec.s_i, hs, hf.functor.2.2,
    arrow_br_left M hm, arrow_br_left L hl, hom_arrow F hf.functor,
    arrow_kernel, map_zero, arrow_F2] at hn
  change (toLInfHom F).φ2 x (L.vec.t h) = _
  linear_combination (norm := abel) hn

theorem hom_ternary {L M : Lie2Data k} (F : Lie2Hom L M)
    (hm : IsLie2 M) (hf : IsLie2Hom F) (x y z : L.vec.V0) :
    -(toLInf M).l2m (F.F0 z) ((toLInfHom F).φ2 x y) +
      (toLInfHom F).φ2 (L.br0 x y) z + (toLInfHom F).φ1 ((toLInf L).l3 x y z) =
      (toLInf M).l3 (F.F0 x) (F.F0 y) (F.F0 z) +
        (toLInf M).l2m (F.F0 x) ((toLInfHom F).φ2 y z) -
        (toLInf M).l2m (F.F0 y) ((toLInfHom F).φ2 x z) +
        (toLInfHom F).φ2 x (L.br0 y z) + (toLInfHom F).φ2 (L.br0 x z) y := by
  have hn := congrArg M.vec.arrowK (hf.square x y z)
  simp only [arrow_comp, map_add, arrow_br_left M hm, arrow_br_right M hm,
    arrow_J, hom_arrow F hf.functor, arrow_F2] at hn
  linear_combination (norm := abel) -hn

theorem hom_construction {L M : Lie2Data k} (F : Lie2Hom L M)
    (hl : IsLie2 L) (hm : IsLie2 M) (hf : IsLie2Hom F) : IsLInfHom (toLInfHom F) := by
  constructor
  · intro h
    change LinearMap.ker L.vec.s at h
    change M.vec.t ((toLInfHom F).φ1 h : LinearMap.ker M.vec.s).val = F.F0 (L.vec.t h)
    rw [hom_kernel F hf.functor]
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

end Lie2Prop25


set_option autoImplicit false
open LieTwoAlg.Equiv
namespace Lie2Prop25
variable {k : Type u} [Field k]

theorem arrow_ext (V : TwoVect k) {f g : V.V1}
    (hs : V.s f = V.s g) (ha : V.arrowK f = V.arrowK g) : f = g := by
  have h := congrArg Subtype.val ha
  change f - V.i (V.s f) = g - V.i (V.s g) at h
  rw [hs] at h
  linear_combination (norm := abel) h

theorem linf_ext {V W : LInfData k} {F G : LInfHom V W}
    (h0 : F.φ0 = G.φ0) (h1 : F.φ1 = G.φ1) (h2 : F.φ2 = G.φ2) : F = G := by
  cases F; cases G; cases h0; cases h1; cases h2; rfl

theorem lie2_ext {L M : Lie2Data k} {F G : Lie2Hom L M}
    (h0 : F.F0 = G.F0) (h1 : F.F1 = G.F1) (h2 : F.F2 = G.F2) : F = G := by
  cases F; cases G; cases h0; cases h1; cases h2; rfl

theorem linf_comp {V W X : LInfData k} (φ : LInfHom V W) (ψ : LInfHom W X)
    (hφ : IsLInfHom φ) (hψ : IsLInfHom ψ) : IsLInfHom (φ.comp ψ) := by
  constructor
  · intro h
    exact (hψ.chain (φ.φ1 h)).trans (congrArg ψ.φ0 (hφ.chain h))
  · intro x y
    change ψ.φ2 (φ.φ0 x) (φ.φ0 y) + ψ.φ1 (φ.φ2 x y) =
      -(ψ.φ2 (φ.φ0 y) (φ.φ0 x) + ψ.φ1 (φ.φ2 y x))
    rw [hψ.skew (φ.φ0 x) (φ.φ0 y), hφ.skew x y, map_neg]
    abel
  · intro x y
    simp only [LInfHom.comp, preBilin, postBilin, LinearMap.add_apply,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, map_add]
    rw [hψ.one, hψ.chain, hφ.one, map_sub]
    abel
  · intro x h
    simp only [LInfHom.comp, preBilin, postBilin, LinearMap.add_apply,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
    rw [← hφ.chain, hψ.two, hφ.two, map_sub]
    abel
  · intro x y z
    simp only [LInfHom.comp, preBilin, postBilin, LinearMap.add_apply,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
    have one (a b : V.V0) :
        φ.φ0 (V.l2 a b) = W.d (φ.φ2 a b) + W.l2 (φ.φ0 a) (φ.φ0 b) := by
      rw [hφ.one]; abel
    rw [one x y, one y z, one x z]
    simp only [map_add, LinearMap.add_apply]
    rw [hψ.skew (W.d (φ.φ2 x y)), hψ.skew (W.d (φ.φ2 x z))]
    rw [hψ.two, hψ.two, hψ.two]
    have eqφ := congrArg ψ.φ1 (hφ.three x y z)
    simp only [map_add, map_sub, map_neg] at eqφ
    have eqψ := hψ.three (φ.φ0 x) (φ.φ0 y) (φ.φ0 z)
    linear_combination (norm := abel) eqφ + eqψ

theorem toLInf_comp {L M N : Lie2Data k} (F : Lie2Hom L M) (G : Lie2Hom M N)
    (hG : IsLinFunctor (V := M.vec) (W := N.vec) ⟨G.F0, G.F1⟩) :
    toLInfHom (F.comp G) = (toLInfHom F).comp (toLInfHom G) := by
  apply linf_ext (F := toLInfHom (F.comp G))
    (G := (toLInfHom F).comp (toLInfHom G)) rfl
  · apply LinearMap.ext
    intro h
    change LinearMap.ker L.vec.s at h
    exact hom_arrow G hG (F.F1 h)
  · apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change L.vec.V0 at x y
    exact (arrow_comp N.vec (G.F2 (F.F0 x) (F.F0 y)) (G.F1 (F.F2 x y))).trans
      (congrArg (fun a : LinearMap.ker N.vec.s => N.vec.arrowK (G.F2 (F.F0 x) (F.F0 y)) + a)
        (hom_arrow G hG (F.F2 x y)))

theorem hom_square_of_linf {L M : Lie2Data k} (F : Lie2Hom L M)
    (hL : IsLie2 L) (hM : IsLie2 M)
    (hfun : IsLinFunctor (V := L.vec) (W := M.vec) ⟨F.F0, F.F1⟩)
    (hs : ∀ x y, M.vec.s (F.F2 x y) = M.br0 (F.F0 x) (F.F0 y))
    (ht : ∀ x y, M.vec.t (F.F2 x y) = F.F0 (L.br0 x y))
    (hi : IsLInfHom (toLInfHom F)) (x y z : L.vec.V0) :
    M.vec.comp
      (M.vec.comp (M.J (F.F0 x) (F.F0 y) (F.F0 z))
        (M.br1 (M.vec.i (F.F0 x)) (F.F2 y z) +
          M.br1 (F.F2 x z) (M.vec.i (F.F0 y))))
      (F.F2 x (L.br0 y z) + F.F2 (L.br0 x z) y) =
    M.vec.comp
      (M.vec.comp (M.br1 (F.F2 x y) (M.vec.i (F.F0 z)))
        (F.F2 (L.br0 x y) z))
      (F.F1 (L.J x y z)) := by
  apply arrow_ext M.vec
  · simp only [TwoVect.comp, map_add, map_sub, M.vec.s_i, M.vec.t_i,
      hM.br_s, hM.br_t, hM.J_s, hM.J_t, hfun.1, hs, ht, hL.J_s]
    abel
  · simp only [arrow_comp, map_add, arrow_br_left M hM, arrow_br_right M hM,
      arrow_J, hom_arrow F hfun, arrow_F2]
    have h := hi.three x y z
    change -(toLInf M).l2m (F.F0 z) ((toLInfHom F).φ2 x y) +
      (toLInfHom F).φ2 (L.br0 x y) z + (toLInfHom F).φ1 ((toLInf L).l3 x y z) =
      (toLInf M).l3 (F.F0 x) (F.F0 y) (F.F0 z) +
        (toLInf M).l2m (F.F0 x) ((toLInfHom F).φ2 y z) -
        (toLInf M).l2m (F.F0 y) ((toLInfHom F).φ2 x z) +
        (toLInfHom F).φ2 x (L.br0 y z) + (toLInfHom F).φ2 (L.br0 x z) y at h
    linear_combination (norm := abel) -h

theorem comp_assoc (V : TwoVect k) (f g h : V.V1) :
    V.comp (V.comp f g) h = V.comp f (V.comp g h) := by
  simp only [TwoVect.comp, map_add, map_sub, V.t_i]
  abel

theorem functor_comp {L M : Lie2Data k} (F : Lie2Hom L M)
    (hf : IsLinFunctor (V := L.vec) (W := M.vec) ⟨F.F0, F.F1⟩)
    (f g : L.vec.V1) : F.F1 (L.vec.comp f g) = M.vec.comp (F.F1 f) (F.F1 g) := by
  change F.F1 (f + g - L.vec.i (L.vec.t f)) =
    F.F1 f + F.F1 g - M.vec.i (M.vec.t (F.F1 f))
  rw [map_sub, map_add, hf.2.2, hf.2.1]

end Lie2Prop25


set_option autoImplicit false
open LieTwoAlg.Equiv
namespace Lie2Prop25
variable {k : Type u} [Field k]

theorem comp_functor {L M N : Lie2Data k} (F : Lie2Hom L M) (G : Lie2Hom M N)
    (hF : IsLie2Hom F) (hG : IsLie2Hom G) :
    IsLinFunctor (V := L.vec) (W := N.vec) ⟨(F.comp G).F0, (F.comp G).F1⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro f
    change N.vec.s (G.F1 (F.F1 f)) = G.F0 (F.F0 (L.vec.s f))
    rw [hG.functor.1, hF.functor.1]
  · intro f
    change N.vec.t (G.F1 (F.F1 f)) = G.F0 (F.F0 (L.vec.t f))
    rw [hG.functor.2.1, hF.functor.2.1]
  · intro x
    change G.F1 (F.F1 (L.vec.i x)) = N.vec.i (G.F0 (F.F0 x))
    rw [hF.functor.2.2, hG.functor.2.2]

theorem comp_source {L M N : Lie2Data k} (F : Lie2Hom L M) (G : Lie2Hom M N)
    (hF : IsLie2Hom F) (hG : IsLie2Hom G) (x y : L.vec.V0) :
    N.vec.s ((F.comp G).F2 x y) = N.br0 ((F.comp G).F0 x) ((F.comp G).F0 y) := by
  change N.vec.s (G.F2 (F.F0 x) (F.F0 y) + G.F1 (F.F2 x y) -
    N.vec.i (N.vec.t (G.F2 (F.F0 x) (F.F0 y)))) =
      N.br0 (G.F0 (F.F0 x)) (G.F0 (F.F0 y))
  rw [map_sub, map_add, N.vec.s_i, hG.F2_s, hG.functor.1, hF.F2_s, hG.F2_t]
  abel

theorem comp_target {L M N : Lie2Data k} (F : Lie2Hom L M) (G : Lie2Hom M N)
    (hF : IsLie2Hom F) (hG : IsLie2Hom G) (x y : L.vec.V0) :
    N.vec.t ((F.comp G).F2 x y) = (F.comp G).F0 (L.br0 x y) := by
  change N.vec.t (G.F2 (F.F0 x) (F.F0 y) + G.F1 (F.F2 x y) -
    N.vec.i (N.vec.t (G.F2 (F.F0 x) (F.F0 y)))) = G.F0 (F.F0 (L.br0 x y))
  rw [map_sub, map_add, N.vec.t_i, hG.functor.2.1, hF.F2_t]
  abel

theorem comp_naturality {L M N : Lie2Data k} (F : Lie2Hom L M) (G : Lie2Hom M N)
    (hM : IsLie2 M) (hN : IsLie2 N) (hF : IsLie2Hom F) (hG : IsLie2Hom G)
    (f g : L.vec.V1) :
    N.vec.comp (N.br1 ((F.comp G).F1 f) ((F.comp G).F1 g))
      ((F.comp G).F2 (L.vec.t f) (L.vec.t g)) =
    N.vec.comp ((F.comp G).F2 (L.vec.s f) (L.vec.s g))
      ((F.comp G).F1 (L.br1 f g)) := by
  have hg := hG.F2_nat (F.F1 f) (F.F1 g)
  have hf := congrArg G.F1 (hF.F2_nat f g)
  change N.vec.comp (N.br1 (G.F1 (F.F1 f)) (G.F1 (F.F1 g)))
    (N.vec.comp (G.F2 (F.F0 (L.vec.t f)) (F.F0 (L.vec.t g)))
      (G.F1 (F.F2 (L.vec.t f) (L.vec.t g)))) =
    N.vec.comp
      (N.vec.comp (G.F2 (F.F0 (L.vec.s f)) (F.F0 (L.vec.s g)))
        (G.F1 (F.F2 (L.vec.s f) (L.vec.s g))))
      (G.F1 (F.F1 (L.br1 f g)))
  simp only [TwoVect.comp, map_add, map_sub, N.vec.t_i,
    hG.functor.2.1, hG.functor.2.2, hG.F2_t, hN.br_t, hM.br_t,
    hF.functor.1, hF.functor.2.1, hF.F2_t] at hg hf ⊢
  linear_combination (norm := abel) hg + hf

theorem comp_lawful {L M N : Lie2Data k} (hL : IsLie2 L) (hM : IsLie2 M)
    (hN : IsLie2 N) (F : Lie2Hom L M) (G : Lie2Hom M N)
    (hF : IsLie2Hom F) (hG : IsLie2Hom G) : IsLie2Hom (F.comp G) := by
  have hi : IsLInfHom (toLInfHom (F.comp G)) := by
    rw [toLInf_comp F G hG.functor]
    exact linf_comp _ _ (hom_construction F hL hM hF) (hom_construction G hM hN hG)
  refine ⟨comp_functor F G hF hG, ?_, comp_source F G hF hG,
    comp_target F G hF hG, comp_naturality F G hM hN hF hG,
    hom_square_of_linf (F.comp G) hL hN (comp_functor F G hF hG)
      (comp_source F G hF hG) (comp_target F G hF hG) hi⟩
  intro x y
  change G.F2 (F.F0 x) (F.F0 y) + G.F1 (F.F2 x y) -
    N.vec.i (N.vec.t (G.F2 (F.F0 x) (F.F0 y))) =
    -(G.F2 (F.F0 y) (F.F0 x) + G.F1 (F.F2 y x) -
      N.vec.i (N.vec.t (G.F2 (F.F0 y) (F.F0 x))))
  rw [hG.skew (F.F0 x) (F.F0 y), hF.skew x y]
  simp only [map_neg]
  abel

theorem toLInf_id (L : Lie2Data k) : toLInfHom (Lie2Hom.id L) = LInfHom.id (toLInf L) := by
  apply linf_ext (F := toLInfHom (Lie2Hom.id L)) (G := LInfHom.id (toLInf L)) rfl
  · apply LinearMap.ext
    intro h
    exact arrow_kernel L.vec h
  · apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact arrow_id L.vec (L.br0 x y)

theorem id_lawful (L : Lie2Data k) (hL : IsLie2 L) : IsLie2Hom (Lie2Hom.id L) := by
  have hfun : IsLinFunctor (V := L.vec) (W := L.vec)
      ⟨(Lie2Hom.id L).F0, (Lie2Hom.id L).F1⟩ := by
    exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  have hs : ∀ x y, L.vec.s ((Lie2Hom.id L).F2 x y) =
      L.br0 ((Lie2Hom.id L).F0 x) ((Lie2Hom.id L).F0 y) := by
    intro x y
    exact L.vec.s_i (L.br0 x y)
  have ht : ∀ x y, L.vec.t ((Lie2Hom.id L).F2 x y) =
      (Lie2Hom.id L).F0 (L.br0 x y) := by
    intro x y
    exact L.vec.t_i (L.br0 x y)
  have hi : IsLInfHom (toLInfHom (Lie2Hom.id L)) := by
    rw [toLInf_id]
    constructor <;> intros <;> simp [LInfHom.id]
  refine ⟨hfun, ?_, hs, ht, ?_, hom_square_of_linf (Lie2Hom.id L) hL hL hfun hs ht hi⟩
  · intro x y
    change L.vec.i (L.br0 x y) = -L.vec.i (L.br0 y x)
    rw [hL.skew0, map_neg]
  · intro f g
    change L.vec.comp (L.br1 f g) (L.vec.i (L.br0 (L.vec.t f) (L.vec.t g))) =
      L.vec.comp (L.vec.i (L.br0 (L.vec.s f) (L.vec.s g))) (L.br1 f g)
    simp only [TwoVect.comp, L.vec.t_i, hL.br_t]
    abel

theorem assoc {L M N P : Lie2Data k} (F : Lie2Hom L M) (G : Lie2Hom M N)
    (H : Lie2Hom N P) (hH : IsLie2Hom H) : (F.comp G).comp H = F.comp (G.comp H) := by
  apply lie2_ext (F := (F.comp G).comp H) (G := F.comp (G.comp H)) rfl rfl
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change P.vec.comp (H.F2 (G.F0 (F.F0 x)) (G.F0 (F.F0 y)))
    (H.F1 (N.vec.comp (G.F2 (F.F0 x) (F.F0 y)) (G.F1 (F.F2 x y)))) =
    P.vec.comp
      (P.vec.comp (H.F2 (G.F0 (F.F0 x)) (G.F0 (F.F0 y)))
        (H.F1 (G.F2 (F.F0 x) (F.F0 y))))
      (H.F1 (G.F1 (F.F2 x y)))
  rw [functor_comp H hH.functor]
  exact (comp_assoc P.vec _ _ _).symm

theorem units {L M : Lie2Data k} (F : Lie2Hom L M) (hF : IsLie2Hom F) :
    (Lie2Hom.id L).comp F = F ∧ F.comp (Lie2Hom.id M) = F := by
  constructor
  · apply lie2_ext (F := (Lie2Hom.id L).comp F) (G := F) rfl rfl
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change M.vec.comp (F.F2 x y) (F.F1 (L.vec.i (L.br0 x y))) = F.F2 x y
    rw [hF.functor.2.2, ← hF.F2_t]
    exact add_sub_cancel_right _ _
  · apply lie2_ext (F := F.comp (Lie2Hom.id M)) (G := F) rfl rfl
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change M.vec.comp (M.vec.i (M.br0 (F.F0 x) (F.F0 y))) (F.F2 x y) = F.F2 x y
    simp only [TwoVect.comp, M.vec.t_i]
    abel

end Lie2Prop25

open Lie2Prop25

theorem solution {k : Type u} [Field k] :
    (∀ {L M N : Lie2Data k} (hL : IsLie2 L) (hM : IsLie2 M) (hN : IsLie2 N)
      (F : Lie2Hom L M) (G : Lie2Hom M N),
      IsLie2Hom F → IsLie2Hom G → IsLie2Hom (F.comp G)) ∧
    (∀ (L : Lie2Data k), IsLie2 L → IsLie2Hom (Lie2Hom.id L)) ∧
    (∀ {L M N P : Lie2Data k} (F : Lie2Hom L M) (G : Lie2Hom M N)
      (H : Lie2Hom N P), IsLie2Hom F → IsLie2Hom G → IsLie2Hom H →
      (F.comp G).comp H = F.comp (G.comp H)) ∧
    (∀ {L M : Lie2Data k} (F : Lie2Hom L M), IsLie2Hom F →
      (Lie2Hom.id L).comp F = F ∧ F.comp (Lie2Hom.id M) = F) := by
  exact ⟨comp_lawful, id_lawful, fun F G H _ _ hH => assoc F G H hH, units⟩
