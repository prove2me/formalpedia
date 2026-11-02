-- Prove2me | solution 1 for LieTwoAlg.Equiv.theorem_36
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:59:10.728486+00:00
-- url     : https://prove2.me/submissions/b022bf77-c6a2-47f7-a8cc-e1c605d818f4

import Definitions.Def_LieTwoAlg_Equiv_Model
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_LieTwoAlg_Equiv_proposition_25
import Theorems.Thm_LieTwoAlg_Equiv_proposition_35
import Theorems.Thm_LieTwoAlg_Equiv_theorem_36_T
import Theorems.Thm_LieTwoAlg_Equiv_theorem_36_S

set_option autoImplicit false
open LieTwoAlg.Equiv
universe u


namespace Lie2Equivalence
variable {k : Type u} [Field k]

theorem linfHom_ext {V W : LInfData k} {φ ψ : LInfHom V W}
    (h0 : ∀ x, φ.φ0 x = ψ.φ0 x) (h1 : ∀ h, φ.φ1 h = ψ.φ1 h)
    (h2 : ∀ x y, φ.φ2 x y = ψ.φ2 x y) : φ = ψ := by
  have e0 : φ.φ0 = ψ.φ0 := LinearMap.ext h0
  have e1 : φ.φ1 = ψ.φ1 := LinearMap.ext h1
  have e2 : φ.φ2 = ψ.φ2 := LinearMap.ext (fun x => LinearMap.ext (h2 x))
  cases φ; cases ψ; cases e0; cases e1; cases e2; rfl

theorem lieHom_ext {L M : Lie2Data k} {F G : Lie2Hom L M}
    (h0 : ∀ x, F.F0 x = G.F0 x) (h1 : ∀ h, F.F1 h = G.F1 h)
    (h2 : ∀ x y, F.F2 x y = G.F2 x y) : F = G := by
  have e0 : F.F0 = G.F0 := LinearMap.ext h0
  have e1 : F.F1 = G.F1 := LinearMap.ext h1
  have e2 : F.F2 = G.F2 := LinearMap.ext (fun x => LinearMap.ext (h2 x))
  cases F; cases G; cases e0; cases e1; cases e2; rfl

theorem arrow_id (V : TwoVect k) (x : V.V0) : V.arrowK (V.i x) = 0 := by
  apply Subtype.ext
  change V.i x - V.i (V.s (V.i x)) = 0
  rw [V.s_i, sub_self]

theorem arrow_kernel (V : TwoVect k) (h : LinearMap.ker V.s) : V.arrowK h = h := by
  apply Subtype.ext
  have hs : V.s h = 0 := h.property
  change h.val - V.i (V.s h) = h.val
  rw [hs, map_zero, sub_zero]

theorem arrow_comp (V : TwoVect k) (f g : V.V1) :
    V.arrowK (V.comp f g) = V.arrowK f + V.arrowK g := by
  change V.arrowK (f + g - V.i (V.t f)) = V.arrowK f + V.arrowK g
  rw [map_sub, map_add, arrow_id, sub_zero]

theorem hom_arrow {L M : Lie2Data k} (F : Lie2Hom L M)
    (hf : IsLinFunctor (V := L.vec) (W := M.vec) ⟨F.F0, F.F1⟩) (f : L.vec.V1) :
    M.vec.arrowK (F.F1 f) = (toLInfHom F).φ1 (L.vec.arrowK f) := by
  change M.vec.arrowK (F.F1 f) = M.vec.arrowK (F.F1 (f - L.vec.i (L.vec.s f)))
  rw [map_sub, hf.2.2, map_sub, arrow_id, sub_zero]

theorem hom_kernel {L M : Lie2Data k} (F : Lie2Hom L M)
    (hf : IsLinFunctor (V := L.vec) (W := M.vec) ⟨F.F0, F.F1⟩)
    (h : LinearMap.ker L.vec.s) :
    ((toLInfHom F).φ1 h : LinearMap.ker M.vec.s).val = F.F1 h := by
  have hs : L.vec.s h = 0 := h.property
  change F.F1 h - M.vec.i (M.vec.s (F.F1 h)) = F.F1 h
  rw [hf.1, hs, map_zero, map_zero, sub_zero]

theorem underlying_comp {L M N : Lie2Data k} (F : Lie2Hom L M) (G : Lie2Hom M N)
    (hf : IsLinFunctor (V := L.vec) (W := M.vec) ⟨F.F0, F.F1⟩)
    (hg : IsLinFunctor (V := M.vec) (W := N.vec) ⟨G.F0, G.F1⟩) :
    IsLinFunctor (V := L.vec) (W := N.vec) ⟨(F.comp G).F0, (F.comp G).F1⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro f
    exact (hg.1 (F.F1 f)).trans (congrArg G.F0 (hf.1 f))
  · intro f
    exact (hg.2.1 (F.F1 f)).trans (congrArg G.F0 (hf.2.1 f))
  · intro x
    exact (congrArg G.F1 (hf.2.2 x)).trans (hg.2.2 (F.F0 x))

theorem S_id (L : Lie2Data k) : toLInfHom (Lie2Hom.id L) = LInfHom.id (toLInf L) := by
  apply linfHom_ext
  · intro x; rfl
  · intro h
    change LinearMap.ker L.vec.s at h
    exact arrow_kernel L.vec h
  · intro x y
    change L.vec.V0 at x y
    exact arrow_id L.vec (L.br0 x y)

theorem S_comp {L M N : Lie2Data k} (F : Lie2Hom L M) (G : Lie2Hom M N)
    (hf : IsLinFunctor (V := L.vec) (W := M.vec) ⟨F.F0, F.F1⟩)
    (hg : IsLinFunctor (V := M.vec) (W := N.vec) ⟨G.F0, G.F1⟩) :
    toLInfHom (F.comp G) = (toLInfHom F).comp (toLInfHom G) := by
  apply linfHom_ext
  · intro x; rfl
  · intro h
    change LinearMap.ker L.vec.s at h
    apply Subtype.ext
    exact (hom_kernel (F.comp G) (underlying_comp F G hf hg) h).trans
      ((hom_kernel G hg ((toLInfHom F).φ1 h)).trans
        (congrArg G.F1 (hom_kernel F hf h))).symm
  · intro x y
    change L.vec.V0 at x y
    exact (arrow_comp N.vec (G.F2 (F.F0 x) (F.F0 y)) (G.F1 (F.F2 x y))).trans
      (congrArg (fun a : LinearMap.ker N.vec.s => N.vec.arrowK (G.F2 (F.F0 x) (F.F0 y)) + a)
        (hom_arrow G hg (F.F2 x y)))

theorem T_id (V : LInfData k) : ofLInfHom (LInfHom.id V) = Lie2Hom.id (ofLInf V) := by
  apply lieHom_ext
  · intro x; rfl
  · rintro ⟨x, h⟩; rfl
  · intro x y; rfl

theorem T_comp {V W X : LInfData k} (φ : LInfHom V W) (ψ : LInfHom W X)
    (hψ : IsLInfHom ψ) :
    ofLInfHom (φ.comp ψ) = (ofLInfHom φ).comp (ofLInfHom ψ) := by
  apply lieHom_ext
  · intro x; rfl
  · rintro ⟨x, h⟩; rfl
  · intro x y
    change V.V0 at x y
    apply Prod.ext
    · change X.l2 (ψ.φ0 (φ.φ0 x)) (ψ.φ0 (φ.φ0 y)) =
        X.l2 (ψ.φ0 (φ.φ0 x)) (ψ.φ0 (φ.φ0 y)) + ψ.φ0 (W.l2 (φ.φ0 x) (φ.φ0 y)) -
          (X.l2 (ψ.φ0 (φ.φ0 x)) (ψ.φ0 (φ.φ0 y)) + X.d (ψ.φ2 (φ.φ0 x) (φ.φ0 y)))
      rw [hψ.one]
      abel
    · change ψ.φ2 (φ.φ0 x) (φ.φ0 y) + ψ.φ1 (φ.φ2 x y) =
        ψ.φ2 (φ.φ0 x) (φ.φ0 y) + ψ.φ1 (φ.φ2 x y) - 0
      exact (sub_zero _).symm

end Lie2Equivalence

namespace Lie2Equivalence
variable {k : Type u} [Field k]

theorem strict_linf {V W : LInfData k} (f0 : V.V0 →ₗ[k] W.V0) (f1 : V.V1 →ₗ[k] W.V1)
    (hd : ∀ h, W.d (f1 h) = f0 (V.d h))
    (h0 : ∀ x y, f0 (V.l2 x y) = W.l2 (f0 x) (f0 y))
    (hm : ∀ x h, f1 (V.l2m x h) = W.l2m (f0 x) (f1 h))
    (h3 : ∀ x y z, f1 (V.l3 x y z) = W.l3 (f0 x) (f0 y) (f0 z)) :
    IsLInfHom (⟨f0, f1, 0⟩ : LInfHom V W) := by
  constructor
  · exact hd
  · intro x y
    change (0 : W.V1) = -0
    simp
  · intro x y
    change W.d 0 = f0 (V.l2 x y) - W.l2 (f0 x) (f0 y)
    rw [map_zero, h0, sub_self]
  · intro x h
    change (0 : W.V1) = f1 (V.l2m x h) - W.l2m (f0 x) (f1 h)
    rw [hm, sub_self]
  · intro x y z
    change -W.l2m (f0 z) 0 + 0 + f1 (V.l3 x y z) =
      W.l3 (f0 x) (f0 y) (f0 z) + W.l2m (f0 x) 0 - W.l2m (f0 y) 0 + 0 + 0
    simp only [map_zero, neg_zero, zero_add, add_zero, sub_zero]
    exact h3 x y z

def beta (V : LInfData k) : LInfHom (toLInf (ofLInf V)) V where
  φ0 := LinearMap.id
  φ1 := (LinearMap.snd k V.V0 V.V1).comp
    (Submodule.subtype (LinearMap.ker (ofLInf V).vec.s))
  φ2 := 0

def betaInv (V : LInfData k) : LInfHom V (toLInf (ofLInf V)) where
  φ0 := LinearMap.id
  φ1 := {
    toFun := fun h => ⟨(0, h), rfl⟩
    map_add' := by
      intro a b
      apply Subtype.ext
      apply Prod.ext
      · change (0 : V.V0) = 0 + 0
        simp
      · rfl
    map_smul' := by
      intro c a
      apply Subtype.ext
      apply Prod.ext
      · change (0 : V.V0) = c • 0
        simp
      · rfl }
  φ2 := 0

theorem beta_law (V : LInfData k) : IsLInfHom (beta V) := by
  apply strict_linf
  · intro h
    change LinearMap.ker (ofLInf V).vec.s at h
    have hs : h.val.1 = 0 := h.property
    change V.d h.val.2 = h.val.1 + V.d h.val.2
    rw [hs, zero_add]
  · intro x y; rfl
  · intro x h
    change V.V0 at x
    change LinearMap.ker (ofLInf V).vec.s at h
    change (-V.l2m h.val.1 0 + V.l2m (x + V.d 0) h.val.2) - 0 = V.l2m x h.val.2
    simp
  · intro x y z
    change V.V0 at x y z
    change V.l3 x y z - 0 = V.l3 x y z
    exact sub_zero _

theorem betaInv_law (V : LInfData k) : IsLInfHom (betaInv V) := by
  apply strict_linf
  · intro h
    change (0 : V.V0) + V.d h = V.d h
    exact zero_add _
  · intro x y; rfl
  · intro x h
    apply Subtype.ext
    apply Prod.ext
    · change (0 : V.V0) = V.l2 x 0 - V.l2 x 0
      exact (sub_self _).symm
    · change V.l2m x h = (-V.l2m 0 0 + V.l2m (x + V.d 0) h) - 0
      simp
  · intro x y z
    apply Subtype.ext
    apply Prod.ext
    · change (0 : V.V0) = V.l2 (V.l2 x y) z - V.l2 (V.l2 x y) z
      exact (sub_self _).symm
    · change V.l3 x y z = V.l3 x y z - 0
      exact (sub_zero _).symm

theorem beta_inv (V : LInfData k) : (beta V).comp (betaInv V) = LInfHom.id (toLInf (ofLInf V)) := by
  apply linfHom_ext
  · intro x; rfl
  · intro h
    change LinearMap.ker (ofLInf V).vec.s at h
    apply Subtype.ext
    have hs : h.val.1 = 0 := h.property
    change (0, h.val.2) = h.val
    exact Prod.ext hs.symm rfl
  · intro x y
    change (0 : (toLInf (ofLInf V)).V1) + (betaInv V).φ1 0 = 0
    rw [map_zero, zero_add]

theorem betaInv_inv (V : LInfData k) : (betaInv V).comp (beta V) = LInfHom.id V := by
  apply linfHom_ext
  · intro x; rfl
  · intro h; rfl
  · intro x y
    change (0 : V.V1) + (beta V).φ1 0 = 0
    rw [map_zero, zero_add]

theorem beta_natural {V W : LInfData k} (φ : LInfHom V W) :
    (toLInfHom (ofLInfHom φ)).comp (beta W) = (beta V).comp φ := by
  apply linfHom_ext
  · intro x; rfl
  · intro h
    change LinearMap.ker (ofLInf V).vec.s at h
    change φ.φ1 h.val.2 - 0 = φ.φ1 h.val.2
    exact sub_zero _
  · intro x y
    change V.V0 at x y
    change (0 : W.V1) + (φ.φ2 x y - 0) = φ.φ2 x y + φ.φ1 0
    rw [sub_zero, zero_add, map_zero, add_zero]

end Lie2Equivalence

namespace Lie2Equivalence
variable {k : Type u} [Field k]

def strictLieMap {L M : Lie2Data k} (f0 : L.vec.V0 →ₗ[k] M.vec.V0)
    (f1 : L.vec.V1 →ₗ[k] M.vec.V1) : Lie2Hom L M where
  F0 := f0
  F1 := f1
  F2 := preBilin (postBilin M.vec.i M.br0) f0 f0

theorem strict_lie2 {L M : Lie2Data k} (f0 : L.vec.V0 →ₗ[k] M.vec.V0)
    (f1 : L.vec.V1 →ₗ[k] M.vec.V1) (hm : IsLie2 M)
    (hf : IsLinFunctor (V := L.vec) (W := M.vec) ⟨f0, f1⟩)
    (h0 : ∀ x y, f0 (L.br0 x y) = M.br0 (f0 x) (f0 y))
    (h1 : ∀ f g, f1 (L.br1 f g) = M.br1 (f1 f) (f1 g))
    (hJ : ∀ x y z, f1 (L.J x y z) = M.J (f0 x) (f0 y) (f0 z)) :
    IsLie2Hom (strictLieMap f0 f1) := by
  constructor
  · exact hf
  · intro x y
    change M.vec.i (M.br0 (f0 x) (f0 y)) = -M.vec.i (M.br0 (f0 y) (f0 x))
    rw [hm.skew0, map_neg]
  · intro x y
    exact M.vec.s_i (M.br0 (f0 x) (f0 y))
  · intro x y
    exact (M.vec.t_i (M.br0 (f0 x) (f0 y))).trans (h0 x y).symm
  · intro f g
    change M.br1 (f1 f) (f1 g) + M.vec.i (M.br0 (f0 (L.vec.t f)) (f0 (L.vec.t g))) -
      M.vec.i (M.vec.t (M.br1 (f1 f) (f1 g))) =
      M.vec.i (M.br0 (f0 (L.vec.s f)) (f0 (L.vec.s g))) + f1 (L.br1 f g) -
        M.vec.i (M.vec.t (M.vec.i (M.br0 (f0 (L.vec.s f)) (f0 (L.vec.s g)))))
    rw [hm.br_t, hf.2.1, hf.2.1, M.vec.t_i, ← h1]
    abel
  · intro x y z
    simp only [strictLieMap, preBilin, postBilin, LinearMap.comp_apply,
      LinearMap.coe_mk, AddHom.coe_mk]
    simp only [TwoVect.comp, map_add, map_sub, hm.br_i, M.vec.t_i, hm.J_t, h0, hJ]
    abel

def alpha1 (L : Lie2Data k) : (ofLInf (toLInf L)).vec.V1 →ₗ[k] L.vec.V1 :=
  L.vec.i.comp (LinearMap.fst k L.vec.V0 (LinearMap.ker L.vec.s)) +
    (Submodule.subtype (LinearMap.ker L.vec.s)).comp
      (LinearMap.snd k L.vec.V0 (LinearMap.ker L.vec.s))

def alphaInv1 (L : Lie2Data k) : L.vec.V1 →ₗ[k] (ofLInf (toLInf L)).vec.V1 :=
  L.vec.s.prod L.vec.arrowK

def alpha (L : Lie2Data k) : Lie2Hom (ofLInf (toLInf L)) L :=
  strictLieMap LinearMap.id (alpha1 L)

def alphaInv (L : Lie2Data k) : Lie2Hom L (ofLInf (toLInf L)) :=
  strictLieMap LinearMap.id (alphaInv1 L)

theorem alpha1_inv (L : Lie2Data k) (f : L.vec.V1) : alpha1 L (alphaInv1 L f) = f := by
  change L.vec.i (L.vec.s f) + (f - L.vec.i (L.vec.s f)) = f
  abel

theorem alphaInv1_inv (L : Lie2Data k) (f : (ofLInf (toLInf L)).vec.V1) :
    alphaInv1 L (alpha1 L f) = f := by
  rcases f with ⟨x, h⟩
  change L.vec.V0 at x
  change LinearMap.ker L.vec.s at h
  have hs : L.vec.s h = 0 := h.property
  apply Prod.ext
  · change L.vec.s (L.vec.i x + h) = x
    rw [map_add, L.vec.s_i, hs, add_zero]
  · apply Subtype.ext
    change (L.vec.i x + h) - L.vec.i (L.vec.s (L.vec.i x + h)) = h
    rw [map_add, L.vec.s_i, hs, add_zero]
    abel

theorem alpha1_injective (L : Lie2Data k) : Function.Injective (alpha1 L) := by
  intro f g h
  exact (alphaInv1_inv L f).symm.trans ((congrArg (alphaInv1 L) h).trans (alphaInv1_inv L g))

theorem alpha_functor (L : Lie2Data k) :
    IsLinFunctor (V := (ofLInf (toLInf L)).vec) (W := L.vec) ⟨LinearMap.id, alpha1 L⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, h⟩
    change L.vec.V0 at x
    change LinearMap.ker L.vec.s at h
    have hs : L.vec.s h = 0 := h.property
    change L.vec.s (L.vec.i x + h) = x
    rw [map_add, L.vec.s_i, hs, add_zero]
  · rintro ⟨x, h⟩
    change L.vec.V0 at x
    change LinearMap.ker L.vec.s at h
    change L.vec.t (L.vec.i x + h) = x + L.vec.t h
    rw [map_add, L.vec.t_i]
  · intro x
    change L.vec.i x + (0 : LinearMap.ker L.vec.s).val = L.vec.i x
    exact add_zero _

theorem alphaInv_functor (L : Lie2Data k) :
    IsLinFunctor (V := L.vec) (W := (ofLInf (toLInf L)).vec) ⟨LinearMap.id, alphaInv1 L⟩ := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro f
    change L.vec.s f + L.vec.t (f - L.vec.i (L.vec.s f)) = L.vec.t f
    rw [map_sub, L.vec.t_i]
    abel
  · intro x
    apply Prod.ext
    · exact L.vec.s_i x
    · apply Subtype.ext
      change L.vec.i x - L.vec.i (L.vec.s (L.vec.i x)) = 0
      rw [L.vec.s_i, sub_self]

theorem mixed_val (L : Lie2Data k) (hl : IsLie2 L)
    (x : L.vec.V0) (h : LinearMap.ker L.vec.s) :
    ((toLInf L).l2m x h : LinearMap.ker L.vec.s).val = L.br1 (L.vec.i x) h := by
  have hs : L.vec.s h = 0 := h.property
  change L.br1 (L.vec.i x) h - L.vec.i (L.vec.s (L.br1 (L.vec.i x) h)) =
    L.br1 (L.vec.i x) h
  rw [hl.br_s, L.vec.s_i, hs, map_zero, map_zero, sub_zero]

theorem bracket_kernel (L : Lie2Data k) (hl : IsLie2 L)
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

theorem alpha_bracket (L : Lie2Data k) (hl : IsLie2 L)
    (f g : (ofLInf (toLInf L)).vec.V1) :
    alpha1 L ((ofLInf (toLInf L)).br1 f g) = L.br1 (alpha1 L f) (alpha1 L g) := by
  rcases f with ⟨x, f⟩; rcases g with ⟨y, g⟩
  change L.vec.V0 at x y
  change LinearMap.ker L.vec.s at f g
  change L.vec.i (L.br0 x y) +
      (-((toLInf L).l2m y f : LinearMap.ker L.vec.s).val +
        ((toLInf L).l2m (x + L.vec.t f) g : LinearMap.ker L.vec.s).val) =
    L.br1 (L.vec.i x + f) (L.vec.i y + g)
  rw [mixed_val L hl, mixed_val L hl]
  simp only [map_add, LinearMap.add_apply, hl.br_i]
  rw [hl.skew1 f (L.vec.i y), bracket_kernel L hl f g]
  abel

theorem alpha_J (L : Lie2Data k) (hl : IsLie2 L) (x y z : L.vec.V0) :
    alpha1 L ((ofLInf (toLInf L)).J x y z) = L.J x y z := by
  change L.vec.i (L.br0 (L.br0 x y) z) +
    (L.J x y z - L.vec.i (L.vec.s (L.J x y z))) = L.J x y z
  rw [hl.J_s]
  abel

theorem alpha_law (L : Lie2Data k) (hl : IsLie2 L) : IsLie2Hom (alpha L) :=
  strict_lie2 (L := ofLInf (toLInf L)) (M := L) LinearMap.id (alpha1 L) hl (alpha_functor L)
    (fun _ _ => rfl) (alpha_bracket L hl) (alpha_J L hl)

theorem alphaInv_law (L : Lie2Data k) (hl : IsLie2 L)
    (ht : IsLie2 (ofLInf (toLInf L))) : IsLie2Hom (alphaInv L) := by
  apply strict_lie2 (L := L) (M := ofLInf (toLInf L)) LinearMap.id (alphaInv1 L) ht (alphaInv_functor L)
  · intro x y; rfl
  · intro f g
    apply alpha1_injective L
    rw [alpha1_inv, alpha_bracket L hl, alpha1_inv, alpha1_inv]
  · intro x y z
    apply alpha1_injective L
    exact (alpha1_inv L (L.J x y z)).trans (alpha_J L hl x y z).symm

theorem comp_i_left (V : TwoVect k) (x : V.V0) (f : V.V1) : V.comp (V.i x) f = f := by
  change V.i x + f - V.i (V.t (V.i x)) = f
  rw [V.t_i]
  abel

theorem alpha_inv (L : Lie2Data k) :
    (alpha L).comp (alphaInv L) = Lie2Hom.id (ofLInf (toLInf L)) := by
  apply lieHom_ext
  · intro x; rfl
  · exact alphaInv1_inv L
  · intro x y
    change L.vec.V0 at x y
    exact (comp_i_left (ofLInf (toLInf L)).vec (L.br0 x y) _).trans
      ((alphaInv_functor L).2.2 (L.br0 x y))

theorem alphaInv_inv (L : Lie2Data k) : (alphaInv L).comp (alpha L) = Lie2Hom.id L := by
  apply lieHom_ext
  · intro x; rfl
  · exact alpha1_inv L
  · intro x y
    exact (comp_i_left L.vec (L.br0 x y) _).trans ((alpha_functor L).2.2 (L.br0 x y))

theorem alpha_natural {L M : Lie2Data k} (F : Lie2Hom L M) (hf : IsLie2Hom F) :
    (ofLInfHom (toLInfHom F)).comp (alpha M) = (alpha L).comp F := by
  apply lieHom_ext
  · intro x; rfl
  · rintro ⟨x, h⟩
    change L.vec.V0 at x
    change LinearMap.ker L.vec.s at h
    change M.vec.i (F.F0 x) + ((toLInfHom F).φ1 h : LinearMap.ker M.vec.s).val =
      F.F1 (L.vec.i x + h)
    rw [hom_kernel F hf.functor, map_add, hf.functor.2.2]
  · intro x y
    change L.vec.V0 at x y
    change M.vec.comp (M.vec.i (M.br0 (F.F0 x) (F.F0 y)))
      (M.vec.i (M.br0 (F.F0 x) (F.F0 y)) + (F.F2 x y - M.vec.i (M.vec.s (F.F2 x y)))) =
      M.vec.comp (F.F2 x y) (F.F1 (L.vec.i (L.br0 x y)))
    simp only [TwoVect.comp, M.vec.t_i, hf.functor.2.2, hf.F2_t, hf.F2_s]
    abel

end Lie2Equivalence

namespace Lie2Equivalence
variable {k : Type u} [Field k]

def S (h2 : (2 : k) ≠ 0) : RawFunctor (lie2AlgCat k) (twoTermLInfCat k) where
  obj L := ⟨toLInf L.1, (theorem_36_S h2).1 L.1 L.2⟩
  map F := toLInfHom F

def T (h2 : (2 : k) ≠ 0) : RawFunctor (twoTermLInfCat k) (lie2AlgCat k) where
  obj V := ⟨ofLInf V.1, (theorem_36_T h2).1 V.1 V.2⟩
  map φ := ofLInfHom φ

theorem S_functor (h2 : (2 : k) ≠ 0) : (S h2).IsFunctor := by
  refine ⟨?_, ?_, ?_⟩
  · intro L M F hf
    exact (theorem_36_S h2).2 F L.2 M.2 hf
  · intro L
    exact S_id L.1
  · intro L M N F G hf hg
    exact S_comp F G hf.functor hg.functor

theorem T_functor (h2 : (2 : k) ≠ 0) : (T h2).IsFunctor := by
  refine ⟨?_, ?_, ?_⟩
  · intro V W φ hφ
    exact (theorem_36_T h2).2 φ V.2 W.2 hφ
  · intro V
    exact T_id V.1
  · intro V W X φ ψ _ hψ
    exact T_comp φ ψ hψ

theorem lie_category : (lie2AlgCat k).IsCategory := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro L
    exact proposition_25.2.1 L.1 L.2
  · intro L M N F G hf hg
    exact proposition_25.1 L.2 M.2 N.2 F G hf hg
  · intro L M N P F G H hf hg hh
    exact proposition_25.2.2.1 F G H hf hg hh
  · intro L M F hf
    exact proposition_25.2.2.2 F hf

theorem linf_category (h2 : (2 : k) ≠ 0) : (twoTermLInfCat k).IsCategory := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V
    exact (proposition_35 h2).2.1 V.1 V.2
  · intro V W X φ ψ hφ hψ
    exact (proposition_35 h2).1 V.2 W.2 X.2 φ ψ hφ hψ
  · intro V W X Y φ ψ χ hφ hψ hχ
    exact (proposition_35 h2).2.2.1 φ ψ χ hφ hψ hχ
  · intro V W φ hφ
    exact (proposition_35 h2).2.2.2 φ hφ

end Lie2Equivalence

open Lie2Equivalence

theorem solution (k : Type u) [Field k] (h2 : (2 : k) ≠ 0) :
    RawCat.Equivalent (lie2AlgCat k) (twoTermLInfCat k) := by
  refine ⟨lie_category, linf_category h2, S h2, T h2,
    (fun L => alpha L.1), (fun V => beta V.1), S_functor h2, T_functor h2, ?_, ?_, ?_, ?_⟩
  · intro L
    refine ⟨alpha_law L.1 L.2, alphaInv L.1, alphaInv_law L.1 L.2 ?_, alpha_inv L.1, alphaInv_inv L.1⟩
    exact ((T h2).obj ((S h2).obj L)).2
  · intro V
    exact ⟨beta_law V.1, betaInv V.1, betaInv_law V.1, beta_inv V.1, betaInv_inv V.1⟩
  · intro L M F hf
    exact alpha_natural F hf
  · intro V W φ _
    exact beta_natural φ
