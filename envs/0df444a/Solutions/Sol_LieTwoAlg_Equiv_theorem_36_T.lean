-- Prove2me | solution 1 for LieTwoAlg.Equiv.theorem_36_T
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:34:46.969783+00:00
-- url     : https://prove2.me/submissions/168288b4-49a6-4c8f-b5b8-358acbc72f3a

import Definitions.Def_LieTwoAlg_Equiv_Model
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
open LieTwoAlg.Equiv
universe u
variable {k : Type u} [Field k]

private theorem bracket_target (V : LInfData k) (hv : IsLInf V)
    (x y : V.V0) (f g : V.V1) :
    V.l2 x y + V.d (-V.l2m y f + V.l2m (x + V.d f) g) =
      V.l2 (x + V.d f) (y + V.d g) := by
  simp only [map_add, map_neg, hv.e, LinearMap.add_apply]
  rw [hv.skew2 y (V.d f)]
  abel

private theorem bracket_target_general (V : LInfData k) (hv : IsLInf V)
    (f g : (ofLInf V).vec.V1) :
    (ofLInf V).vec.t ((ofLInf V).br1 f g) =
      (ofLInf V).br0 ((ofLInf V).vec.t f) ((ofLInf V).vec.t g) := by
  rcases f with ⟨x, f⟩; rcases g with ⟨y, g⟩
  exact bracket_target V hv x y f g

private theorem jacobi_target (V : LInfData k) (hv : IsLInf V) (x y z : V.V0) :
    (ofLInf V).vec.t ((ofLInf V).J x y z) =
      V.l2 x (V.l2 y z) + V.l2 (V.l2 x z) y := by
  change V.l2 (V.l2 x y) z + V.d (V.l3 x y z) = _
  rw [hv.g]; abel

private theorem comp_target (V : TwoVect k) (f g : V.V1) :
    V.t (V.comp f g) = V.t g := by
  simp [TwoVect.comp, map_add, map_sub, V.t_i]

private theorem same_arrow_target (V : LInfData k) {f g : (ofLInf V).vec.V1}
    (ha : f.2 = g.2) (ht : (ofLInf V).vec.t f = (ofLInf V).vec.t g) : f = g := by
  apply Prod.ext
  · change f.1 + V.d f.2 = g.1 + V.d g.2 at ht
    rw [ha] at ht
    exact add_right_cancel ht
  · exact ha

private theorem comp_arrow (V : LInfData k) (f g : (ofLInf V).vec.V1) :
    ((ofLInf V).vec.comp f g).2 = f.2 + g.2 := by
  change (f.2 + g.2) - 0 = _
  exact sub_zero _

private theorem add_arrow (V : LInfData k) (f g : (ofLInf V).vec.V1) :
    (f + g).2 = f.2 + g.2 := rfl

private theorem id_arrow (V : LInfData k) (x : V.V0) :
    ((ofLInf V).vec.i x).2 = 0 := rfl

private theorem jacobi_arrow_eval (V : LInfData k) (x y z : V.V0) :
    ((ofLInf V).J x y z).2 = V.l3 x y z := rfl

private theorem bracket_id_left (V : LInfData k) (x : V.V0) (f : (ofLInf V).vec.V1) :
    ((ofLInf V).br1 ((ofLInf V).vec.i x) f).2 = V.l2m x f.2 := by
  change -V.l2m f.1 0 + V.l2m (x + V.d 0) f.2 = _
  simp

private theorem bracket_id_right (V : LInfData k) (f : (ofLInf V).vec.V1) (y : V.V0) :
    ((ofLInf V).br1 f ((ofLInf V).vec.i y)).2 = -V.l2m y f.2 := by
  change -V.l2m y f.2 + V.l2m (f.1 + V.d f.2) 0 = _
  simp

private theorem l3_cycle (V : LInfData k) (hv : IsLInf V) (x y z : V.V0) :
    V.l3 x y z = V.l3 z x y := by
  rw [hv.skew3b x y z, hv.skew3a x z y, neg_neg]

private theorem jacobi_arrow (V : LInfData k) (hv : IsLInf V)
    (x y z : V.V0) (f g h : V.V1) :
    -V.l2m z (-V.l2m y f + V.l2m (x + V.d f) g) +
      V.l2m (V.l2 (x + V.d f) (y + V.d g)) h +
      V.l3 (x + V.d f) (y + V.d g) (z + V.d h) =
    V.l3 x y z +
      (-V.l2m (V.l2 y z) f +
        V.l2m (x + V.d f) (-V.l2m z g + V.l2m (y + V.d g) h)) +
      (-V.l2m y (-V.l2m z f + V.l2m (x + V.d f) h) +
        V.l2m (V.l2 (x + V.d f) (z + V.d h)) g) := by
  have tel : V.l3 (x + V.d f) (y + V.d g) (z + V.d h) =
      V.l3 x y z + V.l3 (V.d f) y z +
      V.l3 (x + V.d f) (V.d g) z +
      V.l3 (x + V.d f) (y + V.d g) (V.d h) := by
    simp only [map_add, LinearMap.add_apply]
  rw [hv.h f y z, hv.skew3a (x + V.d f) (V.d g) z, hv.h g,
    l3_cycle V hv (x + V.d f) (y + V.d g) (V.d h), hv.h h] at tel
  have swap := hv.f g (V.l2m (x + V.d f) h)
  rw [hv.e] at swap
  simp only [map_add, map_neg, LinearMap.add_apply] at tel swap ⊢
  linear_combination (norm := abel) tel - swap

private theorem jacobi_natural_target (V : LInfData k) (hv : IsLInf V)
    (a b c : (ofLInf V).vec.V1) :
    (ofLInf V).vec.t ((ofLInf V).vec.comp ((ofLInf V).br1 ((ofLInf V).br1 a b) c)
      ((ofLInf V).J ((ofLInf V).vec.t a) ((ofLInf V).vec.t b) ((ofLInf V).vec.t c))) =
    (ofLInf V).vec.t ((ofLInf V).vec.comp
      ((ofLInf V).J ((ofLInf V).vec.s a) ((ofLInf V).vec.s b) ((ofLInf V).vec.s c))
      ((ofLInf V).br1 a ((ofLInf V).br1 b c) + (ofLInf V).br1 ((ofLInf V).br1 a c) b)) := by
  let L := ofLInf V
  have h₁ : L.vec.t (L.br1 a (L.br1 b c)) =
      V.l2 (L.vec.t a) (V.l2 (L.vec.t b) (L.vec.t c)) :=
    (bracket_target_general V hv a (L.br1 b c)).trans
      (congrArg (V.l2 (L.vec.t a)) (bracket_target_general V hv b c))
  have h₂ : L.vec.t (L.br1 (L.br1 a c) b) =
      V.l2 (V.l2 (L.vec.t a) (L.vec.t c)) (L.vec.t b) :=
    (bracket_target_general V hv (L.br1 a c) b).trans
      (congrArg (fun t => V.l2 t (L.vec.t b)) (bracket_target_general V hv a c))
  exact ((comp_target L.vec _ _).trans (jacobi_target V hv _ _ _)).trans
    ((comp_target L.vec _ _).trans
      ((map_add L.vec.t _ _).trans (congrArg₂ (· + ·) h₁ h₂))).symm

set_option maxHeartbeats 800000 in
private theorem object_construction (V : LInfData k) (hv : IsLInf V) : IsLie2 (ofLInf V) := by
  constructor
  · intro f g; rfl
  · rintro ⟨x, f⟩ ⟨y, g⟩
    change V.V0 at x y
    change V.V1 at f g
    exact bracket_target V hv x y f g
  · intro x y
    change V.V0 at x y
    change (V.l2 x y, -V.l2m y 0 + V.l2m (x + V.d 0) 0) = (V.l2 x y, 0)
    simp
  · rintro ⟨x, f⟩ ⟨x', f'⟩ ⟨y, g⟩ ⟨y', g'⟩ hf hg
    change V.V0 at x x' y y'
    change V.V1 at f f' g g'
    change x + V.d f = x' at hf
    change y + V.d g = y' at hg
    subst x'; subst y'
    apply same_arrow_target V
    · change -V.l2m (y + (y + V.d g) - (y + V.d g)) (f + f' - 0) +
          V.l2m (x + (x + V.d f) - (x + V.d f) + V.d (f + f' - 0)) (g + g' - 0) =
        (-V.l2m y f + V.l2m (x + V.d f) g) +
          (-V.l2m (y + V.d g) f' + V.l2m (x + V.d f + V.d f') g') - 0
      simp only [add_sub_cancel_right, sub_zero, map_add, LinearMap.add_apply]
      linear_combination (norm := abel) hv.f f' g
    · repeat first | erw [comp_target] | erw [bracket_target_general V hv]
  · exact hv.skew2
  · rintro ⟨x, f⟩ ⟨y, g⟩
    change V.V0 at x y
    change V.V1 at f g
    apply Prod.ext
    · exact hv.skew2 x y
    · change -V.l2m y f + V.l2m (x + V.d f) g =
        -(-V.l2m x g + V.l2m (y + V.d g) f)
      simp only [map_add, LinearMap.add_apply]
      linear_combination (norm := abel) hv.f f g
  · intro x y z; rfl
  · intro x y z
    change V.V0 at x y z
    change V.l2 (V.l2 x y) z + V.d (V.l3 x y z) =
      V.l2 x (V.l2 y z) + V.l2 (V.l2 x z) y
    rw [hv.g]; abel
  · rintro ⟨x, f⟩ ⟨y, g⟩ ⟨z, h⟩
    change V.V0 at x y z
    change V.V1 at f g h
    apply same_arrow_target V
    · change (-V.l2m z (-V.l2m y f + V.l2m (x + V.d f) g) +
          V.l2m (V.l2 x y + V.d (-V.l2m y f + V.l2m (x + V.d f) g)) h) +
          V.l3 (x + V.d f) (y + V.d g) (z + V.d h) - 0 =
        V.l3 x y z +
          ((-V.l2m (V.l2 y z) f +
            V.l2m (x + V.d f) (-V.l2m z g + V.l2m (y + V.d g) h)) +
          (-V.l2m y (-V.l2m z f + V.l2m (x + V.d f) h) +
            V.l2m (V.l2 x z + V.d (-V.l2m z f + V.l2m (x + V.d f) h)) g)) - 0
      rw [sub_zero, sub_zero, bracket_target V hv, bracket_target V hv]
      simpa only [add_assoc] using jacobi_arrow V hv x y z f g h
    · exact jacobi_natural_target V hv (x, f) (y, g) (z, h)
  · intro x y z
    change V.V0 at x y z
    change ((V.l2 (V.l2 x y) z, V.l3 x y z) - (V.l2 (V.l2 x y) z, 0)) =
      -((V.l2 (V.l2 y x) z, V.l3 y x z) - (V.l2 (V.l2 y x) z, 0))
    apply Prod.ext
    · change V.l2 (V.l2 x y) z - V.l2 (V.l2 x y) z =
        -(V.l2 (V.l2 y x) z - V.l2 (V.l2 y x) z)
      simp
    · change V.l3 x y z - 0 = -(V.l3 y x z - 0)
      simpa only [sub_zero] using hv.skew3a x y z
  · intro x y z
    change V.V0 at x y z
    change ((V.l2 (V.l2 x y) z, V.l3 x y z) - (V.l2 (V.l2 x y) z, 0)) =
      -((V.l2 (V.l2 x z) y, V.l3 x z y) - (V.l2 (V.l2 x z) y, 0))
    apply Prod.ext
    · change V.l2 (V.l2 x y) z - V.l2 (V.l2 x y) z =
        -(V.l2 (V.l2 x z) y - V.l2 (V.l2 x z) y)
      simp
    · change V.l3 x y z - 0 = -(V.l3 x z y - 0)
      simpa only [sub_zero] using hv.skew3b x y z
  · intro w x y z
    change V.V0 at w x y z
    apply same_arrow_target V
    · repeat first | erw [comp_arrow V] | erw [add_arrow V] |
        erw [bracket_id_left V] | erw [bracket_id_right V] |
        erw [id_arrow V] | erw [jacobi_arrow_eval V]
      simp only [add_zero]
      change (V.l3 (V.l2 w x) y z + -V.l2m y (V.l3 w x z)) +
        (V.l3 w (V.l2 x z) y + V.l3 (V.l2 w z) x y + V.l3 w x (V.l2 y z)) =
        ((-V.l2m z (V.l3 w x y) + (V.l3 (V.l2 w y) x z + V.l3 w (V.l2 x y) z)) +
          -V.l2m x (V.l3 w y z)) + V.l2m w (V.l3 x y z)
      rw [hv.skew3a w (V.l2 x z) y, l3_cycle V hv w x (V.l2 y z),
        hv.skew3a w (V.l2 x y) z]
      linear_combination (norm := abel) -(hv.i w x y z)
    · repeat first | erw [comp_target] | erw [map_add] |
        erw [bracket_target_general V hv] | erw [jacobi_target V hv] |
        erw [(ofLInf V).vec.t_i]
      change V.l2 w (V.l2 (V.l2 x z) y) + V.l2 (V.l2 w y) (V.l2 x z) +
        (V.l2 (V.l2 w z) (V.l2 x y) + V.l2 (V.l2 (V.l2 w z) y) x) +
        (V.l2 w (V.l2 x (V.l2 y z)) + V.l2 (V.l2 w (V.l2 y z)) x) =
        ((V.l2 w + V.l2 (V.d 0)) (V.l2 (V.l2 x y) z) +
          (V.l2 w + V.l2 (V.d 0)) (V.d (V.l3 x y z))) +
          (V.l2 (V.l2 (V.l2 w z) y) x + V.l2 (V.l2 w (V.l2 y z)) x +
            V.l2 (V.l2 w y) (V.l2 x z) + V.l2 (V.l2 w z) (V.l2 x y))
      simp only [map_zero, add_zero, hv.g, map_add, map_neg, LinearMap.add_apply]
      abel

private theorem hom_target {V W : LInfData k} (φ : LInfHom V W) (hφ : IsLInfHom φ)
    (f : (ofLInf V).vec.V1) :
    (ofLInf W).vec.t ((ofLInfHom φ).F1 f) = φ.φ0 ((ofLInf V).vec.t f) := by
  rcases f with ⟨x, f⟩
  change φ.φ0 x + W.d (φ.φ1 f) = φ.φ0 (x + V.d f)
  rw [hφ.chain, map_add]

private theorem F2_target {V W : LInfData k} (φ : LInfHom V W) (hφ : IsLInfHom φ)
    (x y : V.V0) :
    (ofLInf W).vec.t ((ofLInfHom φ).F2 x y) = φ.φ0 (V.l2 x y) := by
  change W.l2 (φ.φ0 x) (φ.φ0 y) + W.d (φ.φ2 x y) = _
  rw [hφ.one]; abel

private theorem hom_arrow {V W : LInfData k} (φ : LInfHom V W) (hφ : IsLInfHom φ)
    (x y : V.V0) (f g : V.V1) :
    (-W.l2m (φ.φ0 y) (φ.φ1 f) +
      W.l2m (φ.φ0 x + W.d (φ.φ1 f)) (φ.φ1 g)) +
      φ.φ2 (x + V.d f) (y + V.d g) =
    φ.φ2 x y + φ.φ1 (-V.l2m y f + V.l2m (x + V.d f) g) := by
  have tel : φ.φ2 (x + V.d f) (y + V.d g) =
      φ.φ2 x y + φ.φ2 (V.d f) y + φ.φ2 (x + V.d f) (V.d g) := by
    simp only [map_add, LinearMap.add_apply]
  rw [hφ.skew (V.d f) y, hφ.two y f, hφ.two (x + V.d f) g] at tel
  simp only [map_add, map_neg, LinearMap.add_apply, hφ.chain] at tel ⊢
  linear_combination (norm := abel) tel

private theorem F2_arrow {V W : LInfData k} (φ : LInfHom V W) (x y : V.V0) :
    ((ofLInfHom φ).F2 x y).2 = φ.φ2 x y := rfl

private theorem F1_arrow {V W : LInfData k} (φ : LInfHom V W) (f : (ofLInf V).vec.V1) :
    ((ofLInfHom φ).F1 f).2 = φ.φ1 f.2 := rfl

private theorem hom_construction {V W : LInfData k} (φ : LInfHom V W)
    (hv : IsLInf V) (hw : IsLInf W) (hφ : IsLInfHom φ) : IsLie2Hom (ofLInfHom φ) := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro f; rfl
    · intro f; exact hom_target φ hφ f
    · intro x
      change V.V0 at x
      change (φ.φ0 x, φ.φ1 0) = (φ.φ0 x, 0)
      simp
  · intro x y
    change V.V0 at x y
    apply Prod.ext
    · exact hw.skew2 (φ.φ0 x) (φ.φ0 y)
    · exact hφ.skew x y
  · intro x y; rfl
  · intro x y; exact F2_target φ hφ x y
  · rintro ⟨x, f⟩ ⟨y, g⟩
    change V.V0 at x y
    change V.V1 at f g
    apply same_arrow_target W
    · change (-W.l2m (φ.φ0 y) (φ.φ1 f) +
          W.l2m (φ.φ0 x + W.d (φ.φ1 f)) (φ.φ1 g)) +
          φ.φ2 (x + V.d f) (y + V.d g) - 0 =
        φ.φ2 x y + φ.φ1 (-V.l2m y f + V.l2m (x + V.d f) g) - 0
      simpa only [sub_zero] using hom_arrow φ hφ x y f g
    · repeat first | erw [comp_target] | erw [F2_target φ hφ] |
        erw [hom_target φ hφ] | erw [bracket_target_general V hv]
      rfl
  · intro x y z
    change V.V0 at x y z
    apply same_arrow_target W
    · repeat first | erw [comp_arrow W] | erw [add_arrow W] |
        erw [bracket_id_left W] | erw [bracket_id_right W] |
        erw [F2_arrow φ] | erw [F1_arrow φ] |
        erw [jacobi_arrow_eval W] | erw [jacobi_arrow_eval V]
      change (W.l3 (φ.φ0 x) (φ.φ0 y) (φ.φ0 z) +
        (W.l2m (φ.φ0 x) (φ.φ2 y z) + -W.l2m (φ.φ0 y) (φ.φ2 x z))) +
        (φ.φ2 x (V.l2 y z) + φ.φ2 (V.l2 x z) y) =
        (-W.l2m (φ.φ0 z) (φ.φ2 x y) + φ.φ2 (V.l2 x y) z) + φ.φ1 (V.l3 x y z)
      linear_combination (norm := abel) -(hφ.three x y z)
    · repeat first | erw [comp_target] | erw [map_add] | erw [F2_target φ hφ] |
        erw [hom_target φ hφ] | erw [jacobi_target V hv]
      change φ.φ0 (V.l2 x (V.l2 y z)) + φ.φ0 (V.l2 (V.l2 x z) y) =
        φ.φ0 (V.l2 (V.l2 x y) z) + φ.φ0 (V.d (V.l3 x y z))
      rw [hv.g]
      simp only [map_add, map_neg]
      abel

theorem solution {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) :
    (∀ (V : LInfData k), IsLInf V → IsLie2 (ofLInf V)) ∧
    (∀ {V W : LInfData k} (φ : LInfHom V W),
      IsLInf V → IsLInf W → IsLInfHom φ → IsLie2Hom (ofLInfHom φ)) := by
  exact ⟨object_construction, hom_construction⟩

