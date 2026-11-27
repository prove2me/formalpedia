-- Prove2me | solution 1 for GlobalTheory.bx_frame_pairing_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:45.825449+00:00
-- url     : https://prove2.me/submissions/f0b925ca-450d-45b0-82f8-aae90f875e1f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TransportRightSmulFrame
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
section
variable {R₀ : Type} [CommRing R₀] (B : BX R₀) {R : LAlg R₀}
private lemma transport_left_smul_frame (b : ∀ x y, B.P R x y) {x x' y : B.G R} (h : x = x') (l : (R : Type)ˣ) :
    B.tr1 h (B.smul l (b x y)) = B.smul l (b x' y) := by
  subst h; rfl
private lemma transport_right_smul_frame (b : ∀ x y, B.P R x y) {x y y' : B.G R} (h : y = y') (l : (R : Type)ˣ) :
    B.tr2 h (B.smul l (b x y)) = B.smul l (b x y') := by
  subst h; rfl
private lemma transport_left_of_heq {x x' y : B.G R} (h : x = x') {u : B.P R x y} {w : B.P R x' y}
    (e : HEq u w) : B.tr1 h u = w := by
  subst h; exact eq_of_heq e
private lemma transport_right_of_heq {x y y' : B.G R} (h : y = y') {u : B.P R x y} {w : B.P R x y'}
    (e : HEq u w) : B.tr2 h u = w := by
  subst h; exact eq_of_heq e
private lemma heq_transport_left {x x' y : B.G R} (h : x = x') (u : B.P R x y) : HEq (B.tr1 h u) u := by
  subst h; rfl
private lemma heq_transport_right {x y y' : B.G R} (h : y = y') (u : B.P R x y) : HEq (B.tr2 h u) u := by
  subst h; rfl
private lemma add_left_transport_heq {x x' x'' y : B.G R} (h : x = x') (u : B.P R x y) (w : B.P R x'' y) :
    HEq (B.add1 (B.tr1 h u) w) (B.add1 u w) := by
  subst h; rfl
private lemma add_right_transport_heq {x y y' y'' : B.G R} (h : y = y') (u : B.P R x y) (w : B.P R x y'') :
    HEq (B.add2 (B.tr2 h u) w) (B.add2 u w) := by
  subst h; rfl
private lemma frame_zero1 (b : ∀ x y, B.P R x y) (t : B.G R → B.G R → B.G R → (R : Type)ˣ)
    (h : ∀ x x' y, B.add1 (b x y) (b x' y) = B.smul (t x x' y) (b (x + x') y)) (y : B.G R) :
    b 0 y = B.smul (t 0 0 y) (B.zero1 y) := by
  obtain ⟨l, hl, -⟩ := B.trans (b 0 y) (B.zero1 y)
  have h1 := transport_left_of_heq B (zero_add (0 : B.G R)) (B.zeroFst_add (B.zero1 y))
  rw [← hl, B.addFst_smul, h, ← B.mul_smul, transport_left_smul_frame] at h1
  have h2 := smul_inj B _ h1
  have h3 : t 0 0 y * l = 1 := by
    rw [_root_.mul_assoc, mul_eq_left] at h2
    rw [mul_comm, h2]
  rw [← hl, ← B.mul_smul, h3, B.one_smul]
private lemma frame_zero2 (b : ∀ x y, B.P R x y) (t : B.G R → B.G R → B.G R → (R : Type)ˣ)
    (h : ∀ x y y', B.add2 (b x y) (b x y') = B.smul (t x y y') (b x (y + y'))) (x : B.G R) :
    b x 0 = B.smul (t x 0 0) (B.zero2 x) := by
  obtain ⟨l, hl, -⟩ := B.trans (b x 0) (B.zero2 x)
  have h1 := transport_right_of_heq B (zero_add (0 : B.G R)) (B.zeroSnd_add (B.zero2 x))
  rw [← hl, B.addSnd_smul, h, ← B.mul_smul, transport_right_smul_frame] at h1
  have h2 := smul_inj B _ h1
  have h3 : t x 0 0 * l = 1 := by
    rw [_root_.mul_assoc, mul_eq_left] at h2
    rw [mul_comm, h2]
  rw [← hl, ← B.mul_smul, h3, B.one_smul]
private lemma frame_nsmul1 (b : ∀ x y, B.P R x y) (t : B.G R → B.G R → B.G R → (R : Type)ˣ)
    (h : ∀ x x' y, B.add1 (b x y) (b x' y) = B.smul (t x x' y) (b (x + x') y)) (x y : B.G R)
    (N : ℕ) : B.nsmul1 (b x y) (N + 1) =
      B.smul (∏ k ∈ Finset.range N, t ((k + 1) • x) x y) (b ((N + 1) • x) y) := by
  induction N with
  | zero =>
    rw [Finset.prod_range_zero, ← transport_left_smul_frame B b (show x = (0 + 1) • x by simp), B.one_smul]
    apply eq_of_heq
    unfold BX.nsmul1 BX.nsmul1
    exact (heq_transport_left B _ _).trans ((add_left_transport_heq B _ _ _).trans
      ((B.zeroFst_add _).trans (heq_transport_left B _ _).symm))
  | succ N ih =>
    rw [BX.nsmul1, ih, Finset.prod_range_succ]
    conv_lhs => rw [← B.one_smul (b x y), B.addFst_smul, h, ← B.mul_smul, transport_left_smul_frame, _root_.mul_one]
private lemma frame_nsmul2 (b : ∀ x y, B.P R x y) (t : B.G R → B.G R → B.G R → (R : Type)ˣ)
    (h : ∀ x y y', B.add2 (b x y) (b x y') = B.smul (t x y y') (b x (y + y'))) (x y : B.G R)
    (N : ℕ) : B.nsmul2 (b x y) (N + 1) =
      B.smul (∏ k ∈ Finset.range N, t x ((k + 1) • y) y) (b x ((N + 1) • y)) := by
  induction N with
  | zero =>
    rw [Finset.prod_range_zero, ← transport_right_smul_frame B b (show y = (0 + 1) • y by simp), B.one_smul]
    apply eq_of_heq
    unfold BX.nsmul2 BX.nsmul2
    exact (heq_transport_right B _ _).trans ((add_right_transport_heq B _ _ _).trans
      ((B.zeroSnd_add _).trans (heq_transport_right B _ _).symm))
  | succ N ih =>
    rw [BX.nsmul2, ih, Finset.prod_range_succ]
    conv_lhs => rw [← B.one_smul (b x y), B.addSnd_smul, h, ← B.mul_smul, transport_right_smul_frame, _root_.mul_one]
private lemma coboundary_rearrange {G : Type*} [CommGroup G] (m m' p q r s t : G) (h : r * s = t * (p * q)) :
    m * m' * t * r⁻¹ = m * m' * (p⁻¹ * q⁻¹) * s := by
  rw [← eq_inv_mul_iff_mul_eq] at h
  rw [h, ← mul_inv, ← _root_.mul_assoc r⁻¹, _root_.mul_assoc (m * m') (p * q)⁻¹,
    mul_comm (p * q)⁻¹, mul_inv_cancel_right, _root_.mul_assoc (m * m'), mul_comm t]
private lemma frameEquiv_trans {x y x' y' : B.G R} (w : B.P R x y) (w' : B.P R x' y')
    (l : (R : Type)ˣ) :
    ((frameEquiv B w).symm.trans (frameEquiv B w')) (B.smul l w) = B.smul l w' := by
  have : B.smul l w = frameEquiv B w l := rfl
  rw [this, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl
end
end GlobalTheory
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] (B : BX R₀) (b : ∀ R x y, B.P R x y) (t₁ t₂ : ∀ R : LAlg R₀, B.G R → B.G R → B.G R → (R : Type)ˣ),
    (∀ R x x' y, B.add1 (b R x y) (b R x' y) = B.smul (t₁ R x x' y) (b R (x + x') y)) →
    (∀ R x y y', B.add2 (b R x y) (b R x y') = B.smul (t₂ R x y y') (b R x (y + y'))) →
    (∀ R (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ), B.IsPairing (N + 1) x y z ↔ (N + 1) • x = 0 ∧ (N + 1) • y = 0 ∧
      z = (t₁ R 0 0 y * ∏ k ∈ Finset.range N, t₁ R ((k + 1) • x) x y) / (t₂ R x 0 0 * ∏ k ∈ Finset.range N, t₂ R x ((k + 1) • y) y)) ∧
    ∀ (O : LAlg R₀) (a a' : OEnd B O) (u : ∀ {R : LAlg R₀}, LHom O R → B.G R → B.G R → (R : Type)ˣ),
      (∀ {R : LAlg R₀} (s : LHom O R) x x' y, u s (x + x') y * t₁ R x x' (a'.f s y) = t₁ R (a.f s x) (a.f s x') y * (u s x y * u s x' y)) →
      (∀ {R : LAlg R₀} (s : LHom O R) x y y', u s x (y + y') * t₂ R x (a'.f s y) (a'.f s y') = t₂ R (a.f s x) y y' * (u s x y * u s x y')) →
      ∃ A : OAdj B O, A.a = a ∧ A.ab = a') := by
  intro R₀ _ B b t₁ t₂ h₁ h₂
  refine ⟨fun R N x y z => ?_, fun O a a' u hu₁ hu₂ => ?_⟩
  · have key : ∀ (hx : (N + 1) • x = 0) (hy : (N + 1) • y = 0), B.IsPairing (N + 1) x y
        ((t₁ R 0 0 y * ∏ k ∈ Finset.range N, t₁ R ((k + 1) • x) x y) /
          (t₂ R x 0 0 * ∏ k ∈ Finset.range N, t₂ R x ((k + 1) • y) y)) := by
      intro hx hy
      refine ⟨hx, hy, b R x y, _, _, ?_, ?_, rfl⟩
      · rw [frame_nsmul1 B (b R) (t₁ R) (h₁ R), transport_left_smul_frame, frame_zero1 B (b R) (t₁ R) (h₁ R),
          ← B.mul_smul, mul_comm]
      · rw [frame_nsmul2 B (b R) (t₂ R) (h₂ R), transport_right_smul_frame, frame_zero2 B (b R) (t₂ R) (h₂ R),
          ← B.mul_smul, mul_comm]
    constructor
    · intro h
      exact ⟨h.1, h.2.1, B.pairing_unique _ _ _ _ _ h (key h.1 h.2.1)⟩
    · rintro ⟨hx, hy, rfl⟩
      exact key hx hy
  · refine ⟨⟨a, a', fun {R} s x z => (frameEquiv B (b R (a.f s x) z)).symm.trans
      (frameEquiv B (B.smul (u s x z)⁻¹ (b R x (a'.f s z)))), ?_, ?_, ?_⟩, rfl, rfl⟩
    · intro R s x z l v
      obtain ⟨m, rfl, -⟩ := B.trans (b R (a.f s x) z) v
      rw [← B.mul_smul, frameEquiv_trans, frameEquiv_trans, B.mul_smul]
    · intro R s x x' z v v'
      obtain ⟨m, rfl, -⟩ := B.trans (b R (a.f s x) z) v
      obtain ⟨m', rfl, -⟩ := B.trans (b R (a.f s x') z) v'
      rw [B.addFst_smul, h₁, ← B.mul_smul, transport_left_smul_frame, frameEquiv_trans, frameEquiv_trans,
        frameEquiv_trans, B.addFst_smul, B.addFst_smul, h₁, ← B.mul_smul, ← B.mul_smul, ← B.mul_smul]
      congr 1
      have := hu₁ s x x' z
      exact coboundary_rearrange _ _ _ _ _ _ _ this
    · intro R s x z z' v v'
      obtain ⟨m, rfl, -⟩ := B.trans (b R (a.f s x) z) v
      obtain ⟨m', rfl, -⟩ := B.trans (b R (a.f s x) z') v'
      rw [B.addSnd_smul, h₂, ← B.mul_smul, frameEquiv_trans, frameEquiv_trans,
        frameEquiv_trans, B.addSnd_smul, B.addSnd_smul, h₂, ← B.mul_smul, ← B.mul_smul, ← B.mul_smul,
        transport_right_smul_frame]
      congr 1
      have := hu₂ s x z z'
      exact coboundary_rearrange _ _ _ _ _ _ _ this
end GlobalTheory
