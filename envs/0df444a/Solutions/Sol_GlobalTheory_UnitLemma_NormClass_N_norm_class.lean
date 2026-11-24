-- Prove2me | solution 1 for GlobalTheory.UnitLemma.NormClass.N_norm_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:40:13.054613+00:00
-- url     : https://prove2.me/submissions/de456ba2-8fb8-4621-8dfa-1dc7f3d4339b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountAndGramDetSignNormClass
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_eta_gram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory.UnitLemma.NormClass
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial
section Orb
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]
end Orb
variable {K : UQ}
open Polynomial in
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] in
private theorem isLat_mulLat_unit {E : Type} [Field E] [Algebra E A] (u : Aˣ) (L : Submodule O A)
    (hL : _root_.GlobalTheory.UnitLemma.IsLat O E L) : _root_.GlobalTheory.UnitLemma.IsLat O E (_root_.GlobalTheory.UnitLemma.mulLat O (u : A) L) := by
  unfold _root_.GlobalTheory.UnitLemma.IsLat at hL ⊢
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.UnitLemma.mulLat
    exact hL.1.map _
  · unfold _root_.GlobalTheory.UnitLemma.mulLat
    rw [Submodule.map_coe]
    have e : (⇑(LinearMap.mulLeft O (u : A))) = ⇑(LinearMap.mulLeft E (u : A)) := rfl
    rw [e, Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]
    intro z
    exact ⟨((u⁻¹ : Aˣ) : A) * z, by simp⟩
open Polynomial in
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] in
private theorem forall_mem_mulLat_unit_iff (u : Aˣ) (L : Submodule O A) (P : A → Prop) :
    (∀ z ∈ _root_.GlobalTheory.UnitLemma.mulLat O (u : A) L, P z) ↔ ∀ z ∈ L, P (u * z) := by
  constructor
  · intro h z hz
    exact h _ ((_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat u L _).mpr (by rwa [Units.inv_mul_cancel_left]))
  · intro h z hz
    have := h _ ((_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat u L z).mp hz)
    rwa [Units.mul_inv_cancel_left] at this
open Polynomial in
variable {K : _root_.GlobalTheory.UnitLemma.UQ} in
private theorem herm_mul_unit_sigma (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (u : B.Aˣ) (a b : B.A) :
    B.herm (x * (u * B.σ (u : B.A))) a b = B.herm x (u * a) (u * b) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  simp only [map_mul]
  congr 1
  ring
open Polynomial in
variable {K : _root_.GlobalTheory.UnitLemma.UQ} in
private theorem mem_X_mul_unit_sigma_iff (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (u : B.Aˣ)
    (L : Submodule K.O B.A) :
    L ∈ B.X (x * (u * B.σ (u : B.A))) ↔ _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L ∈ B.X x := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.X
  simp only [Set.mem_setOf_eq]
  refine and_congr ?_ (and_congr ?_ ?_)
  · refine ⟨isLat_mulLat_unit u L, fun h => ?_⟩
    have := isLat_mulLat_unit (u⁻¹) _ h
    have hL : _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) (_root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L) = L :=
      (_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).left_inv L
    rwa [hL] at this
  · rw [forall_mem_mulLat_unit_iff]
    constructor
    · intro h z hz
      rw [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, mul_left_comm, Units.inv_mul_cancel_left]
      exact h z hz
    · intro h z hz
      have := h z hz
      rwa [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, mul_left_comm, Units.inv_mul_cancel_left] at this
  · constructor
    · intro h w
      rw [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, h, forall_mem_mulLat_unit_iff]
      simp only [herm_mul_unit_sigma, Units.mul_inv_cancel_left]
    · intro h w
      have := h (u * w)
      rw [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat, Units.inv_mul_cancel_left, forall_mem_mulLat_unit_iff] at this
      rw [this]
      simp only [herm_mul_unit_sigma]
open Polynomial in
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] in
private theorem mulLat_unit_comm (u t : Aˣ) (L : Submodule O A) :
    _root_.GlobalTheory.UnitLemma.mulLat O (u : A) (_root_.GlobalTheory.UnitLemma.mulLat O (t : A) L) =
      _root_.GlobalTheory.UnitLemma.mulLat O (t : A) (_root_.GlobalTheory.UnitLemma.mulLat O (u : A) L) := by
  ext y
  simp only [_root_.GlobalTheory.UnitLemma.Orbit.mem_mulLat]
  rw [mul_left_comm]
end GlobalTheory.UnitLemma.NormClass
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.NormClass
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial
variable {K : UQ}
open Polynomial
variable {K : _root_.GlobalTheory.UnitLemma.UQ}
namespace GlobalTheory.UnitLemma.NormClass
namespace _root_.GlobalTheory.UnitLemma.NormClass
theorem _root_.solution : ∀ (K : _root_.GlobalTheory.UnitLemma.UQ) (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (u : B.Aˣ),
    B.N (x * (u * B.σ (u : B.A))) = B.N x ∧
      K.eta (B.gramDet (x * (u * B.σ (u : B.A)))) = K.eta (B.gramDet x) := by
  intro K B x u
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.UnitLemma.InvAlg.N _root_.GlobalTheory.UnitLemma.orbSum
    simp only [one_mul]
    let wt : Submodule K.O B.A → ℚ := fun L =>
      ((_root_.GlobalTheory.UnitLemma.stabLat K.O L ⊓ B.T).relIndex (_root_.GlobalTheory.UnitLemma.intUnits K.O B.A ⊓ B.T) : ℚ)
    have hwt : ∀ (t : B.Aˣ) (L : Submodule K.O B.A), wt (_root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) = wt L := by
      intro t L
      simp only [wt, _root_.GlobalTheory.UnitLemma.Orbit.stabLat_mulLat]
    have hrel : ∀ (X : Set (Submodule K.O B.A)) (a b : X),
        (∃ t ∈ B.T, (b : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) a) → wt a = wt b := by
      rintro X a b ⟨t, -, h⟩
      rw [h, hwt]
    have hout : ∀ (X : Set (Submodule K.O B.A)) (o : Quot (fun L M : X => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L)),
        wt ((Quot.out o : X) : Submodule K.O B.A) = Quot.lift (fun a : X => wt a) (hrel X) o := by
      intro X o
      conv_rhs => rw [← Quot.out_eq o]
    show (∑ᶠ o : Quot (fun L M : B.X (x * (u * B.σ (u : B.A))) => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L), wt ((Quot.out o : B.X (x * (u * B.σ (u : B.A)))) : Submodule K.O B.A)) =
      ∑ᶠ o : Quot (fun L M : B.X x => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L), wt ((Quot.out o : B.X x) : Submodule K.O B.A)
    simp only [hout]
    have hφ : ∀ L : B.X (x * (u * B.σ (u : B.A))), _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) L ∈ B.X x :=
      fun L => (mem_X_mul_unit_sigma_iff B x u L).mp L.2
    have hψ : ∀ M : B.X x, _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) M ∈ B.X (x * (u * B.σ (u : B.A))) := by
      intro M
      refine (mem_X_mul_unit_sigma_iff B x u _).mpr ?_
      have hM : _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) (_root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) M) = M :=
        (_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).right_inv (M : Submodule K.O B.A)
      rw [hM]
      exact M.2
    let e : Quot (fun L M : B.X (x * (u * B.σ (u : B.A))) => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) ≃
        Quot (fun L M : B.X x => ∃ t ∈ B.T, (M : Submodule K.O B.A) = _root_.GlobalTheory.UnitLemma.mulLat K.O (t : B.A) L) :=
      { toFun := Quot.map (fun L => ⟨_, hφ L⟩) (by
          rintro a b ⟨t, ht, h⟩
          refine ⟨t, ht, ?_⟩
          show _root_.GlobalTheory.UnitLemma.mulLat K.O (u : B.A) b = _
          rw [h]
          exact mulLat_unit_comm u t (a : Submodule K.O B.A))
        invFun := Quot.map (fun M => ⟨_, hψ M⟩) (by
          rintro a b ⟨t, ht, h⟩
          refine ⟨t, ht, ?_⟩
          show _root_.GlobalTheory.UnitLemma.mulLat K.O ((u⁻¹ : B.Aˣ) : B.A) b = _
          rw [h]
          exact mulLat_unit_comm u⁻¹ t (a : Submodule K.O B.A))
        left_inv := by
          intro o
          induction o using Quot.ind with
          | mk L => exact congrArg (Quot.mk _) (Subtype.ext ((_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).left_inv (L : Submodule K.O B.A)))
        right_inv := by
          intro o
          induction o using Quot.ind with
          | mk M => exact congrArg (Quot.mk _) (Subtype.ext ((_root_.GlobalTheory.UnitLemma.NormClass.mulLatEquiv u).right_inv (M : Submodule K.O B.A))) }
    rw [← finsum_comp_equiv e]
    refine finsum_congr fun o => ?_
    induction o using Quot.ind with
    | mk L => exact (hwt u (L : Submodule K.O B.A)).symm
  · let φ : B.A ≃ₗ[K.E] B.A :=
      { LinearMap.mulLeft K.E (u : B.A) with
        invFun := fun z => ((u⁻¹ : B.Aˣ) : B.A) * z
        left_inv := fun z => Units.inv_mul_cancel_left u z
        right_inv := fun z => Units.mul_inv_cancel_left u z }
    have e : B.gramDet (x * (u * B.σ (u : B.A))) =
        (Matrix.of fun i j => B.herm x (((Module.finBasis K.E B.A).map φ) i)
          (((Module.finBasis K.E B.A).map φ) j)).det := by
      unfold _root_.GlobalTheory.UnitLemma.InvAlg.gramDet
      simp only [herm_mul_unit_sigma, Module.Basis.map_apply]
      rfl
    rw [e, _root_.GlobalTheory.UnitLemma.Orbit.eta_gram]
end _root_.GlobalTheory.UnitLemma.NormClass
end GlobalTheory.UnitLemma.NormClass
