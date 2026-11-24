-- Prove2me | solution 1 for GlobalTheory.CotPoints.points_eq_tangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:00:05.993809+00:00
-- url     : https://prove2.me/submissions/4dfac3d3-1271-4bd4-8ce2-410230b382be

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PointsEqTangent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
namespace GlobalTheory.CotPoints
private lemma comp_assoc' {R₀ : Type} [CommRing R₀] {A B C D : LAlg R₀} (h : LHom C D)
    (g : LHom B C) (f : LHom A B) : (h.comp g).comp f = h.comp (g.comp f) := rfl
private lemma coords_bijective {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {g : ℕ} (b : Module.Basis (Fin g) R M) :
    Function.Bijective (fun m : Fin g → N => ∑ k, b k ⊗ₜ[R] m k) := by
  classical
  have h : (fun m : Fin g → N => ∑ k, b k ⊗ₜ[R] m k) =
      (TensorProduct.equivFinsuppOfBasisLeft (N := N) b).symm ∘ Finsupp.equivFunOnFinite.symm := by
    funext m
    simp only [Function.comp, TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp
  rw [h]
  exact (LinearEquiv.bijective _).comp (Equiv.bijective _)
private lemma coords_nsmul {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {g : ℕ} (b : Module.Basis (Fin g) R M) (n : ℕ)
    (m : Fin g → N) : n • ∑ k, b k ⊗ₜ[R] m k = ∑ k, b k ⊗ₜ[R] (n • m k) := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => (map_nsmul (TensorProduct.mk R M N (b k)) n (m k)).symm
section
variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p}
  {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe]
  {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp)
private lemma ptMap_spec (t : Nb p g) :
    (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = LHom.id Tw.O ∧
      B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = ptOf B D.L.τ t ∧
      ∀ j (φ' : LHom (D.fin.AAx j) Tw.O), φ'.comp (D.fin.sO j) = LHom.id Tw.O →
        B.map φ' (D.fin.y j) = ptOf B D.L.τ t → j = D.ptIdx t ∧ HEq φ' (D.ptMap t) :=
  Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t)))
private lemma ptOf_zero : ptOf B D.L.τ (0 : Nb p g) = 0 := by
  simp [ptOf]
end
end GlobalTheory.CotPoints
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory GlobalTheory.CotPoints
namespace GlobalTheory.CotPoints
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), ∀ (S : LAlg R₀) (s : LHom Tw.O S) (π : LHom S Tw.O) (hπ : π.SqZero), π.comp s = LHom.id Tw.O →
    (∀ m : Fin g → π.ker, (∀ k, p • m k = 0) → ∃! φ : LHom (D.fin.AAx (D.ptIdx 0)) S, φ.comp (D.fin.sO (D.ptIdx 0)) = s ∧ π.comp φ = (D.ptMap 0) ∧
      B.map φ (D.fin.y (D.ptIdx 0)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k)) ∧
    (∀ φ : LHom (D.fin.AAx (D.ptIdx 0)) S, φ.comp (D.fin.sO (D.ptIdx 0)) = s → π.comp φ = (D.ptMap 0) → ∃! m : Fin g → π.ker, (∀ k, p • m k = 0) ∧
      B.map φ (D.fin.y (D.ptIdx 0)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k))) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D S s π hπ hs
  obtain ⟨-, h2, h3⟩ := ptMap_spec D 0
  rw [ptOf_zero D] at h2 h3
  refine ⟨fun m hm => ?_, fun φ hφ hπφ => ?_⟩
  · have hz : p • B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k) = 0 := by
      rw [← map_nsmul, coords_nsmul]
      simp [hm]
    obtain ⟨i, φ, e1, e2, e3⟩ := D.fin.univ S s _ hz
    have h4 := h3 i (π.comp φ) (by rw [comp_assoc', e1, hs])
      (by rw [B.map_comp, e2]; exact (B.tg_ker π hπ _).2 ⟨_, rfl⟩)
    obtain ⟨hi, hφ⟩ := h4
    subst hi
    refine ⟨φ, ⟨e1, eq_of_heq hφ, e2⟩, fun φ' h' => ?_⟩
    exact eq_of_heq (e3 _ φ' h'.1 h'.2.2).2
  · have h0 : B.map π (B.map φ (D.fin.y (D.ptIdx 0))) = 0 := by
      rw [← B.map_comp, hπφ, h2]
    obtain ⟨v, hv⟩ := (B.tg_ker π hπ _).1 h0
    have hb := coords_bijective (N := π.ker) D.ch.gb
    obtain ⟨m, hm⟩ := hb.2 v
    have hm' : ∑ k, D.ch.gb k ⊗ₜ[R₀] m k = v := hm
    have hp : p • v = 0 := by
      apply B.tg_inj π hπ
      rw [map_nsmul, hv, ← map_nsmul, D.fin.y_p, map_zero, map_zero]
    refine ⟨m, ⟨fun k => ?_, by rw [hm', hv]⟩, fun m' h' => ?_⟩
    · have : (fun k => p • m k) = (0 : Fin g → π.ker) := by
        apply hb.1
        show ∑ k, D.ch.gb k ⊗ₜ[R₀] (p • m k) = ∑ k, D.ch.gb k ⊗ₜ[R₀] (0 : Fin g → π.ker) k
        rw [← coords_nsmul, hm', hp]
        simp
      exact congrFun this k
    · apply hb.1
      apply B.tg_inj π hπ
      show B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m' k) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k)
      rw [← h'.2, hm', hv]
end GlobalTheory.CotPoints
