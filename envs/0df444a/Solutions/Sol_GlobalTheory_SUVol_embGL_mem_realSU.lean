-- Prove2me | solution 1 for GlobalTheory.SUVol.embGL_mem_realSU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:09:16.604586+00:00
-- url     : https://prove2.me/submissions/8e338d2f-ba22-4862-b57e-ca662082a805

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Statements_PlaceShiftStatements_DefiniteBound
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EmbGLMemRealSU_dd53fabb718cd1c0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory.SUVol
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped ENNReal NNReal
section General
variable {ι : Type} [Fintype ι] {r : ℕ}
end General
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology in
open scoped ENNReal NNReal in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma hermC_map_mulVec_eq_of_preserves_form (τ : E →+* ℂ) (G M : Matrix (Fin r) (Fin r) E)
    (hK : ∀ a b, ∑ i, ∑ j, M i a * G i j * IsCMField.complexConj E (M j b) = G a b) (u w : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (M.map τ *ᵥ u) (M.map τ *ᵥ w) = _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u w := by
  have hK' : ∀ a b, τ (G a b) = ∑ i, ∑ j, τ (M i a) * τ (G i j) * starRingEnd ℂ (τ (M j b)) := by
    intro a b
    rw [← hK a b]
    simp [map_sum, IsCMField.complexEmbedding_complexConj]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC
  conv_rhs => rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hK' a b]]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory.SUVol
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SUVol
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped ENNReal NNReal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.SUVol
namespace _root_.GlobalTheory.SUVol
theorem _root_.solution (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (γ : GL (Fin r) E) (h1 : (γ : Matrix (Fin r) (Fin r) E).det = 1)
    (h2 : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y) :
    _root_.GlobalTheory.SUVol.embGL Ψ r γ ∈ _root_.GlobalTheory.SUVol.realSU Ψ G := by
  have hK : ∀ a b, ∑ i, ∑ j, (γ : Matrix (Fin r) (Fin r) E) i a * G i j *
      IsCMField.complexConj E ((γ : Matrix (Fin r) (Fin r) E) j b) = G a b := by
    intro a b
    have h := h2 (Pi.single a 1) (Pi.single b 1)
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc at h
    simpa [Pi.single_apply, Matrix.mulVec_single_one] using h
  refine fun τ => ?_
  have hv : ((_root_.GlobalTheory.SUVol.embGL Ψ r γ τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 :=
    Matrix.GeneralLinearGroup.val_map_apply τ.1 γ
  rw [hv]
  exact ⟨by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h1, map_one],
    hermC_map_mulVec_eq_of_preserves_form τ.1 G _ hK⟩
end _root_.GlobalTheory.SUVol
end GlobalTheory.SUVol
