-- Prove2me | solution 1 for GlobalTheory.UnitLemma.SgnProd.sgnLat_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:48.035894+00:00
-- url     : https://prove2.me/submissions/d0f0e375-1e84-4de8-9fb4-e7350edf766b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatProdEqEtaResultantMul
import Theorems.Thm_GlobalTheory_UnitLemma_SgnProd_eta_mul
import Theorems.Thm_GlobalTheory_UnitLemma_SgnProd_eta_of_sq_one
import Theorems.Thm_GlobalTheory_UnitLemma_SgnProd_det_trace_ne_zero
import Theorems.Thm_GlobalTheory_UnitLemma_SgnProd_lattice_split
import Theorems.Thm_GlobalTheory_UnitLemma_SgnProd_det_trace_lift
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_eta_mul
import Theorems.Thm_GlobalTheory_UnitLemma_SgnBasis_sgnLat_span_basis
import Theorems.Thm_GlobalTheory_det_trace_pow_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.SgnProd
open Module
namespace GlobalTheory.UnitLemma.SgnProd
theorem _root_.solution : ∀ (K : UQ) (B₁ B₂ : InvAlg K), (B₁.P * B₂.P).Separable → ∀ M ∈ (B₁.prod B₂).Lin,
    (B₁.prod B₂).sgnLat M = K.eta (resultant B₁.P B₂.P) *
      B₁.sgnLat (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * B₂.sgnLat (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
  intro K B₁ B₂ hsep M hM
  obtain ⟨hfg, hsp⟩ := hM.1
  obtain ⟨e₁, e₂, x, he₁, he₂, hx, hspan⟩ := lattice_split K B₁.A B₂.A M hfg hsp
  have hP : (B₁.prod B₂).P = B₁.P * B₂.P := by
    have h1 : LinearMap.mulLeft K.E (B₁.prod B₂).g =
        (LinearMap.mulLeft K.E B₁.g).prodMap (LinearMap.mulLeft K.E B₂.g) := by
      exact LinearMap.ext fun _ => rfl
    have h2 := LinearMap.charpoly_prodMap (LinearMap.mulLeft K.E B₁.g) (LinearMap.mulLeft K.E B₂.g)
    rw [← h1] at h2
    exact h2
  let f : Fin (finrank K.E B₁.A + finrank K.E B₂.A) → B₁.A × B₂.A :=
    Fin.addCases (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) x
  have hcard : Fintype.card (Fin (finrank K.E B₁.A + finrank K.E B₂.A)) = finrank K.E (B₁.A × B₂.A) := by
    simp [Module.finrank_prod]
  have htop : ⊤ ≤ Submodule.span K.E (Set.range f) := by
    rw [← Submodule.span_span_of_tower K.O, hspan]
    exact hsp.ge
  let bf : Basis (Fin (finrank K.E B₁.A + finrank K.E B₂.A)) K.E (B₁.A × B₂.A) :=
    basisOfTopLeSpanOfCardEqFinrank f htop hcard
  have hbf : ⇑bf = f := coe_basisOfTopLeSpanOfCardEqFinrank f htop hcard
  have hN : finrank K.E B₁.A + finrank K.E B₂.A = finrank K.E (B₁.prod B₂).A := by
    rw [← Fintype.card_fin (finrank K.E B₁.A + finrank K.E B₂.A)]
    exact hcard
  let bF : Basis (Fin (finrank K.E (B₁.prod B₂).A)) K.E (B₁.prod B₂).A := bf.reindex (finCongr hN)
  have hrange : Set.range ⇑bF = Set.range f := by
    exact (Basis.range_reindex bf (finCongr hN)).trans (by rw [hbf])
  have hspanF : Submodule.span K.O (Set.range ⇑bF) = M := by
    rw [hrange]
    exact hspan
  have key := SgnBasis.sgnLat_span_basis K (B₁.prod B₂) bF
  rw [hspanF] at key
  rw [key, ← he₁, ← he₂, SgnBasis.sgnLat_span_basis K B₁ e₁, SgnBasis.sgnLat_span_basis K B₂ e₂]
  have hdet : (Matrix.of fun k l : Fin (finrank K.E (B₁.prod B₂).A) =>
      Algebra.trace K.E (B₁.prod B₂).A ((B₁.prod B₂).g ^ (k : ℕ) * bF l)).det =
      (Matrix.of fun k l : Fin (finrank K.E B₁.A + finrank K.E B₂.A) =>
        Algebra.trace K.E (B₁.A × B₂.A) ((B₁.g, B₂.g) ^ (k : ℕ) * f l)).det := by
    rw [← Matrix.det_submatrix_equiv_self (finCongr hN).symm]
    congr 1
    ext k l
    have hbF : bF l = f ((finCongr hN).symm l) := by
      rw [← hbf]
      exact Basis.reindex_apply bf (finCongr hN) l
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    erw [hbF]
    simp only [finCongr_symm, finCongr_apply, Fin.val_cast]
    rfl
  obtain ⟨ε, hε, hL7⟩ := GlobalTheory.det_trace_pow_prod K.E B₁.A B₂.A B₁.g B₂.g _ _ e₁ e₂ hsep
  have hchain : (Matrix.of fun k l : Fin (finrank K.E (B₁.prod B₂).A) =>
      Algebra.trace K.E (B₁.prod B₂).A ((B₁.prod B₂).g ^ (k : ℕ) * bF l)).det =
      ε * resultant B₁.P B₂.P * (Matrix.of fun k l : Fin (finrank K.E B₁.A) =>
        Algebra.trace K.E B₁.A (B₁.g ^ (k : ℕ) * e₁ l)).det * (Matrix.of fun k l : Fin (finrank K.E B₂.A) =>
        Algebra.trace K.E B₂.A (B₂.g ^ (k : ℕ) * e₂ l)).det :=
    hdet.trans ((det_trace_lift (B₁.g, B₂.g) e₁ e₂ x hx).trans hL7)
  have hne := det_trace_ne_zero (B₁.prod B₂) (by rw [hP]; exact hsep) bF
  rw [hchain] at hne ⊢
  simp only [mul_ne_zero_iff] at hne
  obtain ⟨⟨⟨-, hR⟩, h₁⟩, h₂⟩ := hne
  rw [mul_assoc, mul_assoc, eta_of_sq_one K hε, eta_mul K hR (mul_ne_zero h₁ h₂), eta_mul K h₁ h₂, mul_assoc]
end GlobalTheory.UnitLemma.SgnProd
