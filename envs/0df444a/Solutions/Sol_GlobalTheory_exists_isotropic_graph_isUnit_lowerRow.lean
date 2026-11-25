-- Prove2me | solution 1 for GlobalTheory.exists_isotropic_graph_isUnit_lowerRow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:14:22.152025+00:00
-- url     : https://prove2.me/submissions/1856b23f-5366-4c21-8c96-f5328ad215ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftModMaximalSkewStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsotropicGraphDetLowerRowNeZeroFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsotropicGraphUnitaryIsUnitLowerBlock
import Theorems.Thm_GlobalTheory_T_exists_isotropic_graph_det_ne_zero
import Theorems.Thm_GlobalTheory_T_exists_skew_lift_mod_maximalIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  have hfield := GlobalTheory.T.exists_isotropic_graph_det_ne_zero
  have hlift := GlobalTheory.T.exists_skew_lift_mod_maximalIdeal

  intro O _ _ c hc h2 hx0 n J hJ hJdet g hg hgu
  obtain ⟨x, hx⟩ := hx0
  haveI : IsLocalHom c := ⟨fun a ha => by simpa [hc] using ha.map c⟩
  set π := IsLocalRing.residue O with hπ
  set σ : IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField O := IsLocalRing.ResidueField.map c with hσ
  have hσπ : ∀ a, σ (π a) = π (c a) := fun a => IsLocalRing.ResidueField.map_residue c a
  have hσσ : ∀ y, σ (σ y) = y := by
    intro y; obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y; rw [hσπ, hσπ, hc]
  have hε : ∃ ε, ε ≠ 0 ∧ σ ε = -ε := ⟨π (c x - x), (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hx, by
    rw [hσπ, map_sub, hc, ← neg_sub, map_neg]⟩
  have hmapc : ∀ {m : Type} (M : Matrix m m O), (M.map c).map π = (M.map π).map σ := by
    intro m M; ext i j; simp [hσπ]
  have hJ' : ∀ i j, σ (J.map π j i) = J.map π i j := by intro i j; simp [hσπ, hJ]
  have hJdet' : (J.map π).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hJdet
  have hg' : (g.map π).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hg
  have hgu' : (g.map π)ᵀ * Matrix.fromBlocks 0 (J.map π) (J.map π) 0 * (g.map π).map σ
      = Matrix.fromBlocks 0 (J.map π) (J.map π) 0 := by
    have := congrArg (fun M => M.map π) hgu
    simpa only [Matrix.map_mul, Matrix.transpose_map, hmapc, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero π)] using this
  obtain ⟨Zb, hZb, hdet⟩ := hfield _ σ hσσ hε n _ hJ' hJdet' _ hg' hgu'
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀ : Matrix (Fin n) (Fin n) O, Z₀.map π = Zb :=
    ⟨fun i j => (IsLocalRing.residue_surjective (Zb i j)).choose, by
      ext i j; exact (IsLocalRing.residue_surjective (Zb i j)).choose_spec⟩
  have hZ₀m : ∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O := by
    intro i j
    rw [← IsLocalRing.residue_eq_zero_iff]
    have := congrArg (fun M => M i j) hZb
    simp only [Matrix.zero_apply] at this
    rw [← this, ← hZ₀, ← hmapc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add π)]
    rfl
  obtain ⟨Z, hZ, hZm⟩ := hlift O c hc h2 n J hJ hJdet Z₀ hZ₀m
  refine ⟨Z, hZ, ?_⟩
  have hZπ : Z.map π = Zb := by
    rw [← hZ₀]; ext i j
    simp only [Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hZm i j
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hπ, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map_add _ (map_add π), Matrix.map_mul, hZπ]
  exact hdet
end GlobalTheory
