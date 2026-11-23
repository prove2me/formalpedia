-- Prove2me | solution 1 for GlobalTheory.ZH.exists_basis_adapted_to_idempotents
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:38.693662+00:00
-- url     : https://prove2.me/submissions/57214fce-ca33-4f12-992f-9b557933d009

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedToIdempotents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module
namespace GlobalTheory.ZH
open Module in
private lemma mulVec_column_of_orthogonal_idempotents {R J C : Type} [CommRing R] [Fintype J]
    [DecidableEq C] (e : C → Matrix J J R)
    (he : ∀ c c', e c * e c' = if c = c' then e c else 0) (d c : C) (s : J) :
    (e d).mulVec (fun j => e c j s) = if d = c then (fun j => e c j s) else 0 := by
  ext i
  have h := congrFun (congrFun (he d c) i) s
  rw [Matrix.mul_apply] at h
  simp only [Matrix.mulVec, dotProduct]
  rw [h]
  split_ifs with hdc
  · subst hdc; rfl
  · rfl
end GlobalTheory.ZH
end

set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.ZH
open Module
namespace GlobalTheory.ZH
namespace _root_.GlobalTheory.ZH
theorem _root_.solution :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (J C : Type) [Fintype J] [DecidableEq J] [Fintype C]
      [DecidableEq C] (e : C → Matrix J J O),
      (∀ c c', e c * e c' = if c = c' then e c else 0) → ∑ c, e c = 1 →
      ∃ (κ : J → C) (col : J → J),
        IsUnit (Matrix.det (Matrix.of fun i j => e (κ i) j (col i))) ∧
        ∀ c, Submodule.span O (Set.range fun i => fun j => e c j i) =
          Submodule.span O {v | ∃ i, κ i = c ∧ v = fun j => e c j (col i)} := by
  intro O _ _ J C _ _ _ _ e he hsum
  classical
  let f : Matrix J J O →+* Matrix J J (IsLocalRing.ResidueField O) :=
    (IsLocalRing.residue O).mapMatrix
  let E : C → Matrix J J (IsLocalRing.ResidueField O) := fun c => f (e c)
  have hE : ∀ c c', E c * E c' = if c = c' then E c else 0 := by
    intro c c'
    simp only [E, ← map_mul, he]
    split_ifs <;> simp
  have hEsum : ∑ c, E c = 1 := by simp only [E, ← map_sum, hsum, map_one]
  let w : C → J → (J → IsLocalRing.ResidueField O) := fun c s j => E c j s
  choose T a ha hsp hli using fun c => exists_linearIndependent' (IsLocalRing.ResidueField O) (w c)
  haveI : ∀ c, Fintype (T c) := fun c => Fintype.ofInjective (a c) (ha c)
  let W : (Σ c, T c) → (J → IsLocalRing.ResidueField O) := fun p => w p.1 (a p.1 p.2)
  have hWli : LinearIndependent (IsLocalRing.ResidueField O) W := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    obtain ⟨d, t⟩ := p
    have h1 := congrArg (Matrix.mulVecLin (E d)) hg
    simp only [map_sum, map_smul, map_zero, Matrix.mulVecLin_apply, W, w,
      mulVec_column_of_orthogonal_idempotents E hE, Fintype.sum_sigma, smul_ite, smul_zero] at h1
    rw [Finset.sum_eq_single d (fun c _ hc => by simp [Ne.symm hc]) (by simp)] at h1
    simp only [if_pos rfl] at h1
    exact Fintype.linearIndependent_iff.mp (hli d) (fun t => g ⟨d, t⟩) h1 t
  have hWsp : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField O) (Set.range W) := by
    rw [← (Pi.basisFun (IsLocalRing.ResidueField O) J).span_eq, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    have hs : Pi.basisFun (IsLocalRing.ResidueField O) J s = ∑ c, w c s := by
      ext j
      have := congrFun (congrFun hEsum j) s
      simp only [Matrix.sum_apply, Matrix.one_apply] at this
      simp [w, Finset.sum_apply, this, Pi.single_apply]
    rw [hs]
    refine Submodule.sum_mem _ fun c _ => ?_
    have h2 : w c s ∈ Submodule.span (IsLocalRing.ResidueField O) (Set.range (w c ∘ a c)) := by
      rw [hsp c]; exact Submodule.subset_span ⟨s, rfl⟩
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨t, rfl⟩
    exact ⟨⟨c, t⟩, rfl⟩
  let b := Basis.mk hWli hWsp
  have hcard : Fintype.card J = Fintype.card (Σ c, T c) := by
    rw [← Module.finrank_fintype_fun_eq_card (IsLocalRing.ResidueField O),
      Module.finrank_eq_card_basis b]
  let σ : J ≃ (Σ c, T c) := Fintype.equivOfCardEq hcard
  let M : Matrix J J O := Matrix.of fun i j => e (σ i).1 j (a (σ i).1 (σ i).2)
  have hdet : IsUnit M.det := by
    rw [← isUnit_map_iff (IsLocalRing.residue O), RingHom.map_det,
      ← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_rows_iff_isUnit]
    exact hWli.comp σ σ.injective
  refine ⟨fun i => (σ i).1, fun i => a (σ i).1 (σ i).2, hdet, fun c => le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    show (fun j => e c j s) ∈ Submodule.span O _
    have hfix : (e c).mulVec (fun j => e c j s) = fun j => e c j s := by
      simpa using mulVec_column_of_orthogonal_idempotents e he c c s
    have h3 : (fun j => e c j s) = Matrix.vecMul (Matrix.vecMul (fun j => e c j s) M⁻¹) M := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
    have h4 : (fun j => e c j s) =
        ∑ i, (Matrix.vecMul (fun j => e c j s) M⁻¹) i • (e c).mulVec (M i) := by
      calc (fun j => e c j s) = (e c).mulVec (fun j => e c j s) := hfix.symm
        _ = (e c).mulVec (Matrix.vecMul (Matrix.vecMul (fun j => e c j s) M⁻¹) M) := by rw [← h3]
        _ = _ := by
          rw [Matrix.vecMul_eq_sum]
          simp only [← Matrix.mulVecLin_apply, map_sum, map_smul]
    rw [h4]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have h5 : (e c).mulVec (M i) = if c = (σ i).1 then M i else 0 :=
      mulVec_column_of_orthogonal_idempotents e he c (σ i).1 _
    rw [h5]
    split_ifs with h
    · exact Submodule.subset_span ⟨i, h.symm, by subst h; rfl⟩
    · exact zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨i, -, rfl⟩
    exact Submodule.subset_span ⟨a (σ i).1 (σ i).2, rfl⟩
end _root_.GlobalTheory.ZH
end GlobalTheory.ZH
