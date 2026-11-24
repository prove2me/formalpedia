-- Prove2me | solution 1 for GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:04:01.588177+00:00
-- url     : https://prove2.me/submissions/a6a7fafa-320c-436f-9ae6-5c2ca03210ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsStandardUnipotentRadicalBijOnNilradical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.CuspGL.UnipNilRad
variable {F : Type} [Field F]
open Polynomial in
variable {F : Type} [Field F] in
private lemma card_fin_le_val_eq_sub (d a : ℕ) : Fintype.card {i : Fin d // a ≤ i.val} = d - a := by
  rw [Fintype.card_subtype, ← Finset.card_map Fin.valEmbedding, ← Nat.card_Ico a d]
  congr 1
  ext n
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply, Finset.mem_Ico]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hi, i.isLt⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨n, h2⟩, h1, rfl⟩
open Polynomial in
variable {F : Type} [Field F] in
private lemma finrank_lowSub_of_le {d a : ℕ} (had : a ≤ d) :
    Module.finrank F (_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a) = a := by
  have hs := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.funLeft F F (Subtype.val : {i : Fin d // a ≤ i.val} → Fin d))
  rw [LinearMap.range_eq_top.mpr
    (LinearMap.funLeft_surjective_of_injective _ _ _ Subtype.val_injective),
    finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    card_fin_le_val_eq_sub, Fintype.card_fin] at hs
  rw [_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub]
  omega
open Polynomial in
variable {F : Type} [Field F] in
private lemma mem_lowSub_iff_apply_eq_zero {d a : ℕ} (v : Fin d → F) :
    v ∈ _root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a ↔ ∀ i : Fin d, a ≤ i.val → v i = 0 := by
  rw [_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub, LinearMap.mem_ker]
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.1 i.2
open Polynomial in
variable {F : Type} [Field F] in
private lemma toLin'_mem_nilRad_lowSub_iff {d a : ℕ} (N : Matrix (Fin d) (Fin d) F) :
    Matrix.toLin' N ∈ _root_.GlobalTheory.CuspGL.nilRad (_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a) ↔
      ∀ i j : Fin d, N i j = 0 ∨ (i.val < a ∧ a ≤ j.val) := by
  show ((∀ x, Matrix.toLin' N x ∈ _) ∧ ∀ x ∈ _, Matrix.toLin' N x = 0) ↔ _
  simp only [Matrix.toLin'_apply, mem_lowSub_iff_apply_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩ i j
    by_cases hi : a ≤ i.val
    · left
      have := h1 (Pi.single j 1) i hi
      simpa [Matrix.mulVec_single_one] using this
    by_cases hj : a ≤ j.val
    · exact Or.inr ⟨by omega, hj⟩
    · left
      have hx : ∀ k : Fin d, a ≤ k.val → (Pi.single j (1 : F) : Fin d → F) k = 0 := by
        intro k hk
        have : k ≠ j := fun h => hj (h ▸ hk)
        simp [Pi.single_apply, this]
      have := congrFun (h2 _ hx) i
      simpa [Matrix.mulVec_single_one] using this
  · intro h
    refine ⟨fun x i hi => ?_, fun x hx => ?_⟩
    · rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases h i j with h0 | ⟨hlt, _⟩
      · simp [h0]
      · omega
    · funext i
      rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases h i j with h0 | ⟨_, hj⟩
      · simp [h0]
      · simp [hx j hj]
end GlobalTheory.CuspGL.UnipNilRad
end

set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.UnipNilRad
variable {F : Type} [Field F]
open Polynomial
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL.UnipNilRad
namespace _root_.GlobalTheory.CuspGL.UnipNilRad
theorem _root_.solution :
    ∀ (F : Type) [Field F] [Finite F] (d a : ℕ), a ≤ d → ∃ (A : Submodule F (Fin d → F)) (H : Subgroup (GL (Fin d) F)), Module.finrank F A = a ∧ (H : Set (GL (Fin d) F)) = {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)} ∧ Set.BijOn (fun u : GL (Fin d) F => Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1) (H : Set (GL (Fin d) F)) (_root_.GlobalTheory.CuspGL.nilRad A) := by
  intro F _ _ d a had
  refine ⟨_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a,
    _root_.GlobalTheory.CuspGL.UnipNilRad.unip (_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a),
    finrank_lowSub_of_le had, ?_, ?_⟩
  · ext u
    show Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1 ∈
      _root_.GlobalTheory.CuspGL.nilRad (_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a) ↔ _
    have hsub : Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1 =
        Matrix.toLin' ((u : Matrix (Fin d) (Fin d) F) - 1) := by
      rw [map_sub, Matrix.toLin'_one]
      rfl
    rw [hsub, toLin'_mem_nilRad_lowSub_iff, Set.mem_setOf_eq]
    simp only [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]
  · refine ⟨fun u hu => hu, fun u _ v _ h => ?_, fun f hf => ?_⟩
    · exact Units.ext (Matrix.toLin'.injective (sub_left_injective h))
    · set N := LinearMap.toMatrix' f with hNdef
      have hNf : Matrix.toLin' N = f := Matrix.toLin'_toMatrix' f
      have hN : N * N = 0 := by
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun x => ?_
        rw [Matrix.toLin'_mul, LinearMap.comp_apply, hNf, map_zero, LinearMap.zero_apply]
        exact hf.2 _ (hf.1 x)
      let u : GL (Fin d) F := ⟨1 + N, 1 - N, by noncomm_ring; rw [hN]; simp,
        by noncomm_ring; rw [hN]; simp⟩
      have hu : Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1 = f := by
        show Matrix.toLin' (1 + N) - 1 = f
        rw [map_add, Matrix.toLin'_one, hNf]
        exact add_sub_cancel_left (1 : Module.End F (Fin d → F)) f
      refine ⟨u, ?_, hu⟩
      show Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1 ∈
        _root_.GlobalTheory.CuspGL.nilRad (_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a)
      rw [hu]
      exact hf
end _root_.GlobalTheory.CuspGL.UnipNilRad
end GlobalTheory.CuspGL.UnipNilRad
