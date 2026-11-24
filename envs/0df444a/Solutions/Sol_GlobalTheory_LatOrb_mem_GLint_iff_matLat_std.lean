-- Prove2me | solution 1 for GlobalTheory.LatOrb.mem_GLint_iff_matLat_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:38.274291+00:00
-- url     : https://prove2.me/submissions/c1269cc1-be76-4c2a-b263-5eeb8d84a865

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGLintIffMatrixImageStandardLatticeEq
import Theorems.Thm_GlobalTheory_LatOrbGL_matLat_le_of_entries
import Theorems.Thm_GlobalTheory_LatOrbGL_entries_of_matLat_le
import Theorems.Thm_GlobalTheory_LatOrbGL_matLat_mono
import Theorems.Thm_GlobalTheory_LatOrb_matLat_mul
import Theorems.Thm_GlobalTheory_LatOrb_matLat_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory.LatOrbGL
namespace GlobalTheory.LatOrb
theorem _root_.solution :
    ∀ {K : Type} [Field K] (V : ValuationSubring K) (n : ℕ) (k : GL (Fin n) K),
    k ∈ Formalism.UG.GLint (Fin n) V.toSubring ↔ matLat V k.val (stdLat V n) = stdLat V n := by
  intro K _ V n k
  constructor
  · rintro ⟨g, rfl⟩
    set k := Formalism.UG.bc V.toSubring.subtype g with hk
    have e1 : ∀ i j, k.val i j ∈ V := by
      intro i j; exact ((g : Matrix (Fin n) (Fin n) V.toSubring) i j).2
    have e2 : ∀ i j, (k⁻¹).val i j ∈ V := by
      intro i j; rw [hk, ← map_inv]; exact (((g⁻¹ : GL (Fin n) V.toSubring) : Matrix (Fin n) (Fin n) V.toSubring) i j).2
    apply le_antisymm (matLat_le_of_entries V _ e1)
    have : k.val * (k⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc stdLat V n = matLat V (k.val * (k⁻¹).val) (stdLat V n) := by rw [this, matLat_one]
      _ = _ := matLat_mul _ _ _
      _ ≤ _ := matLat_mono V _ (matLat_le_of_entries V _ e2)
  · intro h
    have e1 := entries_of_matLat_le V k.val h.le
    have h2 : matLat V (k⁻¹ : GL (Fin n) K).val (stdLat V n) = stdLat V n := by
      conv_lhs => rw [← h]
      rw [← matLat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, matLat_one]
    have e2 := entries_of_matLat_le V (k⁻¹ : GL (Fin n) K).val h2.le
    let A : Matrix (Fin n) (Fin n) V.toSubring := Matrix.of fun i j => ⟨k.val i j, e1 i j⟩
    let B : Matrix (Fin n) (Fin n) V.toSubring := Matrix.of fun i j => ⟨(k⁻¹ : GL (Fin n) K).val i j, e2 i j⟩
    have hA : (RingHom.mapMatrix V.toSubring.subtype) A = k.val := by ext i j; rfl
    have hB : (RingHom.mapMatrix V.toSubring.subtype) B = (k⁻¹ : GL (Fin n) K).val := by ext i j; rfl
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) V.toSubring.subtype) := by
      intro X Y hXY; ext i j; exact congrFun (congrFun hXY i) j
    have hAB : A * B = 1 := inj (by rw [map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one])
    have hBA : B * A = 1 := inj (by rw [map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one])
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    rfl
end GlobalTheory.LatOrb
