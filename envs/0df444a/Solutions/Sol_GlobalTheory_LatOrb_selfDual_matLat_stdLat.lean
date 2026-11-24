-- Prove2me | solution 1 for GlobalTheory.LatOrb.selfDual_matLat_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:53:21.092249+00:00
-- url     : https://prove2.me/submissions/2038a218-c80f-4842-a13b-59813542abf3

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSelfDualImageStandardLatticeUnitary
import Theorems.Thm_GlobalTheory_LatOrb_herm_mulVec_right
import Theorems.Thm_GlobalTheory_LatOrb_mem_matLat
import Theorems.Thm_GlobalTheory_LatOrb_mem_stdLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.LatOrb
namespace GlobalTheory.LatOrb
theorem _root_.solution {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K)
    (_hinv : ∀ x, σ (σ x) = x) (hO : ∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b)
    (n : ℕ) (g : Matrix (Fin n) (Fin n) K) (hg : (g.map σ)ᵀ * g = 1) :
    SelfDual O σ (matLat O g (stdLat O n)) := by
  have hg' : g * (g.map σ)ᵀ = 1 := mul_eq_one_comm.mp hg
  have hσO : ∀ z ∈ (algebraMap O K).range, σ z ∈ (algebraMap O K).range := by
    rintro z ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hO a
    exact ⟨b, hb.symm⟩
  intro y
  rw [mem_matLat]
  constructor
  · rintro ⟨u, hu, rfl⟩ x hx
    rw [mem_matLat] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [herm_mulVec_right, Matrix.mulVec_mulVec, hg, Matrix.one_mulVec]
    unfold herm
    refine Subring.sum_mem _ (fun k _ => Subring.mul_mem _ ((mem_stdLat u).mp hu k) (hσO _ ((mem_stdLat v).mp hv k)))
  · intro h
    refine ⟨(g.map σ)ᵀ *ᵥ y, ?_, by rw [Matrix.mulVec_mulVec, hg', Matrix.one_mulVec]⟩
    rw [mem_stdLat]
    intro j
    have hx : g *ᵥ (Pi.single j 1 : Fin n → K) ∈ matLat O g (stdLat O n) := by
      rw [mem_matLat]
      refine ⟨Pi.single j 1, ?_, rfl⟩
      rw [mem_stdLat]
      intro i
      by_cases hij : i = j
      · subst hij; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_apply, hij]⟩
    have := h _ hx
    rw [herm_mulVec_right] at this
    simpa [herm, Pi.single_apply, map_one] using this
end GlobalTheory.LatOrb
