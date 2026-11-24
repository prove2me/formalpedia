-- Prove2me | solution 1 for GlobalTheory.HullClasses.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:40:39.646805+00:00
-- url     : https://prove2.me/submissions/9a8fc19e-8e3a-4706-80dc-f461b8943bc2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat
import Theorems.Thm_GlobalTheory_HullClasses_mem_mulLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.HullClasses
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.HullClasses
theorem _root_.solution (x : B.A) (c cb : K.O) (hc : B.σ (algebraMap K.O B.A c) = algebraMap K.O B.A cb) (a b : B.Aˣ)
    (h4 : ∀ y ∈ mulLat K.O (a : B.A) (abelian₂ B), ∀ z ∈ mulLat K.O (a : B.A) (abelian₂ B),
      B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈ (algebraMap K.O K.E).range)
    (h3 : ∀ y, (∀ z ∈ mulLat K.O (b : B.A) (abelian₂ B), B.herm x y z ∈ (algebraMap K.O K.E).range) →
      y ∈ mulLat K.O (b : B.A) (abelian₂ B)) :
    mulLat K.O (algebraMap K.O B.A (c * cb) * ((a : B.A) * B.σ a)) (abelian₂ B) ≤
      mulLat K.O ((b : B.A) * B.σ b) (abelian₂ B) := by
  intro y hy
  obtain ⟨l, hl, rfl⟩ := (mem_mulLat _ _ _).1 hy
  have hb : B.σ (b : B.A) * B.σ ((b⁻¹ : B.Aˣ) : B.A) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hy' : algebraMap K.O B.A (c * cb) * ((a : B.A) * B.σ a) * l * B.σ ((b⁻¹ : B.Aˣ) : B.A) ∈
      mulLat K.O (b : B.A) (abelian₂ B) := by
    apply h3
    intro z hz
    obtain ⟨m, hm, rfl⟩ := (mem_mulLat _ _ _).1 hz
    have := h4 _ ((mem_mulLat _ _ _).2 ⟨l, hl, rfl⟩) _ ((mem_mulLat _ _ _).2 ⟨m, hm, rfl⟩)
    convert this using 1
    unfold InvAlg.herm
    congr 1
    simp only [map_mul, hc]
    linear_combination (x * algebraMap K.O B.A c * algebraMap K.O B.A cb * (a : B.A) * B.σ (a : B.A) * l *
      B.σ m) * hb
  obtain ⟨n, hn, hbn⟩ := (mem_mulLat _ _ _).1 hy'
  refine (mem_mulLat _ _ _).2 ⟨n, hn, ?_⟩
  linear_combination B.σ (b : B.A) * hbn +
    (algebraMap K.O B.A (c * cb) * ((a : B.A) * B.σ a) * l) * hb
end GlobalTheory.HullClasses
