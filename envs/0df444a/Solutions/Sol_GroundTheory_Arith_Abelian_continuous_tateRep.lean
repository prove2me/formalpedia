-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.continuous_tateRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:31.616928+00:00
-- url     : https://prove2.me/submissions/a588ba7b-0640-4f82-973d-c46e4073bfba

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
import Theorems.Thm_GroundTheory_Arith_Abelian_TateModule_isOpen_setOf_apply_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open AddSubgroup
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* AddMonoid.End A) (hφ : ∀ a : A, IsOpen {g : G | φ g a = a}) :
    Continuous (fun p : G × TateModule ℓ A => tateRep φ p.1 p.2) := by
  letI : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  apply continuous_induced_rng.2
  apply continuous_pi
  intro k
  rw [continuous_discrete_rng]
  intro a
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨g0, t0⟩ hp
  change φ g0 ((t0 : ℕ → A) k) = a at hp
  refine ⟨{p : G × TateModule ℓ A | φ (g0⁻¹ * p.1) ((t0 : ℕ → A) k) = (t0 : ℕ → A) k ∧
      (p.2 : ℕ → A) k = (t0 : ℕ → A) k}, ?_, ?_, ?_⟩
  · rintro ⟨g, t⟩ ⟨hg, ht⟩
    change φ g ((t : ℕ → A) k) = a
    rw [ht, ← hp]
    calc φ g ((t0 : ℕ → A) k) = φ (g0 * (g0⁻¹ * g)) ((t0 : ℕ → A) k) := by
          rw [mul_inv_cancel_left]
      _ = φ g0 (φ (g0⁻¹ * g) ((t0 : ℕ → A) k)) := by rw [map_mul]; rfl
      _ = φ g0 ((t0 : ℕ → A) k) := by rw [hg]
  · exact ((hφ _).preimage (continuous_const.mul continuous_fst)).inter
      ((TateModule.isOpen_setOf_apply_eq k _).preimage continuous_snd)
  · refine ⟨?_, rfl⟩
    show φ (g0⁻¹ * g0) _ = _
    rw [inv_mul_cancel, map_one]
    rfl
end GroundTheory.Arith.Abelian
