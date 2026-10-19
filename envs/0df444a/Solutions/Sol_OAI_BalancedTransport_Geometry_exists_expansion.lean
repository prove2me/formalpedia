-- Prove2me | solution 1 for OAI.BalancedTransport.Geometry.exists_expansion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:50:06.366023+00:00
-- url     : https://prove2.me/submissions/4b03acb3-4111-4b58-b370-3df51ac0db0e

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryMotion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus

open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι]


theorem solution {a b : ι → Space} (ha : Function.Injective a)
    (hb : Function.Injective b) {D R : ℝ} (hD : 0 ≤ D) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ R + 2 ≤ Λ ∧
      CenterSeparated (fun i k => Λ * a i k) D ∧
      CenterSeparated (fun i k => Λ * b i k) D := by
  classical
  have key : ∀ p : ι × ι, ∃ e : ℝ, 0 < e ∧ (p.1 ≠ p.2 → (∃ k, e ≤ |a p.1 k - a p.2 k|) ∧ ∃ k, e ≤ |b p.1 k - b p.2 k|) := by
    rintro ⟨i, j⟩
    by_cases hij : i = j
    · exact ⟨1, one_pos, fun h' => absurd hij h'⟩
    · have h1 : a i ≠ a j := fun h => hij (ha h)
      have h2 : b i ≠ b j := fun h => hij (hb h)
      obtain ⟨k, hk⟩ := Function.ne_iff.mp h1
      obtain ⟨l, hl⟩ := Function.ne_iff.mp h2
      exact ⟨min |a i k - a j k| |b i l - b j l|,
        lt_min (abs_pos.mpr (sub_ne_zero.mpr hk)) (abs_pos.mpr (sub_ne_zero.mpr hl)),
        fun _ => ⟨⟨k, min_le_left _ _⟩, ⟨l, min_le_right _ _⟩⟩⟩
  choose e he hsep using key
  let S : Finset ℝ := insert 1 (Finset.univ.image e)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hδpos : 0 < S.min' hS := by
    have hm := Finset.min'_mem S hS
    rcases Finset.mem_insert.mp hm with h1 | h1
    · rw [h1]; exact one_pos
    · obtain ⟨p, _, hp⟩ := Finset.mem_image.mp h1
      rw [← hp]; exact he p
  have hle : ∀ p, S.min' hS ≤ e p := fun p =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hDd : 0 ≤ D / S.min' hS := div_nonneg hD hδpos.le
  have hm1 := le_max_left 1 (R+2)
  have hm2 := le_max_right 1 (R+2)
  have hΛ : D / S.min' hS < max 1 (R+2) + D / S.min' hS + 1 := by linarith
  have hΛ0 : 0 ≤ max 1 (R+2) + D / S.min' hS + 1 := by linarith
  have hD1 : D < (max 1 (R+2) + D / S.min' hS + 1) * S.min' hS := (div_lt_iff₀ hδpos).mp hΛ
  refine ⟨max 1 (R+2) + D / S.min' hS + 1, by linarith, by linarith, ?_, ?_⟩
  · intro i j hij
    obtain ⟨k, hk⟩ := (hsep (i,j) hij).1
    refine ⟨k, ?_⟩
    dsimp only
    rw [← mul_sub, abs_mul, abs_of_nonneg hΛ0]
    calc D < _ := hD1
      _ ≤ _ * e (i,j) := mul_le_mul_of_nonneg_left (hle (i,j)) hΛ0
      _ ≤ _ := mul_le_mul_of_nonneg_left hk hΛ0
  · intro i j hij
    obtain ⟨k, hk⟩ := (hsep (i,j) hij).2
    refine ⟨k, ?_⟩
    dsimp only
    rw [← mul_sub, abs_mul, abs_of_nonneg hΛ0]
    calc D < _ := hD1
      _ ≤ _ * e (i,j) := mul_le_mul_of_nonneg_left (hle (i,j)) hΛ0
      _ ≤ _ := mul_le_mul_of_nonneg_left hk hΛ0

