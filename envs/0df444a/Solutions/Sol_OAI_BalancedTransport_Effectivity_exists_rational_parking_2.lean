-- Prove2me | solution 2 for OAI.BalancedTransport.Effectivity.exists_rational_parking
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:29:19.988718+00:00
-- url     : https://prove2.me/submissions/d4b9eee9-554e-4cb2-9d2d-6ecb829c53df

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/ElementaryRouting.lean:L44-L107
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.exists_rational_parking. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryMotion ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.RationalConstant
open BalancedTransport.Geometry Set

lemma rat (q : ℚ) : RationalConstant (q : ℝ) := ⟨q,rfl⟩

lemma nat (n : ℕ) : RationalConstant (n : ℝ) := ⟨n, by simp⟩

lemma zero : RationalConstant 0 := by simpa using rat 0

lemma one : RationalConstant 1 := by simpa using rat 1

lemma add {a b : ℝ} (ha : RationalConstant a) (hb : RationalConstant b) : RationalConstant (a+b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a+b, by simp⟩

lemma mul {a b : ℝ} (ha : RationalConstant a) (hb : RationalConstant b) : RationalConstant (a*b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a*b, by simp⟩

end BalancedTransport.Effectivity.RationalConstant
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryCurve
open BalancedTransport.Geometry Set

end BalancedTransport.Effectivity.ElementaryCurve
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryMotion
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]
variable {A B C : BoxLayout ι} {safe : Set ι} {η : ℝ}

end BalancedTransport.Effectivity.ElementaryMotion
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Routing ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι]

lemma finite_upper_bound {α : Type*} [Finite α] (f : α → ℝ) :
    ∃ R : ℝ, ∀ i, f i < R := by
  obtain ⟨R, hR⟩ := (Set.finite_range f).bddAbove
  exact ⟨R + 1, fun i => (hR (mem_range_self i)).trans_lt (lt_add_one _)⟩

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryRouting ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]

lemma RationalConstant.max {a b : ℝ} (ha : RationalConstant a) (hb : RationalConstant b) :
    RationalConstant (max a b) := by
  rcases le_total a b with h | h
  · simpa only [max_eq_right h] using hb
  · simpa only [max_eq_left h] using ha

lemma finite_upper_bound_nat {α : Type*} [Finite α] (f : α → ℝ) :
    ∃ R : ℕ, ∀ i, f i < (R : ℝ) := by
  obtain ⟨R,hR⟩ := finite_upper_bound f
  obtain ⟨N,hN⟩ := exists_nat_gt R
  exact ⟨N, fun i => (hR i).trans hN⟩

lemma exists_rational_parking (a b : ι → Space) {D R : ℝ} (hD : 0 ≤ D) :
    RationalConstant D → RationalConstant R →
    ∃ p : ι → Space, RationalCenters p ∧
      (∀ i j, D < |a i 0 - p j 0|) ∧
      (∀ i j, D < |b i 0 - p j 0|) ∧
      (∀ i j, i ≠ j → D < |p i 0 - p j 0|) ∧
      (∀ i, 2 + R < p i 0) := by
  classical
  intro Dr Rr
  obtain ⟨La, hLa⟩ := finite_upper_bound_nat (fun i => a i 0)
  obtain ⟨Lb, hLb⟩ := finite_upper_bound_nat (fun i => b i 0)
  let K := max (3 + R) (max (La : ℝ) (Lb : ℝ)) + D + 1
  let e := Fintype.equivFin ι
  let p : ι → Space := fun i => ![K + (D + 1) * (e i).val, 0, 0]
  have hKs : 2 + R < K := by dsimp [K]; have := le_max_left (3 + R) (max (La : ℝ) (Lb : ℝ)); linarith
  have hKa : ∀ i, D < K - a i 0 := by
    intro i
    have := (le_max_left (La : ℝ) (Lb : ℝ)).trans (le_max_right (3 + R) (max (La : ℝ) (Lb : ℝ)))
    have := hLa i
    dsimp [K]
    linarith
  have hKb : ∀ i, D < K - b i 0 := by
    intro i
    have := (le_max_right (La : ℝ) (Lb : ℝ)).trans (le_max_right (3 + R) (max (La : ℝ) (Lb : ℝ)))
    have := hLb i
    dsimp [K]
    linarith
  have hpn : ∀ i, K ≤ p i 0 := by
    intro i
    dsimp [p]
    exact le_add_of_nonneg_right (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  have Kr : RationalConstant K :=
    ((RationalConstant.nat 3).add Rr |>.max
      ((RationalConstant.nat La).max (RationalConstant.nat Lb))).add Dr |>.add RationalConstant.one
  have pr : RationalCenters p := by
    intro i k
    fin_cases k
    · exact Kr.add ((Dr.add RationalConstant.one).mul (RationalConstant.nat _))
    · exact RationalConstant.zero
    · exact RationalConstant.zero
  refine ⟨p, pr, ?_, ?_, ?_, fun i => hKs.trans_le (hpn i)⟩
  · intro i j
    have := hKa i
    have := hpn j
    rw [abs_sub_comm]
    exact lt_of_lt_of_le (by linarith : D < p j 0 - a i 0) (le_abs_self _)
  · intro i j
    have := hKb i
    have := hpn j
    rw [abs_sub_comm]
    exact lt_of_lt_of_le (by linarith : D < p j 0 - b i 0) (le_abs_self _)
  · intro i j hij
    have hv : (e i).val ≠ (e j).val := by intro h; exact hij (e.injective (Fin.ext h))
    have hh : (1 : ℝ) ≤ |(e i).val - ((e j).val : ℝ)| := by
      rcases lt_or_gt_of_ne hv with hl | hl
      · have hcast : ((e i).val : ℝ) + 1 ≤ (e j).val := by exact_mod_cast hl
        rw [abs_of_nonpos (by linarith : ((e i).val : ℝ) - (e j).val ≤ 0)]
        linarith
      · have hcast : ((e j).val : ℝ) + 1 ≤ (e i).val := by exact_mod_cast hl
        rw [abs_of_nonneg (by linarith : 0 ≤ ((e i).val : ℝ) - (e j).val)]
        linarith
    have he : p i 0 - p j 0 = (D + 1) * (((e i).val : ℝ) - (e j).val) := by dsimp [p]; ring
    rw [he, abs_mul, abs_of_nonneg (by linarith : 0 ≤ D + 1)]
    nlinarith

end BalancedTransport.Effectivity
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open BalancedTransport.Geometry Set


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.exists_rational_parking := @_root_.OAI.BalancedTransport.Effectivity.exists_rational_parking
