-- Prove2me | solution 2 for OAI.KervaireRibbon.disk_sameCycle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:09:24.987982+00:00
-- url     : https://prove2.me/submissions/2f267066-eca5-4072-9f77-6d6c32756d33

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/RelatorRigidity.lean:L360-L388
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.disk_sameCycle. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal
import Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow
import Definitions.Def_OAI_GroupTheory_Kervaire_RelatorRigidity

-- ---- from OAI.GroupTheory.Kervaire.RelatorRigidity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]

end

section
open Equiv Equiv.Perm
open scoped Classical
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

end

section
open Equiv Equiv.Perm
open scoped Classical
variable {V I D : Type*} [Fintype V] [Fintype I] [Fintype D]

end

open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

omit [Fintype V] [Fintype D] [DecidableEq D] [Group A] in
/-- Every dart on a word disk lies in the same ribbon component as its
chosen representative. -/
lemma disk_sameCycle (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j)
    (a : I → A) (s : I → ℤ) (σ : Perm D) (t : D → ℤ)
    (b : DiskAtlas (V := V) ρ a s σ t) (v : V) (i j : I) :
    σ.SameCycle (b.disk (v,i)) (b.disk (v,j)) := by
  let f : I → D := fun i ↦ b.disk (v,i)
  by_cases hv : b.ε v = 1
  · have hf (i) : σ (f i) = f (ρ i) := by simpa only [f,vertexNext,hv,ite_true] using b.next v i
    obtain ⟨n,hn⟩ := (hρ i j).exists_nat_pow_eq
    have hp : ∀ n, (σ^n) (f i) = f ((ρ^n) i) := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ',mul_apply,ih,hf,pow_succ',mul_apply]
    have hh := (hp n).trans (congrArg f hn)
    change σ.SameCycle (f i) (f j)
    rw [← hh]
    exact SameCycle.rfl.pow_right
  · have hf (i) : σ (f i) = f (ρ.symm i) := by simpa only [f,vertexNext,hv,ite_false] using b.next v i
    obtain ⟨n,hn⟩ := (hρ i j).inv.exists_nat_pow_eq
    have hp : ∀ n, (σ^n) (f i) = f ((ρ.symm^n) i) := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ',mul_apply,ih,hf,pow_succ',mul_apply]
    have hh := (hp n).trans (congrArg f hn)
    change σ.SameCycle (f i) (f j)
    rw [← hh]
    exact SameCycle.rfl.pow_right

end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.disk_sameCycle := @_root_.OAI.KervaireRibbon.disk_sameCycle
