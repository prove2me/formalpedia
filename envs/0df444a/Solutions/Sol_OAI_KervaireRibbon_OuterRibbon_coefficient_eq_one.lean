-- Prove2me | solution 1 for OAI.KervaireRibbon.OuterRibbon.coefficient_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:28:41.250486+00:00
-- url     : https://prove2.me/submissions/c94569c4-5006-4cd0-96d7-ba32e20fed43

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/OuterRibbon.lean:L262-L293
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.OuterRibbon.coefficient_eq_one. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Kervaire_VertexJoin
import Definitions.Def_OAI_GroupTheory_Kervaire_Circles
import Definitions.Def_OAI_GroupTheory_Kervaire_Splicing
import Definitions.Def_OAI_GroupTheory_Kervaire_Capping
import Definitions.Def_OAI_GroupTheory_Kervaire_OuterRibbon
import Theorems.Thm_OAI_KervaireRibbon_OuterRibbon_cap
import Theorems.Thm_OAI_KervaireRibbon_dart_pinch

-- ---- from OAI.GroupTheory.Kervaire.OuterRibbon ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

end
section
open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

end
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

/-- The outside word of a planar relator ribbon can be a coefficient only
when that coefficient is trivial. This is the complete inside-out cap induction. -/
theorem OuterRibbon.coefficient_eq_one [Nonempty I]
    {ρ : Perm I} (hρ : ∀ i j, ρ.SameCycle i j) {a : I → A}
    {s : I → ℤ} (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    {o : D} {l : List D} (r : OuterRibbon (V := V) ρ a s o l) (g : A)
    (he : r.value = Coprod.inl g) : g = 1 := by
  suffices ∀ n (l : List D), l.length = n → ∀ r : OuterRibbon (V := V) ρ a s o l,
      r.value = Coprod.inl g → g=1 by exact this l.length l rfl r he
  intro n
  induction n using Nat.strong_induction_on with | h n ih =>
    intro l hn r he
    by_cases hl : l = []
    · subst l
      have ho : r.σ o = o := by simpa only [Circle,List.nil_append,List.isChain_cons_cons,List.isChain_singleton,and_true] using r.circle
      have hv : r.value = 1 := by
        simp only [OuterRibbon.value,dartEval,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
          dartLetter,corner,r.marker,r.marker_sign,ho,mul_inv_cancel,ofAdd_zero,map_one,mul_one]
      apply (Coprod.inl_injective (N := Multiplicative ℤ))
      simpa only [map_one] using he.symm.trans hv
    · have hd : dartEval r.t (corner r.σ r.θ r.u) l = Coprod.inl ((corner r.σ r.θ r.u o)⁻¹*g) := by
        have hh : Coprod.inl (corner r.σ r.θ r.u o) * dartEval r.t (corner r.σ r.θ r.u) l = Coprod.inl g := by
          simpa only [OuterRibbon.value,dartEval_cons,dartLetter,r.marker_sign,ofAdd_zero,map_one,one_mul] using he
        rw [map_mul,map_inv]
        exact (eq_inv_mul_iff_mul_eq).mpr hh
      obtain ⟨pre,post,x,y,hl',hcx,hpair⟩ := dart_pinch r.t (corner r.σ r.θ r.u) l hl r.unit
        ((corner r.σ r.θ r.u o)⁻¹*g) hd
      subst l
      obtain ⟨r',hr'⟩ := r.cap hρ hs hsum pre post x y hcx hpair
      apply ih (pre++post).length (by simp only [List.length_append,List.length_cons] at hn ⊢; omega)
        (pre++post) rfl r'
      exact hr'.trans he
end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.OuterRibbon.coefficient_eq_one := @_root_.OAI.KervaireRibbon.OuterRibbon.coefficient_eq_one
