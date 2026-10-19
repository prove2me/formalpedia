-- Prove2me | solution 2 for OAI.KervaireRibbon.unit_syllables_every
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:34:16.630896+00:00
-- url     : https://prove2.me/submissions/62e840ee-0a1f-4ff8-b1cc-f025d600990c

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/WordNormalization.lean:L56-L70
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.unit_syllables_every. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Kervaire_RibbonProducts
import Definitions.Def_OAI_GroupTheory_Kervaire_Conjugation
import Definitions.Def_OAI_GroupTheory_Kervaire_Inversion
import Definitions.Def_OAI_GroupTheory_Kervaire_Realization
import Definitions.Def_OAI_GroupTheory_Kervaire_Annulus
import Definitions.Def_OAI_GroupTheory_Kervaire_WordNormalization

-- ---- from OAI.GroupTheory.Kervaire.WordNormalization ----
namespace OAI

namespace KervaireRibbon

section
open Monoid Multiplicative
variable {A : Type*} [Group A]

lemma Normalized.one : Normalized (1 : FreeProd A) :=
  ⟨1,[],by simp [UnitSyllables],by simp [syllableEval]⟩

lemma Normalized.prependCoefficient {w : FreeProd A} (h : Normalized w) (g : A) :
    Normalized (Coprod.inl g*w) := by
  obtain ⟨a,l,hl,rfl⟩ := h
  exact ⟨g*a,l,hl,by simp only [map_mul,mul_assoc]⟩

lemma Normalized.prependLetter {w : FreeProd A} (h : Normalized w) (n : ℤ)
    (hn : n=1 ∨ n = -1) : Normalized (Coprod.inr (ofAdd n)*w) := by
  obtain ⟨a,l,hl,rfl⟩ := h
  refine ⟨1,(n,a)::l,?_,?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hn
    · exact hl x hx
  · simp only [map_one,one_mul,syllableEval,List.map_cons,List.prod_cons,mul_assoc]

lemma Normalized.prependPower {w : FreeProd A} (h : Normalized w) (n : ℤ) :
    Normalized (Coprod.inr (ofAdd n)*w) := by
  induction n using Int.induction_on with
  | zero => simpa using h
  | succ n ih =>
    have hh := ih.prependLetter 1 (Or.inl rfl)
    convert hh using 1
    rw [add_comm,ofAdd_add,map_mul,mul_assoc]
  | pred n ih =>
    have hh := ih.prependLetter (-1) (Or.inr rfl)
    convert hh using 1
    rw [sub_eq_add_neg,add_comm,ofAdd_add,map_mul,mul_assoc]

lemma normalized_every (w : FreeProd A) : Normalized w := by
  induction w using Coprod.induction_on' with
  | one => exact Normalized.one
  | inl_mul g w ih => exact ih.prependCoefficient g
  | inr_mul n w ih => exact ih.prependPower (toAdd n)

/-- Inserting the actually trivial pair t·t⁻¹ absorbs the leading coefficient.
This is equality in the unchanged free product, not a new group relation. -/
lemma unit_syllables_every (w : FreeProd A) :
    ∃ l : List (ℤ × A), 2 ≤ l.length ∧ UnitSyllables l ∧ syllableEval l = w := by
  obtain ⟨g,l,hl,rfl⟩ := normalized_every w
  refine ⟨(1,1)::(-1,g)::l,by simp,?_,?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inl rfl
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr rfl
      · exact hl x hx
  · simp only [syllableEval,List.map_cons,List.prod_cons,map_one,mul_one,
      ofAdd_neg,map_inv]
    group

end

open Equiv Equiv.Perm
open scoped Classical
variable {I : Type*} [DecidableEq I]

end KervaireRibbon

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Monoid Multiplicative


theorem solution : type_of% @_root_.OAI.KervaireRibbon.unit_syllables_every := @_root_.OAI.KervaireRibbon.unit_syllables_every
