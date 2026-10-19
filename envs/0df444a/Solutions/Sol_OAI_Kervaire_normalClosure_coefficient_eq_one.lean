-- Prove2me | solution 1 for OAI.Kervaire.normalClosure_coefficient_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:38:13.784001+00:00
-- url     : https://prove2.me/submissions/dc529afa-4fcc-4943-a7ad-2a16086fb6fa

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Main.lean:L41-L82
-- (upload_full_project.md Phase 4): solution for node OAI.Kervaire.normalClosure_coefficient_eq_one. The node keeps its source
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
import Theorems.Thm_OAI_KervaireRibbon_OuterRibbon_coefficient_eq_one
import Theorems.Thm_OAI_KervaireRibbon_OuterRibbon_value_base
import Theorems.Thm_OAI_KervaireRibbon_circle_cycles
import Theorems.Thm_OAI_KervaireRibbon_circle_formPerm
import Theorems.Thm_OAI_KervaireRibbon_unit_syllables_every

-- ---- from OAI.GroupTheory.Kervaire.Realization ----
namespace OAI

section
noncomputable section

namespace KervaireRibbon
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {I : Type} {A : Type*} [Group A]

lemma Realized.coefficient_eq_one [Fintype I] [Nonempty I] {ρ : Perm I} {a : I → A} {s : I → ℤ}
    (hρ : ∀ i j, ρ.SameCycle i j) (hs : ∀ i, s i=1 ∨ s i = -1)
    (hsum : (∑ i, s i)=1 ∨ (∑ i, s i) = -1) {g : A}
    (h : Realized ρ a s (Coprod.inl g)) : g=1 := by
  obtain ⟨D,V,fd,dd,fv,o,l,r,hr⟩ := h
  exact r.coefficient_eq_one hρ hs hsum g hr
end KervaireRibbon

end
end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.WordNormalization ----
namespace OAI

namespace KervaireRibbon

section
open Monoid Multiplicative
variable {A : Type*} [Group A]

lemma syllableEval_exponent (l : List (ℤ × A)) :
    toAdd (Coprod.snd (syllableEval l)) = (l.map Prod.fst).sum := by
  induction l with
  | nil => simp [syllableEval]
  | cons x l ih =>
    simp only [syllableEval,List.map_cons,List.prod_cons] at ih ⊢
    simpa using congrArg (fun n : ℤ ↦ x.1+n) ih
end

open Equiv Equiv.Perm
open scoped Classical
variable {I : Type*} [DecidableEq I]

lemma formPerm_sameCycle_all [Finite I] (i : I) (l : List I) (hn : (i::l).Nodup)
    (hcover : ∀ j, j ∈ i::l) : ∀ j k, (i::l).formPerm.SameCycle j k := by
  intro j k
  have hc := circle_formPerm i l hn
  exact ((circle_cycles _ i l hc j).mpr (hcover j)).symm.trans
    ((circle_cycles _ i l hc k).mpr (hcover k))
end KervaireRibbon

end OAI

-- ---- from OAI.GroupTheory.Kervaire.Main ----
namespace OAI

section
noncomputable section

namespace KervaireRibbon
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {I : Type} {A : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Group A]

lemma relator_ribbon_realized (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i=1 ∨ s i = -1) (i : I) (l : List I)
    (hc : Circle ρ i l) (hn : (i::l).Nodup) (hcover : ∀ j, j ∈ i::l) :
    Realized ρ a s (dartEval s a (i::l)) :=
  ⟨(I⊕I)⊕PUnit,PUnit,inferInstance,inferInstance,inferInstance,Sum.inr PUnit.unit,
    (i::l).map (fun j ↦ Sum.inl (Sum.inr j)),OuterRibbon.base ρ hρ a s hs i l hc hn hcover,
    OuterRibbon.value_base ρ hρ a s hs i l hc hn hcover⟩

lemma relator_normalClosure_coefficient_eq_one (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j)
    (a : I → A) (s : I → ℤ) (hs : ∀ i, s i=1 ∨ s i = -1)
    (hsum : (∑ i, s i)=1 ∨ (∑ i, s i) = -1) (i : I) (l : List I)
    (hc : Circle ρ i l) (hn : (i::l).Nodup) (hcover : ∀ j, j ∈ i::l)
    (g : A) (hg : Coprod.inl g ∈ Subgroup.normalClosure ({dartEval s a (i::l)} : Set (FreeProd A))) :
    g=1 := by
  have hle : Subgroup.normalClosure ({dartEval s a (i::l)} : Set (FreeProd A)) ≤ realizedSubgroup ρ a s := by
    apply Subgroup.normalClosure_le_normal
    intro w hw
    have he : w = dartEval s a (i::l) := Set.mem_singleton_iff.mp hw
    subst w
    exact relator_ribbon_realized ρ hρ a s hs i l hc hn hcover
  exact (hle hg).coefficient_eq_one hρ hs hsum
end KervaireRibbon

namespace Kervaire
open Monoid Multiplicative Equiv
open KervaireRibbon
open scoped Classical

/-- The finite relator indices range over positions, not over the possibly
uncountable coefficient group. The original element and exponent are preserved. -/
lemma normalClosure_coefficient_eq_one {A : Type*} [Group A] (w : WordGroup A)
    (hw : Unimodular w) (g : A) (hg : Coprod.inl g ∈ relatorClosure w) : g=1 := by
  obtain ⟨l,hlen,hunit,heval⟩ := unit_syllables_every w
  let I := Fin l.length
  let s : I → ℤ := fun i ↦ (l.get i).1
  let a : I → A := fun i ↦ (l.get i).2
  let e : List I := List.finRange l.length
  have hne : e ≠ [] := by
    intro he
    have hpos : 0 < l.length := by omega
    have hm : (⟨0,hpos⟩ : I) ∈ e := List.mem_finRange _
    rw [he] at hm
    exact List.not_mem_nil hm
  obtain ⟨i,is,he⟩ := List.exists_cons_of_ne_nil hne
  have : Nonempty I := ⟨i⟩
  let ρ : Perm I := e.formPerm
  have hn : (i::is).Nodup := by rw [← he]; exact List.nodup_finRange _
  have hcover : ∀ j : I, j ∈ i::is := by intro j; rw [← he]; exact List.mem_finRange j
  have hc : Circle ρ i is := by change Circle e.formPerm i is; rw [he]; exact circle_formPerm i is hn
  have hρ : ∀ j k : I, ρ.SameCycle j k := by
    change ∀ j k, e.formPerm.SameCycle j k
    rw [he]
    exact formPerm_sameCycle_all i is hn hcover
  have hs : ∀ j : I, s j=1 ∨ s j = -1 := fun j ↦ hunit _ (List.get_mem l j)
  have heval' : dartEval s a (i::is) = w := by
    rw [← he]
    change (List.map (fun j : I ↦ Coprod.inr (ofAdd (l.get j).1)*Coprod.inl (l.get j).2) e).prod = w
    change (List.map ((fun x : ℤ×A ↦ Coprod.inr (ofAdd x.1)*Coprod.inl x.2) ∘ l.get) e).prod = w
    rw [← List.map_map (f := l.get) (g := fun x : ℤ×A ↦ Coprod.inr (ofAdd x.1)*Coprod.inl x.2)]
    rw [← List.ofFn_eq_map,List.ofFn_get]
    exact heval
  have hsumEq : (∑ i : I, s i) = exponentSum w := by
    rw [← List.sum_ofFn]
    change (List.ofFn (Prod.fst ∘ l.get)).sum = _
    rw [← List.map_ofFn,List.ofFn_get]
    exact (syllableEval_exponent l).symm.trans (congrArg (fun z : FreeProd A ↦ toAdd (Coprod.snd z)) heval)
  have hsum : (∑ i : I, s i)=1 ∨ (∑ i : I, s i) = -1 := by rw [hsumEq]; exact hw
  apply relator_normalClosure_coefficient_eq_one ρ hρ a s hs hsum i is hc hn hcover g
  rw [heval']
  exact hg

universe u

end Kervaire

end
end

end OAI

-- ---- platform node ----
open OAI OAI.Kervaire
open Monoid Multiplicative Equiv
open KervaireRibbon
open scoped Classical


theorem solution : type_of% @_root_.OAI.Kervaire.normalClosure_coefficient_eq_one := @_root_.OAI.Kervaire.normalClosure_coefficient_eq_one
