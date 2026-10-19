-- Prove2me | solution 2 for OAI.KervaireRibbon.OuterRibbon.value_base
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:30:53.352218+00:00
-- url     : https://prove2.me/submissions/691e9f53-b312-477f-8ffe-bfba5667243c

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Annulus.lean:L175-L190
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.OuterRibbon.value_base. The node keeps its source
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

-- ---- from OAI.GroupTheory.Kervaire.Annulus ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

section

namespace KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

end KervaireRibbon

end

section
namespace KervaireRibbon
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {I A : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Group A]

omit [Fintype I] [Nonempty I] in
lemma base_corner_outside (ρ : Perm I) (a : I → A) (i j : I) :
    corner (markAnnulus ρ i) (pairing.sumCongr 1) (basePotential ρ a i) (Sum.inl (Sum.inr j)) = a j := by
  unfold corner
  rw [markAnnulus_outside]
  by_cases h : ρ j = i
  · rw [ite_eq_left h]
    have hh : ρ.symm i = j := by rw [← h,ρ.symm_apply_apply]
    simp [pairing,basePotential,hh]
  · rw [ite_eq_right h]
    simp [pairing,basePotential]
omit [Fintype I] [Nonempty I] in
lemma base_corner_marker (ρ : Perm I) (a : I → A) (i : I) :
    corner (markAnnulus ρ i) (pairing.sumCongr 1) (basePotential ρ a i) (Sum.inr PUnit.unit) = 1 := by
  simp [corner,markAnnulus_marker,basePotential]

lemma OuterRibbon.value_base (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (i : I) (l : List I)
    (hc : Circle ρ i l) (hn : (i::l).Nodup) (hcover : ∀ j, j ∈ i::l) :
    (OuterRibbon.base ρ hρ a s hs i l hc hn hcover).value = dartEval s a (i::l) := by
  change dartEval (baseSign s) (corner (markAnnulus ρ i) (pairing.sumCongr 1) (basePotential ρ a i))
    (Sum.inr PUnit.unit :: (i::l).map (fun j ↦ Sum.inl (Sum.inr j))) = _
  rw [dartEval_cons]
  have hm : dartLetter (baseSign s) (corner (markAnnulus ρ i) (pairing.sumCongr 1) (basePotential ρ a i)) (Sum.inr PUnit.unit) = 1 := by
    simp [dartLetter,baseSign,base_corner_marker]
  rw [hm,one_mul]
  unfold dartEval
  rw [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply,dartLetter,base_corner_outside,baseSign,Sum.elim_inl,Sum.elim_inr]
end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.OuterRibbon.value_base := @_root_.OAI.KervaireRibbon.OuterRibbon.value_base
