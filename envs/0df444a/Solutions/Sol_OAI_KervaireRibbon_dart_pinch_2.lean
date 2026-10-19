-- Prove2me | solution 2 for OAI.KervaireRibbon.dart_pinch
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:18:36.221304+00:00
-- url     : https://prove2.me/submissions/1f75caac-63a6-4a83-a95e-f5c2b6aaf504

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Circles.lean:L119-L159
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.dart_pinch. The node keeps its source
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

-- ---- from OAI.GroupTheory.Kervaire.Circles ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [DecidableEq D] [Finite D]

end
open Monoid Multiplicative
open scoped Classical
variable {D A : Type*} [Group A]
/-- An actual adjacent cancellable unit pair in a coefficient-valued outside
word. Nothing about coefficients being finite or torsion-free is used. -/
lemma dart_pinch (t : D → ℤ) (c : D → A) (l : List D) (hl : l ≠ [])
    (ht : ∀ d ∈ l, t d = 1 ∨ t d = -1) (g : A)
    (he : dartEval t c l = Coprod.inl g) :
    ∃ pre post x y, l = pre ++ x::y::post ∧ c x = 1 ∧ t y = -t x := by
  let U : D → ℤˣ := fun d ↦ if t d = 1 then 1 else -1
  have hU (d) (hd : d ∈ l) : ((U d : ℤˣ) : ℤ) = t d := by
    rcases ht d hd with h | h <;> simp [U,h]
  have hn : ¬ l.IsChain (fun x y ↦ c x = 1 → t x = t y) := by
    intro hc
    let L := l.map (fun d ↦ (U d,c d))
    have hLc : L.IsChain (fun x y : ℤˣ × A ↦ x.2 = 1 → x.1 = y.1) := by
      change (l.map _).IsChain _
      rw [List.isChain_map]
      exact hc.imp (fun x y hh hh' ↦ by simp only [U,hh hh'])
    let w : HNNExtension.NormalWord.ReducedWord A ⊥ ⊥ :=
      ⟨1,L,by simpa only [HNNExtension.toSubgroup,ite_self,Subgroup.mem_bot] using hLc⟩
    have hL : L = [] := by
      apply HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range w
        (φ := MulEquiv.refl (⊥ : Subgroup A))
      refine ⟨g,?_⟩
      let q : FreeProd A →* HNNExtension A ⊥ ⊥ (MulEquiv.refl (⊥ : Subgroup A)) :=
        Coprod.lift HNNExtension.of (zpowersHom _ HNNExtension.t)
      have hh := congrArg q he
      have hmap : (l.map (fun d ↦ HNNExtension.t ^ (U d : ℤ) * HNNExtension.of (c d))) =
          (l.map (fun d ↦ q (dartLetter t c d))) := by
        apply List.map_congr_left
        intro d hd
        simp [q,dartLetter,hU d hd]
      have hh' := hh.symm
      rw [show q (Coprod.inl g) = HNNExtension.of g by simp [q],dartEval,map_list_prod,List.map_map,Function.comp_def,← hmap] at hh'
      simpa [HNNExtension.NormalWord.ReducedWord.prod,w,L,Function.comp_def] using hh'
    exact hl (List.map_eq_nil_iff.mp hL)
  rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hn
  push Not at hn
  obtain ⟨x,y,pre,post,hl',hc,hne⟩ := hn
  have hx : x ∈ l := by rw [hl']; simp
  have hy : y ∈ l := by rw [hl']; simp
  refine ⟨pre,post,x,y,hl',hc,?_⟩
  rcases ht x hx with ha | ha <;> rcases ht y hy with hb | hb <;> omega
end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Monoid Multiplicative
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.dart_pinch := @_root_.OAI.KervaireRibbon.dart_pinch
