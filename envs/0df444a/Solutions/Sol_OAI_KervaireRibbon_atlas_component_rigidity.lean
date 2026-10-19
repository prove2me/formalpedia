-- Prove2me | solution 1 for OAI.KervaireRibbon.atlas_component_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:11:25.280424+00:00
-- url     : https://prove2.me/submissions/c18adabb-7010-4158-9b9b-888079b0f401

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/RelatorRigidity.lean:L390-L441
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.atlas_component_rigidity. The node keeps its source
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
import Theorems.Thm_OAI_KervaireRibbon_disk_sameCycle
import Theorems.Thm_OAI_KervaireRibbon_fiber_connected
import Theorems.Thm_OAI_KervaireRibbon_planar_fiber
import Theorems.Thm_OAI_KervaireRibbon_relator_corner_rigidity

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

/-- Restricting whole relator disks to one component retains the literal word
coordinates, including the actual reversed corners of negative disks. -/
theorem atlas_component_rigidity [Nonempty I]
    (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d) (t : D → ℤ)
    (ht : ∀ d, t (θ d) = -t d) (hp : planar σ θ)
    (b : DiskAtlas (V := V) ρ a s σ t) (u : D → A) (p : D)
    (hcovered : ∀ d, components σ θ p d → ∃ vi, b.disk vi = d)
    (hu : ∀ v i, b.disk (v,i) ≠ p → vertexCorner ρ a b.ε (v,i) = corner σ θ u (b.disk (v,i))) :
    ∀ vi, b.disk vi = p → vertexCorner ρ a b.ε vi = corner σ θ u p := by
  let r := components σ θ
  let i₀ := Classical.arbitrary I
  let W := {v : V // r p (b.disk (v,i₀))}
  let c : Quotient r := Quotient.mk r p
  let F := Fiber r c
  let σ' := fiberPerm σ r le_sup_left c
  let θ' := fiberPerm θ r le_sup_right c
  have hvi (v : W) (i : I) : r p (b.disk (v.val,i)) :=
    r.trans' v.property ((le_sup_left : SameCycle.setoid σ ≤ r) (disk_sameCycle ρ hρ a s σ t b v.val i₀ i))
  let f : W × I → F := fun vi ↦ ⟨b.disk (vi.1.val,vi.2),Quotient.sound (r.symm' (hvi vi.1 vi.2))⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨v,i⟩ ⟨w,j⟩ hh
      have hcov := b.disk.injective (congrArg Subtype.val hh)
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst hcov)
      · change i = j
        exact congrArg Prod.snd hcov
    · intro d
      have hd : r p d.val := r.symm' (Quotient.exact d.property)
      obtain ⟨⟨v,i⟩,hi⟩ := hcovered d.val hd
      have hv : r p (b.disk (v,i₀)) :=
        r.trans' (hi ▸ hd) ((le_sup_left : SameCycle.setoid σ ≤ r)
          (disk_sameCycle ρ hρ a s σ t b v i i₀))
      exact ⟨(⟨v,hv⟩,i),Subtype.ext hi⟩
  let e : W × I ≃ F := Equiv.ofBijective f hf
  let p' : F := ⟨p,rfl⟩
  have hh := relator_corner_rigidity ρ hρ a s hs hsum e (fun v : W ↦ b.ε v.val)
    (fun v ↦ b.polarity v.val) σ' θ'
    (by intro v i; apply Subtype.ext; exact b.next v.val i)
    (by intro d; apply Subtype.ext; exact hθ d.val)
    (fun d : F ↦ t d.val) (fun d ↦ ht d.val) (fun v i ↦ b.sign v.val i)
    (fiber_connected σ θ c) (planar_fiber σ θ hp c) (fun d : F ↦ u d.val) p'
    (by intro v i hne; exact hu v.val i (fun h ↦ hne (Subtype.ext h)))
  intro vi hvi'
  have hev : (e.symm p').1.val = vi.1 ∧ (e.symm p').2 = vi.2 := by
    have hh' := congrArg Subtype.val (e.apply_symm_apply p')
    change b.disk ((e.symm p').1.val,(e.symm p').2) = p at hh'
    exact Prod.mk.inj (b.disk.injective (hh'.trans hvi'.symm))
  change vertexCorner ρ a (fun v : W ↦ b.ε v.val) (e.symm p') = corner σ θ u p at hh
  simpa only [vertexCorner,hev] using hh
end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.atlas_component_rigidity := @_root_.OAI.KervaireRibbon.atlas_component_rigidity
