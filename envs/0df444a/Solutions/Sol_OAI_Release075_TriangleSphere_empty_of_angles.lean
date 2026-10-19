-- Prove2me | solution 1 for OAI.Release075.TriangleSphere.empty_of_angles
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:26:34.768367+00:00
-- url     : https://prove2.me/submissions/373a9e11-5886-43ac-9fe1-9fb8c12c6033

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Spheres.lean:L201-L226
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.TriangleSphere.empty_of_angles. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres

-- ---- from OAI.GroupTheory.Hyperbolic.Spheres ----
namespace OAI

namespace Release075
open Equiv PermCycles

attribute [instance] TriangleSphere.dartFintype

namespace TriangleSphere
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable (D : TriangleSphere flip color face)

theorem sum_angles (q : V ≃ Fin 3)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a) :
    ∑ v, D.vertexAngle q v = 5 * Fintype.card (Cycles D.next) := by
  have hfiber (c : Cycles D.next) :
      (∑ a : {a : D.Dart // cl D.next a = c},
        TriangleRibbon.weight (q (color (D.label a)))) = 5 := by
    obtain ⟨a,rfl⟩ := cl_surjective D.next c
    obtain ⟨hp,hn,hface⟩ := D.triangular a
    obtain ⟨hab,hbc,hca⟩ := hf _ _ _ hface
    have hb := three_color_bijective D.next a (fun a => q (color (D.label a))) hp hn
      (fun h => hab (q.injective h)) (fun h => hbc (q.injective h))
      (fun h => hca (q.injective h))
    have he := (Equiv.ofBijective _ hb).sum_comp TriangleRibbon.weight
    have he' : (∑ x : {x : D.Dart // cl D.next x = cl D.next a},
        TriangleRibbon.weight (q (color (D.label x)))) = ∑ i, TriangleRibbon.weight i := he
    rw [he']
    norm_num [Fin.sum_univ_succ,TriangleRibbon.weight]
  have hv : ∑ v, D.vertexAngle q v =
      ∑ a : D.Dart, TriangleRibbon.weight (q (color (D.label a))) := by
    have he := (Equiv.sigmaFiberEquiv (cl D.vertexPerm)).sum_comp
      (fun a => TriangleRibbon.weight (q (color (D.label a))))
    simp only [Fintype.sum_sigma,Equiv.sigmaFiberEquiv_apply] at he
    rw [← he]
    apply Finset.sum_congr rfl
    intro v _
    have hie (a : {a : D.Dart // cl D.vertexPerm a = v}) :
        q (color (D.label a)) = D.paint q v := by
      rw [← D.paint_cl q a,a.property]
    simp only [hie,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,vertexAngle,mul_comm]
  rw [hv]
  have he := (Equiv.sigmaFiberEquiv (cl D.next)).sum_comp
    (fun a => TriangleRibbon.weight (q (color (D.label a))))
  simp only [Fintype.sum_sigma,Equiv.sigmaFiberEquiv_apply] at he
  rw [← he]
  simp only [hfiber,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm]

/-- Angular Gauss--Bonnet on a closed genus-zero map forbids a nonempty reduced
sphere. This is a statement about actual finite permutation maps, not an
asphericity or torsion-freeness assumption. -/
theorem empty_of_angles (q : V ≃ Fin 3)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (hmin : ∀ v, 10 ≤ D.vertexAngle q v) : IsEmpty D.Dart := by
  have hs := D.sum_angles q hf
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hmin v)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  rw [hs] at hsum
  have hr := card_eq_mul_cycles D.reverse 2
    (orbit_card_involution D.reverse D.reverse_involutive D.reverse_ne)
  have hfcard := card_eq_mul_cycles D.next 3
    (fun a => orbit_card_three D.next a (D.triangular a).1 (D.triangular a).2.1)
  have he := D.planar
  simp only [PlanarMap,cycleCount,Nat.card_eq_fintype_card] at he
  have hzero : Fintype.card (Quotient (components D.reverse D.next)) = 0 := by
    have hs' : 2 * Fintype.card (Cycles D.vertexPerm) ≤ Fintype.card (Cycles D.next) := by
      have : (2 : ℝ) * Fintype.card (Cycles D.vertexPerm) ≤ Fintype.card (Cycles D.next) := by
        linarith
      exact_mod_cast this
    change 2 * Fintype.card (Cycles (D.reverse * D.next)) ≤ Fintype.card (Cycles D.next) at hs'
    unfold componentCount at he
    rw [Nat.card_eq_fintype_card] at he
    omega
  exact ⟨fun a => (Fintype.card_pos_iff.mpr ⟨Quotient.mk _ a⟩).ne' hzero⟩

end TriangleSphere
end Release075

namespace Release075.MarkedLineData
open Equiv PermCycles
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

namespace Release075.TriangleSphere
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleSphere

namespace Release075.TriangleSphere
open Equiv PermCycles
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}

end Release075.TriangleSphere

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.TriangleSphere
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.TriangleSphere.empty_of_angles := @_root_.OAI.Release075.TriangleSphere.empty_of_angles
