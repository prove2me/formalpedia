-- Prove2me | solution 2 for OAI.KervaireRibbon.suppress_sign
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:22:15.183493+00:00
-- url     : https://prove2.me/submissions/986f3249-e807-4435-b5c9-056f723ad010

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Capping.lean:L57-L82
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.suppress_sign. The node keeps its source
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

-- ---- from OAI.GroupTheory.Kervaire.Suppression ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

end
section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

omit [Fintype D] in
lemma suppress_apply (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hxy' : θ x ≠ y) (hy : θ y ≠ y) :
    suppress θ x y x = x ∧ suppress θ x y y = y ∧
    suppress θ x y (θ x) = θ y ∧ suppress θ x y (θ y) = θ x := by
  have hyx : θ y ≠ x := fun he ↦ hxy' (by simpa only [hθ] using (congrArg θ he).symm)
  have hpq : θ x ≠ θ y := fun he ↦ hxy (θ.injective he)
  simp only [suppress,mul_apply,swap_apply_of_ne_of_ne hxy hx.symm,
    swap_apply_left,swap_apply_right,hθ,swap_apply_of_ne_of_ne hy hpq.symm,
    swap_apply_of_ne_of_ne hyx hy,swap_apply_of_ne_of_ne hx hxy',true_and]

omit [Fintype D] in
lemma suppress_other (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y d : D} (hdx : d ≠ x) (hdy : d ≠ y) (hdp : d ≠ θ x) (hdq : d ≠ θ y) :
    suppress θ x y d = θ d := by
  have htx : θ d ≠ x := fun h ↦ hdp (by simpa only [hθ] using congrArg θ h)
  have hty : θ d ≠ y := fun h ↦ hdq (by simpa only [hθ] using congrArg θ h)
  have htp : θ d ≠ θ x := fun h ↦ hdx (θ.injective h)
  simp only [suppress,mul_apply,swap_apply_of_ne_of_ne hdy hdp,
    swap_apply_of_ne_of_ne hty htp,swap_apply_of_ne_of_ne htx hty]

end
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

end KervaireRibbon

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.Capping ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]

omit [Fintype D] in
lemma suppress_paired (θ : Perm D) {x y : D} (ht : θ x = y) :
    suppress θ x y = swap x y * θ := by
  simp only [suppress,ht,swap_self]
  change swap x y * (1 * θ * 1) = _
  simp only [one_mul,mul_one]

omit [Fintype D] in
lemma suppress_fixed_all (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hy : θ y ≠ y) :
    suppress θ x y x = x ∧ suppress θ x y y = y := by
  by_cases ht : θ x = y
  · have hyx : θ y = x := by simpa only [hθ] using (congrArg θ ht).symm
    rw [suppress_paired θ ht]
    simp only [mul_apply,ht,hyx,swap_apply_left,swap_apply_right,and_self]
  · exact ⟨(suppress_apply θ hθ hxy hx ht hy).1,(suppress_apply θ hθ hxy hx ht hy).2.1⟩

omit [Fintype D] in
lemma capSign_other (t : D → ℤ) {x y d : D} (hdx : d ≠ x) (hdy : d ≠ y) :
    capSign t x y d = t d := ite_eq_right (not_or_intro hdx hdy)

omit [Fintype D] in
lemma suppress_sign (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (t : D → ℤ) (ht : ∀ d, t (θ d) = -t d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hy : θ y ≠ y) (hpair : t y = -t x) :
    ∀ d, capSign t x y (suppress θ x y d) = - capSign t x y d := by
  have hf := suppress_fixed_all θ hθ hxy hx hy
  intro d
  by_cases hdx : d = x
  · subst d; rw [hf.1]; simp [capSign]
  by_cases hdy : d = y
  · subst d; rw [hf.2]; simp [capSign]
  have htx : suppress θ x y d ≠ x := fun h ↦ hdx ((suppress θ x y).injective (h.trans hf.1.symm))
  have hty : suppress θ x y d ≠ y := fun h ↦ hdy ((suppress θ x y).injective (h.trans hf.2.symm))
  rw [capSign_other t htx hty,capSign_other t hdx hdy]
  by_cases htp : θ x = y
  · have hyt : θ y = x := by simpa only [hθ] using (congrArg θ htp).symm
    rw [suppress_paired θ htp,mul_apply,swap_apply_of_ne_of_ne]
    · exact ht d
    · exact fun h ↦ hdy (by simpa only [hθ,htp] using congrArg θ h)
    · exact fun h ↦ hdx (by simpa only [hθ,hyt] using congrArg θ h)
  · have hs := suppress_apply θ hθ hxy hx htp hy
    by_cases hdp : d = θ x
    · subst d; rw [hs.2.2.1,ht,ht,hpair]
    by_cases hdq : d = θ y
    · subst d; rw [hs.2.2.2,ht,ht,hpair]; omega
    rw [suppress_other θ hθ hdx hdy hdp hdq,ht]

end

open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.suppress_sign := @_root_.OAI.KervaireRibbon.suppress_sign
