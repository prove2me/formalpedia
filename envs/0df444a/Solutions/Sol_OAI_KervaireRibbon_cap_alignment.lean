-- Prove2me | solution 1 for OAI.KervaireRibbon.cap_alignment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:24:44.65238+00:00
-- url     : https://prove2.me/submissions/b19f4c96-76e2-4d8c-abd5-f1c9a697f86a

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Capping.lean:L103-L199
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.cap_alignment. The node keeps its source
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
import Theorems.Thm_OAI_KervaireRibbon_atlas_component_rigidity
import Theorems.Thm_OAI_KervaireRibbon_cap_vertex
import Theorems.Thm_OAI_KervaireRibbon_components_suppress
import Theorems.Thm_OAI_KervaireRibbon_planar_cap
import Theorems.Thm_OAI_KervaireRibbon_planar_vertex_split_separates
import Theorems.Thm_OAI_KervaireRibbon_sameCycle_erase
import Theorems.Thm_OAI_KervaireRibbon_suppress_involutive
import Theorems.Thm_OAI_KervaireRibbon_suppress_sign

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

lemma components_fixed_le (σ θ : Equiv.Perm D) {x : D} (hs : σ x = x) (ht : θ x = x) :
    components σ θ ≤ Setoid.ker (fun d ↦ d = x) := by
  apply sup_le
  · apply cycle_le_of_step
    intro d
    change (σ d = x) = (d = x)
    exact propext ⟨fun h ↦ σ.injective (h.trans hs.symm),fun h ↦ h ▸ hs⟩
  · apply cycle_le_of_step
    intro d
    change (θ d = x) = (d = x)
    exact propext ⟨fun h ↦ θ.injective (h.trans ht.symm),fun h ↦ h ▸ ht⟩

lemma components_eq_of_fixed (σ θ : Equiv.Perm D) {x d : D}
    (hs : σ x = x) (ht : θ x = x) (h : components σ θ x d) : x = d := by
  have hh := components_fixed_le σ θ hs ht h
  change (x = x) = (d = x) at hh
  exact (hh ▸ rfl : d = x).symm

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

-- ---- from OAI.GroupTheory.Kervaire.RelatorRigidity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]

omit [Fintype D] [DecidableEq D] in
lemma corner_gauge (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (u c : D → A) (hc : ∀ d, c ((σ*θ) d) = c d) :
    corner σ θ (fun d ↦ u d*c d) = corner σ θ u := by
  funext d
  have h := hc (θ d)
  simp only [mul_apply,hθ] at h
  simp only [corner,h,mul_inv_rev]
  group

/-- Independent face gauges can align two vertices precisely when the two
 relevant faces are distinct. -/
lemma align_distinct_faces (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (u : D → A) {p q : D} (hpq : ¬ (σ*θ).SameCycle p q) :
    ∃ v : D → A, corner σ θ v = corner σ θ u ∧ v q = v p := by
  let φ := σ*θ
  let c : D → A := fun d ↦ if φ.SameCycle d q then (u q)⁻¹*u p else 1
  have hc (d : D) : c (φ d) = c d := by simp only [c,sameCycle_apply_left]
  refine ⟨fun d ↦ u d*c d,corner_gauge σ θ hθ u c hc,?_⟩
  simp only [c,φ,SameCycle.rfl,ite_true,ite_eq_right hpq,mul_one]
  group

omit [Fintype D] in
lemma cap_vertex_other (σ : Perm D) {x y d : D} (hxy : x ≠ y) (hs : σ x = y)
    (hdx : d ≠ x) (hdy : d ≠ y) :
    erase (erase σ x) y d = if σ d = x then σ y else σ d := by
  have hsy : σ d ≠ y := fun h ↦ hdx (σ.injective (h.trans hs.symm))
  rw [erase_apply _ _ _ hdy,erase_apply _ _ _ hdx]
  by_cases hdx' : σ d = x
  · rw [ite_eq_left hdx',hs,ite_eq_left rfl,erase_apply _ _ _ hxy.symm]
    by_cases hyx : σ y = x
    · rw [ite_eq_left hyx,hs,hyx]
      exact (hdy (σ.injective (hdx'.trans hyx.symm))).elim
    · rw [ite_eq_right hyx,ite_eq_left hdx']
  · rw [ite_eq_right hdx',ite_eq_right hsy,ite_eq_right hdx']

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

end KervaireRibbon

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.Capping ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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
lemma capSign_other (t : D → ℤ) {x y d : D} (hdx : d ≠ x) (hdy : d ≠ y) :
    capSign t x y d = t d := ite_eq_right (not_or_intro hdx hdy)

omit [Fintype D] [Group A] in
lemma suppress_u_except (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (u : D → A) {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hy : θ y ≠ y)
    (hup : u (θ x) = u y) {d : D} (hdx : d ≠ x) (hdy : d ≠ y) (hdp : d ≠ θ x) :
    u (suppress θ x y d) = u (θ d) := by
  by_cases ht : θ x = y
  · have hyt : θ y = x := by simpa only [hθ] using (congrArg θ ht).symm
    rw [suppress_paired θ ht,mul_apply,swap_apply_of_ne_of_ne]
    · exact fun h ↦ hdy (by simpa only [hθ,ht] using congrArg θ h)
    · exact fun h ↦ hdx (by simpa only [hθ,hyt] using congrArg θ h)
  · by_cases hdq : d = θ y
    · subst d; rw [(suppress_apply θ hθ hxy hx ht hy).2.2.2,hθ,hup]
    · rw [suppress_other θ hθ hdx hdy hdp hdq]
end

open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

/-- At a freely cancellable outside pair, the two remaining band endpoints
can be aligned without changing any corner. The same-face case is exactly
where the analytic planar-boundary theorem is needed. -/
theorem cap_alignment [Nonempty I]
    (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d) (t : D → ℤ)
    (ht : ∀ d, t (θ d) = -t d) (hp : planar σ θ)
    (b : DiskAtlas (V := V) ρ a s σ t) (u : D → A)
    (hu : ∀ v i, vertexCorner ρ a b.ε (v,i) = corner σ θ u (b.disk (v,i)))
    {x y : D} (hxy : x ≠ y) (hsx : σ x = y) (hsy : σ y ≠ x)
    (hx : θ x ≠ x) (hy : θ y ≠ y) (hpair : t y = -t x) (hcx : corner σ θ u x = 1)
    (hdisj : ∀ vi, ¬ σ.SameCycle (b.disk vi) x)
    (hcover : ∀ d, (∃ vi, b.disk vi = d) ∨ σ.SameCycle d x ∨ (σ d = d ∧ θ d = d)) :
    ∃ v : D → A, corner σ θ v = corner σ θ u ∧ v (θ y) = v x := by
  by_cases hface : (σ*θ).SameCycle x (θ y)
  swap
  · exact align_distinct_faces σ θ hθ u hface
  by_cases hpaired : θ x = y
  · have hyx : θ y = x := by simpa only [hθ] using (congrArg θ hpaired).symm
    exact ⟨u,rfl,congrArg u hyx⟩
  have hyx : θ y ≠ x := fun h ↦ hpaired (by simpa only [hθ] using (congrArg θ h).symm)
  have hzy : σ y ≠ y := fun h ↦ hxy (σ.injective (hsx.trans h.symm))
  let τ := swap x (σ y)*σ
  let σ' := erase (erase σ x) y
  let θ' := suppress θ x y
  let t' := capSign t x y
  have hcy : σ.SameCycle x (σ y) := (hsx ▸ SameCycle.rfl.apply_right).apply_right
  have hφ : (σ*θ).SameCycle x (σ y) := by simpa only [mul_apply,hθ] using hface.apply_right
  have hsep : ¬ components τ θ x (σ y) := planar_vertex_split_separates σ θ hsy.symm hcy hφ hp
  have hτx : τ x = y := by simp only [τ,mul_apply,hsx,swap_apply_of_ne_of_ne hxy.symm hzy.symm]
  have hrle : components σ' θ' ≤ components τ θ := by
    have hh := components_suppress τ θ hτx
    rw [← cap_vertex σ hxy hsx hsy] at hh
    exact ((le_joinPair _ _ _).trans (le_joinPair _ _ _)).trans_eq hh
  have hfix := suppress_apply θ hθ hxy hx hpaired hy
  have hs'x : σ' x = x := by
    dsimp only [σ']; rw [erase_apply _ _ _ hxy,erase_fixed,ite_eq_right hxy]
  have hs'y : σ' y = y := erase_fixed _ _
  have hpneq : θ x ≠ y := hpaired
  have houtside (d : D) (hd : σ.SameCycle d x) (hdx : d ≠ x) (hdy : d ≠ y) :
      σ'.SameCycle d (σ y) := by
    apply (sameCycle_erase (erase σ x) (x := y) (d := d) (e := σ y) (by
      rw [erase_apply _ _ _ hxy.symm,ite_eq_right hsy]; exact hzy) hdy hzy).mpr
    apply (sameCycle_erase σ (x := x) (d := d) (e := σ y) (by rw [hsx]; exact hxy.symm) hdx hsy).mpr
    exact hd.trans hcy
  have hcovered : ∀ d, components σ' θ' (θ x) d → ∃ vi, b.disk vi = d := by
    intro d hd
    rcases hcover d with h | h | h
    · exact h
    · have hdx : d ≠ x := fun he ↦ hx (components_eq_of_fixed σ' θ' hs'x hfix.1 ((components σ' θ').symm' (he ▸ hd))).symm
      have hdy : d ≠ y := fun he ↦ hpaired (components_eq_of_fixed σ' θ' hs'y hfix.2.1 ((components σ' θ').symm' (he ▸ hd))).symm
      apply False.elim
      apply hsep
      exact (components τ θ).trans' ((le_sup_right : SameCycle.setoid θ ≤ components τ θ) SameCycle.rfl.apply_right)
        (hrle ((components σ' θ').trans' hd ((le_sup_left : SameCycle.setoid σ' ≤ components σ' θ') (houtside d h hdx hdy))))
    · have hdx : d ≠ x := fun he ↦ hx (he ▸ h.2)
      have hdy : d ≠ y := fun he ↦ hy (he ▸ h.2)
      have hdp : d ≠ θ x := fun he ↦ hx (by simpa only [he,hθ] using h.2.symm)
      have hdq : d ≠ θ y := fun he ↦ hy (by simpa only [he,hθ] using h.2.symm)
      have hs'd : σ' d = d := by dsimp only [σ']; rw [cap_vertex_other σ hxy hsx hdx hdy,h.1,ite_eq_right hdx]
      have ht'd : θ' d = d := by dsimp only [θ']; rw [suppress_other θ hθ hdx hdy hdp hdq,h.2]
      exact False.elim (hdp (components_eq_of_fixed σ' θ' hs'd ht'd ((components σ' θ').symm' hd)))
  have disk_ne (vi : V × I) : b.disk vi ≠ x ∧ b.disk vi ≠ y := by
    constructor
    · exact fun h ↦ hdisj vi (h ▸ SameCycle.rfl)
    · intro h
      apply hdisj vi
      rw [h,← hsx]
      exact SameCycle.rfl.apply_left
  have disk_next (v : V) (i : I) : σ' (b.disk (v,i)) = σ (b.disk (v,i)) := by
    dsimp only [σ']; rw [cap_vertex_other σ hxy hsx (disk_ne _).1 (disk_ne _).2,ite_eq_right]
    rw [b.next]
    exact (disk_ne _).1
  let b' : DiskAtlas (V := V) ρ a s σ' t' := {
    disk := b.disk, ε := b.ε, polarity := b.polarity
    next := fun v i ↦ (disk_next v i).trans (b.next v i)
    sign := fun v i ↦ (capSign_other t (disk_ne _).1 (disk_ne _).2).trans (b.sign v i) }
  have hup : u (θ x) = u y := by
    apply mul_inv_eq_one.mp
    simpa only [corner,hsx] using hcx
  have hh := atlas_component_rigidity ρ hρ a s hs hsum σ' θ'
    (suppress_involutive θ hθ hxy hx hpaired hy) t'
    (suppress_sign θ hθ t ht hxy hx hy hpair) (planar_cap σ θ hθ hxy hsx hsy hx hy hp)
    b' u (θ x) hcovered (by
      intro v i hne
      change vertexCorner ρ a b.ε (v,i) = _
      rw [hu]
      simp only [corner]
      rw [disk_next,suppress_u_except θ hθ u hxy hx hy hup (disk_ne _).1 (disk_ne _).2 hne])
  obtain ⟨⟨v,i⟩,hvi⟩ := hcovered (θ x) ((components σ' θ').refl _)
  have heq := (hu v i).symm.trans (hh (v,i) hvi)
  rw [hvi] at heq
  change u (θ (θ x)) * (u (σ (θ x)))⁻¹ = u (θ' (θ x)) * (u (σ' (θ x)))⁻¹ at heq
  have hsp : σ' (θ x) = σ (θ x) := by simpa only [hvi] using disk_next v i
  rw [hsp,hθ,hfix.2.2.1] at heq
  exact ⟨u,rfl,(mul_right_cancel heq).symm⟩
end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.cap_alignment := @_root_.OAI.KervaireRibbon.cap_alignment
