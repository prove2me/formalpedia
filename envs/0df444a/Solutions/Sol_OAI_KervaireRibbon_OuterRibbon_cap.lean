-- Prove2me | solution 1 for OAI.KervaireRibbon.OuterRibbon.cap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:26:50.321971+00:00
-- url     : https://prove2.me/submissions/6ed6d328-8a32-4c99-a278-50d3924fc535

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/OuterRibbon.lean:L119-L256
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.OuterRibbon.cap. The node keeps its source
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
import Theorems.Thm_OAI_KervaireRibbon_cap_alignment
import Theorems.Thm_OAI_KervaireRibbon_chain_cap
import Theorems.Thm_OAI_KervaireRibbon_circle_cycles
import Theorems.Thm_OAI_KervaireRibbon_planar_cap
import Theorems.Thm_OAI_KervaireRibbon_suppress_involutive_all
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

omit [Fintype D] [Group A] in
lemma suppress_u (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (u : D → A) {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hy : θ y ≠ y)
    (hup : u (θ x) = u y) (huq : u (θ y) = u x) {d : D} (hdx : d ≠ x) (hdy : d ≠ y) :
    u (suppress θ x y d) = u (θ d) := by
  by_cases ht : θ x = y
  · have hyx : θ y = x := by simpa only [hθ] using congrArg θ ht |>.symm
    have he : suppress θ x y = swap x y * θ := by
      simp only [suppress,ht,swap_self]
      change swap x y * (1 * θ * 1) = _
      simp only [one_mul,mul_one]
    rw [he,mul_apply,swap_apply_of_ne_of_ne]
    · exact fun h ↦ hdy (by simpa only [hθ,ht] using congrArg θ h)
    · exact fun h ↦ hdx (by simpa only [hθ,hyx] using congrArg θ h)
  · have hh := suppress_apply θ hθ hxy hx ht hy
    by_cases hd : d = θ x
    · subst d; rw [hh.2.2.1,hθ,huq]
    by_cases hd' : d = θ y
    · subst d; rw [hh.2.2.2,hθ,hup]
    rw [suppress_other θ hθ hdx hdy hd hd']

omit [Fintype D] in
lemma corner_cap (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (u : D → A) {x y : D} (hxy : x ≠ y) (hs : σ x = y)
    (hx : θ x ≠ x) (hy : θ y ≠ y) (hc : corner σ θ u x = 1) (huq : u (θ y) = u x)
    {d : D} (hdx : d ≠ x) (hdy : d ≠ y) :
    corner (erase (erase σ x) y) (suppress θ x y) u d =
      if σ d = x then corner σ θ u d * corner σ θ u y else corner σ θ u d := by
  have hup : u (θ x) = u y := by
    have hh : u (θ x) * (u y)⁻¹ = 1 := by simpa only [corner,hs] using hc
    exact mul_inv_eq_one.mp hh
  unfold corner
  rw [suppress_u θ hθ u hxy hx hy hup huq hdx hdy,cap_vertex_other σ hxy hs hdx hdy]
  split_ifs with hd
  · rw [hd,huq]
    group
  · rfl
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

-- ---- from OAI.GroupTheory.Kervaire.Circles ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [DecidableEq D] [Finite D]

omit [DecidableEq D] in
lemma sameCycle_two (σ : Perm D) {x y z : D} (hx : σ x = y) (hy : σ y = x)
    (hz : σ.SameCycle x z) : z = x ∨ z = y := by
  obtain ⟨n,hn⟩ := hz.exists_nat_pow_eq
  have hi : ∀ n : ℕ, (σ^n) x = x ∨ (σ^n) x = y := by
    intro n; induction n with
    | zero => exact Or.inl rfl
    | succ n ih => rw [pow_succ',mul_apply]; rcases ih with h | h <;> simp only [h,hx,hy,true_or,or_true]
  simpa only [hn] using hi n

end
open Monoid Multiplicative
open scoped Classical
variable {D A : Type*} [Group A]
lemma dartEval_append (t : D → ℤ) (c : D → A) (l r : List D) :
    dartEval t c (l++r) = dartEval t c l * dartEval t c r := by
  simp only [dartEval,List.map_append,List.prod_append]
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

end

open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

end KervaireRibbon

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.OuterRibbon ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

omit [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] in
lemma dartEval_congr (t t' : D → ℤ) (c c' : D → A) (l : List D)
    (ht : ∀ d ∈ l, t d = t' d) (hc : ∀ d ∈ l, c d = c' d) :
    dartEval t c l = dartEval t' c' l := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro d hd
  simp only [dartLetter,ht d hd,hc d hd]

omit [Fintype V] [Fintype I] [Fintype D] in
lemma dartEval_cap (σ : Perm D) (t t' : D → ℤ) (c c' : D → A)
    (pre post : List D) (d x y : D) (hn : (pre++d::x::y::post).Nodup)
    (hd : σ d = x) (hc : c x = 1) (ht : t y = -t x)
    (ht' : ∀ z ∈ pre++d::post, t' z = t z)
    (hc' : ∀ z ∈ pre++d::post, c' z = if σ z = x then c z*c y else c z) :
    dartEval t' c' (pre++d::post) = dartEval t c (pre++d::x::y::post) := by
  have hdn : d ∉ pre ∧ d ∉ post := by
    have h := List.nodup_append.mp hn
    have hh := List.nodup_cons.mp h.2.1
    exact ⟨fun hm ↦ h.2.2 d hm d (by simp) rfl,fun hm ↦ hh.1 (by simp [hm])⟩
  have he (l : List D) (hl : ∀ z ∈ l, z ∈ pre++d::post) (hnd : d ∉ l) :
      dartEval t' c' l = dartEval t c l := by
    apply dartEval_congr _ _ _ _ _ (fun z hz ↦ ht' z (hl z hz))
    intro z hz
    rw [hc' z (hl z hz),ite_eq_right]
    exact fun h ↦ hnd ((σ.injective (hd.trans h.symm)) ▸ hz)
  rw [dartEval_append,dartEval_append,he pre (by intro z hz; simp [hz]) hdn.1,
    dartEval_cons,dartEval_cons,dartEval_cons,dartEval_cons,
    he post (by intro z hz; simp [hz]) hdn.2]
  simp only [dartLetter,ht' d (by simp),hc' d (by simp),hd,ite_true,hc,ht,map_one,mul_one,map_mul,
    ofAdd_neg,map_inv]
  group
end
section
open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

omit [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A] in
lemma nodup_remove_pair (pre post : List D) (x y : D) (hn : (pre++x::y::post).Nodup) :
    x ≠ y ∧ (pre++post).Nodup ∧ ∀ z ∈ pre++post, z ≠ x ∧ z ≠ y := by
  obtain ⟨hp,hq,hdis⟩ := List.nodup_append.mp hn
  obtain ⟨hx,hy,hpost⟩ := by simpa only [List.nodup_cons] using hq
  have hxy : x ≠ y := fun h ↦ hx (by simp [h])
  refine ⟨hxy,List.nodup_append.mpr ⟨hp,hpost,fun a ha b hb ↦ hdis a ha b (by simp [hb])⟩,?_⟩
  intro z hz
  rcases List.mem_append.mp hz with hh | hh
  · exact ⟨hdis z hh x (by simp),hdis z hh y (by simp)⟩
  · exact ⟨fun h ↦ hx (by simp [← h,hh]),fun h ↦ hy (h ▸ hh)⟩

omit [Fintype V] [Fintype I] [Fintype D] [Group A] in
lemma circle_cap (σ : Perm D) (o : D) (pre post : List D) (x y : D)
    (hc : Circle σ o (pre++x::y::post)) (hn : (o::(pre++x::y::post)).Nodup) :
    Circle (erase (erase σ x) y) o (pre++post) := by
  let L := o::pre
  have hne : L ≠ [] := List.cons_ne_nil _ _
  let d := L.getLast hne
  let pr := L.dropLast
  have he : pr++[d] = o::pre := List.dropLast_concat_getLast hne
  have hcat (q : List D) : pr++d::q = o::(pre++q) := by
    calc
      _ = (pr++[d])++q := by simp only [List.append_assoc,List.cons_append,List.nil_append]
      _ = _ := by rw [he]; rfl
  have hchain : (pr++d::x::y::(post++[o])).IsChain (fun a b ↦ σ a = b) := by
    change (o::((pre++x::y::post)++[o])).IsChain _ at hc
    simpa only [hcat,List.append_assoc,List.cons_append,List.nil_append] using hc
  obtain ⟨hxy,_,hno⟩ := nodup_remove_pair (o::pre) post x y (by simpa using hn)
  have hh := chain_cap σ pr (post++[o]) hchain hxy (by
    intro z hz
    have hm : z ∈ o::(pre++post) := by
      have hh : z ∈ (pr++[d])++post++[o] := by simpa using hz
      rw [he] at hh
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hh ⊢
      tauto
    exact hno z (by simpa using hm))
  change (o::((pre++post)++[o])).IsChain _
  simpa only [hcat,List.append_assoc,List.cons_append,List.nil_append] using hh

/-- Exact cap reduction, including preserved outside word and all relator
corners. The analytic rigidity theorem supplies the one necessary alignment. -/
theorem OuterRibbon.cap [Nonempty I]
    {ρ : Perm I} (hρ : ∀ i j, ρ.SameCycle i j) {a : I → A}
    {s : I → ℤ} (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    {o : D} (pre post : List D) (x y : D)
    (r : OuterRibbon (V := V) ρ a s o (pre++x::y::post))
    (hcx : corner r.σ r.θ r.u x = 1) (hpair : r.t y = -r.t x) :
    ∃ r' : OuterRibbon (V := V) ρ a s o (pre++post), r'.value = r.value := by
  obtain ⟨hxy,hn',hno⟩ := nodup_remove_pair (o::pre) post x y (by simpa using r.nodup)
  have hxmem : x ∈ o::(pre++x::y::post) := by simp
  have hymem : y ∈ o::(pre++x::y::post) := by simp
  have ho := hno o (by simp)
  have hsx : r.σ x = y := by
    have hc := r.circle
    change (o::((pre++x::y::post)++[o])).IsChain _ at hc
    simp only [List.append_assoc,List.cons_append] at hc
    change ((o::pre)++x::y::(post++[o])).IsChain _ at hc
    exact (List.isChain_append_cons_cons.mp hc).2.1
  have hsy : r.σ y ≠ x := by
    intro hh
    have hc := (circle_cycles r.σ o _ r.circle x).mpr hxmem
    rcases sameCycle_two r.σ hsx hh hc.symm with h | h
    · exact ho.1 h
    · exact ho.2 h
  have hx : r.θ x ≠ x := by
    intro hh
    have ht := r.opposite x
    rw [hh] at ht
    rcases r.unit x (by simp) with h | h <;> omega
  have hy : r.θ y ≠ y := by
    intro hh
    have ht := r.opposite y
    rw [hh] at ht
    rcases r.unit y (by simp) with h | h <;> omega
  have hdisj (vi) : ¬ r.σ.SameCycle (r.atlas.disk vi) x := by
    intro hh
    exact r.disjoint vi ((circle_cycles r.σ o _ r.circle _).mp
      (((circle_cycles r.σ o _ r.circle x).mpr hxmem).trans hh.symm))
  obtain ⟨v,hv,hvxy⟩ := cap_alignment ρ hρ a s hs hsum r.σ r.θ r.involutive r.t
    r.opposite r.planar' r.atlas r.u r.corners hxy hsx hsy hx hy hpair hcx hdisj (by
      intro d
      rcases r.cover d with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl (((circle_cycles r.σ o _ r.circle d).mpr hh).symm.trans
          ((circle_cycles r.σ o _ r.circle x).mpr hxmem)))
      · exact Or.inr (Or.inr hh))
  let σ' := erase (erase r.σ x) y
  let θ' := suppress r.θ x y
  let t' := capSign r.t x y
  have hne (vi) : r.atlas.disk vi ≠ x ∧ r.atlas.disk vi ≠ y :=
    ⟨fun h ↦ r.disjoint vi (by rw [h]; exact hxmem),fun h ↦ r.disjoint vi (by rw [h]; exact hymem)⟩
  have hnex (vi) : r.σ (r.atlas.disk vi) ≠ x := by
    intro hh
    apply hdisj vi
    have hc : r.σ.SameCycle (r.atlas.disk vi) (r.σ (r.atlas.disk vi)) := SameCycle.rfl.apply_right
    simpa only [hh] using hc
  have hnext (vi) : σ' (r.atlas.disk vi) = r.σ (r.atlas.disk vi) := by
    dsimp only [σ']; rw [cap_vertex_other r.σ hxy hsx (hne vi).1 (hne vi).2,ite_eq_right (hnex vi)]
  let b' : DiskAtlas (V := V) ρ a s σ' t' := {
    disk := r.atlas.disk, ε := r.atlas.ε, polarity := r.atlas.polarity
    next := fun v i ↦ (hnext (v,i)).trans (r.atlas.next v i)
    sign := fun v i ↦ (capSign_other r.t (hne _).1 (hne _).2).trans (r.atlas.sign v i) }
  have hcv : corner r.σ r.θ v x = 1 := by rw [hv,hcx]
  have hcorner (d) (hdx : d ≠ x) (hdy : d ≠ y) :
      corner σ' θ' v d = if r.σ d = x then corner r.σ r.θ r.u d * corner r.σ r.θ r.u y else corner r.σ r.θ r.u d := by
    simpa only [hv] using corner_cap r.σ r.θ r.involutive v hxy hsx hx hy hcv hvxy hdx hdy
  have hfix := suppress_fixed_all r.θ r.involutive hxy hx hy
  have hσx : σ' x = x := by dsimp only [σ']; rw [erase_apply _ _ _ hxy,erase_fixed,ite_eq_right hxy]
  have hσy : σ' y = y := erase_fixed _ _
  have hmark : θ' o = o := by
    dsimp only [θ']
    rw [suppress_other r.θ r.involutive ho.1 ho.2 (by
      intro h; have hh := congrArg r.θ h; rw [r.marker,r.involutive] at hh; exact ho.1 hh) (by
      intro h; have hh := congrArg r.θ h; rw [r.marker,r.involutive] at hh; exact ho.2 hh),r.marker]
  let r' : OuterRibbon (V := V) ρ a s o (pre++post) := {
    σ := σ', θ := θ', involutive := suppress_involutive_all r.θ r.involutive hxy hx hy
    planar' := planar_cap r.σ r.θ r.involutive hxy hsx hsy hx hy r.planar'
    t := t', opposite := suppress_sign r.θ r.involutive r.t r.opposite hxy hx hy hpair
    marker := hmark, marker_sign := (capSign_other r.t ho.1 ho.2).trans r.marker_sign
    circle := circle_cap r.σ o pre post x y r.circle r.nodup
    nodup := by simpa using hn'
    unit := by
      intro d hd
      have hnd := hno d (by simp [hd])
      change capSign r.t x y d = 1 ∨ capSign r.t x y d = -1
      rw [capSign_other r.t hnd.1 hnd.2]
      exact r.unit d (by rcases List.mem_append.mp hd with h | h <;> simp [h])
    atlas := b'
    disjoint := by
      intro vi hh
      change r.atlas.disk vi ∈ o::(pre++post) at hh
      apply r.disjoint vi
      rcases List.mem_cons.mp hh with hh | hh
      · exact List.mem_cons.mpr (Or.inl hh)
      · rcases List.mem_append.mp hh with hh | hh <;> simp [hh]
    cover := by
      intro d
      by_cases hdx : d = x
      · exact Or.inr (Or.inr (hdx ▸ ⟨hσx,hfix.1⟩))
      by_cases hdy : d = y
      · exact Or.inr (Or.inr (hdy ▸ ⟨hσy,hfix.2⟩))
      rcases r.cover d with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl (by simpa only [List.mem_cons,List.mem_append,hdx,hdy,false_or] using hh))
      · refine Or.inr (Or.inr ⟨?_,?_⟩)
        · dsimp only [σ']; rw [cap_vertex_other r.σ hxy hsx hdx hdy,hh.1,ite_eq_right hdx]
        · dsimp only [θ']; rw [suppress_other r.θ r.involutive hdx hdy (by
            intro h; have hj := congrArg r.θ h; rw [hh.2,r.involutive] at hj; exact hdx hj) (by
            intro h; have hj := congrArg r.θ h; rw [hh.2,r.involutive] at hj; exact hdy hj),hh.2]
    u := v
    corners := by
      intro v i
      change vertexCorner ρ a r.atlas.ε (v,i) = _
      rw [r.corners,hcorner _ (hne _).1 (hne _).2,ite_eq_right (hnex _)] }
  refine ⟨r',?_⟩
  let L := o::pre
  have hL : L ≠ [] := List.cons_ne_nil _ _
  let d := L.getLast hL
  let pr := L.dropLast
  have he : pr++[d] = o::pre := List.dropLast_concat_getLast hL
  have hcat (q : List D) : pr++d::q = o::(pre++q) := by
    calc
      _ = (pr++[d])++q := by simp only [List.append_assoc,List.cons_append,List.nil_append]
      _ = _ := by rw [he]; rfl
  have hchain : (pr++d::x::y::(post++[o])).IsChain (fun a b ↦ r.σ a = b) := by
    have hh := r.circle
    change (o::((pre++x::y::post)++[o])).IsChain _ at hh
    simpa only [hcat,List.append_assoc,List.cons_append,List.nil_append] using hh
  have hd : r.σ d = x := (List.isChain_append_cons_cons.mp hchain).2.1
  have hh := dartEval_cap r.σ r.t t' (corner r.σ r.θ r.u) (corner σ' θ' v) pr post d x y
    (by simpa only [hcat,List.append_assoc,List.cons_append,List.nil_append] using r.nodup) hd hcx hpair
    (by intro z hz; have hnz := hno z (by simpa only [hcat,List.append_assoc,List.cons_append,List.nil_append] using hz)
        exact capSign_other r.t hnz.1 hnz.2)
    (by intro z hz; have hnz := hno z (by simpa only [hcat,List.append_assoc,List.cons_append,List.nil_append] using hz)
        exact hcorner z hnz.1 hnz.2)
  change dartEval t' (corner σ' θ' v) (o::(pre++post)) = dartEval r.t (corner r.σ r.θ r.u) (o::(pre++x::y::post))
  simpa only [hcat,List.append_assoc,List.cons_append,List.nil_append] using hh
end
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.OuterRibbon.cap := @_root_.OAI.KervaireRibbon.OuterRibbon.cap
