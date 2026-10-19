-- Prove2me | solution 1 for OAI.KervaireRibbon.planar_suppress
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:25:33.402692+00:00
-- url     : https://prove2.me/submissions/52486dee-6c8e-432e-a037-48b71f7d35b4

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Suppression.lean:L325-L341
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.planar_suppress. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Theorems.Thm_OAI_KervaireRibbon_components_suppress

-- ---- from OAI.GroupTheory.Kervaire.Suppression ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma numCycles_erase (σ : Equiv.Perm D) {x : D} (hx : σ x ≠ x) :
    numCycles (erase σ x) = numCycles σ + 1 :=
  numCycles_swap_split σ hx.symm SameCycle.rfl.apply_right

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

lemma numCycles_suppress (θ : Equiv.Perm D)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) :
    numCycles (suppress θ x y) = numCycles θ + 1 := by
  let δ := swap y (θ x)
  have ht : (δ*θ*δ⁻¹) x = y := by
    simp only [δ,swap_inv,mul_apply,swap_apply_of_ne_of_ne hxy hx.symm,swap_apply_right]
  have hc := numCycles_swap_split (δ*θ*δ⁻¹) hxy (ht ▸ SameCycle.rfl.apply_right)
  rw [numCycles_conj] at hc
  exact hc

omit [Fintype D] in
lemma suppress_faces (σ θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hsx : σ x = y) (hsy : σ y = x)
    (hx : θ x ≠ x) (hxy' : θ x ≠ y) (hy : θ y ≠ y) :
    (swap x y * σ) * suppress θ x y = erase (erase (σ*θ) x) y := by
  have hyx : θ y ≠ x := fun he ↦ hxy' (by simpa only [hθ] using (congrArg θ he).symm)
  have hpq : θ x ≠ θ y := fun he ↦ hxy (θ.injective he)
  have hpy : σ (θ x) ≠ y := fun he ↦ hx (σ.injective (he.trans hsx.symm))
  have hqx : σ (θ y) ≠ x := fun he ↦ hy (σ.injective (he.trans hsy.symm))
  have hσsw : σ * swap x y = swap x y * σ := by
    rw [mul_swap_eq_swap_mul,hsx,hsy,swap_comm]
  have hφy : erase (σ*θ) x y = σ (θ y) := by
    rw [erase_apply _ _ _ hxy.symm,mul_apply,ite_eq_right hqx]
  have hstart : (swap x y * σ) * suppress θ x y = σ * swap y (θ x) * θ * swap y (θ x) := by
    unfold suppress
    rw [mul_assoc (swap x y) σ,← mul_assoc σ,hσsw]
    simp only [← mul_assoc,swap_mul_self,one_mul]
  rw [hstart,erase,hφy,erase,mul_apply]
  have hcomm : swap x (σ (θ x)) * swap y (σ (θ y)) = swap y (σ (θ y)) * swap x (σ (θ x)) := by
    rw [swap_mul_eq_mul_swap]
    simp only [swap_inv,swap_apply_of_ne_of_ne hxy hqx.symm,
      swap_apply_of_ne_of_ne hpy (fun he ↦ hpq (σ.injective he))]
  calc
    σ * swap y (θ x) * θ * swap y (θ x) =
        swap x (σ (θ x)) * ((σ*θ)*swap y (θ x)) := by
      rw [mul_swap_eq_swap_mul σ y (θ x),hsy]
      simp only [mul_assoc]
    _ = swap x (σ (θ x)) * (swap (σ (θ y)) y * (σ*θ)) := by
      rw [mul_swap_eq_swap_mul (σ*θ) y (θ x),mul_apply,mul_apply,hθ,hsx]
    _ = swap y (σ (θ y)) * (swap x (σ (θ x)) * (σ*θ)) := by
      rw [swap_comm (σ (θ y)) y,← mul_assoc,hcomm,mul_assoc]

end
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma classes_suppress (σ θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hsx : σ x = y) (hsy : σ y = x)
    (hx : θ x ≠ x) (hxy' : θ x ≠ y) (hy : θ y ≠ y) :
    classes (components (swap x y * σ) (suppress θ x y)) = classes (components σ θ) + 2 := by
  let r := components (swap x y * σ) (suppress θ x y)
  have hsp := suppress_apply θ hθ hxy hx hxy' hy
  have hs'x : (swap x y * σ) x = x := by simp [hsx]
  have hs'y : (swap x y * σ) y = y := by simp [hsy]
  have hnx : ¬ r x (θ x) := fun h ↦ hx (components_eq_of_fixed _ _ hs'x hsp.1 h).symm
  have hyker : r ≤ Setoid.ker (fun d ↦ d = y) := components_fixed_le _ _ hs'y hsp.2.1
  have hker : joinPair r x (θ x) ≤ Setoid.ker (fun d ↦ d = y) := by
    apply sup_le hyker
    apply cycle_swap_le
    change (x = y) = (θ x = y)
    simp only [hxy,hxy']
  have hny : ¬ joinPair r x (θ x) y (θ x) := by
    intro h
    have he := hker h
    change (y = y) = (θ x = y) at he
    exact hxy' (he ▸ rfl)
  have h1 := classes_joinPair r hnx
  have h2 := classes_joinPair (joinPair r x (θ x)) hny
  have he := components_suppress σ θ hsx
  change joinPair (joinPair r x (θ x)) y (θ x) = _ at he
  rw [he] at h2
  change classes r = _
  calc
    classes r = classes (joinPair r x (θ x)) + 1 := h1.symm
    _ = (classes (components σ θ) + 1) + 1 := by rw [h2.symm]
    _ = _ := by omega

lemma planar_suppress (σ θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hsx : σ x = y) (hsy : σ y = x)
    (hx : θ x ≠ x) (hxy' : θ x ≠ y) (hy : θ y ≠ y) (hp : planar σ θ) :
    planar (swap x y * σ) (suppress θ x y) := by
  have hyx : θ y ≠ x := fun he ↦ hxy' (by simpa only [hθ] using (congrArg θ he).symm)
  have hpx : (σ*θ) x ≠ x := fun he ↦ hxy' (σ.injective (he.trans hsy.symm))
  have hqx : (σ*θ) y ≠ x := fun he ↦ hy (σ.injective (he.trans hsy.symm))
  have hqy : (σ*θ) y ≠ y := fun he ↦ hyx (σ.injective (he.trans hsx.symm))
  have hey : erase (σ*θ) x y ≠ y := by rw [erase_apply _ _ _ hxy.symm,ite_eq_right hqx]; exact hqy
  have hv := numCycles_swap_split σ hxy (hsx ▸ SameCycle.rfl.apply_right)
  have ht := numCycles_suppress θ hxy hx
  have hf : numCycles ((swap x y * σ)*suppress θ x y) = numCycles (σ*θ) + 2 := by
    rw [suppress_faces σ θ hθ hxy hsx hsy hx hxy' hy,numCycles_erase _ hey,numCycles_erase _ hpx]
  have hc := classes_suppress σ θ hθ hxy hsx hsy hx hxy' hy
  unfold planar at hp ⊢
  rw [hv,ht,hf,hc]
  omega
end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.planar_suppress := @_root_.OAI.KervaireRibbon.planar_suppress
