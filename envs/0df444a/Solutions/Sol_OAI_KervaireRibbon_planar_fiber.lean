-- Prove2me | solution 1 for OAI.KervaireRibbon.planar_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:29:51.905979+00:00
-- url     : https://prove2.me/submissions/c532f72e-b4c1-470e-9c2e-a06641a989cd

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/ComponentFibers.lean:L100-L134
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.planar_fiber. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Theorems.Thm_OAI_KervaireRibbon_fiber_connected

-- ---- from OAI.GroupTheory.Kervaire.ComponentFibers ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
lemma numCycles_fiber_sum (σ : Equiv.Perm D) (r : Setoid D) (h : SameCycle.setoid σ ≤ r) :
    (∑ c : Quotient r, numCycles (fiberPerm σ r h c)) = numCycles σ := by
  have he (c : Quotient r) : SameCycle.setoid (fiberPerm σ r h c) =
      (SameCycle.setoid σ).comap (Subtype.val : Fiber r c → D) := by
    ext x y
    exact sameCycle_subtypePerm
  have hc := Fintype.card_congr (Setoid.sigmaQuotientEquivOfLe h)
  rw [Fintype.card_sigma] at hc
  unfold numCycles
  convert hc using 1
  apply Finset.sum_congr rfl
  intro c _
  exact Fintype.card_congr (Quotient.congrRight (Setoid.ext_iff.mp (he c)))

lemma fiberPerm_mul (σ θ : Equiv.Perm D) (r : Setoid D)
    (hs : SameCycle.setoid σ ≤ r) (ht : SameCycle.setoid θ ≤ r) (c : Quotient r) :
    fiberPerm (σ*θ) r (cycles_mul_le σ θ r hs ht) c = fiberPerm σ r hs c * fiberPerm θ r ht c := by
  ext d
  rfl

lemma planar_fiber (σ θ : Equiv.Perm D) (hp : planar σ θ) (c : Quotient (components σ θ)) :
    planar (fiberPerm σ (components σ θ) le_sup_left c)
      (fiberPerm θ (components σ θ) le_sup_right c) := by
  let r := components σ θ
  let σ' := fun c : Quotient r ↦ fiberPerm σ r le_sup_left c
  let θ' := fun c : Quotient r ↦ fiberPerm θ r le_sup_right c
  have hnon (c : Quotient r) : Nonempty (Fiber r c) := ⟨⟨c.out,c.out_eq⟩⟩
  have hcl (c : Quotient r) : classes (components (σ' c) (θ' c)) = 1 := by
    let _ := hnon c
    rw [fiber_connected,classes_top]
  let f : Quotient r → ℕ := fun c ↦ numCycles (σ' c) + numCycles (θ' c) + numCycles ((σ' c)*(θ' c))
  let g : Quotient r → ℕ := fun c ↦ Fintype.card (Fiber r c) + 2
  have hle (c : Quotient r) : f c ≤ g c := by
    have hh := euler_inequality (σ' c) (θ' c)
    change _ ≤ _ + 2*classes (components (σ' c) (θ' c)) at hh
    simpa only [hcl c,mul_one] using hh
  have hsum : ∑ c, f c = ∑ c, g c := by
    simp only [f,g,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_fiber_sum]
    rw [numCycles_fiber_sum σ r le_sup_left,numCycles_fiber_sum θ r le_sup_right]
    have hh := numCycles_fiber_sum (σ*θ) r (cycles_mul_le σ θ r le_sup_left le_sup_right)
    have hh' : (∑ z, numCycles ((σ' z)*(θ' z))) = numCycles (σ*θ) := by
      calc
        _ = ∑ z, numCycles (fiberPerm (σ*θ) r (cycles_mul_le σ θ r le_sup_left le_sup_right) z) := by
          apply Finset.sum_congr rfl
          intro z _
          exact congrArg numCycles (fiberPerm_mul σ θ r le_sup_left le_sup_right z).symm
        _ = _ := hh
    rw [hh']
    change _ = _ + Fintype.card (Quotient r)*2
    rw [Nat.mul_comm]
    exact hp
  have hc := (Finset.sum_eq_sum_iff_of_le (fun z (_ : z ∈ Finset.univ) ↦ hle z)).mp hsum c (Finset.mem_univ c)
  change f c = _ + 2*classes (components (σ' c) (θ' c))
  rw [hcl,mul_one]
  exact hc
end

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

end

open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.planar_fiber := @_root_.OAI.KervaireRibbon.planar_fiber
