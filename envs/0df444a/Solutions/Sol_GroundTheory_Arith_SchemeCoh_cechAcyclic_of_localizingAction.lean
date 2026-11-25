-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.cechAcyclic_of_localizingAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:19.22455+00:00
-- url     : https://prove2.me/submissions/4f21411d-5c04-4234-aae4-24f106db16ec

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_LocalizingAction_act_sum
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_LocalizingAction_bijective_pow
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_actC
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_exists_d_eq_pow_smul
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {R : Type u} [CommRing R]
variable {D : R → Opens X} (A : LocalizingAction P D)
variable {ι : Type u} (U : ι → Opens X)
variable (h : ι → R)
include A
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution [Finite ι] (g : R) (hcov : ⨆ i, D (h i) = D g) :
    CechAcyclic P (D ∘ h) := by
  classical
  have := Fintype.ofFinite ι
  intro n σ hσ
  choose N τ hτ using fun j => exists_d_eq_pow_smul A h σ hσ j
  obtain ⟨N0, hN0⟩ : ∃ N0, ∀ j, N j ≤ N0 :=
    ⟨Finset.univ.sup N, fun j => Finset.le_sup (Finset.mem_univ j)⟩
  obtain ⟨L, c, hc⟩ := A.cover g h N0 hcov.ge
  let T : Cochain P (D ∘ h) n := ∑ j, actC A (D ∘ h) (c j * h j ^ (N0 - N j)) n (τ j)
  have hT : d P _ n T = actC A (D ∘ h) (g ^ L) (n + 1) σ := by
    funext J
    simp only [T, map_sum, d_actC, hτ]
    refine (Finset.sum_apply J _ _).trans ?_
    change ∑ j, A.act _ _ (A.act _ _ (σ J)) = A.act (g ^ L) _ (σ J)
    rw [hc, A.act_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← A.act_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel (hN0 j)]
  have hle : ∀ {m : ℕ} (I : Fin (m + 1) → ι), inter (D ∘ h) I ≤ D g := fun I =>
    (inter_le _ I 0).trans (hcov ▸ le_iSup (fun i => D (h i)) (I 0))
  choose y hy using fun I : Fin (n + 1) → ι => (A.bijective_pow g _ (hle I) L).2 (T I)
  refine ⟨y, funext fun J => (A.bijective_pow g _ (hle J) L).1 ?_⟩
  have e1 : actC A (D ∘ h) (g ^ L) n y = T := funext hy
  have e2 := congrFun (d_actC A (D ∘ h) (g ^ L) n y) J
  rw [e1, hT] at e2
  exact e2.symm
end GroundTheory.Arith.SchemeCoh
