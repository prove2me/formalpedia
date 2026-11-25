-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.exists_d_eq_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:27.244905+00:00
-- url     : https://prove2.me/submissions/aa6911a0-0e2d-418c-a1f9-5df7021b9992

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_actC
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_le_cons
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_le_cons_comp
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_eq_prod
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_cons_eq
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cons_comp_succAbove_succ
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cons_comp_succAbove_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_res_congr


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
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution [Fintype ι] {n : ℕ} (σ : Cochain P (D ∘ h) (n + 1))
    (hσ : d P (D ∘ h) (n + 1) σ = 0) (j : ι) :
    ∃ (N : ℕ) (τ : Cochain P (D ∘ h) n), d P (D ∘ h) n τ = actC A (D ∘ h) (h j ^ N) (n + 1) σ := by
  classical
  have hlift : ∀ I : Fin (n + 1) → ι, ∃ (N : ℕ) (x : P.obj (op (inter (D ∘ h) I))),
      res P (le_cons _ j I) x = A.act (h j ^ N) _ (σ (Fin.cons j I)) :=
    fun I => A.lift _ (h j) (inter_eq_prod A h I) (inter_cons_eq A h j I) _ _
  choose N x hx using hlift
  obtain ⟨N0, hN0⟩ : ∃ N0, ∀ I, N I ≤ N0 :=
    ⟨Finset.univ.sup N, fun I => Finset.le_sup (Finset.mem_univ I)⟩
  let τ0 : Cochain P (D ∘ h) n := fun I => A.act (h j ^ (N0 - N I)) _ (x I)
  have hτ0 : ∀ I, res P (le_cons _ j I) (τ0 I) = A.act (h j ^ N0) _ (σ (Fin.cons j I)) := by
    intro I
    change res P _ (A.act (h j ^ (N0 - N I)) _ (x I)) = _
    rw [A.res_act, hx, ← A.act_mul, ← pow_add, Nat.sub_add_cancel (hN0 I)]
  have hdef : ∀ J : Fin (n + 2) → ι,
      res P (le_cons _ j J) (d P _ n τ0 J - A.act (h j ^ N0) _ (σ J)) = 0 := by
    intro J
    have hcoc := congrFun hσ (Fin.cons j J)
    rw [d_apply, Fin.sum_univ_succ, Pi.zero_apply] at hcoc
    have e1 : ∀ k : Fin (n + 2), res P (le_cons _ j J) (((-1 : ℤ) ^ (k : ℕ)) •
        res P (inter_le_comp _ J k.succAbove) (τ0 (J ∘ k.succAbove))) =
        ((-1 : ℤ) ^ (k : ℕ)) • A.act (h j ^ N0) _
          (res P (le_cons_comp _ j J k) (σ (Fin.cons j (J ∘ k.succAbove)))) := by
      intro k
      rw [map_zsmul, res_res,
        ← res_res P (le_cons_comp _ j J k) (le_cons _ j (J ∘ k.succAbove)), hτ0, A.res_act]
    have e0 : res P (le_cons _ j J) (σ J) = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
        res P (le_cons_comp _ j J k) (σ (Fin.cons j (J ∘ k.succAbove))) := by
      rw [Fin.val_zero, pow_zero, one_smul,
        res_congr P _ σ (cons_comp_succAbove_zero j J) _ (le_cons _ j J)] at hcoc
      rw [eq_neg_of_add_eq_zero_left hcoc, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, neg_neg,
        res_congr P _ σ (cons_comp_succAbove_succ j J k) _ (le_cons_comp _ j J k)]
    rw [map_sub, d_apply, map_sum, A.res_act, sub_eq_zero, Finset.sum_congr rfl (fun k _ => e1 k),
      e0, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
  have hkill : ∀ J : Fin (n + 2) → ι, ∃ M : ℕ,
      A.act (h j ^ M) _ (d P _ n τ0 J - A.act (h j ^ N0) _ (σ J)) = 0 :=
    fun J => A.kill _ (h j) (inter_eq_prod A h J) (inter_cons_eq A h j J) (le_cons _ j J) _ (hdef J)
  choose M hM using hkill
  obtain ⟨M0, hM0⟩ : ∃ M0, ∀ J, M J ≤ M0 :=
    ⟨Finset.univ.sup M, fun J => Finset.le_sup (Finset.mem_univ J)⟩
  refine ⟨M0 + N0, actC A (D ∘ h) (h j ^ M0) n τ0, ?_⟩
  rw [d_actC]
  funext J
  have hMJ : A.act (h j ^ M0) _ (d P _ n τ0 J - A.act (h j ^ N0) _ (σ J)) = 0 := by
    rw [← Nat.sub_add_cancel (hM0 J), pow_add, A.act_mul, hM J, map_zero]
  rw [map_sub, sub_eq_zero, ← A.act_mul, ← pow_add] at hMJ
  exact hMJ
end GroundTheory.Arith.SchemeCoh
