-- Prove2me | solution 1 for GlobalTheory.AbLaw.Perf.exists_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:08:20.343494+00:00
-- url     : https://prove2.me/submissions/4f574c03-f396-49cf-b330-f894d4dd7d0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AbelianVarietyLineBundleSectionsFinite
import Theorems.Thm_GlobalTheory_AbLaw_finSec_eq_zero_of_cover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
namespace GlobalTheory.AbLaw
namespace Perf
theorem _root_.solution {X : Scheme.{0}} {K : Type} [Field K] {f : X ⟶ Spec (CommRingCat.of K)}
    {M : LB X} (Q : Perf f M) (s : Fin (Q.a + 1) → LB.Sec M) :
    ∃ c : Fin (Q.a + 1) → K, c ≠ 0 ∧ ∀ i, ∑ k, cst f (M.U i) (c k) * (s k).f i = 0 := by
  have hpb : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id K))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.id_horiz f
  obtain ⟨E, hE⟩ := Q.sec K (RingHom.id K) X (𝟙 X) f hpb
  let v : Fin (Q.a + 1) → Fin Q.a → K := fun k => (E.symm (finSecPullId (s k))).1
  have hv : ∀ k j, rs X (Q.le j) ((s k).f (Q.ch j)) = ∑ l, cst f (Q.W j) (v k l) * Q.u l j := by
    intro k j
    have h := hE (E.symm (finSecPullId (s k))) j
    rw [Equiv.apply_symm_apply] at h
    refine Eq.trans ?_ h
    exact (rs_rs _ _ _).symm
  have hdep : ¬ LinearIndependent K v := by
    intro h
    have := h.fintype_card_le_finrank
    simp at this
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨c, hc, k₀, hk₀⟩ := hdep
  have hc' : ∀ l, ∑ k, c k * v k l = 0 := fun l => by
    have := congrFun hc l
    simpa [Finset.sum_apply] using this
  have hW : ∀ j, ∑ k, cst f (Q.W j) (c k) * rs X (Q.le j) ((s k).f (Q.ch j)) = 0 := by
    intro j
    simp only [hv, Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ← map_sum, hc', map_zero, zero_mul, Finset.sum_const_zero]
  refine ⟨c, fun h => hk₀ (congrFun h k₀), fun i => ?_⟩
  refine finSec_eq_zero_of_cover Q.W Q.cover _ fun j => ?_
  have h₁ : ∀ k, rs X (inf_le_left : M.U i ⊓ Q.W j ≤ M.U i) ((s k).f i) =
      rs X (inf_le_inf le_rfl (Q.le j) : M.U i ⊓ Q.W j ≤ M.U i ⊓ M.U (Q.ch j)) (M.g i (Q.ch j)).val *
        rs X (inf_le_right : M.U i ⊓ Q.W j ≤ Q.W j) (rs X (Q.le j) ((s k).f (Q.ch j))) := by
    intro k
    have h := congrArg (rs X (inf_le_inf le_rfl (Q.le j) : M.U i ⊓ Q.W j ≤ M.U i ⊓ M.U (Q.ch j)))
      ((s k).compat i (Q.ch j))
    rw [map_mul] at h
    simp only [rs_rs] at h ⊢
    exact h
  have h₂ := congrArg (rs X (inf_le_right : M.U i ⊓ Q.W j ≤ Q.W j)) (hW j)
  simp only [map_sum, map_mul, rs_cst, map_zero] at h₂
  simp only [map_sum, map_mul, rs_cst, h₁]
  simp only [mul_left_comm (cst f _ _), ← Finset.mul_sum, h₂, mul_zero]
end Perf
end GlobalTheory.AbLaw
