-- Prove2me | solution 1 for GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:47:46.140784+00:00
-- url     : https://prove2.me/submissions/5f0432b3-0498-4217-8465-61a807c631b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetEqOneOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GramDetEqNormMulGramDetOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaSelfAdjointLieOfCountLimitDescent
import Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_eta_sq
import Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_q_ne_zero
import Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_exists_small
import Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_prod_P
import Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_trace_prod
import Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_linLim
import Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_nonempty_of_N_ne_zero
import Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_X_empty
import Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_exists_rad
import Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_rep_plus
import Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_eta_norm
import Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_cast_finsum
import Theorems.Thm_GlobalTheory_T_eta_gramDet_eq_one_of_selfDual_lattice
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_prod_P


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.LieEnd
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ}
namespace GlobalTheory.UnitLemma.LieEnd
theorem _root_.solution (h1 : CountIdentity) (h2 : UnitaryLimit) (h3 : LinearDescent) : UnitLemmaLie := by
  intro K B₁ B₂ hg₁ hg₂ hsep
  show (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * InvAlg.kapSum B₁ B₂ = B₁.stSum * B₂.stSum
  obtain ⟨a, ha⟩ := exists_small K
  have hB : (B₁.prod B₂).LieReg := ⟨Prod.ext hg₁ hg₂, by rw [prod_P]; exact hsep⟩
  have hB₁ : B₁.LieReg := ⟨hg₁, hsep.of_mul_left⟩
  have hB₂ : B₂.LieReg := ⟨hg₂, hsep.of_mul_right⟩
  have hLD := h3 K B₁ B₂ hg₁ hg₂ hsep a ha (fun x => ((B₁.prod B₂).N x : ℝ)) (fun x => (B₁.N x : ℝ))
    (fun x => (B₂.N x : ℝ)) (fun x hx => linLim h1 h2 _ hB a ha x hx)
    (fun x hx => linLim h1 h2 _ hB₁ a ha x hx) (fun x hx => linLim h1 h2 _ hB₂ a ha x hx)
  simp only [← Rat.cast_mul] at hLD
  rw [← cast_finsum, ← cast_finsum, ← cast_finsum] at hLD
  have hq : (-(K.q : ℝ)) ^ val K.O (resultant B₁.P B₂.P) =
      (((-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) : ℚ) : ℝ) := by
    rw [Rat.cast_zpow, Rat.cast_neg, Rat.cast_natCast]
  rw [hq, ← Rat.cast_mul, ← Rat.cast_mul] at hLD
  have hQ := Rat.cast_injective hLD
  have hq0 : (-(K.q : ℚ)) ≠ 0 := by simpa using q_ne_zero K
  by_cases hd : B₁.gramDet 1 = 0
  · obtain ⟨y, hy0, hy⟩ := exists_rad B₁ hd
    have hN₁ : ∀ x, B₁.N x = 0 := fun x =>
      by_contra fun hx => X_empty B₁ y hy0 hy x (nonempty_of_N_ne_zero B₁ x hx)
    have hN : ∀ x, (B₁.prod B₂).N x = 0 := by
      intro x
      by_contra hx
      refine X_empty (B₁.prod B₂) ((y, 0) : B₁.A × B₂.A) (fun h0 => hy0 (congrArg Prod.fst h0))
        (fun z => ?_) x (nonempty_of_N_ne_zero _ x hx)
      have key : ∀ w : B₁.A × B₂.A, Algebra.trace K.E (B₁.A × B₂.A) ((y, 0) * w) = 0 := fun w => by
        rw [trace_prod]
        simp [hy]
      exact key z
    simp [InvAlg.kapSum, InvAlg.stSum, hN, hN₁]
  · have he : K.eta (B₁.gramDet 1) * K.eta (B₁.gramDet 1) = 1 := eta_sq K _
    have hS : ∑ᶠ k : (B₁.prod B₂).Cl, K.eta (Algebra.norm K.E (InvAlg.Cl.rep k).1) * (B₁.prod B₂).N k.rep =
        K.eta (B₁.gramDet 1) * InvAlg.kapSum B₁ B₂ := by
      unfold InvAlg.kapSum
      rw [mul_finsum]
      refine finsum_congr fun k => ?_
      rw [eta_norm B₁ hd _ (Prod.isUnit_iff.1 (rep_plus _ k).1).1, mul_assoc]
    have hS₁ : ∑ᶠ k : B₁.Cl, K.eta (Algebra.norm K.E k.rep) * B₁.N k.rep =
        K.eta (B₁.gramDet 1) * B₁.stSum := by
      unfold InvAlg.stSum
      rw [mul_finsum]
      refine finsum_congr fun k => ?_
      rw [eta_norm B₁ hd _ (rep_plus _ k).1]
      by_cases hk : B₁.N k.rep = 0
      · rw [hk, mul_zero, mul_zero]
      · rw [GlobalTheory.T.eta_gramDet_eq_one_of_selfDual_lattice K B₁ k.rep (rep_plus _ k).2 (nonempty_of_N_ne_zero B₁ _ hk), mul_one]
    have hst : ∑ᶠ k : B₂.Cl, B₂.N k.rep = B₂.stSum := rfl
    rw [hS, hS₁, hst] at hQ
    have hk : InvAlg.kapSum B₁ B₂ =
        (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) * (B₁.stSum * B₂.stSum) := by
      calc InvAlg.kapSum B₁ B₂
          = K.eta (B₁.gramDet 1) * (K.eta (B₁.gramDet 1) * InvAlg.kapSum B₁ B₂) := by
            rw [← mul_assoc, he, one_mul]
        _ = K.eta (B₁.gramDet 1) * ((-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) *
            (K.eta (B₁.gramDet 1) * B₁.stSum * B₂.stSum)) := by rw [hQ]
        _ = (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) * (B₁.stSum * B₂.stSum) *
            (K.eta (B₁.gramDet 1) * K.eta (B₁.gramDet 1)) := by ring
        _ = _ := by rw [he, mul_one]
    rw [hk, ← mul_assoc, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero, one_mul]
end GlobalTheory.UnitLemma.LieEnd
