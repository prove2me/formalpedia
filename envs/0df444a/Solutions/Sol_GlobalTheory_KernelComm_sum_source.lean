-- Prove2me | solution 1 for GlobalTheory.KernelComm.sum_source
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:15:44.093395+00:00
-- url     : https://prove2.me/submissions/a0fe5de6-b7e5-433e-89db-5c1aac780eac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Theorems.Thm_GlobalTheory_LatPair_cross_hasVal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp
noncomputable section
open GlobalTheory GlobalTheory.KernelComm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
variable [Fintype n'] (q : Unif k) {P₁ : Pair k n'} {e₁ : n' → k} (he : P₁.HasVal e₁ 1) (Q : Pair k n)
  (x : Matrix n n' k)
include he
open Classical
namespace GlobalTheory.KernelComm
theorem _root_.solution :
    midInd q P₁.ker e₁ Q x = ∑ P ∈ withLat P₁.ker with cross q P₁ P = 1, phiOne P Q x := by
  rw [midInd]
  have hq : q.1 • e₁ ∈ P₁.ker := Pair.smul_mem_ker q.mem_max he.mem
  split_ifs with h
  · let f : P₁.ker →ₗ[𝒪[k]] 𝓀[k] := Q.fn ∘ₗ ((Matrix.mulVecLin x).restrictScalars 𝒪[k]).restrict h.1
    have hf : ∀ y : P₁.ker, Q.HasVal (x *ᵥ y) (f y) := fun y => ⟨h.1 y y.2, rfl⟩
    have h1 : f ⟨_, hq⟩ = 1 := (hf ⟨_, hq⟩).unique h.2
    let R : Pair k n' := ⟨P₁.ker, P₁.ker_isLat, f, fun h0 => by simp [h0] at h1⟩
    have hR : Maps R Q x := ⟨h.1, fun _ => rfl⟩
    rw [Finset.sum_eq_single_of_mem R]
    · exact (if_pos hR).symm
    · exact Finset.mem_filter.2 ⟨mem_withLat.2 rfl, (cross_hasVal q (P := R) rfl he).unique ⟨hq, h1⟩⟩
    · refine fun P hP h2 => if_neg fun h3 => h2 (Pair.ext fun y a => ?_)
      have hl : P.lat = R.lat := mem_withLat.1 (Finset.mem_filter.1 hP).1
      rw [maps_iff_hasVal] at hR h3
      constructor
      · intro hy
        have h4 := R.hasVal_fn ⟨y, hl ▸ hy.mem⟩
        exact (hR _ _ h4).unique (h3 _ _ hy) ▸ h4
      · intro hy
        have h4 := P.hasVal_fn ⟨y, hl ▸ hy.mem⟩
        exact (h3 _ _ h4).unique (hR _ _ hy) ▸ h4
  · refine (Finset.sum_eq_zero fun P h1 => if_neg fun h3 => h ?_).symm
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h1
    rw [mem_withLat] at h1
    exact ⟨h1 ▸ h3.1, maps_iff_hasVal.1 h3 _ _ (h2 ▸ cross_hasVal q h1 he)⟩
end GlobalTheory.KernelComm
