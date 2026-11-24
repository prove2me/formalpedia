-- Prove2me | solution 1 for GlobalTheory.Published.SvN.exists_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:56:30.546344+00:00
-- url     : https://prove2.me/submissions/160250f1-d7ac-4ac8-a0ff-9a04a9beae7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_SvN_Alt_sq_swap
import Theorems.Thm_GlobalTheory_Published_SvN_Alt_perp_perp_perp
import Theorems.Thm_GlobalTheory_Published_SvN_Ops_comm
import Theorems.Thm_GlobalTheory_Published_SvN_Ops_eq_zero
import Theorems.Thm_GlobalTheory_Published_SvN_Splits_comp
import Theorems.Thm_GlobalTheory_Published_SvN_average

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
variable {W M : Type} [AddCommGroup W] [AddCommGroup M] [Module ℂ M]
variable {c : W → W → ℂ}
variable {ρ : W → Module.End ℂ M}
variable {A : AddSubgroup W} {α : W → ℂ}
namespace GlobalTheory.Published.SvN
theorem _root_.solution (h : Alt c) (hρ : Ops c ρ) (hα : Splits c A α) (T : Set W) (hU : ∀ u ∈ h.perp T, α u = 1)
    [Finite (A ⧸ (h.perp T).addSubgroupOf A)] (N : Submodule ℂ M) (hN : ∀ x, ∀ m ∈ N, ρ x m ∈ N)
    (v : M) (hvN : v ∈ N) (hv0 : v ≠ 0) (hv : ∀ u ∈ h.perp T, ρ u v = v) :
    ∃ e ∈ N, e ≠ 0 ∧ ∀ a ∈ A, ρ a e = α a • e := by
  classical
  set U := h.perp T with hUdef
  let := Fintype.ofFinite (A ⧸ U.addSubgroupOf A)
  by_contra hcon
  have hz : ∀ w ∈ h.perp U, ∑ q : A ⧸ U.addSubgroupOf A, c q.out.1 w ^ 2 • ((α q.out.1)⁻¹ • ρ q.out.1 v) = 0 := by
    intro w hw
    have hm : ∀ u ∈ U, ρ u (ρ w v) = ρ w v := fun u hu => by
      rw [hρ.comm h, h.sq_swap (hw u hu), one_smul, hv u hu]
    have h0 : ∑ q : A ⧸ U.addSubgroupOf A, (α q.out.1)⁻¹ • ρ q.out.1 (ρ w v) = 0 := by
      by_contra hne
      exact hcon ⟨_, N.sum_mem fun q _ => N.smul_mem _ (hN _ _ (hN _ _ hvN)), hne, average hρ hα U hU _ hm⟩
    refine hρ.eq_zero h (x := w) ?_
    rw [map_sum, ← h0]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hρ.comm h q.out.1 w, map_smul, map_smul, smul_comm]
  let χ : A ⧸ U.addSubgroupOf A → (Multiplicative (h.perp U) →* ℂ) := fun q =>
    { toFun := fun w => c q.out.1 w.toAdd.1 ^ 2
      map_one' := by simp [h.zero_right]
      map_mul' := fun x y => by simp [h.right, mul_pow] }
  have hχ : Function.Injective χ := by
    intro p q hpq
    rw [← p.out_eq, ← q.out_eq]
    refine QuotientAddGroup.eq.2 (h.perp_perp_perp T _ fun w hw => ?_)
    have h1 : c p.out.1 w ^ 2 = c q.out.1 w ^ 2 := DFunLike.congr_fun hpq (Multiplicative.ofAdd ⟨w, hw⟩)
    have h2 := h.left (-p.out.1) p.out.1 w
    rw [neg_add_cancel, h.zero_left] at h2
    show c (-p.out.1 + q.out.1) w ^ 2 = 1
    rw [h.left, mul_pow, ← h1, ← mul_pow, ← h2, one_pow]
  have hli := (linearIndependent_monoidHom (Multiplicative (h.perp U)) ℂ).comp χ hχ
  have hq : ∀ q : A ⧸ U.addSubgroupOf A, (α q.out.1)⁻¹ • ρ q.out.1 v = 0 := by
    intro q
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_
    refine Fintype.linearIndependent_iff.1 hli (fun q => φ ((α q.out.1)⁻¹ • ρ q.out.1 v)) ?_ q
    funext w
    have := congrArg φ (hz w.toAdd.1 w.toAdd.2)
    rw [map_sum, map_zero] at this
    rw [Finset.sum_apply, Pi.zero_apply, ← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [φ.map_smul (c q.out.1 w.toAdd.1 ^ 2), smul_eq_mul, mul_comm]
    rfl
  have := (smul_eq_zero.1 (hq 0)).resolve_left (inv_ne_zero (hα.ne _ (Quotient.out (0 : A ⧸ U.addSubgroupOf A)).2))
  exact hv0 (hρ.eq_zero h this)
end GlobalTheory.Published.SvN
