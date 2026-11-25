-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.smul_mem_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:38:30.255745+00:00
-- url     : https://prove2.me/submissions/c26a7d04-dafe-4b73-9591-a695a107143c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_ipow_add
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_ipow_zero
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_ipow_sum
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_star_mem_ipow_neg
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_prod_le_of_forall
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_prod_smul_mem
import Theorems.Thm_GlobalTheory_DegCnt_PosIso_Dl_ne
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_mem_dual_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (N : NF H r) (Λ : Submodule (𝓞 K) V) (hΛ : IsFramed N.F N.F' Λ N.aa) (γ : K)
    (hγ : ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range N.j, ((r : ℤ) - a)),
      γ * y / Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) ∈ (1 : Submodule (𝓞 K) K))
    {ξ : V} (hξ : ξ ∈ N.F.Xa N.j) (hp : ∀ y ∈ Λ, y ∈ N.F'.X → H.B ξ y ∈ (1 : Submodule (𝓞 K) K)) :
    γ • ξ ∈ Λ := by
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x hx
    rw [← hΛ.1.2, mem_dual_iff] at hx
    exact hx.2
  have hD := Dl_ne N
  set D := Dl N.F N.F' N.j (N.j_le.trans (Nat.le_succ r)) with hDdef
  set m : ℤ := 2 * ∑ a ∈ Finset.range N.j, ((r : ℤ) - a) with hm
  let J : Submodule (𝓞 K) K := Λ.comap ((LinearMap.toSpanSingleton K V (D • ξ)).restrictScalars (𝓞 K))
  have h1 : ipow N.𝔡 (-m) ≤ J := by
    have e : -m = ∑ i : Fin N.j ⊕ Fin N.j,
        Sum.elim (fun a : Fin N.j => -((r : ℤ) - a.val)) (fun a : Fin N.j => -((r : ℤ) - a.val)) i := by
      rw [Fintype.sum_sum_type, hm, ← Fin.sum_univ_eq_sum_range (fun a : ℕ => (r : ℤ) - a)]
      simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_neg_distrib]
      ring
    rw [e, ipow_sum _ N.𝔡_ne]
    refine prod_le_of_forall _ _ fun f hf => ?_
    have := prod_smul_mem N.F N.F' Λ N.aa hΛ.2.1 hΛ.2.2 hint N.j_le (fun a => f (Sum.inl a))
      (fun a => star (f (Sum.inr a))) (fun a => hf (Sum.inl a)) (fun a => ?_) hξ hp
    · show (∏ i, f i) • (D • ξ) ∈ Λ
      convert this using 1
      rw [smul_smul, Fintype.prod_sum_type, star_prod]
      simp only [star_star]
      congr 1; ring
    · have h2 := hf (Sum.inr a)
      have ha : a.val ≤ r := a.isLt.le.trans N.j_le
      have e2 : (r : ℤ) - a.val = ((r - a.val : ℕ) : ℤ) := by push_cast [ha]; ring
      show _ ∈ ipow N.𝔡 (-((r : ℤ) - a.val))
      simp only [Sum.elim_inr] at h2
      rw [e2] at h2 ⊢
      exact star_mem_ipow_neg _ N.𝔡_ne N.𝔡_star _ _ h2
  have h2 : ∀ w ∈ ipow N.𝔡 m * ipow N.𝔡 (-m), γ / D * w ∈ ipow N.𝔡 (-m) := by
    intro w hw
    refine Submodule.mul_induction_on hw ?_ ?_
    · intro y hy y' hy'
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hγ y hy)
      have : γ / D * (y * y') = o • y' := by rw [Algebra.smul_def, ho]; ring
      rw [this]; exact Submodule.smul_mem _ _ hy'
    · intro a b ha hb; rw [mul_add]; exact add_mem ha hb
  have h3 := h1 (h2 1 (by rw [← ipow_add _ N.𝔡_ne, add_neg_cancel, ipow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩))
  have h4 : (γ / D * 1) • (D • ξ) ∈ Λ := h3
  rwa [smul_smul, mul_one, div_mul_cancel₀ _ hD] at h4
end GlobalTheory.DegCnt.PosIso
