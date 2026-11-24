-- Prove2me | solution 1 for GlobalTheory.DualTransfer.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:25:06.52944+00:00
-- url     : https://prove2.me/submissions/03c46d2e-0eff-479e-b59f-69cb957ced05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DivisiblePontryaginAnnihilatorDuality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DualTransfer
namespace GlobalTheory.DualTransfer
theorem _root_.solution {G : Type} [AddCommGroup G] (A L₀ : AddSubgroup G) (N : ℕ) (hN : 0 < N)
    (tf : Function.Injective fun t : G => N • t)
    (hA : ∀ t ∈ A, N • t ∈ L₀)
    (fin : ∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L₀, ∃ r ∈ R, ∃ u ∈ L₀, t = r + k • u) :
    Finite (A ⧸ (L₀.map (nsmulAddMonoidHom N)).addSubgroupOf A) := by
  classical
  obtain ⟨R, hR, hcov⟩ := fin (N * N) (Nat.mul_pos hN hN)
  set S := (L₀.map (nsmulAddMonoidHom N)).addSubgroupOf A with hS
  let c : G → A ⧸ S := fun r =>
    if h : ∃ t : A, ∃ u ∈ L₀, N • (t : G) = r + (N * N) • u then
      ((Classical.choose h : A) : A ⧸ S) else 0
  have key : ∀ t : A, ∃ r ∈ R, c r = (t : A ⧸ S) := by
    intro t
    obtain ⟨r, hr, u, hu, htu⟩ := hcov _ (hA t t.2)
    have h : ∃ t : A, ∃ u ∈ L₀, N • (t : G) = r + (N * N) • u := ⟨t, u, hu, htu⟩
    refine ⟨r, hr, ?_⟩
    simp only [c, dif_pos h]
    obtain ⟨u', hu', ht'⟩ := Classical.choose_spec h
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map]
    refine ⟨u - u', L₀.sub_mem hu hu', ?_⟩
    apply tf
    show N • (N • (u - u')) = N • (((-Classical.choose h + t : A)) : G)
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, smul_add, smul_neg, htu, ht', smul_smul, smul_sub]
    abel
  have hfin : Set.Finite (Set.univ : Set (A ⧸ S)) := by
    refine (hR.image c).subset ?_
    intro q _
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, hr, hc⟩ := key t
    exact ⟨r, hr, hc⟩
  exact Set.finite_univ_iff.mp hfin
end GlobalTheory.DualTransfer
