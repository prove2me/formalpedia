-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.StdLattice.mem_span_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:49:18.110362+00:00
-- url     : https://prove2.me/submissions/9af0af8b-61e5-482a-8d58-db12c4cbe4cb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SchrodingerModelSelfDualLatticeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsStd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.StdLattice
namespace GlobalTheory.CompanionTheory.StdLattice
theorem _root_.solution {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] {f : G → ℂ}
    (hf : HasCompactSupport f) (H : AddSubgroup G) (hH : IsOpen (H : Set G))
    (hinv : ∀ y ∈ tsupport f, ∀ u ∈ H, f (y + u) = f y) :
    f ∈ Submodule.span ℂ (Set.range fun a : G => fun x : G => (H : Set G).indicator (fun _ => (1 : ℂ)) (x + a)) := by
  classical
  haveI : DiscreteTopology (G ⧸ H) := QuotientAddGroup.discreteTopology hH
  have hfin : ((QuotientAddGroup.mk : G → G ⧸ H) '' tsupport f).Finite :=
    (hf.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  have key : ∀ c ∈ hfin.toFinset, ∀ x : G, (QuotientAddGroup.mk x : G ⧸ H) = c →
      f x = f (Quotient.out c) := by
    intro c hc x hx
    rw [Set.Finite.mem_toFinset] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    have h1 : ∀ z : G, (QuotientAddGroup.mk z : G ⧸ H) = QuotientAddGroup.mk k → f z = f k := by
      intro z hz
      have hm : -k + z ∈ H := QuotientAddGroup.eq.1 hz.symm
      have h2 := hinv k hk (-k + z) hm
      rwa [add_neg_cancel_left] at h2
    rw [h1 x hx, h1 _ (QuotientAddGroup.out_eq' _)]
  have hfeq : f = ∑ c ∈ hfin.toFinset, f (Quotient.out c) •
      (fun x : G => (H : Set G).indicator (fun _ => (1 : ℂ)) (x + -Quotient.out c)) := by
    funext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hind : ∀ c : G ⧸ H, (H : Set G).indicator (fun _ => (1 : ℂ)) (x + -Quotient.out c) =
        if c = (QuotientAddGroup.mk x : G ⧸ H) then 1 else 0 := by
      intro c
      have hiff : x + -Quotient.out c ∈ H ↔ c = (QuotientAddGroup.mk x : G ⧸ H) := by
        rw [add_comm, ← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
      simp only [Set.indicator_apply, SetLike.mem_coe, hiff]
    simp only [hind, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    split_ifs with hx
    · exact key _ hx x rfl
    · apply image_eq_zero_of_notMem_tsupport
      intro hxK
      apply hx
      rw [Set.Finite.mem_toFinset]
      exact ⟨x, hxK, rfl⟩
  rw [hfeq]
  exact Submodule.sum_mem _ fun c _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨-Quotient.out c, rfl⟩)
end GlobalTheory.CompanionTheory.StdLattice
