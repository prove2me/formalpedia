-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.kill_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:28:40.729838+00:00
-- url     : https://prove2.me/submissions/5eaf15d9-c4b5-426d-8a92-aa2acf4d0ed2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_comp
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_unif
import Theorems.Thm_GlobalTheory_WeilM_HaarUniq_exists_compact_openAddSubgroup
import Theorems.Thm_GlobalTheory_WeilM_HaarUniq_indicator_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution {X V : Type} [TopologicalSpace X] [T2Space X] [AddCommGroup V] [TopologicalSpace V]
    [NonarchimedeanAddGroup V] [LocallyCompactSpace V] [T2Space V] (S : Set X) (l : (X × V → ℂ) →ₗ[ℂ] ℂ)
    (h : ∀ f ∈ SB X, (∀ x ∉ S, f x = 0) → ∀ g ∈ SB V, l (fun z => f z.1 * g z.2) = 0)
    {F : X × V → ℂ} (hF : F ∈ SB (X × V)) (hS : ∀ z : X × V, z.1 ∉ S → F z = 0) : l F = 0 := by
  classical
  obtain ⟨K₁, hK₁⟩ := NonarchimedeanAddGroup.is_nonarchimedean _
    (sb_unif hF (fun (k : V) z => (z.1, z.2 + k)) 0 (by fun_prop) (by simp))
  obtain ⟨K₀, hK₀⟩ := HaarUniq.exists_compact_openAddSubgroup (V := V)
  set K := K₀ ⊓ K₁
  have hK : IsCompact (K : Set V) := hK₀.of_isClosed_subset K.isClosed (fun x hx => hx.1)
  have hinv : ∀ k ∈ K, ∀ x v, F (x, v + k) = F (x, v) := fun k hk x v => by
    by_cases hx : (x, v) ∈ tsupport F
    · exact hK₁ hk.2 _ hx
    · by_cases hx' : (x, v + k) ∈ tsupport F
      · simpa using (hK₁ (neg_mem hk.2 : -k ∈ K₁) _ hx').symm
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
  haveI : DiscreteTopology (V ⧸ K.toAddSubgroup) := QuotientAddGroup.discreteTopology K.isOpen
  have hfin : ((fun z : X × V => (z.2 : V ⧸ K.toAddSubgroup)) '' tsupport F).Finite :=
    (IsCompact.image hF.2 (QuotientAddGroup.continuous_mk.comp continuous_snd)).finite_of_discrete
  have hmem : ∀ (x : V) (q : V ⧸ K.toAddSubgroup), x + -q.out ∈ (K : Set V) ↔ q = (x : V ⧸ K.toAddSubgroup) := by
    intro x q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq]
    rw [add_comm]; rfl
  have : F = ∑ q ∈ hfin.toFinset, fun z : X × V =>
      F (z.1, q.out) * Set.indicator (K : Set V) (fun _ => (1 : ℂ)) (z.2 + -q.out) := by
    ext ⟨x, v⟩
    have hx : F (x, (v : V ⧸ K.toAddSubgroup).out) = F (x, v) := by
      rw [← hinv _ ((hmem v _).2 rfl) x]; congr 2; abel
    rw [Finset.sum_apply, Finset.sum_eq_single (v : V ⧸ K.toAddSubgroup)]
    · rw [Set.indicator_of_mem ((hmem v _).2 rfl), hx, mul_one]
    · intro q _ hq
      rw [Set.indicator_of_notMem (fun h => hq ((hmem v q).1 h)), mul_zero]
    · intro h
      rw [hx, image_eq_zero_of_notMem_tsupport (f := F) (x := (x, v)), zero_mul]
      exact fun hs => h (hfin.mem_toFinset.2 ⟨_, hs, rfl⟩)
  rw [this, map_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  exact h (fun x => F (x, q.out)) (sb_comp (fun x => (x, q.out)) Prod.fst (by fun_prop) (by fun_prop) (fun _ => rfl) hF)
    (fun x hx => hS _ hx) (fun v => Set.indicator (K : Set V) (fun _ => (1 : ℂ)) (v + -q.out))
    (sb_comp (fun v => v + -q.out) (fun v => v + q.out) (by fun_prop) (by fun_prop) (by simp) (HaarUniq.indicator_mem K hK))
end GlobalTheory.ThK.Dbl.LD
