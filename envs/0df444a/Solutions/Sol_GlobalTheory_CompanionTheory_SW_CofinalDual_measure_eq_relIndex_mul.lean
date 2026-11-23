-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CofinalDual.measure_eq_relIndex_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:47.873337+00:00
-- url     : https://prove2.me/submissions/4e009bc4-96af-4783-b0ae-2aba8ed99ca0

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AnnihilatorOfAnnihilatorLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CofinalDual
namespace GlobalTheory.CompanionTheory.SW.CofinalDual
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddLeftInvariant] (S T : AddSubgroup V) (hST : S ≤ T) (hS : IsOpen (S : Set V))
    (hf : S.relIndex T ≠ 0) : μ T = S.relIndex T * μ S := by
  classical
  haveI : (S.addSubgroupOf T).FiniteIndex := ⟨hf⟩
  haveI := Fintype.ofFinite (T ⧸ S.addSubgroupOf T)
  let o : T ⧸ S.addSubgroupOf T → T := fun q => Quotient.out q
  have ho : ∀ q, ((o q : T) : T ⧸ S.addSubgroupOf T) = q := fun q => QuotientAddGroup.out_eq' q
  let C : T ⧸ S.addSubgroupOf T → Set V := fun q => (fun v => (-(o q : V)) + v) ⁻¹' (S : Set V)
  have hU : (T : Set V) = ⋃ q, C q := by
    ext v
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hv
      refine ⟨((⟨v, hv⟩ : T) : T ⧸ S.addSubgroupOf T), ?_⟩
      have h := QuotientAddGroup.eq.1 (ho ((⟨v, hv⟩ : T) : T ⧸ S.addSubgroupOf T))
      exact AddSubgroup.mem_addSubgroupOf.1 h
    · rintro ⟨q, hq⟩
      have h1 : -(o q : V) + v ∈ T := hST hq
      have := T.add_mem (o q).2 h1
      simpa using this
  have hd : Pairwise (Function.onFun Disjoint C) := by
    intro q q' hne
    refine Set.disjoint_left.2 fun v hv hv' => hne ?_
    have h1 : -(o q : V) + v ∈ S := hv
    have h2 : -(o q' : V) + v ∈ S := hv'
    have h3 : -(o q : V) + (o q' : V) ∈ S := by
      have := S.sub_mem h1 h2
      have e : -(o q : V) + v - (-(o q' : V) + v) = -(o q : V) + (o q' : V) := by abel
      rwa [e] at this
    have h4 : ((o q : T) : T ⧸ S.addSubgroupOf T) = (o q' : T) :=
      QuotientAddGroup.eq.2 (AddSubgroup.mem_addSubgroupOf.2 (by simpa using h3))
    rw [ho, ho] at h4
    exact h4
  have hm : ∀ q, MeasurableSet (C q) := fun q =>
    (hS.preimage (continuous_const.add continuous_id)).measurableSet
  have hc : ∀ q, μ (C q) = μ S := fun q => measure_preimage_add μ _ _
  rw [hU, measure_iUnion hd hm, tsum_fintype]
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 2
  rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
end GlobalTheory.CompanionTheory.SW.CofinalDual
