-- Prove2me | solution 1 for GlobalTheory.VolPow.vol_div_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:14:31.822425+00:00
-- url     : https://prove2.me/submissions/c9dfb791-829a-48cc-aa8d-463fd366815b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarCompactOpenRatioEqZpowOfTopNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
namespace GlobalTheory.VolPow
open MeasureTheory ValuativeRel Matrix Topology in
open scoped Pointwise in
private lemma finiteIndex_and_index_subgroupOf_eq_pow {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (q : ℕ) (hq : q.Prime)
    (hpow : ∀ u : G, ∀ U ∈ 𝓝 (1 : G), ∃ m : ℕ, u ^ (q ^ m) ∈ U) {H K : Subgroup G}
    (hH : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO H) (hK : IsOpen (K : Set G)) :
    (K.subgroupOf H).FiniteIndex ∧ ∃ b : ℕ, (K.subgroupOf H).index = q ^ b := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH.2
  set K' := K.subgroupOf H
  have hK' : IsOpen (K' : Set H) := hK.preimage continuous_subtype_val
  haveI : Finite (H ⧸ K') := Subgroup.quotient_finite_of_isOpen K' hK'
  haveI : K'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set N := K'.normalCore
  have hNo : IsOpen (N : Set H) :=
    N.isOpen_of_isClosed_of_finiteIndex (K'.normalCore_isClosed (K'.isClosed_of_isOpen hK'))
  haveI : Finite (H ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  have hp : IsPGroup q (H ⧸ N) := by
    intro x
    induction x using QuotientGroup.induction_on with | H u => ?_
    have hU : (Subtype.val '' (N : Set H)) ∈ 𝓝 (1 : G) :=
      (hH.1.isOpenMap_subtype_val _ hNo).mem_nhds ⟨1, N.one_mem, rfl⟩
    obtain ⟨m, hm⟩ := hpow (u : G) _ hU
    obtain ⟨v, hv, hvu⟩ := hm
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have e : v = u ^ (q ^ m) := Subtype.ext (by rw [hvu]; simp)
    rwa [← e]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hp
  have hdvd : K'.index ∣ q ^ a := by
    rw [← ha]
    exact Subgroup.index_dvd_of_le (Subgroup.normalCore_le K')
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hq).1 hdvd
  exact ⟨inferInstance, b, hb⟩
open MeasureTheory ValuativeRel Matrix Topology in
open scoped Pointwise in
private lemma measure_eq_index_subgroupOf_mul_measure {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] {H K : Subgroup G} (hKH : K ≤ H) (hK : IsOpen (K : Set G))
    [(K.subgroupOf H).FiniteIndex] :
    μ H = ((K.subgroupOf H).index : ENNReal) * μ K := by
  classical
  set K' := K.subgroupOf H
  letI : Fintype (H ⧸ K') := Subgroup.fintypeQuotientOfFiniteIndex
  have hcover : (H : Set G) = ⋃ c : H ⧸ K', ((Quotient.out c : H) : G) • (K : Set G) := by
    ext g
    constructor
    · intro hg
      refine Set.mem_iUnion.2 ⟨(QuotientGroup.mk (⟨g, hg⟩ : H) : H ⧸ K'), ?_⟩
      obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul K' (⟨g, hg⟩ : H)
      refine Set.mem_smul_set.2 ⟨((y⁻¹ : K') : H), ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.1 (y⁻¹).2
      · rw [smul_eq_mul, hy]
        simp
    · intro hg
      obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hg
      obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hc
      exact H.mul_mem (Quotient.out c).2 (hKH hy)
  have hdisj : Pairwise (fun c d : H ⧸ K' => Disjoint (((Quotient.out c : H) : G) • (K : Set G))
      (((Quotient.out d : H) : G) • (K : Set G))) := by
    intro c d hcd
    rw [Set.disjoint_left]
    rintro g hgc hgd
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hgc
    obtain ⟨z, hz, hzy⟩ := Set.mem_smul_set.1 hgd
    apply hcd
    rw [← Quotient.out_eq c, ← Quotient.out_eq d]
    apply (QuotientGroup.eq (s := K')).2
    rw [Subgroup.mem_subgroupOf]
    have e : (((Quotient.out c : H)⁻¹ * Quotient.out d : H) : G) = y * z⁻¹ := by
      simp only [smul_eq_mul] at hzy
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, hzy]
      group
    rw [e]
    exact K.mul_mem hy (K.inv_mem hz)
  rw [hcover, measure_iUnion hdisj (fun c => (hK.smul _).measurableSet), tsum_fintype]
  simp only [measure_smul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Subgroup.index,
    Nat.card_eq_fintype_card]
end GlobalTheory.VolPow
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.VolPow
open MeasureTheory ValuativeRel Matrix Topology
open scoped Pointwise
namespace GlobalTheory.VolPow
namespace _root_.GlobalTheory.VolPow
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (q : ℕ), q.Prime → (∀ u : G, ∀ U ∈ 𝓝 (1 : G), ∃ m : ℕ, u ^ (q ^ m) ∈ U) → ∀ H₁ H₂ : Subgroup G, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO H₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO H₂ → ∃ z : ℤ, (μ H₁).toReal / (μ H₂).toReal = (q : ℝ) ^ z := by
  intro G _ _ _ _ _ μ _ q hq hpow H₁ H₂ h₁ h₂
  have hK : IsOpen ((H₁ ⊓ H₂ : Subgroup G) : Set G) := h₁.1.inter h₂.1
  obtain ⟨hf₁, b₁, hb₁⟩ := finiteIndex_and_index_subgroupOf_eq_pow q hq hpow (K := H₁ ⊓ H₂) h₁ hK
  obtain ⟨hf₂, b₂, hb₂⟩ := finiteIndex_and_index_subgroupOf_eq_pow q hq hpow (K := H₁ ⊓ H₂) h₂ hK
  have e₁ := measure_eq_index_subgroupOf_mul_measure μ (H := H₁) inf_le_left hK
  have e₂ := measure_eq_index_subgroupOf_mul_measure μ (H := H₂) inf_le_right hK
  have hcpt : IsCompact ((H₁ ⊓ H₂ : Subgroup G) : Set G) :=
    h₁.2.of_isClosed_subset ((H₁ ⊓ H₂).isClosed_of_isOpen hK)
      (fun x hx => (inf_le_left : H₁ ⊓ H₂ ≤ H₁) hx)
  have hpos : 0 < (μ (H₁ ⊓ H₂ : Subgroup G)).toReal :=
    ENNReal.toReal_pos (hK.measure_ne_zero μ ⟨1, (H₁ ⊓ H₂).one_mem⟩) hcpt.measure_lt_top.ne
  refine ⟨(b₁ : ℤ) - b₂, ?_⟩
  rw [e₁, e₂, hb₁, hb₂, ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_natCast]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
  field_simp
  push_cast
  ring
end _root_.GlobalTheory.VolPow
end GlobalTheory.VolPow
