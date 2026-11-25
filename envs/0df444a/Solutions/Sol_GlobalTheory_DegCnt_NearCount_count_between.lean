-- Prove2me | solution 1 for GlobalTheory.DegCnt.NearCount.count_between
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:15.82862+00:00
-- url     : https://prove2.me/submissions/1b8634e3-cca1-4847-ad8f-10a6811921e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DedekindLFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardLatticesNearReferenceLatticeLe
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_Formalism_SLP_P_card_submodules_le_of_dedekind
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
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.NearCount
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [Module K V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.NearCount
theorem _root_.solution (P : Submodule (𝓞 K) V) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) (e : ℕ) (v : Fin e → V)
    (hv : ∀ i, v i ∈ P) (hP : P ≤ n • P ⊔ Submodule.span (𝓞 K) (Set.range v)) :
    {L : Submodule (𝓞 K) V | n • P ≤ L ∧ L ≤ P}.encard ≤ ((Ideal.absNorm n ^ (e * e) : ℕ) : ℕ∞) := by
  let S : Submodule (𝓞 K) P := (n • P).comap P.subtype
  let w : Fin e → P ⧸ S := fun i => S.mkQ ⟨v i, hv i⟩
  have hS : ∀ a ∈ n, ∀ y : P ⧸ S, a • y = 0 := by
    intro a ha y
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha x.2
  have hgen : ∀ y : P ⧸ S, ∃ c : Fin e → 𝓞 K, y = ∑ i, c i • w i := by
    intro y
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 (hP x.2)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 ht
    refine ⟨c, ?_⟩
    simp only [w, ← map_smul, ← map_sum]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    show ((x - ∑ i, c i • (⟨v i, hv i⟩ : P) : P) : V) ∈ n • P
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, ← hst, add_sub_cancel_right]
    exact hs
  haveI : Finite (𝓞 K ⧸ n) := Ideal.finiteQuotientOfFreeOfNeBot n hn
  let f : (Fin e → 𝓞 K ⧸ n) → P ⧸ S := fun c => ∑ i, (c i).out • w i
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨c, rfl⟩ := hgen y
    refine ⟨fun i => Ideal.Quotient.mk n (c i), Finset.sum_congr rfl fun i _ => ?_⟩
    rw [← sub_eq_zero, ← sub_smul]
    apply hS
    rw [← Ideal.Quotient.eq]
    exact Quotient.out_eq _
  haveI : Finite (P ⧸ S) := Finite.of_surjective f hf
  have hcard : Nat.card (P ⧸ S) ≤ Ideal.absNorm n ^ e := by
    refine (Nat.card_le_card_of_surjective f hf).trans (le_of_eq ?_)
    rw [Nat.card_fun, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    simp
  have hw : Submodule.span (𝓞 K) (Set.range w) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨c, rfl⟩ := hgen y
    exact (Submodule.mem_span_range_iff_exists_fun _).2 ⟨c, rfl⟩
  have hc := Formalism.SLP.P.card_submodules_le_of_dedekind (𝓞 K) (P ⧸ S) e w hw
  haveI : Finite (Submodule (𝓞 K) (P ⧸ S)) := Finite.of_injective _ SetLike.coe_injective
  have hinj : Set.InjOn (fun L : Submodule (𝓞 K) V => (L.comap P.subtype).map S.mkQ)
      {L : Submodule (𝓞 K) V | n • P ≤ L ∧ L ≤ P} := by
    have key : ∀ L : Submodule (𝓞 K) V, n • P ≤ L → L ≤ P →
        (((L.comap P.subtype).map S.mkQ).comap S.mkQ).map P.subtype = L := by
      intro L h1 h2
      rw [Submodule.comap_map_mkQ, sup_eq_right.2 (Submodule.comap_mono h1),
        Submodule.map_comap_subtype, inf_eq_right.2 h2]
    intro L hL L' hL' h
    rw [← key L hL.1 hL.2, ← key L' hL'.1 hL'.2]
    simp only at h
    rw [h]
  refine (Set.encard_le_encard_of_injOn (t := Set.univ) (Set.mapsTo_univ _ _) hinj).trans ?_
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.cast_le, pow_mul]
  exact hc.trans (Nat.pow_le_pow_left hcard e)
end GlobalTheory.DegCnt.NearCount
