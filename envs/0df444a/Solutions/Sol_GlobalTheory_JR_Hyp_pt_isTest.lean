-- Prove2me | solution 1 for GlobalTheory.JR.Hyp.pt_isTest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:16.681469+00:00
-- url     : https://prove2.me/submissions/596181ae-bc9f-41b7-af32-63c8c2b38763

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierPsiKPreservesTestFunctions
import Theorems.Thm_GlobalTheory_JR_Hyp_PtTest_hasCompactSupport_of_loc
import Theorems.Thm_GlobalTheory_JR_Hyp_PtTest_slice_eventually
import Theorems.Thm_GlobalTheory_JR_Hyp_PtTest_slice_isTest
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts
import Theorems.Thm_GlobalTheory_T_selfDual_measure_exists_unique_fourier_inversion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory.JR.Hyp.PtTest
namespace GlobalTheory.JR.Hyp
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ) := by
  intro F E _ _ _ _ _ A ψ hψ x ν hν Φ hΦ

  let β : LinearMap.BilinForm F A.K := LinearMap.comp (Algebra.traceForm F A.K) (LinearMap.mulLeft F (x : A.K))
  have hβapp : ∀ u b, β u b = Algebra.trace F A.K ((x : A.K) * u * b) := fun u b => by simp [β, Algebra.traceForm_apply, mul_assoc]
  have hsymm : β.IsSymm := by
    refine ⟨fun u b => ?_⟩
    simp only [RingHom.id_apply, hβapp]
    ring_nf
  have htr := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
  have hsepL : ∀ u : A.K, (∀ b, β u b = 0) → u = 0 := fun u hu => by
    have h1 : (x : A.K) * u = 0 := htr.1 _ fun b => by simpa [hβapp] using hu b
    simpa using congrArg (fun t => ((x⁻¹ : A.Kˣ) : A.K) * t) h1
  have hnd : β.Nondegenerate := ⟨hsepL, fun b hb => hsepL b fun u => by
    have := hb u
    rw [hβapp] at this
    rw [hβapp, mul_right_comm]; exact this⟩
  have hF : ∀ f : A.K → ℂ, IsTest f → IsTest (fourB ν (kx A ψ (x : A.K)) f) := fun f hf =>
    (GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ A.K β hsymm hnd).2 ν hν f hf
  have hG : ∀ p, Hyp.pt A ν ψ x Φ p = fourB ν (kx A ψ (x : A.K)) (fun b => Φ (p.1, b)) p.2 := fun p => rfl
  have hloc : IsLocallyConstant (Hyp.pt A ν ψ x Φ) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨a, u⟩
    have h1 := slice_eventually Φ hΦ a
    have h2 := (IsLocallyConstant.iff_eventually_eq _).1 (hF _ (slice_isTest Φ hΦ a)).1 u
    rw [nhds_prod_eq]
    filter_upwards [h1.prod_mk h2] with q hq
    rw [hG, hG, hq.1]
    exact hq.2
  refine ⟨hloc, ?_⟩
  have hC1 : IsCompact (Prod.fst '' tsupport Φ) := hΦ.2.isCompact.image continuous_fst
  obtain ⟨t, -, ht⟩ := hC1.elim_nhds_subcover (fun a => {a' | (fun b => Φ (a', b)) = fun b => Φ (a, b)})
    fun a _ => slice_eventually Φ hΦ a
  refine hasCompactSupport_of_loc _ hloc
    ((Prod.fst '' tsupport Φ) ×ˢ ⋃ i ∈ t, tsupport (fourB ν (kx A ψ (x : A.K)) fun b => Φ (i, b)))
    (hC1.prod (t.isCompact_biUnion fun i _ => (hF _ (slice_isTest Φ hΦ i)).2.isCompact)) ?_
  rintro ⟨a, u⟩ hq
  by_contra hne
  apply hq
  have ha : a ∈ Prod.fst '' tsupport Φ := by
    by_contra ha
    apply hne
    have h0 : ∀ b, Φ (a, b) = 0 := fun b => by
      by_contra hb
      exact ha ⟨(a, b), subset_tsupport _ hb, rfl⟩
    simp [hG, fourB, h0]
  refine ⟨ha, ?_⟩
  obtain ⟨i, hi, hai⟩ := Set.mem_iUnion₂.1 (ht ha)
  refine Set.mem_iUnion₂.2 ⟨i, hi, subset_tsupport _ ?_⟩
  rw [hG] at hne
  simp only [Set.mem_setOf_eq] at hai
  rw [Function.mem_support]
  rwa [hai] at hne
end GlobalTheory.JR.Hyp
