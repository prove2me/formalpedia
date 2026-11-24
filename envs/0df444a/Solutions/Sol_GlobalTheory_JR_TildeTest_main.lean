-- Prove2me | solution 1 for GlobalTheory.JR.TildeTest.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:43:12.717966+00:00
-- url     : https://prove2.me/submissions/57ddba9c-b6bf-4071-a5f9-b1b5dd24cff2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnifConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierEtaleKProdLocallyConstantCompactSu
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts
import Theorems.Thm_GlobalTheory_T_selfDual_measure_exists_unique_fourier_inversion
import Theorems.Thm_GlobalTheory_TestFn_slice_test
import Theorems.Thm_GlobalTheory_TestFn_unif_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.TildeTest
namespace GlobalTheory.JR.TildeTest
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (fun p : A.K × A.K => A.tilde μK ψ φ' p.1 p.2) := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ φ' hφ
  set T : A.K → A.K → ℂ := fun c u => A.tilde μK ψ φ' c u with hTdef
  have hslice : ∀ c, IsTest (fun u => T c u) := by
    intro c
    have hnd := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
    have h := (GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd).2 μK hμ
      (fun b => φ' (b, c)) (GlobalTheory.TestFn.slice_test φ' hφ c)
    convert h using 1
    funext u
    simp only [hTdef, Et.tilde, fourB, Algebra.traceForm_apply, Et.psiK]
    congr 1; funext b; rw [mul_comm u b]
  obtain ⟨V, hV, hVf⟩ := GlobalTheory.TestFn.unif_const (A.K × A.K) φ' hφ
  set V₂ : Set A.K := {v | ((0 : A.K), v) ∈ V} with hV₂def
  have hV₂ : V₂ ∈ 𝓝 (0 : A.K) := by
    have hc : Continuous (fun v : A.K => ((0 : A.K), v)) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by rw [show ((0 : A.K), (0 : A.K)) = (0 : A.K × A.K) from rfl]; exact hV)
  have hshift : ∀ c c', c' - c ∈ V₂ → ∀ u, T c' u = T c u := by
    intro c c' hcc u
    simp only [hTdef, Et.tilde]
    congr 1; funext b
    have := hVf (b, c) (0, c' - c) hcc
    simp only [Prod.mk_add_mk, add_zero, add_sub_cancel] at this
    rw [this]
  have hnbhd : ∀ c : A.K, {c' | c' - c ∈ V₂} ∈ 𝓝 c := by
    intro c
    have hc : Continuous (fun c' : A.K => c' - c) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV₂)
  have hlc : IsLocallyConstant (fun p : A.K × A.K => T p.1 p.2) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨c₀, u₀⟩
    have hu : {u | T c₀ u = T c₀ u₀} ∈ 𝓝 u₀ := ((hslice c₀).1.isOpen_fiber _).mem_nhds rfl
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod (hnbhd c₀) hu] with p hp
    rw [hshift c₀ p.1 hp.1 p.2]; exact hp.2
  refine ⟨hlc, ?_⟩
  have hC₂ : IsCompact (Prod.snd '' tsupport φ') := hφ.2.image continuous_snd
  obtain ⟨t, -, hcover⟩ := hC₂.elim_nhds_subcover (fun c => {c' | c' - c ∈ V₂}) (fun c _ => hnbhd c)
  have hK : IsCompact ((Prod.snd '' tsupport φ') ×ˢ ⋃ c ∈ t, tsupport (fun u => T c u)) :=
    hC₂.prod (t.isCompact_biUnion fun c _ => (hslice c).2)
  have hzero : ∀ c ∉ Prod.snd '' tsupport φ', ∀ u, T c u = 0 := by
    intro c hc u
    have h0 : ∀ b, φ' (b, c) = 0 := fun b => image_eq_zero_of_notMem_tsupport (fun h => hc ⟨(b, c), h, rfl⟩)
    simp [hTdef, Et.tilde, h0]
  have hsupp : Function.support (fun p : A.K × A.K => T p.1 p.2) ⊆
      (Prod.snd '' tsupport φ') ×ˢ ⋃ c ∈ t, tsupport (fun u => T c u) := by
    rintro ⟨c, u⟩ hp
    have hc : c ∈ Prod.snd '' tsupport φ' := by
      by_contra hc; exact hp (hzero c hc u)
    refine ⟨hc, ?_⟩
    obtain ⟨c', hc't, hcc'⟩ := Set.mem_iUnion₂.mp (hcover hc)
    refine Set.mem_iUnion₂.mpr ⟨c', hc't, subset_tsupport _ ?_⟩
    show T c' u ≠ 0
    rw [← hshift c' c hcc' u]; exact hp
  have hclosed : IsClosed (Function.support (fun p : A.K × A.K => T p.1 p.2)) := by
    have := (hlc.isOpen_fiber 0).isClosed_compl
    convert this using 1
    ext p; simp [Function.mem_support]
  have hts : tsupport (fun p : A.K × A.K => T p.1 p.2) = Function.support (fun p : A.K × A.K => T p.1 p.2) :=
    hclosed.closure_eq
  unfold HasCompactSupport
  rw [hts]
  exact hK.of_isClosed_subset hclosed hsupp
end GlobalTheory.JR.TildeTest
