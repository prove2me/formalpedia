-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:15.622845+00:00
-- url     : https://prove2.me/submissions/637e8e33-058e-42e7-a285-75f5a4e8b355

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaussIntegralOneMulGaussIntegralNegOneEqOne
import Theorems.Thm_GlobalTheory_JR_WeilQuad_GaussProd_trace_NL_add
import Theorems.Thm_GlobalTheory_JR_WeilQuad_GaussProd_continuous_trace_NL
import Theorems.Thm_GlobalTheory_JR_SelfDualLat_topo
import Theorems.Thm_GlobalTheory_JR_WeilQuad_FourierTest_beta_isSymm
import Theorems.Thm_GlobalTheory_JR_WeilQuad_FourierTest_beta_nondeg
import Theorems.Thm_GlobalTheory_JR_WeilQuad_FourierTest_cont_psi
import Theorems.Thm_GlobalTheory_JR_WeilQuad_FourierTest_finite_F_L
import Theorems.Thm_GlobalTheory_T_selfDual_iff_lattice_volume_and_plancherel_alt
import Theorems.Thm_GlobalTheory_T_unramifiedStandardAddChar_conductor_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory.JR.WeilQuad.FourierTest GlobalTheory.JR.WeilQuad.GaussProd
namespace GlobalTheory.JR.WeilQuad
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ)
    (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ Λ : AddSubgroup A.L, IsOpen (Λ : Set A.L) →
    IsCompact (Λ : Set A.L) → {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ Λ →
    (∀ y ∈ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1}, A.psiK ψ ((x : A.K) * A.NL y) = 1) →
    gaussInt A ψ x μ 1 Λ * gaussInt A ψ x μ (-1) Λ = 1 := by
  intro F E _ _ _ _ _ A ψ x μ ω h Λ hΛo hΛc hPS hQ
  obtain ⟨hK, hL, hψ, hsd, -⟩ := h
  haveI := hsd.1
  haveI := finite_F_L A
  obtain ⟨hLC, hSC, hT2, hTG⟩ := GlobalTheory.JR.SelfDualLat.topo F E A.L
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hTG
  have hψ' := (GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ
  have hψc : Continuous (fun t : F => ψ t) := cont_psi hψ
  set β := beta A (x : A.K) with hβdef
  have hβc : Continuous (fun p : A.L × A.L => β p.1 p.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left β
  set q : A.L → F := fun y => Algebra.trace F A.K ((x : A.K) * A.NL y) with hqdef
  have hqc : Continuous q := continuous_trace_NL A hK hL (x : A.K)
  have hqa : ∀ t u, q (t + u) = q t + q u + β t u := fun t u => trace_NL_add A hK hL (x : A.K) t u
  set S : Set A.L := (Λ : Set A.L) with hSdef
  set P : Set A.L := {y : A.L | ∀ w ∈ S, ψ (β w y) = 1} with hPdef
  have hSm : MeasurableSet S := hΛo.measurableSet
  have hPc : IsClosed P := by
    have : P = ⋂ w ∈ S, (fun y => ψ (β w y)) ⁻¹' {1} := by ext y; simp [hPdef]
    rw [this]
    exact isClosed_biInter fun w _ =>
      isClosed_singleton.preimage (hψc.comp (hβc.comp (continuous_const.prodMk continuous_id)))
  have hPm : MeasurableSet P := hPc.measurableSet
  have hI := GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.L β (beta_isSymm A hK hL (x : A.K)) (beta_nondeg A hK hL x) μ hsd.1
  have hvol : μ S * μ P = 1 := ((hI.1 Λ hΛo hΛc).1).1 hsd
  have horth : ∀ u, ∫ t in S, ψ (β t u) ∂μ = P.indicator (fun _ => ((μ S).toReal : ℂ)) u :=
    (hI.1 Λ hΛo hΛc).2
  have hPS' : P ⊆ S := hPS
  have hQ' : ∀ y ∈ P, ψ (q y) = 1 := hQ
  have hG1 : gaussInt A ψ x μ 1 Λ = ∫ y in S, ψ (q y) ∂μ := by
    unfold gaussInt
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ψ (Algebra.trace F A.K (1 * (x : A.K) * A.NL y)) = ψ (Algebra.trace F A.K ((x : A.K) * A.NL y))
    rw [one_mul]
  have hG2 : gaussInt A ψ x μ (-1) Λ = ∫ y in S, ψ (-q y) ∂μ := by
    unfold gaussInt
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ψ (Algebra.trace F A.K (-1 * (x : A.K) * A.NL y)) = ψ (-Algebra.trace F A.K ((x : A.K) * A.NL y))
    rw [neg_one_mul, neg_mul, map_neg]
  have hne : ∀ a : F, ψ (-a) * ψ a = 1 := by
    intro a; rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have htr : ∀ t ∈ S, (∫ u in S, ψ (q u) ∂μ) = ψ (q t) * ∫ u in S, ψ (q u) * ψ (β t u) ∂μ := by
    intro t ht
    rw [← integral_indicator hSm, ← integral_add_left_eq_self (S.indicator fun u => ψ (q u)) t,
      ← integral_const_mul, ← integral_indicator hSm]
    congr 1; ext u
    by_cases hu : u ∈ S
    · have htu : t + u ∈ S := Λ.add_mem ht hu
      rw [Set.indicator_of_mem htu, Set.indicator_of_mem hu, hqa, AddChar.map_add_eq_mul,
        AddChar.map_add_eq_mul]
      ring
    · have htu : t + u ∉ S := fun h' => hu (by
        have := Λ.sub_mem h' ht
        rwa [add_sub_cancel_left] at this)
      simp [Set.indicator_of_notMem htu, Set.indicator_of_notMem hu]
  haveI : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hΛc.measure_lt_top.ne
  have hint : Integrable (Function.uncurry fun t u => ψ (q u) * ψ (β t u))
      ((μ.restrict S).prod (μ.restrict S)) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
    · exact ((hψc.comp (hqc.comp continuous_snd)).mul (hψc.comp hβc)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry, norm_mul, hψ'.2.1, mul_one, le_refl]
  rw [hG1, hG2]
  calc (∫ y in S, ψ (q y) ∂μ) * ∫ y in S, ψ (-q y) ∂μ
      = ∫ t in S, (∫ y in S, ψ (q y) ∂μ) * ψ (-q t) ∂μ := (integral_const_mul _ _).symm
    _ = ∫ t in S, ∫ u in S, ψ (q u) * ψ (β t u) ∂μ ∂μ := by
        refine setIntegral_congr_fun hSm (fun t ht => ?_)
        rw [htr t ht, mul_comm, ← mul_assoc, hne, one_mul]
    _ = ∫ u in S, ∫ t in S, ψ (q u) * ψ (β t u) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ u in S, ψ (q u) * P.indicator (fun _ => ((μ S).toReal : ℂ)) u ∂μ := by
        congr 1; ext u
        rw [integral_const_mul, horth u]
    _ = ∫ u in S, P.indicator (fun _ => ((μ S).toReal : ℂ)) u ∂μ := by
        refine setIntegral_congr_fun hSm (fun u _ => ?_)
        by_cases hp : u ∈ P
        · simp only [Set.indicator_of_mem hp, hQ' u hp, one_mul]
        · simp only [Set.indicator_of_notMem hp, mul_zero]
    _ = (μ P).toReal * (μ S).toReal := by
        rw [setIntegral_indicator hPm, Set.inter_eq_right.2 hPS', setIntegral_const]
        simp [Measure.real]
    _ = 1 := by
        have h1 : (μ S).toReal * (μ P).toReal = 1 := by
          rw [← ENNReal.toReal_mul, hvol, ENNReal.toReal_one]
        rw [mul_comm]; exact_mod_cast h1
end GlobalTheory.JR.WeilQuad
