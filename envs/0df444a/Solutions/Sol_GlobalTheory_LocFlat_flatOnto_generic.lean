-- Prove2me | solution 1 for GlobalTheory.LocFlat.flatOnto_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:42:19.956797+00:00
-- url     : https://prove2.me/submissions/95b03f28-c52d-4d33-b17f-b7de3fcda758

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Theorems.Thm_GlobalTheory_LocFlat_flatSB_isLocallyConstant_indicator
import Theorems.Thm_GlobalTheory_LocFlat_ch_affPt_zero_eq
import Theorems.Thm_GlobalTheory_LocFlat_continuous_freeMat
import Theorems.Thm_GlobalTheory_LocFlat_isClosedEmbedding_freeMat
import Theorems.Thm_GlobalTheory_LocFlat_exists_clopen_ch_near
import Theorems.Thm_GlobalTheory_RootEx_continuous_affPt_uncurry
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_IntM_neg
import Theorems.Thm_GlobalTheory_StepData_MaxM_neg
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_isCompact
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_isOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
open Filter Topology
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open Classical
namespace GlobalTheory.LocFlat
theorem _root_.solution {X : Type} [TopologicalSpace X] [T2Space X] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (ν : Measure k) (hν : ν.IsAddHaarMeasure) (p : ℕ)
    (A : X → ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (R : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → X) (hR : Continuous R)
    (Q : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (hQ : Continuous Q)
    (G : X × Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (hG : Continuous G)
    (hGRQ : ∀ z, G (R z, Q z) = z)
    (hRA : ∀ x e, R (A x e) = x) (hQA : ∀ x e, Q (A x e) = freeMat p e)
    (Ψ : X → ℂ) (hΨ : Ψ ∈ SB X) :
    ∃ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x,
      ∫ e, Φ (A x e) * (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ) ∂(Measure.pi fun _ => ν) = Ψ x := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := hν
  obtain ⟨W, hWcl, hWc, hW0, hWψ⟩ := exists_clopen_ch_near (n := n) (n' := n') (c := c) ψ hψ
  set μ : Measure ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) := Measure.pi fun _ => ν
  set f : ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → ℂ :=
    fun e => (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ) with hf
  set K := freeMat (k := k) (n := n) (n' := n') (c := c) p ⁻¹' W with hK
  set I : ℂ := ∫ e, W.indicator (fun _ => (1 : ℂ)) (freeMat p e) * f e ∂μ with hI
  have hfc : Continuous f := by
    refine continuous_subtype_val.comp (hψ.comp (Continuous.neg ?_))
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_affPt_uncurry p).comp (Continuous.prodMk_right (0 : Matrix n n' k))).matrix_elem _ _
  have hKo : IsOpen K := hWcl.isOpen.preimage (continuous_freeMat p)
  have hKc : IsCompact K := (isClosedEmbedding_freeMat p).isCompact_preimage hWc
  have hK0 : (0 : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) ∈ K := by
    show freeMat p 0 ∈ W
    convert hW0 using 1
    ext r s; simp [freeMat]
  have hμK : 0 < μ.real K := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hKo.measure_pos μ ⟨0, hK0⟩).ne' hKc.measure_lt_top.ne
  have hIK : I = ∫ e in K, f e ∂μ := by
    rw [hI, ← integral_indicator hKo.measurableSet]
    congr 1; funext e
    by_cases he : e ∈ K
    · have : freeMat p e ∈ W := he
      simp [Set.indicator_of_mem he, Set.indicator_of_mem this]
    · have : freeMat p e ∉ W := he
      simp [Set.indicator_of_notMem he, Set.indicator_of_notMem this]
  have hInt : IntegrableOn f K μ := hfc.continuousOn.integrableOn_compact hKc
  have hI0 : I ≠ 0 := by
    intro h0
    have hb : ‖∫ e in K, (f e - 1) ∂μ‖ ≤ 1 / 2 * μ.real K := by
      refine norm_setIntegral_le_of_norm_le_const hKc.measure_lt_top fun e he => ?_
      have := hWψ _ he
      rw [← ch_affPt_zero_eq] at this
      exact this.le
    rw [integral_sub hInt (integrableOn_const hKc.measure_lt_top.ne), ← hIK, h0, setIntegral_const] at hb
    simp only [zero_sub, norm_neg, Complex.real_smul, mul_one] at hb
    rw [Complex.norm_real, Real.norm_of_nonneg hμK.le] at hb
    linarith
  refine ⟨fun z => I⁻¹ * (Ψ (R z) * W.indicator (fun _ => (1 : ℂ)) (Q z)), ?_, fun x => ?_⟩
  · have hH : (fun q : X × Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k =>
        Ψ q.1 * W.indicator (fun _ => (1 : ℂ)) q.2) ∈ SB _ := by
      refine ⟨(hΨ.1.comp_continuous continuous_fst).mul
        ((flatSB_isLocallyConstant_indicator hWcl 1).comp_continuous continuous_snd), ?_⟩
      refine HasCompactSupport.intro (hΨ.2.isCompact.prod hWc) fun q hq => ?_
      by_cases h1 : q.1 ∈ tsupport Ψ
      · have h2 : q.2 ∉ W := fun h2 => hq ⟨h1, h2⟩
        simp [Set.indicator_of_notMem h2]
      · simp [image_eq_zero_of_notMem_tsupport h1]
    have hemb : Topology.IsClosedEmbedding fun z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => (R z, Q z) :=
      Function.LeftInverse.isClosedEmbedding (f := G) hGRQ hG (hR.prodMk hQ)
    exact ⟨(IsLocallyConstant.const I⁻¹).mul (hH.1.comp_continuous (hR.prodMk hQ)),
      (hH.2.comp_isClosedEmbedding hemb).mul_left⟩
  · have : ∀ e, I⁻¹ * (Ψ (R (A x e)) * W.indicator (fun _ => (1 : ℂ)) (Q (A x e))) * f e =
        (I⁻¹ * Ψ x) * (W.indicator (fun _ => (1 : ℂ)) (freeMat p e) * f e) := by
      intro e; rw [hRA, hQA]; ring
    simp only [hf] at this
    rw [integral_congr_ae (Eventually.of_forall this), integral_const_mul, ← hI]
    field_simp
end GlobalTheory.LocFlat
