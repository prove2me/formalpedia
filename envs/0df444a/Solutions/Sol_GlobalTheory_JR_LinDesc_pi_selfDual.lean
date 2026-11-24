-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.pi_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:31:57.88287+00:00
-- url     : https://prove2.me/submissions/836f7520-3074-48fd-af0a-cffac50ef05b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierGlOrbitEqFourierEtaleKProd
import Theorems.Thm_GlobalTheory_T_selfDual_iff_lattice_volume_and_plancherel_alt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
namespace GlobalTheory.JR.LinDesc
theorem _root_.solution (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] [MeasurableSpace F] [BorelSpace F] (μF : Measure F) [μF.IsAddHaarMeasure]
    (hvol : μF (Metric.closedBall 0 1) = 1) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (r : ℕ) :
    SelfDual (Measure.pi fun _ : Fin r => μF) (fun x y => ψ (x ⬝ᵥ y)) ∧
      IsTest ((Set.univ.pi fun _ : Fin r => Metric.closedBall (0 : F) 1).indicator 1) := by
  haveI := hU.ultraF
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology F := secondCountable_of_proper
  set S : Set (Fin r → F) := Set.univ.pi fun _ => Metric.closedBall 0 1 with hSdef
  have hmem : ∀ y : Fin r → F, y ∈ S ↔ ∀ i, ‖y i‖ ≤ 1 := by
    intro y; simp [S, Set.mem_pi, Metric.mem_closedBall, dist_zero_right]
  have hSo : IsOpen S :=
    isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall 0 one_ne_zero
  have hSc : IsCompact S := isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hScl : IsClosed S := isClosed_set_pi fun _ _ => Metric.isClosed_closedBall
  let Mg : AddSubgroup (Fin r → F) :=
    { carrier := S
      zero_mem' := by rw [hmem]; simp
      add_mem' := by
        intro a b ha hb
        rw [hmem] at ha hb ⊢
        intro i; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
      neg_mem' := by
        intro a ha
        rw [hmem] at ha ⊢
        intro i; simpa using ha i }
  have hMg : (Mg : Set (Fin r → F)) = S := rfl
  let β : LinearMap.BilinForm F (Fin r → F) := Matrix.toBilin' 1
  have hβ : ∀ x y, β x y = x ⬝ᵥ y := by intro x y; simp [β, Matrix.toBilin'_apply']
  have hβs : β.IsSymm := by
    first
    | exact ⟨fun x y => by simp [hβ, dotProduct_comm]⟩
    | exact fun x y => by simp [hβ, dotProduct_comm]
  have hβn : β.Nondegenerate := Matrix.Nondegenerate.toBilin' (Matrix.nondegenerate_of_det_ne_zero (by simp))
  have key := (GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → F) β hβs hβn (Measure.pi fun _ => μF) inferInstance).1 Mg
    (by rw [hMg]; exact hSo) (by rw [hMg]; exact hSc)
  have hdual : {y | ∀ x ∈ Mg, ψ (β x y) = 1} = S := by
    ext y
    simp only [Set.mem_setOf_eq, hβ]
    constructor
    · intro h
      rw [hmem]
      intro i
      by_contra hi
      push_neg at hi
      obtain ⟨x0, hx0, hx0'⟩ := hψ.2
      have hyi : y i ≠ 0 := by intro h0; rw [h0, norm_zero] at hi; linarith
      have hsmall : ‖(y i)⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hi
      have hx : Pi.single i (x0 * (y i)⁻¹) ∈ Mg := by
        show _ ∈ S
        rw [hmem]
        intro j
        by_cases hj : j = i
        · subst hj; simp only [Pi.single_eq_same]; exact hx0' _ hsmall
        · simp [Pi.single_eq_of_ne hj]
      have h2 := h _ hx
      have e : Pi.single i (x0 * (y i)⁻¹) ⬝ᵥ y = x0 := by
        simp only [dotProduct, Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [mul_assoc, inv_mul_cancel₀ hyi, mul_one]
      rw [e] at h2
      exact hx0 h2
    · intro hy x hx
      have hx' : x ∈ S := hx
      rw [hmem] at hy hx'
      apply hψ.1
      simp only [dotProduct]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
      rw [norm_mul]; exact mul_le_one₀ (hx' i) (norm_nonneg _) (hy i)
  have hvolS : (Measure.pi fun _ : Fin r => μF) S = 1 := by
    rw [hSdef, Measure.pi_pi]; simp [hvol]
  have hsd : SelfDual (Measure.pi fun _ : Fin r => μF) (fun x y => ψ (β x y)) :=
    key.1.2 (by rw [hdual, hMg, hvolS, one_mul])
  refine ⟨?_, ?_⟩
  · have e : (fun x y : Fin r → F => ψ (x ⬝ᵥ y)) = (fun x y => ψ (β x y)) := by funext x y; rw [hβ]
    rw [e]; exact hsd
  · exact ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hScl, hSo⟩).isLocallyConstant,
      HasCompactSupport.intro hSc fun x hx => Set.indicator_of_notMem hx _⟩
end GlobalTheory.JR.LinDesc
