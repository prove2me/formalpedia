-- Prove2me | solution 1 for GlobalTheory.LastSteps.datumHat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:53:27.707899+00:00
-- url     : https://prove2.me/submissions/af975851-9895-4a28-9b76-71e0b01cbff3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_inDual_of_lifts
import Theorems.Thm_GlobalTheory_LastSteps_lifts_unique
import Theorems.Thm_GlobalTheory_LastSteps_exists_lifts
import Theorems.Thm_GlobalTheory_LastSteps_cosetInd_eq
import Theorems.Thm_GlobalTheory_LastSteps_integrable_qLat
import Theorems.Thm_GlobalTheory_LastSteps_integral_qLat
import Theorems.Thm_GlobalTheory_LatPair_hasConductor_mulShift
import Theorems.Thm_GlobalTheory_LatPair_resChar_residue
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData
noncomputable section
open GlobalTheory GlobalTheory.LastSteps
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type}
variable [Fintype n]
variable [MeasurableSpace k] [BorelSpace k] (q : Unif k) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
  (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
include hψ
variable [Fintype n'] (ε : 𝒪[k]ˣ) (P : Pair k n') (x₀ : Matrix n n' k) (η : n → k)
namespace GlobalTheory.LastSteps
theorem _root_.solution :
    Integrable (fun y => datum q P L x₀ y * (ψ (((ε : 𝒪[k]) : k) * (η ⬝ᵥ y)) : ℂ)) μ ∧
      datumHat ψ ε μ q P L x₀ η = (volQ μ q L : ℂ) * ∑ᶠ fW : Module.Dual 𝓀[k] (Red L),
        term q (resChar ψ hψ q) (resUnit ε) P L fW x₀ * cosetInd q L fW η := by
  classical
  haveI := secondCountable k
  by_cases h : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ L
  swap
  · have : ∀ y, datum q P L x₀ y = 0 := fun y => if_neg fun h' => h h'.1
    simp [datumHat, this, term, dif_neg h]
  have hψ' := hasConductor_mulShift hψ ε
  set w := x₀ *ᵥ (q.1 • P.vec) with hw
  have hF : ∀ y, datum q P L x₀ y * (ψ (((ε : 𝒪[k]) : k) * (η ⬝ᵥ y)) : ℂ) =
      (ψ (-(((ε : 𝒪[k]) : k) * (η ⬝ᵥ w))) : ℂ) * ((if q.inv • (y + w) ∈ L then (1 : ℂ) else 0) *
        (ψ.mulShift ((ε : 𝒪[k]) : k) (η ⬝ᵥ (y + w)) : ℂ)) := fun y => by
    have h1 : q.inv • (y + w) = q.inv • y + x₀ *ᵥ P.vec := by
      rw [smul_add, hw, ← mulVec_smul, q.inv_smul_smul]
    rw [mul_left_comm, ← Circle.coe_mul, AddChar.mulShift_apply, ← AddChar.map_add_eq_mul, dotProduct_add, mul_add,
      neg_add_cancel_comm_assoc, h1, datum]
    congr 1
    exact if_congr (and_iff_right h) rfl rfl
  refine ⟨?_, ?_⟩
  · simp only [hF]
    exact ((integrable_qLat q hψ' μ L η).comp_add_right w).const_mul _
  simp only [datumHat, hF]
  rw [integral_const_mul, integral_add_right_eq_self (μ := μ) (fun y => (if q.inv • y ∈ L then (1 : ℂ) else 0) *
    (ψ.mulShift ((ε : 𝒪[k]) : k) (η ⬝ᵥ y) : ℂ)) w, integral_qLat q hψ']
  simp only [cosetInd_eq]
  split_ifs with hD
  · obtain ⟨f, hf⟩ := exists_lifts hD
    rw [finsum_eq_single _ f fun g hg => by rw [if_neg fun h' => hg (lifts_unique h' hf), mul_zero],
      if_pos hf, mul_one, mul_comm, term, dif_pos h]
    obtain ⟨s, hs, e⟩ := hf ⟨w, h _ (Pair.smul_mem_ker q.mem_max P.hasVal_vec.mem)⟩
    have e' : -(((resUnit ε : 𝓀[k]ˣ) : 𝓀[k]) * residue 𝒪[k] s) = residue 𝒪[k] (-(ε * s)) := by simp [resUnit]
    have hs' : (s : k) = (q.1 : k) * (η ⬝ᵥ w) := by rw [hs, smul_dotProduct]; rfl
    rw [← e, e', resChar_residue]
    congr 3
    push_cast
    rw [hs', Unif.inv]
    field_simp [q.ne_zero]
  · simp [show ∀ f, ¬ Lifts L (q.1 • η) f from fun f hf => hD (inDual_of_lifts hf)]
end GlobalTheory.LastSteps
