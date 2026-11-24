-- Prove2me | solution 1 for GlobalTheory.LastSteps.lift_mainDatum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:14:45.141803+00:00
-- url     : https://prove2.me/submissions/82686856-4486-4ae8-aecc-a0f6b8da529a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_card_withKer
import Theorems.Thm_GlobalTheory_LastSteps_mainDatum_eq
import Theorems.Thm_GlobalTheory_LastSteps_dia_FFStar
import Theorems.Thm_GlobalTheory_LatPair_cross_smul
import Theorems.Thm_GlobalTheory_LatPair_phiOne_mem_SB
import Theorems.Thm_GlobalTheory_LatPair_phiOne_smul
import Theorems.Thm_GlobalTheory_LatPair_sum_withKer_smul
import Theorems.Thm_GlobalTheory_LatPair_sum_withLat_smul


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
variable [Fintype n'] {L : Submodule 𝒪[k] (n' → k)} {LY : Submodule 𝒪[k] (n → k)} {x₀ : Matrix n n' k}
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (P : Pair k n')
variable [LY.IsLattice k] (fW : {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0})
variable {M A : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup A] [Module ℂ A]
variable [DecidableEq n'] [Fintype n]
variable {π : Representation ℂ (GL n' k) M} {θ : M →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] A} {φ : Form k n' M}
namespace GlobalTheory.LastSteps
theorem _root_.solution {L : Submodule 𝒪[k] (n' → k)} [L.IsLattice k] (he : φ ∈ EqForm π) (hθ : IsLiftInv π θ L)
    (Q : Pair k n) {P P' : Pair k n'} (hP : P.ker = L) (hP' : P'.lat = L) :
    θ (φ P) (mainDatum q χ ε P Q) = θ (dia ε (FFStar q χ φ) P') (phiOne P' Q) := by
  classical
  let T : Pair k n' → Pair k n' → A := fun P₁ P₂ => χ (-((ε : 𝓀[k]) * cross q P₁ P₂)) • θ (φ P₁) (phiOne P₂ Q)
  have hT : ∀ g : GL n' k, g • L = L → ∀ P₁ P₂, P₁.ker = L → P₂.lat = L → T (g • P₁) (g • P₂) = T P₁ P₂ := by
    intro g hg P₁ P₂ h₁ h₂
    have h3 : phiOne (g • P₂) Q = fun x => phiOne P₂ Q (x * g.val) := funext fun x => by
      simpa using phiOne_smul (P := P₂) (Q := Q) (x := x) g 1
    simp only [T]
    rw [cross_smul q (h₂.trans h₁.symm), he g P₁, h3, hθ g hg _ _ (phiOne_mem_SB P₂ Q)]
  have h1 : ∀ P₁ ∈ withKer L, ∑ P₂ ∈ withLat L, T P₁ P₂ = ∑ P₂ ∈ withLat L, T P P₂ := fun P₁ h => by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n' k) P P₁
    have hg : g • L = L := by simpa [hP] using h
    conv_lhs => rw [← hg, sum_withLat_smul]
    exact Finset.sum_congr rfl fun P₂ h₂ => hT g hg _ _ hP (mem_withLat.1 h₂)
  have h2 : ∀ P₂ ∈ withLat L, ∑ P₁ ∈ withKer L, T P₁ P₂ = ∑ P₁ ∈ withKer L, T P₁ P' := fun P₂ h => by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n' k) P' P₂
    have hg : g • L = L := by simpa [hP'] using h
    conv_lhs => rw [← hg, sum_withKer_smul]
    exact Finset.sum_congr rfl fun P₁ h₁ => hT g hg _ _ (mem_withKer.1 h₁) hP'
  have h3 := Finset.sum_comm (s := withKer L) (t := withLat L) (f := T)
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const, card_withKer,
    ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h3
  have h4 : ((withLat L).card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨P', mem_withLat.2 hP'⟩).ne'
  have h5 := smul_right_injective A h4 h3
  rw [mainDatum_eq, dia_FFStar, hP, hP']
  simpa only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply] using h5
end GlobalTheory.LastSteps
