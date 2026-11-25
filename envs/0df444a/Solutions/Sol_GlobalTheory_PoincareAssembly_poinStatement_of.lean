-- Prove2me | solution 1 for GlobalTheory.PoincareAssembly.poinStatement_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:11:20.071633+00:00
-- url     : https://prove2.me/submissions/e610a1f4-38a1-4e8c-919e-1c30aa7c42aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PoinStatementOf
import Theorems.Thm_GlobalTheory_PoincareAssembly_norm_chi
import Theorems.Thm_GlobalTheory_PoincareAssembly_cpt_lact
import Theorems.Thm_GlobalTheory_PoincareAssembly_dom_of_lact
import Theorems.Thm_GlobalTheory_PoincareAssembly_isOrth_lact
import Theorems.Thm_GlobalTheory_PoincareAssembly_phla_lact
import Theorems.Thm_GlobalTheory_PoincareAssembly_poin_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.PoincareAssembly
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PoincareAssembly
theorem _root_.solution :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ bb : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x, IsOrth X x → ENNReal.ofReal ‖P x‖ ≤ ENNReal.ofReal (C * Real.sqrt (κ x)) * ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom), (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ‖P (cpt X x z)‖ ≤ C * Real.sqrt (κ x)) → (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (κ : Frame X.Ψ r → ℝ) (P : Frame X.Ψ r → ℂ), IsBEq X la P → (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) → (∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ‖P (cpt X x z)‖ ≤ C * Real.sqrt (κ x)) → (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) ∧ X.IsBddSec la (poin X la P)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) → ∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)) → (PoinStatement (E := E)) := by
  intro hκ hball hloc hbdd hFF r X x0 ho hPD la W bb hW hWl hbb F P _ hF hP hPF
  obtain ⟨κ, hκ⟩ := hκ r X x0 ho hPD bb hbb
  obtain ⟨hs, hb⟩ := hbdd r X la κ P hP hκ.2.2.2.2.1
    (hloc r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF)
  refine ⟨hs, hb, hFF r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF hs, fun ρ hρ hρ1 => ?_,
    fun la' g hg x hx => poin_mul X la la' P g hg hx⟩
  obtain ⟨C, hC⟩ := hball r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF ρ hρ hρ1
  obtain ⟨K, hK, hKs⟩ := hκ.2.2.2.2.1
  refine ⟨C * K.toReal, fun x hx hxo => ?_⟩
  set S : ℝ≥0∞ := ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
    (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ) with hS
  have hterm : ∀ γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ₑ ≤
      ENNReal.ofReal C * S * ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) := by
    intro γ
    rw [← ofReal_norm, norm_mul, norm_inv, norm_chi X la γ.2, inv_one, one_mul]
    refine (hC _ (isOrth_lact X γ.2 hxo)).trans ?_
    rw [ENNReal.ofReal_mul' (Real.sqrt_nonneg _), mul_right_comm]
    gcongr
    refine iSup_le fun z => iSup_le fun hz => iSup_le fun hd => ?_
    rw [cpt_lact] at hd ⊢
    have hd' := dom_of_lact X γ.2 hd
    rw [phla_lact X la γ.2, hW.2.2 γ.1 γ.2 _ hd']
    exact le_iSup_of_le z (le_iSup_of_le hz (le_iSup_of_le hd' le_rfl))
  calc ENNReal.ofReal ‖poin X la P x‖
      = ‖∑' γ : X.Γ, (X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ₑ := ofReal_norm _
    _ ≤ ∑' γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ₑ := enorm_tsum_le_tsum_enorm
    _ ≤ ∑' γ : X.Γ, ENNReal.ofReal C * S * ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) :=
        ENNReal.tsum_le_tsum hterm
    _ ≤ ENNReal.ofReal C * S * K := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact hKs x hx
    _ = ENNReal.ofReal (C * K.toReal) * S := by
        rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK.ne, mul_right_comm]
end GlobalTheory.PoincareAssembly
