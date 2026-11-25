-- Prove2me | solution 1 for Newton.hasCompactSupport_scaledMollifier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:01:24.369685+00:00
-- url     : https://prove2.me/submissions/aab272e9-672a-4c9b-8083-4beb82305f3a

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity

set_option autoImplicit false
open MeasureTheory Complex NNReal SchwartzMap
open scoped ENNReal ContDiff Topology Pointwise
open Newton
variable {n : ℕ}
variable {ψ : (Fin n → ℝ) → ℝ}
namespace Newton
theorem _root_.solution
    (hψ : HasCompactSupport ψ) {η : ℝ} (hη_pos : 0 < η) :
    HasCompactSupport (scaledMollifier ψ η) := by
  -- Define the scaling maps s and its inverse image description on sets.
  set s : (Fin n → ℝ) → (Fin n → ℝ) := fun x => fun i => x i / η with hs_def
  have hs_eq_smul : s = fun x : (Fin n → ℝ) => (η⁻¹ : ℝ) • x := by
    funext x i; simp [s, div_eq_mul_inv, mul_comm]
  have hs_cont : Continuous s := by
    simpa [hs_eq_smul] using (continuous_const_smul (η⁻¹ : ℝ))
  -- Support inclusion: support(scaledMollifier) ⊆ preimage of tsupport ψ under s.
  have h_support_subset :
      Function.support (scaledMollifier ψ η)
        ⊆ s ⁻¹' tsupport ψ := by
    intro x hx
    -- If the scaled mollifier is nonzero at x, then ψ (s x) ≠ 0.
    have hx_ne : scaledMollifier ψ η x ≠ 0 := hx
    have hψ_ne : ψ (s x) ≠ 0 := by
      -- If ψ (s x) = 0 then the product is 0, contradiction.
      intro hzero
      have : scaledMollifier ψ η x = 0 := by
        simp [scaledMollifier, hzero, s]
      exact hx_ne this
    -- Hence s x ∈ support ψ ⊆ tsupport ψ.
    have : s x ∈ Function.support ψ := by simpa [Function.support] using hψ_ne
    have : s x ∈ tsupport ψ := subset_tsupport _ this
    simpa [Set.mem_preimage]
      using this
  -- `tsupport` is the closure of `support`; close the inclusion using closedness.
  have h_tsupport_subset :
      tsupport (scaledMollifier ψ η) ⊆ s ⁻¹' tsupport ψ := by
    -- Preimage of a closed set under a continuous map is closed.
    have h_closed : IsClosed (s ⁻¹' tsupport ψ) :=
      (isClosed_tsupport ψ).preimage hs_cont
    -- Use the minimality of closure with respect to closed supersets.
    simpa [tsupport, Function.support]
      using closure_minimal h_support_subset h_closed
  -- Identify the preimage as the image of tsupport ψ under scaling by η.
  have h_preimage_eq :
      s ⁻¹' tsupport ψ
        = (fun z : (Fin n → ℝ) => η • z) '' tsupport ψ := by
    -- Preimage under s = image under its inverse (scaling by η).
    ext x; constructor
    · intro hx
      refine ⟨s x, ?_, ?_⟩
      · simpa [Set.mem_preimage] using hx
      · have hη_ne : (η : ℝ) ≠ 0 := ne_of_gt hη_pos
        simp [hs_eq_smul, smul_smul, hη_ne]
    · intro hx
      rcases hx with ⟨z, hz, rfl⟩
      -- s (η • z) = z ∈ tsupport ψ
      have hη_ne : (η : ℝ) ≠ 0 := ne_of_gt hη_pos
      simpa [hs_eq_smul, smul_smul, hη_ne] using hz
  -- The right-hand side is compact as an image of a compact set under a continuous map.
  have h_image_compact :
      IsCompact ((fun z : (Fin n → ℝ) => η • z) '' tsupport ψ) := by
    have h_compact_tsupport : IsCompact (tsupport ψ) := hψ
    have h_cont_scale : Continuous fun z : (Fin n → ℝ) => η • z :=
      continuous_const_smul η
    exact h_compact_tsupport.image h_cont_scale
  have h_compact : IsCompact (tsupport (scaledMollifier ψ η)) := by
    have : tsupport (scaledMollifier ψ η)
        ⊆ (fun z : (Fin n → ℝ) => η • z) '' tsupport ψ := by
      simpa [h_preimage_eq] using h_tsupport_subset
    exact IsCompact.of_isClosed_subset h_image_compact (isClosed_tsupport _) this
  simpa [HasCompactSupport] using h_compact
end Newton
