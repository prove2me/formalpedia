-- Prove2me | solution 1 for GlobalTheory.exists_isLUB_height_rpow_lowerSemicontinuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:54:51.934844+00:00
-- url     : https://prove2.me/submissions/514c87e2-67ab-4a66-b9db-76c7095db235

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatticeHeightContinuousOnFramesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightAtFrameStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIsLUBHeightRpowLowerSemicontinuousOn
import Theorems.Thm_GlobalTheory_exists_submodule_finrank_eq_of_le
import Theorems.Thm_GlobalTheory_T_exists_pos_le_latticeHeight_at_frame
import Theorems.Thm_GlobalTheory_T_latticeHeight_continuousOn_frames


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ δ : ℝ, 0 < δ → ∃ α : ℕ → Frame X.Ψ r → ℝ, (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) ∧ ∀ i ≤ r, LowerSemicontinuousOn (α i) {x : Frame X.Ψ r | (∀ τ : X.Ψ, (mat x τ).det ≠ 0)}) := by
  intro r X d hd δ hδ
  set s := {x : Frame X.Ψ r | ∀ τ : X.Ψ, (mat x τ).det ≠ 0} with hs

  have hbdd : ∀ x ∈ s, ∀ i : ℕ, BddAbove ((fun W => d x W ^ (-δ)) ''
      {W : Submodule E (Fin r → E) | Module.finrank E W = i}) := by
    intro x hx i
    obtain ⟨m, hm, hmW⟩ := GlobalTheory.T.exists_pos_le_latticeHeight_at_frame r X d hd x hx
    refine ⟨m ^ (-δ), ?_⟩
    rintro _ ⟨W, -, rfl⟩
    exact Real.rpow_le_rpow_of_nonpos hm (hmW W) (by linarith)
  refine ⟨fun i x => sSup ((fun W => d x W ^ (-δ)) ''
      {W : Submodule E (Fin r → E) | Module.finrank E W = i}), ?_, ?_⟩
  · intro i hi x hx
    obtain ⟨W, hW⟩ := exists_submodule_finrank_eq_of_le (K := E) hi
    exact isLUB_csSup (Set.Nonempty.image _ (⟨W, hW⟩ : Set.Nonempty {W : Submodule E (Fin r → E) | Module.finrank E W = i})) (hbdd x hx i)
  ·
    intro i hi x hx y hy
    obtain ⟨W, hW⟩ := exists_submodule_finrank_eq_of_le (K := E) hi
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV⟩ := exists_lt_of_lt_csSup (Set.Nonempty.image _ (⟨W, hW⟩ : Set.Nonempty {W : Submodule E (Fin r → E) | Module.finrank E W = i})) hy
    have hpos : ∀ x' ∈ s, 0 < d x' V := fun x' hx' => by
      obtain ⟨m, hm, hmW⟩ := GlobalTheory.T.exists_pos_le_latticeHeight_at_frame r X d hd x' hx'
      exact hm.trans_le (hmW V)
    have hcont : ContinuousOn (fun x' => d x' V ^ (-δ)) s :=
      (GlobalTheory.T.latticeHeight_continuousOn_frames r X d hd V).rpow_const fun x' hx' => Or.inl (hpos x' hx').ne'
    have hev : ∀ᶠ x' in 𝓝[s] x, y < d x' V ^ (-δ) := (hcont x hx).eventually (lt_mem_nhds hyV)
    filter_upwards [hev, self_mem_nhdsWithin] with x' h1 h2
    exact h1.trans_le (le_csSup (hbdd x' h2 i) ⟨V, hV, rfl⟩)
end GlobalTheory
