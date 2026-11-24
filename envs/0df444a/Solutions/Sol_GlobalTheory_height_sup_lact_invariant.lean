-- Prove2me | solution 1 for GlobalTheory.height_sup_lact_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:03:11.812223+00:00
-- url     : https://prove2.me/submissions/72888cee-f816-418c-9aa0-9dd3f34dcdec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_HeightSupInvariantUnderHermitianLatticeAut
import Theorems.Thm_GlobalTheory_HeightInv_height_lact


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
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (δ : ℝ) (α : ℕ → Frame X.Ψ r → ℝ), (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ i ≤ r, α i (lact γ x) = α i x) := by
  intro r X d hd δ α hα γ hγ x hx i hi
  obtain ⟨hx', hmap⟩ := HeightInv.height_lact r X d hd γ hγ x hx
  have hinj : ∀ g : GL (Fin r) E,
      Function.Injective (g : Matrix (Fin r) (Fin r) E).mulVecLin := by
    intro g v w hvw
    have h := congrArg (fun u => ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u) hvw
    simpa [Matrix.mulVec_mulVec] using h
  have hrank : ∀ (g : GL (Fin r) E) (W : Submodule E (Fin r → E)),
      Module.finrank E (W.map (g : Matrix (Fin r) (Fin r) E).mulVecLin) = Module.finrank E W :=
    fun g W => (Submodule.equivMapOfInjective _ (hinj g) W).finrank_eq.symm
  have hset : (fun W => d (lact γ x) W ^ (-δ)) '' {W | Module.finrank E W = i} =
      (fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i} := by
    ext y
    constructor
    · rintro ⟨W', hW', rfl⟩
      refine ⟨W'.map ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVecLin, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq] at hW' ⊢
        rw [hrank, hW']
      · have hback : (W'.map ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVecLin).map
            (γ : Matrix (Fin r) (Fin r) E).mulVecLin = W' := by
          rw [← Submodule.map_comp, ← Matrix.mulVecLin_mul, ← Units.val_mul, mul_inv_cancel,
            Units.val_one, Matrix.mulVecLin_one, Submodule.map_id]
        simp only
        rw [← hmap, hback]
    · rintro ⟨W, hW, rfl⟩
      refine ⟨W.map (γ : Matrix (Fin r) (Fin r) E).mulVecLin, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq] at hW ⊢
        rw [hrank, hW]
      · simp only
        rw [hmap]
  have h1 := hα i hi (lact γ x) hx'
  rw [hset] at h1
  exact h1.unique (hα i hi x hx)
end GlobalTheory
