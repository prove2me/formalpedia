-- Prove2me | solution 1 for GlobalTheory.UnitaryFrames.unitary_group_frames
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:20.743093+00:00
-- url     : https://prove2.me/submissions/22ba5f48-dc89-4b2a-bbe2-ad63e4c03e4c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Theorems.Thm_GlobalTheory_UnitaryFrames_isClosed_unitary
import Theorems.Thm_GlobalTheory_UnitaryFrames_locallyCompact_GL
import Theorems.Thm_GlobalTheory_UnitaryFrames_secondCountable_GL
import Theorems.Thm_GlobalTheory_UnitaryFrames_isOrth_lmulC
import Theorems.Thm_GlobalTheory_UnitaryFrames_val_toGL
import Theorems.Thm_GlobalTheory_UnitaryFrames_quotient_unitary
import Theorems.Thm_GlobalTheory_UnitaryFrames_continuous_toGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate
open GlobalTheory GlobalTheory.UnitaryFrames
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.UnitaryFrames
theorem _root_.solution :
    ((∀ (r : ℕ) (X : Data E r), ∃ H : Subgroup (X.Ψ → GL (Fin r) ℂ), ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) ∧ (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → LocallyCompactSpace H ∧ SecondCountableTopology H ∧ ∀ x0, IsOrth X x0 → (∀ g : H, IsOrth X (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) ∧ ∃ ι : Frame X.Ψ r → H, ContinuousOn ι {x | IsOrth X x} ∧ (∀ x, IsOrth X x → X.lmulC (fun τ => ((ι x : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 = x) ∧ ∀ g : H, ι (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = g)) := by
  classical
  refine ⟨fun r X => ⟨unitarySubgroup X, fun g => Iff.rfl⟩, fun r X H hH => ?_⟩
  haveI := locallyCompact_GL r
  haveI := secondCountable_GL r
  have hcl : IsClosed (H : Set (X.Ψ → GL (Fin r) ℂ)) := by
    convert isClosed_unitary X using 1
    ext g
    exact hH g
  refine ⟨hcl.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology, fun x0 hx0 => ?_⟩
  have horth : ∀ g : H, IsOrth X (X.lmulC
      (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) :=
    fun g => isOrth_lmulC X ((hH _).1 g.2) hx0
  refine ⟨horth, fun x => if hx : IsOrth X x then
    ⟨toGL X hx * (toGL X hx0)⁻¹, (hH _).2 (quotient_unitary X hx hx0)⟩ else 1, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    refine continuous_induced_rng.2 ?_
    refine ((continuous_toGL X).mul (continuous_const (y := (toGL X hx0)⁻¹))).congr fun x => ?_
    have hx : IsOrth X x.1 := x.2
    simp only [Function.comp_apply, Set.restrict_apply, dif_pos hx]
    rfl
  · intro x hx
    simp only [dif_pos hx]
    funext τ
    change (((toGL X hx τ * (toGL X hx0 τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
      (toGL X hx0 τ : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = mat x τ
    rw [← Units.val_mul, inv_mul_cancel_right, val_toGL]
  · intro g
    simp only [dif_pos (horth g)]
    apply Subtype.ext
    change toGL X (horth g) * (toGL X hx0)⁻¹ = g
    rw [mul_inv_eq_iff_eq_mul]
    funext τ
    exact Units.ext rfl
end GlobalTheory.UnitaryFrames
