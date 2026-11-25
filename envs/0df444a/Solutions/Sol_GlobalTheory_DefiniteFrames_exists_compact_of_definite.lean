-- Prove2me | solution 1 for GlobalTheory.DefiniteFrames.exists_compact_of_definite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:44:27.357696+00:00
-- url     : https://prove2.me/submissions/dcae85e4-a268-4a83-9229-523c1735e25d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsCompactOfDefinite
import Theorems.Thm_GlobalTheory_DefiniteFrames_isCompact_ortho
import Theorems.Thm_PIW_FdPA_det_ne_of_gram
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_bOf_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_lminor_diagonal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_ortho_bOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_sgn_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
namespace GlobalTheory.DefiniteFrames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma mem_dom_of_isOrtho' (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : X.IsOrtho x) :
    x ∈ X.dom := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsOrtho at hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG
  have hsgn : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a ≠ 0 := fun a => by
    rcases _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sgn_sq X.p0 a with h | h <;> simp [h]
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · apply _root_.PIW.FdPA.det_ne_of_gram (τ : E →+* ℂ) X.Gm
    rw [hx τ, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => by exact_mod_cast hsgn a
  · have hmin : _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i = ((_root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i : ℝ) : ℂ) := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn
      rw [hx τ, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_diagonal, Complex.ofReal_prod, ← Fin.prod_univ_eq_prod_range]
      simp
    have hne : _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i ≠ 0 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn
      exact Finset.prod_ne_zero_iff.mpr fun a _ => hsgn a
    rw [hmin, Complex.ofReal_re]
    exact mul_self_pos.mpr hne
end GlobalTheory.DefiniteFrames
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open GlobalTheory GlobalTheory.DefiniteFrames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.DefiniteFrames
namespace _root_.GlobalTheory.DefiniteFrames
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), (X.p0 = 0 ∨ r ≤ X.p0) → ∃ C : Set (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom, ∃ γ ∈ X.Γ, ∃ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r, _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) ∈ C := by
  intro E _ _ _ r X hp
  refine ⟨{x | X.IsOrtho x}, _root_.GlobalTheory.DefiniteFrames.isCompact_ortho X hp,
    fun x hx => mem_dom_of_isOrtho' X hx,
    fun x hx => ⟨1, X.Γ.one_mem, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx, ?_⟩⟩
  have h1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.lact (1 : GL (Fin r) E) (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.lact
    funext τ
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    rfl
  rw [h1]
  exact _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx
end _root_.GlobalTheory.DefiniteFrames
end GlobalTheory.DefiniteFrames
