-- Prove2me | solution 1 for GlobalTheory.SecRatio.isUnit_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:05.19215+00:00
-- url     : https://prove2.me/submissions/1fb2d500-1188-49c7-ae17-25c13b79cdbc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueIsRatio
import Theorems.Thm_GlobalTheory_SecRatio_compat_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
namespace GlobalTheory.SecRatio
private theorem rr {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    resG X h₂ (resG X h₁ s) = resG X (h₂.trans h₁) s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl
variable {X : Scheme.{0}} {H : LB X}
end GlobalTheory.SecRatio
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.SecRatio
variable {X : Scheme.{0}} {H : LB X}
namespace GlobalTheory.SecRatio
theorem _root_.solution (t : H.Sec) (l : H.ι) {V : X.Opens} (hV : V ≤ Out.nonzeroLocus t)
    (hl : V ≤ H.U l) : IsUnit (resG X hl (t.f l)) := by
  have hle : V ≤ X.basicOpen (t.f l) := by
    intro x hx
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV hx)
    have hk' : x ∈ H.U k := X.basicOpen_le _ hk
    have h1 : x ∈ X.basicOpen (resG X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (t.f k)) := by
      erw [Scheme.basicOpen_res]
      exact ⟨⟨hk', hl hx⟩, hk⟩
    rw [compat_res t k l inf_le_left inf_le_right, Scheme.basicOpen_mul] at h1
    have h2 := h1.2
    erw [Scheme.basicOpen_res] at h2
    exact h2.2
  have hu : IsUnit (resG X (X.basicOpen_le (t.f l)) (t.f l)) :=
    X.toRingedSpace.isUnit_res_basicOpen (t.f l)
  have := hu.map (resG X hle)
  rwa [rr] at this
end GlobalTheory.SecRatio
