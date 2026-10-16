-- Prove2me | solution 1 for OAI.PermanentBorder.Polar.exists_normalizer_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:34:22.123035+00:00
-- url     : https://prove2.me/submissions/e3b3b5e8-3556-47ea-afb4-fa153136285d

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/RankTransfer.lean:L380-L399
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Polar.exists_normalizer_equiv. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars
import Definitions.Def_OAI_Algebra_Determinantal_RankTransfer

-- ---- from OAI.Algebra.Determinantal.RankTransfer ----
namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.Polar
open MvPolynomial Matrix PermanentBorder.SliceParameters

section Generic
variable {K τ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

end Generic
end PermanentBorder.Polar

namespace PermanentBorder.Polar
open MvPolynomial Matrix PermanentBorder.SliceParameters
open scoped Classical
variable {τ : Type*} [Fintype τ]

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open scoped Classical
variable {ι : Type*} [Fintype ι]

lemma coordinateSplit_none (l : Option ι → ℂ) (h : l none ≠ 0) (y : Option ι → ℂ) :
    coordinateSplit l h y none = ∑ j, l j * y j := rfl

lemma exists_normalizer_equiv (l : Option ι → ℂ) (hl : l ≠ 0) :
    ∃ e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ),
      ∀ y, e y none = ∑ j, l j * y j := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, l i ≠ 0 := by
    by_contra! h
    exact hl (funext h)
  let p := Equiv.swap none i
  let c : (Option ι → ℂ) ≃ₗ[ℂ] (Option ι → ℂ) :=
    LinearEquiv.funCongrLeft ℂ ℂ p.symm
  have hc (y : Option ι → ℂ) (j : Option ι) : c y j = y (p j) := rfl
  let l' := fun j => l (p j)
  have hl' : l' none ≠ 0 := by simpa [l',p] using hi
  let e := c.trans (coordinateSplit l' hl')
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  intro y
  change (coordinateSplit l' hl' (c y)) none = _
  rw [coordinateSplit_none]
  change (∑ j, l (p j) * y (p j)) = _
  exact Equiv.sum_comp p (fun j => l j * y j)

end PermanentBorder.Polar

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Polar
open scoped Classical


theorem solution : type_of% @_root_.OAI.PermanentBorder.Polar.exists_normalizer_equiv := @_root_.OAI.PermanentBorder.Polar.exists_normalizer_equiv
