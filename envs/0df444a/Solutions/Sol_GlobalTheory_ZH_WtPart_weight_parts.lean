-- Prove2me | solution 1 for GlobalTheory.ZH.WtPart.weight_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:47:47.16725+00:00
-- url     : https://prove2.me/submissions/d57f7eab-0980-438f-a6c9-c76ac3ec074f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Theorems.Thm_GlobalTheory_ZH_WtPart_isPart_partSec
import Theorems.Thm_GlobalTheory_ZH_WtPart_supp_finite
import Theorems.Thm_GlobalTheory_ZH_WtPart_sec_ext
import Theorems.Thm_GlobalTheory_ZH_WtPart_eq_sum_parts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtPart
variable {k : Type} [Field k] (Φ : FibPre k) {d : ℕ}
namespace GlobalTheory.ZH.WtPart
theorem _root_.solution : (∀ (k : Type) [Field k] (Φ : FibPre k) (d : ℕ), (∀ (φ : (Φ.H d).Sec) (α : Φ.E.X), ∃ ψ, Φ.IsPart α φ ψ) ∧ (∀ φ : (Φ.H d).Sec, (Φ.supp φ).Finite) ∧ (∀ φ ψ : (Φ.H d).Sec, (∀ α l, Φ.wt φ α l = Φ.wt ψ α l) → φ = ψ) ∧ ∀ (φ : (Φ.H d).Sec) (A : Finset Φ.E.X) (ψ : Φ.E.X → (Φ.H d).Sec), Φ.supp φ ⊆ A → (∀ α ∈ A, Φ.IsPart α φ (ψ α)) → ∀ l, φ.f l = ∑ α ∈ A, (ψ α).f l) :=
  fun _ _ Φ _ => ⟨fun φ α => ⟨_, isPart_partSec Φ φ α⟩, supp_finite Φ, sec_ext Φ, eq_sum_parts Φ⟩
end GlobalTheory.ZH.WtPart
