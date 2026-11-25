-- Prove2me | solution 1 for GlobalTheory.LatticeBetaCompare.selfDual_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:39:32.690881+00:00
-- url     : https://prove2.me/submissions/98f0fd83-9e80-4dde-84f8-16aea905a587

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeBetaCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.GenusLatCompare
open scoped nonZeroDivisors Pointwise
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)
variable {Dw c}
variable (Dw c)
namespace GlobalTheory.LatticeBetaCompare
theorem _root_.solution {Λ : Lat E n} (h : Λ.SelfDual) {γ : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hγ : IsUnitary γ) :
    (Λ.map γ).SelfDual := by
  intro x
  obtain ⟨x, rfl⟩ := γ.surjective x
  constructor
  · rintro ⟨x', hx, e⟩ _ ⟨y, hy, rfl⟩
    obtain rfl : x' = x := γ.injective e
    exact (hγ x' y).symm ▸ (h x').1 hx y hy
  · intro hx
    exact ⟨x, (h x).2 fun y hy => hγ x y ▸ hx _ ⟨y, hy, rfl⟩, rfl⟩
end GlobalTheory.LatticeBetaCompare
