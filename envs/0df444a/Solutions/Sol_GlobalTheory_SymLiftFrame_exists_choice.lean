-- Prove2me | solution 1 for GlobalTheory.SymLiftFrame.exists_choice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:59:19.389798+00:00
-- url     : https://prove2.me/submissions/c328fda7-cddb-4a8f-ad92-013fdd79a225

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymmetricLiftTorsionPointActionOnTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.SymLiftFrame
open ThetaFn CubeValues SymmetricSemicharacter AppellHumbertTrivial ReciprocityTheory.ChartRestriction.G.Out
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {T : Over (Sp ℂ)} {p : 𝟙_ (Over (Sp ℂ)) ⟶ T} {J : (Sp ℂ ⟶ A.left) → L.ι}
  (hJ : ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
variable {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ} {c : ℂ}
namespace GlobalTheory.SymLiftFrame
theorem _root_.solution (hL : L.IsLB) :
    ∃ J : (Sp ℂ ⟶ A.left) → L.ι, ∀ ψ : Sp ℂ ⟶ A.left, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ) := by
  have hpt : ∀ a b : Sp ℂ, a = b := fun a b =>
    PrimeSpectrum.ext (((Ideal.eq_bot_or_top a.asIdeal).resolve_right a.isPrime.ne_top).trans
      ((Ideal.eq_bot_or_top b.asIdeal).resolve_right b.isPrime.ne_top).symm)
  have key : ∀ ψ : Sp ℂ ⟶ A.left, ∃ i, ⊤ ≤ ψ ⁻¹ᵁ L.U i := by
    intro ψ
    obtain ⟨p0⟩ : Nonempty (PrimeSpectrum ℂ) := inferInstance
    have h0 : ψ p0 ∈ (⨆ i, L.U i) := by
      rw [hL.cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h0
    exact ⟨i, fun p _ => by rw [hpt p p0]; exact hi⟩
  choose J hJ using key
  exact ⟨J, hJ⟩
end GlobalTheory.SymLiftFrame
