-- Prove2me | solution 1 for GlobalTheory.TorsionFourier.le_nonzeroLocus_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:51:41.475042+00:00
-- url     : https://prove2.me/submissions/08a5c315-4e97-4b82-ab37-bb9c062e92c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPointTranslatePure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinsuppEqZeroOfSumTorsionCharactersEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PartVanishesOnTorusTorsionFourier
import Theorems.Thm_GlobalTheory_TorsionFourier_valF_ne_zero_iff_le

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
open GlobalTheory GlobalTheory.TorsionFourier
variable {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : X.Opens}
namespace GlobalTheory.TorsionFourier
theorem _root_.solution {H : LB X} (s : H.Sec) (x : Sp F ⟶ X) :
    ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus s ↔ ∃ l, ⊤ ≤ x ⁻¹ᵁ H.U l ∧ valF x (H.U l) (s.f l) ≠ 0 := by
  constructor
  · intro h
    have hp : x (IsLocalRing.closedPoint F) ∈ Out.nonzeroLocus s :=
      h (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
    have h1 : ⊤ ≤ x ⁻¹ᵁ X.basicOpen (s.f l) := by
      intro y _
      have : y = IsLocalRing.closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
      subst this
      exact hl
    have h2 : ⊤ ≤ x ⁻¹ᵁ H.U l := h1.trans (Scheme.Hom.preimage_mono x (X.basicOpen_le _))
    exact ⟨l, h2, (valF_ne_zero_iff_le h2 _).2 h1⟩
  · rintro ⟨l, h2, hne⟩
    exact ((valF_ne_zero_iff_le h2 _).1 hne).trans
      (Scheme.Hom.preimage_mono x (le_iSup (fun k => X.basicOpen (s.f k)) l))
end GlobalTheory.TorsionFourier
