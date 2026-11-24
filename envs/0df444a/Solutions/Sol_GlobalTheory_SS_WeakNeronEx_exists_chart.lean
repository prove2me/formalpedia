-- Prove2me | solution 1 for GlobalTheory.SS.WeakNeronEx.exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:44:27.889744+00:00
-- url     : https://prove2.me/submissions/9371d17e-d081-4893-a05c-cde6616d5bb1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeakNeronModel
import Theorems.Thm_GlobalTheory_SS_WeakNeronEx_ev_rs
import Theorems.Thm_GlobalTheory_SS_WeakNeronEx_ev_ne_zero
import Theorems.Thm_GlobalTheory_SS_WeakNeronEx_exists_min

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WeakNeronEx
open GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory.SS.WeakNeronEx
theorem _root_.solution {X : Scheme.{0}} {H : LB X} {m : ℕ} (s : Fin (m + 1) → LB.Sec H)
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (r : ∀ i, Fin (m + 1) → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ i j k, rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
        rs X (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r i j) *
          rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k))
    {V L : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field L] [Algebra V L]
    [IsFractionRing V L] (a : Sp L ⟶ X) :
    ∃ (i : Fin (m + 1)) (h : ⊤ ≤ a ⁻¹ᵁ nonzeroLocus (s i)), ∀ j, ev a _ h (r i j) ∈ (algebraMap V L).range := by
  have hpt : ∀ W : X.Opens, a (IsLocalRing.closedPoint L) ∈ W → ⊤ ≤ a ⁻¹ᵁ W := fun W hW y _ => by
    have : y = IsLocalRing.closedPoint L := Subsingleton.elim (α := PrimeSpectrum L) _ _
    subst this
    exact hW
  have hx : a (IsLocalRing.closedPoint L) ∈ ⨆ i, nonzeroLocus (s i) := by rw [hc]; trivial
  obtain ⟨i₀, h₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h₀
  have hU : ⊤ ≤ a ⁻¹ᵁ H.U k := hpt _ (X.basicOpen_le _ hk)
  have hne : ev a _ hU ((s i₀).f k) ≠ 0 := (ev_ne_zero a hU _).2 (hpt _ hk)
  obtain ⟨i, hi⟩ := exists_min (V := V) (fun j => ev a _ hU ((s j).f k))
  have hne' : ev a _ hU ((s i).f k) ≠ 0 := by
    intro h
    obtain ⟨t, ht⟩ := hi i₀
    exact hne (by simpa [h] using ht)
  have hD : ⊤ ≤ a ⁻¹ᵁ nonzeroLocus (s i) :=
    hpt _ (TopologicalSpace.Opens.mem_iSup.2 ⟨k, (ev_ne_zero a hU _).1 hne' (x := IsLocalRing.closedPoint L) trivial⟩)
  have hI : ⊤ ≤ a ⁻¹ᵁ (nonzeroLocus (s i) ⊓ H.U k) := fun y hy => ⟨hD hy, hU hy⟩
  refine ⟨i, hD, fun j => ?_⟩
  obtain ⟨t, ht⟩ := hi j
  have e := congrArg (ev a _ hI) (hr i j k)
  rw [map_mul, ev_rs a _ hU, ev_rs a _ hU, ev_rs a _ hD, ht] at e
  exact ⟨t, mul_right_cancel₀ hne' e⟩
end GlobalTheory.SS.WeakNeronEx
