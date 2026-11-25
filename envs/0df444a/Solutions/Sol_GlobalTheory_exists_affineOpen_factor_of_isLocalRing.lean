-- Prove2me | solution 1 for GlobalTheory.exists_affineOpen_factor_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:56:18.409613+00:00
-- url     : https://prove2.me/submissions/a3291e85-cf93-4fd7-a386-95fc54530235

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


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
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory
theorem _root_.solution {R : CommRingCat.{0}} [IsLocalRing R]
    {X : Scheme.{0}} (y : Spec R ⟶ X) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (φ : Γ(X, V) ⟶ R), Spec.map φ ≫ hV.fromSpec = y := by
  obtain ⟨V, hV, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := y (IsLocalRing.closedPoint R)) trivial
  have hr : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have : y ⁻¹ᵁ V = ⊤ := (IsLocalRing.closed_point_mem_iff).mp hz
    exact (this.ge (Set.mem_univ x) : x ∈ y ⁻¹ᵁ V)
  refine ⟨V, hV, Spec.preimage (IsOpenImmersion.lift hV.fromSpec y hr), ?_⟩
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
end GlobalTheory
