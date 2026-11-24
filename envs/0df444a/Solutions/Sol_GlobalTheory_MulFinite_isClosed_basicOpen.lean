-- Prove2me | solution 1 for GlobalTheory.MulFinite.isClosed_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:19:53.736689+00:00
-- url     : https://prove2.me/submissions/ea021931-7a82-4989-ad89-b7d676905101

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Theorems.Thm_GlobalTheory_MulFinite_exists_pow_mul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.MulFinite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace Polynomial
namespace GlobalTheory.MulFinite
theorem _root_.solution {Z : Scheme.{0}} {K : Type} [Field K] (f : Z ⟶ Spec (.of K))
    [UniversallyClosed f] (a : Γ(Z, ⊤)) : IsClosed (Z.basicOpen a : Set Z) := by
  have hk : IsField Γ(Spec (.of K), ⊤) :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨m, c, b, hc, e⟩ := exists_pow_mul_eq_zero hk _ a (isIntegral_appTop_of_universallyClosed f a)
  have : (Z.basicOpen a : Set Z) = (Z.basicOpen (c + a * b) : Set Z)ᶜ := by
    ext z
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    rw [Scheme.mem_basicOpen Z a z trivial, Scheme.mem_basicOpen Z (c + a * b) z trivial]
    let G : Γ(Z, ⊤) →+* Z.presheaf.stalk z := (Z.presheaf.germ ⊤ z trivial).hom
    change IsUnit (G a) ↔ ¬ IsUnit (G (c + a * b))
    have e' : G a ^ m * G (c + a * b) = 0 := by rw [← map_pow, ← map_mul, e, map_zero]
    constructor
    · intro h1 h2
      exact ((h1.pow m).mul h2).ne_zero e'
    · intro h2
      have hc' : IsUnit (G (c + a * b) + (- (G a * G b))) := by
        have := hc.map G
        simpa using this
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hc' with h | h
      · exact absurd h h2
      · exact isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h)
  rw [this]
  exact (Z.basicOpen _).isOpen.isClosed_compl
end GlobalTheory.MulFinite
