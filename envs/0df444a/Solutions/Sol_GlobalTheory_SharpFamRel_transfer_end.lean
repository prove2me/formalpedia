-- Prove2me | solution 1 for GlobalTheory.SharpFamRel.transfer_end
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:57:45.146313+00:00
-- url     : https://prove2.me/submissions/e2a69517-7af9-4a8b-b183-caf5a38e4ca0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SharpRelations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_E8SharpFamilyMatrixRelationsDense
import Theorems.Thm_GlobalTheory_SharpFamRel_epi_of_isPullback
import Theorems.Thm_GlobalTheory_SharpFamRel_eq_up
import Theorems.Thm_GlobalTheory_SharpFamRel_eq_down
import Theorems.Thm_GlobalTheory_SharpFamRel_ext_of_dense
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_of_isReduced


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SharpFamRel
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}
variable {em : o →+* ℂ} {C : TObj g k J b (spMap em) → Prop} {S : Scheme.{0}} {s : S ⟶ Sp o}
namespace GlobalTheory.SharpFamRel
theorem _root_.solution [IsReduced S] {F G : ∀ {S : Scheme.{0}} {s : S ⟶ Sp o} (t : TObj g k J b s), t.A ⟶ t.A}
    (hF : NatEnd F) (hG : NatEnd G) (H : ∀ tc, C tc → F tc = G tc) (t : TObj g k J b s)
    (hD : Dense (fromSet em C t)) : F t = G t := by
  have := t.ab.smooth
  have := t.ab.proper
  have : IsReduced t.A.left := GlobalTheory.isReduced_of_smooth_of_isReduced t.A.hom
  refine ext_of_dense t.A.hom.isOpenMap (F t) (G t) hD ?_
  rintro p ⟨K, _, x, hp, K₀, _, β, i, j, t₀, tx, tc, -, -, ⟨φx, hx, -, -, hax⟩, ⟨φ0, h0, -, -, ha0⟩,
    ⟨φc, hc, -, -, hac⟩, hC⟩
  have : Nonempty (Sp ℂ) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
  have e0 : F t₀ = G t₀ :=
    eq_down hc (selfMap hc) (epi_of_isPullback hc.1) (hF tc t₀ hc hac) (hG tc t₀ hc hac) (H tc hC)
  have e1 : F tx = G tx := eq_up h0 (selfMap h0) (hF tx t₀ h0 ha0) (hG tx t₀ h0 ha0) e0
  refine ⟨tx.A.left, Sp K, φx, tx.A.hom, x, hx.1, hp, ?_⟩
  have k1 : (F tx).left ≫ φx = φx ≫ (F t).left := congrArg CommaMorphism.left (hF tx t hx hax)
  have k2 : (G tx).left ≫ φx = φx ≫ (G t).left := congrArg CommaMorphism.left (hG tx t hx hax)
  rw [← k1, ← k2, e1]
end GlobalTheory.SharpFamRel
