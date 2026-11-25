-- Prove2me | solution 1 for GlobalTheory.SharpFamRel.transfer_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:45:14.978989+00:00
-- url     : https://prove2.me/submissions/0858b66c-c4f7-457c-b8a6-5ee302fda6f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SharpRelations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_E8SharpFamilyMatrixRelationsDense
import Theorems.Thm_GlobalTheory_SharpFamRel_eq_up
import Theorems.Thm_GlobalTheory_SharpFamRel_eq_down
import Theorems.Thm_GlobalTheory_SharpFamRel_ext_of_dense

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
theorem _root_.solution [IsReduced S]
    {F G : ∀ {S : Scheme.{0}} {s : S ⟶ Sp o} (t : TObj g k J b s), Out.baseOver S ⟶ t.A}
    (hF : NatPt F) (hG : NatPt G) (H : ∀ tc, C tc → F tc = G tc) (t : TObj g k J b s)
    (hD : Dense (fromSet em C t)) : F t = G t := by
  have := t.ab.proper
  have hbase : (Out.baseOver S).hom = 𝟙 S := rfl
  have : IsReduced (Out.baseOver S).left := ‹IsReduced S›
  refine ext_of_dense (by rw [hbase]; exact IsOpenMap.id) (F t) (G t) hD ?_
  rintro p ⟨K, _, x, hp, K₀, _, β, i, j, t₀, tx, tc, -, -, ⟨φx, hx, -, hpx, hax⟩, ⟨φ0, h0, -, hp0, ha0⟩,
    ⟨φc, hc, -, hpc, hac⟩, hC⟩
  have hepi : Epi (baseMap (S' := Sp ℂ) (spMap j)).left := by
    have hs : Surjective (spMap j) := ⟨fun y => by
      obtain ⟨z⟩ : Nonempty (Sp ℂ) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
      exact ⟨z, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective (spMap j)
  have e0 : F t₀ = G t₀ :=
    eq_down hc (baseMap (spMap j)) hepi (hF tc t₀ hc hpc hac) (hG tc t₀ hc hpc hac) (H tc hC)
  have e1 : F tx = G tx := eq_up h0 (baseMap (spMap i)) (hF tx t₀ h0 hp0 ha0) (hG tx t₀ h0 hp0 ha0) e0
  refine ⟨Sp K, Sp K, x, 𝟙 _, x, by rw [hbase]; exact IsPullback.of_id_snd, hp, ?_⟩
  have k1 : (F tx).left ≫ φx = x ≫ (F t).left := congrArg CommaMorphism.left (hF tx t hx hpx hax)
  have k2 : (G tx).left ≫ φx = x ≫ (G t).left := congrArg CommaMorphism.left (hG tx t hx hpx hax)
  rw [← k1, ← k2, e1]
end GlobalTheory.SharpFamRel
