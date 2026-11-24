-- Prove2me | solution 1 for GlobalTheory.TorsionReduced.isReduced_of_forall_dualNumber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:42:28.552808+00:00
-- url     : https://prove2.me/submissions/0bb72d67-68c5-484d-ac16-a971dd61ef9c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsReducedTorsionGeometricFibre
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.TorsionReduced
namespace GlobalTheory.TorsionReduced
theorem _root_.solution (F B : Type) [Field F] [IsAlgClosed F] [CommRing B]
    [Algebra F B] [Module.Finite F B]
    (h : ∀ (φ : B →ₐ[F] DualNumber F) (b : B), (φ b).snd = 0) : _root_.IsReduced B := by
  have hs : Subsingleton (KaehlerDifferential F B) := by
    by_contra hne
    have : Nontrivial (KaehlerDifferential F B) := not_subsingleton_iff_nontrivial.mp hne
    obtain ⟨P, hP, -⟩ := (eq_top_or_exists_le_coatom
      (⊥ : Submodule B (KaehlerDifferential F B))).resolve_left bot_ne_top
    have hsimple : IsSimpleModule B (KaehlerDifferential F B ⧸ P) :=
      isSimpleModule_iff_isCoatom.mpr hP
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
    letI : Field (B ⧸ m) := Ideal.Quotient.field m
    have hb : Function.Bijective (algebraMap F (B ⧸ m)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let u : (B ⧸ m) ≃ₐ[F] F := (AlgEquiv.ofBijective (Algebra.ofId F (B ⧸ m)) hb).symm
    let l : KaehlerDifferential F B →ₗ[B] (B ⧸ m) := e.toLinearMap ∘ₗ P.mkQ
    let D : Derivation F B (B ⧸ m) := l.compDer (KaehlerDifferential.D F B)
    let φ : B →ₐ[F] DualNumber F :=
      { toFun := fun b => TrivSqZeroExt.inl (u (Ideal.Quotient.mk m b)) + TrivSqZeroExt.inr (u (D b))
        map_one' := by ext <;> simp
        map_mul' := fun a b => by
          ext
          · simp
          · simp [Algebra.smul_def, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
        map_zero' := by ext <;> simp
        map_add' := fun a b => by ext <;> simp
        commutes' := fun r => by
          ext
          · simpa [TrivSqZeroExt.algebraMap_eq_inl] using u.commutes r
          · simp [TrivSqZeroExt.algebraMap_eq_inl] }
    have hD : ∀ b, l (KaehlerDifferential.D F B b) = 0 := fun b => by
      have := h φ b
      simpa [φ, D] using this
    have hl : l = 0 := by
      refine LinearMap.ext_on (KaehlerDifferential.span_range_derivation F B) ?_
      rintro _ ⟨b, rfl⟩
      exact hD b
    apply hP.1
    rw [eq_top_iff]
    intro x _
    have := LinearMap.congr_fun hl x
    simpa [l] using this
  have : Algebra.FormallyUnramified F B := ⟨hs⟩
  exact Algebra.FormallyUnramified.isReduced_of_field F B
end GlobalTheory.TorsionReduced
