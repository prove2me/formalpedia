-- Prove2me | solution 1 for GlobalTheory.HL.LocDict.exists_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:29:14.856719+00:00
-- url     : https://prove2.me/submissions/2202847d-6f32-45ed-b045-59c8d61b3d74

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
import Theorems.Thm_GlobalTheory_HL_LocDict_exists_functional
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocDict
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace GlobalTheory.HL.LocDict
theorem _root_.solution [IsDedekindDomain R] (L : Submodule R V) (hL : L.FG) :
    ∃ (m : ℕ) (b : Fin m → V) (Φ : Fin m → V →ₗ[K] K), (∀ i, b i ∈ L) ∧
      (∀ i, ∀ y ∈ L, ∃ o : R, Φ i y = algebraMap R K o) ∧ ∀ y ∈ L, y = ∑ i, Φ i y • b i := by
  haveI : Module.Finite R L := Module.Finite.iff_fg.2 hL
  have htors : Submodule.torsion R L = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨a, ha⟩, hy⟩
    have hy' : a • y = 0 := hy
    have ha0 : algebraMap R K a ≠ 0 := by
      simpa using nonZeroDivisors.ne_zero ha
    have h2 : a • (y : V) = 0 := congrArg Subtype.val hy'
    rw [← algebraMap_smul K a (y : V)] at h2
    have h3 : (y : V) = 0 := (smul_eq_zero.1 h2).resolve_left ha0
    exact Subtype.ext h3
  haveI : Module.Flat R L := flat_iff_torsion_eq_bot.2 htors
  haveI : Module.FinitePresentation R L := Module.finitePresentation_of_finite R L
  haveI : Module.Projective R L := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin' R L
  obtain ⟨t, ht⟩ := Module.projective_lifting_property g LinearMap.id hg
  choose Φ hΦ using fun i : Fin m =>
    exists_functional (K := K) L ((Algebra.linearMap R K) ∘ₗ (LinearMap.proj i) ∘ₗ t)
  refine ⟨m, fun i => (g fun j => if i = j then 1 else 0 : L), Φ, fun i => Subtype.property _,
    fun i y hy => ⟨t ⟨y, hy⟩ i, hΦ i ⟨y, hy⟩⟩, fun y hy => ?_⟩
  have h1 : g (t ⟨y, hy⟩) = ⟨y, hy⟩ := congr($ht ⟨y, hy⟩)
  have h2 := LinearMap.pi_apply_eq_sum_univ g (t ⟨y, hy⟩)
  rw [h1] at h2
  have h3 := congrArg Subtype.val h2
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
  refine h3.trans (Finset.sum_congr rfl fun i _ => ?_)
  have h4 := hΦ i ⟨y, hy⟩
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, Algebra.linearMap_apply] at h4
  change _ = Φ i y • _
  rw [h4, algebraMap_smul]
end GlobalTheory.HL.LocDict
