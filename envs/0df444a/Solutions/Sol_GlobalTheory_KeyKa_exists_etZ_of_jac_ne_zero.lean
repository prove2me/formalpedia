-- Prove2me | solution 1 for GlobalTheory.KeyKa.exists_etZ_of_jac_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:29:11.717776+00:00
-- url     : https://prove2.me/submissions/3825de6d-83eb-42f1-9a41-5d5eb0402117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteOfIsClosedSingleton
import Theorems.Thm_GlobalTheory_TransvFin_valT_eq_zero_of_notMem
import Theorems.Thm_GlobalTheory_TransvFin_eq_of_specializes
import Theorems.Thm_GlobalTheory_TransvFin_finite_of_isClosed_singleton
import Theorems.Thm_GlobalTheory_KeyKa_jac_ne_zero_iff_span_eq_maximalIdeal
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory.TransvFin
namespace GlobalTheory.KeyKa
theorem _root_.solution : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n : ℕ) (s : Fin x.P.g → RR x n), (∀ (z : Pt x) (c : x.P.L.ι), ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c → (∀ i, valT (T := K) z.left (x.P.L.U c) ((s i).f c) = 0) → jac x s z c ≠ 0) → ∃ (d : ℕ) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), EtZ x s z ch := by
  intro K _ _ x n s hs
  have := x.P.smoothDim
  have : Smooth x.P.A.hom := SmoothOfRelativeDimension.smooth x.P.g _
  have : IsProper x.P.A.hom := x.P.isAb.proper
  have : JacobsonSpace x.P.A.left := LocallyOfFiniteType.jacobsonSpace x.P.A.hom
  have : IsLocallyNoetherian x.P.A.left := LocallyOfFiniteType.isLocallyNoetherian x.P.A.hom
  have : CompactSpace x.P.A.left := QuasiCompact.compactSpace_of_compactSpace x.P.A.hom
  have : IsNoetherian x.P.A.left := {}
  let Z : Set x.P.A.left := {y | ∀ i, y ∉ Out.nonzeroLocus (s i)}
  have hZ : IsClosed Z := by
    have e : Z = ⋂ i, (Out.nonzeroLocus (s i) : Set x.P.A.left)ᶜ := by
      ext y
      simp [Z]
    rw [e]
    exact isClosed_iInter fun i => (Out.nonzeroLocus (s i)).isOpen.isClosed_compl
  have hb : ∀ y ∈ Z, ∀ c i, y ∉ x.P.A.left.basicOpen ((s i).f c) := fun y hy c i h =>
    hy i (TopologicalSpace.Opens.mem_iSup.2 ⟨c, h⟩)
  have key : ∀ y ∈ Z, IsClosed ({y} : Set x.P.A.left) → ∃ (z : Pt x) (c : x.P.L.ι), (∀ p, z.left p = y) ∧
      ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c ∧ ∀ i, valT (T := K) z.left (x.P.L.U c) ((s i).f c) = 0 := by
    intro y hy hc
    let z : Pt x := Over.homMk (pointOfClosedPoint (K := K) x.P.A.hom y hc)
      (pointOfClosedPoint_comp (K := K) x.P.A.hom y hc)
    have hz (p) : z.left p = y := pointOfClosedPoint_apply (K := K) x.P.A.hom y hc p
    obtain ⟨c, hyc⟩ := TopologicalSpace.Opens.mem_iSup.1 (x.P.isLB.cover.ge (x := y) trivial)
    have ht : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c := fun p _ => (congrArg (· ∈ x.P.L.U c) (hz p)).mpr hyc
    exact ⟨z, c, hz, ht, fun i => valT_eq_zero_of_notMem z.left ht _ (IsLocalRing.closedPoint K)
      fun h => hb y hy c i ((congrArg (· ∈ x.P.A.left.basicOpen ((s i).f c)) (hz _)).mp h)⟩
  have hcl : ∀ y ∈ Z, IsClosed ({y} : Set x.P.A.left) := by
    intro y' hy'
    obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints (Z := closure ({y'} : Set x.P.A.left))
      ⟨y', subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    have hsp : y' ⤳ y := specializes_iff_mem_closure.2 hy
    obtain ⟨z, c, hz, ht, h0⟩ := key y (hsp.mem_closed hZ hy') hc
    have h1 := (jac_ne_zero_iff_span_eq_maximalIdeal K x n s z c (IsLocalRing.closedPoint K) ht h0).1 (hs z c ht h0)
    have hU : z.left (IsLocalRing.closedPoint K) ∈ x.P.L.U c := ht (x := IsLocalRing.closedPoint K) trivial
    have e := eq_of_specializes (fun i => (s i).f c) ((hz _).symm ▸ hsp) hU h1 (hb y' hy' c)
    rw [e.trans (hz _)]
    exact hc
  have hfin := finite_of_isClosed_singleton hZ hcl
  obtain ⟨d, ⟨e⟩⟩ := Finite.exists_equiv_fin Z (h := hfin)
  choose z c hz ht h0 using fun y : Z => key y y.2 (hcl y y.2)
  refine ⟨d, fun a => z (e.symm a), fun a => c (e.symm a), fun a => ht _, fun a => h0 _,
    fun a => (hs _ _ (ht _) (h0 _)).isUnit, fun a a' hne p h => hne ?_,
    fun y hy => ⟨e ⟨y, hy⟩, IsLocalRing.closedPoint K, ?_⟩⟩
  · exact e.symm.injective (Subtype.ext ((hz _ p).symm.trans (h.trans (hz _ p))))
  · exact (hz _ _).trans (congrArg Subtype.val (e.symm_apply_apply ⟨y, hy⟩))
end GlobalTheory.KeyKa
