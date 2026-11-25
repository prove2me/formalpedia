-- Prove2me | solution 1 for GlobalTheory.KeyKa.etZ_lift_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:47:13.059361+00:00
-- url     : https://prove2.me/submissions/1819b0df-d43a-485d-bb5a-15da8bd6fbcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsSectionOfTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TransversalZerosLiftOfIsAdicComplete
import Theorems.Thm_GlobalTheory_HenselZero_map_mem_nonzeroLocus_via
import Theorems.Thm_GlobalTheory_HenselZero_exists_lift_point
import Theorems.Thm_GlobalTheory_HenselZero_isClosedImmersion_fibre
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory.HenselZero
namespace GlobalTheory.KeyKa
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (xk : KeyIn (IsLocalRing.ResidueField O)) φ w (n d : ℕ) (hg : xk.P.g = x.P.g) (s : Fin x.P.g → RR x n) (sk : Fin xk.P.g → RR xk n) (zk : Fin d → Pt xk) (chk : Fin d → xk.P.L.ι), KeyVia xk x (IsLocalRing.residue O) φ w → (∀ i, SecVia xk x φ w (sk i) (s (i.cast hg))) → EtZ xk sk zk chk → ∃ (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), EtZ x s z ch := by
  intro O _ _ _ _ x xk φ w n d hg s sk zk chk hvia hs ⟨h₁, h₂, h₃, h₄, h₅⟩
  choose z ch hz₀ hz₁ hz₂ hz₃ hz₄ using fun a => exists_lift_point hg hvia hs (zk a) (chk a) (h₁ a) (h₂ a) (h₃ a)
  obtain ⟨_, _, _, ⟨hp, -⟩, -⟩ := hvia
  have := x.P.isAb.proper
  have := isClosedImmersion_fibre hp
  let pt : Sp (IsLocalRing.ResidueField O) := IsLocalRing.closedPoint _
  have hcp : spMap (IsLocalRing.residue O) pt = IsLocalRing.closedPoint O :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  have hw : ∀ a, (z a).left ≫ x.P.A.hom = 𝟙 (Sp O) := fun a => Over.w (z a)
  have hzc : ∀ a, (z a).left (IsLocalRing.closedPoint O) = φ ((zk a).left pt) := fun a =>
    (congrArg (z a).left hcp).symm.trans (congrArg (fun g => g pt) (hz₀ a))
  refine ⟨z, ch, hz₁, hz₂, hz₃, fun a a' h r e => h₄ a a' h pt (φ.isClosedEmbedding.injective ?_), fun y hy => ?_⟩
  · have : IsClosedImmersion ((z a').left ≫ x.P.A.hom) := by
      rw [hw]
      exact (inferInstance : IsClosedImmersion (𝟙 (Sp O) : Sp O ⟶ Sp O))
    have := IsClosedImmersion.of_comp (z a').left x.P.A.hom
    obtain ⟨r', hr'⟩ := ((IsLocalRing.specializes_closedPoint r).map (z a).left.continuous).mem_closed
      (z a').left.isClosedEmbedding.isClosed_range ⟨r, e.symm⟩
    have e₁ : r' = IsLocalRing.closedPoint O :=
      (congrArg (fun g => g r') (hw a')).symm.trans ((congrArg x.P.A.hom hr').trans
        (congrArg (fun g => g (IsLocalRing.closedPoint O)) (hw a)))
    rw [← hzc, ← hzc, ← hr', e₁]
  · obtain ⟨y₀, hy₀, e⟩ := (IsLocalRing.specializes_closedPoint (x.P.A.hom y)).mem_closed
      (x.P.A.hom.isClosedMap _ (isClosed_closure (s := {y}))) ⟨y, subset_closure rfl, rfl⟩
    have hsp : y ⤳ y₀ := specializes_iff_mem_closure.2 hy₀
    obtain ⟨y', rfl, -⟩ := Scheme.exists_preimage_of_isPullback hp y₀ pt (e.trans hcp.symm)
    obtain ⟨a, r, rfl⟩ := h₅ y' fun i h => hy (i.cast hg)
      (hsp.mem_open (Out.nonzeroLocus _).isOpen (map_mem_nonzeroLocus_via (hs i) y' h))
    exact ⟨a, hz₄ a y r hsp hy⟩
end GlobalTheory.KeyKa
