-- Prove2me | solution 1 for NumberField.PlaceDecomp.card_tateH0_units_eq_card_and_subsingleton_tateHneg1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/da936c17-a999-5d9d-aa14-f22ab0ecf14b

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_M4aLocalCFT_VocabDefs
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers
import Theorems.Thm_NumberField_PlaceDecomp_exists_mulEquiv_decompositionSubgroup_fixedPoints
import Theorems.Thm_Rep_nonempty_tate_addEquiv_elementwise
import Theorems.Thm_M4aLocalCFT_fieldUnitsDecomp_card_tateH0_eq_card
import Theorems.Thm_M4aLocalCFT_fieldUnitsDecomp_norm_ker_le_derive_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_card_tateH0_units_eq_card_and_subsingleton_tateHneg1

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

theorem solution (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K))
    [Fintype (NumberField.PlaceDecomp.decomp E K w)] [IsCyclic (NumberField.PlaceDecomp.decomp E K w)] :
    Nat.card (Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ).tateH0 =
      Nat.card (NumberField.PlaceDecomp.decomp E K w) ∧
    Subsingleton (Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ).tateHneg1 := by
  classical
  let G := NumberField.PlaceDecomp.decomp E K w
  let L := w.adicCompletion K
  let A : ValuationSubring L := w.adicCompletionIntegers K
  let K₀ := FixedPoints.subfield G L
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal A) A :=
    IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers K w
  haveI : Finite (IsLocalRing.ResidueField A) :=
    IsDedekindDomain.HeightOneSpectrum.finite_residueField_adicCompletionIntegers K w
  obtain ⟨Φ, hΦ⟩ := NumberField.PlaceDecomp.exists_mulEquiv_decompositionSubgroup_fixedPoints E K w
  haveI : Finite (A.decompositionSubgroup K₀) := Finite.of_equiv G Φ.toEquiv
  letI : Fintype (A.decompositionSubgroup K₀) := Fintype.ofFinite _
  haveI : IsCyclic (A.decompositionSubgroup K₀) := isCyclic_of_surjective Φ Φ.surjective
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := G)
  have hg : ∀ x, x ∈ Subgroup.zpowers (Φ g₀) := fun x => by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg₀ (Φ.symm x))
    exact Subgroup.mem_zpowers_iff.2 ⟨n, by rw [← map_zpow, hn, MulEquiv.apply_symm_apply]⟩

  have hact : ∀ (σ : G) (u : Lˣ), M4aLocalCFT.fieldUnitsAct A (Φ σ) u = σ • u := fun σ u => by
    refine Units.ext ?_
    show (((Φ σ : L ≃ₐ[K₀] L) : L → L) (u : L)) = ((σ • u : Lˣ) : L)
    rw [NumberField.PlaceDecomp.coe_smul_units]
    exact hΦ σ _
  have hD : ∀ x : Lˣ, M4aLocalCFT.fieldUnitsDerive A (Φ g₀) x = g₀ • x / x := fun x => by
    show M4aLocalCFT.fieldUnitsAct A (Φ g₀) x / x = _
    rw [hact]
  have hN : ∀ x : Lˣ, M4aLocalCFT.fieldUnitsNorm (K := K₀) A x = ∏ h : G, h • x := fun x => by
    unfold M4aLocalCFT.fieldUnitsNorm
    rw [MonoidHom.finsetProd_apply]
    exact (Fintype.prod_equiv Φ.toEquiv (fun h : G => h • x) (fun s => M4aLocalCFT.fieldUnitsAct A s x)
      (fun h => (hact h x).symm)).symm
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := Rep.nonempty_tate_addEquiv_elementwise g₀ hg₀ (M4aLocalCFT.fieldUnitsDerive A (Φ g₀))
    (M4aLocalCFT.fieldUnitsNorm (K := K₀) A) hD hN
  have hcard := M4aLocalCFT.fieldUnitsDecomp_card_tateH0_eq_card A (Φ g₀) hg
  have h90 := M4aLocalCFT.fieldUnitsDecomp_norm_ker_le_derive_range A (Φ g₀) hg
  haveI : Subsingleton ((M4aLocalCFT.fieldUnitsNorm (K := K₀) A).ker ⧸
      (M4aLocalCFT.fieldUnitsDerive A (Φ g₀)).range.subgroupOf (M4aLocalCFT.fieldUnitsNorm (K := K₀) A).ker) := by
    rw [Subgroup.subgroupOf_eq_top.2 h90]; exact QuotientGroup.subsingleton_quotient_top
  refine ⟨?_, e1.toEquiv.subsingleton⟩
  rw [Nat.card_congr e0.toEquiv]
  exact hcard.trans (Nat.card_congr Φ.toEquiv.symm)

end S_NumberField_PlaceDecomp_card_tateH0_units_eq_card_and_subsingleton_tateHneg1
end P2MW
export P2MW.S_NumberField_PlaceDecomp_card_tateH0_units_eq_card_and_subsingleton_tateHneg1 (solution)
