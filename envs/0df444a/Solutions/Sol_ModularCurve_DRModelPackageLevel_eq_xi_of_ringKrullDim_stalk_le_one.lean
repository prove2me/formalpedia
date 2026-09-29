-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.eq_xi_of_ringKrullDim_stalk_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/1aa37336-fe60-5dce-82a0-f5facbb98efc

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Theorems.Thm_ModularCurve_DRModelPackageLevel_isIntegral_pullback_toBase_specMap
import Theorems.Thm_ModularCurve_DRLevel_bcMap_apply_notMem_preimage_basicOpen
import Theorems.Thm_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_or
import Theorems.Thm_AlgebraicGeometry_Scheme_branchIdeal_le_branchIdeal_iff
import Theorems.Thm_AlgebraicGeometry_map_appTop_mem_nonZeroDivisors_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_eq_xi_of_ringKrullDim_stalk_le_one
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve IsLocalRing

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

namespace ECL_CodimX0

universe u

private theorem eq_of_specializes_of_ringKrullDim_le_one {X : Scheme.{u}} [IsIntegral X] (s : Γ(X, ⊤)) (hs : s ≠ 0)
    {a z : X} (h : a ⤳ z) (ha : a ∉ X.basicOpen s) (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1) : a = z := by

  set g := (X.presheaf.germ ⊤ z trivial).hom s with hg
  have hg0 : g ≠ 0 := fun h0 =>
    hs (germ_injective_of_isIntegral X (U := ⊤) z trivial (by rw [map_zero]; exact h0))
  have hgP : g ∈ Scheme.branchIdeal h := by
    rw [Scheme.mem_branchIdeal_iff, hg, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => ha ((X.mem_basicOpen_top s a).mpr hu)

  have hP : Scheme.branchIdeal h = maximalIdeal (X.presheaf.stalk z) := by
    rcases (Order.krullDim_le_one_iff.mp hdim) ⟨Scheme.branchIdeal h, inferInstance⟩ with hmin | hmax
    · exfalso
      apply hg0
      have hbot : (⟨Scheme.branchIdeal h, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk z)) ≤
          ⟨⊥, Ideal.isPrime_bot⟩ := hmin (show (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _) ≤ _ from bot_le)
      exact (Ideal.mem_bot).mp (hbot hgP)
    · have hle : (⟨Scheme.branchIdeal h, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk z)) ≤
          ⟨maximalIdeal _, inferInstance⟩ := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
      exact congrArg PrimeSpectrum.asIdeal (le_antisymm hle (hmax hle))

  have hza : z ⤳ a := by
    rw [← AlgebraicGeometry.Scheme.branchIdeal_le_branchIdeal_iff h (specializes_rfl : z ⤳ z), hP]
    exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  exact h.antisymm hza |>.eq

end ECL_CodimX0

namespace ECL_XiDimOne

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})

private noncomputable def pSec : Γ(DRLevel.XO (N₀ := N₀) ρO, ⊤) :=
  (DRLevel.XO.toBase (N₀ := N₀) ρO).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ((q : ℕ) : O))

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem basicOpen_pSec :
    (DRLevel.XO (N₀ := N₀) ρO).basicOpen (pSec O ρO) =
      (DRLevel.XO.toBase (N₀ := N₀) ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
  rw [pSec, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]

include 𝔛 hϖ in

private theorem pSec_ne_zero : pSec (N₀ := N₀) O ρO ≠ 0 := by
  classical
  haveI : IsIntegral (DRLevel.XO (N₀ := N₀) ρO) := ModularCurve.DRModelPackageLevel.isIntegral_pullback_toBase_specMap N₀ q hqN 𝔛 O hϖ ρO
  haveI := 𝔛.flat
  haveI : Flat (DRLevel.XO.toBase (N₀ := N₀) ρO) := inferInstance
  have hp0 : ((q : ℕ) : O) ≠ 0 := by
    intro h
    apply IsDiscreteValuationRing.not_a_field O
    rw [hϖ, h, Ideal.span_singleton_eq_bot.mpr rfl]
  obtain ⟨x⟩ := (inferInstance : Nonempty ↥(DRLevel.XO (N₀ := N₀) ρO))
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens (DRLevel.XO (N₀ := N₀) ρO)))
    (show x ∈ (⊤ : (DRLevel.XO (N₀ := N₀) ρO).Opens) from trivial)
  have hreg := AlgebraicGeometry.map_appTop_mem_nonZeroDivisors_of_flat (DRLevel.XO.toBase (N₀ := N₀) ρO) _
    (mem_nonZeroDivisors_of_ne_zero hp0) U hU
  intro h0
  have : (DRLevel.XO (N₀ := N₀) ρO).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (pSec O ρO) = 0 := by rw [h0, map_zero]
  rw [pSec] at this
  rw [this] at hreg
  haveI : Nontrivial Γ(DRLevel.XO (N₀ := N₀) ρO, U) := ((DRLevel.XO (N₀ := N₀) ρO).presheaf.germ U x hxU).hom.domain_nontrivial
  exact zero_notMem_nonZeroDivisors hreg

end ECL_XiDimOne

open ECL_CodimX0 ECL_XiDimOne in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (z : ↥(DRLevel.XO (N₀ := N₀) ρO))
    (hz : z ∉ (DRLevel.XO.toBase (N₀ := N₀) ρO) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
    (hdim : ringKrullDim ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk z) ≤ 1) :
    z = 𝔛.ξinf ρO toκ ∨ z = 𝔛.ξzero ρO toκ := by
  haveI : IsIntegral (DRLevel.XO (N₀ := N₀) ρO) := ModularCurve.DRModelPackageLevel.isIntegral_pullback_toBase_specMap N₀ q hqN 𝔛 O hϖ ρO
  haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  have ht := ECL_XiDimOne.pSec_ne_zero 𝔛 O ρO hϖ
  have hV : ∀ i : DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO) ⟶ DRLevel.fibre (N₀ := N₀) (toκ.comp ρO),
      (i ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))) ∉
        (DRLevel.XO (N₀ := N₀) ρO).basicOpen (ECL_XiDimOne.pSec (N₀ := N₀) O ρO) := by
    intro i
    rw [ECL_XiDimOne.basicOpen_pSec, Scheme.Hom.comp_apply]
    exact ModularCurve.DRLevel.bcMap_apply_notMem_preimage_basicOpen N₀ q O ρO κ toκ _
  rcases ModularCurve.DRModelPackageLevel.bcMap_genericPoint_specializes_or N₀ q hqN 𝔛 O ρO hϖ κ toκ z hz with h | h
  · exact Or.inl (eq_of_specializes_of_ringKrullDim_le_one _ ht h (hV _) hdim).symm
  · exact Or.inr (eq_of_specializes_of_ringKrullDim_le_one _ ht h (hV _) hdim).symm

end S_ModularCurve_DRModelPackageLevel_eq_xi_of_ringKrullDim_stalk_le_one
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_eq_xi_of_ringKrullDim_stalk_le_one (solution)
