-- Prove2me | solution 1 for GlobalTheory.SW.InvBound.exists_common_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:16:35.925315+00:00
-- url     : https://prove2.me/submissions/6c2a7cc7-c20c-45af-b582-e0add1722ca8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DecayOfVanishingAtCuspsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilActionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatSwdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SwdTendstoZeroAtCuspsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryMoveHermitianHalfSpaceHighStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceAutomorphyLinearityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceInvariantNormBounded
import Theorems.Thm_GlobalTheory_SW_Base_mem_stdL
import Theorems.Thm_GlobalTheory_SW_Base_nat_smul_mem
import Theorems.Thm_GlobalTheory_SW_Model_mem_stdL
import Theorems.Thm_GlobalTheory_SW_Model_nat_smul_mem
import Theorems.Thm_GlobalTheory_SW_finite_cls_and_stab
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW
open GlobalTheory.SW.InvBound
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.InvBound
theorem _root_.solution {M R : ℕ} (hM : 0 < M) (hR : 0 < R) :
    ∃ R₀ : ℕ, 0 < R₀ ∧ ∀ φ : Fam E n N, admitted M R φ → ∀ c : Cls E n M,
      HasLevel R₀ (φ (Quot.out c).1) := by
  haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M hM).1
  haveI := Fintype.ofFinite (Cls E n M)
  choose s hs _ h1 h2 using fun c : Cls E n M => (Quot.out c).2.2.2
  refine ⟨(∏ c, s c) * R, Nat.mul_pos (Finset.prod_pos fun c _ => hs c) hR, fun φ hφ c => ?_⟩
  obtain ⟨m, hm⟩ : s c ∣ ∏ c, s c := Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
  rw [hm]
  constructor
  · intro x hx k a
    have := Base.nat_smul_mem _ m (h1 c _ (hφ.supp _ (Quot.out c).2 x hx a))
    have := (Base.mem_stdL _).1 this k
    convert this using 1
    simp; ring
  · intro x y hy
    have := hφ.per _ (Quot.out c).2 x (((s c * m : ℕ) : E) • y) fun a => by
      have := Base.nat_smul_mem _ m (h2 c (yᵀ a) ((Base.mem_stdL _).2 fun k => hy k a))
      convert this using 1
      ext k; simp; ring
    rw [← this, smul_smul]
    congr 3
    push_cast; ring
end GlobalTheory.SW.InvBound
