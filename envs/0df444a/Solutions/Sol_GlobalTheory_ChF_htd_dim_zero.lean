-- Prove2me | solution 1 for GlobalTheory.ChF.htd_dim_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:33:43.609188+00:00
-- url     : https://prove2.me/submissions/d3adf72c-323e-45f7-9b7d-eee25fdcccb9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_HopfPointMem
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE] (cp : O), Nonempty (HodgeTateDatum p 0 v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ OE _ _ cp
  let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
  have hS : Subsingleton (LieDualModP p O 0) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  refine ⟨{
    ρ :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _
        commutes' := fun _ => Subsingleton.elim _ _ }
    ρL :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _ }
    P := 0
    PL := 0
    E := 0
    E_alternating := ⟨Subsingleton.elim _ _, fun _ => rfl⟩
    isUnit_det_E := by simp
    E_equivariant := fun _ => Subsingleton.elim _ _
    projectors := ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
      fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
    Ht := 0
    Bt := 0
    Ht_equivariant := ⟨fun _ => Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    form_eq_alt := Subsingleton.elim _ _
    AA := hopfPoint O (Nb p 0)
    h3 := fun a f hf => ⟨f, hf, fun t => congrArg f (Subsingleton.elim _ _)⟩
    h4 := fun k => k.elim0
    h5 := fun _ s => ⟨1, hopfPoint_one O _, fun t => by
      have h0 : Up.pair p 0 0 s t = 0 := by simp [Up.pair]
      rw [h0, map_zero, ZMod.val_zero, pow_zero, Pi.one_apply]⟩
    φ := 0
    cotangent_surjective := fun y => ⟨0, Subsingleton.elim _ _⟩
    cotangent_ker_eq := ?_
    cotangent_linear := fun _ _ _ _ _ _ => Subsingleton.elim _ _ }⟩
  rw [LinearMap.ker_zero, eq_comm, eq_top_iff]
  intro f _
  have : f = 0 := by
    apply Subtype.ext
    funext x
    rw [Subsingleton.elim x 0]
    exact f.2.2
  rw [this]
  exact Submodule.zero_mem _
end GlobalTheory.ChF
