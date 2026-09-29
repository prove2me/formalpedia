-- Prove2me | solution 1 for M4aLocalCFT.unitsDecomp_herbrandQuotient_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/391e97e6-3738-5d22-a6ba-9c2d456fe48e

import Definitions.Def_M4aLocalCFT_VocabDefs
import Theorems.Thm_M4aLocalCFT_herbrandQuotient_eq_one_of_cohTrivial_finiteIndex
import Theorems.Thm_M4aLocalCFT_unitsDecomp_exists_cohTrivial_finiteIndex
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aLocalCFT_unitsDecomp_herbrandQuotient_eq_one

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsLocalRing

namespace M4aLocalCFT
p2m_export "M4aLocalCFT" "unitsAct unitsNorm unitsDerive herbrandQuotient_eq_one_of_cohTrivial_finiteIndex unitsDecomp_exists_cohTrivial_finiteIndex"
p2m_open "M4aLocalCFT"

namespace UnitsHerbrand

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L)
variable [Finite (A.decompositionSubgroup K)]

attribute [local instance] Fintype.ofFinite

local notation "G" => (ValuationSubring.decompositionSubgroup K A)

variable (K) in
theorem unitsNorm_apply (u : Aˣ) : unitsNorm (K := K) A u = ∏ s : G, unitsAct A s u := by
  simp only [unitsNorm, MonoidHom.finsetProd_apply]

variable (K) in
theorem unitsAct_mul (s t : G) (u : Aˣ) :
    unitsAct A (s * t) u = unitsAct A s (unitsAct A t u) := by
  ext
  exact congrArg (fun a : A => (a : L)) (mul_smul s t (u : A))

variable (K) in
theorem unitsDerive_apply (g : G) (u : Aˣ) : unitsDerive A g u = unitsAct A g u / u := by
  simp [unitsDerive, MonoidHom.div_apply]

variable (K) in
theorem unitsAct_norm (g : G) (u : Aˣ) :
    unitsAct A g (unitsNorm (K := K) A u) = unitsNorm (K := K) A u := by
  rw [unitsNorm_apply, map_prod]
  simp_rw [← unitsAct_mul]
  exact Fintype.prod_bijective _ (Group.mulLeft_bijective g) _ _ fun _ => rfl

variable (K) in
theorem norm_unitsAct (g : G) (u : Aˣ) :
    unitsNorm (K := K) A (unitsAct A g u) = unitsNorm (K := K) A u := by
  rw [unitsNorm_apply, unitsNorm_apply]
  simp_rw [← unitsAct_mul]
  exact Fintype.prod_bijective _ (Group.mulRight_bijective g) _ _ fun _ => rfl

variable (K) in
theorem derive_norm (g : G) (u : Aˣ) : unitsDerive A g (unitsNorm (K := K) A u) = 1 := by
  rw [unitsDerive_apply, unitsAct_norm, div_self']

variable (K) in
theorem norm_derive (g : G) (u : Aˣ) : unitsNorm (K := K) A (unitsDerive A g u) = 1 := by
  rw [unitsDerive_apply, map_div, norm_unitsAct, div_self']

end UnitsHerbrand

end M4aLocalCFT

open _root_.M4aLocalCFT _root_.P2MW.S_M4aLocalCFT_unitsDecomp_herbrandQuotient_eq_one.M4aLocalCFT M4aLocalCFT.UnitsHerbrand in
theorem solution
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
    [Finite (IsLocalRing.ResidueField A)]
    [Finite (A.decompositionSubgroup K)] [IsCyclic (A.decompositionSubgroup K)]
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ((unitsDerive A g).ker ⧸
      ((unitsNorm (K := K) A).range.subgroupOf (unitsDerive A g).ker)) =
    Nat.card ((unitsNorm (K := K) A).ker ⧸
      ((unitsDerive A g).range.subgroupOf (unitsNorm (K := K) A).ker)) ∧
    Nat.card ((unitsDerive A g).ker ⧸
      ((unitsNorm (K := K) A).range.subgroupOf (unitsDerive A g).ker)) ≠ 0 := by
  obtain ⟨V, hVfi, hVact, h0, h1⟩ :=
    M4aLocalCFT.unitsDecomp_exists_cohTrivial_finiteIndex (K := K) A g hg
  haveI := hVfi
  have hDV : ∀ v ∈ V, unitsDerive A g v ∈ V := by
    intro v hv
    rw [unitsDerive_apply]
    exact div_mem (hVact g v hv) hv
  have hNV : ∀ v ∈ V, unitsNorm (K := K) A v ∈ V := by
    intro v hv
    letI := Fintype.ofFinite (A.decompositionSubgroup K)
    rw [unitsNorm_apply]
    exact prod_mem fun s _ => hVact s v hv
  exact M4aLocalCFT.herbrandQuotient_eq_one_of_cohTrivial_finiteIndex
    (unitsDerive A g) (unitsNorm (K := K) A) (derive_norm K A g) (norm_derive K A g)
    V hDV hNV h0 h1

end S_M4aLocalCFT_unitsDecomp_herbrandQuotient_eq_one
end P2MW
export P2MW.S_M4aLocalCFT_unitsDecomp_herbrandQuotient_eq_one (solution)
