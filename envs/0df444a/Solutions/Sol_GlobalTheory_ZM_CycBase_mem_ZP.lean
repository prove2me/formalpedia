-- Prove2me | solution 1 for GlobalTheory.ZM.CycBase.mem_ZP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:27.766249+00:00
-- url     : https://prove2.me/submissions/6e34fc54-dfd3-44ea-be46-7fdcc44ff986

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCyclotomicBaseRingInvertingPrime
import Theorems.Thm_GlobalTheory_ZM_CycBase_zF_prim
import Theorems.Thm_GlobalTheory_ZM_CycBase_cyc

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
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.CycBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.ZM.CycBase
namespace _root_.GlobalTheory.ZM.CycBase
theorem _root_.solution (p n e : ℕ) (hn : n.Prime) (a : 𝓞 (_root_.GlobalTheory.ZM.CycBase.CF (n ^ e))) :
    ((a : _root_.GlobalTheory.ZM.CycBase.CF (n ^ e)) : ℂ) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e) := by
  haveI : Fact n.Prime := ⟨hn⟩
  haveI : NeZero (n ^ e) := ⟨pow_ne_zero _ hn.ne_zero⟩
  haveI := _root_.GlobalTheory.ZM.CycBase.cyc (k := n ^ e)
  have hζ := _root_.GlobalTheory.ZM.CycBase.zF_prim (NeZero.ne (n ^ e))
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow hζ
  obtain ⟨x, hx⟩ := hcl.isIntegral_iff.mp (RingOfIntegers.isIntegral_coe a)
  have hax : (a : _root_.GlobalTheory.ZM.CycBase.CF (n ^ e)) = x := hx.symm
  rw [hax]
  obtain ⟨y, hmem⟩ := x
  change ((y : _root_.GlobalTheory.ZM.CycBase.CF (n ^ e)) : ℂ) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)
  clear hx hax
  induction hmem using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff.mp hy]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP
    exact Subring.subset_closure (Or.inl rfl)
  | algebraMap r =>
    simpa using intCast_mem (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p (n ^ e)) r
  | add y z _ _ hy hz => simpa using add_mem hy hz
  | mul y z _ _ hy hz => simpa using mul_mem hy hz
end _root_.GlobalTheory.ZM.CycBase
end GlobalTheory.ZM.CycBase
