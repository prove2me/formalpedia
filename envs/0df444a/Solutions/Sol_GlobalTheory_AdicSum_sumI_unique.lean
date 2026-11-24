-- Prove2me | solution 1 for GlobalTheory.AdicSum.sumI_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:55:30.795937+00:00
-- url     : https://prove2.me/submissions/8b46f1d8-6d38-423c-96c6-aa89b3019852

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SumFCalculus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
open GlobalTheory GlobalTheory.AdicSum
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E']
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E']
namespace GlobalTheory.AdicSum
namespace _root_.GlobalTheory.AdicSum
theorem _root_.solution [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥)
    {x : Ix → E} {s s' : E}
    (h : _root_.GlobalTheory.UT.SumI I x s) (h' : _root_.GlobalTheory.UT.SumI I x s') : s = s' := by
  classical
  obtain ⟨N, hN, hs, -, hconv⟩ := h
  obtain ⟨N', hN', hs', -, hconv'⟩ := h'
  set M := N ⊔ N' with hM
  have hMfg : M.FG := hN.sup hN'
  haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hMfg
  have hmem : s - s' ∈ M := M.sub_mem (Submodule.mem_sup_left hs) (Submodule.mem_sup_right hs')
  have hpow : ∀ n : ℕ, (⟨s - s', hmem⟩ : M) ∈ I ^ n • (⊤ : Submodule R M) := by
    intro n
    obtain ⟨S, hS⟩ := hconv n
    obtain ⟨S', hS'⟩ := hconv' n
    have h1 := hS (S ∪ S') Finset.subset_union_left
    have h2 := hS' (S ∪ S') Finset.subset_union_right
    have h3 : s - s' ∈ I ^ n • M := by
      have e : s - s' = (s - ∑ i ∈ S ∪ S', x i) - (s' - ∑ i ∈ S ∪ S', x i) := by abel
      rw [e]
      exact Submodule.sub_mem _ (Submodule.smul_mono le_rfl le_sup_left h1)
        (Submodule.smul_mono le_rfl le_sup_right h2)
    rw [← Submodule.map_subtype_top M, ← Submodule.map_smul''] at h3
    obtain ⟨y, hy, hyeq⟩ := h3
    have hy' : y = ⟨s - s', hmem⟩ := Subtype.ext hyeq
    rwa [← hy']
  have h0 : (⟨s - s', hmem⟩ : M) = 0 := by
    have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) I hI
    rw [← Submodule.mem_bot R, ← hK, Submodule.mem_iInf]
    exact hpow
  exact sub_eq_zero.mp (congrArg Subtype.val h0)
end _root_.GlobalTheory.AdicSum
end GlobalTheory.AdicSum
