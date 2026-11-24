-- Prove2me | solution 1 for GlobalTheory.SW.WeilLevel.relIndex_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:04.896955+00:00
-- url     : https://prove2.me/submissions/c0f89393-1c5b-444c-ac3b-a0ed40baa2a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.WeilLevel
noncomputable section
namespace GlobalTheory.SW.WeilLevel
theorem _root_.solution {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
    (L : AddSubgroup (Matrix κ ι K)) {j : ℕ} (hj : 0 < j) (hL : ∀ x ∈ L, IntM ((j : K) • x))
    {m : ℕ} (hm : 0 < m) :
    (L.map (nsmulAddMonoidHom m)).relIndex L ≠ 0 ∧ (L.map (nsmulAddMonoidHom m)).relIndex L ≤
      m ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) := by
  let f : L →+ Matrix κ ι (𝓞 K) :=
    { toFun := fun x => Matrix.of fun k i => ⟨((j : K) • x.1) k i, hL x.1 x.2 k i⟩
      map_zero' := by
        ext k i
        change ((j : K) • (0 : Matrix κ ι K)) k i = 0
        simp
      map_add' := fun x y => by
        ext k i
        change ((j : K) • (x.1 + y.1)) k i = ((j : K) • x.1) k i + ((j : K) • y.1) k i
        rw [smul_add]; rfl }
  have hj' : (j : K) ≠ 0 := by exact_mod_cast hj.ne'
  have hf : Function.Injective f.toIntLinearMap := by
    intro x y hxy
    ext k i
    have : ((j : K) • x.1) k i = ((j : K) • y.1) k i :=
      congrArg Subtype.val (congrFun (congrFun hxy k) i)
    exact mul_left_cancel₀ hj' this
  haveI : Module.Finite ℤ L := Module.Finite.of_injective _ hf
  haveI : Module.IsTorsionFree ℤ L := hf.moduleIsTorsionFree _ (fun _ _ => map_smul _ _ _)
  have hr := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_matrix, RingOfIntegers.rank] at hr
  have : (L.map (nsmulAddMonoidHom m)).relIndex L = m ^ Module.finrank ℤ L := by
    rw [← AddSubgroup.index_range_nsmul, AddSubgroup.relIndex]
    congr 1
    ext x
    simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, AddMonoidHom.mem_range,
      nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨y, hy, e⟩; exact ⟨⟨y, hy⟩, Subtype.ext e⟩
    · rintro ⟨y, rfl⟩; exact ⟨y.1, y.2, rfl⟩
  rw [this]
  exact ⟨by positivity, Nat.pow_le_pow_right hm (by rw [mul_comm]; exact hr)⟩
end GlobalTheory.SW.WeilLevel
