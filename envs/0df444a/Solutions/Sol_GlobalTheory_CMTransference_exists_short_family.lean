-- Prove2me | solution 1 for GlobalTheory.CMTransference.exists_short_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:58:38.372326+00:00
-- url     : https://prove2.me/submissions/cc0f8c30-1f79-4378-bcad-277c1c50146a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoveringRadiusStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_CmApproximationTransference
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_transference_dual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMTransference
open NumberField Matrix Module Submodule ReciprocityTheory.MultiplicativeHeights ComplexConjugate
namespace GlobalTheory.CMTransference
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ V) (bd : ι → V)
    (hd : ∀ i j, inner ℝ (b i) (bd j) = if i = j then 1 else 0) (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ span ℤ (Set.range bd), x ≠ 0 → lam ≤ ‖x‖) :
    ∃ y : Fin (finrank ℝ V) → V, (∀ i, y i ∈ span ℤ (Set.range b)) ∧ LinearIndependent ℝ y ∧
      ∀ i, ‖y i‖ ≤ (finrank ℝ V : ℝ) ^ 2 / lam := by
  classical
  set n := finrank ℝ V with hn
  have hcard : Fintype.card ι = n := (finrank_eq_card_basis b).symm
  have hli : LinearIndependent ℝ bd := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (inner ℝ (b i)) hg
    simpa [inner_sum, real_inner_smul_right, hd] using this
  let Bd : Basis ι ℝ V := Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' hcard).ge
  have hBd : ∀ i, Bd i = bd i := fun i => Basis.mk_apply _ _ _
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let φ : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := (stdOrthonormalBasis ℝ V).repr
  let B' : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := (Bd.reindex e).map φ.toLinearEquiv
  have hB' : ∀ j, B' j = φ (bd (e.symm j)) := fun j => by simp [B', hBd]
  have hmin' : ∀ x ∈ span ℤ (Set.range B'), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    have hw : (∑ i, c i • B' i) = φ (∑ i, c i • bd (e.symm i)) := by
      simp [hB', map_sum, map_zsmul]
    have hwmem : (∑ i, c i • bd (e.symm i)) ∈ span ℤ (Set.range bd) :=
      sum_mem fun i _ => zsmul_mem (subset_span (Set.mem_range_self _)) _
    rw [hw, LinearIsometryEquiv.norm_map]
    refine hmin _ hwmem ?_
    intro h0
    apply hx0
    rw [hw, h0, map_zero]
  obtain ⟨y, hyli, hyint, hynorm⟩ := ReciprocityTheory.ChartRestriction.G.T0.transference_dual B' lam hlam hmin'
  let yV : Fin n → V := fun i => φ.symm (y i)
  have hyVint : ∀ i k, ∃ m : ℤ, inner ℝ (yV i) (bd k) = m := by
    intro i k
    obtain ⟨m, hm⟩ := hyint i (e k)
    refine ⟨m, ?_⟩
    rw [← hm, hB', Equiv.symm_apply_apply, ← LinearIsometryEquiv.inner_map_map φ]
    simp [yV]
  have hyVmem : ∀ i, yV i ∈ span ℤ (Set.range b) := by
    intro i
    have hrep : ∀ k, b.repr (yV i) k = inner ℝ (yV i) (bd k) := by
      intro k
      have h : inner ℝ (yV i) (bd k) = ∑ l, b.repr (yV i) l * inner ℝ (b l) (bd k) := by
        conv_lhs => rw [← b.sum_repr (yV i)]
        rw [sum_inner]
        simp_rw [real_inner_smul_left]
      rw [h]
      simp [hd]
    rw [← b.sum_repr (yV i)]
    refine sum_mem fun k _ => ?_
    obtain ⟨m, hm⟩ := hyVint i k
    rw [hrep, hm, Int.cast_smul_eq_zsmul]
    exact zsmul_mem (subset_span (Set.mem_range_self k)) m
  refine ⟨yV, hyVmem, hyli.map' φ.symm.toLinearEquiv.toLinearMap φ.symm.toLinearEquiv.ker,
    fun i => ?_⟩
  have : ‖yV i‖ = ‖y i‖ := by simp [yV]
  rw [this]
  exact hynorm i
end GlobalTheory.CMTransference
