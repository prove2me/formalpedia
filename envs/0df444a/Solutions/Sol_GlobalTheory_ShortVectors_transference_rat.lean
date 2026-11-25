-- Prove2me | solution 1 for GlobalTheory.ShortVectors.transference_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:56:56.381913+00:00
-- url     : https://prove2.me/submissions/dbf50811-3cfa-4d33-892a-00348d9342f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Theorems.Thm_GlobalTheory_ShortVectors_exists_euclidean
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_transference_dual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open GlobalTheory
open GlobalTheory.ShortVectors
variable {V : Type} [AddCommGroup V] [Module ℚ V]
namespace GlobalTheory.ShortVectors
theorem _root_.solution {M : ℕ} (b : Basis (Fin M) ℚ V)
    (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm) (hp : ∀ x, 0 ≤ B x x) (hn : B.Nondegenerate)
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ u, u ≠ 0 → (∀ j, ∃ k : ℤ, B u (b j) = k) → lam ^ 2 ≤ (B u u : ℝ)) :
    ∃ v : Fin M → V, (∀ i, v i ∈ span ℤ (Set.range b)) ∧ LinearIndependent ℚ v ∧
      ∀ i, (B (v i) (v i) : ℝ) ≤ ((M : ℝ) ^ 2 / lam) ^ 2 := by
  classical
  have : FiniteDimensional ℚ V := b.finiteDimensional_of_finite
  have hM : finrank ℚ V = M := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  obtain ⟨φ, hφ⟩ := exists_euclidean hM B hs hp
  let bd := B.dualBasis hn b
  have hd1 : ∀ i j, B (bd i) (b j) = if j = i then 1 else 0 := fun i j =>
    LinearMap.BilinForm.apply_dualBasis_left hn b i j
  have hd2 : ∀ i j, inner ℝ (φ (bd i)) (φ (b j)) = if j = i then 1 else 0 := by
    intro i j
    rw [hφ, hd1]
    split_ifs <;> simp
  have hd3 : ∀ i j, inner ℝ (φ (b j)) (φ (bd i)) = if j = i then 1 else 0 := by
    intro i j
    rw [real_inner_comm]
    exact hd2 i j
  have hli : LinearIndependent ℝ (fun i => φ (bd i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg (fun z => inner ℝ z (φ (b i))) hg
    simp only [sum_inner, real_inner_smul_left, hd2, inner_zero_left, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    exact h
  let b' : Basis (Fin M) ℝ (EuclideanSpace ℝ (Fin M)) :=
    basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp)
  have hb' : ∀ i, b' i = φ (bd i) := fun i => by simp [b']
  have hint : ∀ u ∈ Submodule.span ℤ (Set.range bd), ∀ j, ∃ k : ℤ, B u (b j) = k := by
    intro u hu j
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨if j = i then 1 else 0, by rw [hd1]; split_ifs <;> simp⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨k1, h1⟩ := hx
      obtain ⟨k2, h2⟩ := hy
      exact ⟨k1 + k2, by rw [map_add, LinearMap.add_apply, h1, h2]; push_cast; ring⟩
    | smul a x _ hx =>
      obtain ⟨k, h⟩ := hx
      exact ⟨a * k, by rw [map_zsmul, LinearMap.smul_apply, h, zsmul_eq_mul]; push_cast; ring⟩
  have hmin' : ∀ x ∈ Submodule.span ℤ (Set.range b'), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    have hr : Set.range b' = φ.toAddMonoidHom.toIntLinearMap '' Set.range bd := by
      rw [← Set.range_comp]
      ext z
      simp [hb']
    rw [hr, ← Submodule.map_span] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hx0
    have h1 := hmin u hu0 (hint u hu)
    have h2 : (B u u : ℝ) = ‖φ u‖ ^ 2 := by rw [← hφ, real_inner_self_eq_norm_sq]
    rw [h2] at h1
    have h3 : 0 ≤ ‖φ u‖ := norm_nonneg _
    change lam ≤ ‖φ u‖
    nlinarith
  obtain ⟨y, hyli, hyint, hynorm⟩ := ReciprocityTheory.ChartRestriction.G.T0.transference_dual b' lam hlam hmin'
  choose m hm using hyint
  have hyv : ∀ i, φ (∑ j, (m i j : ℚ) • b j) = y i := by
    intro i
    refine InnerProductSpace.ext_inner_right_basis b' fun k => ?_
    rw [hm, hb', map_sum, sum_inner]
    simp only [map_smul, ← Rat.cast_smul_eq_qsmul ℝ, real_inner_smul_left, hd3, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Rat.cast_intCast]
  refine ⟨fun i => ∑ j, (m i j : ℚ) • b j, fun i => ?_, ?_, fun i => ?_⟩
  · refine Submodule.sum_mem _ fun j _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg φ hg
    rw [map_sum, map_zero] at h
    simp only [map_smul, hyv, ← Rat.cast_smul_eq_qsmul ℝ] at h
    have := (Fintype.linearIndependent_iff.mp hyli) (fun i => (g i : ℝ)) h i
    exact_mod_cast this
  · rw [← hφ, hyv, real_inner_self_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hynorm i) 2
end GlobalTheory.ShortVectors
