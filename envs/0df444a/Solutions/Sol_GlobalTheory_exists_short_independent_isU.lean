-- Prove2me | solution 1 for GlobalTheory.exists_short_independent_isU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:22:25.846689+00:00
-- url     : https://prove2.me/submissions/69d9c883-0da6-49c9-b0c5-deb6ff4097b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsShortIndependentIsU
import Theorems.Thm_GlobalTheory_isU_add_shortIndep
import Theorems.Thm_GlobalTheory_isU_zero_shortIndep
import Theorems.Thm_GlobalTheory_isU_zsmul_shortIndep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_exists_isU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_mem_IR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_one_le_abs_im
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_sq_le_Qy_of_le_firstMinimum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace
open GlobalTheory
noncomputable section
namespace GlobalTheory
theorem _root_.solution :
    (∀ (N : ℕ) (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))), DiscreteTopology M → Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ → ∀ lam : ℝ, 0 < lam → (∀ z : EuclideanSpace ℝ (Fin N), (∀ y ∈ M, ∃ k : ℤ, inner ℝ z y = (k : ℝ)) → z ≠ 0 → lam ≤ ‖z‖) → ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ (N : ℝ) ^ 2 / lam) → (∀ (E : Type) [Field E] [NumberField E] (X : PT E) (a : Vsp X.dim), ((∀ y ∈ X.L, (Hf y a).im = 0) → a = 0) ∧ ((∀ y ∈ X.L, ∃ k : ℤ, (Hf y a).im = k) → a ∈ X.L)) → (∀ (E : Type) [Field E] [NumberField E] (X : PT E) (I : Submodule ℤ (Vsp X.dim)), I ≤ X.L → (∀ x ∈ X.L, x ∈ IR I → x ∈ I) → 0 < X.la1 → ∃ x u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim, (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) ∧ LinearIndependent ℝ u ∧ ∀ j, ‖u j‖ ≤ (Module.finrank ℝ (IR I) : ℝ) ^ 2 / X.la1) := by
  intro htrans hpair E _ _ X I hle hsat hla
  set K := IR I with hK
  set N := Module.finrank ℝ K with hNdef
  let e : K ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) := (stdOrthonormalBasis ℝ K).repr
  let M : Submodule ℤ (EuclideanSpace ℝ (Fin N)) :=
    { carrier := {z | ∃ y ∈ X.L, IsU I y ((e.symm z : K) : Vsp X.dim)}
      add_mem' := by
        rintro z z' ⟨y, hy, hu⟩ ⟨y', hy', hu'⟩
        exact ⟨y + y', X.L.add_mem hy hy', by simpa using isU_add_shortIndep hu hu'⟩
      zero_mem' := ⟨0, X.L.zero_mem, by simpa using isU_zero_shortIndep I⟩
      smul_mem' := by
        rintro k z ⟨y, hy, hu⟩
        exact ⟨k • y, X.L.smul_mem k hy, by simpa using isU_zsmul_shortIndep k hu⟩ }
  have hmemM : ∀ y ∈ X.L, ∀ u, IsU I y u → ∃ z ∈ M, ((e.symm z : K) : Vsp X.dim) = u :=
    fun y hy u hu => ⟨e ⟨u, hu.1⟩, ⟨y, hy, by simpa using hu⟩, by simp⟩
  have hinner : ∀ z z' : EuclideanSpace ℝ (Fin N),
      ⟪z, z'⟫_ℝ = ⟪((e.symm z : K) : Vsp X.dim), ((e.symm z' : K) : Vsp X.dim)⟫_ℝ := by
    intro z z'
    rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
  have hnormE : ∀ z, ‖((e.symm z : K) : Vsp X.dim)‖ = ‖z‖ := by
    intro z
    rw [← e.symm.norm_map z]
    rfl
  have hdual : ∀ z : EuclideanSpace ℝ (Fin N), (∀ y ∈ M, ∃ k : ℤ, inner ℝ z y = (k : ℝ)) → ((e.symm z : K) : Vsp X.dim) ∈ I := by
    intro z hz
    apply hsat _ ?_ (e.symm z).2
    apply (hpair E X _).2
    intro y hy
    obtain ⟨u, hu⟩ := exists_isU I y
    obtain ⟨z', hz'M, hz'⟩ := hmemM y hy u hu
    obtain ⟨k, hk⟩ := hz z' hz'M
    refine ⟨k, ?_⟩
    rw [← hu.2 _ (e.symm z).2, ← hk, hinner, hz', real_inner_comm]
  have hspan : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro z hz
    have h0 : ∀ z' ∈ M, ⟪z', z⟫_ℝ = 0 := fun z' hz' =>
      (Submodule.mem_orthogonal _ _).1 hz z' (Submodule.subset_span hz')
    have ha : ((e.symm z : K) : Vsp X.dim) = 0 := by
      apply (hpair E X _).1
      intro y hy
      obtain ⟨u, hu⟩ := exists_isU I y
      obtain ⟨z', hz'M, hz'⟩ := hmemM y hy u hu
      rw [← hu.2 _ (e.symm z).2, ← hz', ← hinner]
      exact h0 z' hz'M
    have : e.symm z = 0 := Subtype.ext ha
    simpa using congrArg e this

  obtain ⟨s, hsI, hsspan, hsli⟩ := exists_linearIndependent ℝ (I : Set (Vsp X.dim))
  have hsfin : s.Finite := hsli.setFinite
  set A := ∑ a ∈ hsfin.toFinset, ‖a‖ + 1 with hA
  have hApos : 0 < A := by
    have : 0 ≤ ∑ a ∈ hsfin.toFinset, ‖a‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  have hlow : ∀ z ∈ M, z ≠ 0 → 1 / A ≤ ‖z‖ := by
    intro z hzM hz0
    obtain ⟨y, hy, hu⟩ := hzM
    set u := ((e.symm z : K) : Vsp X.dim)
    have hu0 : u ≠ 0 := by
      intro h0
      apply hz0
      have : e.symm z = 0 := Subtype.ext h0
      simpa using congrArg e this
    obtain ⟨a, has, ha⟩ : ∃ a ∈ s, ⟪u, a⟫_ℝ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : ∀ w ∈ Submodule.span ℝ s, ⟪u, w⟫_ℝ = 0 := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem x hx => exact hcon x hx
        | zero => exact inner_zero_right _
        | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
        | smul r x _ hx => rw [real_inner_smul_right, hx, mul_zero]
      have h1 := this u (by rw [hsspan]; exact hu.1)
      exact hu0 (inner_self_eq_zero.1 h1)
    have h1 : 1 ≤ |⟪u, a⟫_ℝ| := by
      rw [hu.2 a (mem_IR (hsI has))]
      rw [hu.2 a (mem_IR (hsI has))] at ha
      exact one_le_abs_im X hy (hle (hsI has)) ha
    have h2 : |⟪u, a⟫_ℝ| ≤ ‖u‖ * ‖a‖ := abs_real_inner_le_norm _ _
    have h3 : ‖a‖ ≤ A := by
      have := Finset.single_le_sum (f := fun a => ‖a‖) (fun _ _ => norm_nonneg _)
        ((Set.Finite.mem_toFinset hsfin).2 has)
      linarith
    rw [← hnormE z, div_le_iff₀ hApos]
    nlinarith [norm_nonneg u]
  have hdisc : DiscreteTopology M := by
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
    refine ⟨1 / A, by positivity, fun z hz => ?_⟩
    by_contra hz0
    have h1 := hlow z z.2 (fun h => hz0 (Subtype.ext h))
    rw [dist_zero_right] at hz
    have : ‖(z : EuclideanSpace ℝ (Fin N))‖ = ‖z‖ := rfl
    linarith
  obtain ⟨v, hvM, hvli, hvt⟩ := htrans N M hdisc hspan X.la1 hla (by
    intro z hz hz0
    have ha := hdual z hz
    have hne : ((e.symm z : K) : Vsp X.dim) ≠ 0 := by
      intro h0
      apply hz0
      have : e.symm z = 0 := Subtype.ext h0
      simpa using congrArg e this
    calc X.la1 ≤ ‖((e.symm z : K) : Vsp X.dim)‖ := sq_le_Qy_of_le_firstMinimum X (hle ha) hne
      _ = ‖z‖ := hnormE _)
  choose y hy hyU using hvM
  refine ⟨y, fun j => ((e.symm (v j) : K) : Vsp X.dim), fun j => ⟨hy j, hyU j⟩, ?_, ?_⟩
  · exact (hvli.map' e.symm.toLinearEquiv.toLinearMap (LinearEquiv.ker _)).map' K.subtype
      K.ker_subtype
  · intro j
    rw [hnormE]
    exact hvt j
end GlobalTheory
