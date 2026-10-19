-- Prove2me | solution 1 for OAI.RecursivePotentials.EquivalentNorm.bounded_tree_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:53:45.613904+00:00
-- url     : https://prove2.me/submissions/df43d5e0-5e17-44de-bf75-62bfdbf7ca5a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/EquivalentNorms.lean:L209-L260
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.EquivalentNorm.bounded_tree_step. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms

-- ---- from OAI.Analysis.RecursivePotentials.TreeGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

namespace FiniteRootedTree

section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

end

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace CofiniteSubspace

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma nontrivial_space (F : CofiniteSubspace E) (hE : ¬Module.Finite ℝ E) :
    Nontrivial F.space := by
  by_contra hn
  have : Subsingleton F.space := not_nontrivial_iff_subsingleton.mp hn
  let := F.finiteQuotient
  exact hE (Module.Finite.of_submodule_quotient F.space)

lemma exists_unit (F : CofiniteSubspace E) (hE : ¬Module.Finite ℝ E) :
    ∃ y ∈ F.space, ‖y‖ = 1 := by
  have := F.nontrivial_space hE
  obtain ⟨y, hy⟩ := exists_norm_eq F.space (by norm_num : (0 : ℝ) ≤ 1)
  exact ⟨y, y.2, hy⟩

end CofiniteSubspace

section Moduli

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Moduli

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

end RecursivePotentials

end

end OAI

-- ---- from OAI.Analysis.RecursivePotentials.EquivalentNorms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

lemma WeaklyNull.quotient_tendsto {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ → E} (hd : WeaklyNull d) (F : CofiniteSubspace E) :
    Tendsto (fun k => F.space.mkQL (d k)) atTop (𝓝 0) := by
  let : IsClosed (F.space : Set E) := F.closed
  let := F.finiteQuotient
  let b := Module.finBasis ℝ (E ⧸ F.space)
  let e := b.equivFunL
  have he : Tendsto (fun k => e (F.space.mkQL (d k))) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact hd (((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap).comp F.space.mkQL)
  have hi := e.symm.continuous.continuousAt.tendsto.comp he
  simpa only [Function.comp_def, e.symm_apply_apply, map_zero] using hi

lemma WeaklyNull.approximate_cofinite {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ → E} (hd : WeaklyNull d) (F : CofiniteSubspace E) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∃ w ∈ F.space, ‖d k - w‖ < ε := by
  have hn := (hd.quotient_tendsto F).norm
  simp only [norm_zero] at hn
  have hev : ∀ᶠ k in atTop, ‖F.space.mkQL (d k)‖ < ε / 2 :=
    hn.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hev] with k hk
  obtain ⟨v, hv, hnv⟩ := Submodule.Quotient.norm_mk_lt (F.space.mkQL (d k)) (half_pos hε)
  refine ⟨d k - v, ?_, ?_⟩
  · rw [← F.space.ker_mkQ]
    change F.space.mkQ (d k - v) = 0
    rw [map_sub]
    change F.space.mkQL (d k) - Submodule.Quotient.mk v = 0
    rw [hv, sub_self]
  · have he : d k - (d k - v) = v := by abel
    rw [he]
    linarith

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

lemma upper_pos : 0 < A.upper := A.lower_pos.trans_le A.lower_le_upper

lemma nonneg (x : E) : 0 ≤ A.N x := apply_nonneg _ _

lemma pos {x : E} (hx : x ≠ 0) : 0 < A.N x :=
  (mul_pos A.lower_pos (norm_pos_iff.mpr hx)).trans_le (A.lower_bound x)

lemma sub_le (x y : E) : A.N x - A.N y ≤ A.N (x - y) := by
  have h := map_add_le_add A.N (x - y) y
  rw [sub_add_cancel] at h
  linarith

lemma exists_unit (F : CofiniteSubspace E) (hE : ¬Module.Finite ℝ E) :
    ∃ y ∈ F.space, A.N y = 1 := by
  obtain ⟨x, hx, hxn⟩ := F.exists_unit hE
  have hx0 : x ≠ 0 := by intro he; simp [he] at hxn
  have hp := A.pos hx0
  refine ⟨(A.N x)⁻¹ • x, F.space.smul_mem _ hx, ?_⟩
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']

lemma inner_nonempty (x : E) (t : ℝ) (F : CofiniteSubspace E)
    (hE : ¬Module.Finite ℝ E) :
    {r : ℝ | ∃ y ∈ F.space, A.N y = 1 ∧ r = A.N (x + t • y) - 1}.Nonempty := by
  obtain ⟨y, hy, hy1⟩ := A.exists_unit F hE
  exact ⟨_, y, hy, hy1, rfl⟩

lemma inner_bddBelow (x : E) (t : ℝ) (F : CofiniteSubspace E) :
    BddBelow {r : ℝ | ∃ y ∈ F.space, A.N y = 1 ∧ r = A.N (x + t • y) - 1} := by
  refine ⟨-1, ?_⟩
  rintro r ⟨y, hy, hy1, rfl⟩
  linarith [A.nonneg (x + t • y)]

lemma inner_lower (x : E) (t : ℝ) (F : CofiniteSubspace E)
    (hE : ¬Module.Finite ℝ E) : -1 ≤ A.inner x t F := by
  apply le_csInf (A.inner_nonempty x t F hE)
  rintro r ⟨y, hy, hy1, rfl⟩
  linarith [A.nonneg (x + t • y)]

lemma inner_upper {x : E} (hx : A.N x = 1) {t : ℝ} (ht : 0 ≤ t)
    (F : CofiniteSubspace E) (hE : ¬Module.Finite ℝ E) : A.inner x t F ≤ t := by
  obtain ⟨y, hy, hy1⟩ := A.exists_unit F hE
  have hi : A.inner x t F ≤ A.N (x + t • y) - 1 :=
    csInf_le (A.inner_bddBelow x t F) ⟨y, hy, hy1, rfl⟩
  have h := map_add_le_add A.N x (t • y)
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht, hx, hy1, mul_one] at h
  linarith

lemma modulus_le_sup {x : E} (hx : A.N x = 1) {t : ℝ} (ht : 0 ≤ t)
    (hE : ¬Module.Finite ℝ E) : A.modulus t ≤ sSup (Set.range (A.inner x t)) := by
  have hlower : BddBelow {r : ℝ | ∃ x : E, A.N x = 1 ∧
      r = sSup (Set.range (A.inner x t))} := by
    refine ⟨-1, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    have hb : BddAbove (Set.range (A.inner x t)) := by
      refine ⟨t, ?_⟩
      rintro r ⟨F, rfl⟩
      exact A.inner_upper hx ht F hE
    exact (A.inner_lower x t CofiniteSubspace.top hE).trans
      (le_csSup hb (Set.mem_range_self _))
  exact csInf_le hlower ⟨x, hx, rfl⟩

lemma witness {t γ : ℝ} (ht : 0 ≤ t) (hγ : γ < A.modulus t)
    (hE : ¬Module.Finite ℝ E) (x : E) (hx : A.N x = 1) :
    ∃ F : CofiniteSubspace E, ∀ y ∈ F.space, A.N y = 1 →
      1 + γ ≤ A.N (x + t • y) := by
  have hs : γ < sSup (Set.range (A.inner x t)) :=
    hγ.trans_le (A.modulus_le_sup hx ht hE)
  obtain ⟨r, ⟨F, rfl⟩, hF⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hs
  refine ⟨F, ?_⟩
  intro y hy hy1
  have hi : A.inner x t F ≤ A.N (x + t • y) - 1 :=
    csInf_le (A.inner_bddBelow x t F) ⟨y, hy, hy1, rfl⟩
  linarith

lemma extend_radius {x y : E} (hx : A.N x = 1) (_hy : A.N y = 1)
    {t r γ : ℝ} (ht : 0 < t) (htr : t ≤ r) (hγ : 0 ≤ γ)
    (hg : 1 + γ ≤ A.N (x + t • y)) : 1 + γ ≤ A.N (x + r • y) := by
  have hr : 0 < r := ht.trans_le htr
  have hscale : x + t • y = (t / r) • (x + r • y) + (1 - t / r) • x := by
    rw [smul_add, smul_smul, div_mul_cancel₀ t hr.ne']
    module
  have hle := map_add_le_add A.N ((t / r) • (x + r • y)) ((1 - t / r) • x)
  rw [← hscale, map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg ht.le hr.le), abs_of_nonneg (sub_nonneg.mpr
      ((div_le_one hr).mpr htr)), hx, mul_one] at hle
  have hdiv : 0 < t / r := div_pos ht hr
  have hdiv1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  nlinarith

lemma long_perturbation {u w : E} (hu : u ≠ 0) {t γ : ℝ} (ht : 0 < t) (hγ : 0 ≤ γ)
    (F : CofiniteSubspace E) (hw : w ∈ F.space) (hwn : t * A.N u ≤ A.N w)
    (hF : ∀ y ∈ F.space, A.N y = 1 →
      1 + γ ≤ A.N ((A.N u)⁻¹ • u + t • y)) :
    (1 + γ) * A.N u ≤ A.N (u + w) := by
  have hu0 := A.pos hu
  have hw0 : 0 < A.N w := (mul_pos ht hu0).trans_le hwn
  have hunitu : A.N ((A.N u)⁻¹ • u) = 1 := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu0), inv_mul_cancel₀ hu0.ne']
  have hunitw : A.N ((A.N w)⁻¹ • w) = 1 := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw0), inv_mul_cancel₀ hw0.ne']
  have hg := A.extend_radius hunitu hunitw ht ((le_div_iff₀ hu0).mpr hwn) hγ
    (hF _ (F.space.smul_mem _ hw) hunitw)
  have he : (A.N u)⁻¹ • u + (A.N w / A.N u) • ((A.N w)⁻¹ • w) =
      (A.N u)⁻¹ • (u + w) := by
    rw [smul_smul, div_eq_mul_inv, mul_assoc, mul_comm (A.N u)⁻¹,
      ← mul_assoc, mul_inv_cancel₀ hw0.ne', one_mul, smul_add]
  rw [he, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu0)] at hg
  calc
    (1 + γ) * A.N u ≤ ((A.N u)⁻¹ * A.N (u + w)) * A.N u :=
      mul_le_mul_of_nonneg_right hg hu0.le
    _ = A.N (u + w) := by field_simp

lemma bounded_tree_step (hE : ¬Module.Finite ℝ E) {u : E} (hu : u ≠ 0)
    (d : ℕ → E) (hd : WeaklyNull d) {M c γ : ℝ} (hM : 0 < M) (hc : 0 < c)
    (huM : ‖u‖ ≤ M) (hdc : ∀ k, c ≤ ‖d k‖) (hγ : 0 < γ)
    (hmod : γ < A.modulus (A.lower * c / (2 * A.upper * M))) :
    ∃ k, (1 + γ / 2) * A.N u ≤ A.N (u + d k) := by
  have hu0 := A.pos hu
  have hU0 := A.upper_pos.ne'
  let t := A.lower * c / (2 * A.upper * M)
  have ht : 0 < t := div_pos (mul_pos A.lower_pos hc) (by have := A.upper_pos; positivity)
  have hunit : A.N ((A.N u)⁻¹ • u) = 1 := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu0), inv_mul_cancel₀ hu0.ne']
  obtain ⟨F, hF⟩ := A.witness ht.le hmod hE _ hunit
  let ε := min (A.lower * c / (2 * A.upper)) (γ * A.N u / (2 * A.upper))
  have hε : 0 < ε := lt_min
    (div_pos (mul_pos A.lower_pos hc) (by have := A.upper_pos; positivity))
    (div_pos (mul_pos hγ hu0) (by have := A.upper_pos; positivity))
  obtain ⟨k, w, hw, hdw⟩ := (hd.approximate_cofinite F hε).exists
  have herror₁ : A.upper * ‖d k - w‖ < A.lower * c / 2 := by
    have hh := lt_of_lt_of_le hdw (min_le_left _ _)
    have he : A.upper * (A.lower * c / (2 * A.upper)) = A.lower * c / 2 := by
      field_simp [hU0, hM.ne']
    calc
      A.upper * ‖d k - w‖ < A.upper * (A.lower * c / (2 * A.upper)) :=
        mul_lt_mul_of_pos_left hh A.upper_pos
      _ = _ := he
  have herror₂ : A.upper * ‖d k - w‖ < γ * A.N u / 2 := by
    have hh := lt_of_lt_of_le hdw (min_le_right _ _)
    have he : A.upper * (γ * A.N u / (2 * A.upper)) = γ * A.N u / 2 := by
      field_simp [hU0, hM.ne']
    calc
      A.upper * ‖d k - w‖ < A.upper * (γ * A.N u / (2 * A.upper)) :=
        mul_lt_mul_of_pos_left hh A.upper_pos
      _ = _ := he
  have hwc : A.lower * c / 2 ≤ A.N w := by
    have hb := A.lower_bound (d k)
    have hc' := mul_le_mul_of_nonneg_left (hdc k) A.lower_pos.le
    have he := (A.sub_le (d k) w).trans (A.upper_bound (d k - w))
    linarith
  have hut : t * A.N u ≤ A.lower * c / 2 := by
    have hub := (A.upper_bound u).trans (mul_le_mul_of_nonneg_left huM A.upper_pos.le)
    have he : t * (A.upper * M) = A.lower * c / 2 := by
      dsimp [t]
      field_simp [hU0, hM.ne']
    exact (mul_le_mul_of_nonneg_left hub ht.le).trans_eq he
  have hwgain := A.long_perturbation hu ht hγ.le F hw (hut.trans hwc) hF
  have hdif := A.sub_le (u + w) (u + d k)
  have he : (u + w) - (u + d k) = w - d k := by abel
  rw [he] at hdif
  have hb := A.upper_bound (w - d k)
  rw [norm_sub_rev] at hb
  refine ⟨k, ?_⟩
  nlinarith

end EquivalentNorm

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

end

end TreeSpace

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

end

end TreeSpace

namespace ZeroTreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

end

end ZeroTreeSpace

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

end EquivalentNorm

end RecursivePotentials

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.EquivalentNorm
open scoped BigOperators
open Filter Topology


theorem solution.{uSpace} : type_of% @_root_.OAI.RecursivePotentials.EquivalentNorm.bounded_tree_step.{uSpace} := @_root_.OAI.RecursivePotentials.EquivalentNorm.bounded_tree_step.{uSpace}
