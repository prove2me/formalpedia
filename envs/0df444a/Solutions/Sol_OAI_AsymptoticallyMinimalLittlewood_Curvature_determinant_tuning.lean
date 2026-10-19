-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Curvature.determinant_tuning
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:12:53.316346+00:00
-- url     : https://prove2.me/submissions/efea7beb-ad2c-4d33-9b76-13d5626f1fd5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Curvature.lean:L54-L121
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Curvature.determinant_tuning. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket

-- ---- from OAI.Analysis.Littlewood.Curvature ----
namespace OAI

universe uV uI

namespace AsymptoticallyMinimalLittlewood
namespace Curvature
noncomputable section
open scoped BigOperators Topology
open Filter

lemma separating_kernel {V : Type uV} [AddCommGroup V] [Module ℝ V]
    (f g : V →ₗ[ℝ] ℝ) (hf : f ≠ 0) (hfg : ∀ c : ℝ, g ≠ c • f) :
    ∃ x, f x = 0 ∧ g x ≠ 0 := by
  obtain ⟨e,he⟩ : ∃ e, f e ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext h)
  by_contra h
  push Not at h
  apply hfg (g e/f e)
  ext x
  have hz : f (x-(f x/f e) • e) = 0 := by simp [he]
  have hg := h (x-(f x/f e) • e) hz
  simp only [map_sub, map_smul, LinearMap.smul_apply, smul_eq_mul] at hg ⊢
  field_simp [he] at hg ⊢
  nlinarith

lemma exists_generic {I : Type uI} {V : Type uV} [Finite I] [AddCommGroup V] [Module ℝ V]
    (f : I → V →ₗ[ℝ] ℝ) (hf : ∀ i, f i ≠ 0) :
    ∃ x, ∀ i, f i x ≠ 0 := by
  apply Module.Dual.exists_forall_ne_zero_of_forall_exists
  intro i
  by_contra hn
  push Not at hn
  exact hf i (LinearMap.ext hn)

lemma exists_kernel_vectors {I : Type uI} {V : Type uV} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [Module ℝ V] (f : I → V →ₗ[ℝ] ℝ)
    (hf : ∀ i, f i ≠ 0) (hpair : ∀ i j, i ≠ j → ∀ c : ℝ, f i ≠ c • f j) :
    ∃ b : I → V, (∀ i, f i (b i) = 0) ∧ (∀ i j, i ≠ j → f i (b j) ≠ 0) := by
  have h (j : I) : ∃ x, f j x=0 ∧ ∀ i, i ≠ j → f i x ≠ 0 := by
    let J := {i : I // i ≠ j}
    obtain ⟨x,hx,hall⟩ := Module.Dual.exists_forall_mem_ne_zero_of_forall_exists
      (LinearMap.ker (f j)) (fun i : J ↦ f i.val) (by
        intro i
        obtain ⟨y,hy,hy'⟩ := separating_kernel (f j) (f i.val) (hf j) (hpair _ _ i.property)
        exact ⟨y,hy,hy'⟩)
    exact ⟨x,hx,fun i hi ↦ hall ⟨i,hi⟩⟩
  choose b hb hc using h
  exact ⟨b,hb,fun i j hij ↦ hc j i hij⟩

/-- Given any prescribed positive factors A_i, the products of curvatures
can be made simultaneously (1±delta) tau A_i, with all curvatures nonzero.
The theorem is used with A_i=|c_i|^2/rho_i. -/
theorem determinant_tuning {I : Type uI} {V : Type uV} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : I → V →ₗ[ℝ] ℝ) (hf : ∀ i, f i ≠ 0)
    (hpair : ∀ i j, i ≠ j → ∀ c : ℝ, f i ≠ c • f j)
    (A : I → ℝ) (hA : ∀ i, 0 < A i) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ b : I → V,
      (∀ i j, f i (b j) ≠ 0) ∧
      ∀ i, (1-δ)*τ*A i ≤ ∏ j, |f i (b j)| ∧
        (∏ j, |f i (b j)|) ≤ (1+δ)*τ*A i := by
  obtain ⟨b0,hb0,hb0'⟩ := exists_kernel_vectors f hf hpair
  obtain ⟨e,he⟩ := exists_generic f hf
  let P0 (i : I) : ℝ := ∏ j ∈ Finset.univ.erase i, |f i (b0 j)|
  have hP0 (i : I) : 0 < P0 i := by
    apply Finset.prod_pos
    intro j hj
    exact abs_pos.mpr (hb0' i j (Finset.ne_of_mem_erase hj).symm)
  let b1 (i : I) : V := (A i/(f i e*P0 i)) • e
  have hb1 (i : I) : f i (b1 i) = A i/P0 i := by
    dsimp [b1]
    rw [map_smul, smul_eq_mul]
    field_simp [he i, (hP0 i).ne']
  let b (t : ℝ) (j : I) : V := b0 j+t • b1 j
  let P (i : I) (t : ℝ) : ℝ := |f i (b1 i)| * ∏ j ∈ Finset.univ.erase i, |f i (b t j)|
  have hP (i : I) : Continuous (P i) := by
    dsimp [P,b]
    have hh := (f i).continuous_of_finiteDimensional
    fun_prop
  have hPzero (i : I) : P i 0 = A i := by
    dsimp [P,b]
    simp only [zero_smul, add_zero, hb1]
    rw [abs_of_pos (div_pos (hA i) (hP0 i))]
    change A i/P0 i*P0 i = A i
    exact div_mul_cancel₀ _ (hP0 i).ne'
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, |P i t-A i| < δ*A i := by
    rw [Filter.eventually_all]
    intro i
    have hh := (hP i).continuousAt.eventually (Metric.ball_mem_nhds (P i 0) (mul_pos hδ (hA i)))
    simpa [Metric.mem_ball, Real.dist_eq, hPzero] using hh
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let τ : ℝ := ε/2
  have hτ : 0 < τ := by dsimp [τ]; linarith
  have hd : dist τ 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hτ]
    dsimp [τ]
    linarith
  have hcl := hball hd
  have hprod (i : I) : (∏ j, |f i (b τ j)|) = τ*P i τ := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    dsimp [b,P]
    rw [map_add, hb0, zero_add, map_smul, smul_eq_mul, abs_mul, abs_of_pos hτ]
    ring
  have hpos (i : I) : 0 < ∏ j, |f i (b τ j)| := by
    rw [hprod]
    apply mul_pos hτ
    have hh := (abs_lt.mp (hcl i)).1
    nlinarith [hA i]
  refine ⟨τ,hτ,b τ,?_,?_⟩
  · intro i j hz
    have hh : (∏ j, |f i (b τ j)|) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hz])
    linarith [hpos i]
  · intro i
    rw [hprod]
    have hp := abs_lt.mp (hcl i)
    constructor <;> nlinarith [mul_pos hτ (sub_pos.mpr hp.2),
      mul_pos hτ (sub_pos.mpr hp.1)]

end
end Curvature
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Curvature
open scoped BigOperators Topology
open Filter


theorem solution.{uV,uI} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Curvature.determinant_tuning.{uV,uI} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Curvature.determinant_tuning.{uV,uI}
