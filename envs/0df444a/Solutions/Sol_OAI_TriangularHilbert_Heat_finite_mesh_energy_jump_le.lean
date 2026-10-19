-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.finite_mesh_energy_jump_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:38:24.961511+00:00
-- url     : https://prove2.me/submissions/0b0d7cb6-481a-4cba-ae57-6f5ab3a30192

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/MeshJump.lean:L52-L71
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.finite_mesh_energy_jump_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Theorems.Thm_OAI_TriangularHilbert_Heat_mesh_mass_le
import Theorems.Thm_OAI_TriangularHilbert_Heat_totalPlaneEnergy_replaceZero_jump
import Theorems.Thm_OAI_TriangularHilbert_intInterval_sum_fin
import Theorems.Thm_OAI_TriangularHilbert_intInterval_weighted_le

-- ---- from OAI.Analysis.TriangularHilbert.GaussianConvolution ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_neg (σ x : ℝ) : density σ (-x) = density σ x := by
  simp [density]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.IntWeak ----
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma mem_intInterval (m n : ℤ) (r : ℕ) :
    m ∈ intInterval n r ↔ n-(r:ℤ) ≤ m ∧ m ≤ n+r := Finset.mem_Icc

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.IntMax ----
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma mem_intInterval_iff_dist (m n : ℤ) (r : ℕ) :
    m ∈ intInterval n r ↔ (m-n).natAbs ≤ r := by
  rw [mem_intInterval]
  have he : (m-n).natAbs ≤ r ↔ |m-n| ≤ (r:ℤ) := by
    rw [← Int.natCast_natAbs]
    omega
  rw [he,abs_le]
  constructor <;> intro h <;> constructor <;> omega

lemma intAverage_nonneg (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m) (n : ℤ) (r : ℕ) :
    0 ≤ intAverage D f n r := by
  exact div_nonneg (Finset.sum_nonneg (fun m hm => hf m (Finset.mem_inter.mp hm).1)) (by positivity)

lemma inter_intInterval_of_supportRadius_le (D : Finset ℤ) (n : ℤ) {r : ℕ}
    (hr : supportRadius D n ≤ r) : D ∩ intInterval n r = D := by
  apply Finset.inter_eq_left.mpr
  intro m hm
  rw [mem_intInterval_iff_dist]
  exact (Finset.le_sup hm).trans hr

lemma intAverage_le_intMax (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (n : ℤ) (r : ℕ) : intAverage D f n r ≤ intMax D f n := by
  by_cases hr : r ≤ supportRadius D n
  · exact Finset.le_sup' _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  · have hb : supportRadius D n ≤ r := le_of_lt (lt_of_not_ge hr)
    have hm : intAverage D f n r ≤ intAverage D f n (supportRadius D n) := by
      unfold intAverage
      rw [inter_intInterval_of_supportRadius_le D n hb,
        inter_intInterval_of_supportRadius_le D n le_rfl]
      apply div_le_div_of_nonneg_left (Finset.sum_nonneg hf) (by positivity)
      exact_mod_cast (by omega : 2*supportRadius D n+1 ≤ 2*r+1)
    exact hm.trans (Finset.le_sup' _ (Finset.mem_range.mpr (Nat.lt_succ_self _)))

lemma intMax_nonneg (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m) (n : ℤ) :
    0 ≤ intMax D f n := (intAverage_nonneg D f hf n 0).trans (intAverage_le_intMax D f hf n 0)

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianRadial ----
namespace OAI

section
namespace TriangularHilbert.Heat
open scoped BigOperators
noncomputable section

lemma density_radial_int (σ h : ℝ) (m : ℤ) :
    density σ (h*(m:ℝ)) = density σ (h*(m.natAbs:ℝ)) := by
  have he := congrArg (fun n : ℤ => (n : ℝ)) (Int.natAbs_sq m).symm
  simp only [Int.cast_pow,Int.cast_natCast] at he
  simp only [density,mul_pow,he]

lemma density_radial_descending {σ h : ℝ} (hσ : 0 < σ) (hh : 0 ≤ h) (r : ℕ) :
    h*density σ (h*(r+1:ℕ)) ≤ h*density σ (h*(r:ℝ)) := by
  apply mul_le_mul_of_nonneg_left _ hh
  unfold density
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hr : (0:ℝ) ≤ r := by positivity
  push_cast
  nlinarith [sq_nonneg h]

lemma intInterval_density_mass {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (n : ℤ) (N : ℕ) :
    (∑ m ∈ intInterval n N, h*density σ (h*((m-n).natAbs:ℝ))) ≤ meshMassConstant := by
  simp_rw [← density_radial_int]
  rw [intInterval_sum_fin]
  have he (i : Fin (2*N+1)) : h*density σ (h*((n-(N:ℤ)+(i:ℕ)-n:ℤ):ℝ)) =
      h*density σ (-(h*N)+h*i) := by
    congr 2
    push_cast
    ring
  simp_rw [he]
  exact mesh_mass_le hh hσ (-(h*N)) (2*N+1)

lemma gaussian_sum_le_intMax (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (n : ℤ) :
    (∑ m ∈ D, f m*(h*density σ (h*((m-n:ℤ):ℝ)))) ≤ meshMassConstant * intMax D f n := by
  have hpos : 0 < σ := (sq_pos_of_pos hh).trans_le hσ
  simp_rw [density_radial_int]
  have hw := intInterval_weighted_le D f hf n (fun r => h*density σ (h*(r:ℝ)))
    (fun r => mul_nonneg hh.le (density_nonneg hpos.le _)) (density_radial_descending hpos hh.le)
  apply hw.trans
  rw [mul_comm meshMassConstant]
  exact mul_le_mul_of_nonneg_left (intInterval_density_mass hh hσ n (supportRadius D n)) (intMax_nonneg D f hf n)
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.FiniteLineMax ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe uκ

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma lineExtend_apply (D : Finset ℤ) (f : D → ℝ) (n : D) : lineExtend D f n = f n := by
  simp only [lineExtend,dite_eq_left n.property]

lemma sum_lineExtend (D : Finset ℤ) (f : D → ℝ) (g : ℤ → ℝ) :
    (∑ n ∈ D, lineExtend D f n*g n) = ∑ n : D, f n*g n := by
  rw [← Finset.sum_coe_sort]
  simp only [lineExtend_apply]

lemma gaussian_sum_le_lineMax (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m)
    {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (n : ℤ) :
    (∑ m : D, f m*(h*Heat.density σ (h*((m-n:ℤ):ℝ)))) ≤ Heat.meshMassConstant*lineMax D f n := by
  have hi := Heat.gaussian_sum_le_intMax D (lineExtend D f)
    (fun m hm => by simpa only [lineExtend,dite_eq_left hm] using hf ⟨m,hm⟩) hh hσ n
  rw [sum_lineExtend] at hi
  exact hi

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.MeshJump ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators
noncomputable section

lemma gaussian_sum_back_le_lineMax (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m)
    {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (n : ℤ) :
    (∑ m : D, f m*(h*density σ (h*n-h*(m:ℤ)))) ≤ meshMassConstant*lineMax D f n := by
  have he (m : D) : density σ (h*n-h*(m:ℤ)) = density σ (h*((m-n:ℤ):ℝ)) := by
    rw [show h*n-h*(m:ℤ) = -(h*((m-n:ℤ):ℝ)) by push_cast; ring,density_neg]
  simp_rw [he]
  exact gaussian_sum_le_lineMax D f hf hh hσ n

lemma gaussian_sum_triangle_le_lineMax (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m)
    {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (i j : ℤ) :
    (∑ m : D, f m*(h*density σ (h*i+h*j+h*(m:ℤ)))) ≤ meshMassConstant*lineMax D f (-i-j) := by
  have he (m : D) : h*i+h*j+h*(m:ℤ) = h*((m-(-i-j):ℤ):ℝ) := by push_cast; ring
  simp_rw [he]
  exact gaussian_sum_le_lineMax D f hf hh hσ (-i-j)

lemma jumpExpectation_le_jumpMax (D : Finset ℤ) (A : Three → Matrix D D ℂ)
    {h : ℝ} (hh : 0 < h) {σ : Three → ℝ} (hσ : ∀ v, h^2 ≤ σ v) (i j : D) :
    jumpExpectation A h (fun m => h*(m:ℤ)) σ i j ≤ meshMassConstant*jumpMax D A i j := by
  have htwo (v : Three) : h^2 ≤ 2*σ v := by nlinarith [hσ v,sq_nonneg h]
  have hsum : h^2 ≤ σ 0+σ 1+σ 2 := by nlinarith [hσ 0,hσ 1,hσ 2,sq_nonneg h]
  have hX := gaussian_sum_back_le_lineMax D (fun m => ‖A 0 i m‖^2) (fun _ => sq_nonneg _) hh (htwo 1) j
  have hY := gaussian_sum_back_le_lineMax D (fun m => ‖A 0 m j‖^2) (fun _ => sq_nonneg _) hh (htwo 0) i
  have hH := gaussian_sum_triangle_le_lineMax D (fun m => ‖A 2 m i‖^2) (fun _ => sq_nonneg _) hh hsum i j
  have hK := gaussian_sum_triangle_le_lineMax D (fun m => ‖A 1 j m‖^2) (fun _ => sq_nonneg _) hh hsum i j
  unfold jumpExpectation jumpMax
  linarith

lemma finite_mesh_energy_jump_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) (B C : Matrix D D ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    {h : ℝ} (hh : 0 < h) {σ : Three → ℝ} (hσ : ∀ v, h^2 ≤ σ v) :
    |totalPlaneEnergy (replaceZero A B) h (fun m => h*(m:ℤ)) 0 σ-
      totalPlaneEnergy (replaceZero A C) h (fun m => h*(m:ℤ)) 0 σ| ≤
      3/2*meshMassConstant*h^2*∑ i, ∑ j, ‖B i j-C i j‖*jumpMax D A i j := by
  have hj := totalPlaneEnergy_replaceZero_jump A B C hB hC hh (fun m => h*(m:ℤ))
    (fun v => (sq_pos_of_pos hh).trans_le (hσ v))
  apply hj.trans
  calc
    _ ≤ 3/2*h^2*∑ i, ∑ j, ‖B i j-C i j‖*(meshMassConstant*jumpMax D A i j) := by
      gcongr with i j
      exact jumpExpectation_le_jumpMax D A hh hσ i j
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.finite_mesh_energy_jump_le := @_root_.OAI.TriangularHilbert.Heat.finite_mesh_energy_jump_le
