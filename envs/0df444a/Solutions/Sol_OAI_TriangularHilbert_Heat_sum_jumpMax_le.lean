-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.sum_jumpMax_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:40:08.671382+00:00
-- url     : https://prove2.me/submissions/817d8911-6f7a-4ae5-b767-15f196cb7737

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/JumpScalar.lean:L23-L66
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.sum_jumpMax_le. The node keeps its source
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Theorems.Thm_OAI_TriangularHilbert_int_intervals_strong

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

lemma intMax_attained (D : Finset ℤ) (f : ℤ → ℝ) (n : ℤ) :
    ∃ r : ℕ, intMax D f n = intAverage D f n r := by
  obtain ⟨r,_,hr⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.range (supportRadius D n+1)) (by exact ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩) (intAverage D f n)
  exact ⟨r,hr⟩

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianMax ----
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma intMax_strong (D s : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m) :
    (∑ n ∈ s, intMax D f n * Real.sqrt (intMax D f n)) ≤
      18*Real.sqrt 2 * ∑ m ∈ D, f m*Real.sqrt (f m) := by
  choose r hr using intMax_attained D f
  apply int_intervals_strong D s f (intMax D f) hf (fun n _ => intMax_nonneg D f hf n) r
  intro n _
  rw [hr n,intAverage]
  exact le_of_eq (div_mul_cancel₀ _ (by positivity))

end
end TriangularHilbert
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

lemma lineMax_nonneg (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m) (n : ℤ) :
    0 ≤ lineMax D f n := by
  exact intMax_nonneg D (lineExtend D f) (fun m hm => by simpa only [lineExtend,dite_eq_left hm] using hf ⟨m,hm⟩) n

lemma lineMax_strong (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m)
    {κ : Type uκ} [Fintype κ] (u : κ → ℤ) (hu : Function.Injective u) :
    (∑ n, lineMax D f (u n)*Real.sqrt (lineMax D f (u n))) ≤
      18*Real.sqrt 2 * ∑ m : D, f m*Real.sqrt (f m) := by
  classical
  have hi := intMax_strong D (Finset.univ.image u) (lineExtend D f)
    (fun m hm => by simpa only [lineExtend,dite_eq_left hm] using hf ⟨m,hm⟩)
  rw [Finset.sum_image (fun _ _ _ _ h => hu h)] at hi
  rw [← Finset.sum_coe_sort D (fun m => lineExtend D f m*Real.sqrt (lineExtend D f m))] at hi
  simpa only [lineMax,lineExtend_apply] using hi

lemma cubic_young {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a*b ≤ (a^3+2*b*Real.sqrt b)/3 := by
  have hs := Real.sq_sqrt hb
  have hnn : 0 ≤ (a-Real.sqrt b)^2*(a+2*Real.sqrt b) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hs3 : (Real.sqrt b)^3 = b*Real.sqrt b := by rw [pow_succ,hs]
  have ha2 : a*(Real.sqrt b)^2 = a*b := by rw [hs]
  nlinarith only [hnn,hs3,ha2]

lemma sum_abs_sq_sqrt {κ : Type uκ} [Fintype κ] (f : κ → ℂ) :
    (∑ m, ‖f m‖^2*Real.sqrt (‖f m‖^2)) = ∑ m, ‖f m‖^3 := by
  apply Finset.sum_congr rfl
  intro m _
  rw [Real.sqrt_sq (norm_nonneg _)]; ring

lemma lineMax_scalar_product_bound (D : Finset ℤ) (f : D → ℂ)
    {κ : Type uκ} [Fintype κ] (u : κ → ℤ) (hu : Function.Injective u) (a : κ → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i*lineMax D (fun m => ‖f m‖^2) (u i)) ≤
      ((∑ i, a i^3)+36*Real.sqrt 2*(∑ m, ‖f m‖^3))/3 := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset κ)) =>
    cubic_young (ha i) (lineMax_nonneg D (fun m => ‖f m‖^2) (fun m => sq_nonneg _) (u i)))
  have hm := lineMax_strong D (fun m => ‖f m‖^2) (fun m => sq_nonneg _) u hu
  rw [sum_abs_sq_sqrt] at hm
  simp only [mul_assoc,← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum] at hs
  linarith
end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.JumpScalar ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators
noncomputable section

lemma sum_lineMax_scalar_product_bound (D : Finset ℤ) (f g : D → D → ℂ) (u : D → D → ℤ)
    (hu : ∀ i, Function.Injective (u i)) :
    (∑ i, ∑ j, ‖g i j‖*lineMax D (fun m => ‖f i m‖^2) (u i j)) ≤
      ((∑ i, ∑ j, ‖g i j‖^3)+36*Real.sqrt 2*(∑ i, ∑ m, ‖f i m‖^3))/3 := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset D)) =>
    lineMax_scalar_product_bound D (f i) (u i) (hu i) (fun j => ‖g i j‖) (fun j => norm_nonneg _))
  simpa only [← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum] using hs

lemma sum_jumpMax_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) :
    (∑ i, ∑ j, ‖A 0 i j‖*jumpMax D A i j) ≤
      jumpScalarConstant * (∑ v, ∑ i, ∑ j, ‖A v i j‖^3) := by
  have hu : Function.Injective (fun i : D => (i:ℤ)) := Subtype.val_injective
  have hn (i : D) : Function.Injective (fun j : D => -(i:ℤ)-(j:ℤ)) := by
    intro j k hjk
    apply Subtype.ext
    dsimp at hjk
    omega
  have hX := sum_lineMax_scalar_product_bound D (fun i m => A 0 i m) (fun i j => A 0 i j)
    (fun _ j => (j:ℤ)) (fun _ => hu)
  have hY := sum_lineMax_scalar_product_bound D (fun j m => A 0 m j) (fun j i => A 0 i j)
    (fun _ i => (i:ℤ)) (fun _ => hu)
  have hH := sum_lineMax_scalar_product_bound D (fun i m => A 2 m i) (fun i j => A 0 i j)
    (fun i j => -(i:ℤ)-(j:ℤ)) hn
  have hK := sum_lineMax_scalar_product_bound D (fun j m => A 1 j m) (fun j i => A 0 i j)
    (fun j i => -(j:ℤ)-(i:ℤ)) hn
  have hc (v : Three) : (∑ j : D, ∑ i : D, ‖A v i j‖^3) = ∑ i : D, ∑ j : D, ‖A v i j‖^3 := by rw [Finset.sum_comm]
  rw [hc] at hY hH hK
  have hYe : (∑ j : D, ∑ i : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 0 m j‖^2) (i:ℤ)) =
      ∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 0 m j‖^2) (i:ℤ) := by rw [Finset.sum_comm]
  rw [hYe] at hY
  have hKe : (∑ j : D, ∑ i : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 1 j m‖^2) (-(j:ℤ)-(i:ℤ))) =
      ∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 1 j m‖^2) (-(i:ℤ)-(j:ℤ)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    omega
  rw [hKe] at hK
  have hb (v : Three) : 0 ≤ ∑ i : D, ∑ j : D, ‖A v i j‖^3 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => pow_nonneg (norm_nonneg _) _))
  have he : (∑ i : D, ∑ j : D, ‖A 0 i j‖*jumpMax D A i j) =
      2*(∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 0 i m‖^2) j)+
      2*(∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 0 m j‖^2) i)+
      (∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 2 m i‖^2) (-(i:ℤ)-(j:ℤ)))+
      (∑ i : D, ∑ j : D, ‖A 0 i j‖*lineMax D (fun m => ‖A 1 j m‖^2) (-(i:ℤ)-(j:ℤ))) := by
    simp only [jumpMax,mul_add,Finset.sum_add_distrib,Finset.mul_sum,
      mul_left_comm]
  rw [he,Fin.sum_univ_three]
  unfold jumpScalarConstant
  nlinarith [hb 0,hb 1,hb 2,Real.sqrt_nonneg (2:ℝ)]
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.sum_jumpMax_le := @_root_.OAI.TriangularHilbert.Heat.sum_jumpMax_le
