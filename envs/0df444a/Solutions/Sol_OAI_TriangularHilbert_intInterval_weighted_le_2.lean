-- Prove2me | solution 2 for OAI.TriangularHilbert.intInterval_weighted_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:36:42.444133+00:00
-- url     : https://prove2.me/submissions/6c27c8d6-d52d-4137-b7eb-8e5f146af18d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/GaussianMax.lean:L44-L74
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.intInterval_weighted_le. The node keeps its source
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

-- ---- from OAI.Analysis.TriangularHilbert.IntWeak ----
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma mem_intInterval (m n : ℤ) (r : ℕ) :
    m ∈ intInterval n r ↔ n-(r:ℤ) ≤ m ∧ m ≤ n+r := Finset.mem_Icc

lemma card_intInterval (n : ℤ) (r : ℕ) : (intInterval n r).card = 2*r+1 := by
  rw [intInterval,Int.card_Icc]
  have he : n+(r:ℤ)+1-(n-r) = ((2*r+1 : ℕ):ℤ) := by push_cast; ring
  rw [he,Int.toNat_natCast]

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

lemma sum_interval_le_intMax (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (n : ℤ) (r : ℕ) : (∑ m ∈ D ∩ intInterval n r, f m) ≤ intMax D f n*(2*(r:ℝ)+1) := by
  exact (div_le_iff₀ (by positivity : 0 < 2*(r:ℝ)+1)).mp (intAverage_le_intMax D f hf n r)
end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.FiniteAbel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uκ

section
namespace TriangularHilbert
open scoped BigOperators

lemma descending_layer_identity (g : ℕ → ℝ) (k N : ℕ) (hk : k ≤ N) :
    g k = g N + ∑ r ∈ Finset.range N, if k ≤ r then g r-g (r+1) else 0 := by
  induction N with
  | zero =>
    have he : k = 0 := by omega
    subst k
    simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases hkN : k ≤ N
    · rw [ite_eq_left hkN]
      linarith [ih hkN]
    · have he : k = N+1 := by omega
      subst k
      have hs : (∑ r ∈ Finset.range N, if N+1 ≤ r then g r-g (r+1) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        rw [ite_eq_right (by have := Finset.mem_range.mp hr; omega)]
      rw [hs,ite_eq_right (by omega)]
      ring

lemma weighted_prefix_identity {κ : Type uκ} (s : Finset κ) (d : κ → ℕ) (a : κ → ℝ)
    (g : ℕ → ℝ) (N : ℕ) (hd : ∀ i ∈ s, d i ≤ N) :
    (∑ i ∈ s, a i*g (d i)) = g N*(∑ i ∈ s, a i) +
      ∑ r ∈ Finset.range N, (g r-g (r+1)) * ∑ i ∈ s.filter (fun i => d i ≤ r), a i := by
  classical
  calc
    _ = ∑ i ∈ s, a i*(g N+∑ r ∈ Finset.range N, if d i ≤ r then g r-g (r+1) else 0) :=
      Finset.sum_congr rfl (fun i hi => congrArg (a i*·) (descending_layer_identity g (d i) N (hd i hi)))
    _ = g N*(∑ i ∈ s, a i) + ∑ r ∈ Finset.range N, ∑ i ∈ s, a i*(if d i ≤ r then g r-g (r+1) else 0) := by
      simp_rw [mul_add,Finset.mul_sum]
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      congr 1
      simp_rw [mul_comm (g N)]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring

lemma weighted_prefix_le {κ : Type uκ} (s : Finset κ) (d : κ → ℕ) (a b : κ → ℝ)
    (g : ℕ → ℝ) (N : ℕ) (hd : ∀ i ∈ s, d i ≤ N) (hg : 0 ≤ g N)
    (hdec : ∀ r < N, g (r+1) ≤ g r)
    (hp : ∀ r ≤ N, (∑ i ∈ s.filter (fun i => d i ≤ r), a i) ≤ ∑ i ∈ s.filter (fun i => d i ≤ r), b i) :
    (∑ i ∈ s, a i*g (d i)) ≤ ∑ i ∈ s, b i*g (d i) := by
  classical
  rw [weighted_prefix_identity s d a g N hd,weighted_prefix_identity s d b g N hd]
  apply add_le_add
  · have he : s.filter (fun i => d i ≤ N) = s := Finset.filter_eq_self.mpr hd
    have ht := hp N le_rfl
    rw [he] at ht
    exact mul_le_mul_of_nonneg_left ht hg
  · exact Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left
      (hp r (Finset.mem_range.mp hr).le) (sub_nonneg.mpr (hdec r (Finset.mem_range.mp hr))))
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianMax ----
namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma intInterval_filter (n : ℤ) (N r : ℕ) (hr : r ≤ N) :
    (intInterval n N).filter (fun m => (m-n).natAbs ≤ r) = intInterval n r := by
  ext m
  simp only [Finset.mem_filter,mem_intInterval_iff_dist]
  exact ⟨And.right,fun h => ⟨h.trans hr,h⟩⟩

lemma intInterval_weighted_le (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (n : ℤ) (g : ℕ → ℝ) (hg : ∀ r, 0 ≤ g r) (hdec : ∀ r, g (r+1) ≤ g r) :
    (∑ m ∈ D, f m*g (m-n).natAbs) ≤
      intMax D f n * ∑ m ∈ intInterval n (supportRadius D n), g (m-n).natAbs := by
  classical
  let N := supportRadius D n
  have hD : D ⊆ intInterval n N := by
    intro m hm
    rw [mem_intInterval_iff_dist]
    exact (Finset.le_sup (f := fun k : ℤ => (k-n).natAbs) hm)
  have he : (∑ m ∈ D, f m*g (m-n).natAbs) =
      ∑ m ∈ intInterval n N, (if m ∈ D then f m else 0)*g (m-n).natAbs := by
    simp only [ite_mul,zero_mul,Finset.sum_ite,Finset.sum_const_zero,add_zero]
    congr 1
    ext m
    simp only [Finset.mem_filter]
    exact ⟨fun hm => ⟨hD hm,hm⟩,And.right⟩
  rw [he]
  have hw := weighted_prefix_le (intInterval n N) (fun m => (m-n).natAbs)
    (fun m => if m ∈ D then f m else 0) (fun _ => intMax D f n) g N
    (fun m hm => (mem_intInterval_iff_dist m n N).mp hm) (hg N) (fun r _ => hdec r) ?_
  · simpa only [← Finset.mul_sum] using hw
  · intro r hr
    rw [intInterval_filter n N r hr]
    have he' : (∑ m ∈ intInterval n r, if m ∈ D then f m else 0) = ∑ m ∈ D ∩ intInterval n r, f m := by
      rw [Finset.sum_ite,Finset.sum_const_zero,add_zero]
      congr 1
      ext m
      simp only [Finset.mem_filter,Finset.mem_inter,and_comm]
    rw [he',Finset.sum_const,card_intInterval,nsmul_eq_mul]
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,mul_comm] using sum_interval_le_intMax D f hf n r
end
end TriangularHilbert
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TriangularHilbert.intInterval_weighted_le := @_root_.OAI.TriangularHilbert.intInterval_weighted_le
