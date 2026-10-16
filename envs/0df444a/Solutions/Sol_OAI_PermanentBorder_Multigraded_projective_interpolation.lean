-- Prove2me | solution 1 for OAI.PermanentBorder.Multigraded.projective_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:35:52.643379+00:00
-- url     : https://prove2.me/submissions/4e01e79a-b4af-452f-82a0-14c43b88cf07

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/ProjectiveCounts.lean:L156-L211
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Multigraded.projective_interpolation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts

-- ---- from OAI.Algebra.Determinantal.ProjectiveCounts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI
namespace PermanentBorder.Multigraded
open MvPolynomial
section BilinearPointCount
variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]

end BilinearPointCount
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProductAffineChart
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {L : Type*} [Fintype L] [DecidableEq L]

end ProductAffineChart
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProjectiveInterpolation
variable {K σ ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma projective_pair_separator (group : σ → ι) (x y : σ → K)
    (hxy : BlockSeparated group x y) :
    ∃ (p : MvPolynomial σ K) (e : ι → ℤ),
      p.IsWeightedHomogeneous (blockWeight group) e ∧
      (∀ j, 0 ≤ e j ∧ e j ≤ 1) ∧ eval x p = 1 ∧ eval y p = 0 := by
  classical
  obtain ⟨v,w,hvw,hxy⟩ := hxy
  let p : MvPolynomial σ K := C ((x v * y w - x w * y v)⁻¹) *
    (C (y w) * X v - C (y v) * X w)
  refine ⟨p, Pi.single (group v) 1, ?_, ?_, ?_, ?_⟩
  · apply IsWeightedHomogeneous.C_mul
    apply IsWeightedHomogeneous.sub
    · exact (isWeightedHomogeneous_X K (blockWeight group) v).C_mul _
    · simpa only [blockWeight, hvw] using
        (isWeightedHomogeneous_X K (blockWeight group) w).C_mul (y v)
  · intro j; by_cases h : j = group v <;> simp [h]
  · simp only [p, map_mul, eval_C, map_sub, eval_X]
    rw [mul_comm (y w), mul_comm (y v), inv_mul_cancel₀ (sub_ne_zero.mpr hxy)]
  · simp [p, mul_comm]

variable [Fintype L] [DecidableEq L]

theorem projective_interpolation (group : σ → ι) (d : ι → ℤ)
    (hd : ∀ j, (Fintype.card L : ℤ) ≤ d j)
    (x : L → σ → K) (hx : ∀ i j, i ≠ j → BlockSeparated group (x i) (x j))
    (base : L → ι → σ) (hbase : ∀ i j, group (base i j) = j)
    (hb : ∀ i j, x i (base i j) ≠ 0) :
    ∃ p : L → Piece (K := K) (blockWeight group) d,
      ∀ i j, eval (x j) (p i).val = if j = i then 1 else 0 := by
  classical
  have hs (i j : L) : ∃ (p : MvPolynomial σ K) (e : ι → ℤ),
      p.IsWeightedHomogeneous (blockWeight group) e ∧
      (∀ l, 0 ≤ e l ∧ e l ≤ 1) ∧ eval (x i) p = 1 ∧ (i ≠ j → eval (x j) p = 0) := by
    by_cases hij : i = j
    · refine ⟨1,0,isWeightedHomogeneous_one _ _,?_,by simp,?_⟩
      · intro l; simp
      · exact fun h => (h hij).elim
    · obtain ⟨p,e,hp,he,hi,hj⟩ := projective_pair_separator group (x i) (x j) (hx i j hij)
      exact ⟨p,e,hp,he,hi,fun _ => hj⟩
  choose p e hp he hi hj using hs
  let E : L → ι → ℤ := fun i => ∑ j, e i j
  have hE (i : L) (l : ι) : E i l ≤ Fintype.card L := by
    dsimp [E]
    simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (he i j l).2)
  let b : L → ι → ℕ := fun i l => (d l - E i l).toNat
  have hbdeg (i : L) : (fun l => (b i l : ℤ)) = d-E i := by
    funext l
    exact Int.toNat_of_nonneg (sub_nonneg.mpr ((hE i l).trans (hd l)))
  let pad : L → MvPolynomial σ K := fun i =>
    ∏ l, (C ((x i (base i l))⁻¹) * X (base i l)) ^ b i l
  have hpadhom (i : L) : (pad i).IsWeightedHomogeneous (blockWeight group) (d - E i) := by
    rw [← hbdeg]
    have h := IsWeightedHomogeneous.prod Finset.univ
      (fun l => (C ((x i (base i l))⁻¹) * X (base i l) : MvPolynomial σ K)^b i l)
      (fun l => b i l • Pi.single l (1 : ℤ)) (fun l _ => by
        convert ((isWeightedHomogeneous_X K (blockWeight group) (base i l)).C_mul
          ((x i (base i l))⁻¹)).pow (b i l) using 1
        simp only [blockWeight, hbase])
    convert h using 1
    ext l
    simp [Pi.single_apply]
  have hpadeval (i : L) : eval (x i) (pad i) = 1 := by
    simp [pad, inv_mul_cancel₀ (hb i _)]
  let P : L → MvPolynomial σ K := fun i => (∏ j, p i j) * pad i
  have hPhom (i : L) : (P i).IsWeightedHomogeneous (blockWeight group) d := by
    have hp' := IsWeightedHomogeneous.prod Finset.univ (p i) (e i) (fun j _ => hp i j)
    have h := hp'.mul (hpadhom i)
    have hdeg : (∑ j, e i j) + (d - E i) = d := by dsimp [E]; abel
    rw [hdeg] at h
    exact h
  refine ⟨fun i => ⟨P i,hPhom i⟩,?_⟩
  intro i j
  change eval (x j) (P i) = _
  simp only [P, map_mul, map_prod]
  by_cases hij : j = i
  · subst j
    simp [hi, hpadeval]
  · rw [ite_eq_right hij, Finset.prod_eq_zero (Finset.mem_univ j) (hj i j (Ne.symm hij)), zero_mul]

end ProjectiveInterpolation
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProjectivePointBound
variable {K σ ι L : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]
  [Fintype L] [DecidableEq L]

end ProjectivePointBound
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial Filter
open scoped Topology
section MultiChartProductCount
variable {ι L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

end MultiChartProductCount
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section BilinearMultiChartCount
variable {ι L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

end BilinearMultiChartCount
end PermanentBorder.Multigraded

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
open MvPolynomial


theorem solution : type_of% @_root_.OAI.PermanentBorder.Multigraded.projective_interpolation := @_root_.OAI.PermanentBorder.Multigraded.projective_interpolation
