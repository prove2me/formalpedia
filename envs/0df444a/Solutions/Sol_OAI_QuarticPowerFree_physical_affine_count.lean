-- Prove2me | solution 1 for OAI.QuarticPowerFree.physical_affine_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T15:07:23.377669+00:00
-- url     : https://prove2.me/submissions/c6a6ce52-7945-481e-a6e7-1911f5bc236d

import Mathlib
import Definitions.Def_OAIB3Qp000

section
-- module Solutions.OAIB3_Qpf.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_GenericCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree

open MvPolynomial

lemma monomial_exponent_le_order {σ : Type*} (m : σ →₀ ℕ) (i : σ) :
    m i ≤ monomialOrder m := by
  classical
  by_cases hi : i ∈ m.support
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  · simp only [Finsupp.notMem_support_iff.mp hi, Nat.zero_le]

theorem eval_abs_le_height_degree {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℤ) (D : ℕ) (hp : p.totalDegree ≤ D)
    (C H : ℝ) (hC : 0 ≤ C) (hH : 1 ≤ H)
    (hc : ∀ m, |((p.coeff m : ℤ) : ℝ)| ≤ C)
    (z : σ → ℤ) (hz : ∀ i, |(z i : ℝ)| ≤ H) :
    |((eval z p : ℤ) : ℝ)| ≤
      ((D + Fintype.card σ).choose (Fintype.card σ) : ℝ) * C * H^D := by
  classical
  have hs : p.support ⊆ monomialsUpTo σ D := by
    intro m hm
    exact mem_monomialsUpTo.mpr ((le_totalDegree hm).trans hp)
  have hcard : p.support.card ≤ (D + Fintype.card σ).choose (Fintype.card σ) := by
    rw [← card_monomialsUpTo]
    exact Finset.card_le_card hs
  have hm (m : σ →₀ ℕ) (hm : m ∈ p.support) :
      |((p.coeff m * m.prod (fun i e => z i ^ e) : ℤ) : ℝ)| ≤ C * H^D := by
    rw [Int.cast_mul, abs_mul]
    exact mul_le_mul (hc m)
      (monomial_eval_abs_le z m H hH hz D ((le_totalDegree hm).trans hp))
      (abs_nonneg _) hC
  rw [MvPolynomial.eval_eq, Int.cast_sum]
  calc
    |∑ m ∈ p.support, ((p.coeff m * ∏ i ∈ m.support, z i ^ m i : ℤ) : ℝ)| ≤
        ∑ m ∈ p.support, |((p.coeff m * ∏ i ∈ m.support, z i ^ m i : ℤ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ p.support, C * H^D := Finset.sum_le_sum hm
    _ = (p.support.card : ℝ) * C * H^D := by simp [mul_assoc]
    _ ≤ ((D + Fintype.card σ).choose (Fintype.card σ) : ℝ) * C * H^D := by
      gcongr

theorem pderiv_coeff_abs_le {σ : Type*} (p : MvPolynomial σ ℤ)
    (D : ℕ) (hp : p.totalDegree ≤ D) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ m, |((p.coeff m : ℤ) : ℝ)| ≤ C) (i : σ) (m : σ →₀ ℕ) :
    |(((pderiv i p).coeff m : ℤ) : ℝ)| ≤ (D : ℝ) * C := by
  classical
  rw [coeff_pderiv]
  by_cases hn : p.coeff (m + Finsupp.single i 1) = 0
  · simp only [hn, zero_mul, Int.cast_zero, abs_zero]
    positivity
  · have hd : monomialOrder (m + Finsupp.single i 1) ≤ D :=
      (le_totalDegree (mem_support_iff.mpr hn)).trans hp
    have hex := (monomial_exponent_le_order (m + Finsupp.single i 1) i).trans hd
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hex
    rw [Int.cast_mul, abs_mul, Int.cast_add, Int.cast_natCast, Int.cast_one,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (m i : ℝ) + 1)]
    calc
      _ ≤ C * (D : ℝ) := mul_le_mul (hc _) (by exact_mod_cast hex) (by positivity) hC
      _ = _ := mul_comm _ _

theorem eval_jacobian_minor_abs_le {σ β : Type*}
    [Fintype σ] [Fintype β] [DecidableEq β]
    (G : β → MvPolynomial σ ℤ) (v : β → σ)
    (D : ℕ) (hG : ∀ i, (G i).totalDegree ≤ D)
    (C H : ℝ) (hC : 0 ≤ C) (hH : 1 ≤ H)
    (hc : ∀ i m, |(((G i).coeff m : ℤ) : ℝ)| ≤ C)
    (z : σ → ℤ) (hz : ∀ i, |(z i : ℝ)| ≤ H) :
    |((eval z (Matrix.det (fun i j => pderiv (v j) (G i))) : ℤ) : ℝ)| ≤
      (Fintype.card β).factorial *
        (((D + Fintype.card σ).choose (Fintype.card σ) : ℝ) * ((D : ℝ)*C) * H^D)^Fintype.card β := by
  let M : Matrix β β (MvPolynomial σ ℤ) := fun i j => pderiv (v j) (G i)
  change |((eval z M.det : ℤ) : ℝ)| ≤ _
  rw [(eval z).map_det M]
  apply det_abs_le_uniform
  intro i j
  apply eval_abs_le_height_degree _ D
    ((pderiv_degree_le_sub_one _ D (hG i) _).trans (Nat.sub_le _ _))
    ((D : ℝ)*C) H (mul_nonneg (Nat.cast_nonneg _) hC) hH
    (pderiv_coeff_abs_le _ D (hG i) C hC (hc i) (v j)) z hz

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PointInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators

theorem exists_mv_interpolate {ι σ K : Type*} [Fintype ι] [Field K]
    (z : ι → σ → K) (hz : Function.Injective z) (v : ι → K) :
    ∃ p : MvPolynomial σ K, ∀ i, eval (z i) p = v i := by
  classical
  have hsep : ∀ i j : ι, i ≠ j → ∃ a, z i a ≠ z j a := by
    intro i j hij
    by_contra! h
    exact hij (hz (funext h))
  let L : ι → ι → MvPolynomial σ K := fun i j =>
    if hij : i = j then 1 else
      let a := (hsep i j hij).choose
      C ((z i a - z j a)⁻¹) * (X a - C (z j a))
  have hLi : ∀ i j, eval (z i) (L i j) = 1 := by
    intro i j
    by_cases h : i = j
    · simp [L, h]
    · simp only [L, h, ↓reduceDIte, map_mul, eval_C, map_sub, eval_X]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr (hsep i j h).choose_spec)
  have hLj : ∀ i j, i ≠ j → eval (z j) (L i j) = 0 := by
    intro i j h
    simp [L, h]
  refine ⟨∑ i, C (v i) * ∏ j, L i j, ?_⟩
  intro a
  rw [map_sum, Finset.sum_eq_single a]
  · simp [hLi]
  · intro i _ hia
    rw [map_mul, eval_C, map_prod]
    have hp : (∏ j, eval (z a) (L i j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a) (hLj i a hia)
    rw [hp, mul_zero]
  · simp

end
open MvPolynomial

open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_IntegerPatches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree

open MvPolynomial
attribute [local instance] Classical.propDecidable

theorem evaluationSpace_antitone {n D : ℕ} {S T : Finset (Fin n → ℤ)}
    (hST : S ⊆ T) : evaluationSpace T D ≤ evaluationSpace S D := by
  intro p hp z hz
  exact hp z (hST hz)

theorem evaluationCell_antitone {n : ℕ} {K : Type*} [Field K]
    (S : Finset (Fin n → ℤ)) (I : Ideal (MvPolynomial (Fin n) K))
    (z : Fin n → ℤ) {Q R : Finset ℕ} (hQR : Q ⊆ R) :
    evaluationCell S I z R ⊆ evaluationCell S I z Q := by
  intro w hw
  obtain ⟨hw,hI,hres⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨hw,hI,fun p hp l => hres p (hQR hp) l⟩

theorem evaluationCell_eq_of_congruent {n : ℕ} {K : Type*} [Field K]
    (S : Finset (Fin n → ℤ)) (I : Ideal (MvPolynomial (Fin n) K))
    (z w : Fin n → ℤ) (Q : Finset ℕ)
    (hzw : ∀ p ∈ Q, ∀ l, (p : ℤ) ∣ w l-z l) :
    evaluationCell S I z Q = evaluationCell S I w Q := by
  ext x
  simp only [evaluationCell,Finset.mem_filter]
  suffices (∀ p ∈ Q, ∀ l, (p : ℤ) ∣ x l-z l) ↔
      (∀ p ∈ Q, ∀ l, (p : ℤ) ∣ x l-w l) by tauto
  constructor
  · intro h p hp l
    have he : x l-w l = (x l-z l)-(w l-z l) := by ring
    rw [he]
    exact dvd_sub (h p hp l) (hzw p hp l)
  · intro h p hp l
    have he : x l-z l = (x l-w l)+(w l-z l) := by ring
    rw [he]
    exact dvd_add (h p hp l) (hzw p hp l)

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PatchBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

open scoped BigOperators
open Matrix
open scoped BigOperators

namespace QuarticPowerFree
open MvPolynomial

theorem stagedEvaluationSpace_mono {n d E : ℕ} {S T : Finset (Fin n → ℤ)}
    (hST : S ⊆ T) : stagedEvaluationSpace T d E ≤ stagedEvaluationSpace S d E :=
  inf_le_inf le_rfl (evaluationSpace_antitone hST)

theorem mem_stagedKernelPolynomials {n d E : ℕ} (hdE : d ≤ E)
    (S : Finset (Fin n → ℤ)) (p : MvPolynomial (Fin n) ℂ) :
    p ∈ stagedKernelPolynomials d E (stagedEvaluationSpace S d E) ↔
      p.totalDegree ≤ d ∧ ∀ z ∈ S, eval (fun l => (z l : ℂ)) p = 0 := by
  constructor
  · rintro ⟨v,hv,rfl,hdeg⟩
    exact ⟨hdeg,hv.2⟩
  · rintro ⟨hdeg,hz⟩
    refine ⟨⟨p,mem_totalSpace.mpr (hdeg.trans hdE)⟩,?_,rfl,hdeg⟩
    exact ⟨mem_totalSpace.mpr hdeg,hz⟩

theorem kernelChildList_spec {n E : ℕ} (G : KernelGeometry n) (d A h e : ℕ)
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (W : Submodule ℂ (totalSpace (σ := Fin n) (K := ℂ) E))
    (hi : KernelParent h e I) :
    (kernelChildList G d A h e I W).length ≤
      kernelCountBudget d h e * patchCountBudget n A h (kernelDegreeBudget d h e) ∧
    (∀ C ∈ kernelChildList G d A h e I W,
      GoodPatchPiece I G.points A h (patchDegreeBudget n A h (kernelDegreeBudget d h e)) G.height C ∧
      stagedKernelPolynomials d E W ⊆ C.1 ∧ affineDimension C.1 ≤ affineDimension I ∧
      (¬ stagedKernelPolynomials d E W ⊆ I → affineDimension C.1 < affineDimension I)) ∧
    ∀ z ∈ G.points, PointOn I z →
      (∀ p ∈ stagedKernelPolynomials d E W, eval (fun l => (z l : ℂ)) p = 0) →
      ∃ C ∈ kernelChildList G d A h e I W, PatchPieceCovers C z := by
  classical
  let := hi.1
  simpa only [kernelChildList,dite_eq_left hi] using
    (bounded_kernel_patch_cover (A := A) (stagedKernelPolynomials d E W)
      (stagedKernelPolynomials_degree W) I hi.2.1 hi.2.2 G.points G.height
      G.one_le_height G.bounded).choose_spec

theorem firstCoveringChild_spec {n : ℕ} (z : Fin n → ℤ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n))
    (hL : ∃ C ∈ L, PatchPieceCovers C z) :
    firstCoveringChild z s L ∈ L ∧ PatchPieceCovers (firstCoveringChild z s L) z := by
  classical
  simp only [firstCoveringChild]
  cases hh : L.find? (fun C => decide (PatchPieceCovers C z)) with
  | none =>
    obtain ⟨C,hC,hcov⟩ := hL
    have hc := List.find?_eq_none.mp hh C hC
    simp [hcov] at hc
  | some C =>
    simp only [Option.getD_some]
    have hc : decide (PatchPieceCovers C z) = true :=
      List.find?_some (p := fun C => decide (PatchPieceCovers C z)) hh
    exact ⟨List.mem_of_find?_eq_some hh,of_decide_eq_true hc⟩

open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem kernel_height_pow_bound (m d : ℕ) (H : ℝ) (hH : 1 ≤ H) :
    integralKernelHeight m (H^d) ≤ kernelHeightConstant m * H^(2*d*(m+1)) := by
  have hpow : 1 ≤ (H^d)^2 := one_le_pow₀ (one_le_pow₀ hH)
  have ha : 1+(m:ℝ)^2*(H^d)^2 ≤ (1+(m:ℝ)^2)*(H^d)^2 := by nlinarith
  have hb : 1+(m:ℝ)*(H^d)^2 ≤ (1+(m:ℝ))*(H^d)^2 := by nlinarith
  unfold integralKernelHeight
  calc
    (1+(m:ℝ)^2*(H^d)^2) * m.factorial * (1+(m:ℝ)*(H^d)^2)^m ≤
        ((1+(m:ℝ)^2)*(H^d)^2) * m.factorial * (((1+(m:ℝ))*(H^d)^2)^m) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _)
      · exact pow_le_pow_left₀ (by positivity) hb _
      · positivity
      · positivity
    _ = kernelHeightConstant m * H^(2*d*(m+1)) := by
      rw [kernelHeightConstant,show 2*d*(m+1) = d*2*(m+1) by ring]
      simp only [pow_mul,mul_pow,pow_succ]
      ring

theorem minorSizeConstant_nonneg (n d m : ℕ) : 0 ≤ minorSizeConstant n d m := by
  unfold minorSizeConstant kernelHeightConstant
  positivity

theorem bounded_minor_height {n d : ℕ} {P : IntegerPatch n}
    (hdeg : ∀ i, (P.equations i).totalDegree ≤ d) (H : ℝ) (hH : 1 ≤ H)
    (hc : ∀ i a, |(((P.equations i).coeff a : ℤ) : ℝ)| ≤
      integralKernelHeight ((d+n).choose n) (H^d))
    (z : Fin n → ℤ) (hz : ∀ l, |(z l : ℝ)| ≤ H) :
    |((eval z P.minor : ℤ) : ℝ)| ≤
      minorSizeConstant n d (Fintype.card ↥(P.freeᶜ)) *
        H^(minorSizeExponent n d (Fintype.card ↥(P.freeᶜ))) := by
  let M := (d+n).choose n
  let m := Fintype.card ↥(P.freeᶜ)
  have hC : 0 ≤ integralKernelHeight M (H^d) := by unfold integralKernelHeight; positivity
  have hb := eval_jacobian_minor_abs_le P.equations Subtype.val d hdeg
    (integralKernelHeight M (H^d)) H hC hH hc z hz
  have hi : (M:ℝ)*((d:ℝ)*integralKernelHeight M (H^d))*H^d ≤
      ((M:ℝ)*(d:ℝ)*kernelHeightConstant M)*H^(2*d*(M+1)+d) := by
    calc
      _ ≤ (M:ℝ)*((d:ℝ)*(kernelHeightConstant M * H^(2*d*(M+1))))*H^d := by
        gcongr
        exact kernel_height_pow_bound M d H hH
      _ = _ := by rw [pow_add]; ring
  calc
    |((eval z P.minor : ℤ) : ℝ)| ≤ (m.factorial:ℝ)*
        ((M:ℝ)*((d:ℝ)*integralKernelHeight M (H^d))*H^d)^m := by
      simpa only [IntegerPatch.minor, m, M, Fintype.card_fin] using hb
    _ ≤ (m.factorial:ℝ)*(((M:ℝ)*(d:ℝ)*kernelHeightConstant M)*H^(2*d*(M+1)+d))^m := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply pow_le_pow_left₀ _ hi
      positivity
    _ = _ := by
      simp only [minorSizeConstant,minorSizeExponent,mul_pow,pow_mul,M,m]
      ring

theorem uniform_patch_minor_height (n D : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ B : ℕ, ∀ (P : IntegerPatch n) (H : ℝ),
      1 ≤ H → P.Bounded D H → ∀ z : Fin n → ℤ,
        (∀ l, |(z l : ℝ)| ≤ H) → |((eval z P.minor : ℤ) : ℝ)| ≤ C*H^B := by
  classical
  let C : ℝ := 1 + ∑ d ∈ Finset.range (D+1), ∑ m ∈ Finset.range (n+1), minorSizeConstant n d m
  let B : ℕ := ∑ d ∈ Finset.range (D+1), ∑ m ∈ Finset.range (n+1), minorSizeExponent n d m
  have hnonneg : ∀ d, 0 ≤ ∑ m ∈ Finset.range (n+1), minorSizeConstant n d m := fun d =>
    Finset.sum_nonneg (fun m _ => minorSizeConstant_nonneg n d m)
  have hsum : 0 ≤ ∑ d ∈ Finset.range (D+1), ∑ m ∈ Finset.range (n+1),
      minorSizeConstant n d m := Finset.sum_nonneg (fun d _ => hnonneg d)
  refine ⟨C, by dsimp [C]; linarith, B, ?_⟩
  intro P H hH hP z hz
  obtain ⟨d,hd,hdeg,hcoeff⟩ := hP
  let m := Fintype.card ↥(P.freeᶜ)
  have hm : m ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun x : Fin n => x ∈ P.freeᶜ)
  have hdmem : d ∈ Finset.range (D+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hd)
  have hmmem : m ∈ Finset.range (n+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
  have hCs : minorSizeConstant n d m ≤ C := by
    have h₁ := Finset.single_le_sum (fun j _ => minorSizeConstant_nonneg n d j) hmmem
    have h₂ := Finset.single_le_sum (fun j _ => hnonneg j) hdmem
    dsimp [C]
    linarith
  have hBs : minorSizeExponent n d m ≤ B :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (minorSizeExponent n d j)) hmmem).trans
      (Finset.single_le_sum (fun j _ => Nat.zero_le
        (∑ x ∈ Finset.range (n+1), minorSizeExponent n j x)) hdmem)
  exact (bounded_minor_height hdeg H hH hcoeff z hz).trans
    (mul_le_mul hCs (pow_le_pow_right₀ hH hBs) (by positivity) (by
      exact (minorSizeConstant_nonneg n d m).trans hCs))

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_AdaptiveRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators

namespace QuarticPowerFree

theorem equationRank_mono {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] {W W' : Submodule K V} (h : W ≤ W') :
    equationRank W' ≤ equationRank W := by
  simp only [equationRank, Submodule.finrank_quotient]
  exact Nat.sub_le_sub_left (Submodule.finrank_mono h) _

theorem equationRank_eq_iff_of_le {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] {W W' : Submodule K V} (h : W ≤ W') :
    equationRank W = equationRank W' ↔ W = W' := by
  constructor
  · intro he
    apply Submodule.eq_of_le_of_finrank_eq h
    have h₁ := Submodule.finrank_quotient_add_finrank W
    have h₂ := Submodule.finrank_quotient_add_finrank W'
    dsimp [equationRank] at he
    omega
  · rintro rfl; rfl

variable {K V σ α : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (W : ℕ → σ → α → Submodule K V)
variable (next : ℕ → σ → Submodule K V → σ)

variable [Module.Finite K V]

theorem adaptiveCode_lt (n i : ℕ) (s : σ) (a : α) :
    adaptiveCode W next n i s a < (Module.finrank K V + 1)^n := by
  induction n generalizing i s with
  | zero => simp [adaptiveCode]
  | succ n ih =>
    have hr : equationRank (W i s a) ≤ Module.finrank K V := by
      rw [equationRank, Submodule.finrank_quotient]
      exact Nat.sub_le _ _
    have ht := ih (i+1) (next i s (W i s a))
    simp only [adaptiveCode, pow_succ]
    nlinarith

theorem adaptiveCode_mono_stable (a b : α)
    (hW : ∀ i s, W i s a ≤ W i s b) (n i : ℕ) (s : σ) :
    adaptiveCode W next n i s b ≤ adaptiveCode W next n i s a ∧
    (adaptiveCode W next n i s b = adaptiveCode W next n i s a →
      adaptiveStates W next n i s b = adaptiveStates W next n i s a) := by
  induction n generalizing i s with
  | zero => simp [adaptiveCode, adaptiveStates]
  | succ n ih =>
    have hr := equationRank_mono (hW i s)
    by_cases he : equationRank (W i s a) = equationRank (W i s b)
    · have hw := (equationRank_eq_iff_of_le (hW i s)).mp he
      have hh := ih (i+1) (next i s (W i s a))
      simp only [adaptiveCode, adaptiveStates, ← hw]
      exact ⟨Nat.add_le_add_left hh.1 _, fun h => congrArg (List.cons s) (hh.2 (Nat.add_left_cancel h))⟩
    · have hl : equationRank (W i s b) + 1 ≤ equationRank (W i s a) := by omega
      have ht := adaptiveCode_lt W next n (i+1) (next i s (W i s b)) b
      have hstrict : adaptiveCode W next (n+1) i s b < adaptiveCode W next (n+1) i s a := by
        simp only [adaptiveCode]
        nlinarith
      exact ⟨hstrict.le,fun he => (hstrict.ne he).elim⟩

end QuarticPowerFree

open scoped BigOperators

namespace QuarticPowerFree

theorem sum_subsets_erase {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (P : Finset α) (t : ℕ) (f : Finset α → α → M) :
    (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S, f (S.erase q) q) =
      ∑ B ∈ P.powersetCard t, ∑ q ∈ P \ B, f B q := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun y _ => ⟨y.1.erase y.2, y.2⟩)
  · intro y hy
    obtain ⟨hS, hq⟩ := Finset.mem_sigma.mp hy
    obtain ⟨hSP, hScard⟩ := Finset.mem_powersetCard.mp hS
    apply Finset.mem_sigma.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      exact ⟨(Finset.erase_subset _ _).trans hSP,
        by rw [Finset.card_erase_of_mem hq, hScard]; omega⟩
    · exact Finset.mem_sdiff.mpr ⟨hSP hq, Finset.notMem_erase _ _⟩
  · intro y hy z hz heq
    have hq : y.2 = z.2 := congrArg Sigma.snd heq
    have hS : y.1.erase y.2 = z.1.erase z.2 := congrArg Sigma.fst heq
    have hyq := (Finset.mem_sigma.mp hy).2
    have hzq := (Finset.mem_sigma.mp hz).2
    have : y.1 = z.1 := by
      calc
        y.1 = insert y.2 (y.1.erase y.2) := (Finset.insert_erase hyq).symm
        _ = insert z.2 (z.1.erase z.2) := by rw [hS, hq]
        _ = z.1 := Finset.insert_erase hzq
    exact Sigma.ext this (heq_of_eq hq)
  · intro y hy
    obtain ⟨hB, hq⟩ := Finset.mem_sigma.mp hy
    obtain ⟨hBP, hBcard⟩ := Finset.mem_powersetCard.mp hB
    obtain ⟨hqP, hqB⟩ := Finset.mem_sdiff.mp hq
    refine ⟨⟨insert y.2 y.1, y.2⟩, ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      constructor
      · exact Finset.mem_powersetCard.mpr ⟨Finset.insert_subset hqP hBP,
          by rw [Finset.card_insert_of_notMem hqB, hBcard]⟩
      · exact Finset.mem_insert_self _ _
    · simp only [Finset.erase_insert hqB]
  · intro y _
    rfl

theorem subset_incidence_card {α : Type*} [DecidableEq α] (P : Finset α) (t : ℕ) :
    ((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card =
      ((P.card : ℝ) - t) * (P.powersetCard t).card := by
  have h := sum_subsets_erase P t (fun _ _ => (1 : ℝ))
  have hleft : (∑ S ∈ P.powersetCard (t + 1), ∑ _q ∈ S, (1 : ℝ)) =
      ((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card := by
    have heq : ∀ S ∈ P.powersetCard (t + 1), (∑ _q ∈ S, (1 : ℝ)) = (t + 1 : ℕ) := by
      intro S hS
      simp [(Finset.mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hright : (∑ B ∈ P.powersetCard t, ∑ _q ∈ P \ B, (1 : ℝ)) =
      ((P.card : ℝ) - t) * (P.powersetCard t).card := by
    have heq : ∀ B ∈ P.powersetCard t, (∑ _q ∈ P \ B, (1 : ℝ)) = (P.card : ℝ) - t := by
      intro B hB
      obtain ⟨hBP, hBt⟩ := Finset.mem_powersetCard.mp hB
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_sdiff,
        Finset.inter_eq_left.mpr hBP, hBt]
      exact Nat.cast_sub (hBt ▸ Finset.card_le_card hBP)
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hleft, hright] at h
  exact h

theorem sum_subsets_members {α : Type*} (P : Finset α) (t : ℕ)
    (f : Finset α → ℝ) :
    (∑ S ∈ P.powersetCard t, ∑ _q ∈ S, f S) =
      (t : ℝ) * ∑ S ∈ P.powersetCard t, f S := by
  have heq : ∀ S ∈ P.powersetCard t, (∑ _q ∈ S, f S) = (t : ℝ) * f S := by
    intro S hS
    simp only [Finset.sum_const, nsmul_eq_mul, (Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_congr rfl heq, Finset.mul_sum]

theorem sum_subsets_complement {α : Type*} [DecidableEq α] (P : Finset α) (t : ℕ)
    (f : Finset α → ℝ) :
    (∑ S ∈ P.powersetCard t, ∑ _q ∈ P \ S, f S) =
      ((P.card : ℝ) - t) * ∑ S ∈ P.powersetCard t, f S := by
  have heq : ∀ S ∈ P.powersetCard t, (∑ _q ∈ P \ S, f S) = ((P.card : ℝ) - t) * f S := by
    intro S hS
    obtain ⟨hSP, hSt⟩ := Finset.mem_powersetCard.mp hS
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hSP, hSt,
      Nat.cast_sub (hSt ▸ Finset.card_le_card hSP)]
  rw [Finset.sum_congr rfl heq, Finset.mul_sum]

theorem subset_deletion_mean {α : Type*} [DecidableEq α]
    (P : Finset α) (t : ℕ) (ht : t < P.card) (f : Finset α → ℝ) :
    (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S, f (S.erase q)) /
        (((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card) = subsetMean P t f := by
  rw [sum_subsets_erase P t (fun S _ => f S), sum_subsets_complement,
    subset_incidence_card, subsetMean]
  exact mul_div_mul_left _ _ (sub_ne_zero.mpr (ne_of_gt (Nat.cast_lt.mpr ht)))

theorem subset_marked_mean {α : Type*} (P : Finset α) (t : ℕ)
    (f : Finset α → ℝ) :
    (∑ S ∈ P.powersetCard (t + 1), ∑ _q ∈ S, f S) /
        (((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card) = subsetMean P (t + 1) f := by
  rw [sum_subsets_members, subsetMean]
  exact mul_div_mul_left _ _ (by positivity)

theorem bad_indicator_le_rank_drop {α : Type*} [DecidableEq α]
    (R : Finset α → ℕ) (bad : Finset α → Finset α)
    (S : Finset α) (q : α)
    (hmono : R S ≤ R (S.erase q))
    (hstable : R S = R (S.erase q) → bad S = bad (S.erase q)) :
    (if q ∈ bad S then (1 : ℝ) else 0) ≤
      ((R (S.erase q) : ℝ) - R S) + if q ∈ bad (S.erase q) then 1 else 0 := by
  by_cases heq : R S = R (S.erase q)
  · rw [hstable heq, heq, sub_self, zero_add]
  · have hle : R S + 1 ≤ R (S.erase q) := by omega
    have hle' : (R S : ℝ) + 1 ≤ R (S.erase q) := by exact_mod_cast hle
    split_ifs <;> linarith

theorem deleted_bad_sum_le {α : Type*} [DecidableEq α]
    (P : Finset α) (t : ℕ) (bad : Finset α → Finset α) (D : ℕ)
    (hbad : ∀ S ⊆ P, (P ∩ bad S).card ≤ D) :
    (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S,
      if q ∈ bad (S.erase q) then (1 : ℝ) else 0) ≤
        (P.powersetCard t).card * (D : ℝ) := by
  rw [sum_subsets_erase P t (fun S q => if q ∈ bad S then (1 : ℝ) else 0)]
  calc
    _ ≤ ∑ S ∈ P.powersetCard t, (D : ℝ) := by
      apply Finset.sum_le_sum
      intro S hS
      rw [Finset.sum_boole]
      apply Nat.cast_le.mpr
      apply le_trans (Finset.card_le_card ?_) (hbad S (Finset.mem_powersetCard.mp hS).1)
      intro q hq
      obtain ⟨hqP, hqbad⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hqP).1, hqbad⟩
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem deletion_one_step {α : Type*} [DecidableEq α]
    (P : Finset α) (t : ℕ) (ht : t < P.card)
    (R : Finset α → ℕ) (bad : Finset α → Finset α) (D : ℕ)
    (hmono : ∀ S ⊆ P, ∀ q ∈ S, R S ≤ R (S.erase q))
    (hstable : ∀ S ⊆ P, ∀ q ∈ S, R S = R (S.erase q) → bad S = bad (S.erase q))
    (hbad : ∀ S ⊆ P, (P ∩ bad S).card ≤ D) :
    badFraction P (t + 1) bad ≤
      subsetMean P t (fun S => R S) - subsetMean P (t + 1) (fun S => R S) +
        (D : ℝ) / ((P.card : ℝ) - t) := by
  have hcard : 0 < (P.powersetCard (t + 1)).card :=
    Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr (by omega))
  have hsmall : 0 < (P.powersetCard t).card :=
    Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr (by omega))
  have hden : 0 < ((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card :=
    mul_pos (by positivity) (Nat.cast_pos.mpr hcard)
  have hsum :
      (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S, if q ∈ bad S then (1 : ℝ) else 0) ≤
      (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S, (R (S.erase q) : ℝ)) -
      (∑ S ∈ P.powersetCard (t + 1), ∑ _q ∈ S, (R S : ℝ)) +
      (∑ S ∈ P.powersetCard (t + 1), ∑ q ∈ S,
        if q ∈ bad (S.erase q) then (1 : ℝ) else 0) := by
    simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro S hS
    apply Finset.sum_le_sum
    intro q hq
    exact bad_indicator_le_rank_drop R bad S q
      (hmono S (Finset.mem_powersetCard.mp hS).1 q hq)
      (hstable S (Finset.mem_powersetCard.mp hS).1 q hq)
  have hsum' := div_le_div_of_nonneg_right hsum hden.le
  rw [add_div, sub_div, subset_deletion_mean P t ht (fun S => (R S : ℝ)),
    subset_marked_mean P t (fun S => (R S : ℝ))] at hsum'
  have hbad' := div_le_div_of_nonneg_right (deleted_bad_sum_le P t bad D hbad) hden.le
  have herr : ((P.powersetCard t).card * (D : ℝ)) /
      (((t + 1 : ℕ) : ℝ) * (P.powersetCard (t + 1)).card) =
        (D : ℝ) / ((P.card : ℝ) - t) := by
    rw [subset_incidence_card, mul_comm ((P.card : ℝ) - t)]
    exact mul_div_mul_left _ _ (ne_of_gt (Nat.cast_pos.mpr hsmall))
  rw [herr] at hbad'
  change _ ≤ _ at hsum'
  dsimp only [badFraction]
  linarith

theorem subsetMean_record_bounds {α : Type*}
    (P : Finset α) (t : ℕ) (ht : t ≤ P.card)
    (R : Finset α → ℕ) (B : ℕ) (hR : ∀ S ⊆ P, R S ≤ B) :
    0 ≤ subsetMean P t (fun S => R S) ∧ subsetMean P t (fun S => R S) ≤ B := by
  have hcard : 0 < (P.powersetCard t).card :=
    Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr ht)
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun S _ => Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · rw [subsetMean, div_le_iff₀ (Nat.cast_pos.mpr hcard)]
    calc
      _ ≤ ∑ _S ∈ P.powersetCard t, (B : ℝ) := by
        apply Finset.sum_le_sum
        intro S hS
        exact Nat.cast_le.mpr (hR S (Finset.mem_powersetCard.mp hS).1)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem deletion_average_bound {α : Type*} [DecidableEq α]
    (P : Finset α) (ell T : ℕ) (hT : 0 < T) (hsize : ell + T < P.card)
    (R : Finset α → ℕ) (bad : Finset α → Finset α) (B D : ℕ)
    (hR : ∀ S ⊆ P, R S ≤ B)
    (hmono : ∀ S ⊆ P, ∀ q ∈ S, R S ≤ R (S.erase q))
    (hstable : ∀ S ⊆ P, ∀ q ∈ S, R S = R (S.erase q) → bad S = bad (S.erase q))
    (hbad : ∀ S ⊆ P, (P ∩ bad S).card ≤ D) :
    (∑ j ∈ Finset.range T, badFraction P (ell + j + 1) bad) / (T : ℝ) ≤
      (B : ℝ) / T + (D : ℝ) / ((P.card : ℝ) - (ell + T)) := by
  let F : ℕ → ℝ := fun j => subsetMean P (ell + j) (fun S => R S)
  let err : ℝ := (D : ℝ) / ((P.card : ℝ) - (ell + T))
  have hgap : 0 < (P.card : ℝ) - (ell + T) := by
    apply sub_pos.mpr
    exact_mod_cast hsize
  have hstep (j : ℕ) (hj : j ∈ Finset.range T) :
      badFraction P (ell + j + 1) bad ≤ F j - F (j + 1) + err := by
    have hjt := Finset.mem_range.mp hj
    have ht : ell + j < P.card := by omega
    have h := deletion_one_step P (ell + j) ht R bad D hmono hstable hbad
    have herr : (D : ℝ) / ((P.card : ℝ) - (ell + j)) ≤ err := by
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hgap
      have : (j : ℝ) ≤ T := by exact_mod_cast (Nat.le_of_lt hjt)
      linarith
    dsimp [F]
    simp only [Nat.add_assoc, Nat.cast_add] at h ⊢
    exact h.trans (by linarith)
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib, Finset.sum_range_sub', Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hsum
  have hupper := (subsetMean_record_bounds P ell (by omega) R B hR).2
  have hlower := (subsetMean_record_bounds P (ell + T) (by omega) R B hR).1
  have hdiff : F 0 - F T ≤ (B : ℝ) := by
    dsimp [F]
    simpa only [Nat.add_zero] using sub_le_self _ hlower |>.trans hupper
  have hsum' : (∑ j ∈ Finset.range T, badFraction P (ell + j + 1) bad) ≤
      (B : ℝ) + T * err := by linarith
  have hT' : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  calc
    _ ≤ ((B : ℝ) + T * err) / T := div_le_div_of_nonneg_right hsum' hT'.le
    _ = (B : ℝ) / T + err := by rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hT')]
    _ = _ := rfl

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PrimeBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

theorem product_distinct_prime_divisors_le (a : ℤ) (ha : a ≠ 0)
    (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime)
    (hd : ∀ p ∈ P, (p : ℤ) ∣ a) :
    (∏ p ∈ P, (p : ℝ)) ≤ |(a : ℝ)| := by
  have hn : a.natAbs ≠ 0 := (Int.natAbs_pos.mpr ha).ne'
  have hs : P ⊆ a.natAbs.primeFactors := by
    intro p h
    exact Nat.mem_primeFactors.mpr ⟨hp p h,
      by simpa using Int.natAbs_dvd_natAbs.mpr (hd p h), hn⟩
  have hh := Nat.le_of_dvd (Int.natAbs_pos.mpr ha)
    ((Finset.prod_dvd_prod_of_subset P a.natAbs.primeFactors id hs).trans
      (Nat.prod_primeFactors_dvd a.natAbs))
  have he : (a.natAbs : ℝ) = |(a : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [← he, ← Nat.cast_prod]
  exact_mod_cast hh

theorem card_large_prime_divisors_le (a : ℤ) (ha : a ≠ 0)
    (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) (hd : ∀ p ∈ P, (p : ℤ) ∣ a)
    (X ζ B : ℝ) (hX : 1 < X) (hζ : 0 < ζ)
    (hsmall : ∀ p ∈ P, X ^ ζ ≤ (p : ℝ)) (hlarge : |(a : ℝ)| ≤ X ^ B) :
    (P.card : ℝ) ≤ B / ζ := by
  have hx : 0 ≤ X := (zero_lt_one.trans hX).le
  have h : X ^ (ζ * (P.card : ℝ)) ≤ X ^ B := by
    rw [Real.rpow_mul hx, Real.rpow_natCast]
    calc
      (X ^ ζ) ^ P.card = ∏ _p ∈ P, X ^ ζ := (Finset.prod_const _).symm
      _ ≤ ∏ p ∈ P, (p : ℝ) := Finset.prod_le_prod
        (fun _ _ => (Real.rpow_pos_of_pos (zero_lt_one.trans hX) ζ).le) hsmall
      _ ≤ |(a : ℝ)| := product_distinct_prime_divisors_le a ha P hp hd
      _ ≤ X ^ B := hlarge
  rw [le_div_iff₀ hζ]
  simpa [mul_comm] using (Real.rpow_le_rpow_left_iff hX).mp h

theorem card_large_prime_divisors_le_floor (a : ℤ) (ha : a ≠ 0)
    (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) (hd : ∀ p ∈ P, (p : ℤ) ∣ a)
    (X ζ B : ℝ) (hX : 1 < X) (hζ : 0 < ζ)
    (hsmall : ∀ p ∈ P, X ^ ζ ≤ (p : ℝ)) (hlarge : |(a : ℝ)| ≤ X ^ B) :
    P.card ≤ ⌊B / ζ⌋₊ :=
  Nat.le_floor (card_large_prime_divisors_le a ha P hp hd X ζ B hX hζ hsmall hlarge)

open scoped BigOperators

theorem adaptiveStates_length {K V σ α : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : ℕ → σ → α → Submodule K V) (next : ℕ → σ → Submodule K V → σ)
    (n i : ℕ) (s : σ) (a : α) : (adaptiveStates W next n i s a).length = n+1 := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih => simp only [adaptiveStates, List.length_cons, ih]

theorem list_minor_product_bound {σ : Type*} (l : List σ) (minor : σ → ℤ)
    (X B : ℝ) (hX : 0 < X)
    (hminor : ∀ s ∈ l, minor s ≠ 0 ∧ |(minor s : ℝ)| ≤ X^B) :
    (l.map minor).prod ≠ 0 ∧ |(((l.map minor).prod : ℤ) : ℝ)| ≤ X^(B*(l.length : ℝ)) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := hminor x (by simp)
    have ht := ih (fun s hs => hminor s (by simp [hs]))
    constructor
    · simpa only [List.map_cons, List.prod_cons] using mul_ne_zero hx.1 ht.1
    · simp only [List.map_cons, List.prod_cons, Int.cast_mul, abs_mul,
        List.length_cons, Nat.cast_add, Nat.cast_one, mul_add, mul_one,
        Real.rpow_add hX]
      exact (mul_le_mul hx.2 ht.2 (abs_nonneg _) (Real.rpow_nonneg hX.le _)).trans_eq (mul_comm _ _)

theorem adaptive_deletion_bound {K V σ : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V]
    (W : ℕ → σ → Finset ℕ → Submodule K V)
    (next : ℕ → σ → Submodule K V → σ)
    (hW : ∀ i s A B, A ⊆ B → W i s A ≤ W i s B)
    (minor : σ → ℤ) (n : ℕ) (s : σ)
    (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime)
    (X ζ B : ℝ) (hX : 1 < X) (hζ : 0 < ζ)
    (hsmall : ∀ p ∈ P, X^ζ ≤ (p : ℝ))
    (hminor : ∀ A ⊆ P, ∀ t ∈ adaptiveStates W next n 0 s A,
      minor t ≠ 0 ∧ |(minor t : ℝ)| ≤ X^B)
    (ell T : ℕ) (hT : 0 < T) (hsize : ell+T < P.card) :
    let bad := fun A => P.filter fun p : ℕ =>
      (p : ℤ) ∣ ((adaptiveStates W next n 0 s A).map minor).prod
    (∑ j ∈ Finset.range T, badFraction P (ell+j+1) bad) / (T : ℝ) ≤
      (((Module.finrank K V+1)^n : ℕ) : ℝ) / T +
      (⌊(B*(n+1:ℕ))/ζ⌋₊ : ℝ) / ((P.card : ℝ) - (ell+T)) := by
  classical
  intro bad
  let R := fun A => adaptiveCode W next n 0 s A
  apply deletion_average_bound P ell T hT hsize R bad
    ((Module.finrank K V+1)^n) ⌊(B*(n+1:ℕ))/ζ⌋₊
  · intro A _
    exact (adaptiveCode_lt W next n 0 s A).le
  · intro A _ q _
    exact (adaptiveCode_mono_stable W next (A.erase q) A
      (fun i s => hW i s _ _ (Finset.erase_subset _ _)) n 0 s).1
  · intro A _ q _ he
    have hs := (adaptiveCode_mono_stable W next (A.erase q) A
      (fun i s => hW i s _ _ (Finset.erase_subset _ _)) n 0 s).2 he
    dsimp [bad]
    rw [hs]
  · intro A hAP
    let l := adaptiveStates W next n 0 s A
    have hb := list_minor_product_bound l minor X B (zero_lt_one.trans hX) (hminor A hAP)
    have hl : l.length = n+1 := adaptiveStates_length W next n 0 s A
    have hin : P ∩ bad A = bad A := Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
    rw [hin]
    apply card_large_prime_divisors_le_floor _ hb.1 _
      (fun p h => hp p (Finset.mem_filter.mp h).1)
      (fun _ h => (Finset.mem_filter.mp h).2) X ζ (B*(n+1:ℕ)) hX hζ
      (fun p h => hsmall p (Finset.mem_filter.mp h).1)
    simpa only [hl] using hb.2

open scoped BigOperators

theorem blockSet_spec {P : Finset ℕ} {ell T : ℕ} (a : BlockSample P ell T) :
    blockSet a ⊆ P ∧ (blockSet a).card = ell+a.1.val+1 :=
  Finset.mem_powersetCard.mp a.2.property

theorem blockWeight_nonneg (P : Finset ℕ) (ell T : ℕ)
    (a : BlockSample P ell T) : 0 ≤ blockWeight P ell T a := by
  unfold blockWeight
  positivity

theorem blockWeight_sum (P : Finset ℕ) (ell T : ℕ)
    (hT : 0 < T) (hsize : ell+T ≤ P.card) :
    ∑ a : BlockSample P ell T, blockWeight P ell T a = 1 := by
  classical
  change (∑ a : Σ j : Fin T, (P.powersetCard (ell+j.val+1)),
    ((T : ℝ) * ((P.powersetCard (ell+a.1.val+1)).card : ℝ))⁻¹) = 1
  rw [Fintype.sum_sigma]
  have he (j : Fin T) :
      (∑ _a : (P.powersetCard (ell+j.val+1)),
        ((T : ℝ) * ((P.powersetCard (ell+j.val+1)).card : ℝ))⁻¹) = (T : ℝ)⁻¹ := by
    have hc : 0 < (P.powersetCard (ell+j.val+1)).card :=
      Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr (by omega))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    field_simp
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hT.ne')

theorem blockWeight_bad_average (P : Finset ℕ) (ell T : ℕ)
    (bad : Finset ℕ → Finset ℕ) :
    (∑ a : BlockSample P ell T, blockWeight P ell T a *
      ((∑ q ∈ blockSet a, if q ∈ bad (blockSet a) then (1 : ℝ) else 0) /
        (blockSet a).card)) =
      (∑ j ∈ Finset.range T, badFraction P (ell+j+1) bad) / T := by
  classical
  change (∑ a : Σ j : Fin T, (P.powersetCard (ell+j.val+1)),
    ((T : ℝ) * ((P.powersetCard (ell+a.1.val+1)).card : ℝ))⁻¹ *
      ((∑ q ∈ a.2.val, if q ∈ bad a.2.val then (1 : ℝ) else 0) / a.2.val.card)) = _
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [badFraction]
  rw [Finset.sum_coe_sort (P.powersetCard (ell+j.val+1))
    (fun S : Finset ℕ => ((T : ℝ) * ((P.powersetCard (ell+j.val+1)).card : ℝ))⁻¹ *
      ((∑ q ∈ S, if q ∈ bad S then (1 : ℝ) else 0) / S.card)),
    Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_powersetCard.mp ha).2]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem independent_average_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (w : ∀ i, Ω i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hsum : ∀ i, ∑ a, w i a = 1) (i : ι)
    (F : (∀ j, Ω j) → ℝ) (C : ℝ)
    (hF : ∀ x, (∑ a, w i a * F (Function.update x i a)) ≤ C) :
    (∑ x, (∏ j, w j (x j)) * F x) ≤ C := by
  classical
  let E := Equiv.piSplitAt i Ω
  let W : (∀ j : {j // j ≠ i}, Ω j) → ℝ := fun x => ∏ j : {j // j ≠ i}, w j.val (x j)
  have hs : ∑ x, W x = 1 := by
    rw [show (∑ x, W x) = ∑ x : (∀ j : {j // j ≠ i}, Ω j), ∏ j : {j // j ≠ i}, w j.val (x j) from rfl, ← Fintype.prod_sum]
    simp only [hsum, Finset.prod_const_one]
  have hwE (x : ∀ j, Ω j) : (∏ j, w j (x j)) = w i (x i) * W (E x).2 := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j => w j (x j)) (Finset.mem_univ i)]
    congr 1
    exact Finset.prod_subtype (p := fun j => j ≠ i) (Finset.univ.erase i) (by simp) (fun j => w j (x j))
  have hE (x : (∀ j : {j // j ≠ i}, Ω j)) (a b : Ω i) :
      Function.update (E.symm (a,x)) i b = E.symm (b,x) := by
    funext j
    by_cases h : j = i
    · subst j; simp [E, Equiv.piSplitAt]
    · simp [E, Equiv.piSplitAt, h]
  have hEq : (∑ x, (∏ j, w j (x j)) * F x) =
      ∑ x, W x * (∑ a, w i a * F (E.symm (a,x))) := by
    rw [Fintype.sum_equiv E _ (fun z => w i z.1 * W z.2 * F (E.symm z))]
    · rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    · intro x
      rw [hwE, E.symm_apply_apply]
      rfl
  rw [hEq]
  have hFin (x : ∀ j : {j // j ≠ i}, Ω j) :
      (∑ a, w i a * F (E.symm (a,x))) ≤ C := by
    by_cases h : Nonempty (Ω i)
    · obtain ⟨a⟩ := h
      simpa only [hE] using hF (E.symm (a,x))
    · have := not_nonempty_iff.mp h
      have hz := hsum i
      simp at hz
  calc
    _ ≤ ∑ x, W x * C := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (hFin x) (Finset.prod_nonneg fun j _ => hw j.val (x j))
    _ = C := by rw [← Finset.sum_mul, hs, one_mul]

theorem exists_many_regular {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1)
    (bad : Ω → ι → Prop) [DecidableRel bad]
    (η : ℝ) (hbad : ∀ z, (∑ a, w a * if bad a z then (1 : ℝ) else 0) ≤ η) :
    ∃ a : Ω, ((Finset.univ.filter fun z => ¬ bad a z).card : ℝ) ≥
      (1-η) * Fintype.card ι := by
  classical
  have havg : (∑ a, w a * ((Finset.univ.filter fun z => bad a z).card : ℝ)) ≤
      η * Fintype.card ι := by
    simp_rw [← Finset.sum_boole, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact (Finset.sum_le_sum fun z _ => hbad z).trans_eq (by simp; ring)
  have hex : ∃ a : Ω, ((Finset.univ.filter fun z => bad a z).card : ℝ) ≤ η * Fintype.card ι := by
    by_contra h
    push Not at h
    have hp : ∃ a, 0 < w a := by
      by_contra h0
      push Not at h0
      have hz : ∀ a, w a = 0 := fun a => le_antisymm (h0 a) (hw a)
      simp [hz] at hsum
    obtain ⟨a,ha⟩ := hp
    have hlt : (∑ b, w b * (η * Fintype.card ι)) <
        ∑ b, w b * ((Finset.univ.filter fun z => bad b z).card : ℝ) := by
      apply Finset.sum_lt_sum
      · intro b _
        exact mul_le_mul_of_nonneg_left (h b).le (hw b)
      · exact ⟨a,Finset.mem_univ _,mul_lt_mul_of_pos_left (h a) ha⟩
    rw [← Finset.sum_mul,hsum,one_mul] at hlt
    linarith
  obtain ⟨a,ha⟩ := hex
  refine ⟨a,?_⟩
  have hc : (Finset.univ.filter fun z => bad a z).card +
      (Finset.univ.filter fun z => ¬ bad a z).card = Fintype.card ι := by
    simpa using Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun z => bad a z)
  have hcr : ((Finset.univ.filter fun z => bad a z).card : ℝ) +
      ((Finset.univ.filter fun z => ¬ bad a z).card : ℝ) = Fintype.card ι := by exact_mod_cast hc
  linarith

theorem bad_blocks_indicator_le {r : ℕ} (b : Fin r → ℝ) (hb : ∀ i, 0 ≤ b i)
    (ξ : ℝ) (hξ : 0 < ξ) :
    (if ∃ i, ξ < b i then (1 : ℝ) else 0) ≤ (∑ i, b i) / ξ := by
  classical
  split_ifs with h
  · obtain ⟨i,hi⟩ := h
    rw [le_div_iff₀ hξ, one_mul]
    exact hi.le.trans (Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i))
  · exact div_nonneg (Finset.sum_nonneg fun i _ => hb i) hξ.le

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_RegularBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

open scoped BigOperators

theorem independent_many_regular {r : ℕ} {S : Type*} [Fintype S]
    {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (w : ∀ i, Ω i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hsum : ∀ i, ∑ a, w i a = 1)
    (b : (∀ i, Ω i) → S → Fin r → ℝ)
    (hb : ∀ x z i, 0 ≤ b x z i) (η ξ : ℝ) (hξ : 0 < ξ)
    (hmean : ∀ z i x, (∑ a, w i a * b (Function.update x i a) z i) ≤ η) :
    ∃ x : ∀ i, Ω i,
      ((Finset.univ.filter fun z : S => ∀ i, b x z i ≤ ξ).card : ℝ) ≥
        (1 - (r : ℝ)*η/ξ) * Fintype.card S := by
  classical
  let W : (∀ i, Ω i) → ℝ := fun x => ∏ i, w i (x i)
  have hW : ∀ x, 0 ≤ W x := fun x => Finset.prod_nonneg fun i _ => hw i (x i)
  have hsumW : ∑ x, W x = 1 := by
    change (∑ x : ∀ i, Ω i, ∏ i, w i (x i)) = 1
    rw [← Fintype.prod_sum]
    simp only [hsum,Finset.prod_const_one]
  have hm (z : S) (i : Fin r) : ∑ x, W x * b x z i ≤ η :=
    independent_average_le w hw hsum i (fun x => b x z i) η (hmean z i)
  have hbad (z : S) :
      (∑ x, W x * if ∃ i, ξ < b x z i then (1 : ℝ) else 0) ≤ (r : ℝ)*η/ξ := by
    calc
      _ ≤ ∑ x, W x * ((∑ i, b x z i)/ξ) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
          (bad_blocks_indicator_le (b x z) (hb x z) ξ hξ) (hW x)
      _ = (∑ i, ∑ x, W x * b x z i)/ξ := by
        simp_rw [← mul_div_assoc,Finset.mul_sum]
        rw [← Finset.sum_div,Finset.sum_comm]
      _ ≤ (∑ _i : Fin r, η)/ξ := div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun i _ => hm z i) hξ.le
      _ = (r : ℝ)*η/ξ := by simp
  obtain ⟨x,hx⟩ := exists_many_regular W hW hsumW
    (fun x z => ∃ i, ξ < b x z i) ((r : ℝ)*η/ξ) hbad
  refine ⟨x,?_⟩
  simpa only [not_exists,not_lt] using hx

lemma adaptiveStates_precomp {K V σ α β : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : ℕ → σ → α → Submodule K V)
    (next : ℕ → σ → Submodule K V → σ) (f : β → α)
    (n i : ℕ) (s : σ) (a : β) :
    adaptiveStates (fun j t b => W j t (f b)) next n i s a =
      adaptiveStates W next n i s (f a) := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih => simp only [adaptiveStates,ih]

lemma selectedBlocks_update {r T : ℕ} {P : Fin r → Finset ℕ}
    {ell : Fin r → ℕ} (a : ∀ i, BlockSample (P i) (ell i) T)
    (i : Fin r) (u : BlockSample (P i) (ell i) T) :
    selectedBlocks (Function.update a i u) = Function.update (selectedBlocks a) i (blockSet u) := by
  funext j
  by_cases h : j = i
  · subst j; simp [selectedBlocks]
  · simp [selectedBlocks,Function.update_of_ne h]

theorem regular_adaptive_blocks {K V σ S : Type*}
    [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] [Fintype S]
    {r : ℕ} (P : Fin r → Finset ℕ) (ell : Fin r → ℕ) (T n : ℕ)
    (W : S → ℕ → σ → (Fin r → Finset ℕ) → Submodule K V)
    (next : S → ℕ → σ → Submodule K V → σ) (start : S → σ)
    (minor : S → σ → ℤ)
    (hW : ∀ z j s B i A A', A ⊆ A' →
      W z j s (Function.update B i A) ≤ W z j s (Function.update B i A'))
    (X ζ B η ξ : ℝ) (hX : 1 < X) (hζ : 0 < ζ) (hξ : 0 < ξ)
    (hp : ∀ i p, p ∈ P i → p.Prime)
    (hsmall : ∀ i p, p ∈ P i → X^ζ ≤ (p : ℝ))
    (hminor : ∀ z A, (∀ i, A i ⊆ P i) →
      ∀ t ∈ adaptiveStates (W z) (next z) n 0 (start z) A,
        minor z t ≠ 0 ∧ |(minor z t : ℝ)| ≤ X^B)
    (hT : 0 < T) (hsize : ∀ i, ell i+T < (P i).card)
    (hη : ∀ i, (((Module.finrank K V+1)^n : ℕ) : ℝ)/T +
      (⌊(B*(n+1:ℕ))/ζ⌋₊ : ℝ)/(((P i).card : ℝ)-(ell i+T)) ≤ η) :
    ∃ A : Fin r → Finset ℕ,
      (∀ i, A i ⊆ P i ∧ ell i < (A i).card ∧ (A i).card ≤ ell i+T) ∧
      ((Finset.univ.filter fun z : S => ∀ i,
        ((∑ p ∈ A i,
          if (p : ℤ) ∣ ((adaptiveStates (W z) (next z) n 0 (start z) A).map (minor z)).prod
          then (1 : ℝ) else 0) / (A i).card) ≤ ξ).card : ℝ) ≥
          (1-(r : ℝ)*η/ξ)*Fintype.card S := by
  classical
  let Ω := fun i => BlockSample (P i) (ell i) T
  let w : ∀ i, Ω i → ℝ := fun i => blockWeight (P i) (ell i) T
  let M := fun z A => ((adaptiveStates (W z) (next z) n 0 (start z) A).map (minor z)).prod
  let b : (∀ i, Ω i) → S → Fin r → ℝ := fun a z i =>
    (∑ p ∈ selectedBlocks a i, if (p : ℤ) ∣ M z (selectedBlocks a) then (1 : ℝ) else 0) /
      (selectedBlocks a i).card
  have hb : ∀ a z i, 0 ≤ b a z i := by
    intro a z i
    exact div_nonneg (Finset.sum_nonneg fun p _ => by split_ifs <;> positivity)
      (Nat.cast_nonneg _)
  have hmean : ∀ z i a, (∑ u, w i u * b (Function.update a i u) z i) ≤ η := by
    intro z i a
    let A₀ := selectedBlocks a
    let Wi := fun j s A => W z j s (Function.update A₀ i A)
    let bad : Finset ℕ → Finset ℕ := fun A => (P i).filter fun p : ℕ =>
      (p : ℤ) ∣ M z (Function.update A₀ i A)
    have hm (A : Finset ℕ) (hA : A ⊆ P i) :
        ∀ t ∈ adaptiveStates Wi (next z) n 0 (start z) A,
          minor z t ≠ 0 ∧ |(minor z t : ℝ)| ≤ X^B := by
      rw [adaptiveStates_precomp]
      apply hminor z
      intro j
      by_cases h : j = i
      · subst j; simpa using hA
      · simpa only [Function.update_of_ne h, A₀, selectedBlocks] using (blockSet_spec (a j)).1
    have hdel := adaptive_deletion_bound Wi (next z)
      (fun j s A A' hAA' => hW z j s A₀ i A A' hAA') (minor z) n (start z)
      (P i) (hp i) X ζ B hX hζ (hsmall i) hm (ell i) T hT (hsize i)
    dsimp only at hdel
    simp only [Wi, adaptiveStates_precomp] at hdel
    change ((∑ j ∈ Finset.range T, badFraction (P i) (ell i+j+1) bad) / T) ≤ _ at hdel
    have heq : (∑ u, w i u * b (Function.update a i u) z i) =
        (∑ j ∈ Finset.range T, badFraction (P i) (ell i+j+1) bad) / T := by
      rw [← blockWeight_bad_average]
      apply Finset.sum_congr rfl
      intro u _
      dsimp only [w,b]
      rw [selectedBlocks_update, Function.update_self]
      congr 2
      apply Finset.sum_congr rfl
      intro p hpU
      have hpP := (blockSet_spec u).1 hpU
      simp only [bad,Finset.mem_filter,hpP,true_and,A₀]
    rw [heq]
    exact hdel.trans (hη i)
  obtain ⟨a,ha⟩ := independent_many_regular w
    (fun i => blockWeight_nonneg (P i) (ell i) T)
    (fun i => blockWeight_sum (P i) (ell i) T hT (hsize i).le)
    b hb η ξ hξ hmean
  refine ⟨selectedBlocks a,?_,ha⟩
  intro i
  obtain ⟨hsub,hcard⟩ := blockSet_spec (a i)
  refine ⟨hsub,?_,?_⟩
  · change ell i < (blockSet (a i)).card
    rw [hcard]; omega
  · change (blockSet (a i)).card ≤ ell i+T
    rw [hcard]
    have := (a i).1.isLt
    omega

open MvPolynomial

theorem cumulativeBlockPrimes_mono {r : ℕ} {B C : Fin r → Finset ℕ}
    (hBC : ∀ j, B j ⊆ C j) (i : ℕ) :
    cumulativeBlockPrimes B i ⊆ cumulativeBlockPrimes C i := by
  classical
  intro p hp
  obtain ⟨j,hj,hp⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨j,hj,hBC j hp⟩

theorem physicalKernel_mono {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (z : Fin n → ℤ) (i : ℕ) (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    {B C : Fin r → Finset ℕ} (hBC : ∀ j, B j ⊆ C j) :
    physicalKernel (E := E) G d z i s B ≤ physicalKernel G d z i s C :=
  stagedEvaluationSpace_mono (evaluationCell_antitone G.points s.1 z
    (cumulativeBlockPrimes_mono hBC i))

theorem physical_step {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (z : Fin n → ℤ) (hz : z ∈ G.points) (i : ℕ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : PhysicalState G h (pathDegreeBudget n d A h e i) z s)
    (B : Fin r → Finset ℕ) :
    let W := physicalKernel (E := E) G d z i s B
    let t := physicalNext G d A h e z i s W
    PhysicalState G h (pathDegreeBudget n d A h e (i+1)) z t ∧
      t ∈ kernelChildList G (d i) A h (pathDegreeBudget n d A h e i) s.1 W ∧
      s.1 ≤ t.1 ∧ stagedKernelPolynomials (d i) E W ⊆ t.1 ∧
      affineDimension t.1 ≤ affineDimension s.1 ∧
      (¬ stagedKernelPolynomials (d i) E W ⊆ s.1 → affineDimension t.1 < affineDimension s.1) := by
  classical
  dsimp only
  have hc := kernelChildList_spec G (d i) A h (pathDegreeBudget n d A h e i) s.1
    (physicalKernel (E := E) G d z i s B) hs.1
  have hzc : z ∈ evaluationCell G.points s.1 z (cumulativeBlockPrimes B i) := by
    exact Finset.mem_filter.mpr ⟨hz,hs.2.2.2.1,by simp⟩
  have hzF : ∀ p ∈ stagedKernelPolynomials (d i) E (physicalKernel G d z i s B),
      eval (fun l => (z l : ℂ)) p = 0 := by
    rintro p ⟨v,hv,rfl,_⟩
    exact hv.2 z hzc
  have hsel := firstCoveringChild_spec z s _ (hc.2.2 z hz hs.2.2.2.1 hzF)
  have hg := hc.2.1 _ hsel.1
  obtain ⟨⟨hp,hle,hdim,hdeg,hOn,hBound,_⟩,hF,hdim',hstrict⟩ := hg
  exact ⟨⟨⟨hp,hdim,hdeg⟩,hOn,hBound,hsel.2⟩,hsel.1,hle,hF,hdim',hstrict⟩

theorem physical_path_good {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (z : Fin n → ℤ) (hz : z ∈ G.points)
    (B : Fin r → Finset ℕ) (m i : ℕ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : PhysicalState G h (pathDegreeBudget n d A h e i) z s) :
    ∀ t ∈ adaptiveStates (physicalKernel (E := E) G d z) (physicalNext G d A h e z) m i s B,
      ∃ j, i ≤ j ∧ j ≤ i+m ∧ PhysicalState G h (pathDegreeBudget n d A h e j) z t := by
  induction m generalizing i s with
  | zero =>
    intro t ht
    have ht : t = s := by simpa only [adaptiveStates,List.mem_singleton] using ht
    subst t
    exact ⟨i,le_rfl,by omega,hs⟩
  | succ m ih =>
    intro t ht
    rcases List.mem_cons.mp ht with hts | ht
    · subst t
      exact ⟨i,le_rfl,by omega,hs⟩
    · have hstep := (physical_step (E := E) G d A h e z hz i s hs B).1
      obtain ⟨j,hij,hj,htj⟩ := ih (i+1) _ hstep t ht
      exact ⟨j,by omega,by omega,htj⟩

open MvPolynomial
open scoped BigOperators

theorem physical_uniform_minor_height (n : ℕ) (d : ℕ → ℕ) (A h e m E : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ b : ℕ,
      ∀ (G : KernelGeometry n) (z : Fin n → ℤ), z ∈ G.points →
      ∀ (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n),
        PhysicalState G h e z s → ∀ (r : ℕ) (B : Fin r → Finset ℕ),
      ∀ t ∈ adaptiveStates (physicalKernel (E := E) G d z) (physicalNext G d A h e z) m 0 s B,
        eval z t.2.minor ≠ 0 ∧ |((eval z t.2.minor : ℤ) : ℝ)| ≤ C*G.height^b := by
  classical
  let D := (Finset.range (m+1)).sup (pathDegreeBudget n d A h e)
  obtain ⟨C,hC,b,hb⟩ := uniform_patch_minor_height n D
  refine ⟨C,hC,b,?_⟩
  intro G z hz s hs r B t ht
  obtain ⟨j,_,hj,hjt⟩ := physical_path_good (E := E) G d A h e z hz B m 0 s hs t ht
  have hD : pathDegreeBudget n d A h e j ≤ D :=
    Finset.le_sup (f := pathDegreeBudget n d A h e) (Finset.mem_range.mpr (by omega))
  exact ⟨hjt.2.2.2.2,hb t.2 G.height G.one_le_height (hjt.2.2.1.mono hD) z (G.bounded z hz)⟩

theorem physical_regular_blocks (n : ℕ) (d : ℕ → ℕ) (A h e m E : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ b : ℕ,
    ∀ (G : KernelGeometry n)
      (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n),
      (∀ z, PhysicalState G h e z.val (start z)) →
    ∀ (r : ℕ) (P : Fin r → Finset ℕ) (ell : Fin r → ℕ) (T : ℕ)
      (X ζ w η ξ : ℝ), 1 < X → C ≤ X → 0 ≤ w → G.height ≤ X^w → 0 < ζ → 0 < ξ →
      (∀ i p, p ∈ P i → p.Prime) →
      (∀ i p, p ∈ P i → X^ζ ≤ (p : ℝ)) →
      0 < T → (∀ i, ell i+T < (P i).card) →
      (∀ i, ((((E+n).choose n+1)^m : ℕ) : ℝ)/T +
        (⌊((w*b+1)*(m+1:ℕ))/ζ⌋₊ : ℝ)/(((P i).card : ℝ)-(ell i+T)) ≤ η) →
    ∃ B : Fin r → Finset ℕ,
      (∀ i, B i ⊆ P i ∧ ell i < (B i).card ∧ (B i).card ≤ ell i+T) ∧
      ((Finset.univ.filter fun z : G.points => ∀ i,
        ((∑ p ∈ B i,
          if (p : ℤ) ∣ ((adaptiveStates (physicalKernel (E := E) G d z.val)
            (physicalNext G d A h e z.val) m 0 (start z) B).map
            (fun t => eval z.val t.2.minor)).prod
          then (1 : ℝ) else 0) / (B i).card) ≤ ξ).card : ℝ) ≥
            (1-(r : ℝ)*η/ξ)*G.points.card := by
  classical
  obtain ⟨C,hC,b,hb⟩ := physical_uniform_minor_height n d A h e m E
  refine ⟨C,hC,b,?_⟩
  intro G start hs r P ell T X ζ w η ξ hX hCX hw hheight hζ hξ hp hsmall hT hsize hη
  let := totalSpace_finite (n := n) (K := ℂ) E
  have hmono : ∀ (z : G.points) j s (B : Fin r → Finset ℕ) i U U', U ⊆ U' →
      physicalKernel (E := E) G d z.val j s (Function.update B i U) ≤
      physicalKernel G d z.val j s (Function.update B i U') := by
    intro z j s B i U U' hUU'
    apply physicalKernel_mono
    intro k
    by_cases hk : k = i
    · subst k; simpa using hUU'
    · simp only [Function.update_of_ne hk]
      exact Finset.Subset.refl _
  have hminor : ∀ (z : G.points) B, (∀ i, B i ⊆ P i) →
      ∀ t ∈ adaptiveStates (physicalKernel (E := E) G d z.val)
          (physicalNext G d A h e z.val) m 0 (start z) B,
        eval z.val t.2.minor ≠ 0 ∧ |((eval z.val t.2.minor : ℤ) : ℝ)| ≤ X^(w*b+1) := by
    intro z B _ t ht
    have ht' := hb G z.val z.property (start z) (hs z) r B t ht
    refine ⟨ht'.1,ht'.2.trans ?_⟩
    calc
      C*G.height^b ≤ X*(X^w)^b := mul_le_mul hCX
        (pow_le_pow_left₀ (zero_le_one.trans G.one_le_height) hheight b)
        (pow_nonneg (zero_le_one.trans G.one_le_height) b) (zero_lt_one.trans hX).le
      _ = X^(w*b+1) := by
        rw [Real.rpow_add (zero_lt_one.trans hX), Real.rpow_one,
          Real.rpow_mul (zero_lt_one.trans hX).le,Real.rpow_natCast,mul_comm]
  have hη' : ∀ i, (((Module.finrank ℂ (totalSpace (σ := Fin n) (K := ℂ) E)+1)^m : ℕ) : ℝ)/T +
      (⌊((w*b+1)*(m+1:ℕ))/ζ⌋₊ : ℝ)/(((P i).card : ℝ)-(ell i+T)) ≤ η := by
    simpa only [totalSpace_finrank] using hη
  simpa only [Fintype.card_coe] using
    regular_adaptive_blocks P ell T m (fun z => physicalKernel (E := E) G d z.val)
      (fun z => physicalNext G d A h e z.val) start
      (fun z t => eval z.val t.2.minor) hmono X ζ (w*b+1) η ξ hX hζ hξ hp hsmall hminor
      hT hsize hη'

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_DeformedRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

open MvPolynomial
open scoped Matrix

theorem mv_eval_sub_dvd {σ R : Type*} [CommRing R]
    (q : R) (P : MvPolynomial σ R) (x y : σ → R)
    (hxy : ∀ i, q ∣ x i - y i) : q ∣ eval x P - eval y P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
    simpa only [map_add, add_sub_add_comm] using dvd_add hP hQ
  | mul_X P i hP =>
    have h := dvd_add (dvd_mul_of_dvd_left hP (x i))
      (dvd_mul_of_dvd_right (hxy i) (eval y P))
    simpa only [map_mul, eval_X] using (show q ∣ eval x P * x i - eval y P * y i by
      convert h using 1; ring)

theorem mv_eval_sub_linear_dvd {σ R : Type*} [Fintype σ] [CommRing R]
    (q : R) (s : ℕ) (P : MvPolynomial σ R) (x y : σ → R)
    (hx : ∀ i, q ∣ x i) (hy : ∀ i, q ∣ y i)
    (hxy : ∀ i, q ^ s ∣ x i - y i) :
    q ^ (s + 1) ∣ eval x P - eval y P -
      ∑ i, eval (fun _ => 0) (pderiv i P) * (x i - y i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
    convert dvd_add hP hQ using 1
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    ring
  | mul_X P i hP =>
    have h1 : q ^ (s + 1) ∣ (eval x P - eval y P) * x i := by
      simpa only [pow_succ] using mul_dvd_mul (mv_eval_sub_dvd (q ^ s) P x y hxy) (hx i)
    have h2 : q ^ (s + 1) ∣ (eval y P - eval (fun _ => 0) P) * (x i - y i) := by
      have h0 : q ∣ eval y P - eval (fun _ => 0) P :=
        mv_eval_sub_dvd q P y (fun _ => 0) (by simpa using hy)
      simpa only [pow_succ, mul_comm q] using mul_dvd_mul h0 (hxy i)
    have hs : (∑ j, eval (fun _ => 0) (pderiv j (P * X i)) * (x j - y j)) =
        eval (fun _ => 0) P * (x i - y i) := by
      simp [pderiv_X, Pi.single_apply, apply_ite]
    rw [hs, map_mul, map_mul, eval_X, eval_X]
    convert dvd_add h1 h2 using 1; ring

theorem mv_eval_substitute {σ τ R : Type*} [CommRing R]
    (P : MvPolynomial σ R) (F : σ → MvPolynomial τ R) (x : τ → R) :
    eval x (eval₂ C F P) = eval (fun i => eval x (F i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP => simp [eval₂_mul, hP]

 theorem eval_implicitApprox_succ {ι κ R : Type*} [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R) (n : ℕ) (x : ι → R) (j : κ) :
    eval x (implicitApprox Φ (n + 1) j) =
      eval (Sum.elim x (fun a => eval x (implicitApprox Φ n a))) (Φ j) := by
  rw [implicitApprox, mv_eval_substitute]
  congr 2
  funext a
  cases a <;> simp

 theorem implicitApprox_zero {ι κ R : Type*} [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0) (n : ℕ) (j : κ) :
    eval (fun _ => 0) (implicitApprox Φ n j) = 0 := by
  induction n generalizing j with
  | zero => simp [implicitApprox]
  | succ n ih =>
    rw [eval_implicitApprox_succ]
    have hn : (Sum.elim (fun _ : ι => (0 : R))
        (fun a => eval (fun _ => 0) (implicitApprox Φ n a))) = (fun _ => 0) := by
      funext a
      cases a with
      | inl a => rfl
      | inr a => exact ih a
    rw [hn]
    exact hzero j

theorem implicit_map_contraction {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hlinear : ∀ j a, eval (fun _ => 0) (pderiv (Sum.inr a) (Φ j)) = 0)
    (q : R) (s : ℕ) (x : ι → R) (y z : κ → R)
    (hx : ∀ i, q ∣ x i) (hy : ∀ j, q ∣ y j) (hz : ∀ j, q ∣ z j)
    (hyz : ∀ j, q ^ s ∣ y j - z j) (j : κ) :
    q ^ (s + 1) ∣ eval (Sum.elim x y) (Φ j) - eval (Sum.elim x z) (Φ j) := by
  have hv : ∀ i, q ∣ (Sum.elim x y) i := by intro i; cases i <;> simp_all
  have hw : ∀ i, q ∣ (Sum.elim x z) i := by intro i; cases i <;> simp_all
  have hvw : ∀ i, q ^ s ∣ (Sum.elim x y) i - (Sum.elim x z) i := by
    intro i
    cases i <;> simp_all
  have h := mv_eval_sub_linear_dvd q s (Φ j) (Sum.elim x y) (Sum.elim x z) hv hw hvw
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sub_self,
    mul_zero, hlinear, zero_mul, Finset.sum_const_zero, add_zero, sub_zero] using h

theorem implicitApprox_error_dvd {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0)
    (hlinear : ∀ j a, eval (fun _ => 0) (pderiv (Sum.inr a) (Φ j)) = 0)
    (q : R) (x : ι → R) (y : κ → R)
    (hx : ∀ i, q ∣ x i) (hy : ∀ j, q ∣ y j)
    (hfix : ∀ j, eval (Sum.elim x y) (Φ j) = y j) (n : ℕ) (j : κ) :
    q ^ (n + 1) ∣ y j - eval x (implicitApprox Φ n j) := by
  induction n generalizing j with
  | zero => simpa only [implicitApprox, map_zero, sub_zero, zero_add, pow_one] using hy j
  | succ n ih =>
    have hn : ∀ a, q ∣ eval x (implicitApprox Φ n a) := by
      intro a
      have h := mv_eval_sub_dvd q (implicitApprox Φ n a) x (fun _ => 0)
        (by simpa only [sub_zero] using hx)
      simpa only [implicitApprox_zero Φ hzero, sub_zero] using h
    have h := implicit_map_contraction Φ hlinear q (n + 1) x y
      (fun a => eval x (implicitApprox Φ n a)) hx hy hn
      ih j
    rwa [hfix, ← eval_implicitApprox_succ] at h

theorem normalizedImplicitMap_zero {ι κ R : Type*} [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (G j) = 0) (j : κ) :
    eval (fun _ => 0) (normalizedImplicitMap G j) = 0 := by
  simp only [normalizedImplicitMap, map_sub, map_sum, map_mul, eval_X, eval_C,
    hzero, mul_zero, Finset.sum_const_zero, sub_zero]

theorem normalizedImplicitMap_linear {ι κ R : Type*} [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (hunit : IsUnit (implicitJacobian G).det) (j a : κ) :
    eval (fun _ => 0) (pderiv (Sum.inr a) (normalizedImplicitMap G j)) = 0 := by
  classical
  have hmat := congrArg (fun M : Matrix κ κ R => M j a)
    (Matrix.nonsing_inv_mul (implicitJacobian G) hunit)
  simp only [Matrix.mul_apply, Matrix.one_apply] at hmat
  have hs : (∑ b, (implicitJacobian G)⁻¹ j b *
      eval (fun _ => 0) (pderiv (Sum.inr a) (G b))) = if j = a then 1 else 0 := hmat
  simp only [normalizedImplicitMap, map_sub, map_sum, pderiv_mul, pderiv_C,
    zero_mul, zero_add, pderiv_X, Pi.single_apply, map_mul, eval_C]
  rw [hs]
  by_cases h : j = a <;> simp [h]

theorem normalizedImplicitMap_fixed {ι κ R : Type*} [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (x : ι → R) (y : κ → R)
    (hroot : ∀ j, eval (Sum.elim x y) (G j) = 0) (j : κ) :
    eval (Sum.elim x y) (normalizedImplicitMap G j) = y j := by
  simp [normalizedImplicitMap, hroot]

theorem smooth_patch_polynomial_approx {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (G j) = 0)
    (hunit : IsUnit (implicitJacobian G).det) (q : R) (n : ℕ) :
    ∃ F : κ → MvPolynomial ι R,
      (∀ j, eval (fun _ => 0) (F j) = 0) ∧
      ∀ (x : ι → R) (y : κ → R), (∀ i, q ∣ x i) → (∀ j, q ∣ y j) →
        (∀ j, eval (Sum.elim x y) (G j) = 0) →
        ∀ j, q ^ (n + 1) ∣ y j - eval x (F j) := by
  refine ⟨implicitApprox (normalizedImplicitMap G) n, ?_, ?_⟩
  · exact implicitApprox_zero _ (normalizedImplicitMap_zero G hzero) n
  · intro x y hx hy hroot j
    exact implicitApprox_error_dvd _ (normalizedImplicitMap_zero G hzero)
      (normalizedImplicitMap_linear G hunit) q x y hx hy
      (normalizedImplicitMap_fixed G x y hroot) n j

theorem implicitApprox_eval_dvd {ι κ R : Type*} [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0)
    (q : R) (x : ι → R) (hx : ∀ i, q ∣ x i) (n : ℕ) (j : κ) :
    q ∣ eval x (implicitApprox Φ n j) := by
  have h := mv_eval_sub_dvd q (implicitApprox Φ n j) x (fun _ => 0)
    (by simpa only [sub_zero] using hx)
  simpa only [implicitApprox_zero Φ hzero, sub_zero] using h

theorem implicitApprox_step_dvd {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0)
    (hlinear : ∀ j a, eval (fun _ => 0) (pderiv (Sum.inr a) (Φ j)) = 0)
    (q : R) (x : ι → R) (hx : ∀ i, q ∣ x i) (n : ℕ) (j : κ) :
    q ^ (n + 1) ∣ eval x (implicitApprox Φ (n + 1) j) -
      eval x (implicitApprox Φ n j) := by
  induction n generalizing j with
  | zero =>
    simpa only [zero_add, pow_one, implicitApprox, map_zero, sub_zero] using
      implicitApprox_eval_dvd Φ hzero q x hx 1 j
  | succ n ih =>
    rw [eval_implicitApprox_succ, eval_implicitApprox_succ Φ n]
    exact implicit_map_contraction Φ hlinear q (n + 1) x
      (fun j => eval x (implicitApprox Φ (n + 1) j))
      (fun j => eval x (implicitApprox Φ n j)) hx
      (implicitApprox_eval_dvd Φ hzero q x hx (n + 1))
      (implicitApprox_eval_dvd Φ hzero q x hx n) ih j

theorem implicitApprox_later_dvd {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0)
    (hlinear : ∀ j a, eval (fun _ => 0) (pderiv (Sum.inr a) (Φ j)) = 0)
    (q : R) (x : ι → R) (hx : ∀ i, q ∣ x i) {n m : ℕ} (hnm : n ≤ m) (j : κ) :
    q ^ (n + 1) ∣ eval x (implicitApprox Φ m j) -
      eval x (implicitApprox Φ n j) := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have hs := (pow_dvd_pow q (Nat.add_le_add_right hnm 1)).trans
      (implicitApprox_step_dvd Φ hzero hlinear q x hx m j)
    simpa only [sub_add_sub_cancel] using dvd_add hs ih

theorem exists_implicit_powerSeries_fixed {ι κ K : Type*} [Fintype ι] [Fintype κ]
    [CommRing K] (Φ : κ → MvPolynomial (ι ⊕ κ) (PowerSeries K))
    (hzero : ∀ j, eval (fun _ => 0) (Φ j) = 0)
    (hlinear : ∀ j a, eval (fun _ => 0) (pderiv (Sum.inr a) (Φ j)) = 0)
    (x : ι → PowerSeries K) (hx : ∀ i, PowerSeries.X ∣ x i) :
    ∃ y : κ → PowerSeries K, (∀ j, PowerSeries.constantCoeff (y j) = 0) ∧
      ∀ j, eval (Sum.elim x y) (Φ j) = y j := by
  let v := fun n j => eval x (implicitApprox Φ n j)
  let y : κ → PowerSeries K := fun j =>
    PowerSeries.mk (fun n => PowerSeries.coeff n (v n j))
  have happ : ∀ n j, PowerSeries.X ^ (n + 1) ∣ y j - v n j := by
    intro n j
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro i hi
    have he := PowerSeries.X_pow_dvd_iff.mp
      (implicitApprox_later_dvd Φ hzero hlinear PowerSeries.X x hx
        (Nat.le_of_lt_succ hi) j) i (Nat.lt_succ_self i)
    change PowerSeries.coeff i (v n j - v i j) = 0 at he
    simp only [map_sub] at he
    simp only [map_sub, y, PowerSeries.coeff_mk]
    exact sub_eq_zero.mpr (sub_eq_zero.mp he).symm
  refine ⟨y, ?_, ?_⟩
  · intro j
    have h := happ 0 j
    simpa only [zero_add, pow_one, v, implicitApprox, map_zero, sub_zero,
      PowerSeries.X_dvd_iff] using h
  · intro j
    apply sub_eq_zero.mp
    apply PowerSeries.ext
    intro n
    have hdiff : ∀ a, PowerSeries.X ^ (n + 1) ∣
        (Sum.elim x y) a - (Sum.elim x (v n)) a := by
      intro a
      cases a with
      | inl i => simp
      | inr j => exact happ n j
    have h1 := mv_eval_sub_dvd (PowerSeries.X ^ (n + 1)) (Φ j)
      (Sum.elim x y) (Sum.elim x (v n)) hdiff
    have h2 := implicitApprox_step_dvd Φ hzero hlinear PowerSeries.X x hx n j
    have h3 := dvd_neg.mpr (happ n j)
    have hs := dvd_add (dvd_add h1 h2) h3
    have ht : PowerSeries.X ^ (n + 1) ∣ eval (Sum.elim x y) (Φ j) - y j := by
      convert hs using 1
      rw [eval_implicitApprox_succ]
      dsimp [v]
      ring
    have he := PowerSeries.X_pow_dvd_iff.mp ht n (Nat.lt_succ_self n)
    simpa only [map_zero] using he

theorem normalizedImplicitMap_root {ι κ R : Type*} [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (hunit : IsUnit (implicitJacobian G).det) (x : ι → R) (y : κ → R)
    (hfix : ∀ j, eval (Sum.elim x y) (normalizedImplicitMap G j) = y j) :
    ∀ j, eval (Sum.elim x y) (G j) = 0 := by
  let v : κ → R := fun j => eval (Sum.elim x y) (G j)
  have hv : (implicitJacobian G)⁻¹ *ᵥ v = 0 := by
    funext j
    have h := hfix j
    simp only [normalizedImplicitMap, map_sub, map_sum, map_mul, eval_X, eval_C] at h
    simpa only [Matrix.mulVec, dotProduct, v, Pi.zero_apply] using (sub_eq_self.mp h)
  have h := congrArg (Matrix.mulVec (implicitJacobian G)) hv
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
    Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact fun j => congrFun h j

theorem exists_implicit_powerSeries_root {ι κ K : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [CommRing K] (G : κ → MvPolynomial (ι ⊕ κ) (PowerSeries K))
    (hzero : ∀ j, eval (fun _ => 0) (G j) = 0)
    (hunit : IsUnit (implicitJacobian G).det)
    (x : ι → PowerSeries K) (hx : ∀ i, PowerSeries.X ∣ x i) :
    ∃ y : κ → PowerSeries K, (∀ j, PowerSeries.constantCoeff (y j) = 0) ∧
      ∀ j, eval (Sum.elim x y) (G j) = 0 := by
  obtain ⟨y, hy, hfix⟩ := exists_implicit_powerSeries_fixed (normalizedImplicitMap G)
    (normalizedImplicitMap_zero G hzero) (normalizedImplicitMap_linear G hunit) x hx
  exact ⟨y, hy, normalizedImplicitMap_root G hunit x y hfix⟩

theorem pderiv_shiftedParameterPolynomial {κ R : Type*} [CommRing R]
    (a : κ → R) (p : MvPolynomial κ R) (i : κ) :
    pderiv (Sum.inr i) (shiftedParameterPolynomial a p) =
      shiftedParameterPolynomial a (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp [shiftedParameterPolynomial]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, pderiv_mul, hp, map_add]
    simp only [shiftedParameterPolynomial, eval₂Hom_X', map_add, pderiv_X,
      pderiv_C, add_zero, Pi.single_apply, Sum.inr.injEq]
    split_ifs <;> simp

theorem exists_deformed_powerSeries_root {κ K : Type*} [Fintype κ] [DecidableEq κ]
    [Field K] (f : κ → MvPolynomial κ K) (a : κ → K)
    (ha : ∀ j, eval a (f j) = 0)
    (hJ : (Matrix.of (fun i j => eval a (pderiv j (f i)))).det ≠ 0) (D : ℕ) :
    ∃ y : κ → PowerSeries K,
      (∀ j, PowerSeries.constantCoeff (y j) = a j) ∧
      ∀ j, eval₂ PowerSeries.C y (f j) + PowerSeries.X * y j ^ (D + 1) = 0 := by
  let a' : κ → PowerSeries K := fun j => PowerSeries.C (a j)
  let f' : κ → MvPolynomial κ (PowerSeries K) := fun j => map PowerSeries.C (f j)
  let G : κ → MvPolynomial (Unit ⊕ κ) (PowerSeries K) := fun j =>
    shiftedParameterPolynomial a' (f' j) +
      X (Sum.inl ()) * (X (Sum.inr j) + C (a' j)) ^ (D + 1)
  have hzero : ∀ j, eval (fun _ => 0) (G j) = 0 := by
    intro j
    simp only [G, map_add, eval_shiftedParameterPolynomial, zero_add, map_mul,
      eval_X, zero_mul, add_zero, f', a']
    rw [← eval₂_eq_eval_map]
    simpa only [Function.comp_def, ha, map_zero] using
      (eval₂_comp PowerSeries.C a (f j)).symm
  have hjac : implicitJacobian G =
      (Matrix.of (fun i j => eval a (pderiv j (f i)))).map PowerSeries.C := by
    apply Matrix.ext
    intro i j
    simp only [implicitJacobian, Matrix.of_apply, Matrix.map_apply, G, map_add,
      pderiv_shiftedParameterPolynomial, pderiv_mul, pderiv_X, Pi.single_apply,
      Sum.inl_ne_inr, ite_false, zero_mul, zero_add, eval_X, map_mul, map_add,
      zero_mul, add_zero, eval_shiftedParameterPolynomial, zero_add, f', pderiv_map, a']
    rw [← eval₂_eq_eval_map]
    exact (eval₂_comp PowerSeries.C a (pderiv j (f i))).symm
  have hunit : IsUnit (implicitJacobian G).det := by
    rw [hjac, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.mpr hJ).map PowerSeries.C
  obtain ⟨v, hv, hroot⟩ := exists_implicit_powerSeries_root G hzero hunit
    (fun _ => PowerSeries.X) (fun _ => dvd_refl _)
  refine ⟨fun j => v j + a' j, ?_, ?_⟩
  · intro j
    simp [hv, a']
  · intro j
    have h := hroot j
    simp only [G, map_add, eval_shiftedParameterPolynomial, Sum.elim_inr, map_mul,
      eval_X, Sum.elim_inl, map_pow, eval_C, f', ← eval₂_eq_eval_map] at h
    exact h

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_ResidueBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section

open MvPolynomial MonomialOrder
open scoped MonomialOrder

theorem separate_powers_normal_form {n : ℕ} {K : Type*} [Field K]
    (D : ℕ) (q : Fin n → MvPolynomial (Fin n) K)
    (hq : ∀ i, (q i).totalDegree ≤ D) (p : MvPolynomial (Fin n) K) :
    ∃ (g : Fin n →₀ MvPolynomial (Fin n) K) (r : MvPolynomial (Fin n) K),
      p = Finsupp.linearCombination _ (fun i => X i ^ (D + 1) - q i) g + r ∧
      ∀ m ∈ r.support, ∀ i, m i ≤ D := by
  classical
  have hlt : ∀ i, degLex.degree (q i) ≺[degLex]
      degLex.degree (X i ^ (D + 1) : MvPolynomial (Fin n) K) := by
    intro i
    apply lt_of_not_ge
    intro h
    have ht := MvPolynomial.degLex_totalDegree_monotone h
    simp only [MvPolynomial.totalDegree_X_pow] at ht
    exact Nat.not_succ_le_self D (ht.trans (hq i))
  have hdeg : ∀ i, degLex.degree (X i ^ (D + 1) - q i) =
      Finsupp.single i (D + 1) := by
    intro i
    rw [degLex.degree_sub_of_lt (hlt i), X_pow_eq_monomial,
      degLex.degree_monomial, ite_eq_right one_ne_zero]
  have hun : ∀ i, IsUnit (degLex.leadingCoeff (X i ^ (D + 1) - q i)) := by
    intro i
    rw [degLex.leadingCoeff_sub_of_lt (hlt i), X_pow_eq_monomial,
      degLex.leadingCoeff_monomial]
    exact isUnit_one
  obtain ⟨g, r, he, _, hr⟩ := MonomialOrder.div hun p
  refine ⟨g, r, he, ?_⟩
  intro m hm i
  have hh := hr m hm i
  rw [hdeg i] at hh
  have : ¬ (D + 1 ≤ m i) := by
    intro h
    apply hh
    exact Finsupp.single_le_iff.mpr h
  omega

theorem card_separate_powers_roots {n : ℕ} {K ι : Type*} [Field K] [Fintype ι]
    (D : ℕ) (q : Fin n → MvPolynomial (Fin n) K)
    (hq : ∀ i, (q i).totalDegree ≤ D) (z : ι → Fin n → K)
    (hz : Function.Injective z)
    (hroot : ∀ a i, z a i ^ (D + 1) = eval (z a) (q i)) :
    Fintype.card ι ≤ (D + 1) ^ n := by
  classical
  let ex : (Fin n → Fin (D + 1)) → (Fin n →₀ ℕ) := fun m =>
    Finsupp.equivFunOnFinite.symm (fun i => (m i).val)
  let b : (Fin n → Fin (D + 1)) → (ι → K) := fun m a =>
    eval (z a) (monomial (ex m) 1)
  let E : MvPolynomial (Fin n) K →ₗ[K] (ι → K) :=
    { toFun := fun p a => eval (z a) p
      map_add' := by intro p r; ext a; simp
      map_smul' := by intro c p; ext a; simp [smul_eq_C_mul] }
  have hspan : Submodule.span K (Set.range b) = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨p, hp⟩ := exists_mv_interpolate z hz v
    obtain ⟨g, r, he, hr⟩ := separate_powers_normal_form D q hq p
    have her : E r = v := by
      funext a
      have h := congrArg (eval (z a)) he
      simp only [map_add, Finsupp.linearCombination_apply, Finsupp.sum,
        smul_eq_mul, map_sum, map_mul, map_sub, map_pow, eval_X, hroot,
        sub_self, mul_zero, Finset.sum_const_zero, zero_add, hp] at h
      exact h.symm
    rw [← her, r.as_sum, map_sum]
    apply Submodule.sum_mem
    intro m hm
    let m' : Fin n → Fin (D + 1) := fun i => ⟨m i, Nat.lt_succ_of_le (hr m hm i)⟩
    have hex : ex m' = m := by ext i; rfl
    have hb : E (monomial m (r.coeff m)) = r.coeff m • b m' := by
      funext a
      simp only [E, LinearMap.coe_mk, AddHom.coe_mk, b, hex, Pi.smul_apply,
        smul_eq_mul, eval_monomial, one_mul]
    rw [hb]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m', rfl⟩)
  have h := finrank_le_of_span_eq_top hspan
  simpa only [Module.finrank_pi, Fintype.card_fun, Fintype.card_fin] using h

end

section
open MvPolynomial

theorem card_nonsingular_polynomial_roots {n : ℕ} {K ι : Type*} [Field K]
    [Fintype ι] (D : ℕ) (f : Fin n → MvPolynomial (Fin n) K)
    (hf : ∀ i, (f i).totalDegree ≤ D) (a : ι → Fin n → K)
    (hinj : Function.Injective a) (ha : ∀ b i, eval (a b) (f i) = 0)
    (hJ : ∀ b, (Matrix.of (fun i j => eval (a b) (pderiv j (f i)))).det ≠ 0) :
    Fintype.card ι ≤ (D + 1) ^ n := by
  classical
  choose y hy hyr using fun b => exists_deformed_powerSeries_root f (a b) (ha b) (hJ b) D
  let L := FractionRing (PowerSeries K)
  let inc : PowerSeries K →+* L := algebraMap _ _
  let c : K →+* L := inc.comp PowerSeries.C
  let T : L := inc PowerSeries.X
  let z : ι → Fin n → L := fun b i => inc (y b i)
  have hinc : Function.Injective inc := IsFractionRing.injective _ _
  have ht : T ≠ 0 := by
    exact fun h => PowerSeries.X_ne_zero (hinc (h.trans inc.map_zero.symm))
  have hz : Function.Injective z := by
    intro b b' h
    apply hinj
    funext i
    have hyy := hinc (congrFun h i)
    have hcc := congrArg PowerSeries.constantCoeff hyy
    simpa only [hy] using hcc
  let q : Fin n → MvPolynomial (Fin n) L := fun i => (-T⁻¹) • map c (f i)
  have hq : ∀ i, (q i).totalDegree ≤ D := by
    intro i
    apply (totalDegree_smul_le _ _).trans
    have hmap : (map c (f i)).totalDegree ≤ (f i).totalDegree :=
      Finset.sup_mono (support_map_subset c (f i))
    exact hmap.trans (hf i)
  apply card_separate_powers_roots D q hq z hz
  intro b i
  have h := congrArg inc (hyr b i)
  simp only [map_add, map_mul, map_pow, map_zero, eval₂_comp_left] at h
  change eval₂ c (z b) (f i) + T * z b i ^ (D + 1) = 0 at h
  change z b i ^ (D + 1) = eval (z b) ((-T⁻¹) • map c (f i))
  rw [smul_eq_C_mul, map_mul, eval_C, ← eval₂_eq_eval_map]
  apply mul_left_cancel₀ ht
  rw [← mul_assoc, mul_neg, mul_inv_cancel₀ ht, neg_one_mul]
  exact eq_neg_of_add_eq_zero_right h

theorem totalDegree_linear_substitute_le {σ τ K : Type*} [CommSemiring K]
    (F : σ → MvPolynomial τ K) (hF : ∀ i, (F i).totalDegree ≤ 1)
    (p : MvPolynomial σ K) :
    (eval₂ C F p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, eval₂_sum]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [eval₂_monomial]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    (∑ i ∈ m.support, (F i ^ m i).totalDegree) ≤
        ∑ i ∈ m.support, m i := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m i) (hF i))
    _ ≤ p.totalDegree := le_totalDegree hm

theorem totalDegree_partialEval_le {ι κ K : Type*} [CommSemiring K]
    (x : ι → K) (p : MvPolynomial (ι ⊕ κ) K) :
    (partialEval x p).totalDegree ≤ p.totalDegree := by
  apply totalDegree_linear_substitute_le
  intro a
  cases a with
  | inl i => simp
  | inr j =>
    simpa [X] using
      totalDegree_monomial_le (Finsupp.single j 1) (1 : K)

theorem pderiv_partialEval {ι κ K : Type*} [CommSemiring K]
    (x : ι → K) (p : MvPolynomial (ι ⊕ κ) K) (j : κ) :
    pderiv j (partialEval x p) = partialEval x (pderiv (Sum.inr j) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp [partialEval]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p a hp =>
    simp only [map_mul, pderiv_mul, hp, map_add]
    cases a with
    | inl i => simp [partialEval]
    | inr i =>
      simp only [partialEval, eval₂Hom_X', Sum.elim_inr, pderiv_X,
        Pi.single_apply, Sum.inr.injEq]
      split_ifs <;> simp

end

open scoped BigOperators

theorem card_regular_residue_tuples {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (good : ∀ i, Finset (α i)) (A M h N b : ℕ)
    (hA : 1 ≤ A) (hM : 1 ≤ M)
    (hall : ∀ i, Fintype.card (α i) ≤ M^N)
    (hgood : ∀ i, (good i).card ≤ A*M^h) :
    let R := Finset.univ.filter fun x : ∀ i, α i =>
      (Finset.univ.filter fun i => x i ∉ good i).card ≤ b
    R.card ≤ 2^Fintype.card ι * A^Fintype.card ι *
      M^(h*Fintype.card ι+N*b) := by
  classical
  let U : Finset (Finset ι) := Finset.univ.powerset.filter fun u => u.card ≤ b
  let C : Finset ι → Finset (∀ i, α i) := fun u =>
    Fintype.piFinset fun i => if i ∈ u then Finset.univ else good i
  have hbase : 1 ≤ A*M^h := by simpa using Nat.mul_le_mul hA (one_le_pow₀ hM (n := h))
  have hC (u : Finset ι) (hu : u ∈ U) :
      (C u).card ≤ A^Fintype.card ι*M^(h*Fintype.card ι+N*b) := by
    have hub : u.card ≤ b := (Finset.mem_filter.mp hu).2
    calc
      (C u).card = ∏ i, (if i ∈ u then Fintype.card (α i) else (good i).card) := by
        simp only [C,Fintype.card_piFinset]
        apply Finset.prod_congr rfl
        intro i _
        split_ifs <;> simp
      _ ≤ ∏ i, (A*M^h) * (if i ∈ u then M^N else 1) := by
        apply Finset.prod_le_prod'
        intro i _
        by_cases hi : i ∈ u
        · simp only [hi,ite_true]
          exact (hall i).trans (by simpa using Nat.mul_le_mul_right (M^N) hbase)
        · simpa only [hi,ite_false,mul_one] using hgood i
      _ = (A*M^h)^Fintype.card ι * (M^N)^u.card := by
        rw [Finset.prod_mul_distrib]
        simp
      _ ≤ (A*M^h)^Fintype.card ι * (M^N)^b := by
        gcongr
        exact Nat.one_le_pow _ _ hM
      _ = A^Fintype.card ι*M^(h*Fintype.card ι+N*b) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
  have hsub : (Finset.univ.filter fun x : ∀ i, α i =>
      (Finset.univ.filter fun i => x i ∉ good i).card ≤ b) ⊆ U.biUnion C := by
    intro x hx
    let u := Finset.univ.filter fun i => x i ∉ good i
    refine Finset.mem_biUnion.mpr ⟨u, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
        (Finset.mem_filter.mp hx).2⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      by_cases hi : i ∈ u
      · simp only [hi,ite_true,Finset.mem_univ]
      · have hg : x i ∈ good i := by simpa [u] using hi
        simpa only [hi,ite_false] using hg
  calc
    _ ≤ (U.biUnion C).card := Finset.card_le_card hsub
    _ ≤ ∑ u ∈ U, (C u).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ U, A^Fintype.card ι*M^(h*Fintype.card ι+N*b) :=
      Finset.sum_le_sum hC
    _ = U.card * (A^Fintype.card ι*M^(h*Fintype.card ι+N*b)) := by simp
    _ ≤ 2^Fintype.card ι * (A^Fintype.card ι*M^(h*Fintype.card ι+N*b)) := by
      apply Nat.mul_le_mul_right
      exact (Finset.card_filter_le _ _).trans (by simp)
    _ = _ := by ring

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_StoppingTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

open scoped BigOperators

open MvPolynomial
open scoped BigOperators

theorem card_nonsingular_roots_indexed {κ β K : Type*} [Fintype κ] [DecidableEq κ] [Fintype β]
    [Field K] (D : ℕ) (f : κ → MvPolynomial κ K)
    (hf : ∀ i, (f i).totalDegree ≤ D) (a : β → κ → K)
    (hinj : Function.Injective a) (ha : ∀ b i, eval (a b) (f i) = 0)
    (hJ : ∀ b, (Matrix.of (fun i j => eval (a b) (pderiv j (f i)))).det ≠ 0) :
    Fintype.card β ≤ (D+1)^Fintype.card κ := by
  classical
  let e := Fintype.equivFin κ
  let f' : Fin (Fintype.card κ) → MvPolynomial (Fin (Fintype.card κ)) K :=
    fun i => rename e (f (e.symm i))
  let a' : β → Fin (Fintype.card κ) → K := fun b i => a b (e.symm i)
  have hev (b : β) (p : MvPolynomial κ K) : eval (a' b) (rename e p) = eval (a b) p := by
    rw [eval_rename]
    simp [a',Function.comp_def]
  apply card_nonsingular_polynomial_roots D f'
    (fun i => (totalDegree_rename_le e _).trans (hf (e.symm i))) a'
  · intro b c hab
    apply hinj
    funext j
    simpa [a'] using congrFun hab (e j)
  · intro b i
    exact (hev b _).trans (ha b (e.symm i))
  · intro b
    have heq : (Matrix.of (fun i j => eval (a' b) (pderiv j (f' i)))) =
        Matrix.reindex e e (Matrix.of (fun i j => eval (a b) (pderiv j (f i)))) := by
      ext i j
      change eval (a' b) (pderiv j (rename e (f (e.symm i)))) = _
      rw [← e.apply_symm_apply j, pderiv_rename e.injective, hev]
      simp [Matrix.reindex,Matrix.of_apply]
    rw [heq,Matrix.det_reindex_self]
    exact hJ b

theorem card_smooth_patch_indexed {ι κ β K : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [Fintype β] [Field K] [Fintype K]
    (D : ℕ) (G : κ → MvPolynomial (ι ⊕ κ) K)
    (hG : ∀ j, (G j).totalDegree ≤ D) (z : β → (ι ⊕ κ) → K)
    (hinj : Function.Injective z) (hz : ∀ b j, eval (z b) (G j) = 0)
    (hminor : ∀ b, (Matrix.of (fun i j => eval (z b) (pderiv (Sum.inr j) (G i)))).det ≠ 0) :
    Fintype.card β ≤ Fintype.card K ^ Fintype.card ι * (D+1)^Fintype.card κ := by
  classical
  let free : β → ι → K := fun b i => z b (Sum.inl i)
  have hfiber (x : ι → K) : Fintype.card {b // free b = x} ≤ (D+1)^Fintype.card κ := by
    let a : {b // free b = x} → κ → K := fun b j => z b.val (Sum.inr j)
    have heq (b : {b // free b = x}) : Sum.elim x (a b) = z b.val := by
      funext j
      cases j with
      | inl i => exact (congrFun b.property i).symm
      | inr j => rfl
    apply card_nonsingular_roots_indexed D (fun j => partialEval x (G j))
      (fun j => (totalDegree_partialEval_le x (G j)).trans (hG j)) a
    · intro b b' h
      apply Subtype.ext
      apply hinj
      rw [← heq b, ← heq b',h]
    · intro b j
      rw [eval_partialEval,heq]
      exact hz b.val j
    · intro b
      simpa only [pderiv_partialEval,eval_partialEval,heq] using hminor b.val
  calc
    Fintype.card β = ∑ x : ι → K, Fintype.card {b // free b = x} := by
      rw [← Fintype.card_sigma]
      exact (Fintype.card_congr (Equiv.sigmaFiberEquiv free)).symm
    _ ≤ ∑ _x : ι → K, (D+1)^Fintype.card κ := Finset.sum_le_sum (fun x _ => hfiber x)
    _ = Fintype.card K ^ Fintype.card ι * (D+1)^Fintype.card κ := by simp

theorem IntegerPatch.card_goodResidues {n : ℕ} (P : IntegerPatch n)
    (K : Type*) [Field K] [Fintype K] (D : ℕ)
    (hD : ∀ i, (P.equations i).totalDegree ≤ D) :
    (P.goodResidues K).card ≤ Fintype.card K ^ Nat.card P.free * (D+1)^Nat.card ↥(P.freeᶜ) := by
  classical
  let e := Equiv.Set.sumCompl P.free
  let G : ↥(P.freeᶜ) → MvPolynomial (P.free ⊕ ↥(P.freeᶜ)) K :=
    fun i => rename e.symm (MvPolynomial.map (Int.castRingHom K) (P.equations i))
  let z : P.goodResidues K → (P.free ⊕ ↥(P.freeᶜ)) → K :=
    fun b j => b.val (e j)
  have hev (b : P.goodResidues K) (p : MvPolynomial (Fin n) K) :
      eval (z b) (rename e.symm p) = eval b.val p := by
    rw [eval_rename]
    simp [z,Function.comp_def]
  have heq (i : ↥(P.freeᶜ)) : e.symm i.val = Sum.inr i := by
    apply e.injective
    simp [e]
  have hcard := card_smooth_patch_indexed D G (fun i =>
    (totalDegree_rename_le e.symm _).trans
      ((Finset.sup_mono (support_map_subset _ _)).trans (hD i))) z
  have hz : Function.Injective z := by
    intro b c h
    apply Subtype.ext
    funext j
    simpa [z] using congrFun h (e.symm j)
  have hroot : ∀ b i, eval (z b) (G i) = 0 := by
    intro b i
    exact (hev b _).trans ((Finset.mem_filter.mp b.property).2.1 i)
  have hminor : ∀ b, (Matrix.of (fun i j => eval (z b) (pderiv (Sum.inr j) (G i)))).det ≠ 0 := by
    intro b
    have heval : (Matrix.of (fun i j => eval (z b) (pderiv (Sum.inr j) (G i)))) =
        (Matrix.of (fun i j => eval b.val (pderiv j.val
          (MvPolynomial.map (Int.castRingHom K) (P.equations i))))) := by
      ext i j
      change eval (z b) (pderiv (Sum.inr j) (rename e.symm _)) = _
      rw [← heq j,pderiv_rename e.symm.injective,hev]
      rfl
    rw [heval]
    have hb := (Finset.mem_filter.mp b.property).2.2
    rw [map_integer_minor] at hb
    have hd := (eval b.val).map_det (fun i j : ↥(P.freeᶜ) =>
      pderiv j.val (MvPolynomial.map (Int.castRingHom K) (P.equations i)))
    exact fun hz => hb (hd.trans hz)
  simpa only [Fintype.card_coe,Nat.card_eq_fintype_card] using hcard hz hroot hminor

attribute [local instance] Classical.propDecidable

theorem residueTuple_eq_iff {n : ℕ} (Q : Finset ℕ) (z w : Fin n → ℤ) :
    residueTuple Q z = residueTuple Q w ↔ ∀ p ∈ Q, ∀ i, (p : ℤ) ∣ w i-z i := by
  constructor
  · intro h p hp i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simp only [Int.cast_sub]
    exact sub_eq_zero.mpr (congrFun (congrFun h ⟨p,hp⟩) i).symm
  · intro h
    funext p i
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (w i-z i) p.val).mpr (h p.val p.property i)
    rw [Int.cast_sub,sub_eq_zero] at hz
    exact hz.symm

theorem IntegerPatch.eval_equation_zero {n : ℕ} {P : IntegerPatch n}
    {I : Ideal (MvPolynomial (Fin n) ℂ)} (hP : P.On I) {z : Fin n → ℤ}
    (hz : PointOn I z) (j : ↥(P.freeᶜ)) : eval z (P.equations j) = 0 := by
  have h := hz _ (hP.2.1 j)
  rw [eval_int_map] at h
  exact_mod_cast h

theorem IntegerPatch.residue_mem_iff {n p : ℕ} (P : IntegerPatch n) [Fact p.Prime]
    (z : Fin n → ℤ) (hz : ∀ j, eval z (P.equations j) = 0) :
    (fun i => (z i : ZMod p)) ∈ P.goodResidues (ZMod p) ↔ ¬ (p : ℤ) ∣ eval z P.minor := by
  classical
  simp only [IntegerPatch.goodResidues,Finset.mem_filter,Finset.mem_univ,true_and,eval_int_map,hz,Int.cast_zero,implies_true,true_and]
  exact not_congr (ZMod.intCast_zmod_eq_zero_iff_dvd _ p)

theorem card_filter_coe_finset {α : Type*} (Q : Finset α) (p : α → Prop) :
    (Finset.univ.filter fun a : Q => p a.val).card = (Q.filter p).card := by
  classical
  rw [Finset.card_filter,Finset.card_filter]
  exact Finset.sum_coe_sort Q (fun a => if p a then (1 : ℕ) else 0)

theorem IntegerPatch.card_bad_residue_tuple {n : ℕ} (P : IntegerPatch n)
    (Q : Finset ℕ) [∀ p : Q, Fact p.val.Prime] (z : Fin n → ℤ)
    (hz : ∀ j, eval z (P.equations j) = 0) :
    (Finset.univ.filter fun p : Q => residueTuple Q z p ∉ P.goodResidues (ZMod p.val)).card =
      (Q.filter fun p : ℕ => (p : ℤ) ∣ eval z P.minor).card := by
  classical
  have heq : (Finset.univ.filter fun p : Q => residueTuple Q z p ∉ P.goodResidues (ZMod p.val)) =
      Finset.univ.filter fun p : Q => (p.val : ℤ) ∣ eval z P.minor := by
    apply Finset.filter_congr
    intro p _
    change ¬ ((fun i => (z i : ZMod p.val)) ∈ P.goodResidues (ZMod p.val)) ↔ _
    rw [P.residue_mem_iff z hz,not_not]
  rw [heq]
  convert card_filter_coe_finset Q (fun p : ℕ => (p : ℤ) ∣ eval z P.minor) using 1 <;> congr 1 <;> ext p <;> simp

theorem IntegerPatch.card_goodResidues_zmod_le {n p : ℕ} (P : IntegerPatch n) [Fact p.Prime]
    (D h M : ℕ) (hM : 1 ≤ M) (hfree : Nat.card P.free ≤ h)
    (hD : ∀ j, (P.equations j).totalDegree ≤ D) (hupper : p ≤ M) :
    (P.goodResidues (ZMod p)).card ≤ (D+1)^n * M^h := by
  classical
  refine (P.card_goodResidues (ZMod p) D hD).trans ?_
  rw [ZMod.card]
  have hc : Nat.card ↥(P.freeᶜ) ≤ n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using
      Fintype.card_subtype_le (fun i : Fin n => i ∈ P.freeᶜ)
  calc
    p ^ Nat.card P.free * (D+1)^Nat.card ↥(P.freeᶜ) ≤ M^h*(D+1)^n := by
      apply Nat.mul_le_mul
      · exact (Nat.pow_le_pow_left hupper _).trans (Nat.pow_le_pow_right hM hfree)
      · exact Nat.pow_le_pow_right (by omega) hc
    _ = _ := by ring

theorem IntegerPatch.card_residue_image {n : ℕ} (P : IntegerPatch n)
    (D h M b : ℕ) (hM : 1 ≤ M) (hfree : Nat.card P.free ≤ h)
    (hD : ∀ j, (P.equations j).totalDegree ≤ D)
    (Q : Finset ℕ) (hprime : ∀ p ∈ Q, p.Prime) (hupper : ∀ p ∈ Q, p ≤ M)
    (S : Finset (Fin n → ℤ)) (hroot : ∀ z ∈ S, ∀ j, eval z (P.equations j) = 0)
    (hbad : ∀ z ∈ S, (Q.filter fun p : ℕ => (p : ℤ) ∣ eval z P.minor).card ≤ b) :
    (S.image (residueTuple Q)).card ≤
      2^Q.card * ((D+1)^n)^Q.card * M^(h*Q.card+n*b) := by
  classical
  let (p : Q) : Fact p.val.Prime := ⟨hprime p.val p.property⟩
  let good (p : Q) : Finset (Fin n → ZMod p.val) := P.goodResidues (ZMod p.val)
  have hall (p : Q) : Fintype.card (Fin n → ZMod p.val) ≤ M^n := by
    simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card]
    exact Nat.pow_le_pow_left (hupper p.val p.property) n
  have hgood (p : Q) : (good p).card ≤ (D+1)^n * M^h :=
    P.card_goodResidues_zmod_le D h M hM hfree hD (hupper p.val p.property)
  let R : Finset (∀ p : Q, Fin n → ZMod p.val) := Finset.univ.filter fun x =>
    (Finset.univ.filter fun p => x p ∉ good p).card ≤ b
  have hsub : S.image (residueTuple Q) ⊆ R := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact (P.card_bad_residue_tuple Q z (hroot z hz)).le.trans (hbad z hz)
  exact (Finset.card_le_card hsub).trans (by
    simpa only [Fintype.card_coe] using
      card_regular_residue_tuples good ((D+1)^n) M h n b (one_le_pow₀ (by omega)) hM hall hgood)

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_AdaptiveFibres
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

theorem card_image_le_mul_fibers {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] (S : Finset α) (f : α → β) (g : α → γ) (L : ℕ)
    (hL : ∀ b ∈ S.image f, ((S.filter fun a => f a = b).image g).card ≤ L) :
    (S.image g).card ≤ (S.image f).card * L := by
  classical
  have hsub : S.image g ⊆ (S.image f).biUnion fun b => (S.filter fun a => f a = b).image g := by
    intro c hc
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_biUnion.mpr ⟨f a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,
      Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,rfl⟩,rfl⟩⟩
  calc
    _ ≤ ((S.image f).biUnion fun b => (S.filter fun a => f a = b).image g).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ b ∈ S.image f, ((S.filter fun a => f a = b).image g).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ S.image f, L := Finset.sum_le_sum hL
    _ = _ := by simp

theorem adaptiveStateAt_tail {K V σ α : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : ℕ → σ → α → Submodule K V)
    (next : ℕ → σ → Submodule K V → σ) (m i : ℕ) (s : σ) (a : α) :
    adaptiveStateAt W next m (i+1) (next i s (W i s a)) a =
      adaptiveStateAt W next (m+1) i s a := by
  induction m with
  | zero => simp [adaptiveStateAt]
  | succ m ih =>
    simp only [adaptiveStateAt,ih]
    rw [show i+1+m = i+(m+1) by omega]

theorem adaptiveStateAt_mem_states {K V σ α : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : ℕ → σ → α → Submodule K V)
    (next : ℕ → σ → Submodule K V → σ) (m j i : ℕ) (s : σ) (a : α)
    (hj : j ≤ m) : adaptiveStateAt W next j i s a ∈ adaptiveStates W next m i s a := by
  induction m generalizing j i s with
  | zero =>
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simp [adaptiveStateAt,adaptiveStates]
  | succ m ih =>
    cases j with
    | zero => simp [adaptiveStateAt,adaptiveStates]
    | succ j =>
      rw [← adaptiveStateAt_tail]
      exact List.mem_cons_of_mem _ (ih j (i+1) _ (by omega))

theorem physicalStateAt_succ {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (i : ℕ) (z : G.points) :
    physicalStateAt (E := E) G d A h e start B (i+1) z =
      physicalNext G d A h e z.val i (physicalStateAt (E := E) G d A h e start B i z)
        (physicalKernel (E := E) G d z.val i (physicalStateAt (E := E) G d A h e start B i z) B) := by
  simp only [physicalStateAt,adaptiveStateAt,Nat.zero_add]

theorem physicalStateAt_good {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ) (i : ℕ) (z : G.points) :
    PhysicalState G h (pathDegreeBudget n d A h e i) z.val
      (physicalStateAt (E := E) G d A h e start B i z) := by
  induction i with
  | zero => exact hs z
  | succ i ih =>
    rw [physicalStateAt_succ]
    exact (physical_step (E := E) G d A h e z.val z.property i _ ih B).1

theorem pastBlockPrimes_succ {r : ℕ} (B : Fin r → Finset ℕ) (i : ℕ) :
    pastBlockPrimes B (i+1) = cumulativeBlockPrimes B i := by
  simp only [pastBlockPrimes,cumulativeBlockPrimes,Nat.lt_succ_iff]

theorem cumulativeBlockPrimes_eq_union {r : ℕ} (B : Fin r → Finset ℕ) (i : Fin r) :
    cumulativeBlockPrimes B i.val = pastBlockPrimes B i.val ∪ B i := by
  classical
  ext p
  simp only [cumulativeBlockPrimes,pastBlockPrimes,Finset.mem_biUnion,Finset.mem_filter,
    Finset.mem_univ,true_and,Finset.mem_union]
  constructor
  · rintro ⟨j,hj,hp⟩
    rcases lt_or_eq_of_le hj with hj | hj
    · exact Or.inl ⟨j,hj,hp⟩
    · have he : j = i := Fin.ext hj
      subst j
      exact Or.inr hp
  · rintro (⟨j,hj,hp⟩ | hp)
    · exact ⟨j,hj.le,hp⟩
    · exact ⟨i,le_rfl,hp⟩

theorem residueTuple_cumulative_eq {n r : ℕ} (B : Fin r → Finset ℕ) (i : Fin r)
    (z w : Fin n → ℤ) (hprev : residueTuple (pastBlockPrimes B i.val) z = residueTuple (pastBlockPrimes B i.val) w)
    (hnew : residueTuple (B i) z = residueTuple (B i) w) :
    residueTuple (cumulativeBlockPrimes B i.val) z = residueTuple (cumulativeBlockPrimes B i.val) w := by
  apply (residueTuple_eq_iff _ _ _).mpr
  intro p hp j
  rw [cumulativeBlockPrimes_eq_union] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (residueTuple_eq_iff _ _ _).mp hprev p hp j
  · exact (residueTuple_eq_iff _ _ _).mp hnew p hp j

theorem physical_fixed_residue_children {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (i : ℕ) (z : G.points) (S : Finset G.points)
    (hstate : ∀ w ∈ S, physicalStateAt (E := E) G d A h e start B i w =
      physicalStateAt (E := E) G d A h e start B i z)
    (hres : ∀ w ∈ S, residueTuple (cumulativeBlockPrimes B i) w.val =
      residueTuple (cumulativeBlockPrimes B i) z.val) :
    (S.image (physicalNode (E := E) G d A h e start B (i+1))).card ≤
      kernelCountBudget (d i) h (pathDegreeBudget n d A h e i) *
        patchCountBudget n A h (kernelDegreeBudget (d i) h (pathDegreeBudget n d A h e i)) := by
  classical
  let s := physicalStateAt (E := E) G d A h e start B i z
  let W := physicalKernel (E := E) G d z.val i s B
  let L := kernelChildList G (d i) A h (pathDegreeBudget n d A h e i) s.1 W
  have hz := physicalStateAt_good (E := E) G d A h e start hs B i z
  have hL := kernelChildList_spec G (d i) A h (pathDegreeBudget n d A h e i) s.1 W hz.1
  let f := fun t : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n =>
    (t, residueTuple (pastBlockPrimes B (i+1)) z.val)
  have hsub : S.image (physicalNode (E := E) G d A h e start B (i+1)) ⊆ L.toFinset.image f := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    have hsw := physicalStateAt_good (E := E) G d A h e start hs B i w
    have hstep := physical_step (E := E) G d A h e w.val w.property i _ hsw B
    have hkernel : physicalKernel (E := E) G d w.val i s B = W := by
      unfold W physicalKernel
      congr 1
      exact evaluationCell_eq_of_congruent _ _ _ _ _ ((residueTuple_eq_iff _ _ _).mp (hres w hw))
    have hm : physicalStateAt (E := E) G d A h e start B (i+1) w ∈ L := by
      rw [physicalStateAt_succ]
      have hm := hstep.2.1
      rw [hstate w hw] at hm ⊢
      change physicalNext G d A h e w.val i s (physicalKernel (E := E) G d w.val i s B) ∈ L
      change physicalNext G d A h e w.val i s (physicalKernel (E := E) G d w.val i s B) ∈
        kernelChildList G (d i) A h (pathDegreeBudget n d A h e i) s.1 (physicalKernel (E := E) G d w.val i s B) at hm
      rw [hkernel] at hm ⊢
      exact hm
    refine Finset.mem_image.mpr ⟨_,List.mem_toFinset.mpr hm,?_⟩
    apply Prod.ext
    · rfl
    · change residueTuple (pastBlockPrimes B (i+1)) z.val = residueTuple (pastBlockPrimes B (i+1)) w.val
      rw [pastBlockPrimes_succ]
      exact (hres w hw).symm
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans
    ((List.toFinset_card_le L).trans hL.1))

end

section
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

theorem physical_node_branch_bound {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (i : Fin r) (z : G.points) (S : Finset G.points)
    (hnode : ∀ w ∈ S, physicalNode (E := E) G d A h e start B i.val w =
      physicalNode (E := E) G d A h e start B i.val z)
    (q M b : ℕ) (hM : 1 ≤ M)
    (hdim : affineDimension (physicalStateAt (E := E) G d A h e start B i.val z).1 ≤ q)
    (hprime : ∀ p ∈ B i, p.Prime) (hupper : ∀ p ∈ B i, p ≤ M)
    (hbad : ∀ w ∈ S, ((B i).filter fun p : ℕ => (p : ℤ) ∣
      eval w.val (physicalStateAt (E := E) G d A h e start B i.val w).2.minor).card ≤ b) :
    (S.image (physicalNode (E := E) G d A h e start B (i.val+1))).card ≤
      (2^(B i).card * ((pathDegreeBudget n d A h e i.val+1)^n)^(B i).card *
        M^(q*(B i).card+n*b)) *
      (kernelCountBudget (d i.val) h (pathDegreeBudget n d A h e i.val) *
        patchCountBudget n A h (kernelDegreeBudget (d i.val) h (pathDegreeBudget n d A h e i.val))) := by
  classical
  let P := (physicalStateAt (E := E) G d A h e start B i.val z).2
  let s := physicalStateAt (E := E) G d A h e start B i.val z
  have hg := physicalStateAt_good (E := E) G d A h e start hs B i.val z
  have hstate (w : G.points) (hw : w ∈ S) :
      physicalStateAt (E := E) G d A h e start B i.val w = s :=
    congrArg Prod.fst (hnode w hw)
  have hprev (w : G.points) (hw : w ∈ S) :
      residueTuple (pastBlockPrimes B i.val) w.val = residueTuple (pastBlockPrimes B i.val) z.val :=
    congrArg Prod.snd (hnode w hw)
  let label : G.points → ∀ p : B i, Fin n → ZMod p.val := fun w => residueTuple (B i) w.val
  let K := kernelCountBudget (d i.val) h (pathDegreeBudget n d A h e i.val) *
        patchCountBudget n A h (kernelDegreeBudget (d i.val) h (pathDegreeBudget n d A h e i.val))
  have hfib (a) (ha : a ∈ S.image label) :
      ((S.filter fun w => label w = a).image (physicalNode (E := E) G d A h e start B (i.val+1))).card ≤ K := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    apply physical_fixed_residue_children G d A h e start hs B i.val v
    · intro w hw
      obtain ⟨hw,_⟩ := Finset.mem_filter.mp hw
      exact (hstate w hw).trans (hstate v hv).symm
    · intro w hw
      obtain ⟨hw,hr⟩ := Finset.mem_filter.mp hw
      exact residueTuple_cumulative_eq B i w.val v.val
        ((hprev w hw).trans (hprev v hv).symm) hr
  have hres : (S.image label).card ≤
      2^(B i).card * ((pathDegreeBudget n d A h e i.val+1)^n)^(B i).card * M^(q*(B i).card+n*b) := by
    let Z := S.image (fun w => w.val)
    have hfree : Nat.card P.free ≤ q := hg.2.1.1.trans_le hdim
    have hD : ∀ j, (P.equations j).totalDegree ≤ pathDegreeBudget n d A h e i.val := by
      obtain ⟨dd,hdd,hd,_⟩ := hg.2.2.1
      exact fun j => (hd j).trans hdd
    have hroot : ∀ w ∈ Z, ∀ j, eval w (P.equations j) = 0 := by
      rintro w hw j
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      have hgv := physicalStateAt_good (E := E) G d A h e start hs B i.val v
      rw [hstate v hv] at hgv
      exact IntegerPatch.eval_equation_zero hgv.2.1 hgv.2.2.2.1 j
    have hb : ∀ w ∈ Z, ((B i).filter fun p : ℕ => (p : ℤ) ∣ eval w P.minor).card ≤ b := by
      rintro w hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      have hvb := hbad v hv
      rw [hstate v hv] at hvb
      exact hvb
    have hc := P.card_residue_image (pathDegreeBudget n d A h e i.val) q M b hM hfree hD
      (B i) hprime hupper Z hroot hb
    simpa only [Z,Finset.image_image,Function.comp_def,label] using hc
  exact (card_image_le_mul_fibers S label _ K hfib).trans (Nat.mul_le_mul_right K hres)

end

open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

theorem activePoints_succ_subset {α : Type*} (S : Finset α) (stop : α → ℕ) (i : ℕ) :
    activePoints S stop (i+1) ⊆ activePoints S stop i := by
  intro z hz
  obtain ⟨hz,hi⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hz,by omega⟩

theorem active_node_count {α : Type*} {β : ℕ → Type*} [∀ i, DecidableEq (β i)] (S : Finset α)
    (stop : α → ℕ) (node : (i : ℕ) → α → β i) (B : ℕ → ℕ) (r C : ℕ)
    (hzero : ((activePoints S stop 0).image (node 0)).card ≤ C)
    (hchild : ∀ i < r, ∀ a ∈ (activePoints S stop (i+1)).image (node i),
      (((activePoints S stop (i+1)).filter fun z => node i z = a).image (node (i+1))).card ≤ B i) :
    ∀ i ≤ r, ((activePoints S stop i).image (node i)).card ≤ C*∏ j ∈ Finset.range i, B j := by
  intro i hi
  induction i with
  | zero => simpa using hzero
  | succ i ih =>
    have hcount := card_image_le_mul_fibers (activePoints S stop (i+1)) (node i) (node (i+1)) (B i)
      (hchild i (by omega))
    have hsub := Finset.card_le_card (Finset.image_subset_image (f := node i) (activePoints_succ_subset S stop i))
    calc
      _ ≤ ((activePoints S stop (i+1)).image (node i)).card * B i := hcount
      _ ≤ ((activePoints S stop i).image (node i)).card * B i := Nat.mul_le_mul_right _ hsub
      _ ≤ (C * ∏ j ∈ Finset.range i, B j) * B i := Nat.mul_le_mul_right _ (ih (by omega))
      _ = _ := by rw [Finset.prod_range_succ,mul_assoc]

theorem active_stopping_count {α : Type*} {β : ℕ → Type*} [∀ i, DecidableEq (β i)] (S : Finset α)
    (stop : α → ℕ) (node : (i : ℕ) → α → β i) (B : ℕ → ℕ) (r L : ℕ)
    (hstop : ∀ z ∈ S, stop z ≤ r)
    (hnodes : ∀ i ≤ r, ((activePoints S stop i).image (node i)).card ≤ B i)
    (hterminal : ∀ i ≤ r, ∀ a ∈ (activePoints S stop i).image (node i),
      (S.filter fun z => stop z = i ∧ node i z = a).card ≤ L) :
    S.card ≤ (∑ i ∈ Finset.range (r+1), B i)*L := by
  classical
  have hs (i : ℕ) (hi : i ≤ r) : (S.filter fun z => stop z = i).card ≤ B i * L := by
    let T := S.filter fun z => stop z = i
    have hsub : T ⊆ activePoints S stop i := by
      intro z hz
      obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hz,he.ge⟩
    have hf (a) (ha : a ∈ T.image (node i)) :
        ((T.filter fun z => node i z = a).image id).card ≤ L := by
      have ha' : a ∈ (activePoints S stop i).image (node i) := Finset.image_subset_image hsub ha
      simpa only [Finset.image_id,Finset.filter_filter,T] using hterminal i hi a ha'
    have hh := card_image_le_mul_fibers T (node i) id L hf
    rw [Finset.image_id] at hh
    exact hh.trans (Nat.mul_le_mul_right _ ((Finset.card_le_card (Finset.image_subset_image hsub)).trans (hnodes i hi)))
  calc
    S.card = ∑ i ∈ Finset.range (r+1), (S.filter fun z => stop z = i).card :=
      Finset.card_eq_sum_card_fiberwise (fun z hz => Finset.mem_range.mpr (by have := hstop z hz; omega))
    _ ≤ ∑ i ∈ Finset.range (r+1), B i * L := Finset.sum_le_sum (fun i hi => hs i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem physical_initial_node_count {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (S : Finset G.points)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n))
    (hs : ∀ z ∈ S, start z ∈ L) :
    (S.image (physicalNode (E := E) G d A h e start B 0)).card ≤ L.length := by
  classical
  let f := fun t : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n =>
    (t,residueTuple (pastBlockPrimes B 0) (fun _ : Fin n => 0))
  have hsub : S.image (physicalNode (E := E) G d A h e start B 0) ⊆ L.toFinset.image f := by
    intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_image.mpr ⟨start z,List.mem_toFinset.mpr (hs z hz),?_⟩
    apply Prod.ext
    · rfl
    · apply (residueTuple_eq_iff _ _ _).mpr
      simp
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (List.toFinset_card_le L))

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_ResidueRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

theorem physical_forest_count {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (S : Finset G.points) (stop : G.points → ℕ) (M b q : Fin r → ℕ)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)) (T : ℕ)
    (hstart : ∀ z ∈ S, start z ∈ L) (hstop : ∀ z ∈ S, stop z ≤ r)
    (hM : ∀ i, 1 ≤ M i) (hprime : ∀ i, ∀ p ∈ B i, p.Prime)
    (hupper : ∀ i, ∀ p ∈ B i, p ≤ M i)
    (hdim : ∀ i : Fin r, ∀ z ∈ S, i.val < stop z →
      affineDimension (physicalStateAt (E := E) G d A h e start B i.val z).1 ≤ q i)
    (hbad : ∀ i : Fin r, ∀ z ∈ S, i.val < stop z →
      ((B i).filter fun p : ℕ => (p : ℤ) ∣ eval z.val
        (physicalStateAt (E := E) G d A h e start B i.val z).2.minor).card ≤ b i)
    (hterminal : ∀ i ≤ r, ∀ z ∈ S, stop z = i →
      (S.filter fun w => stop w = i ∧ physicalNode (E := E) G d A h e start B i w =
        physicalNode (E := E) G d A h e start B i z).card ≤ T) :
    S.card ≤ (∑ i ∈ Finset.range (r+1),
      L.length * ∏ j ∈ Finset.range i,
        if hj : j < r then physicalBranchAllowance n d A h e B M b q ⟨j,hj⟩ else 1) * T := by
  classical
  let node := physicalNode (E := E) G d A h e start B
  let C := fun j : ℕ => if hj : j < r then physicalBranchAllowance n d A h e B M b q ⟨j,hj⟩ else 1
  have hzero : ((activePoints S stop 0).image (node 0)).card ≤ L.length := by
    apply physical_initial_node_count G d A h e start B _ L
    intro z hz
    exact hstart z (Finset.mem_filter.mp hz).1
  have hchild : ∀ j < r, ∀ a ∈ (activePoints S stop (j+1)).image (node j),
      (((activePoints S stop (j+1)).filter fun z => node j z = a).image (node (j+1))).card ≤ C j := by
    intro j hj a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hz,hjstop⟩ := Finset.mem_filter.mp hz
    have hcount := physical_node_branch_bound G d A h e start hs B ⟨j,hj⟩ z
      ((activePoints S stop (j+1)).filter fun z' => node j z' = node j z)
      (fun w hw => (Finset.mem_filter.mp hw).2) (q ⟨j,hj⟩) (M ⟨j,hj⟩) (b ⟨j,hj⟩)
      (hM ⟨j,hj⟩) (hdim ⟨j,hj⟩ z hz (by change j < stop z; omega)) (hprime ⟨j,hj⟩) (hupper ⟨j,hj⟩)
      (fun w hw => hbad ⟨j,hj⟩ w (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
        (by change j < stop w; have := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2; omega))
    simpa only [C,dite_eq_left hj,physicalBranchAllowance] using hcount
  have hnodes := active_node_count S stop node C r L.length hzero hchild
  apply active_stopping_count S stop node (fun i => L.length*∏ j ∈ Finset.range i, C j) r T hstop hnodes
  intro i hi a ha
  by_cases he : ∃ z ∈ S, stop z = i ∧ node i z = a
  · obtain ⟨z,hz,hzi,rfl⟩ := he
    convert hterminal i hi z hz hzi using 1
  · have hempty : (S.filter fun z => stop z = i ∧ node i z = a) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact he ⟨z,(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2⟩
    have hh := Finset.card_eq_zero.mpr hempty
    apply (show _ = 0 by convert hh using 1).le.trans
    exact Nat.zero_le _

end

open MvPolynomial
open scoped BigOperators
theorem pow_sum_dvd_det_of_row_dvd {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (q : R) (w : ι → ℕ) (A : Matrix ι ι R)
    (hA : ∀ i j, q ^ w i ∣ A i j) : q ^ (∑ i, w i) ∣ A.det := by
  choose B hB using hA
  have hmatrix : A = Matrix.of (fun i j => q ^ w i * B i j) := by
    ext i j
    exact hB i j
  rw [hmatrix]
  change q ^ (∑ i, w i) ∣ (Matrix.of (fun i j => q ^ w i * (Matrix.of B) i j)).det
  rw [Matrix.det_mul_column, Finset.prod_pow_eq_pow_sum]
  exact dvd_mul_right _ _

theorem determinant_dvd_of_local_expansion
    {ι τ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [CommRing R]
    (q : R) (m : ℕ) (w : τ → ℕ)
    (v : τ → ι → R) (c : ι → τ → R)
    (hv : ∀ a j, q ^ w a ∣ v a j)
    (hm : ∀ r : ι → τ, Function.Injective r → m ≤ ∑ i, w (r i)) :
    q ^ m ∣ (Matrix.of (fun i j => ∑ a, c i a * v a j)).det := by
  classical
  let L := (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R)
  have hexpand : (Matrix.of (fun i j => ∑ a, c i a * v a j)).det =
      ∑ r : ι → τ, (∏ i, c i (r i)) * (Matrix.of (fun i => v (r i))).det := by
    change L (fun i j => ∑ a, c i a * v a j) =
      ∑ r : ι → τ, (∏ i, c i (r i)) * L (fun i => v (r i))
    have h := L.toMultilinearMap.map_sum (fun i a => c i a • v a)
    simp only [AlternatingMap.coe_multilinearMap] at h
    have hfun : (fun i => ∑ a, c i a • v a) =
        (fun i j => ∑ a, c i a * v a j) := by
      funext i j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun] at h
    simpa only [AlternatingMap.map_smul_univ, smul_eq_mul] using h
  rw [hexpand]
  apply Finset.dvd_sum
  intro r _
  by_cases hr : Function.Injective r
  · apply dvd_mul_of_dvd_right
    exact (pow_dvd_pow q (hm r hr)).trans
      (pow_sum_dvd_det_of_row_dvd q (fun i => w (r i)) _ (fun i j => hv (r i) j))
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hr
    have hz : (Matrix.of (fun i => v (r i))).det = 0 := by
      exact L.map_eq_zero_of_eq (fun i => v (r i)) (congrArg v hab) hne
    rw [hz, mul_zero]
    exact dvd_zero _

theorem determinant_dvd_polynomial_eval {σ ι R : Type*} [Fintype ι]
    [DecidableEq ι] [CommRing R] (q : R) (m : ℕ)
    (P : ι → MvPolynomial σ R) (x : ι → σ → R)
    (hx : ∀ j a, q ∣ x j a)
    (hm : ∀ r : ι → (σ →₀ ℕ), Function.Injective r →
      m ≤ ∑ i, (r i).sum (fun _ e => e)) :
    q ^ m ∣ (Matrix.of (fun i j => eval (x j) (P i))).det := by
  classical
  let s : Finset (σ →₀ ℕ) := Finset.univ.biUnion (fun i => (P i).support)
  let v : s → ι → R := fun a j => a.val.prod (fun l e => x j l ^ e)
  let c : ι → s → R := fun i a => (P i).coeff a.val
  have hv : ∀ a j, q ^ a.val.sum (fun _ e => e) ∣ v a j := by
    intro a j
    dsimp [v, Finsupp.sum, Finsupp.prod]
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun l _ => pow_dvd_pow_of_dvd (hx j l) _)
  have hweight : ∀ r : ι → s, Function.Injective r →
      m ≤ ∑ i, (r i).val.sum (fun _ e => e) := by
    intro r hr
    exact hm (fun i => (r i).val) (Subtype.val_injective.comp hr)
  have heq : (Matrix.of (fun i j => eval (x j) (P i))) =
      Matrix.of (fun i j => ∑ a : s, c i a * v a j) := by
    ext i j
    simp only [Matrix.of_apply, c, v, Finsupp.prod, eval_eq]
    rw [Finset.sum_coe_sort s (fun a => (P i).coeff a * ∏ l ∈ a.support, x j l ^ a l)]
    apply Finset.sum_subset
    · intro a ha
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩
    · intro a _ ha
      have hz : (P i).coeff a = 0 := by
        simpa only [MvPolynomial.mem_support_iff, not_not] using ha
      simp only [hz, zero_mul]
  rw [heq]
  exact determinant_dvd_of_local_expansion q m (fun a : s => a.val.sum (fun _ e => e))
    v c hv hweight

theorem smooth_patch_determinant_zero {ι κ α R : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α] [CommRing R]
    (G : κ → MvPolynomial (ι ⊕ κ) R)
    (hzero : ∀ j, eval (fun _ => 0) (G j) = 0)
    (hunit : IsUnit (implicitJacobian G).det)
    (q : R) (m : ℕ) (hqm : q ^ m = 0)
    (P : α → MvPolynomial (ι ⊕ κ) R) (x : α → ι → R) (y : α → κ → R)
    (hx : ∀ a i, q ∣ x a i) (hy : ∀ a j, q ∣ y a j)
    (hroot : ∀ a j, eval (Sum.elim (x a) (y a)) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e)) :
    (Matrix.of (fun a b => eval (Sum.elim (x b) (y b)) (P a))).det = 0 := by
  obtain ⟨F, _, hF⟩ := smooth_patch_polynomial_approx G hzero hunit q m
  have heval : ∀ a j, y a j = eval (x a) (F j) := by
    intro a j
    have h := hF (x a) (y a) (hx a) (hy a) (hroot a) j
    simpa only [pow_succ, hqm, zero_mul, zero_dvd_iff, sub_eq_zero] using h
  let Q : α → MvPolynomial ι R := fun a => eval₂ C (Sum.elim X F) (P a)
  have heq : (Matrix.of (fun a b => eval (Sum.elim (x b) (y b)) (P a))) =
      Matrix.of (fun a b => eval (x b) (Q a)) := by
    ext a b
    dsimp only [Q, Matrix.of_apply]
    rw [mv_eval_substitute]
    congr 2
    funext c
    cases c with
    | inl c => simp
    | inr c => exact heval b c
  rw [heq]
  have h := determinant_dvd_polynomial_eval q m Q x hx hm
  simpa only [hqm, zero_dvd_iff] using h

theorem mv_eval_map_at {σ R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (P : MvPolynomial σ R) (x : σ → R) :
    eval (fun i => φ (x i)) (map φ P) = φ (eval x P) := by
  rw [eval_map, eval₂_comp]
  rfl

theorem intCast_isUnit_prime_power {p m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) : IsUnit (a : ZMod (p ^ m)) := by
  have hn : ¬ p ∣ a.natAbs := by simpa only [← Int.natCast_dvd] using ha
  have hu := (ZMod.isUnit_natCast_iff_not_dvd_pow hp hm).mpr hn
  have hu' : IsUnit (((a.natAbs : ℕ) : ℤ) : ZMod (p ^ m)) := by
    simpa only [Int.cast_natCast] using hu
  rw [Int.natCast_natAbs] at hu'
  rcases le_total 0 a with hpos | hneg
  · rwa [abs_of_nonneg hpos] at hu'
  · rw [abs_of_nonpos hneg, Int.cast_neg] at hu'
    simpa only [neg_neg] using hu'.neg

theorem smooth_patch_determinant_dvd {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α]
    (G : κ → MvPolynomial (ι ⊕ κ) ℤ)
    (hzero : ∀ j, eval (fun _ => 0) (G j) = 0)
    {p : ℕ} (hp : p.Prime) (hgood : ¬ (p : ℤ) ∣ (implicitJacobian G).det)
    (m : ℕ) (P : α → MvPolynomial (ι ⊕ κ) ℤ)
    (x : α → ι → ℤ) (y : α → κ → ℤ)
    (hx : ∀ a i, (p : ℤ) ∣ x a i) (hy : ∀ a j, (p : ℤ) ∣ y a j)
    (hroot : ∀ a j, eval (Sum.elim (x a) (y a)) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e)) :
    (p : ℤ) ^ m ∣
      (Matrix.of (fun a b => eval (Sum.elim (x b) (y b)) (P a))).det := by
  classical
  by_cases hm0 : m = 0
  · simp [hm0]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  let R := ZMod (p ^ m)
  let φ : ℤ →+* R := Int.castRingHom R
  let G' : κ → MvPolynomial (ι ⊕ κ) R := fun j => map φ (G j)
  let P' : α → MvPolynomial (ι ⊕ κ) R := fun a => map φ (P a)
  let x' : α → ι → R := fun a i => φ (x a i)
  let y' : α → κ → R := fun a j => φ (y a j)
  have hzero' : ∀ j, eval (fun _ => 0) (G' j) = 0 := by
    intro j
    have h := mv_eval_map_at φ (G j) (fun _ => 0)
    simpa only [G', map_zero, hzero] using h
  have hjac : implicitJacobian G' = φ.mapMatrix (implicitJacobian G) := by
    ext j a
    change eval (fun _ => 0) (pderiv (Sum.inr a) (map φ (G j))) =
      φ (eval (fun _ => 0) (pderiv (Sum.inr a) (G j)))
    rw [pderiv_map]
    simpa only [map_zero] using mv_eval_map_at φ (pderiv (Sum.inr a) (G j)) (fun _ => 0)
  have hunit : IsUnit (implicitJacobian G').det := by
    rw [hjac, ← φ.map_det]
    exact intCast_isUnit_prime_power hp hmpos _ hgood
  have hqm : (φ (p : ℤ)) ^ m = 0 := by
    change (((p : ℕ) : ℤ) : ZMod (p ^ m)) ^ m = 0
    rw [Int.cast_natCast, ← Nat.cast_pow, ZMod.natCast_self]
  have hx' : ∀ a i, φ (p : ℤ) ∣ x' a i := fun a i => map_dvd φ (hx a i)
  have hy' : ∀ a j, φ (p : ℤ) ∣ y' a j := fun a j => map_dvd φ (hy a j)
  have heval (a : α) (T : MvPolynomial (ι ⊕ κ) ℤ) :
      eval (Sum.elim (x' a) (y' a)) (map φ T) =
        φ (eval (Sum.elim (x a) (y a)) T) := by
    have hf : (fun i => φ ((Sum.elim (x a) (y a)) i)) = Sum.elim (x' a) (y' a) := by
      funext i
      cases i <;> rfl
    rw [← hf]
    exact mv_eval_map_at φ T _
  have hroot' : ∀ a j, eval (Sum.elim (x' a) (y' a)) (G' j) = 0 := by
    intro a j
    rw [show G' j = map φ (G j) from rfl, heval, hroot, map_zero]
  have hdet := smooth_patch_determinant_zero G' hzero' hunit (φ (p : ℤ)) m hqm
    P' x' y' hx' hy' hroot' hm
  let A : Matrix α α ℤ := Matrix.of (fun a b => eval (Sum.elim (x b) (y b)) (P a))
  have hA : φ.mapMatrix A = Matrix.of (fun a b => eval (Sum.elim (x' b) (y' b)) (P' a)) := by
    ext a b
    exact (heval b (P a)).symm
  have hz : (A.det : ZMod (p ^ m)) = 0 := by
    change φ A.det = 0
    rw [φ.map_det, hA]
    exact hdet
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd A.det (p ^ m)).mp hz
  simpa only [Nat.cast_pow] using hd

theorem eval_shiftVariables {σ R : Type*} [CommRing R]
    (z x : σ → R) (P : MvPolynomial σ R) :
    eval x (shiftVariables z P) = eval (fun i => x i + z i) P := by
  rw [shiftVariables, mv_eval_substitute]
  simp only [map_add, eval_X, eval_C]

theorem pderiv_shiftVariables {σ R : Type*} [CommRing R]
    (z : σ → R) (P : MvPolynomial σ R) (i : σ) :
    pderiv i (shiftVariables z P) = shiftVariables z (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp [shiftVariables]
  | add P Q hP hQ => simpa only [shiftVariables, eval₂_add, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P j hP =>
    by_cases h : i = j
    · subst j
      simpa only [shiftVariables, eval₂_mul, eval₂_X, pderiv_mul, map_add, pderiv_X,
        Pi.single_eq_same, pderiv_C, add_zero, mul_one, eval₂_add, eval₂_one, eval₂_zero,
        mul_zero, add_zero] using congrArg (fun T => T * (X i + C (z i)) +
          shiftVariables z P) hP
    · have h' : j ≠ i := Ne.symm h
      simpa only [shiftVariables, eval₂_mul, eval₂_X, pderiv_mul, map_add, pderiv_X,
        Pi.single_eq_of_ne h', pderiv_C, add_zero, mul_zero, eval₂_add, eval₂_one,
        eval₂_zero, mul_zero, add_zero] using congrArg (fun T => T * (X j + C (z j))) hP

theorem smooth_residue_determinant_dvd {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α]
    (G : κ → MvPolynomial (ι ⊕ κ) ℤ) (z : (ι ⊕ κ) → ℤ)
    (hz : ∀ j, eval z (G j) = 0)
    {p : ℕ} (hp : p.Prime)
    (hgood : ¬ (p : ℤ) ∣ (Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j)))).det)
    (m : ℕ) (P : α → MvPolynomial (ι ⊕ κ) ℤ) (w : α → (ι ⊕ κ) → ℤ)
    (hw : ∀ a i, (p : ℤ) ∣ w a i - z i)
    (hroot : ∀ a j, eval (w a) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e)) :
    (p : ℤ) ^ m ∣ (Matrix.of (fun a b => eval (w b) (P a))).det := by
  let G' : κ → MvPolynomial (ι ⊕ κ) ℤ := fun j => shiftVariables z (G j)
  let P' : α → MvPolynomial (ι ⊕ κ) ℤ := fun a => shiftVariables z (P a)
  let x : α → ι → ℤ := fun a i => w a (Sum.inl i) - z (Sum.inl i)
  let y : α → κ → ℤ := fun a j => w a (Sum.inr j) - z (Sum.inr j)
  have hzero : ∀ j, eval (fun _ => 0) (G' j) = 0 := by
    intro j
    simpa only [G', eval_shiftVariables, zero_add] using hz j
  have hjac : implicitJacobian G' =
      Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j))) := by
    ext j a
    simp only [implicitJacobian, Matrix.of_apply, G', pderiv_shiftVariables,
      eval_shiftVariables, zero_add]
  have hgood' : ¬ (p : ℤ) ∣ (implicitJacobian G').det := by rwa [hjac]
  have hs (a : α) (T : MvPolynomial (ι ⊕ κ) ℤ) :
      eval (Sum.elim (x a) (y a)) (shiftVariables z T) = eval (w a) T := by
    rw [eval_shiftVariables]
    congr 2
    funext i
    cases i <;> simp [x, y]
  have hx : ∀ a i, (p : ℤ) ∣ x a i := fun a i => hw a (Sum.inl i)
  have hy : ∀ a j, (p : ℤ) ∣ y a j := fun a j => hw a (Sum.inr j)
  have hroot' : ∀ a j, eval (Sum.elim (x a) (y a)) (G' j) = 0 := by
    intro a j
    rw [show G' j = shiftVariables z (G j) from rfl, hs, hroot]
  have h := smooth_patch_determinant_dvd G' hzero hp hgood' m P' x y hx hy hroot' hm
  have heq : (Matrix.of (fun a b => eval (Sum.elim (x b) (y b)) (P' a))) =
      Matrix.of (fun a b => eval (w b) (P a)) := by
    ext a b
    exact hs b (P a)
  rwa [heq] at h

theorem sum_min_eq_sum_card_filter {α : Type*} (s : Finset α) (f : α → ℕ) (t : ℕ) :
    ∑ a ∈ s, min (f a) t = ∑ j ∈ Finset.range t, (s.filter (fun a => j < f a)).card := by
  classical
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> omega

theorem monomial_order_lower_bound {ι α : Type*} [Fintype ι] [Fintype α]
    (r : α → (ι →₀ ℕ)) (hr : Function.Injective r) (t : ℕ) :
    t * Fintype.card α ≤ (∑ a, monomialOrder (r a)) +
      ∑ j ∈ Finset.range t, (j + Fintype.card ι).choose (Fintype.card ι) := by
  classical
  have hcard (j : ℕ) : (Finset.univ.filter (fun a => monomialOrder (r a) ≤ j)).card ≤
      (j + Fintype.card ι).choose (Fintype.card ι) := by
    rw [← card_monomialsUpTo ι j]
    exact Finset.card_le_card_of_injOn r
      (fun a ha => mem_monomialsUpTo.mpr (Finset.mem_filter.mp ha).2)
      (fun _ _ _ _ h => hr h)
  have hsum : t * Fintype.card α ≤
      (∑ a, monomialOrder (r a)) +
        ∑ j ∈ Finset.range t, (Finset.univ.filter (fun a => monomialOrder (r a) ≤ j)).card := by
    have hmin := sum_min_eq_sum_card_filter Finset.univ (fun a => monomialOrder (r a)) t
    have hcompl (j : ℕ) :
        (Finset.univ.filter (fun a => j < monomialOrder (r a))).card +
        (Finset.univ.filter (fun a => monomialOrder (r a) ≤ j)).card = Fintype.card α := by
      simpa only [not_lt, Finset.card_univ] using
        Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun a => j < monomialOrder (r a))
    have heq : (∑ a, min (monomialOrder (r a)) t) +
        ∑ j ∈ Finset.range t, (Finset.univ.filter (fun a => monomialOrder (r a) ≤ j)).card =
        t * Fintype.card α := by
      rw [hmin, ← Finset.sum_add_distrib]
      simp_rw [hcompl]
      simp
    rw [← heq]
    exact Nat.add_le_add_right (Finset.sum_le_sum (fun a _ => min_le_left _ _)) _
  exact hsum.trans (Nat.add_le_add_left (Finset.sum_le_sum (fun j _ => hcard j)) _)

theorem sum_simplex_card (h t : ℕ) :
    (∑ j ∈ Finset.range t, (j + h).choose h) = (t + h).choose (h + 1) := by
  cases t with
  | zero => simp
  | succ t => simpa only [Nat.succ_eq_add_one, Nat.add_right_comm t 1 h]
      using Nat.sum_range_add_choose t h

theorem monomial_order_simplex_bound {ι α : Type*} [Fintype ι] [Fintype α]
    (r : α → (ι →₀ ℕ)) (hr : Function.Injective r) (t : ℕ)
    (hcard : (t + Fintype.card ι).choose (Fintype.card ι) ≤ Fintype.card α) :
    Fintype.card ι * (t + Fintype.card ι).choose (Fintype.card ι + 1) ≤
      ∑ a, monomialOrder (r a) := by
  have h := monomial_order_lower_bound r hr t
  rw [sum_simplex_card] at h
  have heq := Nat.choose_succ_right_eq (t + Fintype.card ι) (Fintype.card ι)
  rw [Nat.add_sub_cancel_right] at heq
  have hmul := Nat.mul_le_mul_left t hcard
  nlinarith

open Matrix

theorem det_row_sum {ι τ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [CommRing R]
    (v : τ → ι → R) (c : ι → τ → R) :
    (Matrix.of (fun i j => ∑ a, c i a * v a j)).det =
      ∑ r : ι → τ, (∏ i, c i (r i)) * (Matrix.of (fun i => v (r i))).det := by
  classical
  let L := (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R)
  change L (fun i j => ∑ a, c i a * v a j) =
    ∑ r : ι → τ, (∏ i, c i (r i)) * L (fun i => v (r i))
  have h := L.toMultilinearMap.map_sum (fun i a => c i a • v a)
  simp only [AlternatingMap.coe_multilinearMap] at h
  have hfun : (fun i => ∑ a, c i a • v a) =
      (fun i j => ∑ a, c i a * v a j) := by
    funext i j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun] at h
  simpa only [AlternatingMap.map_smul_univ, smul_eq_mul] using h

theorem exists_relation_of_eval_dets_zero {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (v : ι → α → ℚ)
    (hdet : ∀ r : ι → α, (Matrix.of (fun i j => v i (r j))).det = 0) :
    ∃ c : ι → ℚ, c ≠ 0 ∧ ∀ a, ∑ i, c i * v i a = 0 := by
  classical
  let A : Matrix ι α ℚ := Matrix.of v
  have hgram : (A * A.transpose).det = 0 := by
    change (Matrix.of (fun i j => ∑ a, v i a * v j a)).det = 0
    rw [det_row_sum (fun a j => v j a) v]
    apply Finset.sum_eq_zero
    intro r _
    have hr : (Matrix.of (fun i j => v j (r i))).det = 0 := by
      change ((Matrix.of (fun i j => v i (r j))).transpose).det = 0
      rw [Matrix.det_transpose, hdet r]
    rw [hr, mul_zero]
  obtain ⟨c, hc, hzc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hgram
  refine ⟨c, hc, ?_⟩
  have hzero : A.transpose *ᵥ c = 0 := by
    rw [← Matrix.mulVec_mulVec] at hzc
    have h := congrArg (fun v => dotProduct c v) hzc
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,
      dotProduct_zero, dotProduct_self_eq_zero] at h
    exact h
  intro a
  have h := congrFun hzero a
  simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply,
    A, Matrix.of_apply, mul_comm] using h

open Matrix

theorem simultaneous_residue_determinant_dvd {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α]
    (G : κ → MvPolynomial (ι ⊕ κ) ℤ) (z : (ι ⊕ κ) → ℤ)
    (hz : ∀ j, eval z (G j) = 0) (Q : Finset ℕ)
    (hprime : ∀ p ∈ Q, p.Prime)
    (hgood : ∀ p ∈ Q, ¬ (p : ℤ) ∣
      (Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j)))).det)
    (m : ℕ) (P : α → MvPolynomial (ι ⊕ κ) ℤ) (w : α → (ι ⊕ κ) → ℤ)
    (hw : ∀ p ∈ Q, ∀ a i, (p : ℤ) ∣ w a i - z i)
    (hroot : ∀ a j, eval (w a) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e)) :
    (∏ p ∈ Q, (p : ℤ)) ^ m ∣ (Matrix.of (fun a b => eval (w b) (P a))).det := by
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_nat_coprime]
    simpa only [Int.natAbs_natCast] using (Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq
  · intro p hp
    exact smooth_residue_determinant_dvd G z hz (hprime p hp) (hgood p hp) m P w
      (hw p hp) hroot hm

theorem simultaneous_residue_determinant_zero {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α]
    (G : κ → MvPolynomial (ι ⊕ κ) ℤ) (z : (ι ⊕ κ) → ℤ)
    (hz : ∀ j, eval z (G j) = 0) (Q : Finset ℕ)
    (hprime : ∀ p ∈ Q, p.Prime)
    (hgood : ∀ p ∈ Q, ¬ (p : ℤ) ∣
      (Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j)))).det)
    (m : ℕ) (P : α → MvPolynomial (ι ⊕ κ) ℤ) (w : α → (ι ⊕ κ) → ℤ)
    (hw : ∀ p ∈ Q, ∀ a i, (p : ℤ) ∣ w a i - z i)
    (hroot : ∀ a j, eval (w a) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e))
    (B : α → ℝ) (hB : ∀ a b, |(eval (w b) (P a) : ℝ)| ≤ B a)
    (hlt : (Nat.factorial (Fintype.card α) : ℝ) * ∏ a, B a < (∏ p ∈ Q, (p : ℝ)) ^ m) :
    (Matrix.of (fun a b => eval (w b) (P a))).det = 0 := by
  let A : Matrix α α ℤ := Matrix.of (fun a b => eval (w b) (P a))
  have hdiv : (∏ p ∈ Q, (p : ℤ)) ^ m ∣ A.det :=
    simultaneous_residue_determinant_dvd G z hz Q hprime hgood m P w hw hroot hm
  apply Int.eq_zero_of_abs_lt_dvd hdiv
  have hB' := det_abs_le_row_product ((Int.castRingHom ℝ).mapMatrix A) B hB
  rw [← (Int.castRingHom ℝ).map_det] at hB'
  change |(A.det : ℝ)| ≤ _ at hB'
  have h := hB'.trans_lt hlt
  apply (Int.cast_lt (R := ℝ)).mp
  simpa only [Int.cast_abs, Int.cast_pow, Int.cast_prod, Int.cast_natCast] using h

theorem simultaneous_residue_relation {ι κ α β : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [Fintype β] [DecidableEq κ] [DecidableEq α]
    (G : κ → MvPolynomial (ι ⊕ κ) ℤ) (z : (ι ⊕ κ) → ℤ)
    (hz : ∀ j, eval z (G j) = 0) (Q : Finset ℕ)
    (hprime : ∀ p ∈ Q, p.Prime)
    (hgood : ∀ p ∈ Q, ¬ (p : ℤ) ∣
      (Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j)))).det)
    (m : ℕ) (P : α → MvPolynomial (ι ⊕ κ) ℤ) (w : β → (ι ⊕ κ) → ℤ)
    (hw : ∀ p ∈ Q, ∀ a i, (p : ℤ) ∣ w a i - z i)
    (hroot : ∀ a j, eval (w a) (G j) = 0)
    (hm : ∀ r : α → (ι →₀ ℕ), Function.Injective r →
      m ≤ ∑ a, (r a).sum (fun _ e => e))
    (B : α → ℝ) (hB : ∀ a b, |(eval (w b) (P a) : ℝ)| ≤ B a)
    (hlt : (Nat.factorial (Fintype.card α) : ℝ) * ∏ a, B a < (∏ p ∈ Q, (p : ℝ)) ^ m) :
    ∃ c : α → ℚ, c ≠ 0 ∧ ∀ b, ∑ a, c a * (eval (w b) (P a) : ℚ) = 0 := by
  apply exists_relation_of_eval_dets_zero
  intro r
  have hzero := simultaneous_residue_determinant_zero G z hz Q hprime hgood m P
    (fun a => w (r a)) (fun p hp a i => hw p hp (r a) i)
    (fun a j => hroot (r a) j) hm B (fun a b => hB a (r b)) hlt
  have h := congrArg (Int.castRingHom ℚ) hzero
  rw [(Int.castRingHom ℚ).map_det, map_zero] at h
  exact h

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_HilbertSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open scoped BigOperators

theorem extend_independent_finset {K V ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] (v : ι → V) (S A : Finset ι)
    (hAS : A ⊆ S) (hA : LinearIndepOn K v (A : Set ι)) (m : ℕ)
    (hAm : A.card ≤ m) (hm : m ≤ Module.finrank K (Submodule.span K (v '' (S : Set ι)))) :
    ∃ B : Finset ι, A ⊆ B ∧ B ⊆ S ∧ B.card = m ∧ LinearIndepOn K v (B : Set ι) := by
  classical
  have hsub : (A : Set ι) ⊆ (S : Set ι) := hAS
  let T := hA.extend hsub
  have hTs : T ⊆ (S : Set ι) := hA.extend_subset hsub
  have hfin : T.Finite := S.finite_toSet.subset hTs
  let B := hfin.toFinset
  have hli : LinearIndepOn K v (B : Set ι) := by
    simpa only [B, Set.Finite.coe_toFinset] using hA.linearIndepOn_extend hsub
  have hspan : Submodule.span K (v '' (B : Set ι)) =
      Submodule.span K (v '' (S : Set ι)) := by
    simpa only [B, Set.Finite.coe_toFinset] using hA.span_image_extend_eq_span_image hsub
  have hcard : Module.finrank K (Submodule.span K (v '' (B : Set ι))) = B.card := by
    have hh := finrank_span_eq_card (hli.linearIndependent_restrict)
    change Module.finrank K (Submodule.span K (Set.range (fun a : B => v a))) = _ at hh
    have hr : Set.range (fun a : B => v a) = v '' (B : Set ι) := by
      ext x
      constructor
      · rintro ⟨a,rfl⟩; exact ⟨a,a.property,rfl⟩
      · rintro ⟨a,ha,rfl⟩; exact ⟨⟨a,ha⟩,rfl⟩
    rw [hr] at hh
    simpa using hh
  have hAB : A ⊆ B := fun a ha => hfin.mem_toFinset.mpr (hA.subset_extend hsub ha)
  have hBS : B ⊆ S := fun a ha => hTs (hfin.mem_toFinset.mp ha)
  have hmB : m ≤ B.card := by rw [← hcard,hspan]; exact hm
  obtain ⟨C,hAC,hCB,hC⟩ := Finset.exists_subsuperset_card_eq hAB hAm hmB
  exact ⟨C,hAC,hCB.trans hBS,hC,hli.mono hCB⟩

theorem hilbert_simplex_shift (h : ℕ) (hh : 0 < h) (δ c : ℝ)
    (hδ : 0 < δ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℕ,
      ((t+h).choose h : ℝ) ≤ (δ*t+C)^h / ((h.factorial : ℝ)*δ^h) -
        c*(δ*t+C)^(h-1) := by
  let a : ℝ := (h.factorial : ℝ)*c*δ^(h-1) + 1/δ
  let C : ℝ := δ*((h : ℝ)+a)
  have hf : (0 : ℝ) < h.factorial := by exact_mod_cast h.factorial_pos
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hC : 1 ≤ C := by
    dsimp [C,a]
    rw [mul_add, mul_add, div_eq_mul_inv, one_mul, mul_inv_cancel₀ hδ.ne']
    have hN : 0 ≤ δ*(h:ℝ)+δ*((h.factorial:ℝ)*c*δ^(h-1)) := by positivity
    linarith
  refine ⟨C,hC,fun t => ?_⟩
  let x : ℝ := (t+h : ℕ)+a
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hlow : ((t+h : ℕ) : ℝ) ≤ x := by dsimp [x]; linarith
  have hT : δ*t+C = δ*x := by dsimp [C,x]; push_cast; ring
  have hpow : x^h = x^(h-1)*x := by rw [← pow_succ,Nat.sub_add_cancel hh]
  have hnum : ((t+h : ℕ) : ℝ)^h ≤ x^h - (h.factorial : ℝ)*c*δ^(h-1)*x^(h-1) := by
    have hq : ((t+h : ℕ) : ℝ)^(h-1) ≤ x^(h-1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hlow _
    have hb : ((t+h : ℕ) : ℝ) ≤ x - (h.factorial : ℝ)*c*δ^(h-1) := by
      dsimp [x,a]
      linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 1) hδ.le]
    calc
      _ = ((t+h : ℕ) : ℝ)^(h-1)*((t+h : ℕ) : ℝ) := by
        rw [← pow_succ,Nat.sub_add_cancel hh]
      _ ≤ x^(h-1)*(x-(h.factorial : ℝ)*c*δ^(h-1)) :=
        mul_le_mul hq hb (Nat.cast_nonneg _) (pow_nonneg hx _)
      _ = _ := by rw [hpow]; ring
  have hb := (Nat.choose_le_pow_div h (t+h) : ((t+h).choose h : ℝ) ≤
      ((t+h : ℕ) : ℝ)^h / (h.factorial : ℝ))
  apply hb.trans
  rw [hT,mul_pow,mul_pow]
  have he : δ^h*x^h / ((h.factorial:ℝ)*δ^h) - c*(δ^(h-1)*x^(h-1)) =
      (x^h-(h.factorial:ℝ)*c*δ^(h-1)*x^(h-1))/(h.factorial:ℝ) := by
    field_simp
  rw [he]
  exact div_le_div_of_nonneg_right hnum hf.le

theorem simplex_order_step (h t : ℕ) :
    h*((t+1+h).choose (h+1)) + (t+1)*((t+h).choose h) =
      h*((t+h).choose (h+1)) + (t+1)*((t+1+h).choose h) := by
  have h₁ := Nat.choose_succ_succ (t+h) h
  have h₂ := Nat.choose_mul_succ_eq (t+h) h
  rw [show t+h+1-h = t+1 by omega] at h₂
  rw [show t+1+h = t+h+1 by omega]
  nlinarith

theorem independent_weighted_simplex {K V ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] (v : ι → V) (S : ℕ → Finset ι)
    (hS : ∀ t, S t ⊆ S (t+1)) (w : ι → ℝ) (δ C : ℝ)
    (hweight : ∀ t a, a ∈ S t → w a ≤ δ*t+C)
    (h : ℕ) (hrank : ∀ t, (t+h).choose h ≤
      Module.finrank K (Submodule.span K (v '' (S t : Set ι)))) (t : ℕ) :
    ∃ A : Finset ι, A ⊆ S t ∧ A.card = (t+h).choose h ∧
      LinearIndepOn K v (A : Set ι) ∧
      ∑ a ∈ A, w a ≤ δ*(h*((t+h).choose (h+1)) : ℕ) + C*((t+h).choose h) := by
  classical
  induction t with
  | zero =>
    obtain ⟨A,_,hA,hcard,hli⟩ := extend_independent_finset v (S 0) ∅
      (Finset.empty_subset _) (by simp)
      ((0+h).choose h) (by simp) (hrank 0)
    refine ⟨A,hA,hcard,hli,?_⟩
    have hb := Finset.sum_le_sum (s := A) (fun a ha => hweight 0 a (hA ha))
    simpa only [Nat.cast_zero,mul_zero,zero_add,Finset.sum_const, nsmul_eq_mul,
      hcard,Nat.choose_self,Nat.cast_one,mul_one,one_mul,Nat.choose_eq_zero_of_lt (Nat.lt_succ_self h),
      Nat.mul_zero] using hb
  | succ t ih =>
    obtain ⟨A,hA,hcard,hli,hsum⟩ := ih
    have hcount : A.card ≤ (t+1+h).choose h := by
      rw [hcard]
      exact Nat.choose_le_choose h (by omega)
    obtain ⟨B,hAB,hB,hBcard,hlB⟩ := extend_independent_finset v (S (t+1)) A
      (hA.trans (hS t)) hli ((t+1+h).choose h) hcount (hrank (t+1))
    refine ⟨B,hB,hBcard,hlB,?_⟩
    have hnew : ∑ a ∈ B \ A, w a ≤ ((B \ A).card : ℝ)*(δ*(t+1)+C) := by
      calc
        _ ≤ ∑ _a ∈ B \ A, (δ*(t+1)+C) := by
          apply Finset.sum_le_sum
          intro a ha
          have haW := hweight (t+1) a (hB (Finset.mem_sdiff.mp ha).1)
          simpa only [Nat.cast_add,Nat.cast_one] using haW
        _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
    have hsplit : (∑ a ∈ B \ A, w a) + (∑ a ∈ A, w a) = ∑ a ∈ B, w a :=
      Finset.sum_sdiff hAB
    have hcarddiff : ((B \ A).card : ℝ) = (B.card : ℝ)-(A.card : ℝ) := by
      rw [Finset.card_sdiff_of_subset hAB,Nat.cast_sub (Finset.card_le_card hAB)]
    have hstep : (h*((t+1+h).choose (h+1)) : ℕ) +
        ((t+1)*((t+h).choose h) : ℕ) =
      (h*((t+h).choose (h+1)) : ℕ) + ((t+1)*((t+1+h).choose h) : ℕ) :=
      simplex_order_step h t
    have hstepR : (h*((t+1+h).choose (h+1)) : ℝ) +
        ((t:ℝ)+1)*((t+h).choose h) =
      (h*((t+h).choose (h+1)) : ℝ) + ((t:ℝ)+1)*((t+1+h).choose h) := by
      exact_mod_cast hstep
    rw [hcarddiff,hcard,hBcard] at hnew
    push_cast at hsum ⊢
    have he : (δ*(t+1)+C)*(((t+1+h).choose h : ℝ)-((t+h).choose h : ℝ)) +
        (δ*(h:ℝ)*((t+h).choose (h+1))) + C*((t+h).choose h) =
      δ*(h:ℝ)*((t+1+h).choose (h+1)) + C*((t+1+h).choose h) := by
      nlinarith [congrArg (fun x : ℝ => δ*x) hstepR]
    rw [← hsplit]
    calc
      _ ≤ (( (t+1+h).choose h : ℝ)-((t+h).choose h : ℝ))*(δ*(t+1)+C) +
          (δ*((h:ℝ)*((t+h).choose (h+1))) + C*((t+h).choose h)) := add_le_add hnew hsum
      _ = _ := by nlinarith [he]

open scoped BigOperators
open MvPolynomial

theorem mem_weightedMonomials {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (hω : ∀ i, 0 < ω i) (T : ℝ) (a : σ →₀ ℕ) :
    a ∈ weightedMonomials ω T ↔ monomialWeight ω a ≤ T := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr ?_,ha⟩
    intro i
    change a i ≤ ⌊T/ω i⌋₊
    apply Nat.le_floor
    apply (le_div_iff₀ (hω i)).mpr
    have hi := Finset.single_le_sum
      (fun j _ => mul_nonneg (hω j).le (Nat.cast_nonneg (a j))) (Finset.mem_univ i)
    simpa only [mul_comm (a i : ℝ)] using hi.trans ha

theorem weightedMonomials_mono {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (hω : ∀ i, 0 < ω i) {S T : ℝ} (h : S ≤ T) :
    weightedMonomials ω S ⊆ weightedMonomials ω T := by
  intro a ha
  exact (mem_weightedMonomials ω hω T a).mpr
    (((mem_weightedMonomials ω hω S a).mp ha).trans h)

theorem weighted_monomial_degree_bound {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (hω : ∀ i, 0 < ω i) (T : ℝ) (a : σ →₀ ℕ)
    (ha : monomialWeight ω a ≤ T) : a.sum (fun _ e => e) ≤ weightedDegreeBound ω T := by
  classical
  have hs := (Finset.mem_filter.mp ((mem_weightedMonomials ω hω T a).mpr ha)).1
  have hb : a ≤ weightedExponentBound ω T := Finset.mem_Iic.mp hs
  rw [Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.sum_le_sum (fun i _ => hb i)

theorem integer_monomial_abs_le {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (C X : ℝ) (hC : 1 ≤ C) (hX : 0 < X)
    (z : σ → ℤ) (hz : ∀ i, |(z i : ℝ)| ≤ C * X^(ω i)) (a : σ →₀ ℕ)
    (D : ℕ) (hD : a.sum (fun _ e => e) ≤ D) :
    |((eval z (monomial a (1:ℤ)) : ℤ) : ℝ)| ≤ C^D * X^(monomialWeight ω a) := by
  classical
  have hprod : |((eval z (monomial a (1:ℤ)) : ℤ) : ℝ)| = ∏ i, |(z i : ℝ)|^(a i) := by
    rw [eval_monomial,one_mul,Finsupp.prod_fintype _ _ (by simp)]
    simp only [Int.cast_prod,Int.cast_pow,Finset.abs_prod,abs_pow]
  have hexp : (∏ i, (X^(ω i))^(a i)) = X^(monomialWeight ω a) := by
    simp_rw [← Real.rpow_mul_natCast hX.le]
    rw [← Real.rpow_sum_of_pos hX]
    rfl
  calc
    _ = ∏ i, |(z i : ℝ)|^(a i) := hprod
    _ ≤ ∏ i, (C*X^(ω i))^(a i) := Finset.prod_le_prod
      (fun i _ => pow_nonneg (abs_nonneg _) _) (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hz i) _)
    _ = C^(a.sum (fun _ e => e)) * X^(monomialWeight ω a) := by
      simp_rw [mul_pow]
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hexp]
      rw [Finsupp.sum_fintype _ _ (by simp)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hD) (Real.rpow_nonneg hX.le _)

end

open scoped BigOperators
open MvPolynomial

theorem exists_simplex_margin (h : ℕ) (hh : 0 < h) (ν C : ℝ) (hν : 0 < ν) :
    ∃ t : ℕ, 0 < (t+h).choose h ∧
      (C+1)*((t+h).choose h : ℝ) ≤ ν*(h*((t+h).choose (h+1)) : ℕ) := by
  obtain ⟨t,ht⟩ := exists_nat_gt (((C+1)*((h:ℝ)+1))/(ν*h))
  have hp : 0 < ν*(h:ℝ) := mul_pos hν (by exact_mod_cast hh)
  have ht' := (div_lt_iff₀ hp).mp ht
  have hchoose : (h+1)*((t+h).choose (h+1)) = t*((t+h).choose h) := by
    have hc := Nat.add_one_mul_choose_eq (t+h) h
    rw [Nat.choose_succ_succ] at hc
    nlinarith
  have hr : ((h:ℝ)+1)*((t+h).choose (h+1) : ℝ) = (t:ℝ)*((t+h).choose h) := by
    exact_mod_cast hchoose
  have hL : 0 < (t+h).choose h := Nat.choose_pos (by omega)
  refine ⟨t,hL,?_⟩
  have hb := mul_le_mul_of_nonneg_right ht'.le (show (0:ℝ) ≤ (t+h).choose h by positivity)
  push_cast
  nlinarith

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_WeightedRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open scoped BigOperators
open MvPolynomial

theorem weighted_row_product_lt {α : Type*} [Fintype α]
    (w : α → ℝ) (C X δ ν c Q : ℝ) (D m : ℕ)
    (hX : 1 < X)
    (hlarge : (Fintype.card α).factorial * (C^D)^(Fintype.card α) < X)
    (hL : 0 < Fintype.card α)
    (hsum : ∑ a, w a ≤ δ*(m:ℝ)+c*(Fintype.card α))
    (hmargin : (c+1)*(Fintype.card α : ℝ) ≤ ν*(m:ℝ))
    (hQ : X^(δ+ν) ≤ Q) :
    (Nat.factorial (Fintype.card α) : ℝ) * ∏ a, (C^D * X^(w a)) < Q^m := by
  classical
  have hpos : 0 < X := lt_trans zero_lt_one hX
  have hprod : (∏ a, (C^D * X^(w a))) = (C^D)^(Fintype.card α)*X^(∑ a, w a) := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Real.rpow_sum_of_pos hpos]
  have hweight : (∑ a, w a)+1 ≤ (δ+ν)*(m:ℝ) := by
    have hcL : (1:ℝ) ≤ Fintype.card α := by exact_mod_cast hL
    nlinarith
  calc
    _ = ((Fintype.card α).factorial * (C^D)^(Fintype.card α))*X^(∑ a, w a) := by rw [hprod]; ring
    _ < X*X^(∑ a, w a) := mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hpos _)
    _ = X^((∑ a, w a)+1) := by rw [Real.rpow_add hpos,Real.rpow_one,mul_comm]
    _ ≤ X^((δ+ν)*(m:ℝ)) := Real.rpow_le_rpow_of_exponent_le hX.le hweight
    _ = (X^(δ+ν))^m := Real.rpow_mul_natCast hpos.le _ m
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hpos.le _) hQ m

theorem independent_monomial_relation_proper {σ α K : Type*}
    [Fintype α] [Field K] [CharZero K]
    (I : Ideal (MvPolynomial σ K)) (a : α → (σ →₀ ℕ))
    (hli : LinearIndependent K (fun i => Ideal.Quotient.mk I (monomial (a i) (1:K))))
    (c : α → ℚ) (hc : c ≠ 0) :
    MvPolynomial.map (algebraMap ℚ K) (∑ i, monomial (a i) (c i)) ∉ I := by
  intro hp
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have he (i : α) : monomial (a i) (algebraMap ℚ K (c i)) =
      (algebraMap ℚ K (c i)) • monomial (a i) (1:K) := by
    simp only [smul_monomial,smul_eq_mul,mul_one]
  simp only [map_sum,MvPolynomial.map_monomial,he] at hz
  change ∑ i, (Ideal.Quotient.mkₐ K I) ((algebraMap ℚ K (c i)) • monomial (a i) (1:K)) = 0 at hz
  simp only [map_smul] at hz
  have hcoeff := (Fintype.linearIndependent_iff.mp hli) (fun i => algebraMap ℚ K (c i)) hz
  apply hc
  funext i
  change c i = 0
  exact (algebraMap ℚ K).injective (by simpa only [map_zero] using hcoeff i)

theorem monomial_relation_degree {σ α : Type*} [Fintype α]
    (a : α → (σ →₀ ℕ)) (c : α → ℚ) (D : ℕ)
    (hD : ∀ i, (a i).sum (fun _ e => e) ≤ D) :
    (∑ i, monomial (a i) (c i)).totalDegree ≤ D := by
  exact totalDegree_finsetSum_le (fun i _ => (totalDegree_monomial_le _ _).trans (hD i))

theorem monomial_relation_eval {σ α : Type*} [Fintype α]
    (a : α → (σ →₀ ℕ)) (c : α → ℚ) (z : σ → ℤ)
    (hz : ∑ i, c i * (eval z (monomial (a i) (1:ℤ)) : ℚ) = 0) :
    eval (fun i => (z i : ℚ)) (∑ i, monomial (a i) (c i)) = 0 := by
  rw [map_sum]
  convert hz using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [eval_monomial,one_mul,Finsupp.prod,Int.cast_prod,Int.cast_pow]

end

section
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem IntegerPatch.eval_chart {n : ℕ} (P : IntegerPatch n) (z : Fin n → ℤ)
    (p : MvPolynomial (Fin n) ℤ) :
    eval (fun i => z ((Equiv.Set.sumCompl P.free) i))
      (rename (Equiv.Set.sumCompl P.free).symm p) = eval z p := by
  rw [eval_rename]
  simp [Function.comp_def]

theorem IntegerPatch.minor_chart {n : ℕ} (P : IntegerPatch n) (z : Fin n → ℤ) :
    (Matrix.of (fun i j : ↥(P.freeᶜ) =>
      eval (fun a => z ((Equiv.Set.sumCompl P.free) a))
        (pderiv (Sum.inr j) (rename (Equiv.Set.sumCompl P.free).symm (P.equations i))))).det =
      eval z P.minor := by
  classical
  let e := Equiv.Set.sumCompl P.free
  have he (j : ↥(P.freeᶜ)) : e.symm j.val = Sum.inr j := by
    apply e.injective
    simp [e]
  have hm : (Matrix.of (fun i j : ↥(P.freeᶜ) =>
      eval (fun a => z (e a)) (pderiv (Sum.inr j) (rename e.symm (P.equations i))))) =
      Matrix.of (fun i j : ↥(P.freeᶜ) => eval z (pderiv j.val (P.equations i))) := by
    ext i j
    change eval (fun a => z (e a)) (pderiv (Sum.inr j) (rename e.symm (P.equations i))) = _
    rw [← he j,pderiv_rename e.symm.injective]
    exact P.eval_chart z _
  change (Matrix.of (fun i j : ↥(P.freeᶜ) =>
      eval (fun a => z (e a)) (pderiv (Sum.inr j) (rename e.symm (P.equations i))))).det = _
  rw [hm]
  exact ((eval z).map_det (fun i j : ↥(P.freeᶜ) => pderiv j.val (P.equations i))).symm

theorem IntegerPatch.residue_relation {n : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    (P : IntegerPatch n) (z : Fin n → ℤ) (hz : ∀ j, eval z (P.equations j) = 0)
    (Q : Finset ℕ) (hprime : ∀ p ∈ Q, p.Prime)
    (hgood : ∀ p ∈ Q, ¬ (p:ℤ) ∣ eval z P.minor)
    (m : ℕ) (R : α → MvPolynomial (Fin n) ℤ) (w : β → Fin n → ℤ)
    (hw : ∀ p ∈ Q, ∀ b j, (p:ℤ) ∣ w b j-z j)
    (hroot : ∀ b j, eval (w b) (P.equations j) = 0)
    (hm : ∀ r : α → (P.free →₀ ℕ), Function.Injective r → m ≤ ∑ a, (r a).sum (fun _ e => e))
    (B : α → ℝ) (hB : ∀ a b, |(eval (w b) (R a) : ℝ)| ≤ B a)
    (hlt : (Nat.factorial (Fintype.card α) : ℝ) * ∏ a, B a < (∏ p ∈ Q, (p:ℝ))^m) :
    ∃ c : α → ℚ, c ≠ 0 ∧ ∀ b, ∑ a, c a * (eval (w b) (R a) : ℚ) = 0 := by
  classical
  let e := Equiv.Set.sumCompl P.free
  have hc := simultaneous_residue_relation
    (fun j => rename e.symm (P.equations j)) (fun j => z (e j))
    (fun j => (P.eval_chart z _).trans (hz j)) Q hprime
    (fun p hp => by rw [P.minor_chart z]; exact hgood p hp) m
    (fun a => rename e.symm (R a)) (fun b j => w b (e j))
    (fun p hp b j => hw p hp b (e j))
    (fun b j => (P.eval_chart (w b) _).trans (hroot b j)) hm B
    (fun a b => by rw [P.eval_chart]; exact hB a b) hlt
  simpa only [eval_rename,Function.comp_def,Equiv.apply_symm_apply] using hc

theorem weighted_integer_patch_cut {n : ℕ} (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i)
    (h : ℕ) (hh : 0 < h) (δ ν c Cbox : ℝ)
    (hδ : 0 < δ) (hν : 0 < ν) (hc : 0 ≤ c) (hboxC : 1 ≤ Cbox) :
    ∃ D : ℕ, ∃ X₀ : ℝ, ∀ X : ℝ, X₀ < X →
      ∀ I : Ideal (MvPolynomial (Fin n) ℂ),
      (∀ T : ℝ, 1 ≤ T → T^h / ((h.factorial : ℝ)*δ^h) - c*T^(h-1) ≤
        weightedHilbert I ω T) →
      ∀ P : IntegerPatch n, Nat.card P.free = h →
      ∀ z : Fin n → ℤ, (∀ j, eval z (P.equations j) = 0) →
      ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, ¬ (p:ℤ) ∣ eval z P.minor) → X^(δ+ν) ≤ ∏ p ∈ Q, (p:ℝ) →
      ∀ S : Finset (Fin n → ℤ),
      (∀ p ∈ Q, ∀ w ∈ S, ∀ j, (p:ℤ) ∣ w j-z j) →
      (∀ w ∈ S, ∀ j, eval w (P.equations j) = 0) →
      (∀ w ∈ S, ∀ j, |(w j : ℝ)| ≤ Cbox*X^(ω j)) →
      ∃ p : MvPolynomial (Fin n) ℂ, p.totalDegree ≤ D ∧ p ∉ I ∧
        ∀ w ∈ S, eval (fun i => (w i : ℂ)) p = 0 := by
  classical
  obtain ⟨C,hC,hshift⟩ := hilbert_simplex_shift h hh δ c hδ hc
  obtain ⟨t,hL,hmargin⟩ := exists_simplex_margin h hh ν C hν
  let D := weightedDegreeBound ω (δ*t+C)
  let L := (t+h).choose h
  let m := h*((t+h).choose (h+1))
  refine ⟨D,max 1 ((L.factorial : ℝ)*(Cbox^D)^L),?_⟩
  intro X hX I hH P hfree z hz Q hprime hgood hQ S hw hroot hbox
  have hX1 : 1 < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hlarge : (L.factorial : ℝ)*(Cbox^D)^L < X := lt_of_le_of_lt (le_max_right _ _) hX
  let U := fun t : ℕ => weightedMonomials ω (δ*t+C)
  have hU : ∀ t, U t ⊆ U (t+1) := by
    intro t
    apply weightedMonomials_mono ω hω
    push_cast
    linarith
  have hweight : ∀ t a, a ∈ U t → monomialWeight ω a ≤ δ*t+C := by
    intro t a ha
    exact (mem_weightedMonomials ω hω _ a).mp ha
  have hr : ∀ t, (t+h).choose h ≤ Module.finrank ℂ
      (Submodule.span ℂ ((fun a => Ideal.Quotient.mk I (monomial a (1:ℂ))) '' (U t : Set _))) := by
    intro t
    have hT : 1 ≤ δ*(t:ℝ)+C := by nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg t)]
    exact_mod_cast (hshift t).trans (hH _ hT)
  obtain ⟨A,hA,hcard,hli,hsum⟩ := independent_weighted_simplex
    (fun a => Ideal.Quotient.mk I (monomial a (1:ℂ))) U hU (monomialWeight ω) δ C hweight h hr t
  have hcard' : Fintype.card A = L := by simpa only [Fintype.card_coe] using hcard
  have hD : ∀ a : A, a.val.sum (fun _ e => e) ≤ D := fun a =>
    weighted_monomial_degree_bound ω hω _ a.val (hweight t a.val (hA a.property))
  have hsum' : ∑ a : A, monomialWeight ω a.val ≤ δ*(m:ℝ)+C*(Fintype.card A) := by
    rw [hcard',Finset.sum_coe_sort]
    exact hsum
  have hmargin' : (C+1)*(Fintype.card A : ℝ) ≤ ν*(m:ℝ) := by
    rw [hcard']; exact hmargin
  have hlt : (Fintype.card A).factorial * ∏ a : A, (Cbox^D*X^(monomialWeight ω a.val)) <
      (∏ p ∈ Q, (p:ℝ))^m := weighted_row_product_lt
        (fun a : A => monomialWeight ω a.val) Cbox X δ ν C _ D m hX1
        (by rwa [hcard']) (by rwa [hcard']) hsum' hmargin' hQ
  have hf : Fintype.card P.free = h := by simpa only [Nat.card_eq_fintype_card] using hfree
  obtain ⟨c,hc,hrel⟩ := P.residue_relation z hz Q hprime hgood m
    (fun a : A => monomial a.val (1:ℤ)) (fun w : S => w.val)
    (fun p hp w j => hw p hp w.val w.property j)
    (fun w j => hroot w.val w.property j)
    (fun r hr => by
      have hm := monomial_order_simplex_bound r hr t (by rw [hf]; exact hcard'.symm.le)
      simpa only [hf,monomialOrder] using hm)
    (fun a : A => Cbox^D*X^(monomialWeight ω a.val))
    (fun a w => integer_monomial_abs_le ω Cbox X hboxC (lt_trans zero_lt_one hX1)
      w.val (hbox w.val w.property) a.val D (hD a)) hlt
  have hp := independent_monomial_relation_proper I _ hli.linearIndependent_restrict c hc
  let p : MvPolynomial (Fin n) ℚ := ∑ a : A, monomial a.val (c a)
  have hpdeg : (MvPolynomial.map (algebraMap ℚ ℂ) p).totalDegree = p.totalDegree := by
    simp only [totalDegree,support_map_of_injective p (f := algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective]
  refine ⟨MvPolynomial.map (algebraMap ℚ ℂ) p,
    hpdeg.le.trans (monomial_relation_degree _ _ D hD),hp,?_⟩
  intro w hw
  have he := congrArg (algebraMap ℚ ℂ) (monomial_relation_eval _ _ w (hrel ⟨w,hw⟩))
  rw [MvPolynomial.eval_map]
  simpa only [MvPolynomial.eval₂_comp,map_zero,Function.comp_def,map_intCast] using he

end

open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

theorem IntegerPatch.equation_vanishes {n : ℕ} {K : Type*} [Field K] [CharZero K]
    {P : IntegerPatch n} {I : Ideal (MvPolynomial (Fin n) K)}
    (hP : P.On I) {z : Fin n → ℤ} (hz : PointOn I z) (j : ↥(P.freeᶜ)) :
    eval z (P.equations j) = 0 := by
  apply Int.cast_injective (α := K)
  rw [Int.cast_zero,← eval_int_map]
  exact hz _ (hP.2.1 j)

theorem physical_weighted_descent {n : ℕ} (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (q : ℕ) (hq : 0 < q) (δ ν c Cbox : ℝ)
    (hδ : 0 < δ) (hν : 0 < ν) (hc : 0 ≤ c) (hCbox : 1 ≤ Cbox) :
    ∃ D : ℕ, ∃ X₀ : ℝ, ∀ X : ℝ, X₀ < X →
      ∀ (r E : ℕ) (G : KernelGeometry n) (d : ℕ → ℕ) (A h e i : ℕ),
      D ≤ d i → d i ≤ E →
      (∀ w ∈ G.points, ∀ j, |(w j : ℝ)| ≤ Cbox*X^(ω j)) →
      ∀ (z : Fin n → ℤ), z ∈ G.points →
      ∀ s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n,
      PhysicalState G h (pathDegreeBudget n d A h e i) z s →
      affineDimension s.1 = q →
      (∀ T : ℝ, 1 ≤ T → T^q / ((q.factorial : ℝ)*δ^q) - c*T^(q-1) ≤
        weightedHilbert s.1 ω T) →
      ∀ B : Fin r → Finset ℕ, ∀ Q : Finset ℕ,
      Q ⊆ cumulativeBlockPrimes B i → (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, ¬ (p:ℤ) ∣ eval z s.2.minor) → X^(δ+ν) ≤ ∏ p ∈ Q, (p:ℝ) →
      affineDimension (physicalNext G d A h e z i s (physicalKernel (E := E) G d z i s B)).1 <
        affineDimension s.1 := by
  classical
  obtain ⟨D,X₀,hcut⟩ := weighted_integer_patch_cut ω hω q hq δ ν c Cbox hδ hν hc hCbox
  refine ⟨D,X₀,?_⟩
  intro X hX r E G d A h e i hD hE hbox z hz s hs hdim hH B Q hQ hprime hgood hprod
  let S := evaluationCell G.points s.1 z (cumulativeBlockPrimes B i)
  obtain ⟨p,hpD,hpI,hpS⟩ := hcut X hX s.1 hH s.2 (hs.2.1.1.trans hdim) z
    (fun j => IntegerPatch.equation_vanishes hs.2.1 hs.2.2.2.1 j) Q hprime hgood hprod S
    (fun p hp w hw j => (Finset.mem_filter.mp hw).2.2 p (hQ hp) j)
    (fun w hw j => IntegerPatch.equation_vanishes hs.2.1 (Finset.mem_filter.mp hw).2.1 j)
    (fun w hw j => hbox w (Finset.mem_filter.mp hw).1 j)
  apply (physical_step (E := E) G d A h e z hz i s hs B).2.2.2.2.2
  intro hsub
  apply hpI
  apply hsub
  exact (mem_stagedKernelPolynomials hE S p).mpr ⟨hpD.trans hD,hpS⟩

theorem PointOn.eq_of_zeroDim {n : ℕ} {K : Type*} [Field K] [CharZero K]
    {I : Ideal (MvPolynomial (Fin n) K)} [I.IsPrime]
    (hd : affineDimension I = 0) {z w : Fin n → ℤ}
    (hz : PointOn I z) (hw : PointOn I w) : z = w := by
  have hI := zeroDim_eq_point I hd (fun j => (z j : K)) hz
  funext j
  apply Int.cast_injective (α := K)
  have hmem : X j - C (z j : K) ∈ I := by
    rw [hI,RingHom.mem_ker]
    simp
  have he : (w j : K) - (z j : K) = 0 := by simpa using hw _ hmem
  exact (sub_eq_zero.mp he).symm

theorem physical_zeroDim_fiber {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (i : ℕ) (z : G.points) (S : Finset G.points)
    (hd : affineDimension (physicalStateAt (E := E) G d A h e start B i z).1 = 0) :
    (S.filter fun w => physicalNode (E := E) G d A h e start B i w =
      physicalNode (E := E) G d A h e start B i z).card ≤ 1 := by
  classical
  let I := (physicalStateAt (E := E) G d A h e start B i z).1
  have hz := physicalStateAt_good (E := E) G d A h e start hs B i z
  let : I.IsPrime := hz.1.1
  apply (Finset.card_le_card (t := {z}) ?_).trans (by simp)
  intro w hw
  have he := congrArg (fun x => x.1) (Finset.mem_filter.mp hw).2
  change physicalStateAt (E := E) G d A h e start B i w =
    physicalStateAt (E := E) G d A h e start B i z at he
  have hw := (physicalStateAt_good (E := E) G d A h e start hs B i w).2.2.2.1
  rw [he] at hw
  exact Finset.mem_singleton.mpr (Subtype.ext (PointOn.eq_of_zeroDim hd hw hz.2.2.2.1))

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PrimePools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

theorem physical_minor_dvd_pathProduct {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e m : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (z : G.points) (i : ℕ) (hi : i ≤ m) :
    eval z.val (physicalStateAt (E := E) G d A h e start B i z).2.minor ∣
      physicalPathProduct (E := E) G d A h e m start B z := by
  apply List.dvd_prod
  apply List.mem_map.mpr
  exact ⟨physicalStateAt (E := E) G d A h e start B i z,
    adaptiveStateAt_mem_states _ _ m i 0 _ B hi,rfl⟩

theorem filter_card_le_of_fraction {α : Type*} (S : Finset α) (P : α → Prop)
    [DecidablePred P] (ξ : ℝ)
    (h : (∑ p ∈ S, if P p then (1 : ℝ) else 0) / S.card ≤ ξ) :
    ((S.filter P).card : ℝ) ≤ ξ*S.card := by
  by_cases hs : S.card = 0
  · have he := Finset.card_eq_zero.mp hs
    subst S
    simp
  have hp : (0 : ℝ) < S.card := by exact_mod_cast (Nat.pos_of_ne_zero hs)
  rw [Finset.sum_boole] at h
  exact (div_le_iff₀ hp).mp h

theorem PhysicalRegular.bad_minor {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e m : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (ξ : ℝ) (z : G.points)
    (hz : PhysicalRegular (E := E) G d A h e m start B ξ z) (i : ℕ) (hi : i ≤ m) (j : Fin r) :
    (((B j).filter fun p : ℕ => (p:ℤ) ∣ eval z.val
      (physicalStateAt (E := E) G d A h e start B i z).2.minor).card : ℝ) ≤ ξ*(B j).card := by
  have hsub : ((B j).filter fun p : ℕ => (p:ℤ) ∣ eval z.val
      (physicalStateAt (E := E) G d A h e start B i z).2.minor) ⊆
      ((B j).filter fun p : ℕ => (p:ℤ) ∣ physicalPathProduct (E := E) G d A h e m start B z) := by
    intro p hp
    obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp,hd.trans (physical_minor_dvd_pathProduct G d A h e m start B z i hi)⟩
  calc
    _ ≤ (((B j).filter fun p : ℕ =>
        (p:ℤ) ∣ physicalPathProduct (E := E) G d A h e m start B z).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := filter_card_le_of_fraction _ _ ξ (hz j)

theorem cumulative_good_prime_product {r : ℕ} (B : Fin r → Finset ℕ)
    (hdisj : ∀ a b, a ≠ b → Disjoint (B a) (B b)) (i : ℕ) (v : ℤ)
    (X ζ ξ : ℝ) (hX : 1 ≤ X) (hζ : 0 ≤ ζ)
    (hlo : ∀ j p, p ∈ B j → X^ζ ≤ (p:ℝ))
    (hbad : ∀ j, (((B j).filter fun p : ℕ => (p:ℤ) ∣ v).card : ℝ) ≤ ξ*(B j).card) :
    X^((1-ξ)*ζ*∑ j ∈ Finset.univ.filter (fun j : Fin r => j.val ≤ i), ((B j).card : ℝ)) ≤
      ∏ p ∈ (cumulativeBlockPrimes B i).filter (fun p : ℕ => ¬ (p:ℤ) ∣ v), (p:ℝ) := by
  classical
  let J := Finset.univ.filter (fun j : Fin r => j.val ≤ i)
  let Q := (cumulativeBlockPrimes B i).filter (fun p : ℕ => ¬ (p:ℤ) ∣ v)
  have hg (j : Fin r) : (1-ξ)*(B j).card ≤
      (((B j).filter fun p : ℕ => ¬ (p:ℤ) ∣ v).card : ℝ) := by
    have hc := Finset.card_filter_add_card_filter_not (s := B j) (fun p : ℕ => (p:ℤ) ∣ v)
    have hcr : (((B j).filter fun p : ℕ => (p:ℤ) ∣ v).card : ℝ) +
      (((B j).filter fun p : ℕ => ¬ (p:ℤ) ∣ v).card : ℝ) = (B j).card := by exact_mod_cast hc
    nlinarith [hbad j]
  have heq : Q = J.biUnion (fun j => (B j).filter fun p : ℕ => ¬ (p:ℤ) ∣ v) := by
    ext p
    simp only [Q,J,cumulativeBlockPrimes,Finset.mem_filter,Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨j,hj,hp⟩,hg⟩
      exact ⟨j,hj,hp,hg⟩
    · rintro ⟨j,hj,hp,hg⟩
      exact ⟨⟨j,hj,hp⟩,hg⟩
  have hpair : (J : Set (Fin r)).PairwiseDisjoint
      (fun j => (B j).filter fun p : ℕ => ¬ (p:ℤ) ∣ v) := by
    intro a _ b _ hab
    exact (hdisj a b hab).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcard : (1-ξ)*(∑ j ∈ J, ((B j).card : ℝ)) ≤ (Q.card : ℝ) := by
    rw [heq,Finset.card_biUnion hpair,Nat.cast_sum,Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hg j)
  calc
    _ ≤ X^(ζ*(Q.card : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hX
      nlinarith
    _ = (X^ζ)^Q.card := Real.rpow_mul_natCast (zero_le_one.trans hX) ζ Q.card
    _ = ∏ _p ∈ Q, X^ζ := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · intro p _; exact Real.rpow_nonneg (zero_le_one.trans hX) _
      · intro p hp
        obtain ⟨j,_,hpj⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hp).1
        exact hlo j p hpj

end

section
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

theorem firstStop_le (r : ℕ) (P : ℕ → Prop) : firstStop r P ≤ r :=
  Nat.find_min' _ (Or.inl rfl)

theorem firstStop_spec (r : ℕ) (P : ℕ → Prop) : firstStop r P = r ∨ P (firstStop r P) :=
  Nat.find_spec (show ∃ i, i = r ∨ P i from ⟨r,Or.inl rfl⟩)

theorem firstStop_not_before (r : ℕ) (P : ℕ → Prop) {i : ℕ} (hi : i < firstStop r P) : ¬ P i :=
  fun hp => Nat.find_min _ hi (Or.inr hp)

theorem dimension_until_firstStop (r : ℕ) (dim : ℕ → ℕ) (Ex : ℕ → Prop)
    (hzero : dim 0 ≤ r) (hmono : ∀ i < r, dim (i+1) ≤ dim i)
    (hstep : ∀ i < r, ¬ Ex i → dim i = r-i → dim (i+1) < dim i) :
    ∀ i ≤ firstStop r (fun i => Ex i ∨ dim i = 0), dim i ≤ r-i := by
  intro i
  induction i with
  | zero => intro _; simpa using hzero
  | succ i ih =>
    intro hi
    have his : i < firstStop r (fun i => Ex i ∨ dim i = 0) := by omega
    have hir : i < r := lt_of_lt_of_le his (firstStop_le _ _)
    have hd := ih his.le
    have hstop := firstStop_not_before r (fun i => Ex i ∨ dim i = 0) his
    by_cases he : dim i = r-i
    · have hs := hstep i hir (fun h => hstop (Or.inl h)) he
      omega
    · have hm := hmono i hir
      omega

theorem firstStop_terminal (r : ℕ) (dim : ℕ → ℕ) (Ex : ℕ → Prop)
    (hzero : dim 0 ≤ r) (hmono : ∀ i < r, dim (i+1) ≤ dim i)
    (hstep : ∀ i < r, ¬ Ex i → dim i = r-i → dim (i+1) < dim i) :
    let t := firstStop r (fun i => Ex i ∨ dim i = 0)
    Ex t ∨ dim t = 0 := by
  dsimp only
  rcases firstStop_spec r (fun i => Ex i ∨ dim i = 0) with he | hp
  · right
    have hd := dimension_until_firstStop r dim Ex hzero hmono hstep
      (firstStop r (fun i => Ex i ∨ dim i = 0)) le_rfl
    rw [he,Nat.sub_self] at hd
    rw [he]
    exact Nat.eq_zero_of_le_zero hd
  · exact hp

theorem physical_fiber_le_points {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (i : ℕ) (z : G.points) (S : Finset G.points) :
    (S.filter fun w => physicalNode (E := E) G d A h e start B i w =
      physicalNode (E := E) G d A h e start B i z).card ≤
    (G.points.filter (PointOn (physicalStateAt (E := E) G d A h e start B i z).1)).card := by
  classical
  let F := S.filter fun w => physicalNode (E := E) G d A h e start B i w =
    physicalNode (E := E) G d A h e start B i z
  have hsub : F.image (fun w : G.points => w.val) ⊆
      G.points.filter (PointOn (physicalStateAt (E := E) G d A h e start B i z).1) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨w,hw,hwx⟩
    rw [← hwx]
    have hn := (Finset.mem_filter.mp hw).2
    have he := congrArg Prod.fst hn
    change physicalStateAt (E := E) G d A h e start B i w =
      physicalStateAt (E := E) G d A h e start B i z at he
    have hp := (physicalStateAt_good (E := E) G d A h e start hs B i w).2.2.2.1
    rw [he] at hp
    exact Finset.mem_filter.mpr ⟨w.property,hp⟩
  calc
    _ = (F.image (fun w : G.points => w.val)).card :=
      (Finset.card_image_of_injective F Subtype.val_injective).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem physical_dimension_mono {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (i : ℕ) (z : G.points) :
    affineDimension (physicalStateAt (E := E) G d A h e start B (i+1) z).1 ≤
      affineDimension (physicalStateAt (E := E) G d A h e start B i z).1 := by
  rw [physicalStateAt_succ]
  exact (physical_step (E := E) G d A h e z.val z.property i _
    (physicalStateAt_good (E := E) G d A h e start hs B i z) B).2.2.2.2.1

end

theorem finite_prime_pool (N M : ℕ) (hM : M ≠ 0) :
    ∃ P : Finset ℕ, P.card = N ∧ ∀ p ∈ P, p.Prime ∧ M < p ∧ p ≤ 2^N*M := by
  induction N with
  | zero => exact ⟨∅,by simp,by simp⟩
  | succ N ih =>
    obtain ⟨P,hcard,hP⟩ := ih
    obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2^N*M)
      (Nat.mul_ne_zero (by positivity) hM)
    have hnot : p ∉ P := fun h => (not_lt_of_ge (hP p h).2.2) hlo
    refine ⟨insert p P,by simp [hnot,hcard],?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · refine ⟨hp,?_,?_⟩
      · exact (Nat.le_mul_of_pos_left M (by positivity : 0 < 2^N)).trans_lt hlo
      · simpa only [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hhi
    · obtain ⟨hqprime,hqlo,hqhi⟩ := hP q hq
      refine ⟨hqprime,hqlo,hqhi.trans ?_⟩
      exact Nat.mul_le_mul_right M (Nat.pow_le_pow_right (by decide) (Nat.le_succ N))

theorem disjoint_prime_pools (r t : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    ∃ P : Fin r → Finset ℕ,
      (∀ i, (P i).card = t) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      ∀ i p, p ∈ P i → p.Prime ∧ x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2^(r*t+1)*x := by
  classical
  obtain ⟨Q,hcard,hQ⟩ := finite_prime_pool (r*t) ⌈x⌉₊
    (Nat.ne_of_gt (Nat.ceil_pos.mpr (zero_lt_one.trans_le hx)))
  let e : (Fin r × Fin t) ≃ Q := Fintype.equivOfCardEq (by simp [hcard])
  let P : Fin r → Finset ℕ := fun i => Finset.univ.image (fun j => (e (i,j)).val)
  have hinj (i : Fin r) : Function.Injective (fun j => (e (i,j)).val) := by
    intro j k he
    exact (Prod.mk.inj (e.injective (Subtype.ext he))).2
  refine ⟨P,?_,?_,?_⟩
  · intro i
    simp only [P,Finset.card_image_of_injective _ (hinj i),Finset.card_univ,Fintype.card_fin]
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hpi
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hpj
    exact hij (Prod.mk.inj (e.injective (Subtype.ext (ha.trans hb.symm)))).1
  · intro i p hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hprime,hlo,hhi⟩ := hQ _ (e (i,j)).property
    refine ⟨hprime,(Nat.le_ceil x).trans (by exact_mod_cast hlo.le),?_⟩
    have hc : (⌈x⌉₊ : ℝ) ≤ 2*x := (Nat.ceil_lt_add_one (zero_le_one.trans hx)).le.trans (by linarith)
    calc
      ((e (i,j)).val : ℝ) ≤ (2 : ℝ)^(r*t)*(⌈x⌉₊ : ℝ) := by exact_mod_cast hhi
      _ ≤ 2^(r*t)*(2*x) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 2^(r*t+1)*x := by rw [pow_succ]; ring

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_DegreeSchedules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators
namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

theorem physicalDegreeRecord_eq_path (n A h e : ℕ) (chooseDegree : ℕ → ℕ → ℕ) :
    ∀ i, pathDegreeBudget n (fun j => chooseDegree j (physicalDegreeRecord n A h chooseDegree e j))
      A h e i = physicalDegreeRecord n A h chooseDegree e i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih => simp only [pathDegreeBudget,physicalDegreeRecord,ih]

theorem physical_degree_schedule (n A h e r : ℕ) (chooseDegree : ℕ → ℕ → ℕ) :
    ∃ d : ℕ → ℕ, ∃ E : ℕ, ∀ i < r,
      d i = chooseDegree i (pathDegreeBudget n d A h e i) ∧ d i ≤ E := by
  let d := fun j => chooseDegree j (physicalDegreeRecord n A h chooseDegree e j)
  refine ⟨d,(Finset.range r).sup d,?_⟩
  intro i hi
  refine ⟨?_,Finset.le_sup (f := d) (Finset.mem_range.mpr hi)⟩
  dsimp only [d]
  rw [physicalDegreeRecord_eq_path]

theorem physical_block_width (a γ ζ : ℝ) (T t : ℕ)
    (ha : 0 ≤ a) (hγ : 0 < γ) (hζ : 0 < ζ) (hwidth : ζ*T ≤ γ)
    (hlo : ⌊(a+γ)/ζ⌋₊ < t) (hhi : t ≤ ⌊(a+γ)/ζ⌋₊+T) :
    a+γ ≤ ζ*t ∧ ζ*t ≤ a+2*γ := by
  have hx : 0 ≤ (a+γ)/ζ := div_nonneg (by linarith) hζ.le
  have hfloor : (⌊(a+γ)/ζ⌋₊:ℝ) ≤ (a+γ)/ζ := Nat.floor_le hx
  have ht : (a+γ)/ζ < (t:ℝ) := (Nat.floor_lt hx).mp hlo
  have htc : (t:ℝ) ≤ (⌊(a+γ)/ζ⌋₊:ℝ)+T := by exact_mod_cast hhi
  constructor
  · exact (div_lt_iff₀ hζ).mp ht |>.le.trans_eq (mul_comm _ _)
  · have hh := (le_div_iff₀ hζ).mp hfloor
    nlinarith

theorem physical_cumulative_margin {r : ℕ} (a δ : Fin r → ℝ) (t : Fin r → ℕ)
    (γ ζ ξ : ℝ) (ha : ∀ i, 0 ≤ a i) (hγ : 0 < γ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hloss : ξ*((∑ i, a i)+(r:ℝ)*γ) ≤ γ/2)
    (hwidth : ∀ i, a i+γ ≤ ζ*t i)
    (hδ : ∀ i, δ i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin r => j.val ≤ i.val), a j) :
    ∀ i, δ i+γ/2 ≤ (1-ξ)*ζ*∑ j ∈
      Finset.univ.filter (fun j : Fin r => j.val ≤ i.val), (t j:ℝ) := by
  classical
  intro i
  let J := Finset.univ.filter (fun j : Fin r => j.val ≤ i.val)
  have hiJ : i ∈ J := by simp [J]
  have hcard : 1 ≤ J.card := Finset.one_le_card.mpr ⟨i,hiJ⟩
  have hcardr : J.card ≤ r := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  have hs : ∑ j ∈ J, a j ≤ ∑ j, a j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => ha j)
  have hsum : (∑ j ∈ J, a j)+(J.card:ℝ)*γ ≤ ζ*∑ j ∈ J, (t j:ℝ) := by
    simpa only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]
      using Finset.sum_le_sum (fun j (_ : j ∈ J) => hwidth j)
  have hcr : (J.card:ℝ) ≤ r := by exact_mod_cast hcardr
  have hc1 : (1:ℝ) ≤ J.card := by exact_mod_cast hcard
  have hg : γ ≤ (J.card:ℝ)*γ := by nlinarith
  have hsmall : ξ*((∑ j ∈ J, a j)+(J.card:ℝ)*γ) ≤ γ/2 :=
    (mul_le_mul_of_nonneg_left (by nlinarith) hξ0).trans hloss
  have hmul := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hξ1)
  have hd := hδ i
  change δ i ≤ ∑ j ∈ J, a j at hd
  dsimp only [J] at *
  nlinarith

end
section
open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

theorem physical_stagewise_stopped_count {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (S : Finset G.points) (M b : Fin r → ℕ)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)) (T : ℕ)
    (Ex : ℕ → Ideal (MvPolynomial (Fin n) ℂ) → Prop)
    (hstart : ∀ z ∈ S, start z ∈ L) (hT : 1 ≤ T)
    (hroot : ∀ z ∈ S, affineDimension (start z).1 ≤ r)
    (hM : ∀ i, 1 ≤ M i) (hprime : ∀ i, ∀ p ∈ B i, p.Prime)
    (hupper : ∀ i, ∀ p ∈ B i, p ≤ M i)
    (hbad : ∀ i : Fin r, ∀ z ∈ S,
      ((B i).filter fun p : ℕ => (p:ℤ) ∣ eval z.val
        (physicalStateAt (E := E) G d A h e start B i.val z).2.minor).card ≤ b i)
    (hcut : ∀ i < r, ∀ z ∈ S,
      ¬ Ex i (physicalStateAt (E := E) G d A h e start B i z).1 →
      affineDimension (physicalStateAt (E := E) G d A h e start B i z).1 = r-i →
      affineDimension (physicalStateAt (E := E) G d A h e start B (i+1) z).1 <
        affineDimension (physicalStateAt (E := E) G d A h e start B i z).1)
    (hex : ∀ i ≤ r, ∀ z ∈ S,
      Ex i (physicalStateAt (E := E) G d A h e start B i z).1 →
      (G.points.filter (PointOn (physicalStateAt (E := E) G d A h e start B i z).1)).card ≤ T) :
    S.card ≤ (∑ i ∈ Finset.range (r+1), L.length * ∏ j ∈ Finset.range i,
      if hj : j < r then physicalBranchAllowance n d A h e B M b
        (fun k => r-k.val) ⟨j,hj⟩ else 1) * T := by
  classical
  let dim := fun z i => affineDimension (physicalStateAt (E := E) G d A h e start B i z).1
  let ex := fun z i => Ex i (physicalStateAt (E := E) G d A h e start B i z).1
  let stop := fun z => firstStop r (fun i => ex z i ∨ dim z i = 0)
  have hm (z) (i) (_hi : i < r) : dim z (i+1) ≤ dim z i :=
    physical_dimension_mono G d A h e start hs B i z
  have hz (z) (hz : z ∈ S) : dim z 0 ≤ r := hroot z hz
  have hc (z) (hz : z ∈ S) (i) (hi : i < r) :
      ¬ ex z i → dim z i = r-i → dim z (i+1) < dim z i := hcut i hi z hz
  have hd (z) (hz' : z ∈ S) := dimension_until_firstStop r (dim z) (ex z) (hz z hz') (hm z) (hc z hz')
  have ht (z) (hz' : z ∈ S) := firstStop_terminal r (dim z) (ex z) (hz z hz') (hm z) (hc z hz')
  apply physical_forest_count G d A h e start hs B S stop M b (fun k => r-k.val) L T
    hstart (fun _ _ => firstStop_le _ _) hM hprime hupper
  · intro i z hz hi
    exact hd z hz i.val hi.le
  · intro i z hz _
    exact hbad i z hz
  · intro i hi z hz hzi
    have hsub : (S.filter fun w => stop w = i ∧ physicalNode (E := E) G d A h e start B i w =
        physicalNode (E := E) G d A h e start B i z) ⊆
        S.filter (fun w => physicalNode (E := E) G d A h e start B i w =
        physicalNode (E := E) G d A h e start B i z) := by
      intro w hw
      obtain ⟨hw,_,hn⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨hw,hn⟩
    apply (Finset.card_le_card hsub).trans
    have hterm : ex z i ∨ dim z i = 0 := by
      have hh := ht z hz
      change ex z (stop z) ∨ dim z (stop z) = 0 at hh
      simpa only [hzi] using hh
    rcases hterm with he | he
    · exact (physical_fiber_le_points G d A h e start hs B i z S).trans (hex i hi z hz he)
    · exact (physical_zeroDim_fiber G d A h e start hs B i z S he).trans hT

end

section
open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

theorem physical_initial_context {n : ℕ} (G : KernelGeometry n) (A h e : ℕ)
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (hd : affineDimension I ≤ h) (he : affineDegree I ≤ e)
    (hG : ∀ z ∈ G.points, PointOn I z) :
    ∃ L : List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n),
      L.length ≤ patchCountBudget n A h e ∧
    ∃ start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n,
      ∀ z, start z ∈ L ∧ PhysicalState G h (patchDegreeBudget n A h e) z.val (start z) ∧
        I ≤ (start z).1 ∧ EquationLock (start z).1 G.points A := by
  classical
  obtain ⟨L,hL,hgood,hcover⟩ := bounded_integer_patch_cover A h e I hd he G.points hG
    G.height G.one_le_height G.bounded
  choose start hstart hcov using fun z : G.points => hcover z.val z.property
  refine ⟨L,hL,start,fun z => ⟨hstart z,?_,?_,?_⟩⟩
  · have hs := hgood (start z) (hstart z)
    exact ⟨⟨hs.1,hs.2.2.1,hs.2.2.2.1⟩,hs.2.2.2.2.1,hs.2.2.2.2.2.1,hcov z⟩
  · exact (hgood _ (hstart z)).2.1
  · exact (hgood _ (hstart z)).2.2.2.2.2.2

theorem physicalStateAt_context {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (hstart : ∀ z, I ≤ (start z).1 ∧ EquationLock (start z).1 G.points A)
    (i : ℕ) (z : G.points) :
    I ≤ (physicalStateAt (E := E) G d A h e start B i z).1 ∧
      EquationLock (physicalStateAt (E := E) G d A h e start B i z).1 G.points A := by
  induction i with
  | zero => exact hstart z
  | succ i ih =>
    have step := physical_step (E := E) G d A h e z.val z.property i _
      (physicalStateAt_good (E := E) G d A h e start hs B i z) B
    rw [physicalStateAt_succ]
    refine ⟨ih.1.trans step.2.2.1,?_⟩
    exact ((kernelChildList_spec G (d i) A h (pathDegreeBudget n d A h e i) _ _
      (physicalStateAt_good (E := E) G d A h e start hs B i z).1).2.1 _ step.2.1).1.2.2.2.2.2.2

end

section
open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

theorem physical_regular_count {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (M : Fin r → ℕ) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)) (T : ℕ)
    (Ex : ℕ → Ideal (MvPolynomial (Fin n) ℂ) → Prop)
    (hstart : ∀ z, start z ∈ L) (hT : 1 ≤ T)
    (hroot : ∀ z, affineDimension (start z).1 ≤ r)
    (hM : ∀ i, 1 ≤ M i) (hprime : ∀ i, ∀ p ∈ B i, p.Prime)
    (hupper : ∀ i, ∀ p ∈ B i, p ≤ M i)
    (hhalf : (G.points.card:ℝ)/2 ≤ (Finset.univ.filter
      (PhysicalRegular (E := E) G d A h e r start B ξ)).card)
    (hcut : ∀ i < r, ∀ z, PhysicalRegular (E := E) G d A h e r start B ξ z →
      ¬ Ex i (physicalStateAt (E := E) G d A h e start B i z).1 →
      affineDimension (physicalStateAt (E := E) G d A h e start B i z).1 = r-i →
      affineDimension (physicalStateAt (E := E) G d A h e start B (i+1) z).1 <
        affineDimension (physicalStateAt (E := E) G d A h e start B i z).1)
    (hex : ∀ i ≤ r, ∀ z, Ex i (physicalStateAt (E := E) G d A h e start B i z).1 →
      (G.points.filter (PointOn (physicalStateAt (E := E) G d A h e start B i z).1)).card ≤ T) :
    G.points.card ≤ 2*(∑ i ∈ Finset.range (r+1), L.length * ∏ j ∈ Finset.range i,
      if hj : j < r then physicalBranchAllowance n d A h e B M
        (fun k => ⌊ξ*(B k).card⌋₊) (fun k => r-k.val) ⟨j,hj⟩ else 1) * T := by
  classical
  let S := Finset.univ.filter (PhysicalRegular (E := E) G d A h e r start B ξ)
  have hS (z) (hz : z ∈ S) : PhysicalRegular (E := E) G d A h e r start B ξ z :=
    (Finset.mem_filter.mp hz).2
  have hc := physical_stagewise_stopped_count G d A h e start hs B S M
    (fun k => ⌊ξ*(B k).card⌋₊) L T Ex (fun z _ => hstart z) hT (fun z _ => hroot z)
    hM hprime hupper
    (fun i z hz => (Nat.le_floor_iff (mul_nonneg hξ (Nat.cast_nonneg _))).mpr
      (PhysicalRegular.bad_minor G d A h e r start B ξ z (hS z hz) i.val i.isLt.le i))
    (fun i hi z hz => hcut i hi z (hS z hz)) (fun i hi z _ => hex i hi z)
  have hhalf' : G.points.card ≤ 2*S.card := by
    have hh : (G.points.card : ℝ) ≤ 2*(S.card : ℝ) := by linarith
    exact_mod_cast hh
  exact hhalf'.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hc)

end

open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

theorem physical_branch_power_bound {r : ℕ} (n : ℕ) (d : ℕ → ℕ) (A h e : ℕ)
    (U : Fin r → ℕ) (q : Fin r → ℕ) (K ξ : ℝ) (hK : 1 ≤ K) (hξ : 0 ≤ ξ) :
    ∃ C : Fin r → ℝ, (∀ i, 1 ≤ C i) ∧
    ∀ X ζ : ℝ, 1 ≤ X → 0 ≤ ζ → ∀ (B : Fin r → Finset ℕ) (M : Fin r → ℕ),
      (∀ i, (B i).card ≤ U i) → (∀ i, (M i : ℝ) ≤ K*X^ζ) →
      ∀ i, (physicalBranchAllowance n d A h e B M (fun k => ⌊ξ*(B k).card⌋₊) q i : ℝ) ≤
        C i*X^(ζ*((q i:ℝ)*(U i:ℝ)+(n:ℝ)*ξ*(U i:ℝ))) := by
  classical
  let F := fun i : Fin r => kernelCountBudget (d i.val) h (pathDegreeBudget n d A h e i.val) *
    patchCountBudget n A h (kernelDegreeBudget (d i.val) h (pathDegreeBudget n d A h e i.val))
  let m := fun i : Fin r => q i*U i+n*⌊ξ*U i⌋₊
  let C := fun i : Fin r => max 1 ((2:ℝ)^(U i)*(((pathDegreeBudget n d A h e i.val+1:ℕ):ℝ)^n)^(U i)*
    K^(m i)*(F i:ℝ))
  refine ⟨C,fun i => le_max_left _ _,?_⟩
  intro X ζ hX hζ B M hU hM i
  have hxc : 1 ≤ K*X^ζ := one_le_mul_of_one_le_of_one_le hK (Real.one_le_rpow hX hζ)
  have hm : q i*(B i).card+n*⌊ξ*(B i).card⌋₊ ≤ m i := by
    apply Nat.add_le_add (Nat.mul_le_mul_left _ (hU i))
    apply Nat.mul_le_mul_left
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hU i) hξ
  have hpow : (M i:ℝ)^(q i*(B i).card+n*⌊ξ*(B i).card⌋₊) ≤ (K*X^ζ)^(m i) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (hM i) _).trans (pow_le_pow_right₀ hxc hm)
  have he : ζ*(m i:ℝ) ≤ ζ*((q i:ℝ)*(U i:ℝ)+(n:ℝ)*ξ*(U i:ℝ)) := by
    have hh := Nat.floor_le (mul_nonneg hξ (Nat.cast_nonneg (U i)))
    dsimp only [m]
    push_cast
    apply mul_le_mul_of_nonneg_left _ hζ
    calc
      _ ≤ (q i:ℝ)*U i+n*(ξ*U i) := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n))
      _ = _ := by ring
  have hdeg : 1 ≤ ((pathDegreeBudget n d A h e i.val+1:ℕ):ℝ)^n := by
    apply one_le_pow₀
    exact_mod_cast Nat.le_add_left 1 _
  calc
    _ = (2:ℝ)^(B i).card * (((pathDegreeBudget n d A h e i.val+1:ℕ):ℝ)^n)^(B i).card *
      (M i:ℝ)^(q i*(B i).card+n*⌊ξ*(B i).card⌋₊) * (F i:ℝ) := by
        simp only [physicalBranchAllowance,F,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    _ ≤ (2:ℝ)^(U i) * (((pathDegreeBudget n d A h e i.val+1:ℕ):ℝ)^n)^(U i) *
      (K*X^ζ)^(m i) * (F i:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        apply mul_le_mul _ hpow (pow_nonneg (Nat.cast_nonneg _) _) (by positivity)
        exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (hU i))
          (pow_le_pow_right₀ hdeg (hU i)) (by positivity) (by positivity)
    _ = ((2:ℝ)^(U i) * (((pathDegreeBudget n d A h e i.val+1:ℕ):ℝ)^n)^(U i) *
      K^(m i)*(F i:ℝ))*X^(ζ*(m i:ℝ)) := by
        rw [mul_pow,← Real.rpow_mul_natCast (zero_le_one.trans hX)]
        ring
    _ ≤ C i*X^(ζ*(m i:ℝ)) := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (zero_le_one.trans hX) _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX he)
      ((le_max_left _ _ : (1:ℝ) ≤ C i).trans' zero_le_one)

theorem stopped_forest_power_bound {r : ℕ} (L : ℕ) (b : Fin r → ℕ)
    (C κ : Fin r → ℝ) (hC : ∀ i, 1 ≤ C i) (hκ : ∀ i, 0 ≤ κ i)
    (X : ℝ) (hX : 1 ≤ X) (hb : ∀ i, (b i : ℝ) ≤ C i*X^(κ i)) :
    ((∑ i ∈ Finset.range (r+1), L * ∏ j ∈ Finset.range i,
      if hj : j < r then b ⟨j,hj⟩ else 1 : ℕ):ℝ) ≤
      (r+1:ℕ)*(L:ℝ)*(∏ j, C j)*X^(∑ j, κ j) := by
  classical
  let F : ℕ → ℝ := fun j => if hj : j < r then C ⟨j,hj⟩*X^(κ ⟨j,hj⟩) else 1
  have hF : ∀ j, 1 ≤ F j := by
    intro j
    dsimp only [F]
    split_ifs with hj
    · exact one_le_mul_of_one_le_of_one_le (hC ⟨j,hj⟩) (Real.one_le_rpow hX (hκ ⟨j,hj⟩))
    · rfl
  have hprod (i : ℕ) (hi : i ≤ r) :
      ((∏ j ∈ Finset.range i, if hj : j < r then b ⟨j,hj⟩ else 1 : ℕ):ℝ) ≤
        (∏ j, C j)*X^(∑ j, κ j) := by
    calc
      _ ≤ ∏ j ∈ Finset.range i, F j := by
        rw [Nat.cast_prod]
        apply Finset.prod_le_prod
        · intro j _; exact Nat.cast_nonneg _
        · intro j _
          dsimp only [F]
          split_ifs with hj
          · exact hb ⟨j,hj⟩
          · norm_num
      _ ≤ ∏ j ∈ Finset.range r, F j :=
        Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono hi)
          (fun j _ => zero_le_one.trans (hF j)) (fun j _ _ => hF j)
      _ = ∏ j : Fin r, C j*X^(κ j) := by
        rw [← Fin.prod_univ_eq_prod_range]
        simp [F]
      _ = _ := by rw [Finset.prod_mul_distrib,Real.rpow_sum_of_pos (zero_lt_one.trans_le hX)]
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _i ∈ Finset.range (r+1), (L:ℝ)*((∏ j, C j)*X^(∑ j, κ j)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left (hprod i (by have := Finset.mem_range.mp hi; omega)) (Nat.cast_nonneg _)
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_AffineCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

theorem physical_regular_half_blocks (n r E A h e : ℕ) (hr : 0 < r) (d : ℕ → ℕ)
    (a : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i) (γ ξ w : ℝ)
    (hγ : 0 < γ) (hξ : 0 < ξ) (hw : 0 ≤ w) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∃ U : Fin r → ℕ, (∀ i, ζ*(U i:ℝ) ≤ a i+2*γ) ∧
    ∃ K X₀ : ℝ, 1 ≤ K ∧ ∀ X : ℝ, X₀ < X →
      ∀ (G : KernelGeometry n), G.height ≤ X^w →
      ∀ (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n),
      (∀ z, PhysicalState G h e z.val (start z)) →
    ∃ B : Fin r → Finset ℕ,
      (∀ i, (B i).card ≤ U i ∧ a i+γ ≤ ζ*((B i).card:ℝ)) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i p, p ∈ B i → p.Prime ∧ X^ζ ≤ (p:ℝ) ∧ (p:ℝ) ≤ K*X^ζ) ∧
      (G.points.card:ℝ)/2 ≤ (Finset.univ.filter
        (PhysicalRegular (E := E) G d A h e r start B ξ)).card := by
  classical
  obtain ⟨C,hC,b,hblocks⟩ := physical_regular_blocks n d A h e r E
  let η := ξ/(4*r)
  have hη : 0 < η := div_pos hξ (by exact_mod_cast (show 0 < 4*r by omega))
  let V : ℕ := ((E+n).choose n+1)^r
  obtain ⟨T,hTlarge⟩ := exists_nat_gt (2*(V:ℝ)/η)
  have hT : 0 < T := by
    have : (0:ℝ) < T := lt_of_le_of_lt (div_nonneg (by positivity) hη.le) hTlarge
    exact_mod_cast this
  have hVT : (V:ℝ)/T ≤ η/2 := by
    have htc : (0:ℝ) < T := by exact_mod_cast hT
    apply (div_le_iff₀ htc).mpr
    have hh := (div_lt_iff₀ hη).mp hTlarge
    nlinarith
  let ζ := γ/((T:ℝ)+1)
  have hζ : 0 < ζ := div_pos hγ (by positivity)
  have hζT : ζ*T ≤ γ := by
    have he : ζ*((T:ℝ)+1) = γ := div_mul_cancel₀ _ (by positivity)
    nlinarith
  let ell := fun i => ⌊(a i+γ)/ζ⌋₊
  let U := fun i => ell i+T
  have hU (i) : ζ*(U i:ℝ) ≤ a i+2*γ :=
    (physical_block_width (a i) γ ζ T (U i) (ha i) hγ hζ hζT (by dsimp [U,ell]; omega) le_rfl).2
  let v : ℕ := ⌊((w*b+1)*(r+1:ℕ))/ζ⌋₊
  obtain ⟨N,hN⟩ := exists_nat_gt (2*(v:ℝ)/η)
  let t : ℕ := (∑ i, ell i)+T+N+1
  have hsize (i) : ell i+T < t := by
    have he : ell i ≤ ∑ j, ell j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    dsimp [t]
    omega
  have hbound (i) : (v:ℝ)/((t:ℝ)-(ell i+T)) ≤ η/2 := by
    have hp : (0:ℝ) < (t:ℝ)-(ell i+T) := by
      have hh : (ell i:ℝ)+T < t := by exact_mod_cast hsize i
      linarith
    have he : (ell i:ℝ) ≤ ∑ j, (ell j:ℝ) :=
      Finset.single_le_sum (fun j _ => Nat.cast_nonneg _) (Finset.mem_univ i)
    have ht : (t:ℝ) = (∑ j, (ell j:ℝ))+T+N+1 := by simp [t]
    have hn := (div_lt_iff₀ hη).mp hN
    apply (div_le_iff₀ hp).mpr
    nlinarith
  refine ⟨ζ,hζ,U,hU,2^(r*t+1),max 1 C,one_le_pow₀ (by norm_num),?_⟩
  intro X hX G hheight start hs
  have hX1 : 1 < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hCX : C ≤ X := (le_max_right _ _).trans hX.le
  have hxζ : 1 ≤ X^ζ := Real.one_le_rpow hX1.le hζ.le
  obtain ⟨P,hPcard,hPdisj,hP⟩ := disjoint_prime_pools r t (X^ζ) hxζ
  obtain ⟨B,hB,hreg⟩ := hblocks G start hs r P ell T X ζ w η ξ hX1 hCX hw hheight hζ hξ
    (fun i p hp => (hP i p hp).1) (fun i p hp => (hP i p hp).2.1) hT
    (fun i => by rw [hPcard]; exact hsize i)
    (fun i => by rw [hPcard]; exact add_le_add hVT (hbound i) |>.trans_eq (by ring))
  refine ⟨B,?_,?_,?_,?_⟩
  · intro i
    refine ⟨(hB i).2.2,?_⟩
    exact (physical_block_width (a i) γ ζ T (B i).card (ha i) hγ hζ hζT
      (hB i).2.1 (hB i).2.2).1
  · intro i j hij
    exact (hPdisj i j hij).mono (hB i).1 (hB j).1
  · intro i p hp
    exact hP i p ((hB i).1 hp)
  · have he : 1-(r:ℝ)*η/ξ = 3/4 := by
      dsimp only [η]
      have hrc : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      field_simp
      ring
    change (G.points.card:ℝ)/2 ≤ _
    have hr' : (3/4:ℝ)*G.points.card ≤
        (Finset.univ.filter (PhysicalRegular (E := E) G d A h e r start B ξ)).card := by
      unfold PhysicalRegular physicalPathProduct
      rw [he] at hreg
      convert hreg using 1
      congr 1
      congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    linarith [show (0:ℝ) ≤ G.points.card from Nat.cast_nonneg _]

end

open scoped BigOperators

theorem physical_small_parameters {r : ℕ} (n : ℕ) (a : Fin r → ℝ) (q : Fin r → ℕ)
    (ha : ∀ i, 0 ≤ a i) (ε : ℝ) (hε : 0 < ε) :
    ∃ γ ξ : ℝ, 0 < γ ∧ 0 < ξ ∧ ξ ≤ 1 ∧
      ξ*((∑ i, a i)+(r:ℝ)*γ) ≤ γ/2 ∧
      (∑ i, (a i+2*γ)*((q i:ℝ)+(n:ℝ)*ξ)) ≤ (∑ i, (q i:ℝ)*a i)+ε/2 := by
  classical
  let A := ∑ i, a i
  let Q := ∑ i, (q i:ℝ)
  let B := 2*Q+n*A+2*(n:ℝ)*r+1
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => ha i)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  have hB : 0 < B := by dsimp only [B]; positivity
  let γ := min 1 (ε/(4*B))
  have hγ : 0 < γ := lt_min zero_lt_one (div_pos hε (by positivity))
  have hγ1 : γ ≤ 1 := min_le_left _ _
  have hγB : γ*B ≤ ε/4 := by
    have hh : γ ≤ ε/(4*B) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 4*B)).mp hh
    linarith
  let D := A+(r:ℝ)*γ+1
  have hD : 0 < D := by dsimp only [D]; positivity
  let ξ := min γ (γ/(4*D))
  have hξ : 0 < ξ := lt_min hγ (div_pos hγ (by positivity))
  have hξγ : ξ ≤ γ := min_le_left _ _
  have hξ1 : ξ ≤ 1 := hξγ.trans hγ1
  have hξD : ξ*D ≤ γ/4 := by
    have hh : ξ ≤ γ/(4*D) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 4*D)).mp hh
    linarith
  refine ⟨γ,ξ,hγ,hξ,hξ1,?_,?_⟩
  · change ξ*(A+(r:ℝ)*γ) ≤ γ/2
    dsimp only [D] at hξD
    nlinarith
  · have he : (∑ i, (a i+2*γ)*((q i:ℝ)+(n:ℝ)*ξ)) =
        (∑ i, (q i:ℝ)*a i)+2*γ*Q+(n:ℝ)*ξ*A+2*γ*(n:ℝ)*ξ*r := by
      calc
        _ = ∑ i, ((q i:ℝ)*a i+2*γ*(q i:ℝ)+(n:ℝ)*ξ*a i+2*γ*(n:ℝ)*ξ) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, A, Q]
          ring
    have ha' : (n:ℝ)*ξ*A ≤ (n:ℝ)*γ*A := by gcongr
    have hr' : 2*γ*(n:ℝ)*ξ*r ≤ 2*γ*(n:ℝ)*r := by
      calc
        _ ≤ 2*γ*(n:ℝ)*1*r := by gcongr
        _ = _ := by ring
    rw [he]
    dsimp only [B] at hγB
    nlinarith

open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

theorem physical_affine_count_oai (n r A e₀ : ℕ) (hr : 0 < r)
    (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j) (Cbox w : ℝ) (hCbox : 1 ≤ Cbox) (hw : 0 ≤ w)
    (a δ : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i) (hδ : ∀ i, 0 < δ i)
    (hprefix : ∀ i, δ i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin r => j.val ≤ i.val), a j)
    (ε : ℝ) (hε : 0 < ε) (c Kex : ℕ → ℝ) (hc : ∀ e, 0 ≤ c e) (hKex : ∀ e, 1 ≤ Kex e) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X →
      ∀ (G : KernelGeometry n), G.height ≤ X^w →
        (∀ z ∈ G.points, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime →
        affineDimension I ≤ r → affineDegree I ≤ e₀ →
        (∀ z ∈ G.points, PointOn I z) →
        (∀ (i : Fin r) (e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
          I ≤ J → EquationLock J G.points A → affineDegree J ≤ e →
          affineDimension J = r-i.val → (∃ z ∈ G.points, PointOn J z) →
          ((G.points.filter (PointOn J)).card:ℝ) ≤ Kex e*X^(ε/4) ∨
          ∀ T : ℝ, 1 ≤ T → T^(r-i.val) / (((r-i.val).factorial:ℝ)*(δ i)^(r-i.val)) -
            c e*T^(r-i.val-1) ≤ weightedHilbert J ω T) →
        (G.points.card:ℝ) ≤ C*X^((∑ i, ((r-i.val:ℕ):ℝ)*a i)+ε) := by
  classical
  let q := fun i : Fin r => r-i.val
  obtain ⟨γ,ξ,hγ,hξ,hξ1,hloss,hexponent⟩ := physical_small_parameters n a q ha ε hε
  choose D Xcut hcut using fun (i : Fin r) (e : ℕ) => physical_weighted_descent ω hω
    (q i) (by dsimp [q]; omega) (δ i) (γ/2) (c e) Cbox (hδ i) (by linarith) (hc e) hCbox
  let chooseD : ℕ → ℕ → ℕ := fun i e => if hi : i < r then D ⟨i,hi⟩ e else 1
  let e := patchDegreeBudget n A r e₀
  obtain ⟨d,E,hd⟩ := physical_degree_schedule n A r e r chooseD
  let ed := fun i : Fin r => pathDegreeBudget n d A r e i.val
  have hd' (i : Fin r) : D i (ed i) ≤ d i.val ∧ d i.val ≤ E := by
    have hh := hd i.val i.isLt
    refine ⟨?_,hh.2⟩
    simpa only [chooseD,dite_eq_left i.isLt,ed] using hh.1.ge
  obtain ⟨ζ,hζ,U,hUwidth,K,Xpool,hK,hblocks⟩ :=
    physical_regular_half_blocks n r E A r e hr d a ha γ ξ w hγ hξ hw
  obtain ⟨Cb,hCb,hbranch⟩ := physical_branch_power_bound n d A r e U q (K+1) ξ
    (by linarith) hξ.le
  let Ke := 1+∑ i, Kex (ed i)
  have hKe : 1 ≤ Ke := by
    dsimp only [Ke]
    linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => zero_le_one.trans (hKex (ed i)))]
  have hKei (i) : Kex (ed i) ≤ Ke := by
    have hh := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => zero_le_one.trans (hKex (ed j))) (Finset.mem_univ i)
    dsimp only [Ke]
    linarith
  let Lmax := patchCountBudget n A r e₀
  have hCbprod : 0 ≤ ∏ i, Cb i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (hCb i))
  let C := 2*((r+1:ℕ):ℝ)*(Lmax+1)*(∏ i, Cb i)*(Ke+1)
  have hC : 0 < C := by
    dsimp only [C]
    have hp : 0 < ∏ i, Cb i := Finset.prod_pos (fun i _ => zero_lt_one.trans_le (hCb i))
    positivity
  refine ⟨C,max (max 2 Xpool) (∑ i, |Xcut i (ed i)|),hC,?_⟩
  intro X hX G hheight hbox I hI hdim hdeg hG hAlt
  let : I.IsPrime := hI
  have hX2 : 2 < X := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hX
  have hX1 : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hXp : Xpool < X := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hX
  have hXc (i : Fin r) : Xcut i (ed i) < X := lt_of_le_of_lt
    ((le_abs_self _).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (Xcut j (ed j)))
      (Finset.mem_univ i)).trans (le_max_right _ _))) hX
  obtain ⟨L,hL,start,hs⟩ := physical_initial_context G A r e₀ I hdim hdeg hG
  have hs' : ∀ z, PhysicalState G r e z.val (start z) := fun z => (hs z).2.1
  obtain ⟨B,hB,hdisj,hprime,hhalf⟩ := hblocks X hXp G hheight start hs'
  let M : Fin r → ℕ := fun _ => ⌈K*X^ζ⌉₊
  have hMx : 1 ≤ K*X^ζ := one_le_mul_of_one_le_of_one_le hK (Real.one_le_rpow hX1 hζ.le)
  have hM (i) : 1 ≤ M i := by
    have hh := (Nat.le_ceil (K*X^ζ)).trans' hMx
    exact_mod_cast hh
  have hMp (i) (p : ℕ) (hp : p ∈ B i) : p ≤ M i := by
    have hh := (hprime i p hp).2.2.trans (Nat.le_ceil (K*X^ζ))
    exact_mod_cast hh
  have hMb (i) : (M i:ℝ) ≤ (K+1)*X^ζ := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ K*X^ζ by linarith)
    have hx := Real.one_le_rpow hX1 hζ.le
    dsimp only [M]
    nlinarith
  let T := ⌈Ke*X^(ε/4)⌉₊
  have hTx : 1 ≤ Ke*X^(ε/4) := one_le_mul_of_one_le_of_one_le hKe
    (Real.one_le_rpow hX1 (by linarith))
  have hT : 1 ≤ T := by
    have hh := hTx.trans (Nat.le_ceil (Ke*X^(ε/4)))
    exact_mod_cast hh
  have hTb : (T:ℝ) ≤ (Ke+1)*X^(ε/4) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ Ke*X^(ε/4) by linarith)
    have hx := Real.one_le_rpow hX1 (show 0 ≤ ε/4 by linarith)
    dsimp only [T]
    nlinarith
  let Ex : ℕ → Ideal (MvPolynomial (Fin n) ℂ) → Prop := fun _ J =>
    (G.points.filter (PointOn J)).card ≤ T
  have hmargin := physical_cumulative_margin a δ (fun i => (B i).card) γ ζ ξ ha hγ hξ.le hξ1
    hloss (fun i => (hB i).2) hprefix
  have hdesc (i : ℕ) (hi : i < r) (z : G.points)
      (hz : PhysicalRegular (E := E) G d A r e r start B ξ z)
      (hne : ¬ Ex i (physicalStateAt (E := E) G d A r e start B i z).1)
      (hdi : affineDimension (physicalStateAt (E := E) G d A r e start B i z).1 = r-i) :
      affineDimension (physicalStateAt (E := E) G d A r e start B (i+1) z).1 <
        affineDimension (physicalStateAt (E := E) G d A r e start B i z).1 := by
    let ii : Fin r := ⟨i,hi⟩
    let s := physicalStateAt (E := E) G d A r e start B i z
    have hstate := physicalStateAt_good (E := E) G d A r e start hs' B i z
    have hcontext := physicalStateAt_context (E := E) G d A r e start hs' B I
      (fun z => ⟨(hs z).2.2.1,(hs z).2.2.2⟩) i z
    have hH : ∀ T' : ℝ, 1 ≤ T' → T'^(q ii)/(((q ii).factorial:ℝ)*(δ ii)^(q ii)) -
        c (ed ii)*T'^(q ii-1) ≤ weightedHilbert s.1 ω T' := by
      rcases hAlt ii (ed ii) s.1 hstate.1.1 hcontext.1 hcontext.2 hstate.1.2.2 hdi
        ⟨z.val,z.property,hstate.2.2.2.1⟩ with hsmall | hH
      · apply False.elim
        apply hne
        have hh : ((G.points.filter (PointOn s.1)).card:ℝ) ≤ (T:ℝ) := hsmall.trans
          ((mul_le_mul_of_nonneg_right (hKei ii) (Real.rpow_nonneg hXpos.le _)).trans (Nat.le_ceil _))
        exact_mod_cast hh
      · exact hH
    let Q := (cumulativeBlockPrimes B i).filter (fun p : ℕ => ¬ (p:ℤ) ∣ eval z.val s.2.minor)
    have hprod : X^(δ ii+γ/2) ≤ ∏ p ∈ Q, (p:ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hX1 (hmargin ii)).trans
        (cumulative_good_prime_product B hdisj i (eval z.val s.2.minor) X ζ ξ hX1 hζ.le
          (fun j p hp => (hprime j p hp).2.1)
          (fun j => PhysicalRegular.bad_minor G d A r e r start B ξ z hz i hi.le j))
    rw [physicalStateAt_succ]
    apply hcut ii (ed ii) X (hXc ii) r E G d A r e i (hd' ii).1 (hd' ii).2 hbox
      z.val z.property s hstate hdi hH B Q (Finset.filter_subset _ _)
    · intro p hp
      obtain ⟨j,_,hpj⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hp).1
      exact (hprime j p hpj).1
    · intro p hp; exact (Finset.mem_filter.mp hp).2
    · exact hprod
  have hcount := physical_regular_count G d A r e start hs' B M ξ hξ.le L T Ex
    (fun z => (hs z).1) hT (fun z => (hs' z).1.2.1) hM
    (fun i p hp => (hprime i p hp).1) hMp hhalf hdesc (fun _ _ _ hh => hh)
  let κ := fun i : Fin r => ζ*((q i:ℝ)*(U i:ℝ)+(n:ℝ)*ξ*(U i:ℝ))
  have hκ (i) : 0 ≤ κ i := by dsimp [κ]; positivity
  have hsum : ∑ i, κ i ≤ (∑ i, (q i:ℝ)*a i)+ε/2 := by
    apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) hexponent
    dsimp only [κ]
    calc
      _ = (ζ*(U i:ℝ))*((q i:ℝ)+(n:ℝ)*ξ) := by ring
      _ ≤ (a i+2*γ)*((q i:ℝ)+(n:ℝ)*ξ) :=
        mul_le_mul_of_nonneg_right (hUwidth i) (by positivity)
  have hforest := stopped_forest_power_bound L.length
    (physicalBranchAllowance n d A r e B M (fun k => ⌊ξ*(B k).card⌋₊) q)
    Cb κ hCb hκ X hX1 (hbranch X ζ hX1 hζ.le B M (fun i => (hB i).1) hMb)
  have hcount' : (G.points.card:ℝ) ≤ 2*((r+1:ℕ):ℝ)*L.length*(∏ i, Cb i)*
      X^(∑ i, κ i)*((Ke+1)*X^(ε/4)) := by
    have hh : (G.points.card:ℝ) ≤ 2*((∑ i ∈ Finset.range (r+1), L.length * ∏ j ∈ Finset.range i,
      if hj : j < r then physicalBranchAllowance n d A r e B M
        (fun k => ⌊ξ*(B k).card⌋₊) q ⟨j,hj⟩ else 1 : ℕ):ℝ)*(T:ℝ) := by
      exact_mod_cast hcount
    apply hh.trans
    have hh' := mul_le_mul (mul_le_mul_of_nonneg_left hforest (by norm_num : (0:ℝ) ≤ 2)) hTb
      (Nat.cast_nonneg T) (by positivity)
    convert hh' using 1; ring
  calc
    (G.points.card:ℝ) ≤ 2*((r+1:ℕ):ℝ)*L.length*(∏ i, Cb i)*(Ke+1)*X^((∑ i, κ i)+ε/4) := by
      rw [Real.rpow_add hXpos]
      convert hcount' using 1; ring
    _ ≤ C*X^((∑ i, κ i)+ε/4) := by
      have hL' : (L.length:ℝ) ≤ (Lmax:ℝ)+1 := by exact_mod_cast (hL.trans (Nat.le_succ Lmax))
      dsimp only [C]
      gcongr
    _ ≤ C*X^((∑ i, ((r-i.val:ℕ):ℝ)*a i)+ε) := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX1 ?_) hC.le
      dsimp only [q] at hsum
      linarith

end QuarticPowerFree

end OAI
end

theorem solution : type_of% @OAI.QuarticPowerFree.physical_affine_count_oai := @OAI.QuarticPowerFree.physical_affine_count_oai
