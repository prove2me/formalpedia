-- Prove2me | solution 1 for L0BnB.Duality.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T10:07:18.484825+00:00
-- url     : https://prove2.me/submissions/213647c6-e091-4013-b20c-75005942bf28

/-
Equation24 dual attainment for the small-box sparse-regression relaxation.
Original mathematics: Hazimeh, Mazumder and Saab, arXiv2004.06152v2,
Theorem2 pp.13-14, Equation24 and its omitted analogous proof on p.31.
mikedeng1 supplied the platform definitions and corrected explicit hypotheses.
Alexander Richard Towell(queelius) directed the work; OpenAI Codex supplied
substantial formalization, independent exact-type extraction and verification.
New argument: coordinate quadratic expansion, feasible convex interpolation,
one-sided linearization at zero, explicit scalar dual certificates and exact
least-squares equality. No accepted theorem bodies are imported or assumed.
Prior checked Equation45/47 and weak-duality work informed the route; those
contributions retain their separate authors and credit. Lean/Mathlib supplies
finite sums, topology, real algebra and library foundations.
No mathematical novelty or independent human review claimed.
-/
import Mathlib
import Definitions.Def_L0BnB_Duality_Dual
open L0BnB.Reduced L0BnB.Duality Filter
open scoped Topology
namespace SparseAttainment

lemma linear_min_of_quadratic (q a c M x : ℝ) (hc : 0 ≤ c) (hx : |x| ≤ M)
    (h : ∀ b, |b| ≤ M → 0 ≤ q*(b-x)^2+a*(b-x)+c*(|b|-|x|)) :
    ∀ b, |b| ≤ M → c*|x|+a*x ≤ c*|b|+a*b := by
  intro b hb
  let H := a*(b-x)+c*(|b|-|x|)
  have ht (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) : 0 ≤ q*t*(b-x)^2+H := by
    let z := (1-t)*x+t*b
    have hzabs : |z| ≤ (1-t)*|x|+t*|b| := by
      calc |z| ≤ |(1-t)*x|+|t*b| := abs_add_le _ _
        _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg (by linarith : 0 ≤ 1-t),abs_of_pos ht0]
    have hz : |z| ≤ M := by
      have h1 := mul_le_mul_of_nonneg_left hx (by linarith : 0 ≤ 1-t)
      have h2 := mul_le_mul_of_nonneg_left hb ht0.le
      nlinarith
    have hh := h z hz
    have he : z-x=t*(b-x) := by dsimp [z];ring
    rw [he] at hh
    have hh2 := mul_le_mul_of_nonneg_left hzabs hc
    have hprod : 0 ≤ t*(q*t*(b-x)^2+H) := by dsimp [H]; nlinarith
    exact nonneg_of_mul_nonneg_right hprod ht0
  have hlim : Tendsto (fun t : ℝ => q*t*(b-x)^2+H) (𝓝[>] 0) (𝓝 H) := by
    have hc' : Continuous (fun t : ℝ => q*t*(b-x)^2+H) := by fun_prop
    have hh : Tendsto (fun t : ℝ => q*t*(b-x)^2+H) (𝓝 (0:ℝ)) (𝓝 (q*0*(b-x)^2+H)) := hc'.continuousAt
    simpa using hh.mono_left nhdsWithin_le_nhds
  have hH : 0 ≤ H := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with t ht0 ht1
    exact ht t ht0 ht1
  dsimp [H] at hH
  linarith

lemma scalar_certificate (a c M x : ℝ) (hc : 0 ≤ c) (hM : 0 < M) (hx : |x| ≤ M)
    (hmin : ∀ b, |b| ≤ M → c*|x|+a*x ≤ c*|b|+a*b) :
    let μ := if |x|=M then |a|-c else 0
    |a|-μ ≤ c ∧ c*|x|+a*x = -M*|μ| := by
  dsimp
  have hz := hmin 0 (by simpa using hM.le)
  simp only [abs_zero,mul_zero,add_zero] at hz
  have ha : -(|a| * |x|) ≤ a*x := by simpa only [abs_mul] using neg_abs_le (a*x)
  by_cases hca : |a| ≤ c
  · have hm := mul_nonneg (sub_nonneg.mpr hca) (abs_nonneg x)
    have he : c*|x|+a*x=0 := by nlinarith
    by_cases hb : |x|=M
    · have hac : |a|=c := by rw [hb] at he ha; nlinarith
      rw [if_pos hb,hac,sub_self,abs_zero,mul_zero,he]
      exact ⟨by linarith,by ring⟩
    · rw [if_neg hb,sub_zero,abs_zero,mul_zero,he]
      exact ⟨hca,by ring⟩
  · have hlt : c < |a| := not_le.mp hca
    have hane : a ≠ 0 := by intro he; rw [he,abs_zero] at hlt; linarith
    have hab : |-M*Real.sign a|=M := by
      rcases lt_or_gt_of_ne hane with ha | ha
      · rw [Real.sign_of_neg ha];simp [abs_of_pos hM]
      · rw [Real.sign_of_pos ha];simp [abs_of_pos hM]
    have ham : a*(-M*Real.sign a) = -|a| * M := by
      rcases lt_or_gt_of_ne hane with ha | ha
      · rw [Real.sign_of_neg ha,abs_of_neg ha];ring
      · rw [Real.sign_of_pos ha,abs_of_pos ha];ring
    have hu := hmin (-M*Real.sign a) (by rw [hab])
    rw [hab,ham] at hu
    have hb : |x|=M := by nlinarith
    rw [if_pos hb,abs_of_pos (sub_pos.mpr hlt)]
    constructor
    · linarith
    · rw [hb] at ha ⊢;nlinarith

lemma sum_update {p : ℕ} (g : Fin p → ℝ → ℝ) (β : Fin p → ℝ) (i : Fin p) (b : ℝ) :
    (∑ j, g j (Function.update β i b j)) = (∑ j, g j (β j))+g i b-g i (β i) := by
  simp only [Function.apply_update]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),Finset.sdiff_singleton_eq_erase]
  have h := Finset.sum_erase_add (Finset.univ) (fun j => g j (β j)) (Finset.mem_univ i)
  linarith

lemma loss_update {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (β : Fin p → ℝ) (i : Fin p) (b : ℝ) :
    lsLoss X y (Function.update β i b) = lsLoss X y β +
      colDot X (rhoStar X y β) i*(b-β i)+(1/2)*(∑ r, (X r i)^2)*(b-β i)^2 := by
  have hv (r : Fin n) : Matrix.mulVec X (Function.update β i b) r = Matrix.mulVec X β r+X r i*(b-β i) := by
    unfold Matrix.mulVec dotProduct
    rw [sum_update (fun j v => X r j*v) β i b]
    ring
  unfold lsLoss colDot rhoStar rStar
  simp only [hv]
  have he : (∑ r, (y r-(Matrix.mulVec X β r+X r i*(b-β i)))^2) =
      (∑ r, (y r-Matrix.mulVec X β r)^2)+
      2*(∑ r, -(y r-Matrix.mulVec X β r)*X r i)*(b-β i)+
      (∑ r, (X r i)^2)*(b-β i)^2 := by
    simp only [Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [he]
  ring

lemma loss_identity {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (β : Fin p → ℝ) :
    -(1/2)*(∑ r, (rhoStar X y β r)^2)-(∑ r, rhoStar X y β r*y r)+
      (∑ i, colDot X (rhoStar X y β) i*β i) = lsLoss X y β := by
  have hs : (∑ i, colDot X (rhoStar X y β) i*β i) = ∑ r, rhoStar X y β r*Matrix.mulVec X β r := by
    simp only [colDot,Matrix.mulVec,dotProduct,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl;intro r hr
    apply Finset.sum_congr rfl;intro i hi;ring
  rw [hs]
  unfold lsLoss
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  unfold rhoStar rStar
  ring

end SparseAttainment

theorem smallbox_attainment {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hreg : M < Real.sqrt (lam0 / lam2))
    (βs : Fin p → ℝ) (hβs : βs ∈ L0BnB.Reduced.box p M)
    (hopt : ∀ β ∈ L0BnB.Reduced.box p M, F X y lam0 lam2 M βs ≤ F X y lam0 lam2 M β) :
    Feas22 X lam0 lam2 M (rhoStar X y βs) (muStar X y lam0 lam2 M βs) ∧
      h2 y M (rhoStar X y βs) (muStar X y lam0 lam2 M βs) = F X y lam0 lam2 M βs := by
  let c := lam0/M+lam2*M
  have hc : 0 ≤ c := by dsimp [c];positivity
  have hF (β : Fin p → ℝ) : F X y lam0 lam2 M β = lsLoss X y β+∑ i, c*|β i| := by
    simp only [F,psi,if_neg (not_le.mpr hreg),psi2,c]
  have hcoord (i : Fin p) :
      |colDot X (rhoStar X y βs) i|-muStar X y lam0 lam2 M βs i ≤ c ∧
      c*|βs i|+colDot X (rhoStar X y βs) i*βs i = -M*|muStar X y lam0 lam2 M βs i| := by
    have hquad (b : ℝ) (hb : |b| ≤ M) :
        0 ≤ ((1/2)*(∑ r, (X r i)^2))*(b-βs i)^2+
          colDot X (rhoStar X y βs) i*(b-βs i)+c*(|b|-|βs i|) := by
      have hbox : Function.update βs i b ∈ box p M := by
        intro j
        by_cases hj : j=i
        · subst j;simpa using hb
        · simpa [Function.update_of_ne hj] using hβs j
      have hh := hopt _ hbox
      rw [hF βs,hF (Function.update βs i b),SparseAttainment.loss_update,
        SparseAttainment.sum_update (fun _ x => c*|x|)] at hh
      linarith
    have hl := SparseAttainment.linear_min_of_quadratic
      ((1/2)*(∑ r, (X r i)^2)) (colDot X (rhoStar X y βs) i) c M (βs i) hc (hβs i) hquad
    have hm : muStar X y lam0 lam2 M βs i =
        (if |βs i|=M then |colDot X (rhoStar X y βs) i|-c else 0) := by
      unfold muStar
      split_ifs <;> dsimp [c] <;> ring
    have hh := SparseAttainment.scalar_certificate _ c M (βs i) hc hM (hβs i) hl
    dsimp at hh
    rwa [← hm] at hh
  constructor
  · intro i;exact (hcoord i).1
  · have he : (∑ i, (c * |βs i| + colDot X (rhoStar X y βs) i * βs i)) =
        ∑ i, (-M * |muStar X y lam0 lam2 M βs i|) :=
      Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => (hcoord i).2)
    simp only [Finset.sum_add_distrib,← Finset.mul_sum] at he
    have hl := SparseAttainment.loss_identity X y βs
    rw [hF βs]
    unfold h2
    rw [← Finset.mul_sum]
    linarith
#print axioms smallbox_attainment
#print axioms SparseAttainment.linear_min_of_quadratic
#print axioms SparseAttainment.scalar_certificate
#print axioms SparseAttainment.loss_update

namespace Accepted45

set_option autoImplicit false
open L0BnB.Duality

namespace SparseDualitySupport

lemma sqrt_scaling (l0 l2 : ℝ) (h0 : 0 < l0) (h2 : 0 < l2) :
    Real.sqrt (l0 / l2) * Real.sqrt (l2 / l0) = 1 ∧
    l0 * Real.sqrt (l2 / l0) = Real.sqrt (l0 * l2) := by
  constructor
  · rw [← Real.sqrt_mul (div_pos h0 h2).le]
    have : l0 / l2 * (l2 / l0) = 1 := by field_simp
    rw [this, Real.sqrt_one]
  · have hs := Real.sq_sqrt (div_pos h2 h0).le
    have hw := Real.sq_sqrt (mul_pos h0 h2).le
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    have hx : l0 * Real.sqrt (l2 / l0) ^ 2 = l2 := by
      rw [hs]; field_simp
    nlinarith

lemma psi1_linear (l0 l2 b : ℝ) (h0 : 0 < l0) (h2 : 0 < l2)
    (hb : |b| ≤ Real.sqrt (l0 / l2)) :
    L0BnB.Reduced.psi1 l0 l2 b = 2 * Real.sqrt (l0 * l2) * |b| := by
  obtain ⟨ht, hw⟩ := sqrt_scaling l0 l2 h0 h2
  have hs := Real.sqrt_nonneg (l2 / l0)
  have hbound : |b * Real.sqrt (l2 / l0)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hs]
    calc |b| * Real.sqrt (l2 / l0) ≤ Real.sqrt (l0 / l2) * Real.sqrt (l2 / l0) :=
      mul_le_mul_of_nonneg_right hb hs
      _ = 1 := ht
  unfold L0BnB.Reduced.psi1 L0BnB.Reduced.reverseHuber
  rw [if_pos hbound, abs_mul, abs_of_nonneg hs]
  calc 2 * l0 * (|b| * Real.sqrt (l2 / l0)) = 2 * (l0 * Real.sqrt (l2 / l0)) * |b| := by ring
    _ = _ := by rw [hw]

lemma interval_linear_minimum (c a t : ℝ) (hc : 0 ≤ c) (ht : 0 ≤ t) :
    let u := if 0 ≤ c - |a| then 0 else -t * Real.sign a
    u ∈ Set.Icc (-t) t ∧ ∀ b ∈ Set.Icc (-t) t,
      c * |u| + a * u ≤ c * |b| + a * b := by
  dsimp
  by_cases h : 0 ≤ c - |a|
  · rw [if_pos h]
    refine ⟨⟨by linarith, ht⟩, ?_⟩
    intro b hb
    have ha : -(|a| * |b|) ≤ a * b := by simpa only [abs_mul] using neg_abs_le (a*b)
    have hz := mul_nonneg h (abs_nonneg b)
    simp only [abs_zero, mul_zero, zero_add]
    nlinarith
  · rw [if_neg h]
    have hane : a ≠ 0 := by intro hz; subst a; simp at h; linarith
    have habs : |-t * Real.sign a| = t := by
      rcases lt_or_gt_of_ne hane with ha | ha
      · rw [Real.sign_of_neg ha]; simp [abs_of_nonneg ht]
      · rw [Real.sign_of_pos ha]; simp [abs_of_nonneg ht]
    have hau : a * (-t * Real.sign a) = -|a| * t := by
      rcases lt_or_gt_of_ne hane with ha | ha
      · rw [Real.sign_of_neg ha, abs_of_neg ha]; ring
      · rw [Real.sign_of_pos ha, abs_of_pos ha]; ring
    refine ⟨abs_le.mp (by rw [habs]), ?_⟩
    intro b hb
    have hbt : |b| ≤ t := abs_le.mpr hb
    have ha : -(|a| * |b|) ≤ a * b := by simpa only [abs_mul] using neg_abs_le (a*b)
    have hm := mul_le_mul_of_nonpos_left hbt (le_of_lt (not_le.mp h))
    rw [habs, hau]
    nlinarith

end SparseDualitySupport

theorem solution (lam0 lam2 a η : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hη : 0 ≤ η) :
    betaTilde45 lam0 lam2 a η ∈ Set.Icc (-Real.sqrt (lam0 / lam2)) (Real.sqrt (lam0 / lam2)) ∧
      ∀ b ∈ Set.Icc (-Real.sqrt (lam0 / lam2)) (Real.sqrt (lam0 / lam2)),
        D lam0 lam2 a η (betaTilde45 lam0 lam2 a η) ≤ D lam0 lam2 a η b := by
  have hc : 0 ≤ 2 * Real.sqrt (lam0 * lam2) + η := by positivity
  obtain ⟨hu, hmin⟩ := SparseDualitySupport.interval_linear_minimum
    (2 * Real.sqrt (lam0 * lam2) + η) a (Real.sqrt (lam0 / lam2)) hc (Real.sqrt_nonneg _)
  change betaTilde45 lam0 lam2 a η ∈ _ at hu
  change ∀ b ∈ Set.Icc (-Real.sqrt (lam0 / lam2)) (Real.sqrt (lam0 / lam2)),
    (2 * Real.sqrt (lam0 * lam2) + η) * |betaTilde45 lam0 lam2 a η| + a * betaTilde45 lam0 lam2 a η ≤
      (2 * Real.sqrt (lam0 * lam2) + η) * |b| + a * b at hmin
  refine ⟨hu, ?_⟩
  intro b hb
  unfold D
  rw [SparseDualitySupport.psi1_linear _ _ _ hlam0 hlam2 (abs_le.mpr hu),
    SparseDualitySupport.psi1_linear _ _ _ hlam0 hlam2 (abs_le.mpr hb)]
  nlinarith [hmin b hb]

end Accepted45

open L0BnB.Reduced L0BnB.Duality
namespace ReverseHuberAttainment
noncomputable def pen (s x : ℝ) : ℝ := if |x|  ≤  s then 2 * s * |x| else x ^ 2 + s ^ 2

lemma formula (l0 l2 x : ℝ) (h0 : 0 < l0) (h2 : 0 < l2) :
    psi1 l0 l2 x = l2  *  pen (Real.sqrt (l0 / l2)) x := by
  let s := Real.sqrt (l0 / l2)
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos h0 h2)
  have hsq : l2 * s ^ 2=l0 := by dsimp [s];rw [Real.sq_sqrt (div_pos h0 h2).le];field_simp
  have hls : l2 * s=Real.sqrt (l0 * l2) := by
    apply (sq_eq_sq₀ (mul_pos h2 hs).le (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (mul_pos h0 h2).le]
    calc (l2 * s) ^ 2=l2 * (l2 * s ^ 2) := by ring
      _ = l0 * l2 := by rw [hsq];ring
  by_cases hx : |x|  ≤ s
  · rw [Accepted45.SparseDualitySupport.psi1_linear l0 l2 x h0 h2 hx]
    change _ = l2 * (if |x|  ≤ s then 2 * s * |x| else x ^ 2 + s ^ 2)
    rw [if_pos hx,← hls];ring
  · have hu : 0  <  Real.sqrt (l2 / l0) := Real.sqrt_pos.mpr (div_pos h2 h0)
    have hscale := (Accepted45.SparseDualitySupport.sqrt_scaling l0 l2 h0 h2).1
    have hbranch : ¬ |x * Real.sqrt (l2 / l0)|  ≤ 1 := by
      rw [abs_mul,abs_of_pos hu]
      change s * Real.sqrt (l2 / l0)=1 at hscale
      nlinarith [mul_lt_mul_of_pos_right (not_le.mp hx) hu]
    unfold psi1 reverseHuber pen
    rw [if_neg hbranch,if_neg hx]
    rw [mul_pow,Real.sq_sqrt (div_pos h2 h0).le]
    change _=l2 * (x ^ 2 + s ^ 2)
    field_simp
    nlinarith [hsq]

lemma envelope (s x b : ℝ) (hs : 0 ≤ s) :
    pen s b  -  pen s x  ≤  b ^ 2 - x ^ 2 + 2 * (s - min |x| s) * (|b|  - |x|) := by
  have hx0 := abs_nonneg x
  have hb0 := abs_nonneg b
  have hx2 := sq_abs x
  have hb2 := sq_abs b
  by_cases hx : |x|  ≤ s
  · rw [min_eq_left hx]
    unfold pen
    rw [if_pos hx]
    by_cases hb : |b|  ≤ s
    · rw [if_pos hb]
      nlinarith [sq_nonneg (|b|  - |x|)]
    · rw [if_neg hb]
      have hh := mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ 2 * |b|  - s - |x| by linarith [not_le.mp hb])
      nlinarith
  · rw [min_eq_right (not_le.mp hx).le,sub_self,mul_zero,zero_mul,add_zero]
    unfold pen
    rw [if_neg hx]
    by_cases hb : |b|  ≤ s
    · rw [if_pos hb]
      nlinarith [sq_nonneg (|b|  - s)]
    · rw [if_neg hb]
      linarith

lemma linear_stationarity (l s M a q x : ℝ) (hl : 0 ≤ l) (hs : 0 ≤ s) (hx : |x|  ≤ M)
    (h : ∀ b, |b|  ≤ M → 0 ≤ q * (b - x) ^ 2 + a * (b - x) + l * (pen s b - pen s x)) :
    ∀ b, |b|  ≤ M →
      (2 * l * (s - min |x| s)) * |x|  + (a + 2 * l * x) * x  ≤ 
      (2 * l * (s - min |x| s)) * |b|  + (a + 2 * l * x) * b := by
  have hc : 0 ≤ 2 * l * (s - min |x| s) := mul_nonneg (by positivity) (sub_nonneg.mpr (min_le_right _ _))
  apply SparseAttainment.linear_min_of_quadratic (q + l) (a + 2 * l * x) (2 * l * (s - min |x| s)) M x hc hx
  intro b hb
  have henv := mul_le_mul_of_nonneg_left (envelope s x b hs) hl
  have hh := h b hb
  nlinarith
end ReverseHuberAttainment

open L0BnB.Reduced L0BnB.Duality
namespace ReverseHuberAttainment

lemma square_div (l u : ℝ) (hl : 0 < l) : (2 * l * u) ^ 2 / (4 * l)=l * u ^ 2 := by
  field_simp
  ring

lemma large_pen (s x : ℝ) (hs : 0 ≤ s) (hx : s ≤ |x|) : pen s x=x ^ 2 + s ^ 2 := by
  unfold pen
  split_ifs with h
  · have he : |x| =s := le_antisymm h hx
    nlinarith [sq_abs x]
  · rfl

lemma certificate (l s M a x : ℝ) (hl : 0 < l) (hs : 0 < s) (hM : 0 < M)
    (hreg : s ≤ M) (hx : |x|  ≤ M)
    (hmin : ∀ b, |b|  ≤ M →
      (2 * l * (s - min |x| s)) * |x|  + (a + 2 * l * x) * x  ≤ 
      (2 * l * (s - min |x| s)) * |b|  + (a + 2 * l * x) * b) :
    let γ := if |x| =M then a - 2 * M * l * Real.sign a else 0
    l * pen s x + a * x =  - (max ((a - γ) ^ 2 / (4 * l) - l * s ^ 2) 0 + M * |γ|) := by
  dsimp
  by_cases hb : |x| =M
  · rw [if_pos hb]
    have hc : 2 * l * (s - min |x| s)=0 := by rw [hb,min_eq_right hreg];ring
    simp only [hc,zero_mul,zero_add] at hmin
    rw [large_pen s x hs.le (by rw [hb];exact hreg)]
    have hMsq : s ^ 2 ≤ M ^ 2 := sq_le_sq₀ hs.le hM.le |>.mpr hreg
    by_cases hx0 : 0 ≤ x
    · have he : x=M := by simpa [abs_of_nonneg hx0] using hb
      subst x
      have hn := hmin ( - M) (by simp [abs_of_pos hM])
      have ha : a + 2 * l * M ≤ 0 := by nlinarith
      have han : a < 0 := by nlinarith [mul_pos hl hM]
      rw [Real.sign_of_neg han]
      have hgam : a - 2 * M * l * ( - 1) ≤ 0 := by nlinarith
      rw [abs_of_nonpos hgam]
      have heq : (a - (a - 2 * M * l * ( - 1))) ^ 2 / (4 * l) - l * s ^ 2=l * (M ^ 2 - s ^ 2) := by
        calc _ = (2 * l * M) ^ 2 / (4 * l) - l * s ^ 2 := by congr 2  <;> ring
          _ = _ := by rw [square_div l M hl];ring
      rw [heq,max_eq_left (mul_nonneg hl.le (sub_nonneg.mpr hMsq))]
      ring
    · have hxneg : x < 0 := lt_of_not_ge hx0
      have he : x =  - M := by rw [abs_of_neg hxneg] at hb;linarith
      subst x
      have hn := hmin M (by simp [abs_of_pos hM])
      have ha : 0 ≤ a - 2 * l * M := by nlinarith
      have hap : 0 < a := by nlinarith [mul_pos hl hM]
      rw [Real.sign_of_pos hap]
      have hgam : 0 ≤ a - 2 * M * l * 1 := by nlinarith
      rw [abs_of_nonneg hgam]
      have heq : (a - (a - 2 * M * l * 1)) ^ 2 / (4 * l) - l * s ^ 2=l * (M ^ 2 - s ^ 2) := by
        calc _ = (2 * l * M) ^ 2 / (4 * l) - l * s ^ 2 := by congr 2  <;> ring
          _ = _ := by rw [square_div l M hl];ring
      rw [heq,max_eq_left (mul_nonneg hl.le (sub_nonneg.mpr hMsq))]
      ring
  · rw [if_neg hb,sub_zero,abs_zero,mul_zero,add_zero]
    have hc : 0 ≤ 2 * l * (s - min |x| s) := mul_nonneg (by positivity) (sub_nonneg.mpr (min_le_right _ _))
    have hcert := SparseAttainment.scalar_certificate (a + 2 * l * x) (2 * l * (s - min |x| s)) M x hc hM hx hmin
    dsimp at hcert
    rw [if_neg hb,sub_zero,abs_zero,mul_zero] at hcert
    obtain ⟨hA,hcomp⟩ := hcert
    by_cases hxs : |x|  ≤ s
    · rw [min_eq_left hxs] at hA hcomp
      have hab : |a|  ≤ 2 * l * s := by
        calc
          |a| =|(a + 2 * l * x) - 2 * l * x| := by congr 1;ring
          _  ≤  |a + 2 * l * x|  + |2 * l * x| := by simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le (a + 2 * l * x) 0 (2 * l * x))
          _  ≤  2 * l * (s - |x|) + 2 * l * |x| := by
            rw [abs_mul,abs_of_pos (mul_pos (by norm_num) hl)]
            linarith
          _ = _ := by ring
      have harg : a ^ 2 / (4 * l) - l * s ^ 2 ≤ 0 := by
        have hh := (sq_le_sq₀ (abs_nonneg a) (by positivity : 0 ≤ 2 * l * s)).mpr hab
        rw [sq_abs] at hh
        have hd : a ^ 2 / (4 * l) ≤ l * s ^ 2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
        linarith
      rw [max_eq_right harg]
      unfold pen
      rw [if_pos hxs]
      nlinarith [sq_abs x]
    · have hsx : s < |x| := not_le.mp hxs
      simp only [min_eq_right hsx.le,sub_self,mul_zero,zero_mul,zero_add] at hA hcomp
      have he : a + 2 * l * x=0 := abs_nonpos_iff.mp hA
      have hae : a=  - (2 * l * x) := by linarith
      rw [hae,neg_sq,square_div l x hl,large_pen s x hs.le hsx.le]
      have harg : 0 ≤ l * x ^ 2 - l * s ^ 2 := by
        have hh := (sq_le_sq₀ hs.le (abs_nonneg x)).mpr hsx.le
        rw [sq_abs] at hh
        nlinarith [mul_nonneg hl.le (sub_nonneg.mpr hh)]
      rw [max_eq_left harg]
      ring

end ReverseHuberAttainment

open L0BnB.Reduced L0BnB.Duality
theorem largebox_attainment {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hreg : Real.sqrt (lam0 / lam2) ≤ M)
    (βs : Fin p → ℝ) (hβs : βs ∈ box p M)
    (hopt : ∀ β ∈ box p M, F X y lam0 lam2 M βs ≤ F X y lam0 lam2 M β) :
    h1 X y lam0 lam2 M (alphaStar X y βs) (gammaStar X y lam2 M βs) =
      F X y lam0 lam2 M βs := by
  let s := Real.sqrt (lam0 / lam2)
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos hlam0 hlam2)
  have hsq : lam2 * s ^ 2 = lam0 := by
    dsimp [s]; rw [Real.sq_sqrt (div_pos hlam0 hlam2).le]; field_simp
  have hF (β : Fin p → ℝ) : F X y lam0 lam2 M β =
      lsLoss X y β + ∑ i, lam2 * ReverseHuberAttainment.pen s (β i) := by
    simp only [F, psi, if_pos hreg, ReverseHuberAttainment.formula _ _ _ hlam0 hlam2, s]
  have hcoord (i : Fin p) :
      lam2 * ReverseHuberAttainment.pen s (βs i) +
        colDot X (alphaStar X y βs) i * βs i =
      -v X lam0 lam2 M (alphaStar X y βs) i (gammaStar X y lam2 M βs i) := by
    have hquad (b : ℝ) (hb : |b| ≤ M) :
        0 ≤ ((1/2)*(∑ r, (X r i)^2))*(b-βs i)^2 +
          colDot X (rhoStar X y βs) i*(b-βs i) +
          lam2*(ReverseHuberAttainment.pen s b-ReverseHuberAttainment.pen s (βs i)) := by
      have hbox : Function.update βs i b ∈ box p M := by
        intro j
        by_cases hj : j=i
        · subst j; simpa using hb
        · simpa [Function.update_of_ne hj] using hβs j
      have hh := hopt _ hbox
      rw [hF βs, hF (Function.update βs i b), SparseAttainment.loss_update,
        SparseAttainment.sum_update (fun _ x => lam2 * ReverseHuberAttainment.pen s x)] at hh
      linarith
    have hlin := ReverseHuberAttainment.linear_stationarity lam2 s M
      (colDot X (rhoStar X y βs) i) ((1/2)*(∑ r, (X r i)^2)) (βs i)
      hlam2.le hs.le (hβs i) hquad
    have hh := ReverseHuberAttainment.certificate lam2 s M
      (colDot X (rhoStar X y βs) i) (βs i) hlam2 hs hM hreg (hβs i) hlin
    dsimp at hh
    rw [hsq] at hh
    exact hh
  have he := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun i (_ : i ∈ Finset.univ) => hcoord i)
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib] at he
  have hl := SparseAttainment.loss_identity X y βs
  change -(1/2)*(∑ r, (alphaStar X y βs r)^2) -
    (∑ r, alphaStar X y βs r*y r) +
    (∑ i, colDot X (alphaStar X y βs) i*βs i) = lsLoss X y βs at hl
  rw [hF βs]
  unfold h1
  linarith
#print axioms largebox_attainment

namespace WeakArchive

namespace Accepted45

set_option autoImplicit false
open L0BnB.Duality

namespace SparseDualitySupport

lemma sqrt_scaling (l0 l2 : ℝ) (h0 : 0 < l0) (h2 : 0 < l2) :
    Real.sqrt (l0 / l2) * Real.sqrt (l2 / l0) = 1 ∧
    l0 * Real.sqrt (l2 / l0) = Real.sqrt (l0 * l2) := by
  constructor
  · rw [← Real.sqrt_mul (div_pos h0 h2).le]
    have : l0 / l2 * (l2 / l0) = 1 := by field_simp
    rw [this, Real.sqrt_one]
  · have hs := Real.sq_sqrt (div_pos h2 h0).le
    have hw := Real.sq_sqrt (mul_pos h0 h2).le
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    have hx : l0 * Real.sqrt (l2 / l0) ^ 2 = l2 := by
      rw [hs]; field_simp
    nlinarith

lemma psi1_linear (l0 l2 b : ℝ) (h0 : 0 < l0) (h2 : 0 < l2)
    (hb : |b| ≤ Real.sqrt (l0 / l2)) :
    L0BnB.Reduced.psi1 l0 l2 b = 2 * Real.sqrt (l0 * l2) * |b| := by
  obtain ⟨ht, hw⟩ := sqrt_scaling l0 l2 h0 h2
  have hs := Real.sqrt_nonneg (l2 / l0)
  have hbound : |b * Real.sqrt (l2 / l0)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hs]
    calc |b| * Real.sqrt (l2 / l0) ≤ Real.sqrt (l0 / l2) * Real.sqrt (l2 / l0) :=
      mul_le_mul_of_nonneg_right hb hs
      _ = 1 := ht
  unfold L0BnB.Reduced.psi1 L0BnB.Reduced.reverseHuber
  rw [if_pos hbound, abs_mul, abs_of_nonneg hs]
  calc 2 * l0 * (|b| * Real.sqrt (l2 / l0)) = 2 * (l0 * Real.sqrt (l2 / l0)) * |b| := by ring
    _ = _ := by rw [hw]

lemma interval_linear_minimum (c a t : ℝ) (hc : 0 ≤ c) (ht : 0 ≤ t) :
    let u := if 0 ≤ c - |a| then 0 else -t * Real.sign a
    u ∈ Set.Icc (-t) t ∧ ∀ b ∈ Set.Icc (-t) t,
      c * |u| + a * u ≤ c * |b| + a * b := by
  dsimp
  by_cases h : 0 ≤ c - |a|
  · rw [if_pos h]
    refine ⟨⟨by linarith, ht⟩, ?_⟩
    intro b hb
    have ha : -(|a| * |b|) ≤ a * b := by simpa only [abs_mul] using neg_abs_le (a*b)
    have hz := mul_nonneg h (abs_nonneg b)
    simp only [abs_zero, mul_zero, zero_add]
    nlinarith
  · rw [if_neg h]
    have hane : a ≠ 0 := by intro hz; subst a; simp at h; linarith
    have habs : |-t * Real.sign a| = t := by
      rcases lt_or_gt_of_ne hane with ha | ha
      · rw [Real.sign_of_neg ha]; simp [abs_of_nonneg ht]
      · rw [Real.sign_of_pos ha]; simp [abs_of_nonneg ht]
    have hau : a * (-t * Real.sign a) = -|a| * t := by
      rcases lt_or_gt_of_ne hane with ha | ha
      · rw [Real.sign_of_neg ha, abs_of_neg ha]; ring
      · rw [Real.sign_of_pos ha, abs_of_pos ha]; ring
    refine ⟨abs_le.mp (by rw [habs]), ?_⟩
    intro b hb
    have hbt : |b| ≤ t := abs_le.mpr hb
    have ha : -(|a| * |b|) ≤ a * b := by simpa only [abs_mul] using neg_abs_le (a*b)
    have hm := mul_le_mul_of_nonpos_left hbt (le_of_lt (not_le.mp h))
    rw [habs, hau]
    nlinarith

end SparseDualitySupport

theorem solution (lam0 lam2 a η : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hη : 0 ≤ η) :
    betaTilde45 lam0 lam2 a η ∈ Set.Icc (-Real.sqrt (lam0 / lam2)) (Real.sqrt (lam0 / lam2)) ∧
      ∀ b ∈ Set.Icc (-Real.sqrt (lam0 / lam2)) (Real.sqrt (lam0 / lam2)),
        D lam0 lam2 a η (betaTilde45 lam0 lam2 a η) ≤ D lam0 lam2 a η b := by
  have hc : 0 ≤ 2 * Real.sqrt (lam0 * lam2) + η := by positivity
  obtain ⟨hu, hmin⟩ := SparseDualitySupport.interval_linear_minimum
    (2 * Real.sqrt (lam0 * lam2) + η) a (Real.sqrt (lam0 / lam2)) hc (Real.sqrt_nonneg _)
  change betaTilde45 lam0 lam2 a η ∈ _ at hu
  change ∀ b ∈ Set.Icc (-Real.sqrt (lam0 / lam2)) (Real.sqrt (lam0 / lam2)),
    (2 * Real.sqrt (lam0 * lam2) + η) * |betaTilde45 lam0 lam2 a η| + a * betaTilde45 lam0 lam2 a η ≤
      (2 * Real.sqrt (lam0 * lam2) + η) * |b| + a * b at hmin
  refine ⟨hu, ?_⟩
  intro b hb
  unfold D
  rw [SparseDualitySupport.psi1_linear _ _ _ hlam0 hlam2 (abs_le.mpr hu),
    SparseDualitySupport.psi1_linear _ _ _ hlam0 hlam2 (abs_le.mpr hb)]
  nlinarith [hmin b hb]

end Accepted45

namespace Accepted47

set_option autoImplicit false
open L0BnB.Duality

theorem solution (lam0 lam2 a η : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hη : 0 ≤ η)
    (hcase : |a| - η ≥ 2 * Real.sqrt (lam0 * lam2)) :
    IsLeast (Set.range (D lam0 lam2 a η)) (-(1 / (4 * lam2)) * (|a| - η) ^ 2 + lam0) := by
  have hD : ∀ b, D lam0 lam2 a η b = 2 * lam0 * (if |b * Real.sqrt (lam2 / lam0)| ≤ 1 then |b * Real.sqrt (lam2 / lam0)| else ((b * Real.sqrt (lam2 / lam0)) ^ 2 + 1) / 2)
      + a * b + η * |b| := by
    intro b
    unfold D L0BnB.Reduced.psi1 L0BnB.Reduced.reverseHuber
    rfl
  have hw0 : 0 < Real.sqrt (lam0 * lam2) := Real.sqrt_pos.mpr (mul_pos hlam0 hlam2)
  have hw2 : Real.sqrt (lam0 * lam2) ^ 2 = lam0 * lam2 := Real.sq_sqrt (mul_pos hlam0 hlam2).le
  have hs0 : 0 < Real.sqrt (lam2 / lam0) := Real.sqrt_pos.mpr (div_pos hlam2 hlam0)
  have hs2 : Real.sqrt (lam2 / lam0) ^ 2 = lam2 / lam0 := Real.sq_sqrt (div_pos hlam2 hlam0).le
  generalize Real.sqrt (lam0 * lam2) = w at hw0 hw2 hcase
  generalize Real.sqrt (lam2 / lam0) = s at hs0 hs2 hD
  generalize hcdef : |a| - η = c at hcase
  have hls2 : lam0 * s ^ 2 = lam2 := by rw [hs2]; field_simp
  have hws : lam0 * s = w := by
    have h1 : (lam0 * s) ^ 2 = w ^ 2 := by
      rw [mul_pow, hw2]; nlinarith [hls2]
    exact (sq_eq_sq₀ (by positivity) hw0.le).mp h1
  have hws2 : w * s = lam2 := by rw [← hws]; nlinarith [hls2]
  have hc2 : 2 * w ≤ c := hcase
  have hcpos : 0 < c := by linarith
  constructor
  · -- attained
    let b0 : ℝ := if 0 ≤ a then -(c / (2 * lam2)) else c / (2 * lam2)
    have hb0abs : |b0| = c / (2 * lam2) := by
      unfold b0
      split_ifs
      · rw [abs_neg, abs_of_pos (by positivity)]
      · rw [abs_of_pos (by positivity)]
    have hab0 : a * b0 = -|a| * (c / (2 * lam2)) := by
      unfold b0
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · rw [abs_of_neg (not_le.mp h)]; ring
    have hbs : 1 ≤ |b0 * s| := by
      rw [abs_mul, hb0abs, abs_of_pos hs0]
      rw [← sub_nonneg]
      have : c / (2 * lam2) * s - 1 = (c * s - 2 * lam2) / (2 * lam2) := by field_simp
      rw [this]
      apply div_nonneg _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hc2 hs0.le]
    refine ⟨b0, ?_⟩
    rw [hD]
    have hRH : (if |b0 * s| ≤ 1 then |b0 * s| else ((b0 * s) ^ 2 + 1) / 2) = ((b0 * s) ^ 2 + 1) / 2 := by
      split_ifs with h
      · have h1 : |b0 * s| = 1 := le_antisymm h hbs
        have h2 : (b0 * s) ^ 2 = 1 := by rw [← sq_abs, h1]; norm_num
        rw [h1, h2]; norm_num
      · rfl
    rw [hRH, hab0, hb0abs]
    have hb2 : (b0 * s) ^ 2 = (c / (2 * lam2)) ^ 2 * s ^ 2 := by
      rw [mul_pow, ← sq_abs b0, hb0abs]
    rw [hb2]
    have hη' : η = |a| - c := by linarith [hcdef]
    rw [hη']
    field_simp
    nlinarith [hls2]
  · rintro _ ⟨b, rfl⟩
    rw [hD]
    have hab : -|a| * |b| ≤ a * b := by
      have := neg_abs_le (a * b)
      rw [abs_mul] at this
      linarith
    have hη' : η = |a| - c := by linarith [hcdef]
    have hb0 : 0 ≤ |b| := abs_nonneg b
    by_cases hcs : |b * s| ≤ 1
    · rw [if_pos hcs]
      have h1 : |b * s| = |b| * s := by rw [abs_mul, abs_of_pos hs0]
      rw [h1] at hcs ⊢
      have h2 : |b| * w ≤ lam0 := by
        have := mul_le_mul_of_nonneg_left hcs hlam0.le
        nlinarith [hws]
      have h3 : lam2 * |b| ≤ w := by
        have h4 : lam2 * |b| * w ≤ w * w := by nlinarith [hw2]
        exact le_of_mul_le_mul_right h4 hw0
      have h5 : 2 * lam0 * (|b| * s) = 2 * w * |b| := by
        rw [← hws]; ring
      rw [h5]
      have : 0 ≤ (c - 2 * w) * (2 * w + c - 4 * lam2 * |b|) :=
        mul_nonneg (by linarith) (by linarith)
      have e : -(1 / (4 * lam2)) * c ^ 2 + lam0 = (4 * lam0 * lam2 - c ^ 2) / (4 * lam2) := by
        field_simp
        ring
      rw [e, div_le_iff₀ (by positivity)]
      have hlam : lam0 * lam2 = w ^ 2 := hw2.symm
      nlinarith [hab, this]
    · rw [if_neg hcs]
      have h1 : (b * s) ^ 2 = |b| ^ 2 * s ^ 2 := by rw [mul_pow, sq_abs]
      rw [h1]
      have h6 : 2 * lam0 * ((|b| ^ 2 * s ^ 2 + 1) / 2) = lam2 * |b| ^ 2 + lam0 := by
        have : lam0 * (|b| ^ 2 * s ^ 2) = lam2 * |b| ^ 2 := by
          calc lam0 * (|b| ^ 2 * s ^ 2) = |b| ^ 2 * (lam0 * s ^ 2) := by ring
            _ = lam2 * |b| ^ 2 := by rw [hls2]; ring
        nlinarith [this]
      rw [h6]
      have e : -(1 / (4 * lam2)) * c ^ 2 + lam0 = lam0 - c ^ 2 / (4 * lam2) := by ring
      rw [e]
      have h7 : 0 ≤ (2 * lam2 * |b| - c) ^ 2 / (4 * lam2) := by positivity
      have h8 : (2 * lam2 * |b| - c) ^ 2 / (4 * lam2) = lam2 * |b| ^ 2 - c * |b| + c ^ 2 / (4 * lam2) := by
        field_simp; ring
      rw [hη']
      nlinarith [hab, h7, h8]

end Accepted47
set_option autoImplicit false
open L0BnB.Duality L0BnB.Reduced

namespace WeakDualitySupport

lemma psi1_lower (l0 l2 b : ℝ) (h0 : 0 < l0) (h2 : 0 < l2) :
    2 * Real.sqrt (l0 * l2) * |b| ≤ psi1 l0 l2 b := by
  have hw := (Accepted45.SparseDualitySupport.sqrt_scaling l0 l2 h0 h2).2
  have hr : |b * Real.sqrt (l2 / l0)| ≤ reverseHuber (b * Real.sqrt (l2 / l0)) := by
    unfold reverseHuber
    split_ifs with h
    · exact le_rfl
    · nlinarith [sq_nonneg (|b * Real.sqrt (l2/l0)| - 1), sq_abs (b * Real.sqrt (l2/l0))]
  have hm := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2*l0)
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at hm
  unfold psi1
  calc 2 * Real.sqrt (l0 * l2) * |b| = 2*l0*(|b| *Real.sqrt (l2/l0)) := by rw [← hw]; ring
    _ ≤ _ := hm

lemma conjugate_bound (l0 l2 a b : ℝ) (h0 : 0 < l0) (h2 : 0 < l2) :
    -(max (a^2/(4*l2)-l0) 0) ≤ psi1 l0 l2 b + a*b := by
  have hw := Real.sq_sqrt (mul_pos h0 h2).le
  have hw0 := Real.sqrt_nonneg (l0*l2)
  by_cases ha : 2 * Real.sqrt (l0*l2) ≤ |a|
  · have hh := (Accepted47.solution l0 l2 a 0 h0 h2 (le_refl _) (by simpa using ha)).2
    have hb := hh (Set.mem_range_self b)
    have hq : 0 ≤ a^2/(4*l2)-l0 := by
      have hsq : 4*l0*l2 ≤ a^2 := by nlinarith [sq_abs a]
      rw [sub_nonneg, le_div_iff₀ (by positivity)]
      nlinarith
    rw [max_eq_left hq]
    simp only [D, zero_mul, add_zero, sub_zero, sq_abs] at hb
    convert hb using 1 <;> ring
  · have ha' : |a| ≤ 2 * Real.sqrt (l0*l2) := le_of_lt (not_le.mp ha)
    have hq : a^2/(4*l2)-l0 ≤ 0 := by
      rw [sub_nonpos, div_le_iff₀ (by positivity)]
      nlinarith [sq_abs a, abs_nonneg a]
    rw [max_eq_right hq, neg_zero]
    have hp := psi1_lower l0 l2 b h0 h2
    have hab : -(|a| * |b|) ≤ a*b := by simpa only [abs_mul] using neg_abs_le (a*b)
    have hm := mul_le_mul_of_nonneg_right ha' (abs_nonneg b)
    linarith

lemma loss_bound {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (y α : Fin n → ℝ) (β : Fin p → ℝ) :
    -(1/2) * ∑ r, α r ^ 2 - ∑ r, α r * y r + ∑ i, colDot X α i * β i ≤
      lsLoss X y β := by
  have hs : ∑ i, colDot X α i * β i = ∑ r, α r * Matrix.mulVec X β r := by
    simp only [colDot, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r hr
    apply Finset.sum_congr rfl; intro i hi; ring
  rw [hs]
  have hb : ∑ r, (-(1/2)*α r^2 - α r*y r + α r*Matrix.mulVec X β r) ≤
      ∑ r, (1/2)*(y r-Matrix.mulVec X β r)^2 := by
    apply Finset.sum_le_sum; intro r hr
    nlinarith [sq_nonneg (α r+y r-Matrix.mulVec X β r)]
  simpa only [lsLoss, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] using hb

end WeakDualitySupport

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M) :
    (Real.sqrt (lam0 / lam2) ≤ M →
      ∀ (α : Fin n → ℝ) (γ : Fin p → ℝ), ∀ β ∈ L0BnB.Reduced.box p M,
        h1 X y lam0 lam2 M α γ ≤ L0BnB.Reduced.F X y lam0 lam2 M β) ∧
    (M < Real.sqrt (lam0 / lam2) →
      ∀ (ρ : Fin n → ℝ) (μ : Fin p → ℝ), Feas22 X lam0 lam2 M ρ μ → ∀ β ∈ L0BnB.Reduced.box p M,
        h2 y M ρ μ ≤ L0BnB.Reduced.F X y lam0 lam2 M β) := by
  constructor
  · intro hcase α γ β hβ
    have hcoord : ∀ i, -v X lam0 lam2 M α i (γ i) ≤
        psi1 lam0 lam2 (β i) + colDot X α i * β i := by
      intro i
      have hcon := WeakDualitySupport.conjugate_bound lam0 lam2 (colDot X α i-γ i) (β i) hlam0 hlam2
      have hg : -(|γ i| * |β i|) ≤ γ i*β i := by simpa only [abs_mul] using neg_abs_le (γ i*β i)
      have hm := mul_le_mul_of_nonneg_left (hβ i) (abs_nonneg (γ i))
      unfold v
      nlinarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoord i)
    have hls := WeakDualitySupport.loss_bound X y α β
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib] at hsum
    have hF : F X y lam0 lam2 M β = lsLoss X y β + ∑ i, psi1 lam0 lam2 (β i) := by
      simp only [F, psi, if_pos hcase]
    rw [hF]; unfold h1; linarith
  · intro hcase ρ μ hfeas β hβ
    have hcoord : ∀ i, -M* |μ i| ≤ psi2 lam0 lam2 M (β i) + colDot X ρ i * β i := by
      intro i
      have hf := mul_le_mul_of_nonneg_right (hfeas i) (abs_nonneg (β i))
      have ha : -(|colDot X ρ i| * |β i|) ≤ colDot X ρ i * β i := by
        simpa only [abs_mul] using neg_abs_le (colDot X ρ i * β i)
      have hmu := mul_le_mul_of_nonneg_right (le_abs_self (μ i)) (abs_nonneg (β i))
      have hm := mul_le_mul_of_nonneg_left (hβ i) (abs_nonneg (μ i))
      unfold psi2
      nlinarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoord i)
    have hls := WeakDualitySupport.loss_bound X y ρ β
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have hF : F X y lam0 lam2 M β = lsLoss X y β + ∑ i, psi2 lam0 lam2 M (β i) := by
      simp only [F, psi, if_neg (not_le.mpr hcase)]
    rw [hF]; unfold h2; linarith
end WeakArchive
open L0BnB.Duality

/-- Theorem 2, pp. 13–14. Let `β*` be an optimal solution of (5) and `r* = y − Xβ*`.
1. If `√(λ₀/λ₂) ≤ M`, then (20) is a dual of (5): `h₁(α, γ) ≤ L0BnB.Reduced.F(β)` for all `α ∈ ℝⁿ`, `γ ∈ ℝᵖ`
   and all `β` feasible for (5); and the dual variables (23), `α* = −r*`,
   `γ*ᵢ = 𝟙[|β*ᵢ| = M](α*ᵀXᵢ − 2Mλ₂ sign(α*ᵀXᵢ))`, are optimal: `h₁(α*, γ*) = L0BnB.Reduced.F(β*)`.
2. If `√(λ₀/λ₂) > M`, then (22) is a dual of (5): `h₂(ρ, μ) ≤ L0BnB.Reduced.F(β)` for all `(ρ, μ)` feasible
   for (22) and all `β` feasible for (5); and the dual variables (24), `ρ* = −r*`,
   `μ*ᵢ = 𝟙[|β*ᵢ| = M](|ρ*ᵀXᵢ| − λ₀/M − λ₂M)`, are feasible for (22) and optimal:
   `h₂(ρ*, μ*) = L0BnB.Reduced.F(β*)`. -/
theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (βs : Fin p → ℝ) (hβs : βs ∈ L0BnB.Reduced.box p M)
    (hopt : ∀ β ∈ L0BnB.Reduced.box p M, L0BnB.Reduced.F X y lam0 lam2 M βs ≤ L0BnB.Reduced.F X y lam0 lam2 M β) :
    (Real.sqrt (lam0 / lam2) ≤ M →
      (∀ (α : Fin n → ℝ) (γ : Fin p → ℝ), ∀ β ∈ L0BnB.Reduced.box p M,
        h1 X y lam0 lam2 M α γ ≤ L0BnB.Reduced.F X y lam0 lam2 M β) ∧
      h1 X y lam0 lam2 M (alphaStar X y βs) (gammaStar X y lam2 M βs) =
        L0BnB.Reduced.F X y lam0 lam2 M βs) ∧
    (M < Real.sqrt (lam0 / lam2) →
      (∀ (ρ : Fin n → ℝ) (μ : Fin p → ℝ), Feas22 X lam0 lam2 M ρ μ → ∀ β ∈ L0BnB.Reduced.box p M,
        h2 y M ρ μ ≤ L0BnB.Reduced.F X y lam0 lam2 M β) ∧
      Feas22 X lam0 lam2 M (rhoStar X y βs) (muStar X y lam0 lam2 M βs) ∧
      h2 y M (rhoStar X y βs) (muStar X y lam0 lam2 M βs) = L0BnB.Reduced.F X y lam0 lam2 M βs)  := by
  have hw := WeakArchive.solution X y lam0 lam2 M hlam0 hlam2 hM
  constructor
  · intro hreg
    exact ⟨hw.1 hreg, largebox_attainment X y lam0 lam2 M hlam0 hlam2 hM hreg βs hβs hopt⟩
  · intro hreg
    exact ⟨hw.2 hreg, smallbox_attainment X y lam0 lam2 M hlam0 hlam2 hM hreg βs hβs hopt⟩



#print axioms solution
