-- Prove2me | solution 1 for L0BnB.Duality.eq_24
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T09:10:01.656087+00:00
-- url     : https://prove2.me/submissions/5abaaafd-5a59-40a4-9c3b-03e3b6e92bea

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

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
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
#print axioms solution
#print axioms SparseAttainment.linear_min_of_quadratic
#print axioms SparseAttainment.scalar_certificate
#print axioms SparseAttainment.loss_update
