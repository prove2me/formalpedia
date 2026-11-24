-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_mixed_price_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T22:04:08.165691+00:00
-- url     : https://prove2.me/submissions/944a32c3-f6fb-453b-a6fb-09a51629b0b6

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_GrothendieckLB_Supplement_cq_gaussian_fourier_moment_bound
import Theorems.Thm_GrothendieckLB_Supplement_cq_fourier_moment_derivatives
import Theorems.Thm_GrothendieckLB_Supplement_cq_gaussian_price_under_integral


open MeasureTheory Real GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice Filter
open scoped Topology
namespace CQPriceGrowth

noncomputable def weight (w : ℝ×ℝ) := (1+|w.1|)*(1+|w.2|)
theorem wone (w : ℝ×ℝ) : 1≤weight w := by unfold weight;nlinarith [abs_nonneg w.1,abs_nonneg w.2,mul_nonneg (abs_nonneg w.1) (abs_nonneg w.2)]
theorem wpos (w : ℝ×ℝ) : 0≤weight w := zero_le_one.trans (wone w)

def Growth {ι : Type*} (f : ι → ℝ×ℝ → ℂ) : Prop :=
  ∃ C : ℝ, 0≤C ∧ ∃ n : ℕ, ∀ i w, ‖f i w‖ ≤ C*(weight w)^n

theorem Growth.of_bound {ι : Type*} {f : ι→ℝ×ℝ→ℂ} {C : ℝ} (hC : 0≤C) (h : ∀ i w, ‖f i w‖≤C) : Growth f :=
  ⟨C,hC,0,fun i w => by simpa using h i w⟩

theorem Growth.const {ι : Type*} (c : ℂ) : Growth (fun (_ : ι) (_ : ℝ×ℝ) => c) :=
  Growth.of_bound (norm_nonneg _) fun _ _ => le_rfl

theorem Growth.comp {ι κ : Type*} {f : ι→ℝ×ℝ→ℂ} (hf : Growth f) (q : κ→ι) :
    Growth (fun j w => f (q j) w) := by
  obtain ⟨C,hC,n,h⟩ := hf
  exact ⟨C,hC,n,fun j w => h _ w⟩

theorem Growth.mul {ι : Type*} {f g : ι→ℝ×ℝ→ℂ} (hf : Growth f) (hg : Growth g) :
    Growth (fun i w => f i w*g i w) := by
  obtain ⟨C,hC,n,hf⟩ := hf
  obtain ⟨B,hB,k,hg⟩ := hg
  refine ⟨C*B,mul_nonneg hC hB,n+k,fun i w => ?_⟩
  rw [norm_mul,pow_add]
  exact (mul_le_mul (hf i w) (hg i w) (norm_nonneg _) (mul_nonneg hC (pow_nonneg (wpos w) _))).trans_eq (by ring)

theorem Growth.add {ι : Type*} {f g : ι→ℝ×ℝ→ℂ} (hf : Growth f) (hg : Growth g) :
    Growth (fun i w => f i w+g i w) := by
  obtain ⟨C,hC,n,hf⟩ := hf
  obtain ⟨B,hB,k,hg⟩ := hg
  refine ⟨C+B,add_nonneg hC hB,max n k,fun i w => ?_⟩
  rw [add_mul]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (hf _ _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (wone w) (le_max_left _ _)) hC)
  · exact (hg _ _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (wone w) (le_max_right _ _)) hB)

theorem Growth.neg {ι : Type*} {f : ι→ℝ×ℝ→ℂ} (hf : Growth f) :
    Growth (fun i w => -f i w) := by simpa only [Growth,norm_neg] using hf

theorem Growth.sub {ι : Type*} {f g : ι→ℝ×ℝ→ℂ} (hf : Growth f) (hg : Growth g) :
    Growth (fun i w => f i w-g i w) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem Growth.pow {ι : Type*} {f : ι→ℝ×ℝ→ℂ} (hf : Growth f) (k : ℕ) :
    Growth (fun i w => f i w^k) := by
  induction k with
  | zero => simpa using (Growth.const (ι:=ι) 1)
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem Growth.first {ι : Type*} : Growth (fun (_ : ι) (w : ℝ×ℝ) => (w.1:ℂ)) := by
  refine ⟨1,by norm_num,1,fun i w => ?_⟩
  simp only [Complex.norm_real,Real.norm_eq_abs,pow_one,one_mul,weight]
  nlinarith [abs_nonneg w.2,mul_nonneg (abs_nonneg w.1) (abs_nonneg w.2)]
theorem Growth.second {ι : Type*} : Growth (fun (_ : ι) (w : ℝ×ℝ) => (w.2:ℂ)) := by
  refine ⟨1,by norm_num,1,fun i w => ?_⟩
  simp only [Complex.norm_real,Real.norm_eq_abs,pow_one,one_mul,weight]
  nlinarith [abs_nonneg w.1,mul_nonneg (abs_nonneg w.1) (abs_nonneg w.2)]

theorem disk_gap {R : ℝ} (hR : 0≤R) (hR' : R<1) : 0<1-R^2 := by nlinarith [mul_pos (show 0<1-R by linarith) (show 0<1+R by linarith)]

abbrev Disc (R : ℝ) := {z : ℂ // ‖z‖≤R}
end CQPriceGrowth


open GrothendieckLB.Supplement.CQPrice
namespace CQBellLinear
set_option maxHeartbeats 2500000
noncomputable def thr' (x : ℝ) := delta*(3*x^2-3)
theorem dthreshold (x : ℝ) : HasDerivAt threshold (thr' x) x := by
  apply ((((hasDerivAt_id x).pow 3).sub ((hasDerivAt_id x).const_mul 3)).const_mul delta).congr_deriv
  simp [thr',id_eq]
noncomputable def piece (e : Piece) (x : ℝ) := (e.c:ℝ)*x^e.b*(x^2-1)^e.l
noncomputable def dPiece (e : Piece) (x : ℝ) :=
  (e.c:ℝ)*((e.b:ℝ)*x^(e.b-1))*(x^2-1)^e.l+
    (e.c:ℝ)*x^e.b*((e.l:ℝ)*(x^2-1)^(e.l-1)*(2*x))
private theorem hasPiece (e : Piece) (x : ℝ) : HasDerivAt (piece e) (dPiece e x) x := by
  have d := ((hasDerivAt_pow 2 x).sub_const 1).pow e.l
  apply (((hasDerivAt_pow e.b x).const_mul (e.c:ℝ)).mul d).congr_deriv
  dsimp [dPiece];ring
noncomputable def bell' (a i : ℕ) (x : ℝ) := delta^i*((pieces a i).map (fun e => dPiece e x)).sum
private theorem sumPiece (ps : List Piece) (x : ℝ) :
    HasDerivAt (fun t => (ps.map (fun e => piece e t)).sum) ((ps.map (fun e => dPiece e x)).sum) x := by
  induction ps with
  | nil => simpa using hasDerivAt_const x (0:ℝ)
  | cons e ps ih => exact (hasPiece e x).add ih
theorem dbell (a i : ℕ) (x : ℝ) : HasDerivAt (bell a i) (bell' a i x) x := (sumPiece (pieces a i) x).const_mul _
def valid (p a : ℕ) := (List.range (a+1)).filter (fun i => decide (0<bellUnits a i ∧ 0<p+i))

noncomputable def weighted (ls : List ℕ) (p a : ℕ) (x : ℝ) (T : ℕ→ℂ) :=
  (ls.map (fun i => (bell a i x:ℂ)*T (p+i-1))).sum
noncomputable def lin (p a : ℕ) := weighted (valid p a) p a

theorem weighted_param {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    (ls : List ℕ) (p a : ℕ) (x : ℝ) (z : 𝕜) (f : ℕ→𝕜→ℂ) (g : ℕ→ℂ) (h : ∀ m,HasDerivAt (f m) (g m) z) :
    HasDerivAt (fun w => weighted ls p a x (fun m => f m w)) (weighted ls p a x g) z := by
  induction ls with
  | nil => simpa [weighted] using hasDerivAt_const z (0:ℂ)
  | cons i ls ih => exact ((h _).const_mul (bell a i x:ℂ)).add ih
theorem lin_param {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    (p a : ℕ) (x : ℝ) (z : 𝕜) (f : ℕ→𝕜→ℂ) (g : ℕ→ℂ) (h : ∀ m,HasDerivAt (f m) (g m) z) :
    HasDerivAt (fun w => lin p a x (fun m => f m w)) (lin p a x g) z := weighted_param _ _ _ _ _ _ _ h

theorem weighted_scale (ls : List ℕ) (p a : ℕ) (x : ℝ) (c : ℂ) (T : ℕ→ℂ) :
    weighted ls p a x (fun m => c*T m)=c*weighted ls p a x T := by
  induction ls with
  | nil => simp [weighted]
  | cons i ls ih =>
    simp only [weighted,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih];ring

theorem lin_scale (p a : ℕ) (x : ℝ) (c : ℂ) (T : ℕ→ℂ) :
    lin p a x (fun m => c*T m)=c*lin p a x T := weighted_scale _ _ _ _ _ _

noncomputable def diffLin (ls : List ℕ) (p a : ℕ) (x : ℝ) (T : ℕ→ℂ) :=
  (ls.map (fun i => (bell' a i x:ℂ)*T (p+i-1) + (bell a i x:ℂ)*((thr' x:ℂ)*T (p+i-1+1)))).sum

private theorem diff_weight (ls : List ℕ) (p a : ℕ) (x : ℝ) (T : ℕ→ℝ→ℂ)
    (h : ∀ m, HasDerivAt (T m) ((thr' x:ℂ)*T (m+1) x) x) :
    HasDerivAt (fun t : ℝ => weighted ls p a t (fun m => T m t)) (diffLin ls p a x (fun m => T m x)) x := by
  induction ls with
  | nil => simpa [weighted,diffLin] using hasDerivAt_const x (0:ℂ)
  | cons i ls ih => exact (((dbell a i x).ofReal_comp).mul (h _)).add ih

private theorem der0_1 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 0 1) 0 1 x T=lin 0 2 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der0_2 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 0 2) 0 2 x T=lin 0 3 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der0_3 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 0 3) 0 3 x T=lin 0 4 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der0_4 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 0 4) 0 4 x T=lin 0 5 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der1_0 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 1 0) 1 0 x T=lin 1 1 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der1_1 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 1 1) 1 1 x T=lin 1 2 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der1_2 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 1 2) 1 2 x T=lin 1 3 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der1_3 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 1 3) 1 3 x T=lin 1 4 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der1_4 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 1 4) 1 4 x T=lin 1 5 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der2_0 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 2 0) 2 0 x T=lin 2 1 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der2_1 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 2 1) 2 1 x T=lin 2 2 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der2_2 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 2 2) 2 2 x T=lin 2 3 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der2_3 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 2 3) 2 3 x T=lin 2 4 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der3_0 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 3 0) 3 0 x T=lin 3 1 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der3_1 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 3 1) 3 1 x T=lin 3 2 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der3_2 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 3 2) 3 2 x T=lin 3 3 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der4_0 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 4 0) 4 0 x T=lin 4 1 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der4_1 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 4 1) 4 1 x T=lin 4 2 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp
private theorem der5_0 (x : ℝ) (T : ℕ→ℂ) : diffLin (valid 5 0) 5 0 x T=lin 5 1 x T := by
  norm_num [valid,lin,weighted,diffLin,bellUnits,List.range_succ,List.filter_append, bell,bell',dPiece,pieces,thr'] <;> push_cast <;> ring <;> simp

theorem derAll (p a : ℕ) (x : ℝ) (T : ℕ→ℂ) (hp : 0<p+a) (hpa : p+a≤5) (ha : a<5) : diffLin (valid p a) p a x T=lin p (a+1) x T := by
  have pC : p=0 ∨ p=1 ∨ p=2 ∨ p=3 ∨ p=4 ∨ p=5 := by omega
  have aC : a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 := by omega
  rcases pC with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases aC with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · exact der0_1 x T
  · exact der0_2 x T
  · exact der0_3 x T
  · exact der0_4 x T
  · omega
  · exact der1_0 x T
  · exact der1_1 x T
  · exact der1_2 x T
  · exact der1_3 x T
  · exact der1_4 x T
  · omega
  · exact der2_0 x T
  · exact der2_1 x T
  · exact der2_2 x T
  · exact der2_3 x T
  · omega
  · omega
  · exact der3_0 x T
  · exact der3_1 x T
  · exact der3_2 x T
  · omega
  · omega
  · omega
  · exact der4_0 x T
  · exact der4_1 x T
  · omega
  · omega
  · omega
  · omega
  · exact der5_0 x T
  · omega
  · omega
  · omega
  · omega
  · omega
private theorem shift0_1 (x : ℝ) (T : ℕ→ℂ) : lin 0 1 x (fun m => T (m+1))=lin 1 1 x T := by
  rfl
private theorem shift0_2 (x : ℝ) (T : ℕ→ℂ) : lin 0 2 x (fun m => T (m+1))=lin 1 2 x T := by
  rfl
private theorem shift0_3 (x : ℝ) (T : ℕ→ℂ) : lin 0 3 x (fun m => T (m+1))=lin 1 3 x T := by
  rfl
private theorem shift0_4 (x : ℝ) (T : ℕ→ℂ) : lin 0 4 x (fun m => T (m+1))=lin 1 4 x T := by
  rfl
private theorem shift0_5 (x : ℝ) (T : ℕ→ℂ) : lin 0 5 x (fun m => T (m+1))=lin 1 5 x T := by
  rfl
private theorem shift1_0 (x : ℝ) (T : ℕ→ℂ) : lin 1 0 x (fun m => T (m+1))=lin 2 0 x T := by
  rfl
private theorem shift1_1 (x : ℝ) (T : ℕ→ℂ) : lin 1 1 x (fun m => T (m+1))=lin 2 1 x T := by
  rfl
private theorem shift1_2 (x : ℝ) (T : ℕ→ℂ) : lin 1 2 x (fun m => T (m+1))=lin 2 2 x T := by
  rfl
private theorem shift1_3 (x : ℝ) (T : ℕ→ℂ) : lin 1 3 x (fun m => T (m+1))=lin 2 3 x T := by
  rfl
private theorem shift1_4 (x : ℝ) (T : ℕ→ℂ) : lin 1 4 x (fun m => T (m+1))=lin 2 4 x T := by
  rfl
private theorem shift2_0 (x : ℝ) (T : ℕ→ℂ) : lin 2 0 x (fun m => T (m+1))=lin 3 0 x T := by
  rfl
private theorem shift2_1 (x : ℝ) (T : ℕ→ℂ) : lin 2 1 x (fun m => T (m+1))=lin 3 1 x T := by
  rfl
private theorem shift2_2 (x : ℝ) (T : ℕ→ℂ) : lin 2 2 x (fun m => T (m+1))=lin 3 2 x T := by
  rfl
private theorem shift2_3 (x : ℝ) (T : ℕ→ℂ) : lin 2 3 x (fun m => T (m+1))=lin 3 3 x T := by
  rfl
private theorem shift3_0 (x : ℝ) (T : ℕ→ℂ) : lin 3 0 x (fun m => T (m+1))=lin 4 0 x T := by
  rfl
private theorem shift3_1 (x : ℝ) (T : ℕ→ℂ) : lin 3 1 x (fun m => T (m+1))=lin 4 1 x T := by
  rfl
private theorem shift3_2 (x : ℝ) (T : ℕ→ℂ) : lin 3 2 x (fun m => T (m+1))=lin 4 2 x T := by
  rfl
private theorem shift4_0 (x : ℝ) (T : ℕ→ℂ) : lin 4 0 x (fun m => T (m+1))=lin 5 0 x T := by
  rfl
private theorem shift4_1 (x : ℝ) (T : ℕ→ℂ) : lin 4 1 x (fun m => T (m+1))=lin 5 1 x T := by
  rfl
private theorem shift5_0 (x : ℝ) (T : ℕ→ℂ) : lin 5 0 x (fun m => T (m+1))=lin 6 0 x T := by
  rfl

theorem shiftAll (p a : ℕ) (x : ℝ) (T : ℕ→ℂ) (hp : 0<p+a) (hpa : p+a≤5) : lin p a x (fun m => T (m+1))=lin (p+1) a x T := by
  have pC : p=0 ∨ p=1 ∨ p=2 ∨ p=3 ∨ p=4 ∨ p=5 := by omega
  have aC : a=0 ∨ a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 := by omega
  rcases pC with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases aC with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · exact shift0_1 x T
  · exact shift0_2 x T
  · exact shift0_3 x T
  · exact shift0_4 x T
  · exact shift0_5 x T
  · exact shift1_0 x T
  · exact shift1_1 x T
  · exact shift1_2 x T
  · exact shift1_3 x T
  · exact shift1_4 x T
  · omega
  · exact shift2_0 x T
  · exact shift2_1 x T
  · exact shift2_2 x T
  · exact shift2_3 x T
  · omega
  · omega
  · exact shift3_0 x T
  · exact shift3_1 x T
  · exact shift3_2 x T
  · omega
  · omega
  · omega
  · exact shift4_0 x T
  · exact shift4_1 x T
  · omega
  · omega
  · omega
  · omega
  · exact shift5_0 x T
  · omega
  · omega
  · omega
  · omega
  · omega
theorem lin_spatial (p a : ℕ) (x : ℝ) (T : ℕ→ℝ→ℂ)
    (hp : 0<p+a) (hpa : p+a≤5) (ha : a<5)
    (h : ∀ m, HasDerivAt (T m) ((thr' x:ℂ)*T (m+1) x) x) :
    HasDerivAt (fun t : ℝ => lin p a t (fun m => T m t)) (lin p (a+1) x (fun m => T m x)) x := by
  rw [← derAll p a x _ hp hpa ha]
  exact diff_weight _ _ _ _ _ h

end CQBellLinear


open MeasureTheory GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice CQBellLinear CQPriceGrowth
namespace CQMixedIntegrals

noncomputable def V (z : ℂ) (w : ℝ×ℝ) (m n : ℕ) := fourierMoment (eval rho z) (threshold w.1) (threshold w.2) m n
noncomputable def T (p a b : ℕ) (z : ℂ) (w : ℝ×ℝ) := lin p a w.1 (fun m => lin p b w.2 (fun n => V z w m n))
noncomputable def dr (z : ℂ) := deriv (eval rho) z

private theorem rho_sum (ts : List (ℕ×ℤ)) (z : ℂ) (hz : ‖z‖≤1) (h : ∀ e∈ts,0<e.1) :
    ‖(ts.map (fun e => (e.2:ℂ)*z^e.1)).sum‖ ≤
      (ts.map (fun e => |(e.2:ℝ)|)).sum*‖z‖ := by
  induction ts with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons,List.sum_cons,add_mul]
    apply (norm_add_le _ _).trans
    apply add_le_add _ (ih fun j hj => h j (by simp [hj]))
    rw [norm_mul,norm_pow,show ‖(e.2:ℂ)‖=|(e.2:ℝ)| by norm_cast]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (h e (by simp)))
    rw [hj,pow_succ]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)

theorem rho_norm (z : ℂ) (hz : ‖z‖<1) : ‖eval rho z‖≤‖z‖ := by
  rw [eval,norm_div]
  have h : ∀ t∈rho.terms,0<t.1 := by simp [rho]
  have ht := rho_sum rho.terms z hz.le h
  norm_num [rho] at ht ⊢
  linarith

theorem rho_re (z : ℂ) (hz : ‖z‖<1) : |(eval rho z).re|<1 :=
  ((Complex.abs_re_le_norm _).trans (rho_norm z hz)).trans_lt hz

theorem rho_formula : eval rho=(fun z : ℂ => (10000000000000000*z-1162886658063376*z^3+27837347284321*z^5)/11190724005347697) := by
  funext z
  norm_num [eval,rho] <;> ring

theorem deriv_rho (z : ℂ) : HasDerivAt (eval rho) (dr z) z := by
  apply DifferentiableAt.hasDerivAt
  rw [rho_formula]
  fun_prop

theorem cont_dr : Continuous dr := by
  have h : ContDiff ℂ 1 (eval rho) := by rw [rho_formula];fun_prop
  exact h.continuous_deriv (by decide)

private theorem scaleV (z : ℂ) (hz : ‖z‖<1) (w : ℝ×ℝ) (m n : ℕ) :
    HasDerivAt (fun t => V t w m n) (dr z*V z w (m+1) (n+1)) z := by
  have h := (cq_fourier_moment_derivatives _ (rho_re z hz) (threshold w.1) (threshold w.2) m n).1.comp z (deriv_rho z)
  simpa only [V,Function.comp_def,mul_comm] using h

private theorem dX_V (z : ℂ) (hz : ‖z‖<1) (x y : ℝ) (m n : ℕ) :
    HasDerivAt (fun X : ℝ => V z (X,y) m n) ((thr' x:ℂ)*V z (x,y) (m+1) n) x := by
  have h := (cq_fourier_moment_derivatives _ (rho_re z hz) (threshold x) (threshold y) m n).2.1.scomp x (dthreshold x)
  simpa only [V,Function.comp_def,Complex.real_smul] using h
private theorem dY_V (z : ℂ) (hz : ‖z‖<1) (x y : ℝ) (m n : ℕ) :
    HasDerivAt (fun Y : ℝ => V z (x,Y) m n) ((thr' y:ℂ)*V z (x,y) m (n+1)) y := by
  have h := (cq_fourier_moment_derivatives _ (rho_re z hz) (threshold x) (threshold y) m n).2.2.1.scomp y (dthreshold y)
  simpa only [V,Function.comp_def,Complex.real_smul] using h

theorem param_T (p a : ℕ) (hp : 0<p+a) (hpa : p+a≤5) (z : ℂ) (hz : ‖z‖<1) (w : ℝ×ℝ) :
    HasDerivAt (fun t => T p a a t w) (dr z*T (p+1) a a z w) z := by
  have inner (m : ℕ) : HasDerivAt (fun t => lin p a w.2 (fun n => V t w m n))
      (dr z*lin (p+1) a w.2 (fun n => V z w (m+1) n)) z := by
    apply (lin_param p a w.2 z (fun n t => V t w m n) _ (fun n => scaleV z hz w m n)).congr_deriv
    rw [lin_scale,shiftAll p a _ _ hp hpa]
  apply (lin_param p a w.1 z _ _ inner).congr_deriv
  rw [lin_scale]
  exact congrArg (fun v => dr z*v) (shiftAll p a w.1 (fun m => lin (p+1) a w.2 (fun n => V z w m n)) hp hpa)

theorem spatialX_T (p a b : ℕ) (hp : 0<p+a) (hpa : p+a≤5) (ha : a<5)
    (z : ℂ) (hz : ‖z‖<1) (x y : ℝ) :
    HasDerivAt (fun X : ℝ => T p a b z (X,y)) (T p (a+1) b z (x,y)) x := by
  apply lin_spatial p a x (fun m X => lin p b y (fun n => V z (X,y) m n)) hp hpa ha
  intro m
  apply (lin_param p b y x (fun n X => V z (X,y) m n) _ (fun n => dX_V z hz x y m n)).congr_deriv
  exact lin_scale _ _ _ _ _

theorem spatialY_T (p a b : ℕ) (hp : 0<p+b) (hpb : p+b≤5) (hb : b<5)
    (z : ℂ) (hz : ‖z‖<1) (x y : ℝ) :
    HasDerivAt (fun Y : ℝ => T p a b z (x,Y)) (T p a (b+1) z (x,y)) y := by
  apply lin_param p a x y (fun m Y => lin p b Y (fun n => V z (x,Y) m n))
  intro m
  exact lin_spatial p b y _ hp hpb hb (fun n => dY_V z hz x y m n)

end CQMixedIntegrals


open MeasureTheory GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice CQBellLinear CQPriceGrowth
namespace CQMixedIntegrals
set_option maxHeartbeats 1200000

theorem growth_V {R : ℝ} (hR : 0≤R) (hlt : R<1) (m n : ℕ) : Growth (fun i : Disc R => fun w => V i.val w m n) := by
  let v := (Real.sqrt (1-R^2))⁻¹
  let M := Real.sqrt ((momentDF m:ℝ)*(momentDF n:ℝ))
  apply Growth.of_bound (C:=v^(m+n+1)*M) (by dsimp [v,M];positivity)
  intro i w
  have hi := i.property.trans_lt hlt
  have h := cq_gaussian_fourier_moment_bound _ (rho_re i.val hi) (threshold w.1) (threshold w.2) m n
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply pow_le_pow_left₀ (by positivity)
  apply inv_anti₀ (Real.sqrt_pos.mpr (disk_gap hR hlt))
  apply Real.sqrt_le_sqrt
  have hh := ((Complex.abs_re_le_norm _).trans (rho_norm i.val hi)).trans i.property
  have hh₂ := pow_le_pow_left₀ (abs_nonneg _) hh 2
  rw [sq_abs] at hh₂
  linarith

theorem cont_V (z : ℂ) (hz : ‖z‖<1) (m n : ℕ) : Continuous (fun w => V z w m n) := by
  have hc := (cq_fourier_moment_derivatives _ (rho_re z hz) 0 0 m n).2.2.2
  have h : Continuous (fun w : ℝ×ℝ => (threshold w.1,threshold w.2)) := by unfold threshold;fun_prop
  unfold V
  simpa only [Function.comp_def] using hc.comp h

theorem growth_dr {R : ℝ} (hR : 0≤R) : Growth (fun i : Disc R => fun _ => dr i.val) := by
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:ℂ) R).bddAbove_image cont_dr.norm.continuousOn
  apply Growth.of_bound (C:=max B 0) (le_max_right _ _)
  intro i _
  exact (hB (Set.mem_image_of_mem _ (show i.val∈Metric.closedBall (0:ℂ) R by simpa using i.property))).trans (le_max_left _ _)

private theorem growth_sum {ι κ : Type*} (ls : List κ) (f : κ→ι→ℝ×ℝ→ℂ)
    (h : ∀ k,Growth (f k)) : Growth (fun i w => (ls.map (fun k => f k i w)).sum) := by
  induction ls with
  | nil => exact Growth.const 0
  | cons k ls ih => exact (h k).add ih

private theorem coeSum (ls : List ℝ) : (ls.sum:ℂ)=(ls.map (fun r : ℝ => (r:ℂ))).sum := by
  induction ls with
  | nil => simp
  | cons x xs ih => simp only [List.sum_cons,Complex.ofReal_add,List.map_cons,ih]

private theorem growth_bell {ι : Type*} (X : ℝ×ℝ→ℝ) (hX : Growth (fun (_ : ι) w => (X w:ℂ))) (a j : ℕ) :
    Growth (fun (_ : ι) w => (bell a j (X w):ℂ)) := by
  have hbase := ((hX.pow 2).sub (Growth.const 1))
  have h (e : Piece) := (((Growth.const (e.c:ℂ)).mul (hX.pow e.b)).mul (hbase.pow e.l))
  have hp := (Growth.const ((delta:ℂ)^j)).mul (growth_sum (pieces a j) _ h)
  simpa [bell,coeSum,List.map_map,Function.comp_def] using hp

private theorem growth_lin {ι : Type*} (X : ℝ×ℝ→ℝ) (hX : Growth (fun (_ : ι) w => (X w:ℂ)))
    (p a : ℕ) (F : ℕ→ι→ℝ×ℝ→ℂ) (h : ∀ m,Growth (F m)) :
    Growth (fun i w => lin p a (X w) (fun m => F m i w)) :=
  growth_sum (valid p a) _ (fun j => (growth_bell X hX a j).mul (h (p+j-1)))

theorem growth_T {R : ℝ} (hR : 0≤R) (hR' : R<1) (p a b : ℕ) :
    Growth (fun i : Disc R => T p a b i.val) :=
  growth_lin _ Growth.first p a _ (fun m => growth_lin _ Growth.second p b _ (fun n => growth_V hR hR' m n))

private theorem cont_lin (X : ℝ×ℝ→ℝ) (hX : Continuous X) (p a : ℕ) (F : ℕ→ℝ×ℝ→ℂ)
    (h : ∀ m,Continuous (F m)) : Continuous (fun w => lin p a (X w) (fun m => F m w)) := by
  suffices ∀ ls : List ℕ, Continuous (fun w => weighted ls p a (X w) (fun m => F m w)) by apply this
  intro ls
  induction ls with
  | nil => exact continuous_const
  | cons j ls ih =>
    apply Continuous.add _ ih
    apply Continuous.mul _ (h _)
    have hb : Differentiable ℝ (bell a j) := fun x => (dbell a j x).differentiableAt
    exact Complex.continuous_ofReal.comp (hb.continuous.comp hX)

theorem cont_T (z : ℂ) (hz : ‖z‖<1) (p a b : ℕ) : Continuous (T p a b z) :=
  cont_lin _ continuous_fst p a _ (fun m => cont_lin _ continuous_snd p b _ (fun n => cont_V z hz m n))
end CQMixedIntegrals


open MeasureTheory GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice CQBellLinear CQPriceGrowth CQMixedIntegrals
namespace CQMixedIntegrals
private theorem valid_pair (p a : ℕ) (hp : p≤5) (ha : a≤5) :
    indices p a=(valid p a).flatMap (fun i => (valid p a).map (fun j => (i,j))) := by
  interval_cases p <;> interval_cases a <;> decide +kernel

private theorem sum_inner (b : ℂ) (js : List ℕ) (c T : ℕ→ℂ) :
    (js.map (fun j => (b*c j)*T j)).sum=b*(js.map (fun j => c j*T j)).sum := by
  induction js with
  | nil => simp
  | cons j js ih => simp only [List.map_cons,List.sum_cons,ih,mul_add];ring

private theorem sum_pairs (is js : List ℕ) (b c : ℕ→ℂ) (U : ℕ→ℕ→ℂ) :
    ((is.flatMap (fun i => js.map (fun j => (i,j)))).map (fun ij => (b ij.1*c ij.2)*U ij.1 ij.2)).sum =
      (is.map (fun i => b i*(js.map (fun j => c j*U i j)).sum)).sum := by
  induction is with
  | nil => simp
  | cons i is ih =>
    simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_map,Function.comp_def,List.map_cons,List.sum_cons]
    rw [sum_inner,ih]

theorem partial_eq (p a : ℕ) (hp : p≤5) (ha : a≤5) (z : ℂ) :
    partialTerm z p a=∫ w : ℝ×ℝ, density (-z) w.1 w.2*T p a a z w := by
  unfold partialTerm
  apply integral_congr_ae
  filter_upwards with w
  congr 1
  rw [valid_pair p a hp ha]
  simp only [Complex.ofReal_mul]
  exact sum_pairs (valid p a) (valid p a) (fun i => (bell a i w.1:ℂ)) (fun j => (bell a j w.2:ℂ))
    (fun i j => V z w (p+i-1) (p+j-1))

end CQMixedIntegrals

theorem solution (p a : ℕ) (hpos : 0<p+a) (hlt : p+a<5) (z : ℂ) (hz : ‖z‖<1) :
    HasDerivAt (fun w => partialTerm w p a)
      (deriv (eval rho) z * partialTerm z (p+1) a - partialTerm z p (a+1)) z := by
  let f:=T p a a
  let g:=fun t w => dr t*T (p+1) a a t w
  let fx:=T p (a+1) a
  let fxy:=T p (a+1) (a+1)
  have hf (t : ℂ) (ht : ‖t‖<1) : Measurable (f t) := (cont_T _ ht _ _ _).measurable
  have hg (t : ℂ) (ht : ‖t‖<1) : Measurable (g t) := (continuous_const.mul (cont_T _ ht _ _ _)).measurable
  have hfx (t : ℂ) (ht : ‖t‖<1) : Measurable (fx t) := (cont_T _ ht _ _ _).measurable
  have hfxy (t : ℂ) (ht : ‖t‖<1) : Measurable (fxy t) := (cont_T _ ht _ _ _).measurable
  have mF (H) (h : H∈[f,g,fx,fxy]) : ∀ t : ℂ, ‖t‖<1 → Measurable (H t) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl
    exacts [hf,hg,hfx,hfxy]
  have gF (H) (h : H∈[f,g,fx,fxy]) (R : ℝ) (hR : 0≤R) (hR' : R<1) :
      ∃ C : ℝ, 0≤C ∧ ∃ k : ℕ, ∀ t : ℂ, ‖t‖≤R → ∀ w : ℝ×ℝ, ‖H t w‖≤ C*((1+|w.1|)*(1+|w.2|))^k := by
    have G : Growth (fun i : Disc R => H i.val) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl
      exacts [growth_T hR hR' _ _ _, (growth_dr hR).mul (growth_T hR hR' _ _ _),growth_T hR hR' _ _ _,growth_T hR hR' _ _ _]
    obtain ⟨C,hC,k,hk⟩ := G
    exact ⟨C,hC,k,fun t ht w => hk ⟨t,ht⟩ w⟩
  have h := cq_gaussian_price_under_integral f g fx fxy z hz mF gF
    (fun t ht w => param_T p a hpos hlt.le t ht w)
    (spatialX_T p a a hpos hlt.le (by omega) z hz)
    (spatialY_T p (a+1) a hpos hlt.le (by omega) z hz)
  have hbase : (fun w => partialTerm w p a) = (fun t : ℂ => ∫ w : ℝ×ℝ, density (-t) w.1 w.2*f t w) :=
    funext (partial_eq p a (by omega) (by omega))
  rw [hbase,partial_eq (p+1) a (by omega) (by omega),partial_eq p (a+1) (by omega) (by omega)]
  apply h.congr_deriv
  dsimp only [g,fxy,dr]
  rw [← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with w
  ring
