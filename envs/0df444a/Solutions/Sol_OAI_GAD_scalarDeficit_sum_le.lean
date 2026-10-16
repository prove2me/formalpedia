-- Prove2me | solution 1 for OAI.GAD.scalarDeficit_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:51:07.666194+00:00
-- url     : https://prove2.me/submissions/9d9dcb72-b6ef-4bd7-ab74-cc5c26919563

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/ScalarDeficit.lean:L308-L324
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.scalarDeficit_sum_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Theorems.Thm_OAI_GAD_blockLogDet_scalar
import Theorems.Thm_OAI_GAD_convexOn_blockLogDet
import Theorems.Thm_OAI_GAD_scalarDeficit_weighted_le_of_log_le

-- ---- from OAI.InformationTheory.AmplitudeDamping.ScalarDeficit ----
namespace OAI

universe u_1 u_2

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology

open scoped BigOperators ComplexOrder
open Matrix Set
namespace GAD

theorem blockLambda_properties {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ blockLambdaPlus x y z ∧ 0 ≤ blockLambdaMinus x y z ∧
    blockLambdaPlus x y z + blockLambdaMinus x y z = x + y + z ∧
    blockLambdaPlus x y z * blockLambdaMinus x y z = y*z := by
  have hd : 0 ≤ (x+y+z)^2 - 4*y*z := by
    nlinarith [sq_nonneg (y-z), mul_nonneg hx (by linarith : 0 ≤ y+z)]
  have hs := Real.sq_sqrt hd
  have hsr := Real.sqrt_nonneg ((x+y+z)^2-4*y*z)
  have hle : Real.sqrt ((x+y+z)^2-4*y*z) ≤ x+y+z := by
    nlinarith [mul_nonneg hy hz]
  dsimp [blockLambdaPlus, blockLambdaMinus]
  refine ⟨by positivity, by linarith, by ring, ?_⟩
  nlinarith

end GAD
open scoped BigOperators ComplexOrder
open Matrix Set
namespace GAD

theorem convexOn_log_one_add_div_mul {q : ℝ} (hq : 0 ≤ q) :
    ConvexOn ℝ {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2}
      (fun p ↦ Real.log (1 + q/(p.1*p.2))) := by
  let Z : Matrix (Fin 1) (Fin 1) ℂ := Matrix.diagonal (fun _ ↦ (Real.sqrt q : ℂ))
  let diag (d : ℝ) : Matrix (Fin 1) (Fin 1) ℂ := Matrix.diagonal (fun _ ↦ (d : ℂ))
  have hp {d : ℝ} (hd : 0 < d) : (diag d).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    exact_mod_cast hd
  have hl (a b d e : ℝ) : a • diag d + b • diag e = diag (a*d+b*e) := by
    ext i j
    fin_cases i; fin_cases j
    simp [diag]
  refine ⟨?_, ?_⟩
  · intro p hp q hq a b ha hb hab
    exact ⟨convex_Ioi (𝕜 := ℝ) (0 : ℝ) hp.1 hq.1 ha hb hab, convex_Ioi (𝕜 := ℝ) (0 : ℝ) hp.2 hq.2 ha hb hab⟩
  intro p hp' v hv a b ha hb hab
  have h := (convexOn_blockLogDet Z).2 (x := (diag p.1,diag p.2)) (y := (diag v.1,diag v.2))
    ⟨hp hp'.1, hp hp'.2⟩ ⟨hp hv.1, hp hv.2⟩ ha hb hab
  have hd : 0 < a*p.1+b*v.1 := convex_Ioi (𝕜 := ℝ) (0 : ℝ) hp'.1 hv.1 ha hb hab
  have he : 0 < a*p.2+b*v.2 := convex_Ioi (𝕜 := ℝ) (0 : ℝ) hp'.2 hv.2 ha hb hab
  change blockLogDet Z (a • diag p.1+b • diag v.1) (a • diag p.2+b • diag v.2) ≤ _ at h
  rw [hl, hl] at h
  simpa only [Z, diag, blockLogDet_scalar hq hp'.1 hp'.2,
    blockLogDet_scalar hq hv.1 hv.2, blockLogDet_scalar hq hd he,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using h

theorem concaveOn_deficitLog_one {t : ℝ} (ht : 0 < t) :
    ConcaveOn ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}
      (fun p ↦ deficitLog 1 p.1 p.2 t) := by
  refine ⟨?_, ?_⟩
  · intro p hp q hq a b ha hb _
    exact ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1),
       add_nonneg (mul_nonneg ha hp.2) (mul_nonneg hb hq.2)⟩
  intro p hp q hq a b ha hb hab
  have h := (convexOn_log_one_add_div_mul ht.le).2
    (x := (t+p.1,t+p.2)) (y := (t+q.1,t+q.2))
    ⟨by simpa using add_pos_of_pos_of_nonneg ht hp.1,
     by simpa using add_pos_of_pos_of_nonneg ht hp.2⟩
    ⟨by simpa using add_pos_of_pos_of_nonneg ht hq.1,
     by simpa using add_pos_of_pos_of_nonneg ht hq.2⟩ ha hb hab
  have he (u v : ℝ) : a*(t+u)+b*(t+v) = t+(a*u+b*v) := by nlinarith [hab]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    he, deficitLog, mul_one] at h ⊢
  nlinarith [congrArg (fun v : ℝ ↦ v * Real.log (1+1/t)) hab]

theorem concaveOn_scalarDeficit_one :
    ConcaveOn ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}
      (fun p ↦ scalarDeficit 1 p.1 p.2) := by
  refine ⟨?_, ?_⟩
  · intro p hp q hq a b ha hb _
    exact ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1),
       add_nonneg (mul_nonneg ha hp.2) (mul_nonneg hb hq.2)⟩
  intro p hp q hq a b ha hb hab
  have hy : ∀ i : Fin 3, 0 ≤ (![p.1,q.1,a*p.1+b*q.1] : Fin 3 → ℝ) i := by
    intro i; fin_cases i <;> simp
    · exact hp.1
    · exact hq.1
    · exact add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1)
  have hz : ∀ i : Fin 3, 0 ≤ (![p.2,q.2,a*p.2+b*q.2] : Fin 3 → ℝ) i := by
    intro i; fin_cases i <;> simp
    · exact hp.2
    · exact hq.2
    · exact add_nonneg (mul_nonneg ha hp.2) (mul_nonneg hb hq.2)
  have h := scalarDeficit_weighted_le_of_log_le ![a,b,-1] (fun _ : Fin 3 ↦ 1)
    ![p.1,q.1,a*p.1+b*q.1] ![p.2,q.2,a*p.2+b*q.2] (by intro i; positivity) hy hz
    (by
      intro t ht
      have h := (concaveOn_deficitLog_one ht).2 hp hq ha hb hab
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_fin_one, neg_one_mul, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h ⊢
      linarith)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, neg_one_mul, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h ⊢
  linarith

theorem deficitLog_mono {x y z y' z' t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hyy : y ≤ y') (hzz : z ≤ z') (ht : 0 < t) :
    deficitLog x y z t ≤ deficitLog x y' z' t := by
  have hden : (t+y)*(t+z) ≤ (t+y')*(t+z') :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hdiv := div_le_div_of_nonneg_left (mul_nonneg ht.le hx)
    (by positivity : 0 < (t+y)*(t+z)) hden
  have hlog := Real.strictMonoOn_log.monotoneOn
    (show 1+t*x/((t+y')*(t+z')) ∈ Ioi 0 by change (0 : ℝ) < _; have : 0 ≤ y' := hy.trans hyy; have : 0 ≤ z' := hz.trans hzz; positivity)
    (show 1+t*x/((t+y)*(t+z)) ∈ Ioi 0 by change (0 : ℝ) < _; positivity)
    (add_le_add_right hdiv 1)
  dsimp only [deficitLog]
  linarith

theorem scalarDeficit_mono {x y z y' z' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hyy : y ≤ y') (hzz : z ≤ z') : scalarDeficit x y z ≤ scalarDeficit x y' z' := by
  have h := scalarDeficit_weighted_le_of_log_le ![1,-1] (fun _ : Fin 2 ↦ x)
    ![y,y'] ![z,z'] (fun _ ↦ hx)
    (by intro i; fin_cases i <;> simp; exact hy; exact hy.trans hyy)
    (by intro i; fin_cases i <;> simp; exact hz; exact hz.trans hzz)
    (by
      intro t ht
      have h := deficitLog_mono hx hy hz hyy hzz ht
      simpa [Fin.sum_univ_succ] using sub_nonpos.mpr h)
  simpa [Fin.sum_univ_succ, sub_nonpos] using h

theorem scalarDeficit_zero {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    scalarDeficit 0 y z = 0 := by
  have h (c : ℝ) : c * scalarDeficit 0 y z ≤ 0 := by
    have h := scalarDeficit_weighted_le_of_log_le (fun _ : Fin 1 ↦ c) (fun _ ↦ 0)
      (fun _ ↦ y) (fun _ ↦ z) (fun _ ↦ le_rfl) (fun _ ↦ hy) (fun _ ↦ hz)
      (by intro t ht; simp [deficitLog])
    simpa using h
  have hp := h 1
  have hm := h (-1)
  linarith

theorem scalarDeficit_homogeneous {a x y z : ℝ} (ha : 0 ≤ a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    scalarDeficit (a*x) (a*y) (a*z) = a * scalarDeficit x y z := by
  have hs : Real.sqrt ((a*x+a*y+a*z)^2-4*(a*y)*(a*z)) =
      a * Real.sqrt ((x+y+z)^2-4*y*z) := by
    rw [show (a*x+a*y+a*z)^2-4*(a*y)*(a*z) = a^2*((x+y+z)^2-4*y*z) by ring,
      Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  have hp : blockLambdaPlus (a*x) (a*y) (a*z) = a * blockLambdaPlus x y z := by
    dsimp [blockLambdaPlus]; rw [hs]; ring
  have hm : blockLambdaMinus (a*x) (a*y) (a*z) = a * blockLambdaMinus x y z := by
    dsimp [blockLambdaMinus]; rw [hs]; ring
  have hsum := (blockLambda_properties hx hy hz).2.2.1
  simp only [scalarDeficit, hp, hm, Real.negMulLog_mul]
  nlinarith [congrArg (fun v : ℝ ↦ v * Real.negMulLog a) hsum]

theorem scalarDeficit_perspective {x y z : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    scalarDeficit x y z = x * scalarDeficit 1 (y/x) (z/x) := by
  have h := scalarDeficit_homogeneous hx.le (show (0 : ℝ) ≤ 1 by norm_num)
    (div_nonneg hy hx.le) (div_nonneg hz hx.le)
  simpa [mul_div_cancel₀ _ hx.ne'] using h

theorem scalarDeficit_superadd {x y z x' y' z' : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hx' : 0 ≤ x') (hy' : 0 ≤ y') (hz' : 0 ≤ z') :
    scalarDeficit x y z + scalarDeficit x' y' z' ≤
      scalarDeficit (x+x') (y+y') (z+z') := by
  by_cases h0 : x = 0
  · subst x
    rw [scalarDeficit_zero hy hz, zero_add, zero_add]
    exact scalarDeficit_mono hx' hy' hz' (by linarith) (by linarith)
  by_cases h0' : x' = 0
  · subst x'
    rw [scalarDeficit_zero hy' hz', add_zero, add_zero]
    exact scalarDeficit_mono hx hy hz (by linarith) (by linarith)
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm h0)
  have hxp' : 0 < x' := lt_of_le_of_ne hx' (Ne.symm h0')
  have hs : 0 < x+x' := add_pos hxp hxp'
  have h := concaveOn_scalarDeficit_one.2
    (x := (y/x,z/x)) (y := (y'/x',z'/x'))
    ⟨div_nonneg hy hx, div_nonneg hz hx⟩ ⟨div_nonneg hy' hx', div_nonneg hz' hx'⟩
    (div_nonneg hx hs.le) (div_nonneg hx' hs.le)
    (show x/(x+x') + x'/(x+x') = 1 by field_simp)
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h
  have he (a b : ℝ) : x/(x+x')*(a/x) + x'/(x+x')*(b/x') = (a+b)/(x+x') := by
    field_simp
  rw [he, he] at h
  have hm := mul_le_mul_of_nonneg_left h hs.le
  rw [scalarDeficit_perspective hxp hy hz,
    scalarDeficit_perspective hxp' hy' hz',
    scalarDeficit_perspective hs (add_nonneg hy hy') (add_nonneg hz hz')]
  convert hm using 1 <;> first | rfl | field_simp

theorem scalarDeficit_sum_le {ι : Type u_2} (s : Finset ι) (x y z : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∑ i ∈ s, scalarDeficit (x i) (y i) (z i) ≤
      scalarDeficit (∑ i ∈ s, x i) (∑ i ∈ s, y i) (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [scalarDeficit_zero (le_refl 0) (le_refl 0)]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hxs := fun j hj ↦ hx j (Finset.mem_insert_of_mem hj)
    have hys := fun j hj ↦ hy j (Finset.mem_insert_of_mem hj)
    have hzs := fun j hj ↦ hz j (Finset.mem_insert_of_mem hj)
    calc
      _ ≤ scalarDeficit (x i) (y i) (z i) + scalarDeficit (∑ j ∈ s, x j) (∑ j ∈ s, y j) (∑ j ∈ s, z j) := add_le_add le_rfl (ih hxs hys hzs)
      _ ≤ _ := scalarDeficit_superadd (hx i (Finset.mem_insert_self i s))
        (hy i (Finset.mem_insert_self i s)) (hz i (Finset.mem_insert_self i s))
        (Finset.sum_nonneg hxs) (Finset.sum_nonneg hys) (Finset.sum_nonneg hzs)

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder
open Matrix Set
open scoped BigOperators ComplexOrder
open Matrix Set


theorem solution : type_of% @_root_.OAI.GAD.scalarDeficit_sum_le := @_root_.OAI.GAD.scalarDeficit_sum_le
