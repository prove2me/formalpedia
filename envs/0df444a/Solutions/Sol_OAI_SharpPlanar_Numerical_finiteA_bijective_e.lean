-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.finiteA_bijective_e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T03:41:07.696975+00:00
-- url     : https://prove2.me/submissions/4be5a9b1-d3fe-45fd-9494-0f46f433f324
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098E126
import Theorems.Thm_OAI_SharpPlanar_D_0_e
import Theorems.Thm_OAI_SharpPlanar_D_1_e
import Theorems.Thm_OAI_SharpPlanar_D_3_e
import Theorems.Thm_OAI_SharpPlanar_D_4_e
import Theorems.Thm_OAI_SharpPlanar_D_7_e
import Theorems.Thm_OAI_SharpPlanar_D_9_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_Lmat_column_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_centralIndex_injective_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_centralV_norm_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectminus_lt_one_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectplus_lt_one_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_exteriorIndex_injective_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_lowExteriorIndex_injective_e
import Theorems.Thm_OAI_SharpPlanar_Numerical_signedVU_norm_e
import Theorems.Thm_OAI_SharpPlanar_Q_0_e
import Theorems.Thm_OAI_SharpPlanar_Q_1_e
import Theorems.Thm_OAI_SharpPlanar_Q_3_e
import Theorems.Thm_OAI_SharpPlanar_Q_4_e
import Theorems.Thm_OAI_SharpPlanar_Q_7_e
import Theorems.Thm_OAI_SharpPlanar_Q_9_e
import Theorems.Thm_OAI_SharpPlanar_S_apply_e
import Theorems.Thm_OAI_SharpPlanar_X_summable_pairs_e
import Theorems.Thm_OAI_SharpPlanar_b_pos_e
import Theorems.Thm_OAI_SharpPlanar_b_sq_e
import Theorems.Thm_OAI_SharpPlanar_dampingCap_pos_e
import Theorems.Thm_OAI_SharpPlanar_decay_pieceBase_e
import Theorems.Thm_OAI_SharpPlanar_densityCap_nonneg_e
import Theorems.Thm_OAI_SharpPlanar_finiteEmbedding_apply_e
import Theorems.Thm_OAI_SharpPlanar_finiteEmbedding_norm_e
import Theorems.Thm_OAI_SharpPlanar_finiteRestriction_apply_e
import Theorems.Thm_OAI_SharpPlanar_finiteRestriction_bound_e
import Theorems.Thm_OAI_SharpPlanar_l1Finite_norm_e
import Theorems.Thm_OAI_SharpPlanar_lambdaCap_nonneg_e
import Theorems.Thm_OAI_SharpPlanar_pi_fine_e
import Theorems.Thm_OAI_SharpPlanar_pieceBase_pos_e
import Theorems.Thm_OAI_SharpPlanar_pieceL_nonneg_e
import Theorems.Thm_OAI_SharpPlanar_pieceMass_le_e
import Theorems.Thm_OAI_SharpPlanar_pieceMass_nonneg_e
import Theorems.Thm_OAI_SharpPlanar_sharp_moment_bound_e
import Theorems.Thm_OAI_SharpPlanar_slopeCap_nonneg_e
import Theorems.Thm_OAI_SharpPlanar_tailScalar_summable_e
import Theorems.Thm_OAI_SharpPlanar_zCap_nonneg_e

section
-- module Solutions.OAIQ098_PP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar


lemma residue_lt {a : ℕ} (ha : a ∈ residues) : a < 12 := by
  simp only [residues, Finset.mem_insert, Finset.mem_singleton] at ha
  omega

lemma Q_pos (n : ℕ) : 0 < Q n := by
  unfold Q
  apply mul_pos (sq_pos_of_pos (by positivity))
  apply Finset.prod_pos
  intro a ha
  have hane : a ≠ n % 12 := (Finset.mem_erase.mp ha).1
  have hal : a < 12 := residue_lt (Finset.mem_erase.mp ha).2
  have hnl : n % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hh1 : (-12 : ℝ) < ((n % 12 : ℕ) : ℝ) - a := by
    have ha' : (a : ℝ) < 12 := by exact_mod_cast hal
    have hn' : (0 : ℝ) ≤ ((n % 12 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hh2 : (((n % 12 : ℕ) : ℝ) - a) < 12 := by
    have hn' : ((n % 12 : ℕ) : ℝ) < 12 := by exact_mod_cast hnl
    have ha' : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    linarith
  have hs : Real.sin (Real.pi * (((n % 12 : ℕ) : ℝ) - a) / 12) ≠ 0 := by
    rw [ne_eq, Real.sin_eq_zero_iff_of_lt_of_lt
      (by nlinarith [Real.pi_pos, mul_pos Real.pi_pos (by linarith : (0 : ℝ) < ((n%12 : ℕ):ℝ)-a+12)])
      (by nlinarith [Real.pi_pos, mul_pos Real.pi_pos (by linarith : (0 : ℝ) < 12-(((n%12 : ℕ):ℝ)-a))])]
    apply div_ne_zero
    · apply mul_ne_zero Real.pi_ne_zero
      exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hane)
    · norm_num
  exact sq_pos_of_ne_zero (mul_ne_zero (by norm_num) hs)

lemma Q_mod (n : ℕ) : Q (n % 12) = Q n := by simp [Q]
lemma D_mod (n : ℕ) : D (n % 12) = D n := by simp [D]

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

lemma pieceMass_antitone (j : Fin 6) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    pieceMass j t ≤ pieceMass j s := by
  have ht : 0 ≤ t := hs.trans hst
  unfold pieceMass
  split_ifs with htz hsz hsz
  · rfl
  · exfalso
    have hz : slopeCap j*s=0 := by
      apply le_antisymm
      · calc
          _ ≤ slopeCap j*t := mul_le_mul_of_nonneg_left hst (slopeCap_nonneg_e _)
          _ = 0 := htz
      · exact mul_nonneg (slopeCap_nonneg_e _) hs
    exact hsz hz
  · exact min_le_left _ _
  · apply min_le_min_left
    apply one_div_le_one_div_of_le
    · have hh : 0 < slopeCap j*s := lt_of_le_of_ne (mul_nonneg (slopeCap_nonneg_e _) hs) (Ne.symm hsz)
      simpa only [mul_assoc] using mul_pos Real.pi_pos hh
    · exact mul_le_mul_of_nonneg_left hst (mul_nonneg Real.pi_pos.le (slopeCap_nonneg_e _))

lemma pieceL_shift_bound (j : Fin 6) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    pieceL j (s+t) ≤ Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*t)*pieceL j s := by
  have hm := pieceMass_antitone j hs (show s ≤ s+t by linarith)
  unfold pieceL
  rw [mul_add,Real.exp_add]
  calc
    _ ≤ lambdaCap ⟨j.val,by omega⟩*(Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)*
        Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*t))*pieceMass j s := by
      exact mul_le_mul_of_nonneg_left hm (mul_nonneg (lambdaCap_nonneg_e _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
    _ = _ := by ring

lemma pieceL_period_bound (j : Fin 6) {s : ℝ} (hs : 0 ≤ s) (k : ℕ) :
    pieceL j (s+12*k) ≤ (Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩))^k*pieceL j s := by
  have hh := pieceL_shift_bound j hs (by positivity : (0:ℝ) ≤ 12*k)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [← Real.exp_nat_mul]
  congr 2
  ring

end SharpPlanar

namespace SharpPlanar
open IntegerBasis


lemma periodic_geometric_sum {f : ℕ → ℝ} {q : ℝ} (hf : ∀ n, 0 ≤ f n)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hb : ∀ (a : Fin 12) (k : ℕ), f (k*12+a.val) ≤ q^k*f a.val) :
    Summable f ∧ (∑' n, f n) ≤ (∑ a : Fin 12, f a.val)/(1-q) := by
  let g : ℕ × Fin 12 → ℝ := fun p => q^p.1*f p.2.val
  have hgeom := (hasSum_geometric_of_lt_one hq0 hq1).summable
  have hg : Summable g := by
    apply (summable_prod_of_nonneg (fun p => mul_nonneg (pow_nonneg hq0 _) (hf _))).mpr
    constructor
    · intro k; exact summable_of_hasFiniteSupport (Set.toFinite _)
    · simpa only [g,← Finset.mul_sum,tsum_fintype] using hgeom.mul_right (∑ a : Fin 12, f a.val)
  have hh : Summable (fun p : ℕ × Fin 12 => f (p.1*12+p.2.val)) :=
    Summable.of_nonneg_of_le (fun _ => hf _) (fun p => hb p.2 p.1) hg
  have heq : (fun p : ℕ × Fin 12 => f (p.1*12+p.2.val)) = f ∘ (Nat.divModEquiv 12).symm := rfl
  have hs : Summable f := ((Nat.divModEquiv 12).symm.summable_iff).mp (heq ▸ hh)
  refine ⟨hs,?_⟩
  calc
    (∑' n, f n) = ∑' p : ℕ × Fin 12, f (p.1*12+p.2.val) := by
      exact ((Nat.divModEquiv 12).symm.tsum_eq f).symm
    _ ≤ ∑' p : ℕ × Fin 12, g p := hh.tsum_le_tsum (fun p => hb p.2 p.1) hg
    _ = (∑ a : Fin 12, f a.val)/(1-q) := by
      rw [hg.tsum_prod]
      simp only [g,tsum_fintype,← Finset.mul_sum,tsum_mul_right]
      rw [tsum_geometric_of_lt_one hq0 hq1]
      rw [div_eq_mul_inv]
      ring

lemma rowFactor_nonneg (j : Fin 6) (n : ℕ) : 0 ≤ rowFactor j n := by
  unfold rowFactor
  exact mul_nonneg (div_nonneg (by have hz := zCap_nonneg_e (⟨j.val,by omega⟩ : Fin 7); positivity) (Q_pos _).le) (densityCap_nonneg_e _)
lemma rowFactor_periodic (j : Fin 6) (n k : ℕ) : rowFactor j (n+12*k) = rowFactor j n := by
  have hmod : (n+12*k)%12 = n%12 := by omega
  unfold rowFactor Q D
  rw [hmod]
lemma rowPiece_nonneg (j : Fin 6) (n : ℕ) : 0 ≤ rowPiece j n := by
  unfold rowPiece
  split_ifs
  · exact mul_nonneg (rowFactor_nonneg _ _) (pieceL_nonneg_e _ (Nat.cast_nonneg _))
  · rfl
lemma rowPiece_period_bound (j : Fin 6) (n k : ℕ) :
    rowPiece j (n+12*k) ≤ (Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩))^k*rowPiece j n := by
  have hmod : (n+12*k)%12 = n%12 := by omega
  unfold rowPiece
  rw [hmod]
  split_ifs with hn
  · rw [rowFactor_periodic]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    calc
      _ ≤ rowFactor j n*((Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩))^k*pieceL j n) :=
        mul_le_mul_of_nonneg_left (pieceL_period_bound j (Nat.cast_nonneg _) k) (rowFactor_nonneg _ _)
      _ = _ := by ring
  · simp

lemma rowPiece_tail_sum (j : Fin 6) (N : ℕ) :
    Summable (fun n : ℕ => rowPiece j (N+1+n)) ∧
    (∑' n : ℕ, rowPiece j (N+1+n)) ≤
      (∑ a : Fin 12, rowPiece j (N+1+a.val)) /
        (1-Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩)) := by
  apply periodic_geometric_sum (fun _ => rowPiece_nonneg j _) (Real.exp_pos _).le
  · apply Real.exp_lt_one_iff.mpr
    have hg := dampingCap_pos_e (⟨j.val+1,by omega⟩ : Fin 7)
    nlinarith [Real.pi_pos,mul_pos Real.pi_pos hg]
  · intro a k
    convert rowPiece_period_bound j (N+1+a.val) k using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    omega

end SharpPlanar

namespace SharpPlanar
open IntegerBasis

lemma paired_jet_bound {q : ℝ} (hq : 0 < q) (d a b : ℝ) :
    |-a/q|+|(d*a-b)/q| ≤ ((1+|d|)*|a|+|b|)/q := by
  rw [abs_div,abs_div,abs_neg,abs_of_pos hq,← add_div]
  apply div_le_div_of_nonneg_right _ hq.le
  have hh := abs_sub (d*a) b
  rw [abs_mul] at hh
  nlinarith

lemma sharp_S_row (x : X) (n : Node) :
    |S x (n,false)|+|S x (n,true)| ≤ ‖x‖*(∑ j : Fin 6, rowPiece j n.val) := by
  have hs : (0:ℝ) ≤ n.val := Nat.cast_nonneg _
  have h0 := sharp_moment_bound_e (positiveData x) 0 hs
  have h1 := sharp_moment_bound_e (positiveData x) 1 hs
  simp only [positiveData,abs_zero,zero_add,zero_mul,add_zero,pow_zero,mul_one] at h0
  simp only [positiveData,abs_zero,zero_add,zero_mul,add_zero,pow_one] at h1
  have hq := Q_pos n.val
  rw [S_apply_e,S_apply_e]
  simp only [Scoords,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  calc
    _ ≤ ((1+|D n.val|)*|K (positiveData x) 0 n.val|+|K (positiveData x) 1 n.val|)/Q n.val :=
      paired_jet_bound hq _ _ _
    _ ≤ ((1+|D n.val|)*(‖x‖*(∑ j : Fin 6, densityCap j*pieceL j n.val))+
      ‖x‖*(∑ j : Fin 6, densityCap j*pieceL j n.val*(Real.pi*zCap ⟨j.val,by omega⟩)))/Q n.val := by
      exact div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left h0 (by positivity)) h1) hq.le
    _ = _ := by
      simp only [rowPiece,n.prop.2,ite_true, if_true,rowFactor,div_eq_mul_inv]
      rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

lemma rowTailNorm_summable (x : X) (N : ℕ) :
    Summable (fun n : {n : Node // N<n.val} => |x (n.val,false)|+|x (n.val,true)|) := by
  exact (X_summable_pairs_e x).subtype _

lemma natural_row_tail_summable (N : ℕ) :
    Summable (fun k : ℕ => ∑ j : Fin 6, rowPiece j (N+1+k)) := by
  exact (hasSum_sum (fun j _ => (rowPiece_tail_sum j N).1.hasSum)).summable

lemma natural_row_tail_bound (N : ℕ) :
    (∑' k : ℕ, ∑ j : Fin 6, rowPiece j (N+1+k)) ≤ rowTable N := by
  rw [Summable.tsum_finsetSum (fun j _ => (rowPiece_tail_sum j N).1)]
  exact Finset.sum_le_sum (fun j _ => (rowPiece_tail_sum j N).2)


theorem sharp_S_tail (x : X) (N : ℕ) : rowTailNorm (S x) N ≤ rowTable N*‖x‖ := by
  let f : ℕ → ℝ := fun k => ∑ j : Fin 6, rowPiece j (N+1+k)
  let index : {n : Node // N<n.val} → ℕ := fun n => n.val.val-(N+1)
  have hi : Function.Injective index := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have ha := a.prop; have hb := b.prop
    dsimp only [index] at hab
    omega
  have he (n : {n : Node // N<n.val}) : N+1+index n=n.val.val := by
    have hn := n.prop
    dsimp only [index]
    omega
  have hf : Summable f := natural_row_tail_summable N
  have hfn : ∀ n, 0 ≤ f n := fun n => Finset.sum_nonneg (fun _ _ => rowPiece_nonneg _ _)
  have hfi : Summable (f ∘ index) := hf.comp_injective hi
  have hsum : (∑' n, f (index n)) ≤ rowTable N :=
    (tsum_comp_le_tsum_of_inj hf hfn hi).trans (natural_row_tail_bound N)
  calc
    rowTailNorm (S x) N ≤ ∑' n : {n : Node // N<n.val}, ‖x‖*f (index n) := by
      apply (rowTailNorm_summable (S x) N).tsum_le_tsum _ (hfi.mul_left ‖x‖)
      intro n
      simpa only [Function.comp_apply, f, he] using sharp_S_row x n.val
    _ = ‖x‖*(∑' n, f (index n)) := tsum_mul_left
    _ ≤ ‖x‖*rowTable N := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = rowTable N*‖x‖ := mul_comm _ _

end SharpPlanar

namespace SharpPlanar
open IntegerBasis

lemma b_fine : (86602/100000:ℝ) < b ∧ b < 86603/100000 := by
  constructor <;> nlinarith [b_pos_e,b_sq_e]

lemma rowQLower_bound (n : ℕ) (hn : n%12 ∈ residues) : 0 < rowQLower n ∧ rowQLower n < Q n := by
  have hp := pi_fine_e
  have hb := b_fine
  have hp2 : (314159/100000:ℝ)^2 < Real.pi^2 := by nlinarith [Real.pi_pos]
  have hsmall : (2*(314159/100000:ℝ)^2/3)*(2-2*(86603/100000)) < (2*Real.pi^2/3)*(2-2*b) := by
    gcongr; linarith
  have hlarge : (2*(314159/100000:ℝ)^2/3)*(2+2*(86602/100000)) < (2*Real.pi^2/3)*(2+2*b) := by
    gcongr; linarith
  rw [← Q_mod]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn | hn | hn | hn | hn | hn <;>
    simp [rowQLower,hn,Q_0_e,Q_1_e,Q_3_e,Q_4_e,Q_7_e,Q_9_e] <;> nlinarith

lemma rowDUpper_bound (n : ℕ) (hn : n%12 ∈ residues) : |D n| < rowDUpper n := by
  have hp := pi_fine_e
  have hb := b_fine
  have hpb : Real.pi*b < (31416/10000:ℝ)*(86603/100000) := by gcongr <;> linarith
  have hpb0 : (314159/100000:ℝ)*(86602/100000) < Real.pi*b := by gcongr <;> linarith
  have hpbpos : 0 < Real.pi*b := mul_pos Real.pi_pos b_pos_e
  rw [← D_mod]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn | hn | hn | hn | hn | hn <;>
    norm_num [rowDUpper,hn]
  all_goals first | rw [D_0_e] | rw [D_1_e] | rw [D_3_e] | rw [D_4_e] | rw [D_7_e] | rw [D_9_e]
  all_goals apply abs_lt.mpr; constructor <;> nlinarith

end SharpPlanar

namespace SharpPlanar
open IntegerBasis
lemma pieceBase_lt_one (j : Fin 6) : pieceBase j < 1 := by fin_cases j <;> (first | (simp [pieceBase]; all_goals first | (norm_num [pieceBase]; done) | rfl | decide) | (norm_num [pieceBase]; done) | norm_num [pieceBase])
lemma factorRational_nonneg (j : Fin 6) (n : ℕ) : 0 ≤ factorRational j n := by
  have hq : 0 ≤ rowQLower n := by unfold rowQLower; split_ifs <;> norm_num
  have hd : 0 ≤ rowDUpper n := by unfold rowDUpper; split_ifs <;> norm_num
  have hz := zCap_nonneg_e ⟨j.val,by omega⟩
  unfold factorRational
  exact mul_nonneg (div_nonneg (by positivity) hq) (densityCap_nonneg_e j)
lemma rowFactor_le (j : Fin 6) (n : ℕ) (hn : n%12 ∈ residues) :
    rowFactor j n ≤ factorRational j n := by
  unfold rowFactor factorRational
  have hq := rowQLower_bound n hn
  have hd := rowDUpper_bound n hn
  have hz := zCap_nonneg_e ⟨j.val,by omega⟩
  apply mul_le_mul_of_nonneg_right _ (densityCap_nonneg_e j)
  have hd0 : 0 ≤ rowDUpper n := (abs_nonneg (D n)).trans hd.le
  apply div_le_div₀ (by positivity)
  · exact add_le_add (add_le_add le_rfl hd.le) (mul_le_mul_of_nonneg_right pi_fine_e.2.le hz)
  · exact hq.1
  · exact hq.2.le
lemma rowPiece_le (j : Fin 6) (n : ℕ) : rowPiece j n ≤ pieceRational j n := by
  unfold rowPiece pieceRational
  split_ifs with hn
  · unfold pieceL
    apply mul_le_mul (rowFactor_le j n hn)
    · apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (decay_pieceBase_e j n) (lambdaCap_nonneg_e _)
      · exact pieceMass_le_e j n
      · exact pieceMass_nonneg_e j (Nat.cast_nonneg n)
      · exact mul_nonneg (lambdaCap_nonneg_e _) (pow_nonneg (pieceBase_pos_e j).le _)
    · exact pieceL_nonneg_e j (Nat.cast_nonneg n)
    · exact factorRational_nonneg j n
  · rfl
lemma rowTable_le (N : ℕ) : rowTable N ≤ tableRational N := by
  unfold rowTable tableRational
  apply Finset.sum_le_sum
  intro j _
  have hd : 0 < 1-pieceBase j^12 := sub_pos.mpr (pow_lt_one₀ (pieceBase_pos_e j).le (pieceBase_lt_one j) (by norm_num))
  apply div_le_div₀
  · exact Finset.sum_nonneg (fun a _ => (rowPiece_nonneg j _).trans (rowPiece_le j _))
  · exact Finset.sum_le_sum (fun a _ => rowPiece_le j _)
  · exact hd
  · have he := decay_pieceBase_e j 12
    have heq : Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*(12:ℕ)) = Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩) := by congr 1; push_cast <;> ring
    rw [heq] at he
    exact sub_le_sub_left he 1

lemma tableRational_zero : tableRational 0 < 28 := by
  first | (simp [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; all_goals first | (norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; done) | rfl | decide) | (norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; done) | norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]
lemma tableRational_four : tableRational 4 < 28/100 := by
  first | (simp [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; all_goals first | (norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; done) | rfl | decide) | (norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; done) | norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]
lemma tableRational_sixteen : tableRational 16 < 15/1000 := by
  first | (simp [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; all_goals first | (norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; done) | rfl | decide) | (norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; done) | norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]
lemma tableRational_hundred : tableRational 100 < 5/10^10 := by
  first | (simp [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; all_goals first | (norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; done) | rfl | decide) | (norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]; done) | norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase, rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap, residues,Fin.sum_univ_succ]

theorem rowTable_bounds : rowTable 0 < 28 ∧ rowTable 4 < 28/100 ∧
    rowTable 16 < 15/1000 ∧ rowTable 100 < 5/10^10 :=
  ⟨(rowTable_le 0).trans_lt tableRational_zero,(rowTable_le 4).trans_lt tableRational_four,
    (rowTable_le 16).trans_lt tableRational_sixteen,(rowTable_le 100).trans_lt tableRational_hundred⟩
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators

section
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

omit [DecidableEq ι] in
lemma matrixL1_apply (A : Matrix ι κ ℝ) (x : L1Finite κ) (i : ι) :
    matrixL1 A x i = ∑ j, A i j*x j := rfl
omit [DecidableEq ι] in
lemma matrixL1_sub (A B : Matrix ι κ ℝ) :
    matrixL1 (A-B) = matrixL1 A-matrixL1 B := by
  ext x i
  simp [matrixL1_apply,sub_mul,Finset.sum_sub_distrib]
lemma matrixL1_one : matrixL1 (1:Matrix ι ι ℝ) = 1 := by
  ext x i
  simp [matrixL1_apply,Matrix.one_apply]

omit [DecidableEq ι] in
lemma matrixL1_norm_le {A : Matrix ι κ ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ j, ∑ i, |A i j| ≤ b) : ‖matrixL1 A‖ ≤ b := by
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro x
  rw [l1Finite_norm_e,l1Finite_norm_e,Finset.mul_sum]
  calc
    ∑ i, |matrixL1 A x i| ≤ ∑ i, ∑ j, |A i j| * |x j| := by
      apply Finset.sum_le_sum
      intro i _
      rw [matrixL1_apply]
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => A i j*x j) Finset.univ
    _ = ∑ j, (∑ i, |A i j|)* |x j| := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    _ ≤ ∑ j, b* |x j| := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hA j) (abs_nonneg _)

omit [DecidableEq ι] in
lemma matrixL1_norm_lt [Nonempty κ] {A : Matrix ι κ ℝ} {b : ℝ}
    (hA : ∀ j, ∑ i, |A i j| < b) : ‖matrixL1 A‖ < b := by
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ (fun j : κ => ∑ i, |A i j|) Finset.univ_nonempty
  exact (matrixL1_norm_le (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    (fun k => hj k (Finset.mem_univ _))).trans_lt (hA j)
end

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
namespace SharpPlanar
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  (e : ι → Node × Bool) (he : Function.Injective e)
  (f : κ → Node × Bool)
lemma compressed_S_matrix :
    (finiteRestriction e he).comp (S.comp (finiteEmbedding f)) =
      matrixL1 (fun i j => S (lp.single 1 (f j) 1) (e i)) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply,finiteRestriction_apply_e]
  change S (∑ j, lp.single 1 (f j) (x j)) (e i) = _
  rw [map_sum]
  simp only [lp.coeFn_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (lp.single 1 (f j) (x j) : X) = (x j) • (lp.single 1 (f j) 1 : X) := by
    rw [← lp.single_smul]; simp
  rw [hs,map_smul]
  change x j * S (lp.single 1 (f j) 1) (e i) = S (lp.single 1 (f j) 1) (e i) * x j
  ring
end
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Indices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite node coordinates

These coordinates enumerate the value and derivative data on the first
triangular shell nodes in the planar Fourier interpolation problem.
-/

namespace SharpPlanar.Numerical

open scoped BigOperators
lemma exteriorIndex_bound (i : Fin 48 × Fin 2) : 4 < (exteriorIndex i).1.val ∧ (exteriorIndex i).1.val ≤ 100 := by revert i; decide +kernel
lemma lowExteriorIndex_bound (i : Fin 12) : 4 < (lowExteriorIndex i).1.val ∧ (lowExteriorIndex i).1.val ≤ 16 := by revert i; decide +kernel
lemma lowExteriorIndex_cover_check : ∀ n : Fin 17, 4<n.val ∧ n.val%12∈residues → ∀ d : Bool,
    ∃ i : Fin 12, (lowExteriorIndex i).1.val=n.val ∧ (lowExteriorIndex i).2=d := by decide +kernel
lemma lowExteriorIndex_range (n : Node) (d : Bool) : (∃ i, lowExteriorIndex i = (n,d)) ↔ 4<n.val ∧ n.val ≤ 16 := by
  constructor
  · rintro ⟨i,hi⟩
    have hh := lowExteriorIndex_bound i
    simpa only [hi] using hh
  · rintro ⟨hn,hm⟩
    obtain ⟨i,hin,hid⟩ := lowExteriorIndex_cover_check ⟨n.val,Nat.lt_succ_of_le hm⟩ ⟨hn,n.prop.2⟩ d
    exact ⟨i,Prod.ext (Subtype.ext hin) hid⟩
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Schur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

section Schur
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


omit [CompleteSpace F] in
theorem finite_schur_bound
    (V : E →L[ℝ] E) (U : F →L[ℝ] E) (L : E →L[ℝ] F) (D : F →L[ℝ] F)
    (hV : ‖V‖ ≤ 32) (hD : ‖D‖ ≤ 28/100) (hL : ‖L‖ ≤ 11/100)
    (hVU : ‖V.comp U‖ ≤ 37/10)
    {x rE : E} {y rF : F} (hx : x = V (rE + U y))
    (hy : y - L x - D y = rF) :
    ‖x‖ + ‖y‖ ≤ 90 * (‖rE‖ + ‖rF‖) := by
  have hxnorm : ‖x‖ ≤ 32 * ‖rE‖ + (37/10) * ‖y‖ := calc
    ‖x‖ = ‖V rE + (V.comp U) y‖ := by rw [hx]; simp
    _ ≤ ‖V rE‖ + ‖(V.comp U) y‖ := norm_add_le _ _
    _ ≤ ‖V‖ * ‖rE‖ + ‖V.comp U‖ * ‖y‖ := add_le_add (V.le_opNorm _) ((V.comp U).le_opNorm _)
    _ ≤ 32 * ‖rE‖ + (37/10) * ‖y‖ := by gcongr
  have hyrepr : y = rF + L x + D y := by rw [← hy]; abel
  have hynorm : ‖y‖ ≤ ‖rF‖ + (11/100) * ‖x‖ + (28/100) * ‖y‖ := calc
    ‖y‖ = ‖rF + L x + D y‖ := congrArg norm hyrepr
    _ ≤ ‖rF‖ + ‖L x‖ + ‖D y‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖rF‖ + ‖L‖ * ‖x‖ + ‖D‖ * ‖y‖ := by
      gcongr
      exacts [L.le_opNorm _, D.le_opNorm _]
    _ ≤ ‖rF‖ + (11/100) * ‖x‖ + (28/100) * ‖y‖ := by gcongr
  nlinarith [norm_nonneg rE, norm_nonneg rF]


end Schur
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite decompositions of ℓ¹ coordinates

The central and exterior coordinate blocks give an additive decomposition of the ℓ¹ norm.
-/

namespace SharpPlanar
open scoped BigOperators
section
variable {ι κ : Type*}
lemma l1Split_norm [Fintype ι] [Fintype κ] (x : L1Finite (ι ⊕ κ)) :
    ‖x‖ = ‖l1Left x‖+‖l1Right x‖ := by
  classical
  rw [l1Finite_norm_e, l1Finite_norm_e, l1Finite_norm_e, Fintype.sum_sum_type]
  rfl
end
end SharpPlanar
namespace SharpPlanar.Numerical
lemma finiteEmbedding_split (x : L1Finite FiniteIndex) :
    finiteEmbedding finiteIndex x = finiteEmbedding centralIndex (l1Left x) +
      finiteEmbedding exteriorIndex (l1Right x) := by
  ext k
  change finiteEmbedding finiteIndex x k = finiteEmbedding centralIndex (l1Left x) k + finiteEmbedding exteriorIndex (l1Right x) k
  simp only [finiteEmbedding_apply_e]
  change (∑ j, if finiteIndex j=k then x j else 0) =
    (∑ j, if centralIndex j=k then l1Left x j else 0)+
    (∑ j, if exteriorIndex j=k then l1Right x j else 0)
  rw [Fintype.sum_sum_type]
  rfl
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite coordinate projections

Restriction and extension identify the first shell coordinates with a finite
subspace of the absolutely summable interpolation space.
-/

namespace SharpPlanar
open scoped BigOperators
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
lemma finiteProjection_apply (x : X) (k : Node × Bool) :
    finiteEmbedding e (finiteRestriction e he x) k = if ∃ i, e i=k then x k else 0 := by
  classical
  rw [finiteEmbedding_apply_e]
  split_ifs with h
  · obtain ⟨i,rfl⟩ := h
    simp only [he.eq_iff, finiteRestriction_apply_e]
    simp
  · apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (fun hh => h ⟨i,hh⟩)]
end
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tails of the interpolation operator

Coordinate projections and shell estimates bound the tails of the interpolation operator.
-/

namespace SharpPlanar
open scoped BigOperators
lemma tailScalar_eq (x : X) (N : ℕ) : tailScalar x N = rowTailNorm x N := by
  unfold tailScalar rowTailNorm
  rw [(tailScalar_summable_e x N).tsum_prod]
  change _ = ∑' n : {n : Node // n ∈ {n : Node | N<n.val}}, (fun n : Node => |x (n,false)|+|x (n,true)|) n.val
  rw [tsum_subtype {n : Node | N<n.val} (fun n : Node => |x (n,false)|+|x (n,true)|)]
  apply tsum_congr
  intro n
  simp only [tsum_fintype, Fintype.sum_bool, Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> simp [add_comm]
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
lemma finiteRestriction_tail (N : ℕ) (hN : ∀ i, N<(e i).1.val) (x : X) :
    ‖finiteRestriction e he x‖ ≤ rowTailNorm x N := by
  rw [l1Finite_norm_e,← tailScalar_eq]
  have hh := tsum_comp_le_tsum_of_inj (tailScalar_summable_e x N)
    (fun k => by split_ifs <;> positivity) he
  simpa only [Function.comp_apply, hN, ite_true, if_true, tsum_fintype,finiteRestriction_apply_e,tailScalar] using hh
end
end SharpPlanar
namespace SharpPlanar.Numerical
open scoped BigOperators
lemma exterior_low_tail (x : X) : ‖RE x‖ ≤ ‖RL x‖ + rowTailNorm x 16 := by
  have hh := tsum_comp_le_tsum_of_inj (tailScalar_summable_e x 16)
    (fun k => by split_ifs <;> positivity) exteriorIndex_injective_e
  have hh' : (∑ i, if 16<(exteriorIndex i).1.val then |x (exteriorIndex i)| else 0)
      ≤ rowTailNorm x 16 := by
    rw [← tailScalar_eq]
    simpa only [Function.comp_apply,tsum_fintype,tailScalar] using hh
  have hi : ‖RE (IL (RL x))‖ ≤ ‖RL x‖ := by
    exact (finiteRestriction_bound_e _ exteriorIndex_injective_e _).trans_eq (by rw [one_mul,finiteEmbedding_norm_e _ lowExteriorIndex_injective_e])
  calc
    ‖RE x‖ ≤ ‖RE (IL (RL x))‖ +
        ∑ i, if 16<(exteriorIndex i).1.val then |x (exteriorIndex i)| else 0 := by
      rw [l1Finite_norm_e,l1Finite_norm_e,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      simp only [finiteRestriction_apply_e]
      rw [finiteProjection_apply]
      by_cases h : 16<(exteriorIndex i).1.val
      · simp only [h,ite_true, if_true]
        exact le_add_of_nonneg_left (abs_nonneg _)
      · have hmem : ∃ j, lowExteriorIndex j=exteriorIndex i :=
          (lowExteriorIndex_range (exteriorIndex i).1 (exteriorIndex i).2).mpr
            ⟨(exteriorIndex_bound i).1, Nat.le_of_not_gt h⟩
        rw [ite_eq_left hmem,ite_eq_right h,add_zero]
    _ ≤ ‖RL x‖ + rowTailNorm x 16 := add_le_add hi hh'
lemma compressed_low_L : RL.comp (S.comp IJ) = matrixL1 Lmat := by
  rw [compressed_S_matrix]
  rfl
lemma exterior_central_norm : ‖RE.comp (S.comp IJ)‖ ≤ (11:ℝ)/100 := by
  have hlow : ‖RL.comp (S.comp IJ)‖ ≤ (88:ℝ)/1000 := by
    rw [compressed_low_L]
    exact (matrixL1_norm_lt Lmat_column_e).le
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have h := exterior_low_tail (S (IJ x))
  have hL : ‖RL (S (IJ x))‖ ≤ (88:ℝ)/1000 * ‖x‖ :=
    ((RL.comp (S.comp IJ)).le_opNorm x).trans (mul_le_mul_of_nonneg_right hlow (norm_nonneg _))
  have ht := sharp_S_tail (IJ x) 16
  rw [finiteEmbedding_norm_e _ centralIndex_injective_e] at ht
  have ht' := mul_le_mul_of_nonneg_right rowTable_bounds.2.2.1.le (norm_nonneg x)
  change ‖RE (S (IJ x))‖ ≤ _
  nlinarith [norm_nonneg x]
lemma exterior_exterior_norm : ‖RE.comp (S.comp IE)‖ ≤ (28:ℝ)/100 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have h := finiteRestriction_tail exteriorIndex exteriorIndex_injective_e 4
    (fun i => (exteriorIndex_bound i).1) (S (IE x))
  have ht := sharp_S_tail (IE x) 4
  rw [finiteEmbedding_norm_e _ exteriorIndex_injective_e] at ht
  exact h.trans (ht.trans (mul_le_mul_of_nonneg_right rowTable_bounds.2.1.le (norm_nonneg _)))
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite interpolation system

Schur complements give existence, uniqueness and norm bounds for the finite system.
-/

namespace SharpPlanar.Numerical
lemma compressed_D : RJ.comp (S.comp IJ) = matrixL1 Dmat := by
  rw [compressed_S_matrix]; rfl
lemma signedL_norm (neg : Bool) : ‖signedL neg‖ ≤ (11:ℝ)/100 := by
  cases neg <;> simpa only [signedL,signedS,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,
    ContinuousLinearMap.neg_comp,ContinuousLinearMap.comp_neg,norm_neg] using exterior_central_norm
lemma signedE_norm (neg : Bool) : ‖signedE neg‖ ≤ (28:ℝ)/100 := by
  cases neg <;> simpa only [signedE,signedS,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,
    ContinuousLinearMap.neg_comp,ContinuousLinearMap.comp_neg,norm_neg] using exterior_exterior_norm
lemma centralV_left (neg : Bool) (x : L1Finite (Fin 6)) :
    centralV neg (x-RJ (signedS neg (IJ x))) = x := by
  have hD (y : L1Finite (Fin 6)) : RJ (S (IJ y)) = matrixL1 Dmat y :=
    congrArg (fun f => f y) compressed_D
  cases neg
  · change inversePlusEquiv (x-RJ (S (IJ x))) = x
    rw [hD]
    have hh := (certifiedEquiv (matrixL1 Aplus) (matrixL1 Wplus) defectplus_lt_one_e).symm_apply_apply x
    change inversePlusEquiv (matrixL1 Aplus x) = x at hh
    simpa only [Aplus,matrixL1_sub,matrixL1_one,sub_apply,one_apply_eq_self] using hh
  · change inverseMinusEquiv (x-RJ (-S (IJ x))) = x
    rw [map_neg,hD,sub_neg_eq_add]
    have hh := (certifiedEquiv (matrixL1 Aminus) (matrixL1 Wminus) defectminus_lt_one_e).symm_apply_apply x
    change inverseMinusEquiv (matrixL1 Aminus x) = x at hh
    have he : matrixL1 Aminus x = x+matrixL1 Dmat x := by
      ext i
      simp [Aminus,matrixL1_apply,Matrix.add_apply,Matrix.one_apply,add_mul,Finset.sum_add_distrib]
    rw [he] at hh
    exact hh
lemma finiteA_left (neg : Bool) (x : L1Finite FiniteIndex) :
    l1Left (finiteA neg x) = l1Left x - RJ (signedS neg (IJ (l1Left x))) - signedU neg (l1Right x) := by
  have hs := finiteEmbedding_split x
  change IF x = IJ (l1Left x)+IE (l1Right x) at hs
  ext i
  change x (Sum.inl i) - RF (signedS neg (IF x)) (Sum.inl i) = _
  rw [hs,map_add,map_add]
  change x (Sum.inl i) - (RJ (signedS neg (IJ (l1Left x))) i + RJ (signedS neg (IE (l1Right x))) i) = _
  change _ = x (Sum.inl i)-RJ (signedS neg (IJ (l1Left x))) i - RJ (signedS neg (IE (l1Right x))) i
  ring
lemma finiteA_right (neg : Bool) (x : L1Finite FiniteIndex) :
    l1Right (finiteA neg x) = l1Right x - signedL neg (l1Left x) - signedE neg (l1Right x) := by
  have hs := finiteEmbedding_split x
  change IF x = IJ (l1Left x)+IE (l1Right x) at hs
  ext i
  change x (Sum.inr i) - RF (signedS neg (IF x)) (Sum.inr i) = _
  rw [hs,map_add,map_add]
  change x (Sum.inr i) - (RE (signedS neg (IJ (l1Left x))) i + RE (signedS neg (IE (l1Right x))) i) = _
  change _ = x (Sum.inr i)-RE (signedS neg (IJ (l1Left x))) i - RE (signedS neg (IE (l1Right x))) i
  ring
lemma finiteA_coercive (neg : Bool) (x : L1Finite FiniteIndex) : ‖x‖ ≤ 90*‖finiteA neg x‖ := by
  rw [l1Split_norm x,l1Split_norm (finiteA neg x)]
  apply finite_schur_bound (centralV neg) (signedU neg) (signedL neg) (signedE neg)
    (centralV_norm_e neg) (signedE_norm neg) (signedL_norm neg) (signedVU_norm_e neg)
  · rw [finiteA_left,sub_add_cancel,centralV_left]
  · exact (finiteA_right neg x).symm
lemma finiteA_bijective_e_oai (neg : Bool) : Function.Bijective (finiteA neg) := by
  have hi : Function.Injective (finiteA neg) := by
    intro x y hxy
    have hb := finiteA_coercive neg (x-y)
    rw [map_sub,hxy,sub_self,norm_zero,mul_zero] at hb
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))
  exact ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.finiteA_bijective_e_oai := @OAI.SharpPlanar.Numerical.finiteA_bijective_e_oai
