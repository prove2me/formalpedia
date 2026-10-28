-- Prove2me | solution 1 for OAI.ThorpNine.Adaptive.Thorp.UnitaryFinite.medium_exception_decay_q77
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:06:16.620875+00:00
-- url     : https://prove2.me/submissions/d7ae4cce-06d8-456b-be9f-55acbc94e124

import Mathlib
import Definitions.Def_ThorpRouting
import Definitions.Def_OAIQ077T000

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_Coins
attribute [-instance] _root_.OAI.ThorpNine.Adaptive.Thorp.instFintypeSelectedCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp

open scoped BigOperators
open Filter

lemma card_positions (d : ℕ) : Fintype.card (Card d) = 2 ^ d := by
  simp [Card]

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ExposedCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators
open Filter

lemma finiteMean_congr {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ}
    (h : ∀ ω, f ω = g ω) : finiteMean f = finiteMean g := by
  unfold finiteMean
  congr 1
  exact Finset.sum_congr rfl (fun ω _ => h ω)

lemma finiteMean_mul_const {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (c : ℝ) :
    finiteMean (fun ω => f ω * c) = finiteMean f * c := by
  unfold finiteMean
  rw [← Finset.sum_mul]
  ring

lemma finiteMean_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ}
    (h : ∀ ω, f ω ≤ g ω) : finiteMean f ≤ finiteMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω)) (Nat.cast_nonneg _)

lemma finiteMean_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (f : Ω → ℝ) :
    finiteMean f = finiteMean (fun ω => f (e.symm ω)) := by
  unfold finiteMean
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun ω => by simp)

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ParallelFollow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators
open Filter

lemma butterfly_split (r s : ℕ) (lo : Card r × SwitchIndex s → Bool)
    (hi : Card s × SwitchIndex r → Bool) (x : Card (s+r)) :
    cardSplit r s (butterflyPerm (s+r) (decodeButterfly (s+r) (assembleBits r s lo hi)) x) =
      let y := cardSplit r s x
      let z := butterflyPerm s (decodeButterfly s (fun i => lo (y.1,i))) y.2
      (butterflyPerm r (decodeButterfly r (fun i => hi (z,i))) y.1,z) := by
  induction r with
  | zero =>
    apply Prod.ext
    · funext i
      exact Fin.elim0 i
    · rfl
  | succ r ih =>
    let lo' : Card r × SwitchIndex s → Bool := fun j => lo (Fin.cons (x 0) j.1,j.2)
    let hi' : Card s × SwitchIndex r → Bool := fun j => hi (j.1,Sum.inr (x 0,j.2))
    have hh := ih lo' hi' (Fin.tail x)
    let u := butterflyPerm (s+r) (decodeButterfly (s+r) (assembleBits r s lo' hi')) (Fin.tail x)
    let y := cardSplit r s (Fin.tail x)
    let z := butterflyPerm s (decodeButterfly s (fun i => lo' (y.1,i))) y.2
    let w := butterflyPerm r (decodeButterfly r (fun i => hi' (z,i))) y.1
    change cardSplit r s u = (w,z) at hh
    change ((Fin.cons (Bool.xor (x 0) (hi ((cardSplit r s u).2,Sum.inl (cardSplit r s u).1)))
        ((cardSplit r s u).1) : Card (r+1)), (cardSplit r s u).2) =
      ((Fin.cons (Bool.xor (x 0) (hi (z,Sum.inl w))) w : Card (r+1)),z)
    rw [hh]

lemma assembleBits_eq (r s : ℕ) (lo : Card r × SwitchIndex s → Bool)
    (hi : Card s × SwitchIndex r → Bool) (i : SwitchIndex (s+r)) :
    assembleBits r s lo hi i = Sum.elim lo hi (splitSwitch r s i) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rcases i with y | ⟨b,j⟩
    · rfl
    · simp only [assembleBits,splitSwitch,Equiv.coe_fn_mk]
      rw [ih]
      cases splitSwitch r s j <;> rfl

lemma splitCoinEquiv_apply (r s : ℕ) (lo : Card r × SwitchIndex s → Bool)
    (hi : Card s × SwitchIndex r → Bool) :
    splitCoinEquiv r s (lo,hi) = assembleBits r s lo hi := by
  funext i
  exact (assembleBits_eq r s lo hi i).symm

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_AlternatingPerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators
open Filter

lemma butterflyPerm_step (d : ℕ)
    (c : (SwitchIndex d → Bool) × (SwitchIndex d → Bool)) (ξ : Card d → Bool) :
    butterflyPerm (d+1) (decodeButterfly (d+1) ((coinStepEquiv d).symm (c,ξ))) =
    pairSwitch ξ * childLift (fun b => butterflyPerm d (decodeButterfly d (if b then c.2 else c.1))) := by
  change pairSwitch (fun y => (coinStepEquiv d).symm (c,ξ) (Sum.inl y)) *
    childLift (fun b => butterflyPerm d (decodeButterfly d
      (fun i => (coinStepEquiv d).symm (c,ξ) (Sum.inr (b,i))))) = _
  apply congrArg₂ (· * ·)
  · rfl
  · apply congrArg childLift
    funext b
    apply congrArg (fun ω => butterflyPerm d (decodeButterfly d ω))
    funext i
    cases b <;> rfl

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_BenesCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators
open Filter

lemma childLift_inv (d : ℕ) (p : Bool → Equiv.Perm (Card d)) :
    (childLift p)⁻¹ = childLift (fun b => (p b)⁻¹) := rfl

lemma pairSwitch_inv (d : ℕ) (ξ : Card d → Bool) : (pairSwitch ξ)⁻¹ = pairSwitch ξ := rfl

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_InputTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp

lemma mem_exceptionChild {r : ℕ} (E : Finset (Card (r+1))) (b : Bool) (u : Card r) :
    u ∈ exceptionChild E b ↔ Fin.cons b u ∈ E := by
  classical
  simp only [exceptionChild,Finset.mem_filter,Finset.mem_univ,true_and]

lemma modifiedBoundary_cons (L r : ℕ) (E : Finset (Card (r+1)))
    (U : Card (r+1) → Equiv.Perm (Card L)) (Y : SwitchIndex (L+r+1) → Bool) (b : Bool) :
    (fun u => modifiedBoundary L (r+1) E U Y (Fin.cons b u)) =
    modifiedBoundary L r (exceptionChild E b) (fun u => U (Fin.cons b u))
      (if b then (coinStepEquiv (L+r) Y).1.2 else (coinStepEquiv (L+r) Y).1.1) := by
  funext u
  simp only [modifiedBoundary,mem_exceptionChild,boundaryOutput,Fin.cons_zero,Fin.tail_cons]

lemma modifiedInputTree_node (L r : ℕ) (E : Finset (Card (r+1)))
    (ω : ModifiedCoins L r × ModifiedCoins L r) (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    let z := (modifiedStepEquiv L r).symm (ω,coins)
    modifiedInputTree L (r+1) E z.1 z.2.2 z.2.1 =
      InputTree.node coins.1 (fun b =>
        let w := if b then ω.2 else ω.1
        modifiedInputTree L r (exceptionChild E b) w.1 w.2.2 w.2.1) := by
  dsimp only
  unfold modifiedInputTree
  rw [boundaryTree]
  change InputTree.node coins.1 (fun b => boundaryTree L r _ _) = _
  congr 1
  funext b
  rw [modifiedBoundary_cons]
  cases b <;> rfl

lemma modifiedPerm_step (L r : ℕ) (E : Finset (Card (r+1)))
    (ω : ModifiedCoins L r × ModifiedCoins L r) (coins : (Card (L+r) → Bool) × (Card (L+r) → Bool)) :
    modifiedPerm L (r+1) E ((modifiedStepEquiv L r).symm (ω,coins)) =
      pairSwitch coins.2 * childLift (fun b => modifiedPerm L r (exceptionChild E b)
        (if b then ω.2 else ω.1)) * pairSwitch coins.1 := by
  rw [modifiedPerm,modifiedInputTree_node,InputTree.perm,mul_inv_rev,pairSwitch_inv,childLift_inv]
  change (butterflyPerm (L+r+1) (decodeButterfly (L+r+1)
    ((coinStepEquiv (L+r)).symm ((ω.1.2.1,ω.2.2.1),coins.2)))) * _ = _
  rw [butterflyPerm_step,mul_assoc,←mul_assoc (childLift _),childLift_mul,←mul_assoc]
  congr 2
  apply congrArg childLift
  funext b
  cases b <;> rfl

lemma modifiedPerm_zero (L : ℕ) (E : Finset (Card 0)) (ω : ModifiedCoins L 0) :
    modifiedPerm L 0 E ω =
      if (fun j => Fin.elim0 j : Card 0) ∈ E then 1
      else butterflyPerm L (decodeButterfly L ω.2.1)*(ω.1 (fun j => Fin.elim0 j))⁻¹ := by
  unfold modifiedPerm modifiedInputTree boundaryTree InputTree.perm modifiedBoundary boundaryOutput
  split_ifs
  · exact mul_inv_cancel _
  · rfl

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ModifiedRoutingMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp


namespace DensityTransfer
open scoped BigOperators

lemma applyKernel_apply {X : Type*} [Fintype X] (P : X → X → ℝ)
    (v : EuclideanSpace ℂ X) (x : X) :
    applyKernel P v x = ∑ y, (P x y : ℂ)*v y := rfl

lemma applyKernel_add {X : Type*} [Fintype X] (P Q : X → X → ℝ)
    (v : EuclideanSpace ℂ X) :
    applyKernel (fun x y => P x y+Q x y) v = applyKernel P v+applyKernel Q v := by
  ext x
  simp only [applyKernel_apply,Complex.ofReal_add,add_mul,Finset.sum_add_distrib]
  rfl

lemma kernel_component_sq {X : Type*} [Fintype X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (v : EuclideanSpace ℂ X) (x : X) :
    ‖applyKernel P v x‖^2 ≤ (∑ y, P x y) * ∑ y, P x y*‖v y‖^2 := by
  have hs : ‖applyKernel P v x‖ ≤ ∑ y, P x y*‖v y‖ := by
    rw [applyKernel_apply]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro y _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hP x y)]
  apply (pow_le_pow_left₀ (norm_nonneg _) hs 2).trans
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun y _ => hP x y) (fun y _ => mul_nonneg (hP x y) (sq_nonneg _))
    (fun y _ => by ring_nf; exact le_rfl)

lemma schur_bound {X : Type*} [Fintype X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (δ : ℝ) (hδ : 0 ≤ δ)
    (hrow : ∀ x, ∑ y, P x y ≤ δ) (hcol : ∀ y, ∑ x, P x y ≤ δ)
    (v : EuclideanSpace ℂ X) : ‖applyKernel P v‖ ≤ δ*‖v‖ := by
  have hsq : ‖applyKernel P v‖^2 ≤ δ^2*‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ x, δ * ∑ y, P x y*‖v y‖^2 := by
        apply Finset.sum_le_sum
        intro x _
        apply (kernel_component_sq P hP v x).trans
        exact mul_le_mul_of_nonneg_right (hrow x)
          (Finset.sum_nonneg (fun y _ => mul_nonneg (hP x y) (sq_nonneg _)))
      _ = δ * ∑ y, (∑ x, P x y)*‖v y‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        exact (Finset.sum_mul Finset.univ _ _).symm
      _ ≤ δ * ∑ y, δ*‖v y‖^2 := by
        apply mul_le_mul_of_nonneg_left _ hδ
        exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_right (hcol y) (sq_nonneg _))
      _ = _ := by rw [←Finset.mul_sum]; ring
  have hn := norm_nonneg (applyKernel P v)
  have hr := mul_nonneg hδ (norm_nonneg v)
  nlinarith

lemma hilbert_schmidt_family {X I : Type*} [Fintype X] [Fintype I]
    (P : X → X → ℝ) (v : I → EuclideanSpace ℂ X) (hv : Orthonormal ℂ v) :
    (∑ i, ‖applyKernel P (v i)‖^2) ≤ ∑ x, ∑ y, (P x y)^2 := by
  simp_rw [EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  let w : EuclideanSpace ℂ X := WithLp.toLp 2 (fun y => (P x y : ℂ))
  have he (i : I) : ‖applyKernel P (v i) x‖ = ‖inner ℂ (v i) w‖ := by
    rw [norm_inner_symm]
    congr 1
    simp only [applyKernel_apply,PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro y _
    simp [w,RCLike.inner_apply,mul_comm]
  simp_rw [he]
  have h := hv.sum_inner_products_le (s := Finset.univ) w
  apply h.trans_eq
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro y _
  simp [w,Complex.norm_real,Real.norm_eq_abs,sq_abs]


lemma tail_density_pointwise (t a z : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a) (hz : 0 < z) :
    (if z < t then t else 0) ≤ t^(1+a)*z^(-a) := by
  split_ifs with h
  · rw [Real.rpow_neg hz.le,←div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hz a)).mpr
    rw [Real.rpow_add (lt_trans hz h),Real.rpow_one]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hz.le h.le ha) ht
  · positivity

lemma tail_density_mean {X : Type*} [Fintype X] (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    (a z : ℝ) (ha : 0 ≤ a) (hz : 0 < z) :
    finiteMean (fun x => if z < f x then f x else 0) ≤ finiteMean (fun x => f x^(1+a))*z^(-a) := by
  rw [←finiteMean_mul_const]
  exact finiteMean_mono (fun x => tail_density_pointwise (f x) a z (hf x) ha hz)

lemma tail_add_head {X : Type*} [Fintype X] (P : X → X → ℝ) (z : ℝ) :
    (fun x y => tailKernel P z x y+headKernel P z x y) = P := by
  funext x y
  unfold tailKernel headKernel
  split_ifs <;> simp

lemma tailKernel_nonneg {X : Type*} [Fintype X] (P : X → X → ℝ) (z : ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (x y : X) : 0 ≤ tailKernel P z x y := by
  unfold tailKernel
  split_ifs <;> simp only [hP,le_refl]

lemma tailKernel_row {X : Type*} [Fintype X] [Nonempty X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (a z M : ℝ) (ha : 0 ≤ a) (hz : 0 < z)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*P x y)^(1+a)) ≤ M) (x : X) :
    ∑ y, tailKernel P z x y ≤ M*z^(-a) := by
  have hn : (Fintype.card X:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he : finiteMean (fun y => if z < (Fintype.card X:ℝ)*P x y then
      (Fintype.card X:ℝ)*P x y else 0) = ∑ y, tailKernel P z x y := by
    unfold finiteMean
    calc
      _ = (∑ y, (Fintype.card X:ℝ)*tailKernel P z x y)/(Fintype.card X:ℝ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : z < (Fintype.card X:ℝ)*P x y
        · simp only [tailKernel,hy,↓reduceIte]
        · simp only [tailKernel,hy,↓reduceIte,mul_zero]
      _ = _ := by rw [←Finset.mul_sum]; field_simp
  rw [←he]
  exact (tail_density_mean _ (fun y => mul_nonneg (Nat.cast_nonneg _) (hP x y)) a z ha hz).trans
    (mul_le_mul_of_nonneg_right (hM x) (Real.rpow_nonneg hz.le _))

lemma tailKernel_schur {X : Type*} [Fintype X] [Nonempty X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hsym : ∀ x y, P x y = P y x)
    (a z M : ℝ) (ha : 0 ≤ a) (hz : 0 < z) (hM0 : 0 ≤ M)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*P x y)^(1+a)) ≤ M)
    (v : EuclideanSpace ℂ X) :
    ‖applyKernel (tailKernel P z) v‖ ≤ (M*z^(-a))*‖v‖ := by
  apply schur_bound _ (tailKernel_nonneg P z hP) _ (by positivity)
    (tailKernel_row P hP a z M ha hz hM)
  intro y
  have hs : (fun x => tailKernel P z x y) = (fun x => tailKernel P z y x) := by
    funext x
    simp only [tailKernel,hsym x y]
  rw [hs]
  exact tailKernel_row P hP a z M ha hz hM y

lemma headKernel_hs {X : Type*} [Fintype X] [Nonempty X] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (z : ℝ) (hz : 0 ≤ z) :
    (∑ x, ∑ y, (headKernel P z x y)^2) ≤ z := by
  have hn : (0:ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have he (x y : X) : (headKernel P z x y)^2 ≤ (z/(Fintype.card X:ℝ))*P x y := by
    unfold headKernel
    split_ifs with h
    · simp only [zero_pow (by omega : (2:ℕ) ≠ 0)]
      exact mul_nonneg (div_nonneg hz hn.le) (hP x y)
    · have h' : (Fintype.card X:ℝ)*P x y ≤ z := le_of_not_gt h
      have hh := mul_le_mul_of_nonneg_right h' (hP x y)
      rw [show (z/(Fintype.card X:ℝ))*P x y = (z*P x y)/(Fintype.card X:ℝ) by ring]
      apply (le_div_iff₀ hn).mpr
      nlinarith
  calc
    _ ≤ ∑ x, ∑ y, (z/(Fintype.card X:ℝ))*P x y :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => he x y))
    _ = z := by
      simp only [←Finset.mul_sum,hrow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      field_simp


theorem multiplicity_amplification {X I : Type*} [Fintype X] [Nonempty X]
    [Fintype I] [Nonempty I] (P : X → X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (hsym : ∀ x y, P x y = P y x)
    (hrow : ∀ x, ∑ y, P x y = 1) (a z M : ℝ) (ha : 0 ≤ a) (hz : 0 < z) (hM0 : 0 ≤ M)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*P x y)^(1+a)) ≤ M)
    (v : I → EuclideanSpace ℂ X) (hv : Orthonormal ℂ v)
    (μ : ℝ) (hvμ : ∀ i, μ ≤ ‖applyKernel P (v i)‖) :
    μ ≤ M*z^(-a)+Real.sqrt (z/(Fintype.card I:ℝ)) := by
  let δ : ℝ := M*z^(-a)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hm : (0:ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  change μ ≤ δ+_
  by_cases hμ : μ ≤ δ
  · exact hμ.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hmd : 0 ≤ μ-δ := by linarith
  have hsmall (i : I) : μ-δ ≤ ‖applyKernel (headKernel P z) (v i)‖ := by
    have hr := tailKernel_schur P hP hsym a z M ha hz hM0 hM (v i)
    rw [hv.norm_eq_one i,mul_one] at hr
    have he := applyKernel_add (tailKernel P z) (headKernel P z) (v i)
    rw [tail_add_head] at he
    have hn := norm_add_le (applyKernel (tailKernel P z) (v i)) (applyKernel (headKernel P z) (v i))
    rw [←he] at hn
    have hh := hvμ i
    change ‖applyKernel (tailKernel P z) (v i)‖ ≤ δ at hr
    linarith
  have hsum : (Fintype.card I:ℝ)*(μ-δ)^2 ≤ z := by
    calc
      _ = ∑ i : I, (μ-δ)^2 := by simp
      _ ≤ ∑ i : I, ‖applyKernel (headKernel P z) (v i)‖^2 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ hmd (hsmall i) 2)
      _ ≤ ∑ x, ∑ y, (headKernel P z x y)^2 := hilbert_schmidt_family _ v hv
      _ ≤ z := headKernel_hs P hP hrow z hz.le
  have hsq : (μ-δ)^2 ≤ z/(Fintype.card I:ℝ) := (le_div_iff₀ hm).mpr (by nlinarith)
  have hs := (Real.le_sqrt hmd (div_nonneg hz.le hm.le)).mpr hsq
  linarith

end DensityTransfer
namespace PairRouting
open scoped BigOperators

lemma tupleProbability_row_sum {ι β Ω : Type*} [Fintype ι] [Fintype β]
    [DecidableEq β] [Fintype Ω] [Nonempty Ω]
    (P : Ω → Equiv.Perm β) (e : ι ↪ β) :
    (∑ f : ι ↪ β, tupleProbability P e f) = 1 := by
  classical
  simp only [tupleProbability]
  rw [←finiteMean_sum]
  have h (ω : Ω) (f : ι ↪ β) : (∀ i, P ω (e i) = f i) ↔ e.trans (P ω).toEmbedding = f := by
    constructor
    · intro h; ext i; exact h i
    · intro h i; exact congrArg (fun g : ι ↪ β => g i) h
  simp_rw [h]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte,finiteMean_const]

lemma tupleProbability_inverse {ι β Ω : Type*} [Fintype ι] [DecidableEq β]
    [Fintype Ω] (P : Ω → Equiv.Perm β) (e f : ι → β) :
    tupleProbability (fun ω => (P ω)⁻¹) e f = tupleProbability P f e := by
  classical
  apply finiteMean_congr
  intro ω
  congr 1
  apply propext
  constructor
  · intro h i
    have hh := congrArg (P ω) (h i)
    simpa only [Equiv.Perm.inv_def,Equiv.apply_symm_apply] using hh.symm
  · intro h i
    have hh := congrArg (fun x => (P ω).symm x) (h i)
    simpa only [Equiv.Perm.inv_def,Equiv.symm_apply_apply] using hh.symm

lemma tupleProbability_equiv {ι β Ω Ω' : Type*} [Fintype ι] [DecidableEq β]
    [Fintype Ω] [Fintype Ω'] (P : Ω → Equiv.Perm β) (τ : Ω ≃ Ω') (e f : ι → β) :
    tupleProbability P e f = tupleProbability (fun ω => P (τ.symm ω)) e f :=
  finiteMean_equiv τ _

lemma tupleProbability_symmetric {ι β Ω : Type*} [Fintype ι] [DecidableEq β]
    [Fintype Ω] (P : Ω → Equiv.Perm β) (τ : Equiv.Perm Ω)
    (hτ : ∀ ω, P (τ ω) = (P ω)⁻¹) (e f : ι → β) :
    tupleProbability P e f = tupleProbability P f e := by
  rw [tupleProbability_equiv P τ.symm]
  simp only [Equiv.symm_symm,hτ]
  exact tupleProbability_inverse P e f

end PairRouting

lemma palindromePerm_reverse (d : ℕ) (ω : BenesCoins d) :
    palindromePerm d (ω.2,ω.1) = (palindromePerm d ω)⁻¹ := by
  simp only [palindromePerm,mul_inv_rev]
  rfl

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ModifiedReverseEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp

lemma modifiedPerm_reverse (L r : ℕ) (E : Finset (Card r)) (ω : ModifiedCoins L r) :
    modifiedPerm L r E (modifiedReverseCoins L r ω) = (modifiedPerm L r E ω)⁻¹ := by
  induction r with
  | zero =>
      rw [modifiedPerm_zero,modifiedPerm_zero]
      split_ifs
      · simp only [inv_one]
      · simp only [modifiedReverseCoins,mul_inv_rev,inv_inv]
        simp
  | succ r ih =>
      obtain ⟨z,rfl⟩ := (modifiedStepEquiv L r).symm.surjective ω
      rcases z with ⟨⟨ω₀,ω₁⟩,⟨ξ,η⟩⟩
      simp only [modifiedReverseCoins,Equiv.apply_symm_apply,modifiedPerm_step,
        mul_inv_rev,pairSwitch_inv,childLift_inv]
      rw [mul_assoc]
      congr 1
      congr 1
      apply congrArg childLift
      funext b
      cases b <;> simp only [Bool.false_eq_true,↓reduceIte,ih]

lemma modified_kernel_symmetric (L r : ℕ) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e f : ι ↪ Card (L+r)) :
    PairRouting.tupleProbability (modifiedPerm L r E) e f =
      PairRouting.tupleProbability (modifiedPerm L r E) f e :=
  PairRouting.tupleProbability_symmetric _ (modifiedReverseEquiv L r)
    (modifiedPerm_reverse L r E) e f

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ShapePartitionEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma unitary_inner_inv (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) (v w : V) :
    inner ℂ v (ρ g⁻¹ w) = inner ℂ (ρ g v) w := by
  have h := hρ g v (ρ g⁻¹ w)
  have he : ρ g (ρ g⁻¹ w) = w := by
    change (ρ g * ρ g⁻¹) w = w
    rw [←map_mul,mul_inv_cancel,map_one]
    rfl
  rw [he] at h
  exact h.symm

end Thorp.UnitaryFinite

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_Representative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
omit [FiniteDimensional ℂ V] in
lemma averageMap_self_trace (ρ : Representation ℂ G V) (A : Module.End ℂ V) :
    LinearMap.trace ℂ V (averageMap ρ ρ A).toLinearMap =
      (Fintype.card G:ℂ) * LinearMap.trace ℂ V A := by
  change LinearMap.trace ℂ V (∑ g, ρ g * A * ρ g⁻¹) = _
  rw [map_sum]
  have hj (g : G) : LinearMap.trace ℂ V (ρ g*A*ρ g⁻¹) = LinearMap.trace ℂ V A := by
    rw [LinearMap.trace_mul_cycle,←map_mul,inv_mul_cancel,map_one,one_mul]
  simp only [hj,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

lemma averageMap_scalar (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (A : Module.End ℂ V) :
    ∃ c : ℂ, (averageMap ρ ρ A).toLinearMap = c • LinearMap.id ∧
      c * (Module.finrank ℂ V:ℂ) = (Fintype.card G:ℂ)*LinearMap.trace ℂ V A := by
  obtain ⟨c,hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).surjective (averageMap ρ ρ A)
  have he : (averageMap ρ ρ A).toLinearMap = c • LinearMap.id := by
    rw [←hc]
    rfl
  refine ⟨c,he,?_⟩
  rw [←averageMap_self_trace ρ A,he,map_smul,LinearMap.trace_id,smul_eq_mul]

theorem coefficient_orthogonality (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (u v w z : V) :
    (Module.finrank ℂ V:ℂ) * ∑ g, inner ℂ u (ρ g v) * inner ℂ (ρ g w) z =
      (Fintype.card G:ℂ) * inner ℂ w v * inner ℂ u z := by
  obtain ⟨c,hc,htrace⟩ := averageMap_scalar ρ (InnerProductSpace.rankOne ℂ v w).toLinearMap
  rw [InnerProductSpace.trace_rankOne] at htrace
  have happ := congrArg (fun A : Module.End ℂ V => inner ℂ u (A z)) hc
  change inner ℂ u ((∑ g, ρ g * (InnerProductSpace.rankOne ℂ v w).toLinearMap * ρ g⁻¹) z) = _ at happ
  simp only [LinearMap.sum_apply,Module.End.mul_apply,ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply,map_smul,unitary_inner_inv ρ hρ,inner_sum,
    inner_smul_right,LinearMap.smul_apply,LinearMap.id_apply] at happ
  have hsum : ∑ g, inner ℂ u (ρ g v) * inner ℂ (ρ g w) z = c * inner ℂ u z := by
    simpa only [mul_comm] using happ
  rw [hsum]
  calc
    _ = (c*(Module.finrank ℂ V:ℂ))*inner ℂ u z := by ring
    _ = _ := by rw [htrace]

end Thorp.UnitaryFinite
namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G X : Type*} [Group G] [Fintype G] [Fintype X]
  (a : G →* Equiv.Perm X) (x₀ : X) (ha : ∀ x, ∃ g, a g x₀=x)

omit [Fintype G] [Fintype X] in
lemma representative_apply (x : X) : a (representative a x₀ ha x) x₀=x :=
  Classical.choose_spec (ha x)

include ha in
lemma orbit_sum (F : X → ℂ) :
    (Fintype.card X:ℂ)*∑ g, F (a g x₀) = (Fintype.card G:ℂ)*∑ x, F x := by
  have ht (x : X) : ∑ g, F (a g x)=∑ g, F (a g x₀) := by
    obtain ⟨t,rfl⟩ := ha x
    symm
    apply Fintype.sum_equiv (Equiv.mulRight t⁻¹)
    intro g
    simp
  calc
    _ = ∑ x : X, ∑ g : G, F (a g x) := by simp only [ht,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ = ∑ g : G, ∑ x : X, F (a g x) := Finset.sum_comm
    _ = ∑ g : G, ∑ x : X, F x := by
      apply Finset.sum_congr rfl
      intro g _
      exact Equiv.sum_comp (a g) F
    _ = _ := by simp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

omit [Fintype G] [Fintype X] [FiniteDimensional ℂ V] in
lemma coefficient_at (w : V) (hw : IsFixed a x₀ ρ w) (v : V) (g : G) :
    coefficient a x₀ ha ρ w v (a g x₀) = inner ℂ (ρ g w) v := by
  let r := representative a x₀ ha (a g x₀)
  have hr : a r x₀=a g x₀ := representative_apply a x₀ ha _
  have hs : a (g⁻¹*r) x₀=x₀ := by
    simp only [map_mul,Equiv.Perm.mul_apply]
    rw [hr,←Equiv.Perm.mul_apply,←map_mul,inv_mul_cancel,map_one]
    rfl
  have he := congrArg (ρ g) (hw (g⁻¹*r) hs)
  have hh : ρ r w=ρ g w := by
    simpa only [map_mul,Module.End.mul_apply,←Module.End.mul_apply,←map_mul,
      mul_inv_cancel_left] using he
  change inner ℂ (ρ r w) v= _
  rw [hh]

lemma coefficient_inner [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (w z : V) (hw : IsFixed a x₀ ρ w) (hz : IsFixed a x₀ ρ z) (v t : V) :
    (Module.finrank ℂ V:ℂ)*inner ℂ (coefficient a x₀ ha ρ w v) (coefficient a x₀ ha ρ z t) =
      (Fintype.card X:ℂ)*inner ℂ z w*inner ℂ v t := by
  have hs := orbit_sum a x₀ ha (fun x => star (coefficient a x₀ ha ρ w v x)*coefficient a x₀ ha ρ z t x)
  simp only [coefficient_at a x₀ ha ρ w hw,coefficient_at a x₀ ha ρ z hz] at hs
  simp only [←starRingEnd_apply,inner_conj_symm] at hs
  simp only [starRingEnd_apply] at hs
  have ho := coefficient_orthogonality ρ hρ v w z t
  have hcard : (Fintype.card G:ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hcard
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,starRingEnd_apply]
  have hsum : ∑ x, coefficient a x₀ ha ρ z t x * star (coefficient a x₀ ha ρ w v x) =
      ∑ x, star (coefficient a x₀ ha ρ w v x)*coefficient a x₀ ha ρ z t x := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  calc
    _ = (Module.finrank ℂ V:ℂ)*((Fintype.card G:ℂ)*∑ x,
        star (coefficient a x₀ ha ρ w v x)*coefficient a x₀ ha ρ z t x) := by ring
    _ = (Fintype.card X:ℂ)*((Module.finrank ℂ V:ℂ)*∑ g,
        inner ℂ v (ρ g w)*inner ℂ (ρ g z) t) := by rw [←hs]; ring
    _ = _ := by rw [ho]; ring

omit [Fintype G] [Fintype X] [FiniteDimensional ℂ V] in
lemma coefficient_action (hρ : IsUnitary ρ) (w : V) (hw : IsFixed a x₀ ρ w)
    (v : V) (g : G) (x : X) :
    coefficient a x₀ ha ρ w v (a g x) = coefficient a x₀ ha ρ w (ρ g⁻¹ v) x := by
  obtain ⟨r,rfl⟩ := ha x
  rw [←Equiv.Perm.mul_apply,←map_mul,coefficient_at a x₀ ha ρ w hw,
    coefficient_at a x₀ ha ρ w hw]
  simp only [map_mul,Module.End.mul_apply,unitary_inner_inv ρ hρ]

lemma normalizedCoefficient_inner [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (w z : V) (hw : IsFixed a x₀ ρ w) (hz : IsFixed a x₀ ρ z) (v t : V) :
    inner ℂ (normalizedCoefficient a x₀ ha ρ w v) (normalizedCoefficient a x₀ ha ρ z t) =
      inner ℂ z w*inner ℂ v t := by
  let : Nonempty X := ⟨x₀⟩
  have hX : (Fintype.card X:ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (Real.sqrt ((Module.finrank ℂ V:ℝ)/(Fintype.card X:ℝ)) : ℂ)^2 =
      (Module.finrank ℂ V:ℂ)/(Fintype.card X:ℂ) := by
    rw [←Complex.ofReal_pow,Real.sq_sqrt (by positivity)]
    simp
  simp only [normalizedCoefficient,inner_smul_left,inner_smul_right]
  simp only [Complex.conj_ofReal]
  rw [←mul_assoc,←pow_two,hs]
  have hi := coefficient_inner a x₀ ha ρ hρ w z hw hz v t
  field_simp
  simpa only [mul_assoc] using hi

lemma normalizedCoefficient_orthonormal [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    {I : Type*} (w : I → V) (hw : Orthonormal ℂ w)
    (hfix : ∀ i, IsFixed a x₀ ρ (w i)) (v : V) (hv : ‖v‖=1) :
    Orthonormal ℂ (fun i => normalizedCoefficient a x₀ ha ρ (w i) v) := by
  rw [orthonormal_iff_ite] at hw ⊢
  intro i j
  rw [normalizedCoefficient_inner a x₀ ha ρ hρ _ _ (hfix i) (hfix j),hw,
    inner_self_eq_norm_sq_to_K,hv]
  simp [eq_comm]

lemma normalizedCoefficient_norm [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (w : V) (hw : IsFixed a x₀ ρ w) (hn : ‖w‖=1) (v : V) :
    ‖normalizedCoefficient a x₀ ha ρ w v‖=‖v‖ := by
  have he := normalizedCoefficient_inner a x₀ ha ρ hρ w w hw hw v v
  rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K,hn] at he
  simp only [inner_self_eq_norm_sq_to_K] at he
  norm_num at he
  have hs : ‖normalizedCoefficient a x₀ ha ρ w v‖^2=‖v‖^2 := by exact_mod_cast he
  nlinarith [norm_nonneg (normalizedCoefficient a x₀ ha ρ w v),norm_nonneg v]

end Thorp.UnitaryFinite

namespace Thorp.UnitaryFinite

section
open scoped BigOperators ComplexConjugate Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma unitary_norm (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) (v : V) :
    ‖ρ g v‖=‖v‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),hρ,norm_eq_sqrt_re_inner (𝕜 := ℂ)]

omit [Fintype G] in
lemma continuousRepresentation_norm_le (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) :
    ‖continuousRepresentation ρ g‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [continuousRepresentation_apply,unitary_norm ρ hρ,one_mul,le_refl]

omit [Fintype G] in
lemma continuousRepresentation_adjoint (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (g : G) :
    (continuousRepresentation ρ g).adjoint=continuousRepresentation ρ g⁻¹ := by
  ext w
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (unitary_inner_inv ρ hρ g v w).symm

lemma weightedOperator_norm_le (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∀ g, 0≤p g) : ‖weightedOperator ρ p‖ ≤ ∑ g, p g := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro g _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp g)]
  exact mul_le_of_le_one_right (hp g) (continuousRepresentation_norm_le ρ hρ g)

lemma weightedOperator_symmetric (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∀ g, p g⁻¹=p g) : IsSelfAdjoint (weightedOperator ρ p) := by
  change (weightedOperator ρ p).adjoint=weightedOperator ρ p
  unfold weightedOperator
  rw [map_sum]
  simp only [map_smulₛₗ,Complex.conj_ofReal,continuousRepresentation_adjoint ρ hρ]
  apply Fintype.sum_equiv (Equiv.inv G)
  intro g
  simp [hp]

lemma uniformOperator_symmetric (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) :
    IsSelfAdjoint (uniformOperator ρ) := weightedOperator_symmetric ρ hρ _ (fun _ => rfl)

lemma uniformOperator_left (ρ : Representation ℂ G V) (g : G) :
    continuousRepresentation ρ g * uniformOperator ρ=uniformOperator ρ := by
  unfold uniformOperator weightedOperator
  rw [Finset.mul_sum]
  simp only [mul_smul_comm,←map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

lemma uniformOperator_right (ρ : Representation ℂ G V) (g : G) :
    uniformOperator ρ * continuousRepresentation ρ g=uniformOperator ρ := by
  unfold uniformOperator weightedOperator
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc,←map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

lemma uniformOperator_idempotent (ρ : Representation ℂ G V) :
    IsIdempotentElem (uniformOperator ρ) := by
  change uniformOperator ρ * uniformOperator ρ=uniformOperator ρ
  nth_rw 1 [uniformOperator,weightedOperator]
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc,uniformOperator_left,Finset.sum_const,Finset.card_univ,
    ←Nat.cast_smul_eq_nsmul ℂ,smul_smul,Complex.ofReal_inv,Complex.ofReal_natCast]
  rw [mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_smul]

lemma uniformOperator_projection (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) :
    IsStarProjection (uniformOperator ρ) :=
  ⟨uniformOperator_idempotent ρ,uniformOperator_symmetric ρ hρ⟩

lemma weighted_uniform_left (ρ : Representation ℂ G V) (p : G → ℝ) :
    weightedOperator ρ p * uniformOperator ρ=(∑ g,p g : ℝ) • uniformOperator ρ := by
  unfold weightedOperator
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc,uniformOperator_left,←Finset.sum_smul,←Complex.ofReal_sum]
  rfl

lemma weighted_uniform_right (ρ : Representation ℂ G V) (p : G → ℝ) :
    uniformOperator ρ * weightedOperator ρ p=(∑ g,p g : ℝ) • uniformOperator ρ := by
  unfold weightedOperator
  rw [Finset.mul_sum]
  simp only [mul_smul_comm,uniformOperator_right,←Finset.sum_smul,←Complex.ofReal_sum]
  rfl

theorem doeblin_off_invariants (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∑ g,p g=1) (ε : ℝ)
    (hminor : ∀ g, ε/(Fintype.card G:ℝ)≤p g) :
    ‖weightedOperator ρ p * (1-uniformOperator ρ)‖≤1-ε := by
  let q : G → ℝ := fun g => p g-ε/(Fintype.card G:ℝ)
  have hq : ∀ g, 0≤q g := fun g => sub_nonneg.mpr (hminor g)
  have hcard : (Fintype.card G:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ g,q g=1-ε := by
    simp only [q,Finset.sum_sub_distrib,hp,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
  have he : weightedOperator ρ p=weightedOperator ρ q+(ε:ℂ) • uniformOperator ρ := by
    simp only [uniformOperator,weightedOperator]
    rw [Finset.smul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g _
    simp only [q,Complex.ofReal_sub,Complex.ofReal_div,smul_smul,←add_smul,
      Complex.ofReal_inv,Complex.ofReal_natCast]
    congr 1
    field_simp
    ring
  have hz : uniformOperator ρ*(1-uniformOperator ρ)=0 := by
    rw [mul_sub,mul_one,(uniformOperator_idempotent ρ).eq,sub_self]
  rw [he,add_mul,smul_mul_assoc,hz,smul_zero,add_zero]
  calc
    _ ≤ ‖weightedOperator ρ q‖*‖1-uniformOperator ρ‖ := norm_mul_le _ _
    _ ≤ (1-ε)*1 := mul_le_mul (by rw [←hsum]; exact weightedOperator_norm_le ρ hρ q hq)
      ((uniformOperator_projection ρ hρ).one_sub.norm_le _) (norm_nonneg _)
      (by rw [←hsum]; exact Finset.sum_nonneg (fun g _ => hq g))
    _ = _ := mul_one _

end
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma weightedOperator_conv (ρ : Representation ℂ G V) (p q : G → ℝ) :
    weightedOperator ρ (FiniteConvolution.conv p q)=weightedOperator ρ p*weightedOperator ρ q := by
  unfold weightedOperator FiniteConvolution.conv
  simp only [Complex.ofReal_sum,Finset.sum_smul]
  rw [Finset.sum_comm,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,←map_mul]
  apply Fintype.sum_equiv (Equiv.mulLeft h⁻¹)
  intro g
  simp [Complex.ofReal_mul,mul_comm]

lemma weightedOperator_power (ρ : Representation ℂ G V) (p : G → ℝ) (n : ℕ) :
    weightedOperator ρ (FiniteConvolution.power p n)=(weightedOperator ρ p)^n := by
  induction n with
  | zero => simp [FiniteConvolution.power,weightedOperator]
  | succ n ih => rw [FiniteConvolution.power,weightedOperator_conv,ih,pow_succ']

lemma off_invariants_pow (ρ : Representation ℂ G V) (p : G → ℝ)
    (hp : ∑ g,p g=1) (n : ℕ) (hn : n≠0) :
    (weightedOperator ρ p-uniformOperator ρ)^n=
      (weightedOperator ρ p)^n*(1-uniformOperator ρ) := by
  have hAP := weighted_uniform_left ρ p
  have hPA := weighted_uniform_right ρ p
  rw [hp,one_smul] at hAP hPA
  have hc : Commute (weightedOperator ρ p) (1-uniformOperator ρ) := by
    show _*_= _*_
    rw [mul_sub,sub_mul,mul_one,one_mul,hAP,hPA]
  have he : weightedOperator ρ p-uniformOperator ρ=
      weightedOperator ρ p*(1-uniformOperator ρ) := by rw [mul_sub,mul_one,hAP]
  rw [he,hc.mul_pow,((uniformOperator_idempotent ρ).one_sub).pow_eq hn]

omit [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] in
lemma minorantGap_pos {p : G → ℝ} (c : FiniteConvolution.Minorant p) : 0 < minorantGap c := by
  have hn : (1:ℝ) ≤ 2^c.exponent := one_le_pow₀ (by norm_num)
  have hq : c.mass/(2*(2:ℝ)^c.exponent) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [c.mass_le_one]
  unfold minorantGap
  linarith

omit [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] in
lemma minorantGap_lt_one {p : G → ℝ} (c : FiniteConvolution.Minorant p) : minorantGap c < 1 := by
  unfold minorantGap
  exact sub_lt_self _ (div_pos c.mass_pos (by positivity))

theorem norm_off_invariants_le_gap (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (p : G → ℝ) (hp : ∑ g,p g=1) (hsym : ∀ g,p g⁻¹=p g)
    (c : FiniteConvolution.Minorant p) :
    ‖weightedOperator ρ p-uniformOperator ρ‖ ≤ minorantGap c := by
  have hself := (weightedOperator_symmetric ρ hρ p hsym).sub (uniformOperator_symmetric ρ hρ)
  have hbound := doeblin_off_invariants ρ hρ (FiniteConvolution.power p (2^c.exponent))
    (FiniteConvolution.sum_power hp _) c.mass c.lower
  rw [weightedOperator_power,←off_invariants_pow ρ p hp _ (by positivity),
    hself.norm_pow_two_pow] at hbound
  have hn : (1:ℝ) ≤ 2^c.exponent := one_le_pow₀ (by norm_num)
  have hq : c.mass/(2*(2:ℝ)^c.exponent) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [c.mass_le_one]
  have hbern := one_add_mul_le_pow
    (a := -(c.mass/(2*(2:ℝ)^c.exponent))) (by linarith : (-2:ℝ) ≤ -(c.mass/(2*(2:ℝ)^c.exponent)))
    (2^c.exponent)
  have he : 1+(2^c.exponent:ℕ)*(-(c.mass/(2*(2:ℝ)^c.exponent)))=1-c.mass/2 := by
    push_cast
    field_simp
    ring
  rw [he,show 1+ -(c.mass/(2*(2:ℝ)^c.exponent))=minorantGap c by rfl] at hbern
  by_contra h
  have hlt : minorantGap c < ‖weightedOperator ρ p-uniformOperator ρ‖ := lt_of_not_ge h
  have hpows := pow_lt_pow_left₀ hlt (minorantGap_pos c).le (by positivity : (2^c.exponent:ℕ)≠0)
  linarith [c.mass_pos]

end Thorp.UnitaryFinite
namespace Thorp
open scoped BigOperators Classical

variable {Ω G : Type*} [Fintype Ω] [Fintype G]

omit [Fintype G] in
lemma sampleLaw_equiv {Ω' : Type*} [Fintype Ω'] (P : Ω → G) (e : Ω' ≃ Ω) :
    sampleLaw (P ∘ e)=sampleLaw P := by
  funext g
  simpa only [sampleLaw,Function.comp_apply,Equiv.apply_symm_apply] using
    finiteMean_equiv e (fun ω => if P (e ω)=g then (1:ℝ) else 0)

variable [Group G]
omit [Fintype G] in
lemma sampleLaw_inverse (P : Ω → G) (g : G) :
    sampleLaw (fun ω => (P ω)⁻¹) g=sampleLaw P g⁻¹ := by
  apply finiteMean_congr
  intro ω
  rw [inv_eq_iff_eq_inv]

omit [Fintype G] in
lemma sampleLaw_symmetric (P : Ω → G) (e : Equiv.Perm Ω)
    (he : ∀ ω,P (e ω)=(P ω)⁻¹) (g : G) : sampleLaw P g⁻¹=sampleLaw P g := by
  rw [←sampleLaw_inverse]
  have hh : (fun ω => (P ω)⁻¹)=P ∘ e := funext (fun ω => (he ω).symm)
  rw [hh,sampleLaw_equiv]

end Thorp

namespace Thorp
open scoped BigOperators Classical

lemma blockGap_pos (d : ℕ) : 0<blockGap d := UnitaryFinite.minorantGap_pos _
lemma blockGap_lt_one (d : ℕ) : blockGap d<1 := UnitaryFinite.minorantGap_lt_one _

theorem palindrome_off_invariants_gap (d : ℕ) {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) (hρ : UnitaryFinite.IsUnitary ρ) :
    ‖UnitaryFinite.weightedOperator ρ (sampleLaw (palindromePerm d))-
      UnitaryFinite.uniformOperator ρ‖≤blockGap d := by
  apply UnitaryFinite.norm_off_invariants_le_gap ρ hρ _ (sampleLaw_sum _)
  exact sampleLaw_symmetric _ (Equiv.prodComm _ _) (palindromePerm_reverse d)

end Thorp

namespace Thorp.CommutingBlocks
open scoped BigOperators Classical
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {ι : Type*} [Fintype ι]

omit [CompleteSpace V] in
lemma orthogonal_sum_norm_sq (v : ι → V) (hv : ∀ i j, i≠j → inner ℂ (v i) (v j)=0) :
    ‖∑ i,v i‖^2=∑ i,‖v i‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),sum_inner]
  simp only [inner_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact (norm_sq_eq_re_inner (𝕜 := ℂ) (v i)).symm
  · intro j _ hji
    rw [hv i j hji.symm]
    rfl
  · simp

lemma projection_inner_zero (P Q : V →L[ℂ] V) (hP : IsStarProjection P)
    (hPQ : P*Q=0) (v w : V) : inner ℂ (P v) (Q w)=0 := by
  rw [←ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ v ((star P*Q) w)=0
  rw [hP.isSelfAdjoint.star_eq,hPQ]
  simp

lemma projection_sandwich_norm (P B : V →L[ℂ] V) (hP : IsStarProjection P) :
    ‖B.adjoint*P*B‖=‖P*B‖^2 := by
  have he : star (P*B)*(P*B)=B.adjoint*P*B := by
    rw [star_mul,hP.isSelfAdjoint.star_eq]
    change B.adjoint*P*(P*B)=_
    rw [←mul_assoc,mul_assoc B.adjoint P P,hP.isIdempotentElem.eq]
  rw [←he,CStarRing.norm_star_mul_self]
  ring

theorem resolution_norm_bound (P : ι → V →L[ℂ] V)
    (hP : ∀ i, IsStarProjection (P i))
    (horth : ∀ i j, i≠j → P i*P j=0) (hsum : ∑ i,P i=1)
    (A : V →L[ℂ] V) (hcomm : ∀ i, Commute A (P i))
    (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ i, ‖A*P i‖ ≤ c) : ‖A‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro v
  have hsplit (w : V) : ∑ i,P i w=w := by
    rw [←sum_apply,hsum]
    rfl
  have hp := orthogonal_sum_norm_sq (fun i => P i v)
    (fun i j hij => projection_inner_zero _ _ (hP i) (horth i j hij) v v)
  rw [hsplit] at hp
  have ha := orthogonal_sum_norm_sq (fun i => P i (A v))
    (fun i j hij => projection_inner_zero _ _ (hP i) (horth i j hij) (A v) (A v))
  rw [hsplit] at ha
  have he (i : ι) : P i (A v)=(A*P i) (P i v) := by
    change (P i*A) v=(A*P i*P i) v
    rw [mul_assoc,(hP i).isIdempotentElem.eq,(hcomm i).eq]
  have hh (i : ι) : ‖P i (A v)‖ ≤ c*‖P i v‖ := by
    rw [he]
    exact ((A*P i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hbound i) (norm_nonneg _))
  have hsq := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (hh i) 2)
  simp_rw [mul_pow] at hsq
  rw [←Finset.mul_sum,←hp,←ha,←mul_pow] at hsq
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp hsq

theorem sector_sandwich_le (T P A B : V →L[ℂ] V)
    (hT : IsStarProjection T) (hP : IsStarProjection P)
    (hTP : T*P=T) (hcomm : Commute A T) (hA : ‖A‖≤1) :
    ‖B.adjoint*A*T*B‖≤‖B.adjoint*P*B‖ := by
  have he : B.adjoint*A*T*B=(T*B).adjoint*A*(T*B) := by
    change _=star (T*B)*A*(T*B)
    rw [star_mul,hT.isSelfAdjoint.star_eq]
    change _=B.adjoint*T*A*(T*B)
    rw [mul_assoc B.adjoint T A,←hcomm.eq]
    simp only [mul_assoc]
    rw [←mul_assoc T T B,hT.isIdempotentElem.eq]
  have hTB : ‖T*B‖≤‖P*B‖ := by
    have he : T*B=T*(P*B) := by rw [←mul_assoc,hTP]
    rw [he]
    exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right (hT.norm_le _) (norm_nonneg _)).trans_eq (one_mul _))
  rw [he,projection_sandwich_norm P B hP]
  calc
    _ ≤ ‖(T*B).adjoint‖*‖A‖*‖T*B‖ := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ‖T*B‖^2 := by rw [ContinuousLinearMap.adjoint.norm_map]; nlinarith [norm_nonneg (T*B)]
    _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) hTB 2

omit [CompleteSpace V] [Fintype ι] in
lemma resolution_commute (P : ι → V →L[ℂ] V)
    (horth : ∀ i j, i≠j → P i*P j=0) (i j : ι) : Commute (P i) (P j) := by
  by_cases hij : i=j
  · subst j; exact Commute.refl _
  · exact (horth i j hij).trans (horth j i (Ne.symm hij)).symm

omit [Fintype ι] in
lemma resolution_sum_mul (P : ι → V →L[ℂ] V) (hP : ∀ i, IsStarProjection (P i))
    (horth : ∀ i j, i≠j → P i*P j=0) (S : Finset ι) (j : ι) :
    (∑ i∈S,P i)*P j=if j∈S then P j else 0 := by
  rw [Finset.sum_mul]
  have he (i : ι) : P i*P j=if i=j then P j else 0 := by
    split_ifs with h
    · subst i; exact (hP j).isIdempotentElem.eq
    · exact horth i j h
  simp only [he,Finset.sum_ite_eq']

lemma resolution_truncated_norm (P : ι → V →L[ℂ] V)
    (hP : ∀ i, IsStarProjection (P i))
    (horth : ∀ i j, i≠j → P i*P j=0) (hsum : ∑ i,P i=1)
    (A : V →L[ℂ] V) (hcomm : ∀ i, Commute A (P i))
    (S : Finset ι) (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ i∈S, ‖A*P i‖ ≤ c) :
    ‖A*(∑ i∈S,P i)‖ ≤ c := by
  apply resolution_norm_bound P hP horth hsum _ _ c hc
  · intro i
    rw [mul_assoc,resolution_sum_mul P hP horth]
    split_ifs with hi
    · exact hbound i hi
    · simp [hc]
  · intro i
    exact (hcomm i).mul_left (Commute.sum_left S P (P i) fun j _ => resolution_commute P horth j i)

theorem resolution_exception_bound (T Q : ι → V →L[ℂ] V)
    (hT : ∀ i, IsStarProjection (T i))
    (horth : ∀ i j, i≠j → T i*T j=0) (hsum : ∑ i,T i=1)
    (hQ : ∀ i, IsStarProjection (Q i)) (hTQ : ∀ i,T i*Q i=T i)
    (A B : V →L[ℂ] V) (hcomm : ∀ i, Commute A (T i))
    (hA : ‖A‖≤1) (hB : ‖B‖≤1)
    (S : Finset ι) (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ i∉S, ‖A*T i‖ ≤ c) :
    ‖B.adjoint*A*B‖ ≤ c+∑ i∈S,‖B.adjoint*Q i*B‖ := by
  have hhigh : ‖A*(∑ i∈Sᶜ,T i)‖ ≤ c := resolution_truncated_norm T hT horth hsum A hcomm
    Sᶜ c hc (fun i hi => hbound i (Finset.mem_compl.mp hi))
  have hsplit : (∑ i∈Sᶜ,T i)+(∑ i∈S,T i)=1 := by
    rw [Finset.sum_compl_add_sum,hsum]
  have he : B.adjoint*A*B=B.adjoint*(A*(∑ i∈Sᶜ,T i))*B+
      ∑ i∈S,B.adjoint*A*T i*B := by
    rw [←Finset.sum_mul,←Finset.mul_sum]
    rw [←add_mul]
    simp only [mul_assoc]
    rw [←mul_add,←mul_add,hsplit]
    simp only [mul_one,mul_assoc]
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      _ ≤ ‖B.adjoint‖*‖A*(∑ i∈Sᶜ,T i)‖*‖B‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1*c*1 := mul_le_mul (mul_le_mul (by simpa only [ContinuousLinearMap.adjoint.norm_map] using hB)
        hhigh (norm_nonneg _) zero_le_one) hB (norm_nonneg _) (by simpa using hc)
      _ = c := by ring
  · apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum fun i _ => sector_sandwich_le _ _ _ _ (hT i) (hQ i) (hTQ i) (hcomm i) hA

variable [DecidableEq ι]
variable (P : ι → V →L[ℂ] V) (hcomm : ∀ i j, Commute (P i) (P j))

include hcomm

omit [CompleteSpace V] [Fintype ι] in
lemma sector_insert (s E : Finset ι) (a : ι) (ha : a∉s) :
    sector P hcomm (insert a s) E=choice P E a*sector P hcomm s E := by
  exact Finset.noncommProd_insert_of_notMem _ _ _ _ ha

omit [CompleteSpace V] [Fintype ι] in
lemma sector_congr (s E F : Finset ι) (h : ∀ i∈s, (i∈E ↔ i∈F)) :
    sector P hcomm s E=sector P hcomm s F := by
  apply Finset.noncommProd_congr rfl
  intro i hi
  simp only [choice,h i hi]

omit [CompleteSpace V] [Fintype ι] in
lemma sector_factor_commute (s E F : Finset ι) (i : ι) :
    Commute (choice P E i) (sector P hcomm s F) :=
  Finset.noncommProd_commute _ _ _ _ (fun j _ => choice_commute P hcomm E F i j)

omit [Fintype ι] in
lemma sector_projection (hP : ∀ i, IsStarProjection (P i)) (s E : Finset ι) :
    IsStarProjection (sector P hcomm s E) := by
  induction s using Finset.induction_on with
  | empty => exact IsStarProjection.one _
  | @insert a s ha ih =>
    rw [sector_insert P hcomm s E a ha]
    have hc : IsStarProjection (choice P E a) := by
      unfold choice
      split_ifs
      · exact (hP a).one_sub
      · exact hP a
    exact hc.mul ih (sector_factor_commute P hcomm s E E a)

end Thorp.CommutingBlocks

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_BlockProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.CommutingBlocks
open scoped BigOperators Classical
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
variable (P : ι → V →L[ℂ] V) (hcomm : ∀ i j, Commute (P i) (P j))
include hcomm
omit [CompleteSpace V] [Fintype ι] in
lemma sector_sum (s : Finset ι) : ∑ E∈s.powerset, sector P hcomm s E=1 := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.powerset_empty,Finset.sum_singleton]
    exact Finset.noncommProd_empty _ _
  | @insert a s ha ih =>
    rw [Finset.sum_powerset_insert ha]
    have h₁ (E : Finset ι) (hE : E∈s.powerset) :
        sector P hcomm (insert a s) E=P a*sector P hcomm s E := by
      rw [sector_insert P hcomm s E a ha]
      congr 1
      exact ite_eq_right (fun h => ha ((Finset.mem_powerset.mp hE) h))
    have h₂ (E : Finset ι) (_hE : E∈s.powerset) :
        sector P hcomm (insert a s) (insert a E)=(1-P a)*sector P hcomm s E := by
      rw [sector_insert P hcomm s (insert a E) a ha]
      simp only [choice,Finset.mem_insert_self,↓reduceIte]
      congr 1
      apply sector_congr
      intro i hi
      simp [ne_of_mem_of_not_mem hi ha]
    rw [Finset.sum_congr rfl h₁,Finset.sum_congr rfl h₂,
      ←Finset.mul_sum,←Finset.mul_sum,ih]
    simp

omit [Fintype ι] in
lemma sector_absorb_factor (s E : Finset ι) (i : ι) (hi : i∈s)
    (hP : ∀ i, IsStarProjection (P i)) :
    choice P E i*sector P hcomm s E=sector P hcomm s E := by
  have hc : IsIdempotentElem (choice P E i) := by
    unfold choice
    split_ifs
    · exact (hP i).one_sub.isIdempotentElem
    · exact (hP i).isIdempotentElem
  have hsplit := Finset.mul_noncommProd_erase s hi (choice P E)
    (fun i _ j _ _ => choice_commute P hcomm E E i j)
  change choice P E i*sector P hcomm s E=sector P hcomm s E
  change _=sector P hcomm s E at hsplit
  nth_rw 1 [←hsplit]
  rw [←mul_assoc,hc.eq,hsplit]

omit [Fintype ι] in
lemma sector_orthogonal (s E F : Finset ι) (hE : E⊆s) (hF : F⊆s) (hEF : E≠F)
    (hP : ∀ i, IsStarProjection (P i)) :
    sector P hcomm s E*sector P hcomm s F=0 := by
  have hdiff : ∃ i∈s, ¬(i∈E ↔ i∈F) := by
    by_contra h
    push Not at h
    exact hEF (Finset.ext fun i => by
      by_cases hi : i∈s
      · exact h i hi
      · exact iff_of_false (fun h => hi (hE h)) (fun h => hi (hF h)))
  obtain ⟨i,hi,hdiff⟩ := hdiff
  have hz : choice P E i*choice P F i=0 := by
    by_cases he : i∈E <;> by_cases hf : i∈F
    · exact (hdiff (iff_of_true he hf)).elim
    · simpa only [choice,ite_eq_left he,ite_eq_right hf] using (hP i).one_sub_mul_self
    · simpa only [choice,ite_eq_right he,ite_eq_left hf] using (hP i).mul_one_sub_self
    · exact (hdiff (iff_of_false he hf)).elim
  have hEi := sector_absorb_factor P hcomm s E i hi hP
  have hFi := sector_absorb_factor P hcomm s F i hi hP
  calc
    _ = sector P hcomm s E*(choice P E i*choice P F i)*sector P hcomm s F := by
      simp only [mul_assoc]
      rw [hFi]
      rw [←mul_assoc,(sector_factor_commute P hcomm s E E i).eq.symm,hEi]
    _ = 0 := by rw [hz,mul_zero,zero_mul]

omit hcomm [Fintype ι] in
lemma norm_noncommProd_le (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j))
    (s : Finset ι) : ‖blockProduct A hA s‖≤∏ i∈s,‖A i‖ := by
  induction s using Finset.induction_on with
  | empty => exact ContinuousLinearMap.norm_id_le
  | @insert a s ha ih =>
    have he : blockProduct A hA (insert a s)=A a*blockProduct A hA s :=
      Finset.noncommProd_insert_of_notMem _ _ _ _ ha
    rw [he,Finset.prod_insert ha]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

omit hcomm in
lemma blocks_norm_le_one (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j))
    (hn : ∀ i,‖A i‖≤1) : ‖blocks A hA‖≤1 :=
  (norm_noncommProd_le A hA Finset.univ).trans (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hn i))

omit [CompleteSpace V] in
lemma blocks_sector_commute (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j))
    (hAP : ∀ i j, Commute (A i) (P j)) (E : Finset ι) :
    Commute (blocks A hA) (sector P hcomm Finset.univ E) := by
  unfold blocks blockProduct
  apply (Finset.noncommProd_commute _ _ (fun i _ j _ _ => hA i j) _ _).symm
  intro i _
  unfold sector
  apply (Finset.noncommProd_commute _ _ (fun i _ j _ _ => choice_commute P hcomm E E i j) _ _).symm
  intro j _
  unfold choice
  split_ifs
  · exact (Commute.one_right _).sub_right (hAP i j)
  · exact hAP i j

lemma blocks_sector_norm (hP : ∀ i, IsStarProjection (P i))
    (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j))
    (hAP : ∀ i j, Commute (A i) (P j)) (hn : ∀ i,‖A i‖≤1)
    (θ : ℝ) (_hθ : 0≤θ) (hgap : ∀ i,‖A i*(1-P i)‖≤θ) (E : Finset ι) :
    ‖blocks A hA*sector P hcomm Finset.univ E‖≤θ^E.card := by
  have hAC (i j : ι) : Commute (A i) (choice P E j) := by
    unfold choice
    split_ifs
    · exact (Commute.one_right _).sub_right (hAP i j)
    · exact hAP i j
  have hprod := Finset.noncommProd_mul_distrib (s := Finset.univ) A (choice P E)
    (fun i _ j _ _ => hA i j) (fun i _ j _ _ => choice_commute P hcomm E E i j)
    (fun i _ j _ _ => (hAC j i).symm)
  change _=blocks A hA*sector P hcomm Finset.univ E at hprod
  rw [←hprod]
  have hc (i j : ι) : Commute ((A*choice P E) i) ((A*choice P E) j) :=
    ((hA i j).mul_right (hAC i j)).mul_left ((hAC j i).symm.mul_right (choice_commute P hcomm E E i j))
  apply (norm_noncommProd_le _ hc Finset.univ).trans
  calc
    _ ≤ ∏ i : ι, if i∈E then θ else 1 := by
      apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
      intro i _
      dsimp only [Pi.mul_apply]
      unfold choice
      split_ifs with hi
      · exact hgap i
      · exact (norm_mul_le _ _).trans (by nlinarith [hn i,(hP i).norm_le (P i),norm_nonneg (A i),norm_nonneg (P i)])
    _ = _ := by rw [Fintype.prod_ite_mem,Finset.prod_const]

lemma coarse_projection (hP : ∀ i, IsStarProjection (P i)) (E : Finset ι) :
    IsStarProjection (coarse P hcomm E) := by
  have he : coarse P hcomm E=sector P hcomm Eᶜ ∅ := by
    apply Finset.noncommProd_congr rfl
    intro i _
    simp [choice]
  rw [he]
  exact sector_projection P hcomm hP _ _

lemma sector_coarse (hP : ∀ i, IsStarProjection (P i)) (E : Finset ι) :
    sector P hcomm Finset.univ E*coarse P hcomm E=sector P hcomm Finset.univ E := by
  have hpi (i : ι) (hi : i∈Eᶜ) : sector P hcomm Finset.univ E*P i=sector P hcomm Finset.univ E := by
    have h := sector_absorb_factor P hcomm Finset.univ E i (Finset.mem_univ i) hP
    rw [(sector_factor_commute P hcomm Finset.univ E E i).eq] at h
    simpa only [choice,ite_eq_right (Finset.mem_compl.mp hi)] using h
  have hp (s : Finset ι) (hs : ∀ i∈s,
      sector P hcomm Finset.univ E*P i=sector P hcomm Finset.univ E) :
      sector P hcomm Finset.univ E*blockProduct P hcomm s=sector P hcomm Finset.univ E := by
    induction s using Finset.induction_on with
    | empty => exact mul_one _
    | @insert a s ha ih =>
      have he : blockProduct P hcomm (insert a s)=P a*blockProduct P hcomm s :=
        Finset.noncommProd_insert_of_notMem _ _ _ _ ha
      rw [he,←mul_assoc,hs a (Finset.mem_insert_self _ _)]
      exact ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
  exact hp Eᶜ hpi

theorem blocks_exception_bound (hP : ∀ i, IsStarProjection (P i))
    (A : ι → V →L[ℂ] V) (hA : ∀ i j, Commute (A i) (A j))
    (hAP : ∀ i j, Commute (A i) (P j)) (hn : ∀ i,‖A i‖≤1)
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (hgap : ∀ i,‖A i*(1-P i)‖≤θ)
    (B : V →L[ℂ] V) (hB : ‖B‖≤1) (n : ℕ) :
    ‖B.adjoint*blocks A hA*B‖≤θ^n+
      ∑ E : Finset ι, if E.card<n then ‖B.adjoint*coarse P hcomm E*B‖ else 0 := by
  let T : Finset ι → V →L[ℂ] V := sector P hcomm Finset.univ
  have hsum : ∑ E,T E=1 := by
    simpa only [Finset.powerset_univ] using sector_sum P hcomm Finset.univ
  have hbound := resolution_exception_bound T (coarse P hcomm)
    (fun E => sector_projection P hcomm hP _ E)
    (fun E F hEF => sector_orthogonal P hcomm _ E F (Finset.subset_univ _) (Finset.subset_univ _) hEF hP)
    hsum (coarse_projection P hcomm hP) (sector_coarse P hcomm hP)
    (blocks A hA) B (blocks_sector_commute P hcomm A hA hAP)
    (blocks_norm_le_one A hA hn) hB (Finset.univ.filter fun E : Finset ι => E.card<n)
    (θ^n) (pow_nonneg hθ _) (by
      intro E hE
      have hEn : n≤E.card := by simpa using hE
      exact (blocks_sector_norm P hcomm hP A hA hAP hn θ hθ hgap E).trans
        (pow_le_pow_of_le_one hθ hθ1 hEn))
  simpa only [Finset.sum_filter] using hbound


end Thorp.CommutingBlocks

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma sampleOperator_weighted (ρ : Representation ℂ G V) (P : Ω → G) :
    sampleOperator ρ P=weightedOperator ρ (sampleLaw P) := by
  unfold sampleOperator weightedOperator sampleLaw finiteMean
  simp only [Complex.ofReal_sum,div_eq_mul_inv,Finset.sum_mul,Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  calc
    _ = ∑ g, if P ω=g then (Fintype.card Ω:ℂ)⁻¹ • continuousRepresentation ρ g else 0 := by
      symm
      simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g _
      split_ifs <;> simp_all

lemma sampleOperator_norm_le [Nonempty Ω] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (P : Ω → G) :
    ‖sampleOperator ρ P‖≤1 := by
  rw [sampleOperator_weighted]
  exact (weightedOperator_norm_le ρ hρ _ (sampleLaw_nonneg _)).trans_eq (sampleLaw_sum P)

omit [Fintype G] in
lemma sampleOperator_equiv (ρ : Representation ℂ G V) (P : Ω → G) (e : Ξ ≃ Ω) :
    sampleOperator ρ (P ∘ e)=sampleOperator ρ P := by
  simp only [sampleOperator,Fintype.card_congr e,Function.comp_apply]
  rw [Equiv.sum_comp e (fun ω => continuousRepresentation ρ (P ω))]

omit [Fintype G] in
lemma sampleOperator_prod (ρ : Representation ℂ G V) (P : Ω → G) (Q : Ξ → G) :
    sampleOperator ρ (fun ω : Ω × Ξ => P ω.1*Q ω.2)=sampleOperator ρ P*sampleOperator ρ Q := by
  simp only [sampleOperator,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,map_mul,Fintype.sum_prod_type,
    Finset.sum_mul,Finset.mul_sum,smul_mul_smul,Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro ξ _
  rw [mul_comm]

omit [Fintype G] in
lemma sampleOperator_inv (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (P : Ω → G) :
    sampleOperator ρ (fun ω => (P ω)⁻¹)=(sampleOperator ρ P).adjoint := by
  simp only [sampleOperator,map_smulₛₗ,map_sum,map_inv₀,map_natCast,
    continuousRepresentation_adjoint ρ hρ]

omit [Fintype G] in
lemma sampleOperator_one [Nonempty Ω] (ρ : Representation ℂ G V) :
    sampleOperator ρ (fun _ : Ω => 1)=1 := by
  simp only [sampleOperator,map_one,Finset.sum_const,Finset.card_univ,←Nat.cast_smul_eq_nsmul ℂ,
    smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_smul]

lemma sampleOperator_uniform_mul [Nonempty Ω] (ρ : Representation ℂ G V) (P : Ω → G) :
    sampleOperator ρ (fun ω : Ω × G => P ω.1*ω.2⁻¹)=uniformOperator ρ := by
  rw [sampleOperator_prod]
  have he : sampleOperator ρ (fun g : G => g⁻¹)=uniformOperator ρ := by
    rw [←sampleOperator_uniform]
    exact sampleOperator_equiv ρ id (Equiv.inv G)
  rw [he,sampleOperator_weighted,weighted_uniform_left,sampleLaw_sum,one_smul]

end Thorp.UnitaryFinite

namespace Thorp.FiniteAverage
open scoped BigOperators Classical
variable {I Ω A : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    [Ring A] [Algebra ℂ A]

lemma orderedProduct_eq (f : I → A) (hc : Pairwise fun i j => Commute (f i) (f j)) :
    orderedProduct f=Finset.univ.noncommProd f (fun _ _ _ _ hij => hc hij) := by
  unfold orderedProduct
  rw [MultilinearMap.domDomCongr_apply,MultilinearMap.mkPiAlgebraFin_apply]
  let l := List.ofFn (Fintype.equivFin I).symm
  have hl : l.Nodup := List.nodup_ofFn.mpr (Fintype.equivFin I).symm.injective
  have hu : l.toFinset=Finset.univ := by
    ext i
    simp only [List.mem_toFinset,List.mem_ofFn,Finset.mem_univ,iff_true,l]
    exact (Fintype.equivFin I).symm.surjective i
  have he := Finset.noncommProd_toFinset l f (by intro i hi j hj hij; exact hc hij) hl
  rw [hu] at he
  rw [he]
  congr 1
  exact List.map_ofFn.symm

lemma multilinear_average (F : MultilinearMap ℂ (fun _ : I => A) A) (x : I → Ω → A) :
    F (fun i => (Fintype.card Ω:ℂ)⁻¹ • ∑ ω,x i ω)=
      (Fintype.card (I → Ω):ℂ)⁻¹ • ∑ ω : I → Ω,F (fun i => x i (ω i)) := by
  rw [F.map_smul_univ,F.map_sum]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fun,Nat.cast_pow,inv_pow]

lemma ordered_average (x : I → Ω → A)
    (hc : ∀ ω, Pairwise fun i j => Commute (x i (ω i)) (x j (ω j)))
    (havg : Pairwise fun i j => Commute ((Fintype.card Ω:ℂ)⁻¹ • ∑ ω,x i ω)
      ((Fintype.card Ω:ℂ)⁻¹ • ∑ ω,x j ω)) :
    (Finset.univ.noncommProd (fun i => (Fintype.card Ω:ℂ)⁻¹ • ∑ ω,x i ω)
      (fun _ _ _ _ hij => havg hij))=
    (Fintype.card (I → Ω):ℂ)⁻¹ • ∑ ω : I → Ω,
      Finset.univ.noncommProd (fun i => x i (ω i)) (fun _ _ _ _ hij => hc ω hij) := by
  rw [←orderedProduct_eq _ havg,multilinear_average]
  simp only [orderedProduct_eq _ (hc _)]

end Thorp.FiniteAverage

namespace Thorp.ParallelBlocks
open scoped BigOperators Classical
variable {B X : Type*}

variable [Fintype B]

lemma lift_product (p : B → Equiv.Perm X) :
    lift p=Finset.univ.noncommProd (fun b => injection b (p b))
      (fun _ _ _ _ h => injection_commute h _ _) := by
  have he (s : Finset B) (x : B × X) :
      s.noncommProd (fun b => injection b (p b))
        (fun _ _ _ _ h => injection_commute h _ _) x=
          (x.1,if x.1∈s then p x.1 x.2 else x.2) := by
    induction s using Finset.induction_on with
    | empty =>
      have hz : Finset.noncommProd (∅ : Finset B) (fun b => injection b (p b))
          (fun _ _ _ _ h => injection_commute h _ _)=1 := Finset.noncommProd_empty _ _
      rw [hz]; simp
    | @insert a s ha ih =>
      have hz : (insert a s).noncommProd (fun b => injection b (p b))
          (fun _ _ _ _ h => injection_commute h _ _)=injection a (p a)*
          s.noncommProd (fun b => injection b (p b))
            (fun _ _ _ _ h => injection_commute h _ _) :=
        Finset.noncommProd_insert_of_notMem _ _ _ _ ha
      rw [hz,Equiv.Perm.mul_apply,ih,injection_apply]
      by_cases h : x.1=a
      · subst a; simp [ha]
      · simp [h]
  apply Equiv.ext
  intro x
  rw [he]
  simp

end Thorp.ParallelBlocks
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {G H : Type*} [Group G] [Group H]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

omit [FiniteDimensional ℂ V] in
lemma unitary_comp (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (φ : H →* G) :
    IsUnitary (ρ.comp φ) := fun h v w => hρ (φ h) v w

lemma sampleOperator_uniform_absorb [Fintype G] [Nonempty Ω]
    (ρ : Representation ℂ G V) (P : Ω → G) :
    sampleOperator ρ P*uniformOperator ρ=uniformOperator ρ := by
  rw [sampleOperator_weighted,weighted_uniform_left,sampleLaw_sum,one_smul]

end Thorp.UnitaryFinite
namespace Thorp.ParallelBlocks
open scoped BigOperators Classical
open UnitaryFinite
variable {B X Ω : Type*} [Fintype B] [DecidableEq B] [Fintype Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma sampleOperator_parallel (ρ : Representation ℂ (Equiv.Perm (B × X)) V)
    (P : B → Ω → Equiv.Perm X) :
    sampleOperator ρ (fun ω : B → Ω => lift (fun b => P b (ω b)))=
      CommutingBlocks.blocks (fun b => sampleOperator (ρ.comp (injection b)) (P b))
        (local_average_commute ρ P) := by
  let A (b : B) (w : Ω) := continuousRepresentation ρ (injection b (P b w))
  have hc : ∀ ω : B → Ω, Pairwise fun b c => Commute (A b (ω b)) (A c (ω c)) := by
    intro ω b c h
    exact (injection_commute h _ _).map (continuousRepresentation ρ)
  have havg : Pairwise fun b c => Commute ((Fintype.card Ω:ℂ)⁻¹ • ∑ w,A b w)
      ((Fintype.card Ω:ℂ)⁻¹ • ∑ w,A c w) := by
    intro b c _
    exact local_average_commute ρ P b c
  have he (ω : B → Ω) : continuousRepresentation ρ (lift (fun b => P b (ω b)))=
      Finset.univ.noncommProd (fun b => A b (ω b)) (fun _ _ _ _ h => hc ω h) := by
    rw [lift_product]
    exact Finset.map_noncommProd _ _ _ (continuousRepresentation ρ)
  unfold sampleOperator
  simp_rw [he]
  exact (FiniteAverage.ordered_average A hc havg).symm

end Thorp.ParallelBlocks
namespace Thorp
open scoped BigOperators Classical

lemma splitPerm_butterfly (r L : ℕ) (lo : Card r × SwitchIndex L → Bool)
    (hi : Card L × SwitchIndex r → Bool) :
    splitPerm r L (butterflyPerm (L+r) (decodeButterfly (L+r) (assembleBits r L lo hi)))=
      outerPerm r L hi*ParallelBlocks.lift
        (fun b => butterflyPerm L (decodeButterfly L (fun i => lo (b,i)))) := by
  apply Equiv.ext
  intro x
  change cardSplit r L (butterflyPerm (L+r) (decodeButterfly (L+r) (assembleBits r L lo hi))
    ((cardSplit r L).symm x))=_
  rw [butterfly_split,Equiv.apply_symm_apply]
  rfl

lemma boundaryTree_node_raw (L r : ℕ) (U : Card (r+1) → Equiv.Perm (Card L))
    (X : SwitchIndex (L+r+1) → Bool) :
    boundaryTree L (r+1) U X=InputTree.node (fun y => X (Sum.inl y))
      (fun b => boundaryTree L r (fun u => U (Fin.cons b u)) (fun i => X (Sum.inr (b,i)))) := by
  conv_lhs => unfold boundaryTree
  congr 1
  funext b
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> rfl

lemma boundaryOutput_node_raw (L r : ℕ) (Y : SwitchIndex (L+r+1) → Bool) (b : Card (r+1)) :
    boundaryOutput L (r+1) Y b=
      boundaryOutput L r (fun i => Y (Sum.inr (b 0,i))) (Fin.tail b) := by
  conv_lhs => unfold boundaryOutput
  cases b 0 <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> rfl

lemma boundaryTree_split (L r : ℕ) (U : Card r → Equiv.Perm (Card L))
    (lo : Card r × SwitchIndex L → Bool) (hi : Card L × SwitchIndex r → Bool) (x : Card (L+r)) :
    cardSplit r L ((boundaryTree L r U (assembleBits r L lo hi)).perm x)=
      let y := cardSplit r L x
      let z := U y.1 y.2
      (butterflyPerm r (decodeButterfly r (fun i => hi (z,i))) y.1,z) := by
  induction r with
  | zero =>
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  | succ r ih =>
    let lo' : Card r × SwitchIndex L → Bool := fun j => lo (Fin.cons (x 0) j.1,j.2)
    let hi' : Card L × SwitchIndex r → Bool := fun j => hi (j.1,Sum.inr (x 0,j.2))
    let U' : Card r → Equiv.Perm (Card L) := fun b => U (Fin.cons (x 0) b)
    have hh := ih U' lo' hi' (Fin.tail x)
    let u := (boundaryTree L r U' (assembleBits r L lo' hi')).perm (Fin.tail x)
    let y := cardSplit r L (Fin.tail x)
    let z := U' y.1 y.2
    let w := butterflyPerm r (decodeButterfly r (fun i => hi' (z,i))) y.1
    change cardSplit r L u=(w,z) at hh
    rw [boundaryTree_node_raw]
    change ((Fin.cons (Bool.xor (x 0) (hi ((cardSplit r L u).2,Sum.inl (cardSplit r L u).1)))
      ((cardSplit r L u).1) : Card (r+1)),(cardSplit r L u).2)=
        ((Fin.cons (Bool.xor (x 0) (hi (z,Sum.inl w))) w : Card (r+1)),z)
    rw [hh]

lemma splitPerm_boundaryTree (L r : ℕ) (U : Card r → Equiv.Perm (Card L))
    (lo : Card r × SwitchIndex L → Bool) (hi : Card L × SwitchIndex r → Bool) :
    splitPerm r L (boundaryTree L r U (assembleBits r L lo hi)).perm=
      outerPerm r L hi*ParallelBlocks.lift U := by
  apply Equiv.ext
  intro x
  change cardSplit r L ((boundaryTree L r U (assembleBits r L lo hi)).perm
    ((cardSplit r L).symm x))=_
  rw [boundaryTree_split,Equiv.apply_symm_apply]
  rfl

lemma boundaryOutput_split (L r : ℕ) (lo : Card r × SwitchIndex L → Bool)
    (hi : Card L × SwitchIndex r → Bool) (b : Card r) :
    boundaryOutput L r (assembleBits r L lo hi) b=
      butterflyPerm L (decodeButterfly L (fun i => lo (b,i))) := by
  induction r with
  | zero =>
    rw [Subsingleton.elim b (fun j => Fin.elim0 j)]
    rfl
  | succ r ih =>
    rw [boundaryOutput_node_raw]
    change boundaryOutput L r (assembleBits r L (fun j => lo (Fin.cons (b 0) j.1,j.2))
      (fun j => hi (j.1,Sum.inr (b 0,j.2)))) (Fin.tail b)=_
    rw [ih]
    simp only [Fin.cons_self_tail]


lemma parallelSplitCoinEquiv_apply (r L : ℕ) (c : Card r → LocalCoins L) (h : OuterCoins r L) :
    parallelSplitCoinEquiv r L (c,h)=assembleBits r L (fun x => c x.1 x.2) h := by
  exact splitCoinEquiv_apply _ _ _ _

lemma palindromeStageEquiv_apply (r L : ℕ)
    (w : (OuterCoins r L × (Card r → BenesCoins L)) × OuterCoins r L) :
    palindromeStageEquiv r L w=
      (assembleBits r L (fun x => (w.1.2 x.1).1 x.2) w.1.1,
       assembleBits r L (fun x => (w.1.2 x.1).2 x.2) w.2) := by
  simp only [palindromeStageEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,pairAssembleEquiv,
    Equiv.coe_fn_mk,Prod.map_apply,parallelSplitCoinEquiv_apply]

end Thorp

end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_ModifiedStageEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp
open scoped BigOperators Classical

lemma modifiedStageEquiv_apply (r L : ℕ)
    (w : (OuterCoins r L × (Card r → Equiv.Perm (Card L) × BenesCoins L)) × OuterCoins r L) :
    modifiedStageEquiv r L w=
      ((fun b => (w.1.2 b).1),
       (assembleBits r L (fun x => (w.1.2 x.1).2.1 x.2) w.1.1,
        assembleBits r L (fun x => (w.1.2 x.1).2.2 x.2) w.2)) := by
  simp only [modifiedStageEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,modifiedAssembleEquiv,
    Equiv.coe_fn_mk,Prod.map_apply,Equiv.refl_apply,parallelSplitCoinEquiv_apply]

lemma palindrome_stage (r L : ℕ)
    (w : (OuterCoins r L × (Card r → BenesCoins L)) × OuterCoins r L) :
    splitPerm r L (palindromePerm (L+r) (palindromeStageEquiv r L w))=
      outerPerm r L w.1.1*ParallelBlocks.lift (fun b => palindromePerm L (w.1.2 b))*
        (outerPerm r L w.2)⁻¹ := by
  rw [palindromeStageEquiv_apply]
  change splitPerm r L (_*_⁻¹)=_
  rw [map_mul,map_inv,splitPerm_butterfly,splitPerm_butterfly,mul_inv_rev]
  rw [mul_assoc,←mul_assoc (ParallelBlocks.lift _),←map_inv,←map_mul,←mul_assoc]
  rfl

lemma modified_stage (r L : ℕ) (E : Finset (Card r))
    (w : (OuterCoins r L × (Card r → Equiv.Perm (Card L) × BenesCoins L)) × OuterCoins r L) :
    splitPerm r L (modifiedPerm L r E (modifiedStageEquiv r L w))=
      outerPerm r L w.1.1*ParallelBlocks.lift (fun b => localModifiedPerm L (decide (b∈E)) (w.1.2 b))*
        (outerPerm r L w.2)⁻¹ := by
  rw [modifiedStageEquiv_apply]
  unfold modifiedPerm modifiedInputTree
  rw [map_mul,map_inv,splitPerm_butterfly,splitPerm_boundaryTree,mul_inv_rev]
  rw [mul_assoc,←mul_assoc (ParallelBlocks.lift _),←map_inv,←map_mul,←mul_assoc]
  congr 2
  apply congrArg ParallelBlocks.lift
  funext b
  simp only [Pi.mul_apply,Pi.inv_apply,modifiedBoundary,boundaryOutput_split,localModifiedPerm]
  by_cases h : b∈E <;> simp [h]

end Thorp
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical
variable {G : Type*} [Group G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma sampleOperator_sandwich (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (P : Ω → G) (Q : Ξ → G) :
    sampleOperator ρ (fun w : (Ω × Ξ) × Ω => P w.1.1*Q w.1.2*(P w.2)⁻¹)=
      sampleOperator ρ P*sampleOperator ρ Q*(sampleOperator ρ P).adjoint := by
  rw [sampleOperator_prod ρ (fun w : Ω × Ξ => P w.1*Q w.2) (fun w : Ω => (P w)⁻¹),
    sampleOperator_prod ρ P Q,sampleOperator_inv ρ hρ]

lemma localModified_average (L : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card L)) V) (e : Bool) :
    sampleOperator ρ (localModifiedPerm L e)=if e then 1 else uniformOperator ρ := by
  cases e
  · simp only [Bool.false_eq_true,ite_false]
    rw [←sampleOperator_equiv ρ _ (Equiv.prodComm _ _)]
    exact sampleOperator_uniform_mul ρ (fun w : BenesCoins L => butterflyPerm L (decodeButterfly L w.1))
  · simp only [ite_true]
    exact sampleOperator_one ρ

end Thorp.UnitaryFinite

namespace Thorp
open scoped BigOperators Classical
open UnitaryFinite
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma sampleOperator_palindrome_stage (r L : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) (hρ : IsUnitary ρ) :
    sampleOperator (ρ.comp (splitPerm r L).toMonoidHom) (palindromePerm (L+r))=
      sampleOperator ρ (outerPerm r L)*
        sampleOperator ρ (fun w : Card r → BenesCoins L => ParallelBlocks.lift (fun b => palindromePerm L (w b)))*
          (sampleOperator ρ (outerPerm r L)).adjoint := by
  have he : ((splitPerm r L).toMonoidHom ∘ palindromePerm (L+r)) ∘ palindromeStageEquiv r L=
      fun w => outerPerm r L w.1.1*ParallelBlocks.lift (fun b => palindromePerm L (w.1.2 b))*
        (outerPerm r L w.2)⁻¹ := funext (palindrome_stage r L)
  calc
    _ = sampleOperator ρ (((splitPerm r L).toMonoidHom ∘ palindromePerm (L+r)) ∘ palindromeStageEquiv r L) :=
      (sampleOperator_equiv ρ ((splitPerm r L).toMonoidHom ∘ palindromePerm (L+r)) (palindromeStageEquiv r L)).symm
    _ = _ := (congrArg (sampleOperator ρ) he).trans
      (sampleOperator_sandwich ρ hρ (outerPerm r L)
        (fun w : Card r → BenesCoins L => ParallelBlocks.lift (fun b => palindromePerm L (w b))))

lemma sampleOperator_modified_stage (r L : ℕ) (E : Finset (Card r))
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) (hρ : IsUnitary ρ) :
    sampleOperator (ρ.comp (splitPerm r L).toMonoidHom) (modifiedPerm L r E)=
      sampleOperator ρ (outerPerm r L)*
        sampleOperator ρ (fun w : Card r → Equiv.Perm (Card L) × BenesCoins L =>
          ParallelBlocks.lift (fun b => localModifiedPerm L (decide (b∈E)) (w b)))*
          (sampleOperator ρ (outerPerm r L)).adjoint := by
  have he : ((splitPerm r L).toMonoidHom ∘ modifiedPerm L r E) ∘ modifiedStageEquiv r L=
      fun w => outerPerm r L w.1.1*ParallelBlocks.lift
        (fun b => localModifiedPerm L (decide (b∈E)) (w.1.2 b))*(outerPerm r L w.2)⁻¹ :=
    funext (modified_stage r L E)
  calc
    _ = sampleOperator ρ (((splitPerm r L).toMonoidHom ∘ modifiedPerm L r E) ∘ modifiedStageEquiv r L) :=
      (sampleOperator_equiv ρ ((splitPerm r L).toMonoidHom ∘ modifiedPerm L r E) (modifiedStageEquiv r L)).symm
    _ = _ := (congrArg (sampleOperator ρ) he).trans
      (sampleOperator_sandwich ρ hρ (outerPerm r L)
        (fun w : Card r → Equiv.Perm (Card L) × BenesCoins L =>
          ParallelBlocks.lift (fun b => localModifiedPerm L (decide (b∈E)) (w b))))

end Thorp
namespace Thorp.CommutingBlocks
open scoped BigOperators Classical
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CompleteSpace V] in
lemma blocks_retain (P : ι → V →L[ℂ] V) (hP : ∀ i j, Commute (P i) (P j)) (E : Finset ι) :
    blocks (retain P E) (retain_commute P hP E)=coarse P hP E := by
  have hs : E∪Eᶜ=(Finset.univ : Finset ι) := Finset.union_compl E
  have hh := Finset.noncommProd_union_of_disjoint (s := E) (t := Eᶜ) disjoint_compl_right
    (retain P E) (fun _ _ _ _ _ => retain_commute P hP E _ _)
  simp only [hs] at hh
  change blocks (retain P E) (retain_commute P hP E)=_ at hh
  rw [hh]
  have he : E.noncommProd (retain P E) (fun _ _ _ _ _ => retain_commute P hP E _ _)=1 := by
    exact (Finset.noncommProd_eq_pow_card E (retain P E)
      (fun i _ j _ _ => retain_commute P hP E i j) 1 (by intro i hi; exact ite_eq_left hi)).trans (one_pow _)
  rw [he,one_mul]
  apply Finset.noncommProd_congr rfl
  intro i hi
  exact ite_eq_right (Finset.mem_compl.mp hi)

end Thorp.CommutingBlocks

namespace Thorp.ParallelBlocks
open scoped BigOperators Classical
open UnitaryFinite
variable {B X : Type*} [Fintype B] [Fintype X] [DecidableEq X]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype B] in
lemma local_central_commute {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (ρ : Representation ℂ (Equiv.Perm (B × X)) V) (P : B → Ω → Equiv.Perm X) (b c : B) :
    Commute (sampleOperator (ρ.comp (injection b)) (P b)) (centralProjection ρ c) := by
  by_cases h : b=c
  · subst c
    change _*uniformOperator _=uniformOperator _*_
    rw [sampleOperator_uniform_absorb,sampleOperator_weighted,weighted_uniform_right,sampleLaw_sum,one_smul]
  · unfold centralProjection
    rw [←sampleOperator_uniform,sampleOperator_comp,sampleOperator_comp]
    exact sampleOperator_commute ρ _ _ (fun _ _ => injection_commute h _ _)

end Thorp.ParallelBlocks
namespace Thorp
open scoped BigOperators Classical
open UnitaryFinite ParallelBlocks CommutingBlocks
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma modified_central_average (r L : ℕ) (E : Finset (Card r))
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) :
    sampleOperator ρ (fun w : Card r → Equiv.Perm (Card L) × BenesCoins L =>
      lift (fun b => localModifiedPerm L (decide (b∈E)) (w b)))=
      coarse (centralProjection ρ) (centralProjection_commute ρ) E := by
  rw [sampleOperator_parallel ρ (fun b => localModifiedPerm L (decide (b∈E))),←blocks_retain]
  apply Finset.noncommProd_congr rfl
  · intro b _
    rw [localModified_average]
    simp only [retain,centralProjection,decide_eq_true_eq]
  · intro b _ c _ _
    exact local_average_commute ρ (fun b => localModifiedPerm L (decide (b∈E))) b c

lemma central_local_gap (r L : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) (hρ : IsUnitary ρ) (b : Card r) :
    ‖sampleOperator (ρ.comp (injection b)) (palindromePerm L)*(1-centralProjection ρ b)‖≤blockGap L := by
  change ‖sampleOperator _ _*(1-uniformOperator _)‖≤_
  rw [mul_sub,mul_one,sampleOperator_uniform_absorb,sampleOperator_weighted]
  exact palindrome_off_invariants_gap L _ (unitary_comp ρ hρ _)

lemma central_blocks_exception_bound (r L : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) (hρ : IsUnitary ρ)
    (B : V →L[ℂ] V) (hB0 : ‖B‖≤1) (n : ℕ) :
    ‖B*blocks (fun b : Card r => sampleOperator (ρ.comp (injection b)) (palindromePerm L))
      (local_average_commute ρ (fun _ => palindromePerm L))*B.adjoint‖ ≤
      (blockGap L)^n + ∑ E : Finset (Card r), if E.card<n then
        ‖B*coarse (centralProjection ρ) (centralProjection_commute ρ) E*B.adjoint‖ else 0 := by
  have hB : ‖B.adjoint‖≤1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hB0
  have h := blocks_exception_bound (centralProjection ρ) (centralProjection_commute ρ)
    (fun b => uniformOperator_projection (ρ.comp (injection b)) (unitary_comp ρ hρ _))
    (fun b : Card r => sampleOperator (ρ.comp (injection b)) (palindromePerm L))
    (local_average_commute ρ (fun _ => palindromePerm L))
    (local_central_commute ρ (fun _ => palindromePerm L))
    (fun b => sampleOperator_norm_le (ρ.comp (injection b)) (unitary_comp ρ hρ _) (palindromePerm L))
    (blockGap L) (blockGap_pos L).le (blockGap_lt_one L).le (central_local_gap r L ρ hρ)
    B.adjoint hB n
  simpa only [ContinuousLinearMap.adjoint_adjoint] using h

theorem palindrome_exception_bound (r L : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card r × Card L)) V) (hρ : IsUnitary ρ) (n : ℕ) :
    ‖sampleOperator (ρ.comp (splitPerm r L).toMonoidHom) (palindromePerm (L+r))‖ ≤
      (blockGap L)^n + ∑ E : Finset (Card r), if E.card<n then
        ‖sampleOperator (ρ.comp (splitPerm r L).toMonoidHom) (modifiedPerm L r E)‖ else 0 := by
  rw [sampleOperator_palindrome_stage r L ρ hρ]
  rw [sampleOperator_parallel ρ (fun _ => palindromePerm L)]
  apply (central_blocks_exception_bound r L ρ hρ (sampleOperator ρ (outerPerm r L))
    (sampleOperator_norm_le ρ hρ _) n).trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro E _
  split_ifs
  · rw [sampleOperator_modified_stage r L E ρ hρ,modified_central_average]
  · rfl

end Thorp

namespace Thorp.UnitaryFinite
open scoped BigOperators ComplexConjugate Classical

variable {G X Ω : Type*} [Group G] [Fintype G] [Fintype X] [Fintype Ω]

omit [Fintype G] in
lemma actionKernel_apply (a : G →* Equiv.Perm X) (P : Ω → G)
    (v : EuclideanSpace ℂ X) (x : X) :
    DensityTransfer.applyKernel (actionKernel a P) v x =
      (Fintype.card Ω:ℂ)⁻¹ * ∑ ω, v (a (P ω) x) := by
  simp only [DensityTransfer.applyKernel_apply,actionKernel,finiteMean,
    Complex.ofReal_sum,div_eq_mul_inv,Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ ω, (Fintype.card Ω:ℂ)⁻¹ * ∑ y : X, if a (P ω) x=y then v y else 0 := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp_all
    _ = _ := by simp [Finset.mul_sum]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] [FiniteDimensional ℂ V] in
lemma coefficient_random (a : G →* Equiv.Perm X) (x₀ : X)
    (ha : ∀ x, ∃ g, a g x₀=x) (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (P : Ω → G) (w : V) (hw : IsFixed a x₀ ρ w) (v : V) :
    DensityTransfer.applyKernel (actionKernel a P) (normalizedCoefficient a x₀ ha ρ w v) =
      normalizedCoefficient a x₀ ha ρ w (randomOperator ρ P v) := by
  ext x
  rw [actionKernel_apply]
  simp only [normalizedCoefficient,PiLp.smul_apply,smul_eq_mul,Finset.mul_sum,
    coefficient,randomOperator,LinearMap.smul_apply,LinearMap.sum_apply,
    inner_smul_right,inner_sum]
  apply Finset.sum_congr rfl
  intro ω _
  have h := coefficient_action a x₀ ha ρ hρ w hw v (P ω) x
  change inner ℂ (ρ (representative a x₀ ha (a (P ω) x)) w) v =
    inner ℂ (ρ (representative a x₀ ha x) w) (ρ (P ω)⁻¹ v) at h
  rw [h]
  ring

theorem operator_amplification (a : G →* Equiv.Perm X) (x₀ : X)
    (ha : ∀ x, ∃ g, a g x₀=x) (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (P : Ω → G)
    (hsym : ∀ x y, actionKernel a P x y=actionKernel a P y x)
    (hrow : ∀ x, ∑ y, actionKernel a P x y=1)
    (b z M : ℝ) (hb : 0≤b) (hz : 0<z) (hM0 : 0≤M)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*actionKernel a P x y)^(1+b)) ≤ M)
    (hm : 0 < Module.finrank ℂ (fixedSpace a x₀ ρ)) (v : V) (hv : ‖v‖=1) :
    ‖randomOperator ρ P v‖ ≤ M*z^(-b)+Real.sqrt (z/(Module.finrank ℂ (fixedSpace a x₀ ρ):ℝ)) := by
  let K := fixedSpace a x₀ ρ
  let m := Module.finrank ℂ K
  let : Nonempty X := ⟨x₀⟩
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  let B := stdOrthonormalBasis ℂ K
  let w : Fin m → V := fun i => (B i : V)
  have hfix (i : Fin m) : IsFixed a x₀ ρ (w i) := (B i).2
  have hw : Orthonormal ℂ w := B.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hc := normalizedCoefficient_orthonormal a x₀ ha ρ hρ w hw hfix v hv
  have hn (i : Fin m) : ‖DensityTransfer.applyKernel (actionKernel a P)
      (normalizedCoefficient a x₀ ha ρ (w i) v)‖ = ‖randomOperator ρ P v‖ := by
    rw [coefficient_random a x₀ ha ρ hρ P (w i) (hfix i),
      normalizedCoefficient_norm a x₀ ha ρ hρ (w i) (hfix i) (hw.norm_eq_one i)]
  have h := DensityTransfer.multiplicity_amplification (actionKernel a P)
    (fun x y => finiteMean_nonneg (fun _ => by split_ifs <;> norm_num)) hsym hrow
    b z M hb hz hM0 hM _ hc (‖randomOperator ρ P v‖) (fun i => (hn i).ge)
  simpa only [Fintype.card_fin] using h

end Thorp.UnitaryFinite
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {α ι : Type*} [Fintype α] [Fintype ι]

omit [Fintype α] in
lemma tupleAction_transitive (e f : ι ↪ α) : ∃ p, tupleAction p e=f := by
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair e f e.injective f.injective
  exact ⟨p,Function.Embedding.ext hp⟩

omit [Fintype α] in
lemma tupleAction_kernel [DecidableEq α] {Ω : Type*} [Fintype Ω] (P : Ω → Equiv.Perm α)
    (e f : ι ↪ α) : actionKernel tupleAction P e f=PairRouting.tupleProbability P e f := by
  unfold actionKernel PairRouting.tupleProbability
  congr 1
  funext ω
  congr 1
  exact propext Function.Embedding.ext_iff

end Thorp.UnitaryFinite
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {G H X Ω : Type*} [Group G] [Group H] [Fintype G] [Fintype X] [Fintype Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] in
lemma sampleOperator_inv_apply (ρ : Representation ℂ G V) (P : Ω → G) (v : V) :
    sampleOperator ρ (fun ω => (P ω)⁻¹) v=randomOperator ρ P v := by
  simp only [sampleOperator,randomOperator,smul_apply,
    sum_apply,continuousRepresentation_apply,LinearMap.smul_apply,LinearMap.sum_apply]

theorem sampleOperator_amplification (a : G →* Equiv.Perm X) (x₀ : X)
    (ha : ∀ x, ∃ g, a g x₀=x) (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (P : Ω → G)
    (hsym : ∀ x y, actionKernel a P x y=actionKernel a P y x)
    (hrow : ∀ x, ∑ y, actionKernel a P x y=1)
    (b z M : ℝ) (hb : 0≤b) (hz : 0<z) (hM0 : 0≤M)
    (hM : ∀ x, finiteMean (fun y => ((Fintype.card X:ℝ)*actionKernel a P x y)^(1+b)) ≤ M)
    (hm : 0 < Module.finrank ℂ (fixedSpace a x₀ ρ)) :
    ‖sampleOperator ρ P‖ ≤ M*z^(-b)+Real.sqrt (z/(Module.finrank ℂ (fixedSpace a x₀ ρ):ℝ)) := by
  rw [←ContinuousLinearMap.adjoint.norm_map (sampleOperator ρ P),←sampleOperator_inv ρ hρ]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  rw [sampleOperator_inv_apply]
  exact operator_amplification a x₀ ha ρ hρ P hsym hrow b z M hb hz hM0 hM hm v hv

end Thorp.UnitaryFinite


end ThorpNine.Adaptive

end OAI
end

section
-- module Solutions.OAIQ077_TR.ThorpRouting_Adaptive_InsertionPerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.DimensionEstimates
open scoped BigOperators Classical

lemma amplification_numerical (m u : ℝ) (hm : 1 ≤ m) (hu : u ≤ Real.log m/4000) :
    Real.exp u*(Real.exp (Real.log m/2))^(-(1/1000:ℝ))+
      Real.sqrt (Real.exp (Real.log m/2)/m) ≤ 2*Real.exp (-Real.log m/4000) := by
  have hmp : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hl : 0≤Real.log m := Real.log_nonneg hm
  have he : Real.exp (Real.log m/2)/m=Real.exp (-Real.log m/2) := by
    calc
      _ = Real.exp (Real.log m/2)/Real.exp (Real.log m) := by rw [Real.exp_log hmp]
      _ = _ := by rw [←Real.exp_sub]; congr 1; ring
  have hs : Real.sqrt (Real.exp (-Real.log m/2))=Real.exp (-Real.log m/4) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    congr 1
    ring
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,←Real.exp_add,he,hs]
  have h₁ : u+(Real.log m/2)*(-(1/1000:ℝ))≤ -Real.log m/4000 := by linarith
  have h₂ : -Real.log m/4≤ -Real.log m/4000 := by linarith
  linarith [Real.exp_le_exp.mpr h₁,Real.exp_le_exp.mpr h₂]

lemma amplification_absorb (x : ℝ) (hx : 8000*Real.log 2≤x) :
    2*Real.exp (-x/4000)≤Real.exp (-x/8000) := by
  rw [show (2:ℝ)=Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)],←Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

lemma amplification_decay (m u : ℝ) (hm : 1 ≤ m) (hu : u ≤ Real.log m/4000)
    (hl : 8000*Real.log 2≤Real.log m) :
    Real.exp u*(Real.exp (Real.log m/2))^(-(1/1000:ℝ))+
      Real.sqrt (Real.exp (Real.log m/2)/m) ≤ Real.exp (-Real.log m/8000) :=
  (amplification_numerical m u hm hu).trans (amplification_absorb _ hl)

end Thorp.DimensionEstimates

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
lemma full_tuple_fixed (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V) :
    fixedSpace tupleAction (Function.Embedding.refl (Card d)) ρ=⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro v g hg
  have he : g=1 := by
    apply Equiv.ext
    intro x
    exact congrArg (fun f : Card d ↪ Card d => f x) hg
  rw [he,map_one]
  rfl

omit [FiniteDimensional ℂ V] in
lemma full_tuple_finrank (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V) :
    Module.finrank ℂ (fixedSpace tupleAction (Function.Embedding.refl (Card d)) ρ)=Module.finrank ℂ V := by
  rw [full_tuple_fixed,finrank_top]

theorem modified_irrep_amplification (L r : ℕ) (E : Finset (Card r))
    (ρ : Representation ℂ (Equiv.Perm (Card (L+r))) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ V)
    (u z : ℝ) (hz : 0<z)
    (hM : ∀ e : Card (L+r) ↪ Card (L+r), modifiedRowMoment L r E e (1/1000)≤Real.exp u) :
    ‖sampleOperator ρ (modifiedPerm L r E)‖ ≤
      Real.exp u*z^(-(1/1000:ℝ))+Real.sqrt (z/(Module.finrank ℂ V:ℝ)) := by
  let f := Function.Embedding.refl (Card (L+r))
  have h := sampleOperator_amplification tupleAction f (tupleAction_transitive f) ρ hρ
    (modifiedPerm L r E) (fun e f => by simpa only [tupleAction_kernel] using modified_kernel_symmetric L r E e f)
    (fun e => by simpa only [tupleAction_kernel] using PairRouting.tupleProbability_row_sum (modifiedPerm L r E) e)
    (1/1000) z (Real.exp u) (by norm_num) hz (by positivity)
    (fun e => by simpa only [tupleAction_kernel,modifiedRowMoment] using hM e)
    (by simpa only [f,full_tuple_finrank] using hm)
  simpa only [f,full_tuple_finrank] using h

end Thorp.UnitaryFinite

namespace Thorp.DimensionEstimates

section
open scoped BigOperators Classical
open Filter

lemma finset_power_sum {ι : Type*} [Fintype ι] (x : ℝ) :
    ∑ E : Finset ι, x^E.card=(1+x)^Fintype.card ι := by
  have h := Finset.prod_one_add (f := fun _ : ι => x) Finset.univ
  simpa only [Finset.prod_const,Finset.card_univ,Finset.powerset_univ] using h.symm

lemma small_sets_count {ι : Type*} [Fintype ι] (ε t : ℝ) (ht : 0≤t) :
    (∑ E : Finset ι, if (E.card:ℝ)<ε*Fintype.card ι then (1:ℝ) else 0) ≤
      Real.exp ((t*ε+Real.log (1+Real.exp (-t)))*Fintype.card ι) := by
  have hpow (E : Finset ι) : (Real.exp (-t))^E.card=Real.exp (-t*(E.card:ℝ)) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ ≤ ∑ E : Finset ι, Real.exp (t*ε*Fintype.card ι)*(Real.exp (-t))^E.card := by
      apply Finset.sum_le_sum
      intro E _
      split_ifs with hE
      · rw [hpow,←Real.exp_add,←Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hE.le ht]
      · positivity
    _ = Real.exp (t*ε*Fintype.card ι)*(1+Real.exp (-t))^Fintype.card ι := by
      rw [←Finset.mul_sum,finset_power_sum]
    _ = _ := by
      have he : (1+Real.exp (-t))^Fintype.card ι=
          Real.exp (Real.log (1+Real.exp (-t))*(Fintype.card ι:ℝ)) := by
        rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by positivity)]
      rw [he,←Real.exp_add]
      congr 1
      ring

lemma small_sets_ceil_bound {ι : Type*} [Fintype ι] (ε t : ℝ) (ht : 0≤t) :
    (∑ E : Finset ι, if E.card<⌈ε*Fintype.card ι⌉₊ then (1:ℝ) else 0) ≤
      Real.exp ((t*ε+Real.log (1+Real.exp (-t)))*Fintype.card ι) := by
  have he (E : Finset ι) : E.card<⌈ε*Fintype.card ι⌉₊ ↔ (E.card:ℝ)<ε*Fintype.card ι := Nat.lt_ceil
  simp only [he]
  exact small_sets_count ε t ht

end
open Filter

end Thorp.DimensionEstimates

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical
open DimensionEstimates
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem full_modified_decay (L r : ℕ) (E : Finset (Card r))
    (ρ : Representation ℂ (Equiv.Perm (Card (L+r))) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ V) (u : ℝ)
    (hM : ∀ e : Card (L+r) ↪ Card (L+r), modifiedRowMoment L r E e (1/1000)≤Real.exp u)
    (hden : u≤Real.log (Module.finrank ℂ V)/4000)
    (hl : 8000*Real.log 2≤Real.log (Module.finrank ℂ V)) :
    ‖sampleOperator ρ (modifiedPerm L r E)‖≤Real.exp (-Real.log (Module.finrank ℂ V)/8000) := by
  exact (modified_irrep_amplification L r E ρ hρ hm u
    (Real.exp (Real.log (Module.finrank ℂ V)/2)) (Real.exp_pos _) hM).trans
    (amplification_decay _ _ (by exact_mod_cast hm) hden hl)

lemma palindrome_exception_cards (r L : ℕ)
    (ρ : Representation ℂ (Equiv.Perm (Card (L+r))) V) (hρ : IsUnitary ρ) (n : ℕ) :
    ‖sampleOperator ρ (palindromePerm (L+r))‖ ≤
      (blockGap L)^n+∑ E : Finset (Card r), if E.card<n then
        ‖sampleOperator ρ (modifiedPerm L r E)‖ else 0 := by
  let σ := ρ.comp (splitPerm r L).symm.toMonoidHom
  have he : σ.comp (splitPerm r L).toMonoidHom=ρ := by
    ext g v
    change ρ ((splitPerm r L).symm ((splitPerm r L) g)) v=ρ g v
    rw [MulEquiv.symm_apply_apply]
  have h := palindrome_exception_bound r L σ (unitary_comp ρ hρ _) n
  simpa only [he] using h

end Thorp.UnitaryFinite

namespace Thorp.DimensionEstimates
open scoped BigOperators Classical
open Filter

lemma geometric_ceil_bound (θ ε : ℝ) (hθ : 0<θ) (hθ1 : θ<1) (M : ℕ) :
    θ^⌈ε*M⌉₊≤Real.exp (Real.log θ*ε*M) := by
  conv_lhs => rw [←Real.exp_log hθ,←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hg := mul_le_mul_of_nonpos_left (Nat.le_ceil (ε*M)) (Real.log_nonpos hθ.le hθ1.le)
  nlinarith

end Thorp.DimensionEstimates

namespace Thorp.UnitaryFinite
open scoped BigOperators Classical
open DimensionEstimates
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem medium_exception_decay_q77_oai (L r : ℕ) (h ε t : ℝ) (ht : 0≤t)
    (hcount : t*ε+Real.log (1+Real.exp (-t))≤h*(2:ℝ)^L/16000)
    (ρ : Representation ℂ (Equiv.Perm (Card (L+r))) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (hm : 0<Module.finrank ℂ V)
    (hd : h*(2:ℝ)^(L+r)≤Real.log (Module.finrank ℂ V))
    (hl : 8000*Real.log 2≤Real.log (Module.finrank ℂ V))
    (hM : ∀ (E : Finset (Card r)), (E.card:ℝ)<ε*(2:ℝ)^r →
      ∀ e : Card (L+r) ↪ Card (L+r),
        modifiedRowMoment L r E e (1/1000)≤Real.exp ((h/4000)*(2:ℝ)^(L+r))) :
    ‖sampleOperator ρ (palindromePerm (L+r))‖≤
      Real.exp (Real.log (blockGap L)*ε*(2:ℝ)^r)+Real.exp (-h*(2:ℝ)^(L+r)/16000) := by
  have hmE (E : Finset (Card r)) (hE : E.card<⌈ε*(2:ℝ)^r⌉₊) :
      ‖sampleOperator ρ (modifiedPerm L r E)‖≤Real.exp (-h*(2:ℝ)^(L+r)/8000) := by
    apply (full_modified_decay L r E ρ hρ hm ((h/4000)*(2:ℝ)^(L+r))
      (hM E (Nat.lt_ceil.mp hE)) (by linarith) hl).trans
    apply Real.exp_le_exp.mpr
    linarith
  have hs : (∑ E : Finset (Card r), if E.card<⌈ε*(2:ℝ)^r⌉₊ then
      ‖sampleOperator ρ (modifiedPerm L r E)‖ else 0) ≤
      Real.exp (-h*(2:ℝ)^(L+r)/16000) := by
    calc
      _ ≤ (∑ E : Finset (Card r), if E.card<⌈ε*(2:ℝ)^r⌉₊ then (1:ℝ) else 0)*
          Real.exp (-h*(2:ℝ)^(L+r)/8000) := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro E _
        split_ifs with hE
        · simpa only [one_mul] using hmE E hE
        · simp
      _ ≤ Real.exp ((t*ε+Real.log (1+Real.exp (-t)))*(2:ℝ)^r)*
          Real.exp (-h*(2:ℝ)^(L+r)/8000) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        simpa only [card_positions,Nat.cast_pow,Nat.cast_ofNat] using
          small_sets_ceil_bound (ι := Card r) ε t ht
      _ ≤ _ := by
        rw [←Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right hcount (by positivity : (0:ℝ)≤(2:ℝ)^r)
        rw [pow_add]
        nlinarith
  apply (palindrome_exception_cards r L ρ hρ ⌈ε*(2:ℝ)^r⌉₊).trans
  apply add_le_add _ hs
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using
    geometric_ceil_bound (blockGap L) ε (blockGap_pos L) (blockGap_lt_one L) (2^r)

end Thorp.UnitaryFinite

end ThorpNine.Adaptive

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ThorpNine.Adaptive.Thorp.UnitaryFinite.medium_exception_decay_q77_oai.{u_1} := @OAI.ThorpNine.Adaptive.Thorp.UnitaryFinite.medium_exception_decay_q77_oai.{u_1}
