-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.claim_5_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T16:13:15.170262+00:00
-- url     : https://prove2.me/submissions/71322705-accb-4d62-87fa-528527b6ca80

import Definitions.Def_ITPIRPreproc_MatchVec_ActivationPrimitive
import Mathlib.GroupTheory.Index
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal
open Matrix Finset ITPIRPreproc.MatchVec

namespace PIRCount
section General
variable {A B : Type*} [AddCommGroup A] [Fintype A] [AddCommGroup B] [Fintype B] [DecidableEq A] [DecidableEq B]

noncomputable def fiber (f : A →+ B) (b : B) : Finset A := by
  classical
  exact univ.filter (fun a => f a = b)

lemma fiber_card (f : A →+ B) (hf : Function.Surjective f) (b : B) :
    (fiber f b).card * Fintype.card B = Fintype.card A := by
  classical
  have he : ∀ c : B, (fiber f c).card = (fiber f b).card := fun c =>
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf c) (hf b)
  have hc := Finset.card_eq_sum_card_fiberwise (f := f) (s := univ) (t := univ)
    (fun a _ => mem_univ (f a))
  change Fintype.card A = ∑ c : B, (fiber f c).card at hc
  rw [show (∑ c : B, (fiber f c).card) = Fintype.card B * (fiber f b).card by simp [he]] at hc
  simpa [Nat.mul_comm] using hc.symm

lemma fiber_pos (f : A →+ B) (hf : Function.Surjective f) (b : B) :
    0 < (fiber f b).card := by
  classical
  obtain ⟨a, ha⟩ := hf b
  exact card_pos.mpr ⟨a, by simp [fiber, ha]⟩

lemma inv_mul_nat (n m : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
    ((n * m : ℕ) : ℝ≥0∞)⁻¹ * n = (m : ℝ≥0∞)⁻¹ := by
  have hn' : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn
  rw [Nat.cast_mul, ENNReal.mul_inv (Or.inl hn') (Or.inl (ENNReal.natCast_ne_top _))]
  rw [mul_right_comm, ENNReal.inv_mul_cancel hn' (ENNReal.natCast_ne_top _), one_mul]

lemma fiber_uniform (f : A →+ B) (hf : Function.Surjective f) (b : B) :
    (Fintype.card A : ℝ≥0∞)⁻¹ * (fiber f b).card = (Fintype.card B : ℝ≥0∞)⁻¹ := by
  rw [← fiber_card f hf b]
  exact inv_mul_nat _ _ (fiber_pos f hf b).ne' Fintype.card_ne_zero

lemma conditional_uniform (f g : A →+ B)
    (hfg : Function.Surjective (fun x => (f x, g x))) (b c : B) :
    avgOver (fiber f b) (fun x => if g x = c then 1 else 0) =
      (Fintype.card B : ℝ≥0∞)⁻¹ := by
  classical
  have hf : Function.Surjective f := fun b => by
    obtain ⟨a, ha⟩ := hfg (b,0); exact ⟨a, congrArg Prod.fst ha⟩
  let fg : A →+ B × B := f.prod g
  have hfg' : Function.Surjective fg := hfg
  have hc := fiber_card fg hfg' (b,c)
  have hfcard := fiber_card f hf b
  have hrel : (fiber fg (b,c)).card * Fintype.card B = (fiber f b).card := by
    apply Nat.mul_right_cancel (Fintype.card_pos (α := B))
    rw [mul_assoc, ← Fintype.card_prod (α := B) (β := B), hc, hfcard]
  have he : (fiber f b).filter (fun x => g x = c) = fiber fg (b,c) := by
    ext x
    simp [fiber, fg, Prod.ext_iff]
  have hs : (∑ x ∈ fiber f b, if g x = c then (1 : ℝ≥0∞) else 0) =
      (((fiber f b).filter (fun x => g x = c)).card : ℝ≥0∞) := by
    rw [card_filter, Nat.cast_sum]
    apply sum_congr rfl
    intro x hx
    split_ifs <;> simp
  rw [avgOver, hs, he, ← hrel]
  exact inv_mul_nat _ _ (fiber_pos fg hfg' (b,c)).ne' Fintype.card_ne_zero

lemma sampler_uniform (f : A →+ B) (g : B →+ A)
    (hfg : ∀ b, f (g b) = b) (b : B) (x : A) :
    (Fintype.card A : ℝ≥0∞)⁻¹ *
      ((univ.filter (fun y : A => y + g (b - f y) = x)).card : ℝ≥0∞) =
        if f x = b then ((fiber f b).card : ℝ≥0∞)⁻¹ else 0 := by
  classical
  have hf : Function.Surjective f := fun c => ⟨g c, hfg c⟩
  by_cases hx : f x = b
  · rw [if_pos hx]
    have he : (univ.filter (fun y : A => y + g (b - f y) = x)).card = Fintype.card B := by
      let e' : {y : A // y + g (b - f y) = x} ≃ B :=
        { toFun := fun y => f y.1 - b
          invFun := fun c => ⟨x + g c, by simp [map_add, hfg, hx]⟩
          left_inv := fun y => by
            apply Subtype.ext
            have hy := y.2
            dsimp
            calc
              x + g (f y.1 - b) = (y.1 + g (b - f y.1)) + g (f y.1 - b) :=
                congrArg (fun t => t + g (f y.1 - b)) hy.symm
              _ = y.1 := by simp only [map_sub]; abel
          right_inv := fun c => by simp [hfg, hx] }
      simpa only [Fintype.card_subtype] using Fintype.card_congr e'
    rw [he, ← fiber_card f hf b, Nat.mul_comm]
    exact inv_mul_nat _ _ Fintype.card_ne_zero (fiber_pos f hf b).ne'
  · rw [if_neg hx]
    have he : (univ.filter (fun y : A => y + g (b - f y) = x)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hy' := (mem_filter.mp hy).2
      apply hx
      rw [← hy']
      simp [hfg]
    rw [he]
    simp
end General

lemma binary (c : ZMod 2) : c = 0 ∨ c = 1 := by
  have he : (univ : Finset (ZMod 2)) = {0,1} := by decide
  have hm := mem_univ c
  rw [he] at hm
  simpa only [mem_insert, mem_singleton] using hm

lemma dual_pair {d : ℕ} (x y u : Fin d → ZMod 2)
    (hu : u ⬝ᵥ x = 1) (hy : y ≠ 0) (hne : y ≠ x) :
    ∃ p q : Fin d → ZMod 2,
      p ⬝ᵥ x = 1 ∧ p ⬝ᵥ y = 0 ∧ q ⬝ᵥ x = 0 ∧ q ⬝ᵥ y = 1 := by
  classical
  have hnot : y ≠ (u ⬝ᵥ y) • x := by
    rcases binary (u ⬝ᵥ y) with hz | ho
    · simpa [hz] using hy
    · simpa [ho] using hne
  obtain ⟨k, hk⟩ : ∃ k, y k - x k * (u ⬝ᵥ y) ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hnot
    ext k
    have := sub_eq_zero.mp (hn k)
    simpa [smul_eq_mul, mul_comm] using this
  have hk1 : y k - x k * (u ⬝ᵥ y) = 1 := (binary _).resolve_left hk
  let q : Fin d → ZMod 2 := Pi.single k 1 - x k • u
  have hqx : q ⬝ᵥ x = 0 := by
    simp [q, sub_dotProduct, smul_dotProduct, hu, smul_eq_mul]
  have hqy : q ⬝ᵥ y = 1 := by
    simpa [q, sub_dotProduct, smul_dotProduct, smul_eq_mul] using hk1
  refine ⟨u - (u ⬝ᵥ y) • q, q, ?_, ?_, hqx, hqy⟩
  · simp [sub_dotProduct, smul_dotProduct, hu, hqx]
  · simp [sub_dotProduct, smul_dotProduct, hqy]
end PIRCount

namespace PIRCount
variable {h d : ℕ} {u v : Fin (2^h) → Fin d → ZMod 6}
lemma diag (hmv : IsMVFamily (2^h) d u v) (a : Fin (2^h)) :
    vec2 (u a) ⬝ᵥ vec2 (v a) = 1 := by
  change (fun k => red2 (u a k)) ⬝ᵥ (fun k => red2 (v a k)) = 1
  calc
    _ = red2 (u a ⬝ᵥ v a) := (red2.map_dotProduct (u a) (v a)).symm
    _ = 1 := by rw [hmv.diag, map_one]
lemma mv_dual (hmv : IsMVFamily (2^h) d u v) {a b : Fin (2^h)} (hab : a ≠ b) :
    ∃ p q : Fin d → ZMod 2,
      p ⬝ᵥ vec2 (v a) = 1 ∧ p ⬝ᵥ vec2 (v b) = 0 ∧
      q ⬝ᵥ vec2 (v a) = 0 ∧ q ⬝ᵥ vec2 (v b) = 1 := by
  apply dual_pair _ _ (vec2 (u a)) (diag hmv a)
  · intro hz
    have hd := diag hmv b
    rw [hz, dotProduct_zero] at hd
    exact zero_ne_one hd
  · intro he
    exact hab (hmv.distinct_mod2 he.symm)

def basicEval (x : Fin d → ZMod 2) : BasicKey h d →+ (Fin h → ZMod 2) where
  toFun R := R *ᵥ x
  map_zero' := by ext j; simp [mulVec]
  map_add' R S := add_mulVec R S x
def basicSection (u : Fin d → ZMod 2) : (Fin h → ZMod 2) →+ BasicKey h d where
  toFun b := vecMulVec b u
  map_zero' := by ext j k; simp [vecMulVec]
  map_add' b c := by ext j k; simp [vecMulVec, add_mul]
lemma basic_section (x u : Fin d → ZMod 2) (hu : u ⬝ᵥ x = 1) (b : Fin h → ZMod 2) :
    basicEval x (basicSection u b) = b := by
  change vecMulVec b u *ᵥ x = b
  simp [vecMulVec_mulVec, hu]
lemma basic_surj (hmv : IsMVFamily (2^h) d u v) (a : Fin (2^h)) :
    Function.Surjective (basicEval (h := h) (vec2 (v a))) :=
  fun b => ⟨basicSection (vec2 (u a)) b, basic_section _ _ (diag hmv a) b⟩
lemma basic_pair_surj (hmv : IsMVFamily (2^h) d u v) {a b : Fin (2^h)} (hab : a ≠ b) :
    Function.Surjective (fun R : BasicKey h d =>
      (basicEval (vec2 (v a)) R, basicEval (vec2 (v b)) R)) := by
  obtain ⟨p,q,hpx,hpy,hqx,hqy⟩ := mv_dual hmv hab
  intro bc
  refine ⟨vecMulVec bc.1 p + vecMulVec bc.2 q, ?_⟩
  apply Prod.ext <;> simp [basicEval, add_mulVec, vecMulVec_mulVec, hpx,hpy,hqx,hqy]

def actEval (x : Fin d → ZMod 2) : ActKey h d →+ (ZMod 2 × (Fin h → ZMod 2)) where
  toFun K := (K.2 ⬝ᵥ x, K.1 *ᵥ x)
  map_zero' := by apply Prod.ext <;> simp [mulVec]
  map_add' K L := by apply Prod.ext <;> simp [add_dotProduct, add_mulVec]
def actSection (u : Fin d → ZMod 2) : (ZMod 2 × (Fin h → ZMod 2)) →+ ActKey h d where
  toFun c := (vecMulVec c.2 u, c.1 • u)
  map_zero' := by apply Prod.ext <;> ext k <;> simp [vecMulVec]
  map_add' b c := by apply Prod.ext <;> ext k <;> simp [vecMulVec, add_mul, add_smul]
lemma act_section (x u : Fin d → ZMod 2) (hu : u ⬝ᵥ x = 1)
    (b : ZMod 2 × (Fin h → ZMod 2)) : actEval x (actSection u b) = b := by
  apply Prod.ext <;> simp [actEval,actSection,smul_dotProduct,vecMulVec_mulVec,hu]
lemma act_surj (hmv : IsMVFamily (2^h) d u v) (a : Fin (2^h)) :
    Function.Surjective (actEval (h := h) (vec2 (v a))) :=
  fun b => ⟨actSection (vec2 (u a)) b, act_section _ _ (diag hmv a) b⟩
lemma act_pair_surj (hmv : IsMVFamily (2^h) d u v) {a b : Fin (2^h)} (hab : a ≠ b) :
    Function.Surjective (fun K : ActKey h d =>
      (actEval (vec2 (v a)) K, actEval (vec2 (v b)) K)) := by
  obtain ⟨p,q,hpx,hpy,hqx,hqy⟩ := mv_dual hmv hab
  intro bc
  refine ⟨(vecMulVec bc.1.2 p + vecMulVec bc.2.2 q, bc.1.1 • p + bc.2.1 • q), ?_⟩
  apply Prod.ext <;> apply Prod.ext <;>
    simp [actEval, add_mulVec, vecMulVec_mulVec, add_dotProduct, smul_dotProduct,
      hpx,hpy,hqx,hqy]
lemma basic_fiber (i : Pos h) : basicCompat v i = fiber (basicEval (vec2 (v i.1))) i.2 := rfl
lemma act_fiber (i : Pos h) : actCompat v i = fiber (actEval (vec2 (v i.1))) (1,i.2) := by
  ext K
  simp [actCompat, actSel, fiber, actEval, Prod.ext_iff, and_comm]
lemma act_eval_sel (i : Pos h) (K : ActKey h d) :
    actEval (vec2 (v i.1)) K = (1,i.2) ↔ actSel v K i := by
  simp [actEval,actSel,Prod.ext_iff,and_comm]
end PIRCount

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal
open Matrix Finset ITPIRPreproc.MatchVec PIRCount

theorem solution (h d : ℕ) (u v : Fin (2 ^ h) → Fin d → ZMod 6) (hh : 3 ≤ h)
    (hmv : IsMVFamily (2 ^ h) d u v) :
    (∀ i j : Pos h, i ≠ j →
      (Fintype.card (BasicKey h d) : ℝ≥0∞)⁻¹ * (basicCompat v i).card = (2 ^ h : ℝ≥0∞)⁻¹ ∧
      avgOver (basicCompat v i) (fun R => if basicSel v R j then 1 else 0) ≤
        (2 ^ h : ℝ≥0∞)⁻¹) ∧
    ∀ (i : Pos h) (R : BasicKey h d),
      (Fintype.card (BasicKey h d) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun R₀ => basicSampler u v i R₀ = R).card =
        if basicSel v R i then ((basicCompat v i).card : ℝ≥0∞)⁻¹ else 0 := by
  classical
  constructor
  · intro i j hij
    constructor
    · rw [basic_fiber, fiber_uniform _ (basic_surj hmv i.1)]
      simp [Fintype.card_fun, ZMod.card]
    · by_cases ha : i.1 = j.1
      · have hz : avgOver (basicCompat v i) (fun R => if basicSel v R j then 1 else 0) = 0 := by
          unfold avgOver
          suffices (∑ R ∈ basicCompat v i, if basicSel v R j then (1:ℝ≥0∞) else 0) = 0 by rw [this,mul_zero]
          apply sum_eq_zero
          intro R hR
          rw [if_neg]
          intro hj
          have hi : basicSel v R i := (mem_filter.mp hR).2
          apply hij
          apply Prod.ext ha
          exact hi.symm.trans (ha.symm ▸ hj)
        rw [hz]
        exact zero_le
      · apply le_of_eq
        rw [basic_fiber]
        simpa only [basicSel, basicEval, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, Nat.cast_ofNat] using
          conditional_uniform (basicEval (vec2 (v i.1))) (basicEval (vec2 (v j.1)))
            (basic_pair_surj hmv ha) i.2 j.2
  · intro i R
    have hs := sampler_uniform (basicEval (h := h) (vec2 (v i.1)))
      (basicSection (vec2 (u i.1))) (basic_section _ _ (diag hmv i.1)) i.2 R
    simpa only [basicSampler,basicSel,basic_fiber,basicEval,basicSection,
      AddMonoidHom.coe_mk,ZeroHom.coe_mk] using hs
