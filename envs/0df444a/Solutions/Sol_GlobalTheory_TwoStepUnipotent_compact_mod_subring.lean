-- Prove2me | solution 1 for GlobalTheory.TwoStepUnipotent.compact_mod_subring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:28:08.903242+00:00
-- url     : https://prove2.me/submissions/ccb4c23e-82ff-4b22-a3c2-ddbe30066851

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_TwoStepUnipotentCompactModSubring
import Theorems.Thm_GlobalTheory_TwoStepUnipotent_st_half
import Theorems.Thm_GlobalTheory_TwoStepUnipotent_elt_mul
import Theorems.Thm_GlobalTheory_TwoStepUnipotent_elt_neg_mul
import Theorems.Thm_GlobalTheory_TwoStepUnipotent_elt_mul_neg
import Theorems.Thm_GlobalTheory_TwoStepUnipotent_elt_cond
import Theorems.Thm_GlobalTheory_TwoStepUnipotent_exists_elt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory GlobalTheory.TwoStepUnipotent
namespace GlobalTheory.TwoStepUnipotent
theorem _root_.solution (S : Type) [Ring S] [TopologicalSpace S] [IsTopologicalRing S]
    (st : S →+ S) (S₀ : Subring S) (e₁ e₃ h : S) (K : Set S) (hcont : Continuous st)
    (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (h0 : ∀ x ∈ S₀, st x ∈ S₀) (he : e₁ ∈ S₀) (hh0 : h ∈ S₀) (h11 : e₁ * e₁ = e₁)
    (hs : st e₁ = e₃) (h13 : e₁ * e₃ = 0) (h31 : e₃ * e₁ = 0) (hh : h + h = 1)
    (hc : ∀ x, h * x = x * h) (hK : IsCompact K) (hcov : ∀ x, ∃ y ∈ S₀, x - y ∈ K) :
    ∃ K' : Set Sˣ, IsCompact K' ∧ (∀ g ∈ K', (st (g : S) * (g : S) = 1 ∧ ((g : S) - 1) * e₁ = 0 ∧
      (1 - e₁) * ((g : S) - 1) * (1 - e₃) = 0)) ∧ ∀ g : Sˣ, (st (g : S) * (g : S) = 1 ∧
      ((g : S) - 1) * e₁ = 0 ∧ (1 - e₁) * ((g : S) - 1) * (1 - e₃) = 0) →
      ∃ γ : Sˣ, (st (γ : S) * (γ : S) = 1 ∧ ((γ : S) - 1) * e₁ = 0 ∧
      (1 - e₁) * ((γ : S) - 1) * (1 - e₃) = 0) ∧ (γ : S) ∈ S₀ ∧ ((γ⁻¹ : Sˣ) : S) ∈ S₀ ∧
      γ * g ∈ K' := by
  have he3 : st e₃ = e₁ := by rw [← hs, hi]
  have he33 : e₃ * e₃ = e₃ := by rw [← hs, ← hm, h11]
  have he3S : e₃ ∈ S₀ := hs ▸ h0 e₁ he
  obtain ⟨pb, hpb⟩ : ∃ f : S → S, ∀ x, f x = (1 - e₁ - e₃) * x * e₃ := ⟨_, fun _ => rfl⟩
  obtain ⟨pw, hpw⟩ : ∃ f : S → S, ∀ x, f x = e₁ * (h * (x - st x)) * e₃ := ⟨_, fun _ => rfl⟩
  have pb_sub : ∀ x y, pb (x - y) = pb x - pb y := fun x y => by
    simp only [hpb, mul_sub, sub_mul]
  have pw_sub : ∀ x y, pw (x - y) = pw x - pw y := fun x y => by
    simp only [hpw, map_sub, mul_sub, sub_mul]
    abel
  have hbx : ∀ x, e₁ * pb x = 0 ∧ e₃ * pb x = 0 ∧ pb x * e₃ = pb x := fun x => by
    refine ⟨?_, ?_, ?_⟩
    · simp only [hpb, ← mul_assoc, mul_sub, mul_one, h11, h13, sub_self, zero_mul]
    · simp only [hpb, ← mul_assoc, mul_sub, mul_one, h31, he33, sub_self, sub_zero, zero_mul]
    · simp only [hpb, mul_assoc, he33]
  have hwx : ∀ y, e₁ * pw y = pw y ∧ pw y * e₃ = pw y ∧ st (pw y) = -pw y := fun y => by
    refine ⟨?_, ?_, ?_⟩
    · simp only [hpw, ← mul_assoc, h11]
    · simp only [hpw, mul_assoc, he33]
    · simp only [hpw, hm, he3, hs, map_sub, hi, st_half hm hi hh hc]
      rw [← hc (st y - y)]
      noncomm_ring
  have pb_id : ∀ b, e₁ * b = 0 → e₃ * b = 0 → b * e₃ = b → pb b = b := fun b h1 h3 h3' => by
    simp only [hpb, sub_mul, one_mul, h1, h3, sub_zero, h3']
  have pw_id : ∀ w, e₁ * w = w → w * e₃ = w → st w = -w → pw w = w := fun w h1 h3 hs' => by
    rw [hpw, hs', sub_neg_eq_add, mul_add, ← add_mul, hh, one_mul, h1, h3]
  have pbS : ∀ x ∈ S₀, pb x ∈ S₀ := fun x hx => by
    rw [hpb]
    exact S₀.mul_mem (S₀.mul_mem (S₀.sub_mem (S₀.sub_mem S₀.one_mem he) he3S) hx) he3S
  have pwS : ∀ x ∈ S₀, pw x ∈ S₀ := fun x hx => by
    rw [hpw]
    exact S₀.mul_mem (S₀.mul_mem he (S₀.mul_mem hh0 (S₀.sub_mem hx (h0 x hx)))) he3S
  have pb_cont : Continuous pb := by
    rw [show pb = fun x => (1 - e₁ - e₃) * x * e₃ from funext hpb]
    exact (continuous_const.mul continuous_id).mul continuous_const
  have pw_cont : Continuous pw := by
    rw [show pw = fun x => e₁ * (h * (x - st x)) * e₃ from funext hpw]
    exact (continuous_const.mul (continuous_const.mul (continuous_id.sub hcont))).mul continuous_const
  have hE : ∀ {f g : S × S → S}, Continuous f → Continuous g →
      Continuous (fun p => elt st h (f p) (g p)) := by
    intro f g hf hg
    show Continuous (fun p => 1 - st (f p) + f p + (g p - h * (st (f p) * f p)))
    exact ((continuous_const.sub (hcont.comp hf)).add hf).add
      (hg.sub (continuous_const.mul ((hcont.comp hf).mul hf)))
  have eltS : ∀ x y, x ∈ S₀ → y ∈ S₀ → elt st h x y ∈ S₀ := fun x y hx hy =>
    S₀.add_mem (S₀.add_mem (S₀.sub_mem S₀.one_mem (h0 x hx)) hx)
      (S₀.sub_mem hy (S₀.mul_mem hh0 (S₀.mul_mem (h0 x hx) hx)))
  have hbneg : ∀ b, (e₁ * b = 0 ∧ e₃ * b = 0 ∧ b * e₃ = b) → (e₁ * -b = 0 ∧ e₃ * -b = 0 ∧ -b * e₃ = -b) :=
    fun b ⟨a1, a2, a3⟩ => ⟨by rw [mul_neg, a1, neg_zero], by rw [mul_neg, a2, neg_zero], by rw [neg_mul, a3]⟩
  have hwneg : ∀ w, (e₁ * w = w ∧ w * e₃ = w ∧ st w = -w) →
      (e₁ * -w = -w ∧ -w * e₃ = -w ∧ st (-w) = -(-w)) :=
    fun w ⟨a1, a2, a3⟩ => ⟨by rw [mul_neg, a1], by rw [neg_mul, a2], by rw [map_neg, a3]⟩
  have hQ : ∀ x y, (e₁ * x = 0 ∧ e₃ * x = 0 ∧ x * e₃ = x) → (e₁ * y = 0 ∧ e₃ * y = 0 ∧ y * e₃ = y) →
      e₁ * (st x * y - st y * x) = st x * y - st y * x ∧ (st x * y - st y * x) * e₃ = st x * y - st y * x ∧
        st (st x * y - st y * x) = -(st x * y - st y * x) := by
    intro x y hx hy
    have sx1 : e₁ * st x = st x := by rw [← he3, ← hm, hx.2.2]
    have sy1 : e₁ * st y = st y := by rw [← he3, ← hm, hy.2.2]
    refine ⟨?_, ?_, ?_⟩
    · rw [mul_sub, ← mul_assoc, ← mul_assoc, sx1, sy1]
    · rw [sub_mul, mul_assoc, mul_assoc, hy.2.2, hx.2.2]
    · rw [map_sub, hm, hm, hi, hi, neg_sub]
  obtain ⟨F, hF⟩ : ∃ F : S × S → Sˣ, ∀ p, (F p : S) = elt st h (pb p.1) (pw p.2) ∧
      (((F p)⁻¹ : Sˣ) : S) = elt st h (-pb p.1) (-pw p.2) :=
    ⟨fun p => ⟨elt st h (pb p.1) (pw p.2), elt st h (-pb p.1) (-pw p.2),
      elt_mul_neg hm hi hs h31 hh hc ⟨(hbx p.1).2.1, (hbx p.1).2.2⟩ ⟨(hwx p.2).1, (hwx p.2).2.1⟩,
      elt_neg_mul hm hi hs h31 hh hc ⟨(hbx p.1).2.1, (hbx p.1).2.2⟩ ⟨(hwx p.2).1, (hwx p.2).2.1⟩⟩,
      fun p => ⟨rfl, rfl⟩⟩
  have hFc : Continuous F := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · rw [show (Units.val ∘ F) = fun p => elt st h (pb p.1) (pw p.2) from funext fun p => (hF p).1]
      exact hE (pb_cont.comp continuous_fst) (pw_cont.comp continuous_snd)
    · rw [show (fun p => (((F p)⁻¹ : Sˣ) : S)) = fun p => elt st h (-pb p.1) (-pw p.2)
        from funext fun p => (hF p).2]
      exact hE (pb_cont.comp continuous_fst).neg (pw_cont.comp continuous_snd).neg
  refine ⟨F '' (K ×ˢ K), (hK.prod hK).image hFc, ?_, ?_⟩
  · rintro _ ⟨p, _, rfl⟩
    rw [(hF p).1]
    exact elt_cond hm hi hs h31 hh hc (hbx p.1) (hwx p.2)
  · intro g hg
    obtain ⟨b, w, hb, hw, hgeq⟩ := exists_elt hm hi h11 hs h31 hh hc hg.1 hg.2.1 hg.2.2
    obtain ⟨y₁, hy₁, hk₁⟩ := hcov b
    obtain ⟨q1, q3, qs⟩ := hQ b (-pb y₁) hb (hbneg _ (hbx y₁))
    have hw1 : e₁ * (w + h * (st b * -pb y₁ - st (-pb y₁) * b)) = w + h * (st b * -pb y₁ - st (-pb y₁) * b) := by
      rw [mul_add, hw.1, ← mul_assoc, ← hc e₁, mul_assoc, q1]
    have hw3 : (w + h * (st b * -pb y₁ - st (-pb y₁) * b)) * e₃ = w + h * (st b * -pb y₁ - st (-pb y₁) * b) := by
      rw [add_mul, hw.2.1, mul_assoc, q3]
    have hws : st (w + h * (st b * -pb y₁ - st (-pb y₁) * b)) = -(w + h * (st b * -pb y₁ - st (-pb y₁) * b)) := by
      rw [map_add, hm, st_half hm hi hh hc, hw.2.2, qs, ← hc, mul_neg, neg_add]
    obtain ⟨y₂, hy₂, hk₂⟩ := hcov (w + h * (st b * -pb y₁ - st (-pb y₁) * b))
    have hb0 := hbx y₁
    have hw0 := hwx y₂
    let γ : Sˣ := ⟨elt st h (-pb y₁) (-pw y₂), elt st h (pb y₁) (pw y₂),
      elt_neg_mul hm hi hs h31 hh hc ⟨hb0.2.1, hb0.2.2⟩ ⟨hw0.1, hw0.2.1⟩,
      elt_mul_neg hm hi hs h31 hh hc ⟨hb0.2.1, hb0.2.2⟩ ⟨hw0.1, hw0.2.1⟩⟩
    refine ⟨γ, ?_, ?_, ?_, ?_⟩
    · exact elt_cond hm hi hs h31 hh hc (hbneg _ hb0) (hwneg _ hw0)
    · exact eltS _ _ (S₀.neg_mem (pbS y₁ hy₁)) (S₀.neg_mem (pwS y₂ hy₂))
    · exact eltS _ _ (pbS y₁ hy₁) (pwS y₂ hy₂)
    · refine ⟨(b - y₁, w + h * (st b * -pb y₁ - st (-pb y₁) * b) - y₂), ⟨hk₁, hk₂⟩, ?_⟩
      apply Units.ext
      rw [Units.val_mul, (hF _).1]
      show elt st h (pb (b - y₁)) (pw (w + h * (st b * -pb y₁ - st (-pb y₁) * b) - y₂)) =
        elt st h (-pb y₁) (-pw y₂) * (g : S)
      rw [hgeq, elt_mul hm hi hs h31 hh hc ⟨(hbneg _ hb0).2.1, (hbneg _ hb0).2.2⟩ ⟨hb.2.1, hb.2.2⟩
        (hwneg _ hw0).2.1 hw.1]
      rw [pb_sub, pb_id b hb.1 hb.2.1 hb.2.2, pw_sub, pw_id _ hw1 hw3 hws]
      congr 1 <;> abel
end GlobalTheory.TwoStepUnipotent
