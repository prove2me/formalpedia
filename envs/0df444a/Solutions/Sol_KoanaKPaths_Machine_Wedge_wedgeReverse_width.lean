-- Prove2me | solution 1 for KoanaKPaths.Machine.Wedge.wedgeReverse_width
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:31:20.122385+00:00
-- url     : https://prove2.me/submissions/58fd353c-62ef-4f6d-a442-8a2533047f7e

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Mathlib.Data.Nat.Size
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

variable {S P : ℕ}



































lemma nbits_eq_bits (n : ℕ) : nbits n = Nat.bits n := by
  induction n using Nat.binaryRec' with
  | zero => simp [nbits]
  | bit b n hn ih =>
    have hne : Nat.bit b n ≠ 0 := by
      intro hz
      cases b <;> simp_all [Nat.bit]
    rw [nbits,dif_neg hne,Nat.bit_mod_two,Nat.bit_div_two,ih,Nat.bits_append_bit n b hn]
    cases b <;> rfl

















end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}






































lemma zsz_neg (z : ℤ) : zsz (-z)=zsz z := by simp [zsz,zbits]



end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates

lemma zsz_eq_size (z : ℤ) : zsz z=z.natAbs.size := by
  simp [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len]

lemma zsz_le_iff (z : ℤ) (w : ℕ) : zsz z ≤ w ↔ z.natAbs<2^w := by
  rw [zsz_eq_size,Nat.size_le]

lemma zsz_add_le (x y : ℤ) (w : ℕ) (hx : zsz x≤w) (hy : zsz y≤w) : zsz (x+y)≤w+1 := by
  apply (zsz_le_iff _ _).mpr
  have hx' := (zsz_le_iff x w).mp hx
  have hy' := (zsz_le_iff y w).mp hy
  have ha := Int.natAbs_add_le x y
  rw [pow_succ]
  omega

lemma zsz_sub_le (x y : ℤ) (w : ℕ) (hx : zsz x≤w) (hy : zsz y≤w) : zsz (x-y)≤w+1 := by
  simpa only [sub_eq_add_neg] using zsz_add_le x (-y) w hx (by simpa [zsz_neg] using hy)



lemma zipWith_all {α β γ : Type} (f : α → β → γ) (P : γ → Prop) (xs : List α) (ys : List β)
    (h : ∀ x∈xs, ∀ y∈ys, P (f x y)) : ∀ z∈List.zipWith f xs ys, P z := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      intro z hz
      simp only [List.zipWith_cons_cons,List.mem_cons] at hz
      rcases hz with rfl|hz
      · exact h x (by simp) y (by simp)
      · exact ih ys (fun a ha b hb => h a (by simp [ha]) b (by simp [hb])) z hz

lemma wedgeReverse_width (vs xs : List ℤ) (w : ℕ)
    (hv : ∀ z∈vs, z=1 ∨ z = -1) (hx : ∀ x∈xs, zsz x≤w) :
    ∀ y∈wedgeReverse vs xs, zsz y≤w+vs.length := by
  induction vs generalizing xs with
  | nil => simp [wedgeReverse,zsz_eq_size]
  | cons z vs ih =>
    have hvs : ∀ a∈vs, a=1 ∨ a = -1 := fun a ha => hv a (by simp [ha])
    have hx0 : ∀ x∈xs.take (2^vs.length), zsz x≤w := fun x hm => hx x (List.mem_of_mem_take hm)
    have hx1 : ∀ x∈xs.drop (2^vs.length), zsz x≤w := fun x hm => hx x (List.mem_of_mem_drop hm)
    have hlow := ih _ hvs hx0
    have hupp := ih _ hvs hx1
    intro y hy
    simp only [wedgeReverse,List.mem_append] at hy
    rcases hy with hy|hy
    · have := hlow y hy
      simpa [Nat.add_assoc] using le_trans this (Nat.le_succ _)
    · have hz := hv z (by simp)
      have hzip : ∀ y∈List.zipWith (fun x y => z*x-y) (xs.take (2^vs.length))
          (wedgeReverse vs (xs.drop (2^vs.length))), zsz y≤w+vs.length+1 := by
        apply zipWith_all
        intro a ha b hb
        apply zsz_sub_le
        · rcases hz with rfl|rfl
          · simpa using le_trans (hx0 a ha) (Nat.le_add_right w vs.length)
          · simpa [zsz_neg] using le_trans (hx0 a ha) (Nat.le_add_right w vs.length)
        · exact hupp b hb
      simpa [Nat.add_assoc] using hzip y hy

























end KoanaKPaths.Machine.Wedge

end

theorem solution :
∀ (vs xs : List.{0} Int) (w : Nat)
  (hv :
    ∀ (z : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) vs z →
        Or (@Eq.{1} Int z (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Eq.{1} Int z (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (hx :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
        @LE.le.{0} Nat instLENat (NLogN.zsz x) w)
  (y : Int),
  @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int)
      (KoanaKPaths.ExteriorCoordinates.wedgeReverse vs xs) y →
    @LE.le.{0} Nat instLENat (NLogN.zsz y)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w (@List.length.{0} Int vs)) := by
  exact @KoanaKPaths.Machine.Wedge.wedgeReverse_width
