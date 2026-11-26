-- Prove2me | solution 1 for HMBinPacking.residue_short_optimization_oracle
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:12:29.415213+00:00
-- url     : https://prove2.me/submissions/de648511-cec8-4077-a03c-adca6a8eb37a

import Definitions.Def_HMBinPacking_Oracles
import Definitions.Def_HMBinPacking_ILP
import Theorems.Thm_HMBinPacking_lenstra_residue_optimization
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
open HMBinPacking Finset ExponomialAssortment.FPTAS

private lemma bits_read (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih => rw [Nat.bits_append_bit _ _ h,List.foldr_cons,ih]

private lemma nat_prefix {a b : ℕ} {x y : List Bool}
    (h : encodeNat a ++ x = encodeNat b ++ y) : a = b ∧ x = y := by
  have hf (n : ℕ) (l) : (encodeNat n ++ l).idxOf false = n.bits.length := by
    simp [encodeNat,List.append_assoc,List.idxOf_append,List.mem_replicate]
  have hl := congrArg (fun z : List Bool => z.idxOf false) h
  change (encodeNat a ++ x).idxOf false = (encodeNat b ++ y).idxOf false at hl
  rw [hf,hf] at hl
  simp only [encodeNat,List.append_assoc] at h
  rw [hl] at h
  have hr := List.append_cancel_left h
  have hh : a.bits ++ x = b.bits ++ y := (List.cons.inj hr).2
  obtain ⟨hb,hxy⟩ := List.append_inj hh hl
  exact ⟨by simpa only [bits_read] using congrArg (fun l : List Bool => l.foldr Nat.bit 0) hb,hxy⟩

private lemma int_prefix {a b : ℤ} {x y : List Bool} (h : encodeInt a ++ x = encodeInt b ++ y) :
    a = b ∧ x = y := by
  have hh := List.cons.inj h
  obtain ⟨ha,ht⟩ := nat_prefix hh.2
  refine ⟨?_,ht⟩
  have hs : decide (a < 0) = decide (b < 0) := hh.1
  cases a <;> cases b <;> simp_all <;> omega

private lemma rat_prefix {a b : ℚ} {x y : List Bool} (h : encodeRat a ++ x = encodeRat b ++ y) :
    a = b ∧ x = y := by
  simp only [encodeRat,List.append_assoc] at h
  obtain ⟨hn,ht⟩ := int_prefix h
  obtain ⟨hd,ht⟩ := nat_prefix ht
  exact ⟨Rat.ext hn hd,ht⟩

private lemma vec_inj {n : ℕ} : Function.Injective (@encVec n) := by
  induction n with
  | zero => exact fun _ _ _ => Subsingleton.elim _ _
  | succ n ih =>
    intro a b h
    simp only [encVec,List.ofFn_succ,List.flatten_cons] at h
    obtain ⟨h0,hs⟩ := rat_prefix h
    have htail : (fun i : Fin n => a i.succ) = fun i => b i.succ := ih hs
    funext i
    exact Fin.cases h0 (congrFun htail) i

private lemma cfg_encoded {I : Instance} (x : Fin I.d → ℤ) (hx : x ∈ S I) :
    (encVec (fun i => (x i : ℚ))).length ≤ I.d * (2 * I.B.size + 5) := by
  have hi (i) : x i ≤ I.B := by
    have h := Finset.single_le_sum (f := fun i => (I.s i : ℤ)*x i)
      (fun j (_ : j ∈ univ) => mul_nonneg (by positivity) (hx.1 j)) (Finset.mem_univ i)
    exact le_trans (by simpa using mul_le_mul_of_nonneg_right (by exact_mod_cast I.s_pos i : (1:ℤ) ≤ I.s i) (hx.1 i)) (h.trans hx.2)
  have hs (i) : (x i).natAbs.size ≤ I.B.size := by
    apply Nat.size_le_size
    exact_mod_cast (by simpa [Int.natAbs_of_nonneg (hx.1 i)] using hi i : ((x i).natAbs : ℤ) ≤ I.B)
  have he (i) : (encodeRat (x i : ℚ)).length ≤ 2 * I.B.size + 5 := by
    simp [encodeRat,encodeInt,encodeNat,Nat.size_eq_bits_len]; have := hs i; omega
  simpa [encVec,List.sum_ofFn,Function.comp_def] using Finset.sum_le_sum (s := univ) (fun i _ => he i)

theorem solution (I : Instance) (r : Fin I.d → Fin I.d) (hr : ∑ i, I.s i * (r i : ℕ) ≤ I.B) :
    (∀ x ∈ Set.extremePoints ℝ (Pr I r), ∃ v : Fin I.d → ℚ, qCast v = x ∧
      (encVec v).length ≤ I.d * (2 * I.B.size + 5)) ∧
    ∃ O : List Bool → List Bool, ∀ u : Fin I.d → ℚ,
      IsOptAnswer (Pr I r) u (O (encVec u)) ∧
      (O (encVec u)).length ≤ I.d * (2 * I.B.size + 5) := by
  classical
  constructor
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := (extremePoints_convexHull_subset (A := zCast '' Sr I r) hx)
    refine ⟨fun i => (z i : ℚ),?_,cfg_encoded z hz.1⟩
    ext i; simp [zCast,qCast]
  · obtain ⟨_,_,_,hg⟩ := lenstra_residue_optimization I r hr
    have hv (u : Fin I.d → ℚ) : ∃ w, IsOptAnswer (Pr I r) u w ∧ w.length ≤ I.d*(2*I.B.size+5) := by
      obtain ⟨y,hy,hm,ho,_⟩ := hg u
      let z (i : Fin I.d) : ℤ := ((r i : ℕ) + I.d*y i : ℕ)
      let v (i : Fin I.d) : ℚ := z i
      have hz : z ∈ S I := ⟨fun i => by dsimp [z]; positivity,by dsimp [z]; exact_mod_cast hy⟩
      have he : qCast v = fun i => (((r i : ℕ) + I.d*y i : ℕ) : ℝ) := by ext i; simp [qCast,v,z]
      refine ⟨encVec v,⟨v,rfl,he ▸ hm,fun x hx => ?_⟩,cfg_encoded z hz⟩
      simpa [v,z] using ho.2 (Set.mem_image_of_mem _ hx)
    choose w hw using hv
    let O := Function.extend encVec w (fun _ => [])
    refine ⟨O,fun u => ?_⟩
    simpa [O,Function.Injective.extend_apply vec_inj] using hw u
