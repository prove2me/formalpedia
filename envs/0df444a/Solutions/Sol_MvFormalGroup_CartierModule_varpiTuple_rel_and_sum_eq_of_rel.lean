-- Prove2me | solution 1 for MvFormalGroup.CartierModule.varpiTuple_rel_and_sum_eq_of_rel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a35b8936-3574-5cd6-a838-247025bf4644

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_varpiTuple_rel_and_sum_eq_of_rel

set_option autoImplicit false

universe u

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld

noncomputable section

namespace FormalPi

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {Φ : MvFormalGroup 2 B} [Φ.IsComm]

set_option quotPrecheck false in
local notation "V" => (⇑(verschiebungInt (p := p) (Φ := Φ)))

theorem iterV_add (K : ℕ) (x y : CartierModule p Φ) : V^[K] (x + y) = V^[K] x + V^[K] y := by
  induction K generalizing x y with
  | zero => rfl
  | succ K ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_add]

theorem iterV_zero (K : ℕ) : V^[K] (0 : CartierModule p Φ) = 0 := iterate_map_zero _ K

theorem iterV_neg (K : ℕ) (x : CartierModule p Φ) : V^[K] (-x) = -(V^[K] x) := by
  induction K generalizing x with
  | zero => rfl
  | succ K ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_neg]

theorem iterV_sub (K : ℕ) (x y : CartierModule p Φ) : V^[K] (x - y) = V^[K] x - V^[K] y := by
  rw [sub_eq_add_neg, iterV_add, iterV_neg, ← sub_eq_add_neg]

theorem iterV_sum {ι : Type} (s : Finset ι) (K : ℕ) (F : ι → CartierModule p Φ) :
    V^[K] (∑ i ∈ s, F i) = ∑ i ∈ s, V^[K] (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [iterV_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, iterV_add, ih]

theorem iterV_nsmul (K n : ℕ) (x : CartierModule p Φ) : V^[K] (n • x) = n • V^[K] x := by
  induction K generalizing x with
  | zero => rfl
  | succ K ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_nsmul]

theorem iterV_iterV (m n : ℕ) (x : CartierModule p Φ) : V^[m] (V^[n] x) = V^[m + n] x :=
  (Function.iterate_add_apply _ m n x).symm

private theorem _root_.FormalPi.homothety_iterV (c : B) (n : ℕ) (x : CartierModule p Φ) :
    homothety c (V^[n] x) = V^[n] (homothety (c ^ p ^ n) x) := by
  induction n generalizing c x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', homothety_verschiebungInt, ih, Function.iterate_succ_apply',
      ← pow_mul, ← pow_succ']

p2m_export "FormalPi" "homothety_iterV"
private theorem _root_.FormalPi.smul_iterV (m : ℕ) (w : WittVector p B) (x : CartierModule p Φ) :
    w • V^[m] x = V^[m] (((⇑(WittVector.frobenius (p := p) (R := B)))^[m] w) • x) := by
  induction m generalizing w x with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', smul_verschiebungInt, ih, Function.iterate_succ_apply]
    exact (Function.iterate_succ_apply' V m _).symm

p2m_export "FormalPi" "smul_iterV"

def ModV (K : ℕ) (x y : CartierModule p Φ) : Prop := ∃ t : CartierModule p Φ, x = y + V^[K] t

theorem ModV.refl (K : ℕ) (x : CartierModule p Φ) : ModV K x x := ⟨0, by rw [iterV_zero, add_zero]⟩

theorem ModV.symm {K : ℕ} {x y : CartierModule p Φ} (h : ModV K x y) : ModV K y x := by
  obtain ⟨t, ht⟩ := h
  exact ⟨-t, by rw [ht, iterV_neg, add_neg_cancel_right]⟩

theorem ModV.trans {K : ℕ} {x y z : CartierModule p Φ} (h₁ : ModV K x y) (h₂ : ModV K y z) : ModV K x z := by
  obtain ⟨t, ht⟩ := h₁
  obtain ⟨u, hu⟩ := h₂
  exact ⟨u + t, by rw [ht, hu, iterV_add, add_assoc]⟩

theorem ModV.add {K : ℕ} {x y x' y' : CartierModule p Φ} (h₁ : ModV K x y) (h₂ : ModV K x' y') :
    ModV K (x + x') (y + y') := by
  obtain ⟨t, ht⟩ := h₁
  obtain ⟨u, hu⟩ := h₂
  exact ⟨t + u, by rw [ht, hu, iterV_add]; abel⟩

theorem ModV.nsmul {K : ℕ} (n : ℕ) {x y : CartierModule p Φ} (h : ModV K x y) : ModV K (n • x) (n • y) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨n • t, by rw [ht, smul_add, iterV_nsmul]⟩

theorem ModV.iterV_zero' (K : ℕ) (t : CartierModule p Φ) : ModV K (V^[K] t) 0 := ⟨t, by rw [zero_add]⟩

theorem ModV.sum {ι : Type} (s : Finset ι) {K : ℕ} {F G : ι → CartierModule p Φ}
    (h : ∀ i ∈ s, ModV K (F i) (G i)) : ModV K (∑ i ∈ s, F i) (∑ i ∈ s, G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ModV.refl K 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ModV.homothety_iterV {K : ℕ} (m : ℕ) (c : B) {x y : CartierModule p Φ} (h : ModV K x y) :
    ModV K (V^[m] (homothety c x)) (V^[m] (homothety c y)) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨V^[m] (homothety (c ^ p ^ K) t), ?_⟩
  rw [ht, map_add, iterV_add, FormalPi.homothety_iterV, iterV_iterV, iterV_iterV, Nat.add_comm]

theorem ModV.smul_iterV {K : ℕ} (m : ℕ) (w : WittVector p B) {x y : CartierModule p Φ} (h : ModV K x y) :
    ModV K (V^[m] (w • x)) (V^[m] (w • y)) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨V^[m] ((((⇑(WittVector.frobenius (p := p) (R := B)))^[K] w)) • t), ?_⟩
  rw [ht, smul_add, iterV_add, FormalPi.smul_iterV, iterV_iterV, iterV_iterV, Nat.add_comm]

variable (a : ℕ → Fin 2 → B)

def Pop (N : ℕ) (x : Fin 2 → CartierModule p Φ) (i : Fin 2) : CartierModule p Φ :=
  ∑ m ∈ Finset.range N, V^[m] (homothety (a m i) (x (FormalODModule.piIndex m i)))

def dco (k : ℕ) (i : Fin 2) : WittVector p B :=
  ∑ m ∈ Finset.range (k + 2),
    WittVector.teichmuller p (a m i ^ p ^ (k + 1 - m) * a (k + 1 - m) (FormalODModule.piIndex m i))

def P2op (N : ℕ) (x : Fin 2 → CartierModule p Φ) (i : Fin 2) : CartierModule p Φ :=
  WittVector.teichmuller p (p : B) • x i +
    ∑ k ∈ Finset.range N, V^[k + 1] (dco (p := p) a k i • x (FormalODModule.piIndex k i))

variable {a}

theorem Pop_congr {K N : ℕ} {x y : Fin 2 → CartierModule p Φ} (h : ∀ j, ModV K (x j) (y j)) (i : Fin 2) :
    ModV K (Pop (Φ := Φ) a N x i) (Pop a N y i) :=
  ModV.sum _ fun m _ => ModV.homothety_iterV m _ (h _)

theorem P2op_congr {K N : ℕ} {x y : Fin 2 → CartierModule p Φ} (h : ∀ j, ModV K (x j) (y j)) (i : Fin 2) :
    ModV K (P2op (Φ := Φ) a N x i) (P2op a N y i) := by
  refine ModV.add ?_ (ModV.sum _ fun k _ => ModV.smul_iterV (k + 1) _ (h _))
  have := ModV.smul_iterV (Φ := Φ) 0 (WittVector.teichmuller p (p : B)) (h i)
  exact this

theorem Pop_nsmul (N n : ℕ) (x : Fin 2 → CartierModule p Φ) (i : Fin 2) :
    Pop (Φ := Φ) a N (fun j => n • x j) i = n • Pop a N x i := by
  simp only [Pop, map_nsmul, iterV_nsmul, Finset.smul_sum]

theorem Pop_Pop (M : ℕ) (x : Fin 2 → CartierModule p Φ) (i : Fin 2) :
    Pop (Φ := Φ) a M (Pop a M x) i =
      ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M, V^[m + n]
        (WittVector.teichmuller p (a m i ^ p ^ n * a n (FormalODModule.piIndex m i)) •
          x (FormalODModule.piIndex n (FormalODModule.piIndex m i))) := by
  simp only [Pop]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_sum, iterV_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [homothety_iterV, ← homothety_mul, iterV_iterV, teichmuller_smul]

theorem sum_sum_iterV_modV (M : ℕ) (G : ℕ → ℕ → CartierModule p Φ) :
    ModV M (∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M, V^[m + n] (G m n))
      (∑ k ∈ Finset.range M, V^[k] (∑ m ∈ Finset.range (k + 1), G m (k - m))) := by

  have h1 : ModV M (∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M, V^[m + n] (G m n))
      (∑ m ∈ Finset.range M, ∑ n ∈ Finset.range (M - m), V^[m + n] (G m n)) := by
    refine ModV.sum _ fun m hm => ?_
    have hmM : M - m ≤ M := Nat.sub_le M m
    rw [← Finset.sum_range_add_sum_Ico _ hmM]
    refine ⟨∑ n ∈ Finset.Ico (M - m) M, V^[m + n - M] (G m n), ?_⟩
    congr 1
    rw [iterV_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [iterV_iterV]
    congr 1
    have : M - m ≤ n := (Finset.mem_Ico.mp hn).1
    omega

  have h2 : (∑ m ∈ Finset.range M, ∑ n ∈ Finset.range (M - m), V^[m + n] (G m n)) =
      ∑ k ∈ Finset.range M, V^[k] (∑ m ∈ Finset.range (k + 1), G m (k - m)) := by
    have e1 : ∀ m ∈ Finset.range M, (∑ n ∈ Finset.range (M - m), V^[m + n] (G m n)) =
        ∑ k ∈ Finset.Ico m M, V^[k] (G m (k - m)) := by
      intro m hm
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Nat.add_sub_cancel_left]
    rw [Finset.sum_congr rfl e1]
    simp only [Finset.range_eq_Ico]
    rw [Finset.sum_Ico_Ico_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iterV_sum]
  obtain ⟨t, ht⟩ := h1
  exact ⟨t, by rw [ht, h2]⟩

theorem piIndex_piIndex_sub {k m : ℕ} (hm : m ≤ k + 1) (i : Fin 2) :
    FormalODModule.piIndex (k + 1 - m) (FormalODModule.piIndex m i) = FormalODModule.piIndex k i := by
  apply Fin.ext
  simp only [FormalODModule.piIndex_val]
  omega

theorem piIndex_zero_piIndex_zero (i : Fin 2) :
    FormalODModule.piIndex 0 (FormalODModule.piIndex 0 i) = i := by
  apply Fin.ext
  simp only [FormalODModule.piIndex_val]
  have := i.isLt
  omega

theorem a_zero_mul (ha : a 0 0 * a 0 1 = (p : B)) (i : Fin 2) :
    a 0 i * a 0 (FormalODModule.piIndex 0 i) = (p : B) := by
  fin_cases i
  · exact ha
  · rw [mul_comm]
    exact ha

theorem Pop_Pop_modV (ha : a 0 0 * a 0 1 = (p : B)) (N : ℕ) (x : Fin 2 → CartierModule p Φ) (i : Fin 2) :
    ModV (N + 1) (Pop (Φ := Φ) a (N + 1) (Pop a (N + 1) x) i) (P2op a N x i) := by
  rw [Pop_Pop]
  refine (sum_sum_iterV_modV (N + 1) fun m n =>
    WittVector.teichmuller p (a m i ^ p ^ n * a n (FormalODModule.piIndex m i)) •
      x (FormalODModule.piIndex n (FormalODModule.piIndex m i))).trans ?_
  refine ⟨0, ?_⟩
  rw [iterV_zero, add_zero, Finset.sum_range_succ', P2op]
  refine Eq.trans (add_comm _ _) ?_
  congr 1
  · rw [Finset.sum_range_one, Function.iterate_zero, id, Nat.sub_zero, pow_zero, pow_one,
      piIndex_zero_piIndex_zero, a_zero_mul ha]
  · refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [dco, Finset.sum_smul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [piIndex_piIndex_sub (by have := Finset.mem_range.mp hm; omega) i]

theorem main (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (a : ℕ → Fin 2 → B) (ha : a 0 0 * a 0 1 = (p : B))
    (Φ : MvFormalGroup 2 B) [Φ.IsComm]
    (f : Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hrel : ∀ (N : ℕ) (i : Fin 2), ∃ s : MvFormalGroup.CartierModule p Φ,
      p • f i = WittVector.teichmuller p (p : B) • f i +
        (∑ k ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[k + 1]
          ((∑ m ∈ Finset.range (k + 2), WittVector.teichmuller p
              (a m i ^ p ^ (k + 1 - m) * a (k + 1 - m) (CerednikDrinfeld.FormalODModule.piIndex m i))) •
            f (CerednikDrinfeld.FormalODModule.piIndex k i))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N + 1] s)
    (g : Fin 2 → MvFormalGroup.CartierModule p Φ)
    (r : ℕ → Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hg : ∀ (N : ℕ) (i : Fin 2), g i =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
        (MvFormalGroup.CartierModule.homothety (a m i) (f (CerednikDrinfeld.FormalODModule.piIndex m i)))) +
      (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (r N i)) :
    (∀ (N : ℕ) (i : Fin 2), ∃ s : MvFormalGroup.CartierModule p Φ,
      p • g i = WittVector.teichmuller p (p : B) • g i +
        (∑ k ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[k + 1]
          ((∑ m ∈ Finset.range (k + 2), WittVector.teichmuller p
              (a m i ^ p ^ (k + 1 - m) * a (k + 1 - m) (CerednikDrinfeld.FormalODModule.piIndex m i))) •
            g (CerednikDrinfeld.FormalODModule.piIndex k i))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N + 1] s) ∧
    (∀ (N : ℕ) (i : Fin 2), ∃ s : MvFormalGroup.CartierModule p Φ,
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
        (MvFormalGroup.CartierModule.homothety (a m i) (g (CerednikDrinfeld.FormalODModule.piIndex m i)))) +
      (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] s = p • f i) := by

  have hrel' : ∀ (N : ℕ) (j : Fin 2), ModV (N + 1) (p • f j) (P2op (Φ := Φ) a N f j) := by
    intro N j
    obtain ⟨s, hs⟩ := hrel N j
    exact ⟨s, hs⟩
  have hg' : ∀ (N : ℕ) (j : Fin 2), ModV N (g j) (Pop (Φ := Φ) a N f j) := fun N j => ⟨r N j, hg N j⟩
  refine ⟨fun N i => ?_, fun N i => ?_⟩
  ·
    have h1 : ModV (N + 1) (p • g i) (p • Pop (Φ := Φ) a (N + 1) f i) := (hg' (N + 1) i).nsmul p
    have h2 : p • Pop (Φ := Φ) a (N + 1) f i = Pop a (N + 1) (fun j => p • f j) i := (Pop_nsmul _ _ _ _).symm
    have h3 : ModV (N + 1) (Pop (Φ := Φ) a (N + 1) (fun j => p • f j) i) (Pop a (N + 1) (P2op a N f) i) :=
      Pop_congr (hrel' N) i
    have h4 : ModV (N + 1) (Pop (Φ := Φ) a (N + 1) (P2op a N f) i)
        (Pop a (N + 1) (Pop a (N + 1) (Pop a (N + 1) f)) i) :=
      Pop_congr (fun j => (Pop_Pop_modV ha N f j).symm) i
    have h5 : ModV (N + 1) (Pop (Φ := Φ) a (N + 1) (Pop a (N + 1) (Pop a (N + 1) f)) i)
        (P2op a N (Pop a (N + 1) f) i) := Pop_Pop_modV ha N _ i
    have h6 : ModV (N + 1) (P2op (Φ := Φ) a N (Pop a (N + 1) f) i) (P2op a N g i) :=
      P2op_congr (fun j => (hg' (N + 1) j).symm) i
    obtain ⟨s, hs⟩ := ((h2 ▸ h1).trans h3).trans h4 |>.trans h5 |>.trans h6
    exact ⟨s, hs⟩
  ·
    cases N with
    | zero => exact ⟨p • f i, by simp⟩
    | succ N =>
      have h1 : ModV (N + 1) (Pop (Φ := Φ) a (N + 1) g i) (Pop a (N + 1) (Pop a (N + 1) f) i) :=
        Pop_congr (hg' (N + 1)) i
      obtain ⟨s, hs⟩ := ((h1.trans (Pop_Pop_modV ha N f i)).trans (hrel' N i).symm).symm
      exact ⟨s, hs.symm⟩

end FormalPi

end

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (a : ℕ → Fin 2 → B) (ha : a 0 0 * a 0 1 = (p : B))
    (Φ : MvFormalGroup 2 B) [Φ.IsComm]
    (f : Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hrel : ∀ (N : ℕ) (i : Fin 2), ∃ s : MvFormalGroup.CartierModule p Φ,
      p • f i = WittVector.teichmuller p (p : B) • f i +
        (∑ k ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[k + 1]
          ((∑ m ∈ Finset.range (k + 2), WittVector.teichmuller p
              (a m i ^ p ^ (k + 1 - m) * a (k + 1 - m) (CerednikDrinfeld.FormalODModule.piIndex m i))) •
            f (CerednikDrinfeld.FormalODModule.piIndex k i))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N + 1] s)
    (g : Fin 2 → MvFormalGroup.CartierModule p Φ)
    (r : ℕ → Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hg : ∀ (N : ℕ) (i : Fin 2), g i =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
        (MvFormalGroup.CartierModule.homothety (a m i) (f (CerednikDrinfeld.FormalODModule.piIndex m i)))) +
      (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (r N i)) :
    (∀ (N : ℕ) (i : Fin 2), ∃ s : MvFormalGroup.CartierModule p Φ,
      p • g i = WittVector.teichmuller p (p : B) • g i +
        (∑ k ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[k + 1]
          ((∑ m ∈ Finset.range (k + 2), WittVector.teichmuller p
              (a m i ^ p ^ (k + 1 - m) * a (k + 1 - m) (CerednikDrinfeld.FormalODModule.piIndex m i))) •
            g (CerednikDrinfeld.FormalODModule.piIndex k i))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N + 1] s) ∧
    (∀ (N : ℕ) (i : Fin 2), ∃ s : MvFormalGroup.CartierModule p Φ,
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
        (MvFormalGroup.CartierModule.homothety (a m i) (g (CerednikDrinfeld.FormalODModule.piIndex m i)))) +
      (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] s = p • f i) := by
  exact FormalPi.main p a ha Φ f hrel g r hg

end S_MvFormalGroup_CartierModule_varpiTuple_rel_and_sum_eq_of_rel
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_varpiTuple_rel_and_sum_eq_of_rel (solution)
