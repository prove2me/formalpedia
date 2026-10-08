-- Prove2me | solution 1 for OAI.DeligneDrinfeld.IntegralFamily.main_of_oddValues
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T18:54:08.846976+00:00
-- url     : https://prove2.me/submissions/8f34737a-fceb-4626-a7e2-df0eab111fcd

import Mathlib
import Definitions.Def_DeligneDrinfeld
import Definitions.Def_DeligneDrinfeldBraid
import Theorems.Thm_OAI_DeligneDrinfeld_Differentiation_special_identity
import Theorems.Thm_OAI_DeligneDrinfeld_ImageBound_actual_image
import Theorems.Thm_OAI_DeligneDrinfeld_NormalizedFamily_bihomogeneous_leading
import Theorems.Thm_OAI_DeligneDrinfeld_ProjectionKernel_leading_projection_kernel

set_option linter.all false

universe u

section

namespace OAI

noncomputable section
namespace DeligneDrinfeld

theorem t_disjoint (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ⁅t i j,t k l⁆ = 0 := by
  rw [t, t, ← LieSubmodule.Quotient.mk_bracket, LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inl ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩)

theorem t_three (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅t i j,t i k + t j k⁆ = 0 := by
  change LieSubmodule.Quotient.mk (⁅chord i j, chord i k + chord j k⁆) = (0 : T4)
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inr ⟨i,j,k,hij,hik,hjk,rfl⟩)

namespace T4Universal
variable {M : Type*} [LieRing M] [LieAlgebra ℚ M]

def pre (f : Fin 4 → Fin 4 → M) : BraidFree →ₗ⁅ℚ⁆ M :=
  FreeLieAlgebra.lift ℚ (fun e => f e.val.1 e.val.2)

theorem pre_chord (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0) (i j : Fin 4) :
    pre f (chord i j) = f i j := by
  unfold chord
  split_ifs with hij hji
  · simp [pre]
  · simp [pre, hs j i]
  · have h : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
    subst j
    simp [hz]

def lift (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0)
    (hd : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      ⁅f i j,f k l⁆ = 0)
    (ht : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ⁅f i j,f i k+f j k⁆ = 0) : T4 →ₗ⁅ℚ⁆ M := by
  have hker : braidIdeal ≤ (pre f).ker := by
    rw [braidIdeal, LieSubmodule.lieSpan_le]
    intro z hz'
    change pre f z = 0
    rcases hz' with ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
    · simpa only [LieHom.map_lie, pre_chord f hs hz] using hd i j k l hij hik hil hjk hjl hkl
    · simpa only [LieHom.map_lie, map_add, pre_chord f hs hz] using ht i j k hij hik hjk
  exact { braidIdeal.toSubmodule.liftQ (pre f).toLinearMap hker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact (pre f).map_lie a b }

@[simp] theorem lift_t (f : Fin 4 → Fin 4 → M) (hs hz hd ht) (i j : Fin 4) :
    lift f hs hz hd ht (t i j) = f i j := pre_chord f hs hz i j

end T4Universal

namespace Elimination
open LieAlgebra
variable {R α : Type*} [CommRing R]
attribute [local instance] LieRing.ofAssociativeRing

theorem expand_adWord (n : ℕ) (a : α) :
    expand (adWord n a : G R α) = SemiDirectSum.inl action (E n a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [adWord_succ,LieHom.map_lie,expand_X,ih]
    simp only [SemiDirectSum.lie_eq_mk,SemiDirectSum.inl_eq_mk,SemiDirectSum.inr_eq_mk]
    ext <;> simp [action]

end Elimination

namespace IntegralWords
open Classical
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {α β : Type*}
abbrev AQ (α : Type*) := A ℚ α

def word (w : List α) : AQ α := MonoidAlgebra.single (FreeMonoid.ofList w) 1
@[simp] theorem word_nil : word ([] : List α) = 1 := rfl
@[simp] theorem word_singleton (a : α) : word [a] = atom a := rfl
theorem word_append (u v : List α) : word (u++v) = word u * word v := by
  simp [word,MonoidAlgebra.single_mul_single,FreeMonoid.ofList_append]
theorem word_cons (a : α) (w : List α) : word (a::w) = atom a * word w := by
  exact word_append [a] w

def lattice : Submodule ℤ (AQ α) := Submodule.span ℤ (Set.range word)
def lieLattice : LieSubalgebra ℤ (AQ α) := LieSubalgebra.lieSpan ℤ (AQ α) (Set.range atom)
def rationalLie : LieSubalgebra ℚ (AQ α) := LieSubalgebra.lieSpan ℚ (AQ α) (Set.range atom)

theorem word_integral (w : List α) : word w ∈ lattice := Submodule.subset_span ⟨w,rfl⟩
theorem atom_integral (a : α) : (atom a : AQ α) ∈ lattice := word_integral [a]
theorem one_integral : (1 : AQ α) ∈ lattice := word_integral []

theorem integral_mul {p q : AQ α} (hp : p ∈ lattice) (hq : q ∈ lattice) : p*q ∈ lattice := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨u,rfl⟩
    induction hq using Submodule.span_induction with
    | mem q hq =>
      rcases hq with ⟨v,rfl⟩
      rw [← word_append]
      exact word_integral _
    | zero => simp
    | add p q _ _ hp hq => simpa only [mul_add] using (lattice.add_mem hp hq)
    | smul r p _ hp => simpa only [mul_smul_comm] using lattice.smul_mem r hp
  | zero => simp
  | add p q _ _ hp hq => simpa only [add_mul] using lattice.add_mem hp hq
  | smul r p _ hp => simpa only [smul_mul_assoc] using lattice.smul_mem r hp

theorem integral_of_coeff {p : AQ α} (hp : ∀ w, ∃ z : ℤ, p.coeff w = (z : ℚ)) : p ∈ lattice := by
  classical
  rw [← MonoidAlgebra.sum_coeff_single p]
  apply Submodule.sum_mem
  intro w hw
  obtain ⟨z,hz⟩ := hp w
  rw [hz]
  convert lattice.smul_mem z (word_integral w.toList) using 1
  simp [word]

def words (P : List α → Prop) : Submodule ℚ (AQ α) :=
  Submodule.span ℚ {p | ∃ w, P w ∧ p=word w}

theorem word_mem {P : List α → Prop} {w : List α} (hw : P w) : word w ∈ words P :=
  Submodule.subset_span ⟨w,hw,rfl⟩

theorem mem_words {P : List α → Prop} {p : AQ α} :
    p ∈ words P ↔ ∀ w, p.coeff w ≠ 0 → P w.toList := by
  classical
  constructor
  · intro hp w hw
    induction hp using Submodule.span_induction with
    | mem p hp =>
      rcases hp with ⟨u,hu,rfl⟩
      have h : FreeMonoid.ofList u = w := by
        by_contra h
        exact hw (by simp [word,h])
      simpa [← h] using hu
    | zero => exact (hw (by simp)).elim
    | add p q _ _ hp hq =>
      by_cases h : p.coeff w = 0
      · exact hq (by simpa [h] using hw)
      · exact hp h
    | smul r p _ hp =>
      exact hp (by intro h; apply hw; simp [h])
  · intro hp
    rw [← MonoidAlgebra.sum_coeff_single p]
    apply Submodule.sum_mem
    intro w hw
    have h : P w.toList := hp w (Finsupp.mem_support_iff.mp hw)
    convert (words P).smul_mem (p.coeff w) (word_mem h) using 1
    simp [word]

theorem words_mono {P Q : List α → Prop} (h : ∀ w, P w → Q w) : words P ≤ words Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w,hw,rfl⟩
  exact word_mem (h w hw)

theorem mul_words {P Q T : List α → Prop} {p q : AQ α}
    (h : ∀ u v, P u → Q v → T (u++v)) (hp : p ∈ words P) (hq : q ∈ words Q) : p*q ∈ words T := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    rcases hp with ⟨u,hu,rfl⟩
    induction hq using Submodule.span_induction with
    | mem q hq =>
      rcases hq with ⟨v,hv,rfl⟩
      rw [← word_append]
      exact word_mem (h u v hu hv)
    | zero => simp
    | add p q _ _ hp hq => simpa only [mul_add] using (words T).add_mem hp hq
    | smul r p _ hp => simpa only [mul_smul_comm] using (words T).smul_mem r hp
  | zero => simp
  | add p q _ _ hp hq => simpa only [add_mul] using (words T).add_mem hp hq
  | smul r p _ hp => simpa only [smul_mul_assoc] using (words T).smul_mem r hp

theorem lie_has_preimage {p : AQ α} (hp : p ∈ rationalLie) : ∃ q : FreeLieAlgebra ℚ α, embed q = p := by
  have h : rationalLie (α := α) ≤ (embed : FreeLieAlgebra ℚ α →ₗ⁅ℚ⁆ AQ α).range := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨a,rfl⟩
    exact ⟨FreeLieAlgebra.of ℚ a,embed_of a⟩
  exact h hp

theorem embed_mem_lie (p : FreeLieAlgebra ℚ α) : embed p ∈ rationalLie := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => rw [embed_of]; exact LieSubalgebra.subset_lieSpan ⟨a,rfl⟩
  | ha p q hp hq => simpa using rationalLie.add_mem hp hq
  | hs r p hp => simpa using rationalLie.smul_mem r hp
  | hl p q hp hq => simpa only [LieHom.map_lie] using rationalLie.lie_mem hp hq

theorem shift_integral {p : AQ (ℕ×α)} (hp : p ∈ lattice) : shift p ∈ lattice := by
  have hword : ∀ w : List (ℕ×α), shift (word w) ∈ lattice := by
    intro w
    induction w with
    | nil => simp
    | cons a w ih =>
      rcases a with ⟨i,a⟩
      rw [word_cons,shift_mul,shift_atom]
      exact lattice.add_mem (integral_mul (atom_integral _) (word_integral _))
        (integral_mul (atom_integral _) ih)
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,rfl⟩ := hp; exact hword w
  | zero => simp
  | add p q _ _ hp hq => simpa using lattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lattice.smul_mem r hp

theorem extract_integral {p : AQ (Option α)} (hp : p ∈ lattice) : extract p ∈ lattice := by
  have hword : ∀ w : List (Option α), ∀ q : AQ (ℕ×α), q ∈ lattice → operator (word w) q ∈ lattice := by
    intro w
    induction w with
    | nil => intro q hq; simpa using hq
    | cons a w ih =>
      intro q hq
      rw [word_cons,map_mul,Module.End.mul_apply]
      cases a with
      | none => simpa [operator] using shift_integral (ih q hq)
      | some a => simpa [operator] using integral_mul (atom_integral (0,a)) (ih q hq)
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,rfl⟩ := hp; exact hword w 1 one_integral
  | zero => simp
  | add p q _ _ hp hq => simpa using lattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lattice.smul_mem r hp

theorem extract_lie {p : AQ (Option α)} (hp : p ∈ rationalLie) : extract p ∈ rationalLie := by
  obtain ⟨q,rfl⟩ := lie_has_preimage hp
  rw [extract_embed]
  exact embed_mem_lie _

theorem shift_length {p : AQ (ℕ×α)} {n : ℕ} (hp : p ∈ words (fun w => w.length=n)) :
    shift p ∈ words (fun w => w.length=n) := by
  have hword : ∀ w : List (ℕ×α), shift (word w) ∈ words (fun v => v.length=w.length) := by
    intro w
    induction w with
    | nil => simp
    | cons a w ih =>
      rcases a with ⟨i,a⟩
      rw [word_cons,shift_mul,shift_atom]
      apply (words _).add_mem
      · exact mul_words (fun u v hu hv => by simp [List.length_append,hu,hv,Nat.add_comm])
          (word_mem (P := fun v => v.length=1) (w := [(i+1,a)]) rfl) (word_mem (P := fun v => v.length=w.length) (w := w) rfl)
      · exact mul_words (fun u v hu hv => by simp [List.length_append,hu,hv,Nat.add_comm])
          (word_mem (P := fun v => v.length=1) (w := [(i,a)]) rfl) ih
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,hw,rfl⟩ := hp; simpa [hw] using hword w
  | zero => simp
  | add p q _ _ hp hq => simpa using (words _).add_mem hp hq
  | smul r p _ hp => simpa using (words _).smul_mem r hp

theorem operator_length (w : List (Option α)) {q : AQ (ℕ×α)} {n : ℕ}
    (hq : q ∈ words (fun v => v.length=n)) :
    operator (word w) q ∈ words (fun v => v.length=n+countSome w) := by
  induction w with
  | nil => simpa [countSome] using hq
  | cons a w ih =>
    rw [word_cons,map_mul,Module.End.mul_apply]
    cases a with
    | none => simpa [operator,countSome] using shift_length ih
    | some a =>
      have h : atom (0,a) * operator (word w) q ∈ words (fun v => v.length=n+countSome w+1) :=
        mul_words (fun u v (hu : u.length=1) (hv : v.length=n+countSome w) => by
          simp [List.length_append,hu,hv,Nat.add_comm])
          (word_mem (P := fun v => v.length=1) (w := [(0,a)]) rfl) ih
      simpa [operator,countSome, Nat.add_assoc] using h

theorem extract_word_length (w : List (Option α)) :
    extract (word w) ∈ words (fun v => v.length=countSome w) := by
  simpa [extract] using operator_length w (word_mem (w := []) rfl)

def rename (f : α → β) : AQ α →ₐ[ℚ] AQ β := lift (fun a => atom (f a))
@[simp] theorem rename_atom (f : α → β) (a : α) : rename f (atom a) = atom (f a) := by
  simp [rename]

theorem rename_word (f : α → β) (w : List α) : rename f (word w) = word (w.map f) := by
  induction w with
  | nil => simp
  | cons a w ih => simp [word_cons,ih]

theorem rename_integral (f : α → β) {p : AQ α} (hp : p ∈ lattice) : rename f p ∈ lattice := by
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,rfl⟩ := hp; rw [rename_word]; exact word_integral _
  | zero => simp
  | add p q _ _ hp hq => simpa using lattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lattice.smul_mem r hp

theorem rename_lie (f : α → β) {p : AQ α} (hp : p ∈ rationalLie) : rename f p ∈ rationalLie := by
  induction hp using LieSubalgebra.lieSpan_induction ℚ with
  | mem p hp => obtain ⟨a,rfl⟩ := hp; rw [rename_atom]; exact LieSubalgebra.subset_lieSpan ⟨f a,rfl⟩
  | zero => simp
  | add p q _ _ hp hq => simpa using rationalLie.add_mem hp hq
  | smul r p _ hp => simpa using rationalLie.smul_mem r hp
  | lie p q _ _ hp hq => simpa only [Ring.lie_def,map_sub,map_mul] using rationalLie.lie_mem hp hq

theorem rename_lieIntegral (f : α → β) {p : AQ α} (hp : p ∈ lieLattice) : rename f p ∈ lieLattice := by
  induction hp using LieSubalgebra.lieSpan_induction ℤ with
  | mem p hp => obtain ⟨a,rfl⟩ := hp; rw [rename_atom]; exact LieSubalgebra.subset_lieSpan ⟨f a,rfl⟩
  | zero => simp
  | add p q _ _ hp hq => simpa using lieLattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lieLattice.smul_mem r hp
  | lie p q _ _ hp hq => simpa only [Ring.lie_def,map_sub,map_mul] using lieLattice.lie_mem hp hq

noncomputable def kill (a : α) : AQ α →ₐ[ℚ] AQ α := by
  classical
  exact lift fun b => if a=b then 0 else atom b

theorem kill_atom (a b : α) : kill a (atom b) = if a=b then 0 else atom b := by
  classical
  simp [kill]

theorem kill_word (a : α) (w : List α) : kill a (word w) = if a ∈ w then 0 else word w := by
  classical
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [word_cons,map_mul,kill_atom,ih]
    by_cases h : a=b <;> by_cases h' : a ∈ w <;> simp [h,h']

theorem kill_integral (a : α) {p : AQ α} (hp : p ∈ lattice) : kill a p ∈ lattice := by
  classical
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,rfl⟩ := hp
    rw [kill_word]
    split_ifs <;> simp [word_integral]
  | zero => simp
  | add p q _ _ hp hq => simpa using lattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lattice.smul_mem r hp

theorem kill_lie (a : α) {p : AQ α} (hp : p ∈ rationalLie) : kill a p ∈ rationalLie := by
  classical
  induction hp using LieSubalgebra.lieSpan_induction ℚ with
  | mem p hp =>
    obtain ⟨b,rfl⟩ := hp
    rw [kill_atom]
    split_ifs
    · exact rationalLie.zero_mem
    · exact LieSubalgebra.subset_lieSpan ⟨b,rfl⟩
  | zero => simp
  | add p q _ _ hp hq => simpa using rationalLie.add_mem hp hq
  | smul r p _ hp => simpa using rationalLie.smul_mem r hp
  | lie p q _ _ hp hq => simpa only [Ring.lie_def,map_sub,map_mul] using rationalLie.lie_mem hp hq

theorem rename_untag_tag (a : α) (p : AQ α) : rename (untag a) (rename (tag a) p) = p := by
  have h : (rename (untag a)).comp (rename (tag a)) = AlgHom.id ℚ (AQ α) := by
    apply hom_ext
    intro b
    simp only [AlgHom.comp_apply,rename_atom,AlgHom.id_apply]
    congr 1
    dsimp [tag]
    split_ifs with h
    · exact h
    · rfl
  exact AlgHom.congr_fun h p

theorem rename_extract_lower (a : α) {p : AQ α} {n : ℕ}
    (hp : p ∈ words (fun w => w.length≤n+1 ∧ a ∈ w)) :
    extract (rename (tag a) p) ∈ words (fun w => w.length≤n) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    rw [rename_word]
    have hm : none ∈ w.map (tag a) := List.mem_map.mpr ⟨a,hw.2,by simp [tag]⟩
    have hc := countSome_lt hm
    apply words_mono (P := fun v => v.length=countSome (w.map (tag a))) ?_ (extract_word_length _)
    intro v hv
    simp only [List.length_map] at hc
    omega
  | zero => simp
  | add p q _ _ hp hq => simpa using (words _).add_mem hp hq
  | smul r p _ hp => simpa using (words _).smul_mem r hp

theorem kill_bound (a : α) (S : Finset α) (n : ℕ) {p : AQ α}
    (hp : p ∈ words (fun w => w.length≤n ∧ ∀ b ∈ w, b ∈ insert a S)) :
    kill a p ∈ words (fun w => w.length≤n ∧ ∀ b ∈ w, b ∈ S) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    rw [kill_word]
    split_ifs with h
    · exact (words _).zero_mem
    · apply word_mem
      refine ⟨hw.1,?_⟩
      intro b hb
      rcases Finset.mem_insert.mp (hw.2 b hb) with h'|h'
      · exact (h (h' ▸ hb)).elim
      · exact h'
  | zero => simp
  | add p q _ _ hp hq => simpa using (words _).add_mem hp hq
  | smul r p _ hp => simpa using (words _).smul_mem r hp

theorem remainder_bound (a : α) {p : AQ α} {n : ℕ}
    (hp : p ∈ words (fun w => w.length≤n)) :
    p-kill a p ∈ words (fun w => w.length≤n ∧ a ∈ w) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    rw [kill_word]
    split_ifs with h
    · simpa using word_mem (P := fun v => v.length≤n ∧ a ∈ v) ⟨hw,h⟩
    · simp
  | zero => simp
  | add p q _ _ hp hq =>
    rw [map_add]
    convert (words _).add_mem hp hq using 1
    abel
  | smul r p _ hp => simpa only [map_smul,smul_sub] using (words _).smul_mem r hp

theorem lie_positive {p : AQ α} (hp : p ∈ rationalLie) : p ∈ words (fun w => 0<w.length) := by
  induction hp using LieSubalgebra.lieSpan_induction ℚ with
  | mem p hp => obtain ⟨a,rfl⟩ := hp; exact word_mem (w := [a]) (by simp)
  | zero => simp
  | add p q _ _ hp hq => exact (words _).add_mem hp hq
  | smul r p _ hp => exact (words _).smul_mem r hp
  | lie p q _ _ hp hq =>
    apply (words _).sub_mem
    · exact mul_words (fun u v hu hv => by simp only [List.length_append]; omega) hp hq
    · exact mul_words (fun u v hu hv => by simp only [List.length_append]; omega) hq hp

def traceX : AQ (Option α) →ₐ[ℚ] ℚ := lift (fun | none => 1 | some _ => 0)

theorem trace_embed (q : Elimination.G ℚ α) : traceX (embed q) = (Elimination.expand q).right := by
  have h : traceX.toLieHom.comp embed =
      (LieAlgebra.SemiDirectSum.projr Elimination.action).comp (Elimination.expand : Elimination.G ℚ α →ₗ⁅ℚ⁆ Elimination.M ℚ α) := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [traceX,Elimination.expand]
  exact LieHom.congr_fun h q

def collapseAssoc : AQ (ℕ×α) →ₐ[ℚ] AQ (Option α) :=
  lift (fun (i,a) => embed (Elimination.adWord i a))

theorem collapse_embed (q : Elimination.F ℚ α) :
    collapseAssoc (embed q) = embed (Elimination.collapseFiber q) := by
  have h : collapseAssoc.toLieHom.comp embed =
      (embed : Elimination.G ℚ α →ₗ⁅ℚ⁆ AQ (Option α)).comp Elimination.collapseFiber := by
    apply FreeLieAlgebra.hom_ext
    intro a
    rcases a with ⟨i,a⟩
    simp [collapseAssoc,Elimination.collapseFiber]
  exact LieHom.congr_fun h q

theorem decompose_lie {p : AQ (Option α)} (hp : p ∈ rationalLie) :
    p = collapseAssoc (extract p) + traceX p • atom none := by
  obtain ⟨q,rfl⟩ := lie_has_preimage hp
  rw [extract_embed,collapse_embed,trace_embed]
  conv_lhs => rw [← Elimination.collapse_expand q]
  change embed (Elimination.collapseFiber (Elimination.expand q).left +
    (Elimination.expand q).right • Elimination.X) = _
  simp [Elimination.X]

theorem trace_integral {p : AQ (Option α)} (hp : p ∈ lattice) : ∃ z : ℤ, traceX p = (z : ℚ) := by
  have hw : ∀ w : List (Option α), ∃ z : ℤ, traceX (word w) = (z : ℚ) := by
    intro w
    induction w with
    | nil => exact ⟨1,by simp⟩
    | cons a w ih =>
      obtain ⟨z,hz⟩ := ih
      rw [word_cons,map_mul,hz]
      cases a with
      | none => exact ⟨z,by simp [traceX]⟩
      | some a => exact ⟨0,by simp [traceX]⟩
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,rfl⟩ := hp; exact hw w
  | zero => exact ⟨0,by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := hq
    exact ⟨a+b,by simp [ha,hb]⟩
  | smul r p _ hp =>
    obtain ⟨a,ha⟩ := hp
    refine ⟨r*a,?_⟩
    rw [map_zsmul,ha]
    simp [zsmul_eq_mul]

theorem adWord_integralLie (i : ℕ) (a : α) :
    embed (Elimination.adWord i a) ∈ lieLattice := by
  induction i with
  | zero =>
    simp only [Elimination.adWord,Function.iterate_zero_apply,Elimination.Y,embed_of]
    exact LieSubalgebra.subset_lieSpan ⟨some a,rfl⟩
  | succ i ih =>
    rw [Elimination.adWord_succ,LieHom.map_lie]
    apply lieLattice.lie_mem ?_ ih
    simp only [Elimination.X,embed_of]
    exact LieSubalgebra.subset_lieSpan ⟨none,rfl⟩

theorem collapse_integralLie {p : AQ (ℕ×α)} (hp : p ∈ lieLattice) : collapseAssoc p ∈ lieLattice := by
  induction hp using LieSubalgebra.lieSpan_induction ℤ with
  | mem p hp =>
    obtain ⟨⟨i,a⟩,rfl⟩ := hp
    simpa [collapseAssoc] using adWord_integralLie i a
  | zero => simp
  | add p q _ _ hp hq => simpa using lieLattice.add_mem hp hq
  | smul r p _ hp => simpa only [map_zsmul] using lieLattice.smul_mem r hp
  | lie p q _ _ hp hq => simpa only [Ring.lie_def,map_sub,map_mul] using lieLattice.lie_mem hp hq

theorem words_and {P Q : List α → Prop} {p : AQ α} (hp : p ∈ words P) (hq : p ∈ words Q) :
    p ∈ words (fun w => P w ∧ Q w) := by
  apply mem_words.mpr
  intro w hw
  exact ⟨mem_words.mp hp w hw,mem_words.mp hq w hw⟩

theorem exists_support (p : AQ α) : ∃ S : Finset α, p ∈ words (fun w => ∀ b ∈ w, b ∈ S) := by
  let S := p.coeff.support.biUnion (fun w => w.toList.toFinset)
  refine ⟨S,mem_words.mpr ?_⟩
  intro w hw b hb
  exact Finset.mem_biUnion.mpr ⟨w,Finsupp.mem_support_iff.mpr hw,by simpa using hb⟩

theorem exists_bound (p : AQ α) : ∃ n : ℕ, p ∈ words (fun w => w.length≤n) := by
  refine ⟨p.coeff.support.sup (fun w => w.toList.length),mem_words.mpr ?_⟩
  intro w hw
  exact Finset.le_sup (f := fun w => w.toList.length) (Finsupp.mem_support_iff.mpr hw)

theorem bound_zero_of_lie {p : AQ α} (hl : p ∈ rationalLie)
    (hp : p ∈ words (fun w => w.length≤0)) : p=0 := by
  ext w
  change p.coeff w = 0
  by_contra h
  have h₁ := mem_words.mp (lie_positive hl) w h
  have h₂ := mem_words.mp hp w h
  omega

theorem support_empty_of_lie {p : AQ α} (hl : p ∈ rationalLie)
    (hp : p ∈ words (fun w => ∀ b ∈ w, b ∈ (∅ : Finset α))) : p=0 := by
  ext w
  change p.coeff w = 0
  by_contra h
  have h₁ := mem_words.mp (lie_positive hl) w h
  have h₂ := mem_words.mp hp w h
  cases ht : w.toList with
  | nil => simp [ht] at h₁
  | cons b v =>
    have hb := h₂ b (by simp [ht])
    simp at hb

theorem saturation_bounded (n : ℕ) : ∀ (α : Type u) (p : AQ α),
    p ∈ rationalLie → p ∈ lattice → p ∈ words (fun w => w.length≤n) → p ∈ lieLattice := by
  induction n with
  | zero =>
    intro α p hl _ hw
    rw [bound_zero_of_lie hl hw]
    exact lieLattice.zero_mem
  | succ n ih =>
    intro α p hl hi hw
    have hs : ∀ S : Finset α, ∀ p : AQ α,
        p ∈ rationalLie → p ∈ lattice →
        p ∈ words (fun w => w.length≤n+1 ∧ ∀ b ∈ w, b ∈ S) → p ∈ lieLattice := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        intro p hl _ hw
        have hz : p=0 := support_empty_of_lie hl (words_mono (fun _ h => h.2) hw)
        rw [hz]
        exact lieLattice.zero_mem
      | @insert a S ha ihS =>
        intro p hl hi hw
        have hl0 := kill_lie a hl
        have hi0 := kill_integral a hi
        have hp0 := ihS (kill a p) hl0 hi0 (kill_bound a S (n+1) hw)
        have hrl : p-kill a p ∈ rationalLie := rationalLie.sub_mem hl hl0
        have hri : p-kill a p ∈ lattice := lattice.sub_mem hi hi0
        have hrw := remainder_bound a (words_mono (fun _ h => h.1) hw)
        have htl := rename_lie (tag a) hrl
        have hti := rename_integral (tag a) hri
        have he := ih (ℕ×α) (extract (rename (tag a) (p-kill a p)))
          (extract_lie htl) (extract_integral hti) (rename_extract_lower a hrw)
        have ht : rename (tag a) (p-kill a p) ∈ lieLattice := by
          rw [decompose_lie htl]
          apply lieLattice.add_mem (collapse_integralLie he)
          obtain ⟨z,hz⟩ := trace_integral hti
          rw [hz,Int.cast_smul_eq_zsmul]
          exact lieLattice.smul_mem z (LieSubalgebra.subset_lieSpan ⟨none,rfl⟩)
        have hr := rename_lieIntegral (untag a) ht
        rw [rename_untag_tag] at hr
        convert lieLattice.add_mem hr hp0 using 1
        abel
    obtain ⟨S,hS⟩ := exists_support p
    exact hs S p hl hi (words_and hw hS)

theorem saturation {p : AQ α} (hl : p ∈ rationalLie) (hi : p ∈ lattice) : p ∈ lieLattice := by
  obtain ⟨n,hn⟩ := exists_bound p
  exact saturation_bounded n α p hl hi hn

end IntegralWords

namespace QuadraticAlphabet
open AssociativeElimination LieAlgebra
attribute [local instance] LieRing.ofAssociativeRing
abbrev F := ZMod 2
inductive Letter | a | c | b deriving DecidableEq
instance (α : Type*) : CharP (A F α) 2 :=
  charP_of_injective_ringHom (algebraMap F (A F α)).injective 2
abbrev S := A F Letter
abbrev T := A F (Option Unit)
def a : S := atom Letter.a
def c : S := atom Letter.c
def b : S := atom Letter.b
def x : T := atom none
def y : T := atom (some ())

def delta : S →ₗ[F] S := deriv (fun | .a => 0 | .c => ⁅a,b⁆ | .b => c)
@[simp] theorem delta_a : delta a=0 := by simp [delta,a]
@[simp] theorem delta_b : delta b=c := by simp [delta,b]
@[simp] theorem delta_c : delta c=⁅a,b⁆ := by simp [delta,c]
@[simp] theorem delta_one : delta 1=0 := deriv_one _
theorem delta_mul (p q : S) : delta (p*q)=delta p*q+p*delta q := deriv_mul _ _ _
theorem delta_lie (p q : S) : delta ⁅p,q⁆=⁅delta p,q⁆+⁅p,delta q⁆ := deriv_lie _ _ _

theorem delta_square_mul (p q : S) :
    delta (delta (p*q))=delta (delta p)*q+p*delta (delta q) := by
  rw [delta_mul,map_add,delta_mul,delta_mul]
  calc
    _ = delta (delta p)*q+p*delta (delta q)+(delta p*delta q+delta p*delta q) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

theorem delta_square (p : S) : delta (delta p)=⁅a,p⁆ := by
  induction p using algebra_induction with
  | h1 => simp [Ring.lie_def]
  | ha l =>
    cases l with
    | a => change delta (delta a)=⁅a,a⁆; simp
    | c => change delta (delta c)=⁅a,c⁆; simp [delta_lie]
    | b => change delta (delta b)=⁅a,b⁆; simp
  | hadd p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hm p q hp hq => rw [delta_square_mul,hp,hq]; simp [Ring.lie_def]; noncomm_ring

def left : S →ₐ[F] Module.End F (S×S) where
  toFun p :=
    { toFun := fun z => (p*z.1,p*z.2)
      map_add' := by intro z w; ext <;> simp [mul_add]
      map_smul' := by intro r z; ext <;> simp }
  map_one' := by ext z <;> simp
  map_mul' := by intro p q; ext z <;> simp [mul_assoc]
  map_zero' := by ext z <;> simp
  map_add' := by intro p q; ext z <;> simp [add_mul]
  commutes' := by intro r; ext z <;> simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem left_apply (p : S) (z : S×S) : left p z=(p*z.1,p*z.2) := rfl

def root : Module.End F (S×S) where
  toFun z := (delta z.1+z.2*a,z.1+delta z.2)
  map_add' := by intro z w; apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,map_add,add_mul] <;> abel
  map_smul' := by intro r z; ext <;> simp [smul_add]
@[simp] theorem root_apply (z : S×S) : root z=(delta z.1+z.2*a,z.1+delta z.2) := rfl

theorem root_comm (p : S) : ⁅root,left p⁆=left (delta p) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;> simp [Ring.lie_def,delta_mul,Module.End.mul_apply,mul_add,mul_assoc]

theorem root_square : root*root=left a := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;> simp only [Module.End.mul_apply,root_apply,left_apply,
    map_add,delta_mul,delta_square,delta_a,mul_zero,add_zero,Ring.lie_def,add_mul]
  · calc
      _ = a*z.1+(delta z.2*a+delta z.2*a) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]
  · calc
      _ = a*z.2+(delta z.1+delta z.1) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

def substitution : S →ₐ[F] T := lift (fun | .a => x*x | .c => ⁅x,y⁆ | .b => y)
@[simp] theorem substitution_a : substitution a=x*x := by simp [substitution,a]
@[simp] theorem substitution_c : substitution c=⁅x,y⁆ := by simp [substitution,c]
@[simp] theorem substitution_b : substitution b=y := by simp [substitution,b]

def representation : T →ₐ[F] Module.End F (S×S) :=
  lift (fun | none => root | some _ => left b)
@[simp] theorem representation_x : representation x=root := by simp [representation,x]
@[simp] theorem representation_y : representation y=left b := by simp [representation,y]

theorem representation_substitution : representation.comp substitution=left := by
  apply hom_ext
  intro l
  cases l with
  | a => change representation (substitution a)=left a; simp [root_square]
  | c =>
    change representation (substitution c)=left c
    rw [substitution_c]
    change representation (x*y-y*x)=left c
    rw [map_sub,map_mul,map_mul,representation_x,representation_y]
    change ⁅root,left b⁆=left c
    rw [root_comm,delta_b]
  | b => change representation (substitution b)=left b; simp

theorem left_injective : Function.Injective left := by
  intro p q h
  have hh := congrArg (fun f : Module.End F (S×S) => (f (1,0)).1) h
  simpa using hh

theorem substitution_injective : Function.Injective substitution := by
  intro p q h
  apply left_injective
  rw [← representation_substitution]
  exact congrArg representation h

theorem ad_square (u v : T) : ⁅u,⁅u,v⁆⁆=⁅u*u,v⁆ := by
  simp only [Ring.lie_def,sub_eq_add_neg,CharTwo.neg_eq,mul_add,add_mul,mul_assoc]
  calc
    _ = u*(u*v)+v*(u*u)+(u*(v*u)+u*(v*u)) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]

abbrev LABC := FreeLieAlgebra F Letter
def la : LABC := FreeLieAlgebra.of F Letter.a
def lc : LABC := FreeLieAlgebra.of F Letter.c
def lb : LABC := FreeLieAlgebra.of F Letter.b
def under : LABC →ₗ⁅F⁆ T := substitution.toLieHom.comp embed
@[simp] theorem under_a : under la=x*x := by simp [under,la,substitution]
@[simp] theorem under_c : under lc=⁅x,y⁆ := by simp [under,lc,substitution]
@[simp] theorem under_b : under lb=y := by simp [under,lb,substitution]

def lieDelta : LieDerivation F LABC LABC :=
  FreeDerivations.extend (fun | .a => 0 | .c => ⁅la,lb⁆ | .b => lc)
@[simp] theorem lieDelta_a : lieDelta la=0 := by simp [lieDelta,la]
@[simp] theorem lieDelta_c : lieDelta lc=⁅la,lb⁆ := by simp [lieDelta,lc]
@[simp] theorem lieDelta_b : lieDelta lb=lc := by simp [lieDelta,lb]

theorem under_delta (p : LABC) : under (lieDelta p)=⁅x,under p⁆ := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg l =>
    cases l with
    | a => change under (lieDelta la)=⁅x,under la⁆; simp [Ring.lie_def,mul_assoc]
    | c => change under (lieDelta lc)=⁅x,under lc⁆; simp [LieHom.map_lie,ad_square]
    | b => change under (lieDelta lb)=⁅x,under lb⁆; simp
  | ha p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hl p q hp hq =>
    simp only [LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,hp,hq]
    simpa only [add_comm] using (leibniz_lie x (under p) (under q)).symm

def iter (i : ℕ) : LABC := lieDelta^[i] lb
@[simp] theorem iter_zero : iter 0=lb := rfl
@[simp] theorem iter_succ (i : ℕ) : iter (i+1)=lieDelta (iter i) :=
  Function.iterate_succ_apply' _ _ _

theorem under_iter (i : ℕ) : under (iter i)=embed (Elimination.adWord i () : Elimination.G F Unit) := by
  induction i with
  | zero => simp [Elimination.Y,y]
  | succ i ih =>
    rw [iter_succ,under_delta,ih,Elimination.adWord_succ,LieHom.map_lie]
    simp [Elimination.X,x]

def fiberLift : Elimination.F F Unit →ₗ⁅F⁆ LABC :=
  FreeLieAlgebra.lift F (fun (i,_) => iter i)
theorem under_fiberLift (p : Elimination.F F Unit) :
    under (fiberLift p)=embed (Elimination.collapseFiber p) := by
  have h : under.comp fiberLift = (embed : Elimination.G F Unit →ₗ⁅F⁆ T).comp Elimination.collapseFiber := by
    apply FreeLieAlgebra.hom_ext
    rintro ⟨i,u⟩
    cases u
    simp [fiberLift,Elimination.collapseFiber,under_iter]
  exact LieHom.congr_fun h p

def polynomial (p : Elimination.G F Unit) : LABC := fiberLift (Elimination.expand p).left

theorem decompose (p : Elimination.G F Unit) :
    embed p=under (polynomial p)+(Elimination.expand p).right • x := by
  rw [polynomial,under_fiberLift]
  have hx : embed (Elimination.X : Elimination.G F Unit)=x := by simp [Elimination.X,x]
  rw [← hx,← map_smul,← map_add]
  conv_lhs => rw [← Elimination.collapse_expand p]
  rfl

theorem under_injective : Function.Injective under := by
  intro p q h
  exact UniversalEmbedding.injective (substitution_injective h)

theorem represent_unique (p : Elimination.G F Unit)
    (hp : (Elimination.expand p).right=0) : ∃! q : LABC, under q=embed p := by
  refine ⟨polynomial p,?_,?_⟩
  · simpa only [hp,zero_smul,add_zero] using (decompose p).symm
  · intro q hq
    apply under_injective
    rw [hq,decompose,hp,zero_smul,add_zero]

def homogeneous (n : ℕ) : Submodule F (Elimination.G F Unit) :=
  Submodule.span F {p | ∃ t : UniversalEmbedding.Tree (Option Unit), t.leaves.length=n ∧ t.eval=p}

theorem homogeneous_trace_zero {p : Elimination.G F Unit} {n : ℕ}
    (hn : 1<n) (hp : p∈homogeneous n) : (Elimination.expand p).right=0 := by
  have hm : ∀ t : UniversalEmbedding.Tree (Option Unit), 1<t.leaves.length →
      (Elimination.expand (t.eval : Elimination.G F Unit)).right=0 := by
    intro t ht
    cases t with
    | leaf l => simp [UniversalEmbedding.Tree.leaves] at ht
    | node t u =>
      simp [UniversalEmbedding.Tree.eval,LieHom.map_lie,Ring.lie_def,mul_comm]
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨t,ht,rfl⟩ := hp; exact hm t (ht ▸ hn)
  | zero => simp
  | add p q _ _ hp hq => simp [hp,hq]
  | smul r p _ hp => simp [hp]

theorem homogeneous_representation {p : Elimination.G F Unit} {n : ℕ}
    (hn : 1<n) (hp : p∈homogeneous n) : ∃! q : LABC, under q=embed p :=
  represent_unique p (homogeneous_trace_zero hn hp)

end QuadraticAlphabet

namespace GenericBraid
open LieAlgebra FreeDerivations
variable {R α : Type*} [CommRing R]

variable {E : Type*} [LieRing E] [LieAlgebra R E]

variable [DecidableEq α]
local notation "F" => FreeLieAlgebra R α
local notation "SD" => SemiDirectSum F (T R α) action
def fiber (i : α) : SD := SemiDirectSum.inl action (FreeLieAlgebra.of R i)
def base (i j : α) : SD := SemiDirectSum.inr action (t i j)
def chord : Option α → Option α → SD
  | none, none => 0
  | none, some j => fiber j
  | some i, none => fiber i
  | some i, some j => base i j
@[simp] theorem chord_nn : chord (R:=R) (α:=α) none none=0 := rfl
@[simp] theorem chord_ns (i : α) : chord (R:=R) none (some i)=fiber i := rfl
@[simp] theorem chord_sn (i : α) : chord (R:=R) (some i) none=fiber i := rfl
@[simp] theorem chord_ss (i j : α) : chord (R:=R) (some i) (some j)=base i j := rfl
@[simp] theorem chord_self (i : Option α) : chord (R:=R) i i=0 := by
  cases i <;> simp [base]
theorem chord_comm (i j : Option α) : chord (R:=R) i j=chord j i := by
  cases i <;> cases j <;> simp [base,t_comm]
theorem base_fiber (i j k : α) : ⁅base (R:=R) i j,fiber k⁆=
    SemiDirectSum.inl action (pair (R:=R) i j (FreeLieAlgebra.of R k)) := by
  simp [base,fiber]
theorem fiber_base (i j k : α) : ⁅fiber (R:=R) k,base i j⁆=
    -SemiDirectSum.inl action (pair (R:=R) i j (FreeLieAlgebra.of R k)) := by
  rw [← lie_skew,base_fiber]
theorem chord_disjoint (i j k l : Option α)
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅chord (R:=R) i j,chord (R:=R) k l⁆=0 := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp_all [base,fiber,t_disjoint]
  all_goals apply pair_of_other <;> intro h <;> subst_vars <;> contradiction
theorem chord_three (i j k : Option α) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ⁅chord (R:=R) i j,chord (R:=R) i k+chord (R:=R) j k⁆=0 := by
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      cases k with
      | none => exact (hik rfl).elim
      | some k =>
        rw [chord_ns,chord_ns,chord_ss,lie_add,fiber_base]
        simp [fiber]
        grind [lie_skew]
  | some i =>
    cases j with
    | none =>
      cases k with
      | none => exact (hjk rfl).elim
      | some k =>
        rw [chord_sn,chord_ss,chord_ns,lie_add,fiber_base]
        simp [fiber]
        grind [lie_skew]
    | some j =>
      cases k with
      | none =>
        rw [chord_ss,chord_sn,chord_sn,lie_add,base_fiber,base_fiber]
        simp only [pair_of_left,pair_of_right,← map_add]
        grind [lie_skew]
      | some k =>
        simp only [chord_ss,base,← map_add,← LieHom.map_lie]
        rw [t_three _ _ _ (fun h => hij (congrArg some h))
          (fun h => hik (congrArg some h)) (fun h => hjk (congrArg some h)),map_zero]
def toSemidirect : T R (Option α) →ₗ⁅R⁆ SD :=
  lift chord chord_self chord_comm chord_disjoint chord_three
@[simp] theorem toSemidirect_t (i j : Option α) : toSemidirect (t (R:=R) i j)=chord i j := by
  simp [toSemidirect]
end GenericBraid

namespace GenericBraid
open LieAlgebra AssociativeElimination
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R] [DecidableEq α]

omit [DecidableEq α] in
theorem hom_ext {E : Type*} [LieRing E] [LieAlgebra R E]
    {f g : T R α →ₗ⁅R⁆ E} (h : ∀ i j, f (t i j)=g (t i j)) : f=g := by
  let q : Free R α →ₗ⁅R⁆ T R α :=
    { (ideal (R:=R) (α:=α)).mkQ with map_lie' := by intros; rfl }
  have hh : f.comp q=g.comp q := by
    apply FreeLieAlgebra.hom_ext
    rintro ⟨i,j⟩
    exact h i j
  apply LieHom.ext
  intro a
  induction a using Submodule.Quotient.induction_on with | _ a =>
    exact LieHom.congr_fun hh a

end GenericBraid

namespace GenericBraid
open LieAlgebra FreeDerivations
variable {R α : Type*} [CommRing R]

theorem induction {P : T R α → Prop} (h0 : P 0) (ht : ∀ i j,P (t i j))
    (ha : ∀ p q,P p → P q → P (p+q)) (hs : ∀ (r : R) p,P p → P (r • p))
    (hl : ∀ p q,P p → P q → P ⁅p,q⁆) (p : T R α) : P p := by
  induction p using Submodule.Quotient.induction_on with | _ p =>
    induction p using freeLie_induction with
    | h0 => exact h0
    | hg ij => exact ht ij.1 ij.2
    | ha p q hp hq => exact ha _ _ hp hq
    | hs r p hp => exact hs r _ hp
    | hl p q hp hq => exact hl _ _ hp hq

variable [DecidableEq α]
def fiberLie : FreeLieAlgebra R α →ₗ⁅R⁆ T R (Option α) :=
  FreeLieAlgebra.lift R (fun i => t none (some i))
omit [DecidableEq α] in
@[simp] theorem fiberLie_of (i : α) : fiberLie (FreeLieAlgebra.of R i)=t none (some i) := by
  simp [fiberLie]

theorem t_base_fiber_left (i j : α) :
    ⁅t (R:=R) (some i) (some j),t (R:=R) none (some i)⁆=⁅t (R:=R) none (some i),t (R:=R) none (some j)⁆ := by
  by_cases hij : i=j
  · subst j; simp
  have h := t_three (R:=R) (none : Option α) (some i) (some j) (by simp) (by simp)
    (fun h => hij (Option.some.inj h))
  rw [lie_add] at h
  grind [lie_skew]

theorem compatibility (g : T R α) (p : FreeLieAlgebra R α) :
    fiberLie (action g p)=⁅baseLie g,fiberLie p⁆ := by
  induction g using induction generalizing p with
  | h0 => simp
  | ht i j =>
    rw [action_t,baseLie_t]
    induction p using freeLie_induction with
    | h0 => simp
    | hg k =>
      by_cases hki : k=i
      · subst k; simp only [pair_of_left,LieHom.map_lie,fiberLie_of]; exact (t_base_fiber_left i j).symm
      by_cases hkj : k=j
      · subst k
        simp only [pair_of_right,LieHom.map_lie,fiberLie_of]
        rw [t_comm (some i) (some j)]
        exact (t_base_fiber_left j i).symm
      simp only [pair_of_other i j k hki hkj,map_zero,fiberLie_of]
      exact (t_disjoint _ _ _ _ (by simp) (fun h => hki (Option.some.inj h).symm)
        (by simp) (fun h => hkj (Option.some.inj h).symm)).symm
    | ha p q hp hq => simp [hp,hq,lie_add]
    | hs r p hp => simp [hp]
    | hl p q hp hq =>
      simp only [LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,hp,hq]
      simpa only [add_comm] using (leibniz_lie (t (R:=R) (some i) (some j)) (fiberLie p) (fiberLie q)).symm
  | ha g h hg hh => simp [hg,hh,add_lie]
  | hs r g hg => simp [hg]
  | hl g h hg hh =>
    simp only [LieHom.map_lie,LieDerivation.lie_apply,map_sub,hg,hh]
    exact (lie_lie _ _ _).symm

def fromSemidirect : SemiDirectSum (FreeLieAlgebra R α) (T R α) action →ₗ⁅R⁆ T R (Option α) :=
  InnerSemiDirect.lift action fiberLie baseLie compatibility

theorem toSemidirect_fiberLie (p : FreeLieAlgebra R α) :
    toSemidirect (fiberLie p)=SemiDirectSum.inl action p := by
  have h : (toSemidirect (R:=R) (α:=α)).comp fiberLie=SemiDirectSum.inl action := by
    apply FreeLieAlgebra.hom_ext
    intro i
    simp [fiber]
  exact LieHom.congr_fun h p

theorem toSemidirect_baseLie (p : T R α) :
    toSemidirect (baseLie p)=SemiDirectSum.inr action p := by
  have h : (toSemidirect (R:=R) (α:=α)).comp baseLie=SemiDirectSum.inr action := by
    apply hom_ext
    intro i j
    simp [base]
  exact LieHom.congr_fun h p

theorem from_to (p : T R (Option α)) : fromSemidirect (toSemidirect p)=p := by
  have h : (fromSemidirect (R:=R) (α:=α)).comp toSemidirect=LieHom.id := by
    apply hom_ext
    intro i j
    cases i <;> cases j <;> simp [fromSemidirect,InnerSemiDirect.lift,fiber,base,t_comm]
  exact LieHom.congr_fun h p

end GenericBraid

attribute [local instance 2000] FreeLieAlgebra.instLieAlgebra

namespace IntegralBaseChange
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {S α : Type*} [CommRing S]
def words : A ℤ α →+* A S α := MonoidAlgebra.mapRingHom _ (Int.castRingHom S)
@[simp] theorem words_atom (a : α) : words (atom a : A ℤ α)=(atom a : A S α) := by
  simp [words,atom]
@[simp] theorem words_coeff (p : A ℤ α) (w : FreeMonoid α) :
    (words p : A S α).coeff w=(p.coeff w : S) := by simp [words]
def lie : FreeLieAlgebra ℤ α →ₗ⁅ℤ⁆ FreeLieAlgebra S α :=
  FreeLieAlgebra.lift ℤ (FreeLieAlgebra.of S)
@[simp] theorem lie_of (a : α) : lie (FreeLieAlgebra.of ℤ a)=FreeLieAlgebra.of S a := by exact FreeLieAlgebra.lift_of_apply (FreeLieAlgebra.of S) a
theorem embed_lie (p : FreeLieAlgebra ℤ α) :
    embed (lie p : FreeLieAlgebra S α)=words (embed p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq,Ring.lie_def,map_sub,map_mul]
theorem words_rational_injective : Function.Injective (words (S:=ℚ) (α:=α)) := by
  intro p q h
  ext w
  have hc := congrArg (fun z : A ℚ α => z.coeff w) h
  simpa using hc

theorem lie_rational_injective : Function.Injective (lie (S:=ℚ) (α:=α)) := by
  intro p q h
  apply UniversalEmbedding.injective
  apply words_rational_injective
  rw [← embed_lie,← embed_lie,h]

theorem lift_integral {p : FreeLieAlgebra ℚ α} (hp : embed p∈IntegralWords.lattice) :
    ∃ q : FreeLieAlgebra ℤ α,lie q=p := by
  have hr : embed p∈IntegralWords.rationalLie := by
    clear hp
    induction p using freeLie_induction with
    | h0 => simp
    | hg a => exact LieSubalgebra.subset_lieSpan ⟨a,by simp⟩
    | ha p q hp hq => simpa using IntegralWords.rationalLie.add_mem hp hq
    | hs r p hp => simpa using IntegralWords.rationalLie.smul_mem r hp
    | hl p q hp hq => simpa only [LieHom.map_lie] using IntegralWords.rationalLie.lie_mem hp hq
  have hi := IntegralWords.saturation hr hp
  let f : FreeLieAlgebra ℤ α →ₗ⁅ℤ⁆ A ℚ α := FreeLieAlgebra.lift ℤ atom
  have he (q : FreeLieAlgebra ℤ α) : f q=embed (lie q : FreeLieAlgebra ℚ α) := by
    induction q using freeLie_induction with
    | h0 => simp
    | hg a => rw [lie_of,embed_of]; exact FreeLieAlgebra.lift_of_apply atom a
    | ha p q hp hq => simp [hp,hq]
    | hs r p hp => simp [map_smul,hp]
    | hl p q hp hq => simp [hp,hq]
  have hspan : IntegralWords.lieLattice ≤ f.range := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro a ⟨a,rfl⟩
    exact ⟨FreeLieAlgebra.of ℤ a,FreeLieAlgebra.lift_of_apply atom a⟩
  obtain ⟨q,hq⟩ := hspan hi
  refine ⟨q, UniversalEmbedding.injective ?_⟩
  rw [← he]
  exact hq
end IntegralBaseChange

namespace GenericBraid

section
variable {S α β : Type*} [CommRing S]
def cast : T ℤ α →ₗ⁅ℤ⁆ T S α :=
  lift (t (R:=S)) t_self t_comm t_disjoint t_three
@[simp] theorem cast_t (i j : α) : cast (t (R:=ℤ) i j)=t (R:=S) i j := by simp [cast]
def rename {R : Type*} [CommRing R] (e : α ≃ β) : T R α →ₗ⁅R⁆ T R β :=
  lift (fun i j => t (e i) (e j)) (fun i => t_self (e i)) (fun i j => t_comm (e i) (e j))
    (fun i j k l hik hil hjk hjl => t_disjoint (e i) (e j) (e k) (e l)
      (e.injective.ne hik) (e.injective.ne hil) (e.injective.ne hjk) (e.injective.ne hjl))
    (fun i j k hij hik hjk => t_three (e i) (e j) (e k) (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hjk))
@[simp] theorem rename_t {R : Type*} [CommRing R] (e : α ≃ β) (i j : α) :
    rename e (t (R:=R) i j)=t (e i) (e j) := by simp [rename]
theorem rename_symm {R : Type*} [CommRing R] (e : α ≃ β) (p : T R α) :
    rename e.symm (rename e p)=p := by
  induction p using induction with
  | h0 => simp
  | ht i j => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
theorem rename_injective {R : Type*} [CommRing R] (e : α ≃ β) :
    Function.Injective (rename (R:=R) e) := Function.LeftInverse.injective (rename_symm e)
theorem cast_rename (e : α ≃ β) (p : T ℤ α) :
    cast (S:=S) (rename e p)=rename e (cast p) := by
  induction p using induction with
  | h0 => simp
  | ht i j => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
variable [DecidableEq α]
omit [DecidableEq α] in
theorem cast_fiber (p : FreeLieAlgebra ℤ α) :
    cast (S:=S) (fiberLie p)=fiberLie (IntegralBaseChange.lie p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
omit [DecidableEq α] in
theorem cast_base (p : T ℤ α) : cast (S:=S) (baseLie p)=baseLie (cast p) := by
  induction p using induction with
  | h0 => simp
  | ht i j => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
theorem cast_option_injective (h : Function.Injective (cast (S:=ℚ) (α:=α))) :
    Function.Injective (cast (S:=ℚ) (α:=Option α)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  have hd : p=fiberLie (toSemidirect p).left+baseLie (toSemidirect p).right := (from_to p).symm
  rw [hd,map_add,cast_fiber,cast_base] at hp
  have he := congrArg (toSemidirect (R:=ℚ) (α:=α)) hp
  rw [map_add,toSemidirect_fiberLie,toSemidirect_baseLie,map_zero] at he
  have hl := congrArg LieAlgebra.SemiDirectSum.left he
  have hr := congrArg LieAlgebra.SemiDirectSum.right he
  simp only [LieAlgebra.SemiDirectSum.add_eq_mk,LieAlgebra.SemiDirectSum.inl_eq_mk,
    LieAlgebra.SemiDirectSum.inr_eq_mk,add_zero,zero_add,LieAlgebra.SemiDirectSum.zero_eq_mk] at hl hr
  have hl0 : (toSemidirect p).left=0 := IntegralBaseChange.lie_rational_injective (hl.trans (map_zero _).symm)
  have hr0 : (toSemidirect p).right=0 := h (hr.trans (map_zero _).symm)
  rw [hd,hl0,hr0,map_zero,map_zero,add_zero]
end

variable {α : Type*}
theorem cast_fin_injective (n : ℕ) : Function.Injective (cast (S:=ℚ) (α:=Fin n)) := by
  induction n with
  | zero =>
    have hz (p : T ℤ (Fin 0)) : p=0 := by
      induction p using induction with
      | h0 => rfl
      | ht i j => exact Fin.elim0 i
      | ha p q hp hq => simp [hp,hq]
      | hs r p hp => simp [hp]
      | hl p q hp hq => simp [hp,hq]
    intro p q _
    rw [hz p,hz q]
  | succ n ih =>
    intro p q h
    apply rename_injective (finSuccEquiv' (0 : Fin (n+1)))
    apply cast_option_injective ih
    rw [cast_rename,cast_rename,h]

def fromT4 : T4 →ₗ⁅ℚ⁆ T ℚ (Fin 4) :=
  T4Universal.lift (t (R:=ℚ)) t_comm t_self
    (fun i j k l _ hik hil hjk hjl _ => t_disjoint i j k l hik hil hjk hjl) t_three
@[simp] theorem fromT4_t (i j : Fin 4) : fromT4 (DeligneDrinfeld.t i j)=t i j := by
  simp [fromT4]
end GenericBraid

namespace BaseChangeEquations
variable {R : Type*} [CommRing R]
def threeTerm (q : FreeLieAlgebra R Bool) := q+eval y (-x-y) q+eval (-x-y) x q

def Equations (q : FreeLieAlgebra R Bool) : Prop :=
  antisymmetry q=0 ∧ threeTerm q=0 ∧ pentagon q=0

theorem pentagon_rational {q : L} (hq : q∈W) : pentagon q=0 := by
  have h := congrArg GenericBraid.fromT4 hq.2.2
  have he (a b : T4) : GenericBraid.fromT4 (DeligneDrinfeld.eval a b q)=
      eval (GenericBraid.fromT4 a) (GenericBraid.fromT4 b) q := by
    have hm : GenericBraid.fromT4.comp (DeligneDrinfeld.eval a b)=
        eval (GenericBraid.fromT4 a) (GenericBraid.fromT4 b) := by
      apply FreeLieAlgebra.hom_ext
      intro i
      cases i <;> simp [eval,DeligneDrinfeld.eval]
    exact LieHom.congr_fun hm q
  simp only [map_add,he,GenericBraid.fromT4_t] at h
  change _ - _ - _ - _ = 0
  rw [h]
  abel

theorem rational {q : L} (hq : q∈W) : Equations q :=
  ⟨hq.1,hq.2.1,pentagon_rational hq⟩

variable {S : Type*} [CommRing S]
theorem cast_eval_lie (a b q : FreeLieAlgebra ℤ Bool) :
    IntegralBaseChange.lie (S:=S) (eval a b q)=
      eval (R:=S) (IntegralBaseChange.lie a) (IntegralBaseChange.lie b) (IntegralBaseChange.lie q) := by
  induction q using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp =>
    rw [map_smul,map_smul]
    simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
theorem cast_eval_braid (a b : GenericBraid.T ℤ (Fin 4)) (q : FreeLieAlgebra ℤ Bool) :
    GenericBraid.cast (S:=S) (eval a b q)=
      eval (R:=S) (GenericBraid.cast a) (GenericBraid.cast b) (IntegralBaseChange.lie q) := by
  induction q using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]
@[simp] theorem cast_x : IntegralBaseChange.lie (x : FreeLieAlgebra ℤ Bool)=(x : FreeLieAlgebra S Bool) := by simp [x]
@[simp] theorem cast_y : IntegralBaseChange.lie (y : FreeLieAlgebra ℤ Bool)=(y : FreeLieAlgebra S Bool) := by simp [y]
theorem cast_antisymmetry (q : FreeLieAlgebra ℤ Bool) :
    IntegralBaseChange.lie (S:=S) (antisymmetry q)=antisymmetry (IntegralBaseChange.lie q) := by
  simp [antisymmetry,cast_eval_lie]
theorem cast_threeTerm (q : FreeLieAlgebra ℤ Bool) :
    IntegralBaseChange.lie (S:=S) (threeTerm q)=threeTerm (IntegralBaseChange.lie q) := by
  simp [threeTerm,cast_eval_lie]
theorem cast_pentagon (q : FreeLieAlgebra ℤ Bool) :
    GenericBraid.cast (S:=S) (pentagon q)=pentagon (IntegralBaseChange.lie q) := by
  simp only [pentagon,map_sub,map_add,cast_eval_braid,GenericBraid.cast_t]

theorem integral_of_rational (q : FreeLieAlgebra ℤ Bool)
    (hq : (IntegralBaseChange.lie q : L)∈W) : Equations q := by
  have h := rational hq
  refine ⟨IntegralBaseChange.lie_rational_injective ?_,IntegralBaseChange.lie_rational_injective ?_,
    GenericBraid.cast_fin_injective 4 ?_⟩
  · rw [cast_antisymmetry,h.1,map_zero]
  · rw [cast_threeTerm,h.2.1,map_zero]
  · rw [cast_pentagon,h.2.2,map_zero]

theorem reduce (q : FreeLieAlgebra ℤ Bool)
    (hq : (IntegralBaseChange.lie q : L)∈W) : Equations (IntegralBaseChange.lie (S:=S) q) := by
  have h := integral_of_rational q hq
  refine ⟨?_,?_,?_⟩
  · rw [← cast_antisymmetry,h.1,map_zero]
  · rw [← cast_threeTerm,h.2.1,map_zero]
  · rw [← cast_pentagon,h.2.2,map_zero]
end BaseChangeEquations

namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]
theorem mem_space_iff {P : FreeMonoid α → Prop} {p : A R α} :
    p∈space P ↔ ∀ w,p.coeff w≠0 → P w := by
  constructor
  · intro hp w hw
    by_contra h
    exact hw (coeff_support hp w h)
  · exact mem_space

theorem deriv_homogeneous {wt : α → ℕ} {c : ℕ} {f : α → A R α}
    (hf : ∀ a,f a∈homogeneous wt (wt a+c)) {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : deriv f p∈homogeneous wt (n+c) := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈homogeneous wt (degree wt w+c) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      have h1 := homogeneous_mul (hf a) (word_mem (R:=R) w rfl : word w∈homogeneous wt (degree wt w))
      have h2 := homogeneous_mul (word_mem (R:=R) (FreeMonoid.of a) (degree_of wt a) : atom a∈homogeneous wt (wt a)) ih
      simp only [degree_mul,degree_of]
      apply (homogeneous wt (wt a+degree wt w+c)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [word_of,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2
  exact map_space (deriv f) _ (by intro w hw'; simpa only [hw'] using hw w) hp

theorem homogeneous_above {wt : α → ℕ} {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : p∈above wt n := space_mono (by intros; omega) hp

theorem deriv_above {wt : α → ℕ} {c : ℕ} {f : α → A R α}
    (hf : ∀ a,f a∈above wt (wt a+c)) {n : ℕ} {p : A R α}
    (hp : p∈above wt n) : deriv f p∈above wt (n+c) := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈above wt (degree wt w+c) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      have h1 := above_mul (hf a) (homogeneous_above (word_mem (R:=R) w rfl : word w∈homogeneous wt (degree wt w)))
      have h2 := above_mul (homogeneous_above (word_mem (R:=R) (FreeMonoid.of a) (degree_of wt a) : atom a∈homogeneous wt (wt a))) ih
      simp only [degree_mul,degree_of]
      apply (above wt (wt a+degree wt w+c)).add_mem
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
      · simpa only [word_of,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2
  apply map_space (deriv f) _ ?_ hp
  intro w hn
  exact space_mono (by intro v hv; omega) (hw w)

end WordGrading

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld
namespace WordGrading
open AssociativeElimination
variable {R α β : Type*} [CommRing R]
variable (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)

theorem algHom_homogeneous (hf : ∀ a,f (atom a)∈homogeneous wb (wa a))
    {n : ℕ} {p : A R α} (hp : p∈homogeneous wa n) : f p∈homogeneous wb n := by
  have hw (w : FreeMonoid α) : f (word w)∈homogeneous wb (degree wa w) := by
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one,map_one,degree_one]
      exact word_mem (1 : FreeMonoid β) (degree_one wb)
    | of_mul a w ih =>
      simp only [word_mul,word_of,map_mul,degree_mul,degree_of]
      exact homogeneous_mul (hf a) ih
  apply map_space f.toLinearMap _ ?_ hp
  intro w h
  change f (word w)∈homogeneous wb n
  rw [← h]
  exact hw w

end WordGrading

namespace RowKernel
open AssociativeElimination WordGrading WeightedDeletion RowTwo
open RowTwo.Letter RowTwo.Slot

def aCount (a : Slot) : ℕ := if a=.A then 1 else 0
def cCount (a : Slot) : ℕ := if a=.C then 1 else 0

def acCount (k : Slot) : ℕ := aCount k+cCount k

end RowKernel

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section
namespace WordGrading
open AssociativeElimination
variable {R α β : Type*} [CommRing R]

theorem piece_mem (wt : α → ℕ) (n : ℕ) (p : A R α) : piece wt n p∈homogeneous wt n :=
  project_mem _ p

theorem piece_eq_self_iff (wt : α → ℕ) (n : ℕ) (p : A R α) :
    piece wt n p=p ↔ p∈homogeneous wt n := by
  constructor
  · intro h; rw [← h]; exact piece_mem wt n p
  · exact project_eq_self

theorem project_degree_homogeneous (wt : α → ℕ) (P : ℕ → Prop) [DecidablePred P]
    {k : ℕ} {p : A R α} (hp : p∈homogeneous wt k) :
    project (fun w => P (degree wt w)) p=if P k then p else 0 := by
  by_cases h : P k
  · rw [if_pos h]
    exact project_eq_self (space_mono (by intro w hw; exact hw ▸ h) hp)
  · rw [if_neg h]
    exact project_eq_zero hp (by intro w hw; simpa only [hw] using h)

theorem algHom_project (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈homogeneous wb (wa a)) (P : ℕ → Prop) [DecidablePred P]
    (p : A R α) :
    f (project (fun w => P (degree wa w)) p)=project (fun w => P (degree wb w)) (f p) := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change f (project _ (word w))=project _ (f (word w))
    rw [project_word,project_degree_homogeneous wb P
      (algHom_homogeneous f wa wb hf (word_mem w rfl))]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]

theorem algHom_piece (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈homogeneous wb (wa a)) (n : ℕ) (p : A R α) :
    f (piece wa n p)=piece wb n (f p) := algHom_project f wa wb hf (fun k => k=n) p

theorem homogeneous_reflect (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈homogeneous wb (wa a)) (hi : Function.Injective f)
    {n : ℕ} {p : A R α} (hp : f p∈homogeneous wb n) : p∈homogeneous wa n := by
  apply (piece_eq_self_iff wa n p).mp
  apply hi
  rw [algHom_piece f wa wb hf,piece_homogeneous hp,if_pos rfl]

theorem project_preserves {P Q : FreeMonoid α → Prop} [DecidablePred Q]
    {p : A R α} (hp : p∈space P) : project Q p∈space P := by
  apply mem_space
  intro w hw
  rw [project_coeff] at hw
  split_ifs at hw with h
  · exact (mem_space_iff.mp hp) w hw
  · exact (hw rfl).elim

theorem subtract_piece_above {wt : α → ℕ} {n : ℕ} {p : A R α}
    (hp : p∈above wt n) : p-piece wt n p∈above wt (n+1) := by
  apply mem_space
  intro w hw
  change (p-piece wt n p).coeff w≠0 at hw
  simp only [MonoidAlgebra.coeff_sub,Finsupp.sub_apply] at hw
  change p.coeff w-(project (fun w => degree wt w=n) p).coeff w≠0 at hw
  rw [project_coeff] at hw
  have hn : n≤degree wt w := by
    by_contra h
    have hz := coeff_support hp w h
    simp [hz] at hw
  by_cases he : degree wt w=n
  · simp [he] at hw
  · omega
end WordGrading

namespace LieGrading
open AssociativeElimination UniversalEmbedding WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]

theorem homogeneous_iff {wt : α → ℕ} {n : ℕ} {p : FreeLieAlgebra R α} :
    p∈homogeneousLie wt n ↔ embed p∈homogeneous wt n := by
  constructor
  · exact homogeneousLie_embed
  · intro hp
    have h : piece wt n p=p := by
      apply UniversalEmbedding.injective
      rw [embed_piece]
      exact WordGrading.project_eq_self hp
    rw [← h]
    exact (piece_spec wt n p).1

end LieGrading
end

namespace WordCoordinates
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]

variable (P : FreeMonoid α → Prop) [Fintype {w // P w}]

variable {P}

theorem length_le_degree (wt : α → ℕ) (hpos : ∀ a,0<wt a) (w : FreeMonoid α) :
    w.toList.length≤degree wt w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [degree]
  | of_mul a w ih =>
    rw [degree_mul,degree_of]
    change w.toList.length+1≤wt a+degree wt w
    have := hpos a
    omega

theorem letter_le_degree (wt : α → ℕ) (w : FreeMonoid α) {a : α} (ha : a∈w.toList) :
    wt a≤degree wt w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp at ha
  | of_mul b w ih =>
    rw [degree_mul,degree_of]
    rcases List.mem_cons.mp ha with h | h
    · subst a; omega
    · have := ih h; omega

theorem finite_degree (wt : α → ℕ) (hpos : ∀ a,0<wt a) (n : ℕ)
    (hf : {a | wt a≤n}.Finite) : {w | degree wt w=n}.Finite := by
  classical
  let : Finite {a // wt a≤n} := hf.to_subtype
  apply Set.Finite.subset ((List.finite_length_le {a // wt a≤n} n).image
    (fun l => FreeMonoid.ofList (l.map Subtype.val)))
  intro w hw
  let l : List {a // wt a≤n} := w.toList.attach.map (fun a => ⟨a.val,(letter_le_degree wt w a.property).trans_eq hw⟩)
  refine ⟨l,?_,?_⟩
  · simpa [l] using (length_le_degree wt hpos w).trans_eq hw
  · simp [l,List.map_map]

theorem finite_degree_finite_alphabet [Finite α] (wt : α → ℕ) (hpos : ∀ a,0<wt a) (n : ℕ) :
    {w | degree wt w=n}.Finite := finite_degree wt hpos n (Set.toFinite _)

end WordCoordinates

end DeligneDrinfeld

end

end OAI

end


section

namespace OAI

noncomputable section

namespace DeligneDrinfeld
namespace AlphabetTransport
open AssociativeElimination UniversalEmbedding
variable {R α β γ : Type*} [CommRing R]

theorem assoc_retract (f : α → β) (g : β → α) (h : Function.LeftInverse g f) (p : A R α) :
    renameAssoc g (renameAssoc f p)=p := by
  have he : (renameAssoc (R:=R) g).comp (renameAssoc f)=AlgHom.id R (A R α) := by
    apply hom_ext
    intro a
    simp [h a]
  exact AlgHom.congr_fun he p

theorem assoc_injective (f : α → β) (g : β → α) (h : Function.LeftInverse g f) :
    Function.Injective (renameAssoc (R:=R) f) := by
  intro p q hp
  simpa only [assoc_retract f g h] using congrArg (renameAssoc g) hp

end AlphabetTransport
namespace QuadraticLeading
open AssociativeElimination UniversalEmbedding WordGrading AlphabetTransport
open RowTwo RowKernel ExactPentagon
attribute [local instance] LieRing.ofAssociativeRing

def letters : Slot ≃ QuadraticAlphabet.Letter where
  toFun := fun | .A => .a | .C => .c | .B => .b
  invFun := fun | .a => .A | .c => .C | .b => .B
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

theorem quad_transport : (renameAssoc bitOption).comp quad=
    QuadraticAlphabet.substitution.comp (renameAssoc letters) := by
  apply hom_ext
  intro k
  cases k <;> simp [quad,letters,bitOption,QuadraticAlphabet.substitution,
    QuadraticAlphabet.x,QuadraticAlphabet.y,Ring.lie_def]

theorem quad_transport_inv : (renameAssoc bitOption.symm).comp QuadraticAlphabet.substitution=
    quad.comp (renameAssoc letters.symm) := by
  apply hom_ext
  intro k
  cases k <;> simp [quad,letters,bitOption,QuadraticAlphabet.substitution,
    QuadraticAlphabet.x,QuadraticAlphabet.y,Ring.lie_def]

theorem quad_injective : Function.Injective quad := by
  intro p q hp
  apply assoc_injective letters letters.symm letters.left_inv
  apply QuadraticAlphabet.substitution_injective
  have h := congrArg (renameAssoc bitOption) hp
  exact (AlgHom.congr_fun quad_transport p).symm.trans (h.trans (AlgHom.congr_fun quad_transport q))

theorem under_injective : Function.Injective under := by
  intro p q h
  exact UniversalEmbedding.injective (quad_injective h)

theorem tree_degree_length {α : Type*} (t : UniversalEmbedding.Tree α) :
    LieGrading.treeDegree (fun _ : α => 1) t=t.leaves.length := by
  simp [LieGrading.treeDegree]

theorem representation {ψ : FreeLieAlgebra K Bool} {n : ℕ} (hn : 1<n)
    (hψ : embed ψ∈homogeneous (fun _ => 1) n) :
    ∃! p : FreeLieAlgebra K Slot,under p=embed ψ := by
  have ho : embed (rename bitOption ψ)∈homogeneous (fun _ => 1) n := by
    rw [rename_embed]
    apply algHom_homogeneous (renameAssoc bitOption) (fun _ => 1) (fun _ => 1) ?_ hψ
    intro a
    rw [renameAssoc_atom]
    exact word_mem (FreeMonoid.of (bitOption a)) (degree_of _ _)
  have hl : rename bitOption ψ∈QuadraticAlphabet.homogeneous n := by
    have h := LieGrading.homogeneous_iff.mpr ho
    apply (show (LieGrading.homogeneousLie (fun _ : Option Unit => 1) n :
        Submodule K (FreeLieAlgebra K (Option Unit))) ≤ QuadraticAlphabet.homogeneous n from ?_) h
    apply Submodule.span_le.mpr
    rintro p ⟨t,ht,rfl⟩
    exact Submodule.subset_span ⟨t,(tree_degree_length t) ▸ ht,rfl⟩
  obtain ⟨p,hp,_⟩ := QuadraticAlphabet.homogeneous_representation hn hl
  refine ⟨rename letters.symm p,?_,fun q hq => under_injective (hq.trans ?_)⟩
  · change quad (embed (rename letters.symm p))=embed ψ
    rw [rename_embed]
    rw [← AlgHom.comp_apply,← quad_transport_inv,AlgHom.comp_apply]
    change renameAssoc bitOption.symm (QuadraticAlphabet.under p)=embed ψ
    rw [hp,rename_embed,assoc_retract bitOption bitOption.symm bitOption.left_inv]
  · change embed ψ=quad (embed (rename letters.symm p))
    rw [rename_embed,← AlgHom.comp_apply,← quad_transport_inv,AlgHom.comp_apply]
    change embed ψ=renameAssoc bitOption.symm (QuadraticAlphabet.under p)
    rw [hp,rename_embed,assoc_retract bitOption bitOption.symm bitOption.left_inv]

theorem quad_homogeneous (a : Slot) : quad (atom a)∈homogeneous (fun _ => 1) (weight a) := by
  have hx : (atom false : A K Bool)∈homogeneous (fun _ => 1) 1 := word_mem _ rfl
  have hy : (atom true : A K Bool)∈homogeneous (fun _ => 1) 1 := word_mem _ rfl
  cases a with
  | A =>
    rw [quad,lift_atom]
    have h := homogeneous_mul hx hx
    exact h
  | C =>
    rw [quad,lift_atom]
    have h1 := homogeneous_mul hx hy
    have h2 := homogeneous_mul hy hx
    exact (homogeneous _ 2).sub_mem h1 h2
  | B => simpa only [quad,lift_atom,weight] using hy

theorem representation_weight {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n : ℕ}
    (hψ : embed ψ∈homogeneous (fun _ => 1) n) (hp : under p=embed ψ) :
    embed p∈homogeneous weight n := by
  apply homogeneous_reflect quad weight (fun _ => 1) quad_homogeneous quad_injective
  change under p∈_
  rw [hp]
  exact hψ

theorem weight_count (w : FreeMonoid Slot) : degree weight w=2*degree acCount w+degree bCount w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    simp only [degree_mul,degree_of,ih]
    cases a <;> simp [weight,acCount,bCount,aCount,cCount] <;> omega

end QuadraticLeading

namespace BaseChangeEquations
open AssociativeEvaluation
variable {R S : Type*} [CommRing R] [CommRing S]

theorem cast_special (q : FreeLieAlgebra ℤ Bool) :
    IntegralBaseChange.lie (S:=S) (special q)=special (IntegralBaseChange.lie q) := by
  simp only [special,map_add,LieHom.map_lie,cast_eval_lie,map_sub,map_neg,cast_x,cast_y]

theorem reduce_special (q : FreeLieAlgebra ℤ Bool) {n : ℕ}
    (hq : (IntegralBaseChange.lie q : L)∈W)
    (hw : (IntegralBaseChange.lie q : L)∈Ln n) (hn : 2<n) :
    special (IntegralBaseChange.lie (S:=S) q)=0 := by
  have hi : special q=0 := by
    apply IntegralBaseChange.lie_rational_injective
    rw [cast_special,map_zero]
    exact Differentiation.special_identity hq hw hn DeligneDrinfeld.x DeligneDrinfeld.y
  rw [← cast_special,hi,map_zero]

end BaseChangeEquations

namespace EliminationGraded
open AssociativeElimination UniversalEmbedding WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]

theorem operator_collapse (p : A R (ℕ×α)) : operator (collapse p)=leftMul p := by
  have h : operator.comp collapse=(leftMul : A R (ℕ×α) →ₐ[R] Module.End R (A R (ℕ×α))) := by
    apply hom_ext
    rintro ⟨n,a⟩
    simp only [AlgHom.comp_apply,collapse_atom,operator_embed,Elimination.expand_adWord,representation_inl]
    simp [Elimination.E]
  exact AlgHom.congr_fun h p

theorem extract_collapse (p : A R (ℕ×α)) : extract (collapse p)=p := by
  change operator (collapse p) 1=p
  rw [operator_collapse,leftMul_apply,mul_one]

theorem collapse_injective : Function.Injective (collapse : A R (ℕ×α) →ₐ[R] A R (Option α)) :=
  Function.LeftInverse.injective extract_collapse

end EliminationGraded

namespace OreShift

section
open AssociativeElimination WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]
local instance {α : Type*} [CharP R 2] : CharP (A R α) 2 :=
  charP_of_injective_ringHom (show Function.Injective (algebraMap R (A R α)) from by
    intro r s h
    have hc := congrArg (fun p : A R α => p.coeff 1) h
    simpa using hc) 2
abbrev S (R : Type*) [CommRing R] := A R Bool

def C : S R := atom false
def B : S R := atom true

def P (s : S R) : ℕ → S R
  | 0 => C
  | n+1 => ⁅B+s,P s n⁆

@[simp] theorem P_zero (s : S R) : P s 0=C := rfl
@[simp] theorem P_succ (s : S R) (n : ℕ) : P s (n+1)=⁅B+s,P s n⁆ := rfl

variable {s : S R}

end

open AssociativeElimination WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]

variable {s : S R} [CharP R 2]

end OreShift

namespace OreShift

section
open AssociativeElimination WordGrading
open QuadraticLeading RowTwo RowKernel AlphabetTransport ProjectionKernel ExactPentagon
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]
local instance {α : Type*} [CharP R 2] : CharP (A R α) 2 :=
  charP_of_injective_ringHom (show Function.Injective (algebraMap R (A R α)) from by
    intro r s h
    have hc := congrArg (fun p : A R α => p.coeff 1) h
    simpa using hc) 2

def eraseShift (s : S R) : A R Slot →ₐ[R] S R :=
  lift (fun | .A => 0 | .C => C | .B => B+s)

end

open AssociativeElimination WordGrading UniversalEmbedding
open QuadraticLeading RowTwo RowKernel ExactPentagon ProjectionKernel
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]

end OreShift

namespace GeneratorDeletion

section
open AssociativeElimination WordGrading UniversalEmbedding AlphabetTransport PositionalDeletion QuadraticLeading
attribute [local instance] LieRing.ofAssociativeRing

theorem input_injective : Function.Injective EvenIndex.input :=
  (assoc_injective bitOption.symm bitOption bitOption.right_inv).comp EliminationGraded.collapse_injective

end

open AssociativeElimination WordGrading UniversalEmbedding
attribute [local instance] LieRing.ofAssociativeRing

def cutAssoc : Q →ₐ[K] A K ℕ := lift (fun a => match a.1 with | 0 => 0 | n+1 => atom n)

end GeneratorDeletion

namespace ImageBound

section
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon AlphabetTransport
attribute [local instance] LieRing.ofAssociativeRing

theorem positiveInput_injective : Function.Injective positiveInput := by
  apply GeneratorDeletion.input_injective.comp
  have hc : GeneratorDeletion.cutAssoc.comp GeneratorDeletion.includeAssoc=AlgHom.id K (A K ℕ) := by
    apply hom_ext
    intro n
    simp [GeneratorDeletion.cutAssoc,GeneratorDeletion.includeAssoc]
  exact Function.LeftInverse.injective (f:=GeneratorDeletion.includeAssoc) (g:=GeneratorDeletion.cutAssoc) (fun p => AlgHom.congr_fun hc p)

theorem erase_embed (p : FreeLieAlgebra K Slot) : embed (eraseLie p)=OreShift.eraseShift 0 (embed p) := by
  have h : embed.comp eraseLie=(OreShift.eraseShift (0 : A K Bool)).toLieHom.comp embed := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [eraseLie,OreShift.eraseShift,OreShift.B,OreShift.C]
  exact LieHom.congr_fun h p

@[simp] theorem embed_leading (r : ℕ) (p : FreeLieAlgebra K Slot) :
    embed (leading r p)=OreShift.eraseShift 0 (WordGrading.piece bCount r (embed p)) := by
  rw [leading,erase_embed,LieGrading.embed_piece]

end

open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon AlphabetTransport
attribute [local instance] LieRing.ofAssociativeRing

end ImageBound
end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section
namespace WordGrading
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]

theorem homogeneous_lie {wt : α → ℕ} {r s : ℕ} {p q : A R α}
    (hp : p∈homogeneous wt r) (hq : q∈homogeneous wt s) : ⁅p,q⁆∈homogeneous wt (r+s) := by
  change p*q-q*p∈_
  exact (homogeneous wt _).sub_mem (homogeneous_mul hp hq) (by simpa only [Nat.add_comm] using homogeneous_mul hq hp)

theorem above_lie {wt : α → ℕ} {r s : ℕ} {p q : A R α}
    (hp : p∈above wt r) (hq : q∈above wt s) : ⁅p,q⁆∈above wt (r+s) := by
  change p*q-q*p∈_
  exact (above wt _).sub_mem (above_mul hp hq) (by simpa only [Nat.add_comm] using above_mul hq hp)

end WordGrading

namespace GenericIhara
open AssociativeElimination UniversalEmbedding
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]

def assocD (p : A R Bool) : A R Bool →ₗ[R] A R Bool :=
  deriv (fun b => if b then ⁅(atom true : A R Bool),p⁆ else 0)
def assocIhara (p q : A R Bool) := assocD p q-assocD q p+⁅p,q⁆

theorem embed_D (p q : FreeLieAlgebra R Bool) : embed (D p q)=assocD (embed p) (embed q) := by
  rw [←AssociativeDerivations.extend_embed]
  congr 1
  unfold AssociativeDerivations.extend assocD
  congr 1
  funext b
  cases b <;> simp [D]

theorem embed_ihara (p q : FreeLieAlgebra R Bool) : embed (ihara p q)=assocIhara (embed p) (embed q) := by
  simp only [ihara,assocIhara,map_add,map_sub,LieHom.map_lie,embed_D]

theorem rational_D (p q : L) : D p q=DeligneDrinfeld.D p q := by
  have h : D p=derivation p := by
    apply derivation_ext
    · change D p x=DeligneDrinfeld.D p x
      rw [D_x]
      simp [D,x]
    · change D p y=DeligneDrinfeld.D p y
      rw [D_y]
      simp [D,y]
  exact LieDerivation.congr_fun h q

theorem rational_ihara (p q : L) : ihara p q=DeligneDrinfeld.ihara p q := by
  simp only [ihara,DeligneDrinfeld.ihara,rational_D]

end GenericIhara

namespace GenericIhara

section
open AssociativeElimination UniversalEmbedding WordGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R : Type*} [CommRing R]

theorem assocD_above {p q : A R Bool} {r s : ℕ} (hp : p∈above depth r) (hq : q∈above depth s) :
    assocD p q∈above depth (s+r) := by
  apply deriv_above (c:=r) (f:=fun b => if b then ⁅(atom true : A R Bool),p⁆ else 0) ?_ hq
  intro b
  cases b with
  | false => exact Submodule.zero_mem _
  | true =>
    exact above_lie (homogeneous_above (word_mem (FreeMonoid.of true) (degree_of depth true))) hp

theorem assocIhara_above {p q : A R Bool} {r s : ℕ} (hp : p∈above depth r) (hq : q∈above depth s) :
    assocIhara p q∈above depth (r+s) := by
  apply (above depth (r+s)).add_mem ?_ (above_lie hp hq)
  apply (above depth (r+s)).sub_mem
  · simpa only [Nat.add_comm] using assocD_above hp hq
  · exact assocD_above hq hp

theorem ihara_above {p q : FreeLieAlgebra R Bool} {r s : ℕ}
    (hp : embed p∈above depth r) (hq : embed q∈above depth s) :
    embed (ihara p q)∈above depth (r+s) := by
  rw [embed_ihara]
  exact assocIhara_above hp hq

theorem assocD_homogeneous {wt : Bool → ℕ} {p q : A R Bool} {n m : ℕ}
    (hp : p∈homogeneous wt n) (hq : q∈homogeneous wt m) :
    assocD p q∈homogeneous wt (m+n) := by
  apply deriv_homogeneous (c:=n) (f:=fun b => if b then ⁅(atom true : A R Bool),p⁆ else 0) ?_ hq
  intro b
  cases b with
  | false => exact Submodule.zero_mem _
  | true => exact homogeneous_lie (word_mem (FreeMonoid.of true) (degree_of wt true)) hp

theorem ihara_homogeneous {wt : Bool → ℕ} {p q : FreeLieAlgebra R Bool} {n m : ℕ}
    (hp : embed p∈homogeneous wt n) (hq : embed q∈homogeneous wt m) :
    embed (ihara p q)∈homogeneous wt (n+m) := by
  rw [embed_ihara]
  apply (homogeneous wt (n+m)).add_mem ?_ (homogeneous_lie hp hq)
  apply (homogeneous wt (n+m)).sub_mem
  · simpa only [Nat.add_comm] using assocD_homogeneous hp hq
  · exact assocD_homogeneous hq hp

end

open LieAlgebra
variable {R : Type*} [CommRing R]
local notation "FL" => FreeLieAlgebra R Bool
local notation "Der" => LieDerivation R FL FL

def Dlinear : FL →ₗ[R] Der where
  toFun := D
  map_add' := D_add
  map_smul' := D_smul

theorem erase_lie (p q : Algebra R) : erase ⁅p,q⁆=ihara (erase p) (erase q) := by
  change ⁅p.val.left,q.val.left⁆+p.val.right q.val.left-q.val.right p.val.left=_
  rw [p.property,q.property]
  change ⁅p.val.left,q.val.left⁆+D p.val.left q.val.left-D q.val.left p.val.left =
    D p.val.left q.val.left-D q.val.left p.val.left+⁅p.val.left,q.val.left⁆
  abel

variable {α : Type*}

theorem evalIhara_lie (f : α → FL) (p q : FreeLieAlgebra R α) :
    evalIhara f ⁅p,q⁆=ihara (evalIhara f p) (evalIhara f q) := by
  change erase (lift f ⁅p,q⁆)=_
  rw [LieHom.map_lie,erase_lie]
  rfl

end GenericIhara

namespace LatticeDimension
open scoped TensorProduct
variable {ι : Type*}

def cast : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) where
  toFun u i := u i
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp] theorem cast_apply (u : ι → ℤ) (i : ι) : cast u i=(u i : ℚ) := rfl

def lattice (E : Submodule ℚ (ι → ℚ)) : Submodule ℤ (ι → ℤ) :=
  (E.restrictScalars ℤ).comap cast

@[simp] theorem mem_lattice (E : Submodule ℚ (ι → ℚ)) (u : ι → ℤ) :
    u∈lattice E ↔ cast u∈E := Iff.rfl

theorem saturated (E : Submodule ℚ (ι → ℚ)) {k : ℤ} (hk : k≠0) {u : ι → ℤ}
    (hu : k • u∈lattice E) : u∈lattice E := by
  have h : (k : ℚ) • cast u∈E := by
    change cast (k • u)∈E at hu
    rw [map_smul] at hu
    simpa only [Int.cast_smul_eq_zsmul] using hu
  exact (E.smul_mem_iff (by exact_mod_cast hk)).mp h

instance quotient_torsionFree (E : Submodule ℚ (ι → ℚ)) :
    Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ lattice E) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro k u h
  by_cases hk : k=0
  · exact Or.inl hk
  right
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    apply (Submodule.Quotient.mk_eq_zero (lattice E)).mpr
    apply saturated E hk
    exact (Submodule.Quotient.mk_eq_zero (lattice E)).mp h

variable [Fintype ι]

theorem exists_retraction (E : Submodule ℚ (ι → ℚ)) :
    ∃ p : (ι → ℤ) →ₗ[ℤ] lattice E,p.comp (lattice E).subtype=LinearMap.id := by
  obtain ⟨s,hs⟩ := (lattice E).mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (lattice E).mkQ_surjective)
  let p : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) := LinearMap.id-s.comp (lattice E).mkQ
  have hp (u : ι → ℤ) : p u∈lattice E := by
    apply (Submodule.Quotient.mk_eq_zero (lattice E)).mp
    change (lattice E).mkQ (p u)=0
    dsimp [p]
    have he := LinearMap.congr_fun hs ((lattice E).mkQ u)
    simpa using sub_eq_zero.mpr he.symm
  refine ⟨p.codRestrict (lattice E) hp,?_⟩
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  have hu0 : (lattice E).mkQ u.val=0 := (Submodule.Quotient.mk_eq_zero _).mpr u.property
  change u.val-s ((lattice E).mkQ u.val)=u.val
  rw [hu0,map_zero,sub_zero]

variable (F : Type*) [Field F]

def scalarMap (E : Submodule ℚ (ι → ℚ)) : F ⊗[ℤ] lattice E →ₗ[F] (ι → F) :=
  (TensorProduct.piScalarRightHom ℤ F F ι).comp ((lattice E).subtype.baseChange F)

omit [Fintype ι] in
@[simp] theorem scalarMap_tmul (E : Submodule ℚ (ι → ℚ)) (r : F) (u : lattice E) :
    scalarMap F E (r ⊗ₜ u)=fun i => (u.val i : F)*r := by
  ext i
  simp [scalarMap]

theorem scalarMap_injective (E : Submodule ℚ (ι → ℚ)) : Function.Injective (scalarMap F E) := by
  classical
  obtain ⟨p,hp⟩ := exists_retraction E
  have hleft : (p.baseChange F).comp ((lattice E).subtype.baseChange F)=LinearMap.id := by
    rw [←LinearMap.baseChange_comp,hp,LinearMap.baseChange_id]
  have hi : Function.Injective ((lattice E).subtype.baseChange F) := by
    apply Function.LeftInverse.injective (f:=((lattice E).subtype.baseChange F)) (g:=p.baseChange F)
    intro u
    exact LinearMap.congr_fun hleft u
  exact (TensorProduct.piScalarRight ℤ F F ι).injective.comp hi

def reduction (E : Submodule ℚ (ι → ℚ)) : Submodule F (ι → F) :=
  (scalarMap F E).range

theorem rational_range (E : Submodule ℚ (ι → ℚ)) : reduction ℚ E=E := by
  apply le_antisymm
  · rintro v ⟨u,rfl⟩
    induction u using TensorProduct.induction_on with
    | zero => first | rfl | exact Submodule.zero_mem _ | simp
    | tmul r u =>
      have he : scalarMap ℚ E (r ⊗ₜ u)=r • cast u.val := by ext; simp [mul_comm]
      rw [he]
      exact E.smul_mem r u.property
    | add u v hu hv => simpa using E.add_mem hu hv
  · intro v hv
    obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) v
    choose u hu using hd
    have hcast : cast u=(d.val : ℚ) • v := by
      ext i
      simpa using hu i
    have huE : u∈lattice E := by
      rw [mem_lattice,hcast]
      exact E.smul_mem _ hv
    refine ⟨(d.val : ℚ)⁻¹ ⊗ₜ (⟨u,huE⟩ : lattice E),?_⟩
    have hd0 : (d.val : ℚ)≠0 := by exact_mod_cast nonZeroDivisors.ne_zero d.property
    ext i
    rw [scalarMap_tmul]
    have hi := congrFun hcast i
    dsimp at hi ⊢
    rw [hi]
    field_simp

theorem finrank_reduction (E : Submodule ℚ (ι → ℚ)) :
    Module.finrank F (reduction F E)=Module.finrank ℚ E := by
  have hF := (LinearEquiv.ofInjective (scalarMap F E) (scalarMap_injective F E)).finrank_eq
  have hQ := (LinearEquiv.ofInjective (scalarMap ℚ E) (scalarMap_injective ℚ E)).finrank_eq
  rw [Module.finrank_baseChange] at hF hQ
  change _=Module.finrank ℚ (reduction ℚ E) at hQ
  rw [rational_range] at hQ
  exact hF.symm.trans hQ

end LatticeDimension

namespace LieDimension
open AssociativeElimination UniversalEmbedding WordGrading
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {α : Type*}
variable (R : Type*) [CommRing R] (wt : α → ℕ) (n : ℕ)

theorem coordinates_injective : Function.Injective (coordinates R wt n) := by
  intro p q h
  have he := WordCoordinates.coordinates_injective (fun w => degree wt w=n) h
  apply Subtype.ext
  apply UniversalEmbedding.injective
  exact congrArg Subtype.val he

def image : Submodule R (Words wt n → R) := (coordinates R wt n).range

variable {R wt n}

theorem words_space {P : FreeMonoid α → Prop} {p : A ℤ α} (hp : p∈space P) :
    IntegralBaseChange.words (S:=R) p∈space P := by
  apply mem_space
  intro w hw
  rw [IntegralBaseChange.words_coeff] at hw
  apply mem_space_iff.mp hp w
  intro h
  exact hw (by rw [h,Int.cast_zero])

theorem words_space_reflect {P : FreeMonoid α → Prop} {p : A ℤ α}
    (hp : IntegralBaseChange.words (S:=ℚ) p∈space P) : p∈space P := by
  apply mem_space
  intro w hw
  apply mem_space_iff.mp hp w
  rw [IntegralBaseChange.words_coeff]
  exact_mod_cast hw

def castHom (p : LieGrading.homogeneousLie (R:=ℤ) wt n) : LieGrading.homogeneousLie (R:=R) wt n :=
  ⟨IntegralBaseChange.lie p.val,LieGrading.homogeneous_iff.mpr (by
    rw [IntegralBaseChange.embed_lie]
    exact words_space (LieGrading.homogeneousLie_embed p.property))⟩

@[simp] theorem coordinates_castHom (p : LieGrading.homogeneousLie (R:=ℤ) wt n) (w : Words wt n) :
    coordinates R wt n (castHom p) w=(coordinates ℤ wt n p w : R) := by
  simp [castHom,IntegralBaseChange.embed_lie]

theorem lattice_image (wt : α → ℕ) (n : ℕ) :
    LatticeDimension.lattice (image ℚ wt n)=image ℤ wt n := by
  apply le_antisymm
  · rintro u ⟨p,hp⟩
    have hpint : embed p.val∈IntegralWords.lattice := by
      apply IntegralWords.integral_of_coeff
      intro w
      by_cases hw : degree wt w=n
      · refine ⟨u ⟨w,hw⟩,?_⟩
        exact congrFun hp ⟨w,hw⟩
      · exact ⟨0,(coeff_support (LieGrading.homogeneousLie_embed p.property) w hw).trans (Int.cast_zero).symm⟩
    obtain ⟨q,hq⟩ := IntegralBaseChange.lift_integral hpint
    have hqm : q∈LieGrading.homogeneousLie wt n := by
      apply LieGrading.homogeneous_iff.mpr
      apply words_space_reflect
      rw [←IntegralBaseChange.embed_lie,hq]
      exact LieGrading.homogeneousLie_embed p.property
    refine ⟨⟨q,hqm⟩,?_⟩
    ext w
    apply Int.cast_injective (α:=ℚ)
    change ((embed q).coeff w.val : ℚ)=_
    rw [←IntegralBaseChange.words_coeff,←IntegralBaseChange.embed_lie,hq]
    exact congrFun hp w
  · rintro u ⟨p,rfl⟩
    refine ⟨castHom (R:=ℚ) p,?_⟩
    ext w
    exact coordinates_castHom p w

theorem cast_eval (t : UniversalEmbedding.Tree α) : IntegralBaseChange.lie (t.eval (R:=ℤ))=t.eval (R:=R) := by
  induction t with
  | leaf a => simp [Tree.eval]
  | node t u ht hu => simp [Tree.eval,ht,hu]

variable (F : Type*) [Field F] (wt : α → ℕ) (n : ℕ) [Fintype (Words wt n)]

omit [Fintype (Words wt n)] in
theorem reduction_image : LatticeDimension.reduction F (image ℚ wt n)=image F wt n := by
  apply le_antisymm
  · rintro v ⟨u,rfl⟩
    induction u using TensorProduct.induction_on with
    | zero => first | rfl | exact Submodule.zero_mem _ | simp
    | tmul c u =>
      have hup : u.val∈image ℤ wt n := by
        rw [←lattice_image]
        exact u.property
      obtain ⟨p,hp⟩ := hup
      have he : LatticeDimension.scalarMap F (image ℚ wt n) (c ⊗ₜ u)=
          c • coordinates F wt n (castHom p) := by
        ext w
        rw [LatticeDimension.scalarMap_tmul]
        simp only [Pi.smul_apply,smul_eq_mul,coordinates_castHom]
        rw [←congrFun hp w,mul_comm]
      rw [he]
      exact (image F wt n).smul_mem c ⟨castHom p,rfl⟩
    | add u v hu hv => simpa using (image F wt n).add_mem hu hv
  · rintro v ⟨p,rfl⟩
    have hgen : ∀ q : FreeLieAlgebra F α,q∈LieGrading.homogeneousLie wt n →
        ∀ hq,coordinates F wt n ⟨q,hq⟩∈LatticeDimension.reduction F (image ℚ wt n) := by
      intro q hq
      induction hq using Submodule.span_induction with
      | mem q hq =>
        obtain ⟨t,ht,rfl⟩ := hq
        intro hm
        let pZ : LieGrading.homogeneousLie (R:=ℤ) wt n := ⟨t.eval,Submodule.subset_span ⟨t,ht,rfl⟩⟩
        have hpZ : coordinates ℤ wt n pZ∈LatticeDimension.lattice (image ℚ wt n) := by
          rw [lattice_image]
          exact ⟨pZ,rfl⟩
        refine ⟨(1 : F) ⊗ₜ (⟨coordinates ℤ wt n pZ,hpZ⟩ : LatticeDimension.lattice (image ℚ wt n)),?_⟩
        ext w
        rw [LatticeDimension.scalarMap_tmul]
        change ((embed (t.eval (R:=ℤ))).coeff w.val : F)*1=(embed (t.eval (R:=F))).coeff w.val
        rw [mul_one]
        rw [←IntegralBaseChange.words_coeff,←IntegralBaseChange.embed_lie,cast_eval]
      | zero => intro hm; change coordinates F wt n 0∈_; simp
      | add q r hq hr hi hj =>
        intro hm
        change coordinates F wt n (⟨q,hq⟩+⟨r,hr⟩)∈_
        rw [map_add]
        exact (LatticeDimension.reduction F (image ℚ wt n)).add_mem (hi hq) (hj hr)
      | smul c q hq hi =>
        intro hm
        change coordinates F wt n (c • ⟨q,hq⟩)∈_
        rw [map_smul]
        exact (LatticeDimension.reduction F (image ℚ wt n)).smul_mem c (hi hq)
    exact hgen p.val p.property p.property

instance homogeneous_finite : Module.Finite F (LieGrading.homogeneousLie (R:=F) wt n) :=
  Module.Finite.of_injective (coordinates F wt n) (coordinates_injective F wt n)

theorem finrank_homogeneous :
    Module.finrank F (LieGrading.homogeneousLie (R:=F) wt n)=
      Module.finrank ℚ (LieGrading.homogeneousLie (R:=ℚ) wt n) := by
  have hF := (LinearEquiv.ofInjective (coordinates F wt n) (coordinates_injective F wt n)).finrank_eq
  have hQ := (LinearEquiv.ofInjective (coordinates ℚ wt n) (coordinates_injective ℚ wt n)).finrank_eq
  have h := LatticeDimension.finrank_reduction F (image ℚ wt n)
  rw [reduction_image] at h
  exact hF.trans (h.trans hQ.symm)

end LieDimension

namespace LieGrading
open AssociativeElimination UniversalEmbedding WordGrading
variable {R α : Type*} [CommRing R]

def projection (wt : α → ℕ) (n : ℕ) : FreeLieAlgebra R α →ₗ[R] FreeLieAlgebra R α where
  toFun := piece wt n
  map_add' := piece_add wt n
  map_smul' := piece_smul wt n

theorem piece_homogeneous {wt : α → ℕ} {m : ℕ} {p : FreeLieAlgebra R α}
    (hp : p∈homogeneousLie wt m) (n : ℕ) : piece wt n p=if m=n then p else 0 := by
  apply UniversalEmbedding.injective
  rw [embed_piece,WordGrading.piece_homogeneous (homogeneousLie_embed hp)]
  split_ifs <;> simp

def components (wa wb : α → ℕ) (n m : ℕ) :
    homogeneousLie (R:=R) wa n →ₗ[R] ((r : Fin (m+1)) → biPiece (R:=R) wa wb n r.val) where
  toFun p r := ⟨piece wb r.val p.val,⟨homogeneous_iff.mpr (by
      rw [embed_piece]; exact project_preserves (homogeneousLie_embed p.property)),
      (piece_spec wb r.val p.val).1⟩⟩
  map_add' p q := by ext r; exact piece_add wb r.val p.val q.val
  map_smul' c p := by ext r; exact piece_smul wb r.val c p.val

def assemble (wa wb : α → ℕ) (n m : ℕ) :
    ((r : Fin (m+1)) → biPiece (R:=R) wa wb n r.val) →ₗ[R] homogeneousLie (R:=R) wa n where
  toFun q := ⟨∑ r,(q r).val,Submodule.sum_mem _ (fun r _ => (q r).property.1)⟩
  map_add' p q := by ext; simp only [Pi.add_apply,Submodule.coe_add,Finset.sum_add_distrib]
  map_smul' c p := by ext; simp only [Pi.smul_apply,Submodule.coe_smul,Finset.smul_sum,RingHom.id_apply]

theorem components_assemble (wa wb : α → ℕ) (n m : ℕ)
    (q : (r : Fin (m+1)) → biPiece (R:=R) wa wb n r.val) :
    components wa wb n m (assemble wa wb n m q)=q := by
  classical
  funext r
  apply Subtype.ext
  change projection wb r.val (∑ s,(q s).val)=(q r).val
  rw [map_sum]
  simp only [projection,LinearMap.coe_mk,AddHom.coe_mk]
  simp_rw [piece_homogeneous (q _).property.2]
  simp [Fin.val_inj]

theorem assemble_components (wa wb : α → ℕ) (n m : ℕ)
    (hbound : ∀ w : FreeMonoid α, degree wa w = n → degree wb w ≤ m)
    (p : homogeneousLie (R:=R) wa n) :
    assemble wa wb n m (components wa wb n m p)=p := by
  classical
  apply Subtype.ext
  apply UniversalEmbedding.injective
  change embed (∑ r : Fin (m+1),piece wb r.val p.val)=embed p.val
  rw [map_sum]
  simp_rw [embed_piece]
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  change (∑ r : Fin (m+1), WordGrading.piece wb r.val (embed p.val)).coeff w=(embed p.val).coeff w
  simp only [MonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,WordGrading.piece,project_coeff]
  by_cases hw : degree wa w=n
  · have hb := hbound w hw
    exact Finset.sum_eq_single (⟨degree wb w,by omega⟩ : Fin (m+1))
      (by intro r _ hr; rw [if_neg (by intro h; apply hr; exact Fin.ext h.symm)])
      (by simp) |>.trans (if_pos rfl)
  · have hz := coeff_support (homogeneousLie_embed p.property) w hw
    simp [hz]

def decomposition (wa wb : α → ℕ) (n m : ℕ)
    (hbound : ∀ w : FreeMonoid α, degree wa w = n → degree wb w ≤ m) :
    homogeneousLie (R:=R) wa n ≃ₗ[R] ((r : Fin (m+1)) → biPiece (R:=R) wa wb n r.val) :=
  LinearEquiv.ofLinearMap (components wa wb n m) (assemble wa wb n m)
    (LinearMap.ext (components_assemble wa wb n m))
    (LinearMap.ext (assemble_components wa wb n m hbound))

variable (F : Type*) [Field F]

theorem finrank_decomposition (wa wb : α → ℕ) (n m : ℕ)
    (hbound : ∀ w : FreeMonoid α, degree wa w = n → degree wb w ≤ m)
    [Module.Finite F (homogeneousLie (R:=F) wa n)] :
    Module.finrank F (homogeneousLie (R:=F) wa n)=
      ∑ r : Fin (m+1),Module.finrank F (biPiece (R:=F) wa wb n r.val) := by
  let (r : Fin (m+1)) : Module.Finite F (biPiece (R:=F) wa wb n r.val) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)
  rw [(decomposition (R:=F) wa wb n m hbound).finrank_eq,Module.finrank_pi_fintype]

end LieGrading
end

namespace FiltrationDimension
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
variable {T : ℕ → Type*} [∀ r,AddCommGroup (T r)] [∀ r,Module K (T r)] [∀ r,Module.Finite K (T r)]

theorem step (F : ℕ → Submodule K V) (r : ℕ) (f : F r →ₗ[K] T r)
    (hk : ∀ p : F r,f p=0 → p.val∈F (r+1)) :
    Module.finrank K (F r)≤Module.finrank K (T r)+Module.finrank K (F (r+1)) := by
  let g : f.ker →ₗ[K] F (r+1) :=
    { toFun := fun p => ⟨p.val.val,hk p.val p.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hi : Function.Injective g := by
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun p : F (r+1) => p.val) h
  have hker := LinearMap.finrank_le_finrank_of_injective hi
  have hrange := Submodule.finrank_le f.range
  have := f.finrank_range_add_finrank_ker
  omega

theorem telescoping (F : ℕ → Submodule K V) (f : (r : ℕ) → F r →ₗ[K] T r)
    (hk : ∀ r (p : F r),f r p=0 → p.val∈F (r+1)) (N : ℕ) :
    Module.finrank K (F 0)≤(∑ r∈Finset.range N,Module.finrank K (T r))+Module.finrank K (F N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs := step F N (f N) (hk N)
    rw [Finset.sum_range_succ]
    omega

theorem bound (F : ℕ → Submodule K V) (f : (r : ℕ) → F r →ₗ[K] T r)
    (hk : ∀ r (p : F r),f r p=0 → p.val∈F (r+1)) (N : ℕ)
    (hN : F N=⊥) : Module.finrank K (F 0)≤∑ r∈Finset.range N,Module.finrank K (T r) := by
  have h := telescoping F f hk N
  rw [hN,finrank_bot,add_zero] at h
  exact h

omit [∀ r,Module.Finite K (T r)] in
theorem range_step (F : ℕ → Submodule K V) (r : ℕ) (f : F r →ₗ[K] T r)
    (hk : ∀ p : F r,f p=0 → p.val∈F (r+1)) :
    Module.finrank K (F r)≤Module.finrank K f.range+Module.finrank K (F (r+1)) := by
  let g : f.ker →ₗ[K] F (r+1) :=
    { toFun := fun p => ⟨p.val.val,hk p.val p.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hi : Function.Injective g := by
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun p : F (r+1) => p.val) h
  have hker := LinearMap.finrank_le_finrank_of_injective hi
  have := f.finrank_range_add_finrank_ker
  omega

theorem surjective_of_equality (F : ℕ → Submodule K V)
    (f : (r : ℕ) → F r →ₗ[K] T r)
    (hk : ∀ r (p : F r),f r p=0 → p.val∈F (r+1)) (N : ℕ)
    (hN : F N=⊥)
    (he : Module.finrank K (F 0)=∑ r∈Finset.range N,Module.finrank K (T r))
    (r : ℕ) (hr : r<N) : Function.Surjective (f r) := by
  let a := fun i => (∑ j∈Finset.range i,Module.finrank K (T j))+Module.finrank K (F i)
  have ha : Monotone a := by
    apply monotone_nat_of_le_succ
    intro i
    have hi := step F i (f i) (hk i)
    dsimp [a]
    rw [Finset.sum_range_succ]
    omega
  have hends : a 0=a N := by
    simp only [a,Finset.range_zero,Finset.sum_empty,zero_add]
    rw [hN,finrank_bot,add_zero]
    exact he
  have hstep : a r=a (r+1) := by
    apply le_antisymm (ha (by omega))
    exact (ha (by omega : r+1≤N)).trans (hends.symm.le.trans (ha (Nat.zero_le r)))
  have hs := range_step F r (f r) (hk r)
  have hle := Submodule.finrank_le (f r).range
  have heq : Module.finrank K (f r).range=Module.finrank K (T r) := by
    dsimp [a] at hstep
    rw [Finset.sum_range_succ] at hstep
    omega
  exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq heq)
end FiltrationDimension

section
namespace ReducedDimension
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open RowTwo RowKernel ExactPentagon ImageBound
attribute [local instance] LieRing.ofAssociativeRing

instance finite_boolWords (n : ℕ) : Fintype (LieDimension.Words (fun _ : Bool => 1) n) :=
  (WordCoordinates.finite_degree_finite_alphabet (fun _ : Bool => 1) (by simp) n).fintype

instance finite_oddWords (n : ℕ) : Fintype (LieDimension.Words oddWeight n) := by
  apply Set.Finite.fintype
  apply WordCoordinates.finite_degree oddWeight (by intro a; simp [oddWeight]) n
  apply (Set.finite_Iic n).subset
  intro a ha
  change a≤n
  change oddWeight a≤n at ha
  unfold oddWeight at ha
  omega

theorem solutions_hom {n : ℕ} (p : solutions n) :
    p.val∈LieGrading.homogeneousLie (fun _ => 1) n := p.property.1.1.1

theorem solutions_anti {n : ℕ} (p : solutions n) : BaseChangeEquations.antisymmetry p.val=0 := p.property.1.1.2

theorem solutions_special {n : ℕ} (p : solutions n) : BaseChangeEquations.special p.val=0 := p.property.1.2

theorem solutions_pentagon {n : ℕ} (p : solutions n) : BaseChangeEquations.pentagon p.val=0 := p.property.2

instance finite_solutions (n : ℕ) : Module.Finite K (solutions n) :=
  Module.Finite.of_injective (Submodule.inclusion (inf_le_left.trans (inf_le_left.trans inf_le_left)))
    (Submodule.inclusion_injective _)

def representation (n : ℕ) (hn : 1<n) (p : solutions n) : FreeLieAlgebra K Slot :=
  (QuadraticLeading.representation hn (LieGrading.homogeneousLie_embed (solutions_hom p))).choose

theorem representation_under (n : ℕ) (hn : 1<n) (p : solutions n) :
    under (representation n hn p)=embed p.val :=
  (QuadraticLeading.representation hn (LieGrading.homogeneousLie_embed (solutions_hom p))).choose_spec.1

def representationMap (n : ℕ) (hn : 1<n) : solutions n →ₗ[K] FreeLieAlgebra K Slot where
  toFun := representation n hn
  map_add' p q := by
    apply under_injective
    rw [map_add,representation_under,representation_under,representation_under]
    simp only [Submodule.coe_add,map_add]
  map_smul' c p := by
    apply under_injective
    rw [map_smul,representation_under,representation_under]
    simp only [Submodule.coe_smul,map_smul,RingHom.id_apply]

theorem representation_injective (n : ℕ) (hn : 1<n) : Function.Injective (representationMap n hn) := by
  intro p q h
  apply Subtype.ext
  apply UniversalEmbedding.injective
  exact (representation_under n hn p).symm.trans ((congrArg under h).trans (representation_under n hn q))

def filtration (n : ℕ) (hn : 1<n) (r : ℕ) : Submodule K (solutions n) :=
  (above bCount r).comap (embed.toLinearMap.comp (representationMap n hn))

def oddPiece (n r : ℕ) : Submodule K (FreeLieAlgebra K ℕ) :=
  LieGrading.biPiece oddWeight (fun _ => 1) n r

instance finite_oddPiece (n r : ℕ) : Module.Finite K (oddPiece n r) :=
  Module.Finite.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)

def inclusion (n r : ℕ) : oddPiece n r →ₗ[K] A K Bool :=
  positiveInput.toLinearMap.comp (embed.toLinearMap.comp (oddPiece n r).subtype)

theorem inclusion_injective (n r : ℕ) : Function.Injective (inclusion n r) :=
  positiveInput_injective.comp (UniversalEmbedding.injective.comp Subtype.val_injective)

def leadingMap (n : ℕ) (hn : 1<n) (r : ℕ) : filtration n hn r →ₗ[K] A K Bool :=
  (embed.toLinearMap.comp (eraseLie.toLinearMap.comp (LieGrading.projection bCount r))).comp
    ((representationMap n hn).comp (filtration n hn r).subtype)

theorem leadingMap_apply (n : ℕ) (hn : 1<n) (r : ℕ) (p : filtration n hn r) :
    leadingMap n hn r p=embed (leading r (representation n hn p.val)) := rfl

theorem leading_in_range (n : ℕ) (hn : 2<n) (r : ℕ) (p : filtration n (by omega) r) :
    leadingMap n (by omega) r p∈(inclusion n r).range := by
  obtain ⟨q,hq,hw,hr⟩ := actual_image hn (LieGrading.homogeneousLie_embed (solutions_hom p.val))
    (representation_under n (by omega) p.val) p.val.property.1.1.2 p.property
  exact ⟨⟨q,LieGrading.homogeneous_iff.mpr hw,LieGrading.homogeneous_iff.mpr hr⟩,hq⟩

def gradedMap (n : ℕ) (hn : 2<n) (r : ℕ) : filtration n (by omega) r →ₗ[K] oddPiece n r :=
  (LinearEquiv.ofInjective (inclusion n r) (inclusion_injective n r)).symm.toLinearMap.comp
    ((leadingMap n (by omega) r).codRestrict _ (leading_in_range n hn r))

theorem gradedMap_spec (n : ℕ) (hn : 2<n) (r : ℕ) (p : filtration n (by omega) r) :
    inclusion n r (gradedMap n hn r p)=leadingMap n (by omega) r p := by
  have h := (LinearEquiv.ofInjective (inclusion n r) (inclusion_injective n r)).apply_symm_apply
    ⟨leadingMap n (by omega) r p,leading_in_range n hn r p⟩
  exact congrArg Subtype.val h

def restore : FreeLieAlgebra K Bool →ₗ⁅K⁆ FreeLieAlgebra K Slot :=
  FreeLieAlgebra.lift K (fun b => if b then FreeLieAlgebra.of K Slot.B else FreeLieAlgebra.of K Slot.C)

theorem restore_erase (p : FreeLieAlgebra K Slot) :
    restore (eraseLie p)=LetterRetraction.lie (fun a => a≠Slot.A) p := by
  have he : restore.comp eraseLie=LetterRetraction.lie (fun a => a≠Slot.A) := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [restore,eraseLie,LetterRetraction.lie]
  exact LieHom.congr_fun he p

theorem graded_kernel (n : ℕ) (hn : 2<n) (r : ℕ) (p : filtration n (by omega) r)
    (hz : gradedMap n hn r p=0) : p.val∈filtration n (by omega) (r+1) := by
  have he : leading r (representation n (by omega) p.val)=0 := by
    apply UniversalEmbedding.injective
    rw [map_zero,←leadingMap_apply,←gradedMap_spec n hn r p,hz,map_zero]
  have hret : LetterRetraction.lie (fun a => a≠Slot.A)
      (LieGrading.piece bCount r (representation n (by omega) p.val))=0 := by
    rw [←restore_erase]
    change restore (leading r (representation n (by omega) p.val))=0
    rw [he,map_zero]
  have hproj := ProjectionKernel.leading_projection_kernel hn (representation_under n (by omega) p.val)
    (representation_weight (LieGrading.homogeneousLie_embed (solutions_hom p.val))
      (representation_under n (by omega) p.val)) p.property
    (solutions_anti p.val) (solutions_special p.val) (solutions_pentagon p.val) hret
  have hs := subtract_piece_above p.property
  change embed (representation n (by omega) p.val)-
    WordGrading.piece bCount r (embed (representation n (by omega) p.val))∈above bCount (r+1) at hs
  rw [←LieGrading.embed_piece,hproj,map_zero,sub_zero] at hs
  exact hs

theorem filtration_zero (n : ℕ) (hn : 1<n) : filtration n hn 0=⊤ := by
  apply top_unique
  intro p hp
  apply mem_space
  intro w hw
  exact Nat.zero_le _

theorem filtration_terminal (n : ℕ) (hn : 1<n) : filtration n hn (n+1)=⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro p hp
  apply representation_injective n hn
  rw [map_zero]
  apply UniversalEmbedding.injective
  rw [map_zero]
  have hw := representation_weight (LieGrading.homogeneousLie_embed (solutions_hom p))
    (representation_under n hn p)
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  change (embed (representation n hn p)).coeff w=0
  by_contra hc
  have h1 := mem_space_iff.mp hw w hc
  have h2 := mem_space_iff.mp hp w hc
  have h3 := weight_count w
  omega

theorem odd_length_bound (n : ℕ) (w : FreeMonoid ℕ) (hw : degree oddWeight w=n) :
    degree (fun _ => 1) w≤n := by
  calc
    _=w.toList.length := by simp [degree]
    _≤degree oddWeight w := WordCoordinates.length_le_degree oddWeight (by intro a; simp [oddWeight]) w
    _=n := hw

theorem finrank_bound (n : ℕ) (hn : 2<n) :
    Module.finrank K (solutions n)≤Module.finrank K (LieGrading.homogeneousLie (R:=K) oddWeight n) := by
  have h := FiltrationDimension.bound (filtration n (by omega)) (gradedMap n hn)
    (graded_kernel n hn) (n+1) (filtration_terminal n (by omega))
  rw [filtration_zero,finrank_top] at h
  rw [LieGrading.finrank_decomposition K oddWeight (fun _ => 1) n n (odd_length_bound n)]
  change Module.finrank K (solutions n)≤∑ r : Fin (n+1),Module.finrank K (oddPiece n r.val)
  rw [Fin.sum_univ_eq_sum_range (fun r => Module.finrank K (oddPiece n r)) (n+1)]
  exact h

theorem rational_finrank_bound (n : ℕ) (hn : 2<n) :
    Module.finrank K (solutions n)≤Module.finrank ℚ (LieGrading.homogeneousLie (R:=ℚ) oddWeight n) := by
  rw [←LieDimension.finrank_homogeneous K oddWeight n]
  exact finrank_bound n hn

end ReducedDimension

open AssociativeElimination UniversalEmbedding WordGrading
open scoped TensorProduct

namespace RationalBound
open ReducedDimension

theorem coordinates_injective (n : ℕ) : Function.Injective (coordinates n) := by
  intro p q h
  apply Subtype.ext
  exact congrArg (fun z : LieGrading.homogeneousLie (R:=ℚ) wt n => z.val) (LieDimension.coordinates_injective ℚ wt n h)

instance finite_Wn (n : ℕ) : Module.Finite ℚ (Wn n) :=
  Module.Finite.of_injective (coordinates n) (coordinates_injective n)

def image (n : ℕ) : Submodule ℚ (Words n → ℚ) := (coordinates n).range

def reducedCoordinates (n : ℕ) : solutions n →ₗ[K] (Words n → K) :=
  (LieDimension.coordinates K wt n).comp ((solutions n).subtype.codRestrict _ solutions_hom)

theorem reducedCoordinates_injective (n : ℕ) : Function.Injective (reducedCoordinates n) := by
  intro p q h
  apply Subtype.ext
  exact congrArg (fun z : LieGrading.homogeneousLie (R:=K) wt n => z.val) (LieDimension.coordinates_injective K wt n h)

def reducedImage (n : ℕ) : Submodule K (Words n → K) := (reducedCoordinates n).range

theorem lattice_lift (n : ℕ) (u : LatticeDimension.lattice (image n)) :
    ∃ q : LieGrading.homogeneousLie (R:=ℤ) wt n,
      LieDimension.coordinates ℤ wt n q=u.val ∧ (LieDimension.castHom (R:=ℚ) q).val∈W := by
  obtain ⟨p,hp⟩ := u.property
  have hfull : u.val∈LatticeDimension.lattice (LieDimension.image ℚ wt n) := by
    exact ⟨toHom n p,hp⟩
  rw [LieDimension.lattice_image] at hfull
  obtain ⟨q,hq⟩ := hfull
  refine ⟨q,hq,?_⟩
  have he : LieDimension.castHom (R:=ℚ) q=toHom n p := by
    apply LieDimension.coordinates_injective ℚ wt n
    ext w
    rw [LieDimension.coordinates_castHom]
    change ((LieDimension.coordinates ℤ wt n q) w : ℚ)=coordinates n p w
    rw [hq,congrFun hp w]
    rfl
  rw [he]
  exact p.property.1

def reduceLattice (n : ℕ) (hn : 2<n) (q : LieGrading.homogeneousLie (R:=ℤ) wt n)
    (hq : (LieDimension.castHom (R:=ℚ) q).val∈W) : solutions n := by
  have hw : (IntegralBaseChange.lie q.val : L)∈Ln n := by
    change (IntegralBaseChange.lie q.val : L)∈weightPiece wt n
    rw [LieGrading.weightPiece_eq]
    exact (LieDimension.castHom (R:=ℚ) q).property
  have hE := BaseChangeEquations.reduce (S:=K) q.val hq
  have hS := BaseChangeEquations.reduce_special (S:=K) q.val hq hw hn
  exact ⟨(LieDimension.castHom (R:=K) q).val,
    ⟨⟨⟨(LieDimension.castHom (R:=K) q).property,hE.1⟩,hS⟩,hE.2.2⟩⟩

theorem reduction_le (n : ℕ) (hn : 2<n) :
    LatticeDimension.reduction K (image n)≤reducedImage n := by
  rintro v ⟨u,rfl⟩
  induction u using TensorProduct.induction_on with
  | zero => first | rfl | exact Submodule.zero_mem _ | simp
  | tmul c u =>
    obtain ⟨q,hq,hW⟩ := lattice_lift n u
    have he : LatticeDimension.scalarMap K (image n) (c ⊗ₜ u)=
        c • reducedCoordinates n (reduceLattice n hn q hW) := by
      ext w
      rw [LatticeDimension.scalarMap_tmul]
      change (u.val w : K)*c=c*(embed (IntegralBaseChange.lie (S:=K) q.val)).coeff w.val
      rw [IntegralBaseChange.embed_lie,IntegralBaseChange.words_coeff]
      have hh := congrFun hq w
      change (embed q.val).coeff w.val=u.val w at hh
      rw [hh,mul_comm]
    rw [he]
    exact (reducedImage n).smul_mem c ⟨reduceLattice n hn q hW,rfl⟩
  | add u v hu hv => simpa using (reducedImage n).add_mem hu hv

theorem finrank_Wn_le (n : ℕ) (hn : 2<n) :
    Module.finrank ℚ (Wn n)≤Module.finrank ℚ (Fn n) := by
  have h0 := (LinearEquiv.ofInjective (coordinates n) (coordinates_injective n)).finrank_eq
  have h1 := LatticeDimension.finrank_reduction K (image n)
  have h2 := Submodule.finrank_mono (reduction_le n hn)
  have h3 := (LinearEquiv.ofInjective (reducedCoordinates n) (reducedCoordinates_injective n)).finrank_eq
  have h4 := rational_finrank_bound n hn
  rw [←LieGrading.weightPiece_eq] at h4
  change Module.finrank ℚ (Wn n)=Module.finrank ℚ (image n) at h0
  change Module.finrank K (solutions n)=Module.finrank K (reducedImage n) at h3
  change Module.finrank ℚ (Wn n)≤Module.finrank ℚ (weightPiece DeligneDrinfeld.oddWeight n)
  omega

end RationalBound
end

namespace LowWeight
open LieGrading UniversalEmbedding

theorem treeDegree_pos {α : Type*} {wt : α → ℕ} (hw : ∀ a,0<wt a) (u : UniversalEmbedding.Tree α) :
    0<treeDegree wt u := by
  induction u with
  | leaf a => simpa using hw a
  | node u v hu hv => simp only [treeDegree_node]; omega

theorem tree_degree_one {α : Type*} (u : UniversalEmbedding.Tree α) (hu : treeDegree (fun _ => 1) u=1) :
    ∃ a,u=.leaf a := by
  cases u with
  | leaf a => exact ⟨a,rfl⟩
  | node u v =>
    have h1 := treeDegree_pos (fun _ : α => Nat.zero_lt_one) u
    have h2 := treeDegree_pos (fun _ : α => Nat.zero_lt_one) v
    simp only [treeDegree_node] at hu
    omega

theorem weight_zero {α : Type*} {wt : α → ℕ} (hw : ∀ a,0<wt a) :
    weightPiece wt 0=⊥ := by
  rw [weightPiece_eq]
  apply le_antisymm ?_ bot_le
  apply Submodule.span_le.mpr
  rintro p ⟨u,hu,rfl⟩
  have h := treeDegree_pos hw u
  omega

theorem weight_one_form {p : L} (hp : p∈Ln 1) : ∃ a b : ℚ,p=a • x+b • y := by
  simp only [Ln,weightPiece_eq] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,hu,rfl⟩ := hp
    obtain ⟨a,rfl⟩ := tree_degree_one u hu
    cases a
    · exact ⟨1,0,by simp [Tree.eval,x]⟩
    · exact ⟨0,1,by simp [Tree.eval,y]⟩
  | zero => exact ⟨0,0,by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨a,b,rfl⟩ := hp
    obtain ⟨c,d,rfl⟩ := hq
    exact ⟨a+c,b+d,by simp only [add_smul]; abel⟩
  | smul c p _ hp =>
    obtain ⟨a,b,rfl⟩ := hp
    exact ⟨c*a,c*b,by simp only [smul_add,mul_smul]⟩

attribute [local instance] LieRing.ofAssociativeRing

def edgeValue (a b i j : Fin 4) : ℚ :=
  if (i=a ∧ j=b) ∨ (i=b ∧ j=a) then 1 else 0

def detector (a b : Fin 4) (hab : a≠b) : T4 →ₗ⁅ℚ⁆ ℚ :=
  T4Universal.lift (edgeValue a b)
    (by intros; simp only [edgeValue]; congr 1; apply propext; tauto)
    (by
      intro i
      simp only [edgeValue]
      split_ifs with h
      · rcases h with h|h
        · exact (hab (h.1.symm.trans h.2)).elim
        · exact (hab (h.2.symm.trans h.1)).elim
      · rfl)
    (by intros; simp only [LieRing.of_associative_ring_bracket,mul_comm,sub_self])
    (by intros; simp only [LieRing.of_associative_ring_bracket,mul_comm,sub_self])

@[simp] theorem detector_t (a b : Fin 4) (hab : a≠b) (i j : Fin 4) :
    detector a b hab (t i j)=edgeValue a b i j := T4Universal.lift_t _ _ _ _ _ _ _

theorem weight_one_zero {p : L} (hp : p∈Wn 1) : p=0 := by
  obtain ⟨a,b,rfl⟩ := weight_one_form hp.2
  have h := hp.1.2.2
  simp only [eval,map_add,map_smul,FreeLieAlgebra.lift_of_apply,x,y,Bool.false_eq_true,↓reduceIte] at h
  have h1 := congrArg (detector 0 1 (by decide)) h
  have h2 := congrArg (detector 2 3 (by decide)) h
  norm_num [map_add,map_smul,edgeValue,Fin.ext_iff] at h1 h2
  have ha : a=0 := by linarith
  have hb : b=0 := by linarith
  simp [ha,hb]

def cyclic : L →ₗ[ℚ] L := LinearMap.id+(eval y (-x-y)).toLinearMap+(eval (-x-y) x).toLinearMap

theorem cyclic_weight_two {p : L} (hp : p∈Ln 2) : cyclic p=(3 : ℚ) • p := by
  simp only [Ln,weightPiece_eq] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,hu,rfl⟩ := hp
    cases u with
    | leaf a => simp at hu
    | node u v =>
      have h1 := treeDegree_pos (fun _ : Bool => Nat.zero_lt_one) u
      have h2 := treeDegree_pos (fun _ : Bool => Nat.zero_lt_one) v
      simp only [treeDegree_node] at hu
      obtain ⟨a,rfl⟩ := tree_degree_one u (by omega)
      obtain ⟨b,rfl⟩ := tree_degree_one v (by omega)
      cases a <;> cases b <;>
        simp [Tree.eval,cyclic,eval,x,y,lie_sub,sub_lie,lie_skew,show (3 : ℚ)=(1+1+1) by norm_num,add_smul]
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add,hp,hq,smul_add]
  | smul c p _ hp => simp only [map_smul,hp,smul_smul,mul_comm]

theorem weight_two_zero {p : L} (hp : p∈Wn 2) : p=0 := by
  have hc : cyclic p=0 := hp.1.2.1
  rw [cyclic_weight_two hp.2] at hc
  exact (smul_eq_zero.mp hc).resolve_left (by norm_num)

theorem Wn_eq_bot {n : ℕ} (hn : n≤2) : Wn n=⊥ := by
  apply le_antisymm ?_ bot_le
  intro p hp
  change p=0
  interval_cases n
  · have h : Ln 0=⊥ := weight_zero (fun _ => by decide)
    have hz := hp.2
    rw [h] at hz
    exact hz
  · exact weight_one_zero hp
  · exact weight_two_zero hp

end LowWeight

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace GenericIhara
open AssociativeElimination UniversalEmbedding WordGrading LieGrading
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]

theorem above_zero {wt : α → ℕ} (p : A R α) : p∈above wt 0 :=
  mem_space (fun _ _ => Nat.zero_le _)

theorem tree_depth (u : UniversalEmbedding.Tree Bool) :
    u=.leaf false ∨ embed (u.eval : FreeLieAlgebra R Bool)∈above depth 1 := by
  induction u with
  | leaf a =>
    cases a with
    | false => exact Or.inl rfl
    | true =>
      right
      simp only [Tree.eval,AssociativeElimination.embed_of]
      exact word_mem (R:=R) (FreeMonoid.of true) (show 1≤degree depth (FreeMonoid.of true) from le_rfl)
  | node u v hu hv =>
    right
    rcases hu with rfl|hu
    · rcases hv with rfl|hv
      · simp only [Tree.eval,lie_self,map_zero,Submodule.zero_mem]
      · simpa only [Tree.eval,LieHom.map_lie,Nat.zero_add] using above_lie (above_zero (embed (Tree.eval (R:=R) (.leaf false)))) hv
    · simpa only [Tree.eval,LieHom.map_lie,Nat.add_zero] using above_lie hu (above_zero (embed (Tree.eval (R:=R) v)))

theorem homogeneous_depth {n : ℕ} (hn : 1<n) {p : FreeLieAlgebra R Bool}
    (hp : p∈homogeneousLie (fun _ => 1) n) : embed p∈above depth 1 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,hu,rfl⟩ := hp
    rcases tree_depth (R:=R) u with rfl|h
    · simp only [treeDegree_leaf] at hu
      omega
    · exact h
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using (above depth 1).add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using (above depth 1).smul_mem c hp

theorem evalIhara_homogeneous (wt : α → ℕ) (f : α → FreeLieAlgebra R Bool)
    (hf : ∀ a,embed (f a)∈homogeneous (fun _ => 1) (wt a))
    {n : ℕ} {p : FreeLieAlgebra R α} (hp : p∈homogeneousLie wt n) :
    embed (evalIhara f p)∈homogeneous (fun _ => 1) n := by
  have ht : ∀ u : UniversalEmbedding.Tree α,
      embed (evalIhara f u.eval)∈homogeneous (fun _ => 1) (treeDegree wt u) := by
    intro u
    induction u with
    | leaf a => simpa only [Tree.eval,evalIhara_of,treeDegree_leaf] using hf a
    | node u v hu hv =>
      simpa only [Tree.eval,evalIhara_lie,treeDegree_node] using ihara_homogeneous hu hv
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨u,hu,rfl⟩ := hp; simpa only [hu] using ht u
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using (homogeneous _ _).add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using (homogeneous _ _).smul_mem c hp

theorem evalIhara_depth (f : α → FreeLieAlgebra R Bool)
    (hf : ∀ a,embed (f a)∈above depth 1)
    {n : ℕ} {p : FreeLieAlgebra R α} (hp : p∈homogeneousLie (fun _ => 1) n) :
    embed (evalIhara f p)∈above depth n := by
  have ht : ∀ u : UniversalEmbedding.Tree α,
      embed (evalIhara f u.eval)∈above depth (treeDegree (fun _ => 1) u) := by
    intro u
    induction u with
    | leaf a => simpa only [Tree.eval,evalIhara_of,treeDegree_leaf] using hf a
    | node u v hu hv =>
      simpa only [Tree.eval,evalIhara_lie,treeDegree_node] using ihara_above hu hv
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨u,hu,rfl⟩ := hp; simpa only [hu] using ht u
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using (above _ _).add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using (above _ _).smul_mem c hp

theorem degree_depthOneWord (n : ℕ) : degree depth (depthOneWord n)=1 := by
  have h : ∀ n,degree depth (FreeMonoid.of false^n)=0 := by
    intro n
    induction n with
    | zero => simp
    | succ n hn => simp [pow_succ,hn,depth]
  simp [depthOneWord,h,depth]

theorem depthOne_zero {p : FreeLieAlgebra R Bool} {r : ℕ} (hr : 1<r)
    (hp : embed p∈above depth r) (n : ℕ) : (embed p).coeff (depthOneWord n)=0 := by
  exact coeff_support hp _ (by rw [degree_depthOneWord]; omega)

end GenericIhara

section

end

section

end

end DeligneDrinfeld

end

end OAI

end












section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace LatticeDimension
open scoped TensorProduct
variable {ι F : Type*} [Field F]

theorem reduction_lift (E : Submodule ℚ (ι → ℚ))
    (hs : Function.Surjective (Int.cast : ℤ → F)) {v : ι → F}
    (hv : v∈reduction F E) : ∃ u : lattice E, (fun i => (u.val i : F))=v := by
  obtain ⟨w,rfl⟩ := hv
  induction w using TensorProduct.induction_on with
  | zero => refine ⟨0, ?_⟩; ext i; simp
  | tmul c u =>
    obtain ⟨z,rfl⟩ := hs c
    refine ⟨z • u,?_⟩
    ext i
    rw [scalarMap_tmul]
    simp only [Submodule.coe_smul,Pi.smul_apply,zsmul_eq_mul,Int.cast_mul]
    exact mul_comm _ _
  | add w w' hw hw' =>
    obtain ⟨u,hu⟩ := hw
    obtain ⟨u',hu'⟩ := hw'
    refine ⟨u+u',?_⟩
    rw [map_add,←hu,←hu']
    ext i
    simp

theorem reduction_lift_two (E : Submodule ℚ (ι → ℚ)) {v : ι → ZMod 2}
    (hv : v∈reduction (ZMod 2) E) : ∃ u : lattice E,(fun i => (u.val i : ZMod 2))=v := by
  apply reduction_lift E ?_ hv
  intro c
  exact ⟨c.val,by simp⟩
theorem reduction_mono {E E' : Submodule ℚ (ι → ℚ)} (h : E≤E') :
    reduction F E≤reduction F E' := by
  rintro v ⟨w,rfl⟩
  induction w using TensorProduct.induction_on with
  | zero => first | rfl | exact Submodule.zero_mem _ | simp
  | tmul c u =>
    refine ⟨c ⊗ₜ (⟨u.val,h u.property⟩ : lattice E'),?_⟩
    simp only [scalarMap_tmul]
  | add w w' hw hw' => simpa only [map_add] using (reduction F E').add_mem hw hw'
end LatticeDimension

namespace SaturatedSolutions
open AssociativeElimination UniversalEmbedding WordGrading
open ReducedDimension
abbrev K := ZMod 2
variable (n : ℕ) (E : Submodule ℚ (Wn n))

theorem image_le : image n E≤RationalBound.image n := by
  rintro v ⟨p,_,rfl⟩
  exact ⟨p,rfl⟩

def reduction : Submodule K (solutions n) :=
  (LatticeDimension.reduction K (image n E)).comap (RationalBound.reducedCoordinates n)

theorem reduction_image_le (hn : 2<n) :
    LatticeDimension.reduction K (image n E)≤RationalBound.reducedImage n :=
  (LatticeDimension.reduction_mono (image_le n E)).trans (RationalBound.reduction_le n hn)

def coordReduction : reduction n E →ₗ[K] LatticeDimension.reduction K (image n E) :=
  ((RationalBound.reducedCoordinates n).comp (reduction n E).subtype).codRestrict _ (fun p => p.property)

theorem coordReduction_injective : Function.Injective (coordReduction n E) := by
  intro p q h
  apply Subtype.ext
  apply RationalBound.reducedCoordinates_injective n
  exact congrArg Subtype.val h

theorem coordReduction_surjective (hn : 2<n) : Function.Surjective (coordReduction n E) := by
  intro v
  obtain ⟨p,hp⟩ := reduction_image_le n E hn v.property
  let pR : reduction n E := ⟨p,by
    change RationalBound.reducedCoordinates n p∈LatticeDimension.reduction K (image n E)
    rw [hp]
    exact v.property⟩
  exact ⟨pR,Subtype.ext hp⟩

theorem finrank_reduction (hn : 2<n) : Module.finrank K (reduction n E)=Module.finrank ℚ E := by
  let eqv := LinearEquiv.ofBijective (coordReduction n E)
    ⟨coordReduction_injective n E,coordReduction_surjective n E hn⟩
  have he := eqv.finrank_eq
  rw [LatticeDimension.finrank_reduction] at he
  have hi : Function.Injective ((RationalBound.coordinates n).comp E.subtype) :=
    (RationalBound.coordinates_injective n).comp Subtype.val_injective
  have hq := (LinearEquiv.ofInjective _ hi).finrank_eq
  have hr : ((RationalBound.coordinates n).comp E.subtype).range=image n E := by
    rw [LinearMap.range_comp,Submodule.range_subtype]
    rfl
  rw [hr] at hq
  exact he.trans hq.symm

def filtration (hn : 1<n) (r : ℕ) : Submodule K (reduction n E) :=
  (ReducedDimension.filtration n hn r).comap (reduction n E).subtype

def inclusionFiltration (hn : 1<n) (r : ℕ) :
    filtration n E hn r →ₗ[K] ReducedDimension.filtration n hn r :=
  ((reduction n E).subtype.comp (filtration n E hn r).subtype).codRestrict _ (fun p => p.property)

def gradedMap (hn : 2<n) (r : ℕ) : filtration n E (by omega) r →ₗ[K] oddPiece n r :=
  (ReducedDimension.gradedMap n hn r).comp (inclusionFiltration n E (by omega) r)

theorem graded_kernel (hn : 2<n) (r : ℕ) (p : filtration n E (by omega) r)
    (hz : gradedMap n E hn r p=0) : p.val∈filtration n E (by omega) (r+1) :=
  ReducedDimension.graded_kernel n hn r (inclusionFiltration n E (by omega) r p) hz

theorem filtration_zero (hn : 1<n) : filtration n E hn 0=⊤ := by
  unfold filtration
  rw [ReducedDimension.filtration_zero,Submodule.comap_top]

theorem filtration_terminal (hn : 1<n) : filtration n E hn (n+1)=⊥ := by
  unfold filtration
  rw [ReducedDimension.filtration_terminal]
  exact LinearMap.ker_eq_bot_of_injective Subtype.val_injective

theorem graded_surjective (hn : 2<n) (he : Module.finrank ℚ E=Module.finrank ℚ (Fn n))
    (r : ℕ) (hr : r≤n) : Function.Surjective (gradedMap n E hn r) := by
  apply FiltrationDimension.surjective_of_equality (filtration n E (by omega))
    (gradedMap n E hn) (graded_kernel n E hn) (n+1) (filtration_terminal n E (by omega)) ?_ r (by omega)
  rw [filtration_zero,finrank_top,finrank_reduction n E hn,he]
  change Module.finrank ℚ (weightPiece oddWeight n)=_
  rw [LieGrading.weightPiece_eq,←LieDimension.finrank_homogeneous K oddWeight n,
    LieGrading.finrank_decomposition K oddWeight (fun _ => 1) n n (ReducedDimension.odd_length_bound n)]
  exact Fin.sum_univ_eq_sum_range (fun r => Module.finrank K (oddPiece n r)) (n+1)

theorem lattice_lift (u : LatticeDimension.lattice (image n E)) :
    ∃ q : LieGrading.homogeneousLie (R:=ℤ) RationalBound.wt n,
      LieDimension.coordinates ℤ RationalBound.wt n q=u.val ∧
      ∃ hq : (LieDimension.castHom (R:=ℚ) q).val∈Wn n,
        (⟨(LieDimension.castHom (R:=ℚ) q).val,hq⟩ : Wn n)∈E := by
  obtain ⟨p,hpE,hp⟩ := u.property
  have hu : u.val∈LatticeDimension.lattice (LieDimension.image ℚ RationalBound.wt n) :=
    ⟨RationalBound.toHom n p,hp⟩
  rw [LieDimension.lattice_image] at hu
  obtain ⟨q,hq⟩ := hu
  have heq : LieDimension.castHom (R:=ℚ) q=RationalBound.toHom n p := by
    apply LieDimension.coordinates_injective ℚ RationalBound.wt n
    ext w
    rw [LieDimension.coordinates_castHom]
    change ((LieDimension.coordinates ℤ RationalBound.wt n q) w : ℚ)=RationalBound.coordinates n p w
    rw [hq,congrFun hp w]
    rfl
  refine ⟨q,hq,?_,?_⟩
  · rw [heq]
    exact p.property
  · have hval : (LieDimension.castHom (R:=ℚ) q).val=p.val := congrArg Subtype.val heq
    have hsub : (⟨(LieDimension.castHom (R:=ℚ) q).val, by rw [heq]; exact p.property⟩ : Wn n)=p := Subtype.ext hval
    rw [hsub]
    exact hpE

theorem reduction_lift (hn : 2<n) (p : reduction n E) :
    ∃ q : LieGrading.homogeneousLie (R:=ℤ) RationalBound.wt n,
      (LieDimension.castHom (R:=K) q).val=p.val.val ∧
      ∃ hq : (LieDimension.castHom (R:=ℚ) q).val∈Wn n,
        (⟨(LieDimension.castHom (R:=ℚ) q).val,hq⟩ : Wn n)∈E := by
  obtain ⟨u,hu⟩ := LatticeDimension.reduction_lift_two (image n E) p.property
  obtain ⟨q,hq,hW,hE⟩ := lattice_lift n E u
  refine ⟨q,?_,hW,hE⟩
  let qS := RationalBound.reduceLattice n hn q hW.1
  have he : qS=p.val := by
    apply RationalBound.reducedCoordinates_injective n
    ext w
    change (LieDimension.coordinates K RationalBound.wt n (LieDimension.castHom q)) w=_
    rw [LieDimension.coordinates_castHom,hq]
    exact congrFun hu w
  exact congrArg Subtype.val he

end SaturatedSolutions

namespace LieGrading
open AssociativeElimination UniversalEmbedding WordGrading
variable {R α : Type*} [CommRing R]

theorem eval_homogeneous (wt : α → ℕ) (t : UniversalEmbedding.Tree α) :
    (t.eval : FreeLieAlgebra R α)∈homogeneousLie wt (treeDegree wt t) :=
  Submodule.subset_span ⟨t,rfl,rfl⟩

theorem piece_tree (wt : α → ℕ) (r : ℕ) (t : UniversalEmbedding.Tree α) :
    piece wt r (t.eval : FreeLieAlgebra R α)=if treeDegree wt t=r then t.eval else 0 :=
  piece_homogeneous (eval_homogeneous wt t) r

def biTreeSpan (wa wb : α → ℕ) (n r : ℕ) : Submodule R (FreeLieAlgebra R α) :=
  Submodule.span R {p | ∃ t : UniversalEmbedding.Tree α,treeDegree wa t=n ∧ treeDegree wb t=r ∧ t.eval=p}

theorem biTreeSpan_eq (wa wb : α → ℕ) (n r : ℕ) :
    biTreeSpan (R:=R) wa wb n r=biPiece wa wb n r := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨t,hn,hr,rfl⟩
    exact ⟨hn ▸ eval_homogeneous wa t,hr ▸ eval_homogeneous wb t⟩
  · intro p hp
    have he : piece wb r p=p := by rw [piece_homogeneous hp.2,if_pos rfl]
    rw [←he]
    have hw : p∈homogeneousLie wa n := hp.1
    clear hp he
    induction hw using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨t,ht,rfl⟩ := hp
      rw [piece_tree]
      split_ifs with h
      · exact Submodule.subset_span ⟨t,ht,h,rfl⟩
      · exact Submodule.zero_mem _
    | zero =>
      have hz : piece wb r (0 : FreeLieAlgebra R α)=0 := (projection wb r).map_zero
      rw [hz]
      exact Submodule.zero_mem _
    | add p q _ _ hp hq => rw [piece_add]; exact Submodule.add_mem _ hp hq
    | smul c p _ hp => rw [piece_smul]; exact Submodule.smul_mem _ c hp

theorem treeDegree_pos {wt : α → ℕ} (h : ∀ a,0<wt a) (t : UniversalEmbedding.Tree α) : 0<treeDegree wt t := by
  induction t with
  | leaf a => simpa only [treeDegree_leaf] using h a
  | node t u ht hu => rw [treeDegree_node]; omega

theorem treeDegree_lower {wt : α → ℕ} {m : ℕ} (h : ∀ a,m≤wt a) (t : UniversalEmbedding.Tree α) : m≤treeDegree wt t := by
  induction t with
  | leaf a => simpa only [treeDegree_leaf] using h a
  | node t u ht hu => rw [treeDegree_node]; omega

theorem leaf_degree_le {wt : α → ℕ} {t : UniversalEmbedding.Tree α} {a : α}
    (ha : a∈t.leaves) : wt a≤treeDegree wt t := by
  induction t with
  | leaf b =>
    have hab : a=b := List.mem_singleton.mp ha
    simpa only [hab,treeDegree_leaf] using le_refl (wt b)
  | node t u ht hu =>
    rw [Tree.leaves,List.mem_append] at ha
    rw [treeDegree_node]
    rcases ha with h|h
    · exact (ht h).trans (Nat.le_add_right _ _)
    · exact (hu h).trans (Nat.le_add_left _ _)

theorem leaf_degree_lt {wt : α → ℕ} (hwt : ∀ a,0<wt a)
    {t : UniversalEmbedding.Tree α} (ht : 1<treeDegree (fun _ => 1) t)
    {a : α} (ha : a∈t.leaves) : wt a<treeDegree wt t := by
  cases t with
  | leaf b => simp only [treeDegree_leaf] at ht; omega
  | node t u =>
    rw [Tree.leaves,List.mem_append] at ha
    rw [treeDegree_node]
    rcases ha with h|h
    · have hle := leaf_degree_le (wt:=wt) h
      have hpos := treeDegree_pos hwt u
      omega
    · have hle := leaf_degree_le (wt:=wt) h
      have hpos := treeDegree_pos hwt t
      omega

end LieGrading

namespace NormalizedFamily
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open ImageBound LieGrading RowTwo RowKernel ExactPentagon
attribute [local instance] LieRing.ofAssociativeRing

variable (g : Data)

def treeSolution (t : UniversalEmbedding.Tree ℕ) : ReducedDimension.solutions (treeDegree oddWeight t) :=
  ⟨GenericIhara.evalIhara g.value t.eval,g.solution _ _ (eval_homogeneous oddWeight t)⟩

end NormalizedFamily

namespace Triangular
variable {R : Type*} [Semiring R] {N : ℕ}
    {V : Fin N → Type*} [∀ i,AddCommGroup (V i)] [∀ i,Module R (V i)]
    {W : Type*} [AddCommMonoid W] [Module R W]
    {Z : Fin N → Type*} [∀ i,AddCommGroup (Z i)] [∀ i,Module R (Z i)]

def assemble (f : ∀ i,V i →ₗ[R] W) : (∀ i,V i) →ₗ[R] W :=
  ∑ i,(f i).comp (LinearMap.proj i)

theorem assemble_apply (f : ∀ i,V i →ₗ[R] W) (v : ∀ i,V i) : assemble f v=∑ i,f i (v i) := by
  simp [assemble]

theorem assemble_injective (f : ∀ i,V i →ₗ[R] W) (π : ∀ i,W →ₗ[R] Z i)
    (diag : ∀ i,Function.Injective ((π i).comp (f i)))
    (upper : ∀ i j,i < j → ∀ v,π i (f j v)=0) : Function.Injective (assemble f) := by
  classical
  intro v w hvw
  have aux : ∀ n (i : Fin N),i.val=n → v i=w i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      apply diag i
      change π i (f i (v i))=π i (f i (w i))
      have h := congrArg (π i) hvw
      simp only [assemble_apply,map_sum] at h
      have hv : (∑ j,π i (f j (v j))) =
          (∑ j∈(Finset.univ.filter (fun j => j < i)),π i (f j (v j))) + π i (f i (v i)) := by
        classical
        rw [←Finset.sum_filter_add_sum_filter_not (s:=Finset.univ) (p:=fun j => j < i)]
        congr 1
        apply Finset.sum_eq_single i
        · intro j hj hji
          have hle : i ≤ j := le_of_not_gt (Finset.mem_filter.mp hj).2
          exact upper i j (lt_of_le_of_ne hle (Ne.symm hji)) (v j)
        · simp
      have hw : (∑ j,π i (f j (w j))) =
          (∑ j∈(Finset.univ.filter (fun j => j < i)),π i (f j (w j))) + π i (f i (w i)) := by
        classical
        rw [←Finset.sum_filter_add_sum_filter_not (s:=Finset.univ) (p:=fun j => j < i)]
        congr 1
        apply Finset.sum_eq_single i
        · intro j hj hji
          have hle : i ≤ j := le_of_not_gt (Finset.mem_filter.mp hj).2
          exact upper i j (lt_of_le_of_ne hle (Ne.symm hji)) (w j)
        · simp
      have he : (∑ j∈(Finset.univ.filter (fun j => j < i)),π i (f j (v j))) =
          ∑ j∈(Finset.univ.filter (fun j => j < i)),π i (f j (w j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih j.val (by have hj' := (Finset.mem_filter.mp hj).2; change j.val < i.val at hj'; omega) j rfl]
      rw [hv,hw,he] at h
      exact add_left_cancel h
  funext i
  exact aux i.val i rfl

end Triangular

namespace NormalizedFamily

section
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading
open ImageBound LieGrading RowTwo RowKernel ExactPentagon
attribute [local instance] LieRing.ofAssociativeRing
variable (g : Data)

def valueMap (n : ℕ) : homogeneousLie (R:=K) oddWeight n →ₗ[K] ReducedDimension.solutions n :=
  ((GenericIhara.evalIhara g.value).comp (homogeneousLie oddWeight n).subtype).codRestrict _
    (fun p => g.solution n p.val p.property)

def repMap (n : ℕ) (hn : 1<n) : homogeneousLie (R:=K) oddWeight n →ₗ[K] FreeLieAlgebra K Slot :=
  (ReducedDimension.representationMap n hn).comp (valueMap g n)

def leadingLinear (r : ℕ) : FreeLieAlgebra K Slot →ₗ[K] A K Bool :=
  (OreShift.eraseShift 0).toLinearMap.comp ((WordGrading.piece bCount r).comp embed.toLinearMap)

theorem leadingLinear_apply (r : ℕ) (p : FreeLieAlgebra K Slot) :
    leadingLinear r p=embed (leading r p) := (embed_leading r p).symm

theorem repMap_bihomogeneous {n r : ℕ} (hn : 1<n) (p : biPiece (R:=K) oddWeight (fun _ => 1) n r)
    (hactive : ∀ t : UniversalEmbedding.Tree ℕ,treeDegree oddWeight t=n →
      treeDegree (fun _ => 1) t=r → ∀ k∈t.leaves,g.active k) :
    embed (repMap g n hn ⟨p.val,p.property.1⟩)∈above bCount r ∧
      leadingLinear r (repMap g n hn ⟨p.val,p.property.1⟩)=positiveInput (embed p.val) := by
  obtain ⟨q,hq,hqr,hql⟩ := bihomogeneous_leading g p.property hactive
  have he : repMap g n hn ⟨p.val,p.property.1⟩=q := by
    apply under_injective
    exact (ReducedDimension.representation_under n hn (valueMap g n ⟨p.val,p.property.1⟩)).trans hq.symm
  rw [he,leadingLinear_apply]
  exact ⟨hqr,hql⟩

def oldPiece (n r : ℕ) : Submodule K (FreeLieAlgebra K ℕ) :=
  if 1<r then biPiece oddWeight (fun _ => 1) n r else ⊥

theorem oldPiece_le (n r : ℕ) : oldPiece n r≤homogeneousLie oddWeight n := by
  unfold oldPiece
  split_ifs
  · exact inf_le_left
  · exact bot_le

instance finite_oldPiece (n r : ℕ) : Module.Finite K (oldPiece n r) :=
  Module.Finite.of_injective (Submodule.inclusion (oldPiece_le n r)) (Submodule.inclusion_injective _)

def oldMap (n r : ℕ) : oldPiece n r →ₗ[K] ReducedDimension.solutions n :=
  (valueMap g n).comp (Submodule.inclusion (oldPiece_le n r))

def solutionLeading (n : ℕ) (hn : 1<n) (r : ℕ) : ReducedDimension.solutions n →ₗ[K] A K Bool :=
  (leadingLinear r).comp (ReducedDimension.representationMap n hn)

theorem oldMap_leading {n r : ℕ} (hn : 1<n) (hr : 1<r)
    (ha : ∀ k,oddWeight k<n → g.active k) (p : oldPiece n r) :
    embed (ReducedDimension.representationMap n hn (oldMap g n r p))∈above bCount r ∧
      solutionLeading n hn r (oldMap g n r p)=positiveInput (embed p.val) := by
  have hp : p.val∈biPiece oddWeight (fun _ => 1) n r := by
    have h := p.property
    simpa only [oldPiece,if_pos hr] using h
  exact repMap_bihomogeneous g hn ⟨p.val,hp⟩ (by
    intro t htn htr k hk
    apply ha k
    have hlt := leaf_degree_lt (wt:=oddWeight) (by intro k; simp [oddWeight]) (by omega : 1<treeDegree (fun _ => 1) t) hk
    simpa only [htn] using hlt)

theorem oldMap_low {n r : ℕ} (hr : ¬1<r) (p : oldPiece n r) : p=0 := by
  apply Subtype.ext
  change p.val=0
  have h := p.property
  simpa only [oldPiece,if_neg hr,Submodule.mem_bot] using h

theorem old_assemble_injective (n : ℕ) (hn : 1<n) (ha : ∀ k,oddWeight k<n → g.active k) :
    Function.Injective (Triangular.assemble (fun r : Fin (n+1) => oldMap g n r.val)) := by
  apply Triangular.assemble_injective _ (fun r => solutionLeading n hn r.val)
  · intro r p q hpq
    by_cases hr : 1<r.val
    · have hp := (oldMap_leading g hn hr ha p).2
      have hq := (oldMap_leading g hn hr ha q).2
      apply Subtype.ext
      apply UniversalEmbedding.injective
      apply positiveInput_injective
      exact hp.symm.trans (hpq.trans hq)
    · rw [oldMap_low hr p,oldMap_low hr q]
  · intro r s hrs p
    by_cases hs : 1<s.val
    · have hp := (oldMap_leading g hn hs ha p).1
      change OreShift.eraseShift 0 (project (fun w => degree bCount w=r.val) (embed _))=0
      rw [project_eq_zero hp ?_,map_zero]
      intro w hw hwr
      change s.val≤degree bCount w at hw
      change degree bCount w=r.val at hwr
      have hrs' : r.val<s.val := hrs
      omega
    · rw [oldMap_low hs p,map_zero,map_zero]

end

open AssociativeElimination UniversalEmbedding WordGrading ImageBound LieGrading RowKernel

variable (g : Data)

def fullMap (n r : ℕ) : biPiece (R:=K) oddWeight (fun _ => 1) n r →ₗ[K] ReducedDimension.solutions n :=
  (valueMap g n).comp (Submodule.inclusion inf_le_left)

theorem fullMap_leading {n r : ℕ} (hn : 1<n) (ha : ∀ k,g.active k)
    (p : biPiece (R:=K) oddWeight (fun _ => 1) n r) :
    embed (ReducedDimension.representationMap n hn (fullMap g n r p))∈above bCount r ∧
      solutionLeading n hn r (fullMap g n r p)=positiveInput (embed p.val) :=
  repMap_bihomogeneous g hn p (by intros; apply ha)

theorem full_assemble_injective (n : ℕ) (hn : 1<n) (ha : ∀ k,g.active k) :
    Function.Injective (Triangular.assemble (fun r : Fin (n+1) => fullMap g n r.val)) := by
  apply Triangular.assemble_injective _ (fun r => solutionLeading n hn r.val)
  · intro r p q hpq
    apply Subtype.ext
    apply UniversalEmbedding.injective
    apply positiveInput_injective
    exact (fullMap_leading g hn ha p).2.symm.trans (hpq.trans (fullMap_leading g hn ha q).2)
  · intro r s hrs p
    have hp := (fullMap_leading g hn ha p).1
    change OreShift.eraseShift 0 (project (fun w => degree bCount w=r.val) (embed _))=0
    rw [project_eq_zero hp ?_,map_zero]
    intro w hw hwr
    change s.val≤degree bCount w at hw
    change degree bCount w=r.val at hwr
    have hrs' : r.val<s.val := hrs
    omega

theorem valueMap_injective (n : ℕ) (hn : 1<n) (ha : ∀ k,g.active k) :
    Function.Injective (valueMap g n) := by
  intro p q hpq
  have he (v : homogeneousLie (R:=K) oddWeight n) :
      Triangular.assemble (fun r : Fin (n+1) => fullMap g n r.val)
        (components oddWeight (fun _ => 1) n n v)=valueMap g n v := by
    have h := assemble_components oddWeight (fun _ => 1) n n (ReducedDimension.odd_length_bound n) v
    rw [Triangular.assemble_apply]
    calc
      _ = valueMap g n (assemble oddWeight (fun _ => 1) n n
          (components oddWeight (fun _ => 1) n n v)) := by
        change (∑ r : Fin (n+1),(valueMap g n) ⟨_,_⟩)=(valueMap g n) ⟨∑ r : Fin (n+1),_,_⟩
        rw [←map_sum]
        congr 1
        apply Subtype.ext
        simp only [Submodule.coe_sum]
        rfl
      _ = valueMap g n v := congrArg (valueMap g n) h
  have hc := full_assemble_injective g n hn ha ((he p).trans (hpq.trans (he q).symm))
  have h := congrArg (assemble oddWeight (fun _ => 1) n n) hc
  simpa only [assemble_components oddWeight (fun _ => 1) n n (ReducedDimension.odd_length_bound n)] using h

end NormalizedFamily

namespace GenericIhara
variable {R α : Type*} [CommRing R]

theorem cast_D (p q : FreeLieAlgebra ℤ Bool) :
    IntegralBaseChange.lie (S:=R) (D p q)=D (IntegralBaseChange.lie p) (IntegralBaseChange.lie q) := by
  induction q using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [D]
  | ha q r hq hr => simp only [map_add,hq,hr]
  | hs c q hq =>
    change IntegralBaseChange.lie ((D p).toLinearMap (c • q)) =
      (D (IntegralBaseChange.lie p)).toLinearMap (IntegralBaseChange.lie (c • q))
    simp only [map_zsmul]
    exact congrArg (fun v => c • v) hq
  | hl q r hq hr => simp only [LieDerivation.apply_lie_eq_add,LieHom.map_lie,map_add,hq,hr]

theorem cast_ihara (p q : FreeLieAlgebra ℤ Bool) :
    IntegralBaseChange.lie (S:=R) (ihara p q)=ihara (IntegralBaseChange.lie p) (IntegralBaseChange.lie q) := by
  simp only [ihara,map_add,map_sub,LieHom.map_lie,cast_D]

theorem cast_evalIhara (f : α → FreeLieAlgebra ℤ Bool) (p : FreeLieAlgebra ℤ α) :
    IntegralBaseChange.lie (S:=R) (evalIhara f p)=
      evalIhara (fun a => IntegralBaseChange.lie (f a)) (IntegralBaseChange.lie p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp only [map_add,hp,hq]
  | hs c p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [evalIhara_lie,LieHom.map_lie,cast_ihara,hp,hq]

end GenericIhara

namespace IntegralFamily
open LieGrading AssociativeElimination UniversalEmbedding WordGrading
open scoped TensorProduct
abbrev K := ZMod 2

variable (V : Values)

structure Family where
  value : ℕ → FreeLieAlgebra ℤ Bool
  homogeneous : ∀ k,value k∈homogeneousLie (fun _ => 1) (oddWeight k)
  member : ∀ k,IntegralBaseChange.lie (S:=ℚ) (value k)∈V.space

variable {V} (f : Family V)

def cast (R : Type*) [CommRing R] (k : ℕ) : FreeLieAlgebra R Bool :=
  IntegralBaseChange.lie (f.value k)

theorem cast_homogeneous (R : Type*) [CommRing R] (k : ℕ) :
    cast f R k∈homogeneousLie (fun _ => 1) (oddWeight k) :=
  (LieDimension.castHom (R:=R) ⟨f.value k,f.homogeneous k⟩).property

theorem rational_mem (p : FreeLieAlgebra ℚ ℕ) : GenericIhara.evalIhara (cast f ℚ) p∈V.space := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg k => simpa only [GenericIhara.evalIhara_of,cast] using f.member k
  | ha p q hp hq => rw [map_add]; exact V.space.add_mem hp hq
  | hs c p hp => rw [map_smul]; exact V.space.smul_mem c hp
  | hl p q hp hq => rw [GenericIhara.evalIhara_lie,GenericIhara.rational_ihara]; exact V.bracket hp hq

theorem eval_homogeneous (R : Type*) [CommRing R] {n : ℕ} {p : FreeLieAlgebra R ℕ}
    (hp : p∈homogeneousLie oddWeight n) :
    GenericIhara.evalIhara (cast f R) p∈homogeneousLie (fun _ => 1) n := by
  apply homogeneous_iff.mpr
  exact GenericIhara.evalIhara_homogeneous oddWeight _ (fun k => homogeneousLie_embed (cast_homogeneous f R k)) hp

theorem integral_eval_homogeneous {n : ℕ} {p : FreeLieAlgebra ℤ ℕ}
    (hp : p∈homogeneousLie oddWeight n) :
    GenericIhara.evalIhara f.value p∈homogeneousLie (fun _ => 1) n := by
  apply homogeneous_iff.mpr
  exact GenericIhara.evalIhara_homogeneous oddWeight _ (fun k => homogeneousLie_embed (f.homogeneous k)) hp

theorem integral_reduction_mem {n : ℕ} (E : Submodule ℚ (Wn n))
    (q : homogeneousLie (R:=ℤ) RationalBound.wt n)
    (hW : (LieDimension.castHom (R:=ℚ) q).val∈Wn n)
    (hE : (⟨(LieDimension.castHom (R:=ℚ) q).val,hW⟩ : Wn n)∈E)
    (p : ReducedDimension.solutions n)
    (hp : (LieDimension.castHom (R:=K) q).val=p.val) :
    p∈SaturatedSolutions.reduction n E := by
  let u : LatticeDimension.lattice (SaturatedSolutions.image n E) :=
    ⟨LieDimension.coordinates ℤ RationalBound.wt n q,by
      refine ⟨⟨(LieDimension.castHom (R:=ℚ) q).val,hW⟩,hE,?_⟩
      ext w
      exact LieDimension.coordinates_castHom q w⟩
  refine ⟨(1 : K) ⊗ₜ[ℤ] u,?_⟩
  ext w
  rw [LatticeDimension.scalarMap_tmul]
  change (LieDimension.coordinates ℤ RationalBound.wt n q w : K)*1=(embed p.val).coeff w.val
  rw [mul_one,←LieDimension.coordinates_castHom,LieDimension.coordinates_apply,hp]

theorem tree_rational_W (t : UniversalEmbedding.Tree ℕ) :
    IntegralBaseChange.lie (S:=ℚ) (GenericIhara.evalIhara f.value (t.eval (R:=ℤ)))∈W := by
  rw [GenericIhara.cast_evalIhara,LieDimension.cast_eval]
  exact V.le_W (rational_mem f t.eval)

theorem reduced_solution {n : ℕ} {p : FreeLieAlgebra K ℕ}
    (hp : p∈homogeneousLie oddWeight n) :
    GenericIhara.evalIhara (cast f K) p∈ReducedDimension.solutions n := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,ht,rfl⟩ := hp
    have hn : 2<n := by
      have h := treeDegree_lower (m:=3) (wt:=oddWeight) (by intro k; simp [oddWeight]) t
      omega
    let q : homogeneousLie (R:=ℤ) RationalBound.wt n :=
      ⟨GenericIhara.evalIhara f.value t.eval,integral_eval_homogeneous f (ht ▸ LieGrading.eval_homogeneous oddWeight t)⟩
    have hq := (RationalBound.reduceLattice n hn q (tree_rational_W f t)).property
    change IntegralBaseChange.lie (S:=K) (GenericIhara.evalIhara f.value t.eval)∈_ at hq
    rwa [GenericIhara.cast_evalIhara,LieDimension.cast_eval] at hq
  | zero => simp
  | add p q _ _ hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
  | smul c p _ hp => rw [map_smul]; exact Submodule.smul_mem _ c hp

def reducedValue (n : ℕ) : homogeneousLie (R:=K) oddWeight n →ₗ[K] ReducedDimension.solutions n :=
  ((GenericIhara.evalIhara (cast f K)).comp (homogeneousLie oddWeight n).subtype).codRestrict _
    (fun p => reduced_solution f p.property)

theorem reduced_mem {n : ℕ} (p : homogeneousLie (R:=K) oddWeight n) :
    reducedValue f n p∈SaturatedSolutions.reduction n (piece V n) := by
  have ht : ∀ (t : UniversalEmbedding.Tree ℕ) (ht : treeDegree oddWeight t=n),
      reducedValue f n ⟨t.eval,ht ▸ LieGrading.eval_homogeneous oddWeight t⟩∈SaturatedSolutions.reduction n (piece V n) := by
    intro t ht
    let q : homogeneousLie (R:=ℤ) RationalBound.wt n :=
      ⟨GenericIhara.evalIhara f.value t.eval,integral_eval_homogeneous f (ht ▸ LieGrading.eval_homogeneous oddWeight t)⟩
    have he : (LieDimension.castHom (R:=ℚ) q).val=GenericIhara.evalIhara (cast f ℚ) t.eval := by
      exact (GenericIhara.cast_evalIhara f.value t.eval).trans (congrArg _ (LieDimension.cast_eval t))
    have hW : (LieDimension.castHom (R:=ℚ) q).val∈Wn n := by
      constructor
      · rw [he]; exact V.le_W (rational_mem f t.eval)
      · change _∈weightPiece RationalBound.wt n
        rw [weightPiece_eq]; exact (LieDimension.castHom (R:=ℚ) q).property
    apply integral_reduction_mem (piece V n) q hW ?_ _ ?_
    · change (LieDimension.castHom (R:=ℚ) q).val∈V.space
      rw [he]; exact rational_mem f t.eval
    · change IntegralBaseChange.lie (S:=K) (GenericIhara.evalIhara f.value t.eval)=_
      rw [GenericIhara.cast_evalIhara,LieDimension.cast_eval]
      rfl
  have hp := p.property
  change p.val∈homogeneousLie oddWeight n at hp
  have hh : ∀ v (hv : v∈homogeneousLie (R:=K) oddWeight n),
      reducedValue f n ⟨v,hv⟩∈SaturatedSolutions.reduction n (piece V n) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨t,htree,rfl⟩ := hv; exact ht t htree
    | zero =>
      change reducedValue f n 0∈_
      rw [map_zero]
      exact Submodule.zero_mem _
    | add v w hv hw hi hj =>
      change reducedValue f n (⟨v,hv⟩+⟨w,hw⟩)∈_
      rw [map_add]
      exact (SaturatedSolutions.reduction n (piece V n)).add_mem hi hj
    | smul c v hv hi =>
      change reducedValue f n (c • ⟨v,hv⟩)∈_
      rw [map_smul]
      exact (SaturatedSolutions.reduction n (piece V n)).smul_mem c hi
  exact hh p.val hp

end IntegralFamily

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace NormalizedFamily
open LieGrading UniversalEmbedding

theorem length_zero_piece (n : ℕ) : biPiece (R:=K) oddWeight (fun _ => 1) n 0=⊥ := by
  rw [←biTreeSpan_eq]
  apply le_antisymm ?_ bot_le
  apply Submodule.span_le.mpr
  rintro p ⟨t,_,ht,rfl⟩
  have h := treeDegree_pos (wt:=fun _ : ℕ => 1) (by intro; decide) t
  omega

theorem length_one_piece_le (k : ℕ) :
    biPiece (R:=K) oddWeight (fun _ => 1) (oddWeight k) 1≤
      Submodule.span K {FreeLieAlgebra.of K k} := by
  rw [←biTreeSpan_eq]
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,hr,rfl⟩
  cases t with
  | leaf j =>
    have hj : j=k := by
      simp only [treeDegree_leaf,oddWeight] at ht
      omega
    subst j
    exact Submodule.subset_span rfl
  | node t u =>
    have h₁ := treeDegree_pos (wt:=fun _ : ℕ => 1) (by intro; decide) t
    have h₂ := treeDegree_pos (wt:=fun _ : ℕ => 1) (by intro; decide) u
    simp only [treeDegree_node] at hr
    omega

theorem finrank_length_one_le (k : ℕ) :
    Module.finrank K (biPiece (R:=K) oddWeight (fun _ => 1) (oddWeight k) 1)≤1 := by
  have h := Submodule.finrank_mono (length_one_piece_le k)
  have h' := finrank_span_le_card (R:=K) ({FreeLieAlgebra.of K k} : Set (FreeLieAlgebra K ℕ))
  exact h.trans (by simpa using h')

abbrev OldDomain (n : ℕ) := (r : Fin (n+1)) → oldPiece n r.val

theorem finrank_odd_le (k : ℕ) :
    Module.finrank K (homogeneousLie (R:=K) oddWeight (oddWeight k))≤
      Module.finrank K (OldDomain (oddWeight k))+1 := by
  classical
  let n := oddWeight k
  rw [finrank_decomposition K oddWeight (fun _ => 1) n n (ReducedDimension.odd_length_bound n),Module.finrank_pi_fintype]
  have hterm (r : ℕ) :
      Module.finrank K (biPiece (R:=K) oddWeight (fun _ => 1) n r)≤
        Module.finrank K (oldPiece n r)+(if r=1 then 1 else 0) := by
    by_cases hr : 1<r
    · have he : oldPiece n r=biPiece (R:=K) oddWeight (fun _ => 1) n r := if_pos hr
      rw [he]
      split_ifs <;> omega
    · have he : oldPiece n r=⊥ := if_neg hr
      rw [he,finrank_bot,Nat.zero_add]
      by_cases hr1 : r=1
      · subst r
        rw [if_pos rfl]
        exact finrank_length_one_le k
      · have hr0 : r=0 := by omega
        subst r
        rw [length_zero_piece,finrank_bot]
        split_ifs <;> omega
  have hs := Finset.sum_le_sum (fun (r : Fin (n+1)) (_ : r∈Finset.univ) => hterm r.val)
  rw [Finset.sum_add_distrib] at hs
  have hin : (1 : ℕ)<n+1 := by dsimp [n,oddWeight]; omega
  have hsum : (∑ r : Fin (n+1),if r.val=1 then (1:ℕ) else 0)=1 := by
    have hiff (r : Fin (n+1)) : r.val=1 ↔ r=⟨1,hin⟩ := by simp only [Fin.ext_iff]
    simp only [hiff]
    simp
  rwa [hsum] at hs

end NormalizedFamily

namespace IntegralFamily

section
open LieGrading AssociativeElimination UniversalEmbedding WordGrading
attribute [local instance] LieRing.ofAssociativeRing

variable (V : Values)

def depthPiece (n : ℕ) : Submodule ℚ (Wn n) :=
  piece V n ⊓ (above GenericIhara.depth 2).comap (embed.toLinearMap.comp (Wn n).subtype)

variable {V} (f : Family V)

theorem cast_depth (k : ℕ) : embed (cast f ℚ k)∈above GenericIhara.depth 1 :=
  GenericIhara.homogeneous_depth (by simp [oddWeight]) (cast_homogeneous f ℚ k)

theorem tree_depth_two (t : UniversalEmbedding.Tree ℕ) (ht : 1<treeDegree (fun _ => 1) t) :
    embed (GenericIhara.evalIhara (cast f ℚ) t.eval)∈above GenericIhara.depth 2 := by
  have h := GenericIhara.evalIhara_depth (cast f ℚ) (cast_depth f) (LieGrading.eval_homogeneous (fun _ => 1) t)
  exact WordGrading.space_mono (by intro w hw; change treeDegree (fun _ => 1) t≤degree GenericIhara.depth w at hw; omega) h

theorem tree_reduced_depth_mem {n : ℕ} (t : UniversalEmbedding.Tree ℕ)
    (ht : treeDegree oddWeight t=n) (hr : 1<treeDegree (fun _ => 1) t) :
    reducedValue f n ⟨t.eval,ht ▸ LieGrading.eval_homogeneous oddWeight t⟩∈
      SaturatedSolutions.reduction n (depthPiece V n) := by
  let q : homogeneousLie (R:=ℤ) RationalBound.wt n :=
    ⟨GenericIhara.evalIhara f.value t.eval,integral_eval_homogeneous f (ht ▸ LieGrading.eval_homogeneous oddWeight t)⟩
  have he : (LieDimension.castHom (R:=ℚ) q).val=GenericIhara.evalIhara (cast f ℚ) t.eval := by
    exact (GenericIhara.cast_evalIhara f.value t.eval).trans (congrArg _ (LieDimension.cast_eval t))
  have hW : (LieDimension.castHom (R:=ℚ) q).val∈Wn n := by
    constructor
    · rw [he]; exact V.le_W (rational_mem f t.eval)
    · change _∈weightPiece RationalBound.wt n
      rw [weightPiece_eq]; exact (LieDimension.castHom (R:=ℚ) q).property
  apply integral_reduction_mem (depthPiece V n) q hW ?_ _ ?_
  · constructor
    · change (LieDimension.castHom (R:=ℚ) q).val∈V.space
      rw [he]; exact rational_mem f t.eval
    · change embed (LieDimension.castHom (R:=ℚ) q).val∈above GenericIhara.depth 2
      rw [he]; exact tree_depth_two f t hr
  · change IntegralBaseChange.lie (S:=K) (GenericIhara.evalIhara f.value t.eval)=_
    rw [GenericIhara.cast_evalIhara,LieDimension.cast_eval]
    rfl

theorem bi_reduced_depth_mem {n r : ℕ} (hr : 1<r)
    (p : biPiece (R:=K) oddWeight (fun _ => 1) n r) :
    reducedValue f n ⟨p.val,p.property.1⟩∈SaturatedSolutions.reduction n (depthPiece V n) := by
  let E := SaturatedSolutions.reduction n (depthPiece V n)
  let T := E.map (ReducedDimension.solutions n).subtype
  have hp : p.val∈biTreeSpan (R:=K) oddWeight (fun _ => 1) n r :=
    (biTreeSpan_eq (R:=K) oddWeight (fun _ => 1) n r).symm ▸ p.property
  have hh : ∀ v,v∈biTreeSpan (R:=K) oddWeight (fun _ => 1) n r →
      GenericIhara.evalIhara (cast f K) v∈T := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨t,ht,hl,rfl⟩ := hq
      refine ⟨reducedValue f n ⟨t.eval,ht ▸ LieGrading.eval_homogeneous oddWeight t⟩,
        tree_reduced_depth_mem f t ht (by omega),rfl⟩
    | zero => rw [map_zero]; exact T.zero_mem
    | add p q _ _ hp hq => rw [map_add]; exact T.add_mem hp hq
    | smul c p _ hp => rw [map_smul]; exact T.smul_mem c hp
  obtain ⟨q,hq,he⟩ := hh p.val hp
  have he' : q=reducedValue f n ⟨p.val,p.property.1⟩ := Subtype.ext he
  rwa [←he']

theorem old_reduced_depth_mem {n r : ℕ} (p : NormalizedFamily.oldPiece n r) :
    reducedValue f n ⟨p.val,NormalizedFamily.oldPiece_le n r p.property⟩∈
      SaturatedSolutions.reduction n (depthPiece V n) := by
  by_cases hr : 1<r
  · have hp : p.val∈biPiece (R:=K) oddWeight (fun _ => 1) n r := by
      have he : NormalizedFamily.oldPiece n r=biPiece (R:=K) oddWeight (fun _ => 1) n r := if_pos hr
      rw [←he]; exact p.property
    exact bi_reduced_depth_mem f hr ⟨p.val,hp⟩
  · have hp := NormalizedFamily.oldMap_low hr p
    subst p
    change reducedValue f n 0∈_
    rw [map_zero]
    exact Submodule.zero_mem _

end

section
open LieGrading AssociativeElimination UniversalEmbedding WordGrading
open ImageBound RowKernel QuadraticLeading RowTwo
attribute [local instance] LieRing.ofAssociativeRing

variable (V : Values)

structure Generator (k : ℕ) where
  value : FreeLieAlgebra ℤ Bool
  homogeneous : value∈homogeneousLie (fun _ => 1) (oddWeight k)
  member : IntegralBaseChange.lie (S:=ℚ) value∈V.space
  rep : FreeLieAlgebra K Slot
  under_rep : under rep=embed (IntegralBaseChange.lie (S:=K) value)
  above_rep : embed rep∈above bCount 1
  leading_rep : embed (leading 1 rep)=positiveInput (atom k)

variable {V}

def partialFamily (k : ℕ) (g : ∀ j,j<k → Generator V j) : Family V where
  value j := if h : j<k then (g j h).value else 0
  homogeneous j := by
    classical
    split_ifs with h
    · exact (g j h).homogeneous
    · exact Submodule.zero_mem _
  member j := by
    classical
    split_ifs with h
    · exact (g j h).member
    · rw [map_zero]; exact V.space.zero_mem

def partialData (k : ℕ) (g : ∀ j,j<k → Generator V j) : NormalizedFamily.Data where
  active j := j<k
  value := cast (partialFamily k g) K
  solution _ _ hp := reduced_solution (partialFamily k g) hp
  rep j := if h : j<k then (g j h).rep else 0
  under_rep j := by
    classical
    dsimp only [cast,partialFamily]
    split_ifs with h
    · exact (g j h).under_rep
    · simp only [map_zero]
  above_rep j h := by
    classical
    simpa only [dif_pos h] using (g j h).above_rep
  leading_rep j h := by
    classical
    simpa only [dif_pos h] using (g j h).leading_rep

variable (f : Family V) (g : NormalizedFamily.Data) (hg : g.value=cast f K)

include f hg in
theorem oldMap_mem {n r : ℕ} (p : NormalizedFamily.oldPiece n r) :
    NormalizedFamily.oldMap g n r p∈SaturatedSolutions.reduction n (depthPiece V n) := by
  have he : NormalizedFamily.oldMap g n r p=
      reducedValue f n ⟨p.val,NormalizedFamily.oldPiece_le n r p.property⟩ :=
    Subtype.ext (congrArg (fun v => GenericIhara.evalIhara v p.val) hg)
  rw [he]
  exact old_reduced_depth_mem f p

def oldToDepth (n : ℕ) : NormalizedFamily.OldDomain n →ₗ[K]
    SaturatedSolutions.reduction n (depthPiece V n) :=
  (Triangular.assemble (fun r : Fin (n+1) => NormalizedFamily.oldMap g n r.val)).codRestrict _ (by
    intro p
    rw [Triangular.assemble_apply]
    exact Submodule.sum_mem _ (fun r _ => oldMap_mem f g hg (p r)))

include f hg in
theorem old_rank_le (n : ℕ) (hn : 2<n) (ha : ∀ k,oddWeight k<n → g.active k) :
    Module.finrank K (NormalizedFamily.OldDomain n)≤Module.finrank ℚ (depthPiece V n) := by
  have hi : Function.Injective (oldToDepth f g hg n) := by
    intro p q he
    exact NormalizedFamily.old_assemble_injective g n (by omega) ha (congrArg Subtype.val he)
  have hh := LinearMap.finrank_le_finrank_of_injective hi
  rwa [SaturatedSolutions.finrank_reduction n (depthPiece V n) hn] at hh

theorem depth_rank_lt {n : ℕ} (p : Wn n) (hp : p∈piece V n)
    (hc : (embed p.val).coeff (GenericIhara.depthOneWord (n-1))≠0) :
    Module.finrank ℚ (depthPiece V n)<Module.finrank ℚ (piece V n) := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_not_ge inf_le_left
  intro h
  have hp' := (h hp).2
  exact hc (GenericIhara.depthOne_zero (by decide : 1<(2:ℕ)) hp' (n-1))

include f hg in
theorem dimension_sharp (k : ℕ) (ha : ∀ j,oddWeight j<oddWeight k → g.active j)
    (p : Wn (oddWeight k)) (hp : p∈piece V (oddWeight k))
    (hc : (embed p.val).coeff (GenericIhara.depthOneWord (oddWeight k-1))≠0) :
    Module.finrank ℚ (piece V (oddWeight k))=Module.finrank ℚ (Fn (oddWeight k)) := by
  have hn : 2<oddWeight k := by simp [oddWeight]
  have hlo := old_rank_le f g hg (oddWeight k) hn ha
  have hlt := depth_rank_lt p hp hc
  have hub : Module.finrank ℚ (Fn (oddWeight k))≤
      Module.finrank K (NormalizedFamily.OldDomain (oddWeight k))+1 := by
    change Module.finrank ℚ (weightPiece oddWeight (oddWeight k))≤_
    rw [weightPiece_eq,←LieDimension.finrank_homogeneous K oddWeight (oddWeight k)]
    exact NormalizedFamily.finrank_odd_le k
  have hupper := (Submodule.finrank_le (piece V (oddWeight k))).trans (RationalBound.finrank_Wn_le _ hn)
  omega

end

open LieGrading AssociativeElimination UniversalEmbedding WordGrading
open ImageBound RowKernel QuadraticLeading RowTwo
attribute [local instance] LieRing.ofAssociativeRing

variable (V : Values)

theorem generator_of_sharp (k : ℕ)
    (he : Module.finrank ℚ (piece V (oddWeight k))=Module.finrank ℚ (Fn (oddWeight k))) :
    Nonempty (Generator V k) := by
  have hn : 2<oddWeight k := by simp [oddWeight]
  let e : ReducedDimension.oddPiece (oddWeight k) 1 :=
    ⟨FreeLieAlgebra.of K k,LieGrading.eval_homogeneous oddWeight (.leaf k),
      LieGrading.eval_homogeneous (fun _ => 1) (.leaf k)⟩
  obtain ⟨p,hp⟩ := SaturatedSolutions.graded_surjective (oddWeight k) (piece V (oddWeight k)) hn he 1 (by omega) e
  obtain ⟨q,hq,hW,hV⟩ := SaturatedSolutions.reduction_lift (oddWeight k) (piece V (oddWeight k)) hn p.val
  refine ⟨⟨q.val,q.property,hV,ReducedDimension.representation (oddWeight k) (by omega) p.val.val,?_,?_,?_⟩⟩
  · rw [ReducedDimension.representation_under,←hq]
    rfl
  · exact p.property
  · have hs := ReducedDimension.gradedMap_spec (oddWeight k) hn 1
      (SaturatedSolutions.inclusionFiltration (oddWeight k) (piece V (oddWeight k)) (by omega) 1 p)
    have he' := congrArg (ReducedDimension.inclusion (oddWeight k) 1) hp
    change ReducedDimension.inclusion (oddWeight k) 1 (SaturatedSolutions.gradedMap (oddWeight k) (piece V (oddWeight k)) hn 1 p)=positiveInput (embed (FreeLieAlgebra.of K k)) at he'
    rw [AssociativeElimination.embed_of] at he'
    exact hs.symm.trans he'

theorem generators_exist (hv : OddValues V) : ∀ k,Nonempty (Generator V k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k hi =>
    classical
    let g : ∀ j,j<k → Generator V j := fun j hj => Classical.choice (hi j hj)
    obtain ⟨p,hp,hc⟩ := hv k
    apply generator_of_sharp V k
    apply dimension_sharp (partialFamily k g) (partialData k g) rfl k ?_ p hp hc
    intro j hj
    change j<k
    simp only [oddWeight] at hj
    omega

noncomputable def generators (hv : OddValues V) (k : ℕ) : Generator V k :=
  Classical.choice (generators_exist V hv k)

def normalizedFamily (hv : OddValues V) : Family V where
  value k := (generators V hv k).value
  homogeneous k := (generators V hv k).homogeneous
  member k := (generators V hv k).member

def normalizedData (hv : OddValues V) : NormalizedFamily.Data where
  active _ := True
  value := cast (normalizedFamily V hv) K
  solution _ _ hp := reduced_solution (normalizedFamily V hv) hp
  rep k := (generators V hv k).rep
  under_rep k := (generators V hv k).under_rep
  above_rep k _ := (generators V hv k).above_rep
  leading_rep k _ := (generators V hv k).leading_rep

end IntegralFamily

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section
namespace LieGrading
open AssociativeElimination UniversalEmbedding WordGrading
variable {R α : Type*} [CommRing R]

def weightSupport (wt : α → ℕ) (p : FreeLieAlgebra R α) : Finset ℕ :=
  (embed p).coeff.support.image (degree wt)

theorem piece_eq_zero_of_not_mem {wt : α → ℕ} {p : FreeLieAlgebra R α} {n : ℕ}
    (hn : n∉weightSupport wt p) : piece wt n p=0 := by
  classical
  apply UniversalEmbedding.injective
  rw [embed_piece,map_zero]
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  rw [WordGrading.piece,project_coeff]
  by_cases hw : degree wt w=n
  · rw [if_pos hw]
    change (embed p).coeff w=0
    by_contra hc
    apply hn
    exact Finset.mem_image.mpr ⟨w,by simpa only [Finsupp.mem_support_iff] using hc,hw⟩
  · rw [if_neg hw]
    rfl

theorem sum_pieces (wt : α → ℕ) (p : FreeLieAlgebra R α) :
    ∑ n∈weightSupport wt p,piece wt n p=p := by
  classical
  apply UniversalEmbedding.injective
  rw [map_sum]
  simp_rw [embed_piece]
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  simp only [MonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,WordGrading.piece,project_coeff]
  by_cases hw : degree wt w∈weightSupport wt p
  · simp only [Finset.sum_ite_eq,hw,ite_true]
  · have hz : (embed p).coeff w=0 := by
      by_contra hc
      apply hw
      exact Finset.mem_image.mpr ⟨w,by simpa only [Finsupp.mem_support_iff] using hc,rfl⟩
    simp [hz]

theorem ext_pieces (wt : α → ℕ) {p q : FreeLieAlgebra R α}
    (h : ∀ n,piece wt n p=piece wt n q) : p=q := by
  have hz : ∀ n,piece wt n (p-q)=0 := by
    intro n
    change projection wt n (p-q)=0
    rw [map_sub]
    change piece wt n p-piece wt n q=0
    rw [h n,sub_self]
  apply sub_eq_zero.mp
  rw [←sum_pieces wt (p-q)]
  simp only [hz,Finset.sum_const_zero]

end LieGrading
namespace PolynomialModuleCoefficients
open Polynomial
variable {M : Type*} [AddCommGroup M] [Module ℚ M]

theorem eq_zero (s : Finset ℕ) (v : ℕ → M)
    (h : ∀ c : ℚ,∑ n∈s,c^n • v n=0) {n : ℕ} (hn : n∈s) : v n=0 := by
  classical
  apply (Module.forall_dual_apply_eq_zero_iff ℚ (v n)).mp
  intro l
  let P : ℚ[X] := ∑ k∈s,Polynomial.monomial k (l (v k))
  have hp : P=0 := by
    apply Polynomial.funext
    intro c
    have he := congrArg l (h c)
    simpa only [P,Polynomial.eval_finsetSum,Polynomial.eval_monomial,map_sum,map_smul,
      map_zero,smul_eq_mul,mul_comm,Polynomial.eval_zero] using he
  have hc := congrArg (fun p : ℚ[X] => p.coeff n) hp
  simpa only [P,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,Polynomial.coeff_zero,
    Finset.sum_ite_eq',hn,ite_true] using hc

theorem mem (E : Submodule ℚ M) (s : Finset ℕ) (v : ℕ → M)
    (h : ∀ c : ℚ,∑ n∈s,c^n • v n∈E) {n : ℕ} (hn : n∈s) : v n∈E := by
  apply (Submodule.Quotient.mk_eq_zero E).mp
  exact eq_zero s (fun n => (Submodule.mkQ E) (v n)) (fun c => by
    have he : E.mkQ (∑ n∈s,c^n • v n)=0 := (Submodule.Quotient.mk_eq_zero E).mpr (h c)
    simpa only [map_sum,map_smul] using he) hn

end PolynomialModuleCoefficients
end

namespace LieGrading
variable {R α β : Type*} [CommRing R]
variable (wa : α → ℕ) (wb : β → ℕ)
variable (f : FreeLieAlgebra R α →ₗ[R] FreeLieAlgebra R β)
variable (hf : ∀ n {p},p∈homogeneousLie wa n → f p∈homogeneousLie wb n)
include hf

theorem map_piece (n : ℕ) (p : FreeLieAlgebra R α) : f (piece wa n p)=piece wb n (f p) := by
  classical
  have he : f p=∑ k∈weightSupport wa p,f (piece wa k p) := by
    rw [←map_sum,sum_pieces]
  rw [he]
  change _=projection wb n (∑ k∈weightSupport wa p,f (piece wa k p))
  rw [map_sum]
  simp only [projection,LinearMap.coe_mk,AddHom.coe_mk]
  simp_rw [piece_homogeneous (hf _ (piece_spec wa _ p).1)]
  by_cases hn : n∈weightSupport wa p
  · simp [hn]
  · rw [piece_eq_zero_of_not_mem hn,map_zero]
    simp [hn]

theorem injective_of_homogeneous
    (hi : ∀ n {p q},p∈homogeneousLie wa n → q∈homogeneousLie wa n → f p=f q → p=q) :
    Function.Injective f := by
  intro p q hpq
  apply ext_pieces wa
  intro n
  apply hi n (piece_spec wa n p).1 (piece_spec wa n q).1
  rw [map_piece wa wb f hf,map_piece wa wb f hf,hpq]

theorem reflects_homogeneous (hi : Function.Injective f) {n : ℕ} {p : FreeLieAlgebra R α}
    (hp : f p∈homogeneousLie wb n) : p∈homogeneousLie wa n := by
  have he : piece wa n p=p := by
    apply hi
    rw [map_piece wa wb f hf,piece_homogeneous hp,if_pos rfl]
  rw [←he]
  exact (piece_spec wa n p).1

end LieGrading

section
namespace SolutionGrading
open LieGrading AssociativeElimination UniversalEmbedding

def dilation (c : ℚ) : L →ₗ⁅ℚ⁆ L := eval (c • x) (c • y)
@[simp] theorem dilation_x (c : ℚ) : dilation c x=c • x := eval_x _ _
@[simp] theorem dilation_y (c : ℚ) : dilation c y=c • y := eval_y _ _

theorem eval_dilation {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (c : ℚ) (a b : M) (p : L) : eval a b (dilation c p)=eval (c • a) (c • b) p := by
  simp only [dilation,map_eval,map_smul,eval_x,eval_y]

def braidDilation (c : ℚ) : T4 →ₗ⁅ℚ⁆ T4 :=
  T4Universal.lift (fun i j => c • t i j)
    (by intros; rw [t_comm]) (by intros; rw [t_self,smul_zero])
    (by intros; rw [smul_lie,lie_smul,t_disjoint _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›,smul_zero,smul_zero])
    (by intros; rw [←smul_add,smul_lie,lie_smul,t_three _ _ _ ‹_› ‹_› ‹_›,smul_zero,smul_zero])

@[simp] theorem braidDilation_t (c : ℚ) (i j : Fin 4) : braidDilation c (t i j)=c • t i j :=
  T4Universal.lift_t _ _ _ _ _ _ _

theorem dilation_W (c : ℚ) {p : L} (hp : p∈W) : dilation c p∈W := by
  change IsSolution (dilation c p)
  constructor
  · have h := congrArg (dilation c) hp.1
    simp only [map_add,map_zero,map_eval,dilation_x,dilation_y] at h
    simpa only [eval_dilation] using h
  constructor
  · have h := congrArg (dilation c) hp.2.1
    simp only [map_add,map_zero,map_eval,map_sub,map_neg,dilation_x,dilation_y,←smul_neg,←smul_sub] at h
    simpa only [eval_dilation] using h
  · have h := congrArg (braidDilation c) hp.2.2
    simp only [map_add,map_eval,braidDilation_t,←smul_add] at h
    simpa only [eval_dilation] using h

theorem dilation_homogeneous (c : ℚ) {n : ℕ} {p : L}
    (hp : p∈homogeneousLie (fun _ => 1) n) : dilation c p=c^n • p := by
  have ht : ∀ t : UniversalEmbedding.Tree Bool,dilation c t.eval=c^(treeDegree (fun _ => 1) t) • t.eval := by
    intro t
    induction t with
    | leaf a => cases a <;> simp [Tree.eval,dilation,x,y,treeDegree_leaf,eval]
    | node t u ht hu =>
      simp only [Tree.eval,LieHom.map_lie,treeDegree_node,ht,hu,smul_lie,lie_smul,smul_smul,←pow_add,Nat.add_comm]
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨t,hn,rfl⟩ := hp; simpa only [hn] using ht t
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add,hp,hq,smul_add]
  | smul a p _ hp => simp only [map_smul,hp,smul_smul,mul_comm]

theorem dilation_sum (c : ℚ) (p : L) :
    dilation c p=∑ n∈weightSupport (fun _ => 1) p,c^n • piece (fun _ => 1) n p := by
  conv_lhs => rw [←sum_pieces (fun _ => 1) p]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact dilation_homogeneous c (piece_spec (fun _ => 1) n p).1

theorem piece_W {p : L} (hp : p∈W) (n : ℕ) : piece (fun _ => 1) n p∈W := by
  classical
  by_cases hn : n∈weightSupport (fun _ => 1) p
  · apply PolynomialModuleCoefficients.mem W (weightSupport (fun _ => 1) p)
      (fun n => piece (fun _ => 1) n p) ?_ hn
    intro c
    rw [←dilation_sum]
    exact dilation_W c hp
  · rw [piece_eq_zero_of_not_mem hn]
    exact W.zero_mem

theorem piece_Wn {p : L} (hp : p∈W) (n : ℕ) : piece (fun _ => 1) n p∈Wn n := by
  exact ⟨piece_W hp n,by change _∈weightPiece (fun _ => 1) n; rw [LieGrading.weightPiece_eq]; exact (piece_spec (fun _ => 1) n p).1⟩

end SolutionGrading

theorem completed_leftInverse (e : OddFree ≃ₗ[ℚ] W) (h : Graded e) :
    Function.LeftInverse (completedInv e h) (completed e h) := by
  intro a
  funext n
  apply Subtype.ext
  change e.symm (e (a n))=(a n : OddFree)
  exact e.symm_apply_apply _

theorem completed_rightInverse (e : OddFree ≃ₗ[ℚ] W) (h : Graded e) :
    Function.RightInverse (completedInv e h) (completed e h) := by
  intro a
  funext n
  apply Subtype.ext
  change (e (e.symm ⟨a n,(a n).property.1⟩) : L)=(a n : L)
  rw [e.apply_symm_apply]

theorem completed_continuous (e : OddFree ≃ₗ[ℚ] W) (h : Graded e) :
    Continuous (completed e h) := by
  let : DiscreteTopology OddFree := ⟨rfl⟩
  apply continuous_pi
  intro n
  let f : Fn n → Wn n := fun p => ⟨e p,(e p).property,(h n p).2 p.property⟩
  exact (continuous_of_discreteTopology (f:=f)).comp (continuous_apply n)

theorem completedInv_continuous (e : OddFree ≃ₗ[ℚ] W) (h : Graded e) :
    Continuous (completedInv e h) := by
  let : DiscreteTopology L := ⟨rfl⟩
  apply continuous_pi
  intro n
  let f : Wn n → Fn n := fun p => ⟨e.symm ⟨p,p.property.1⟩,
    (h n _).1 (by rw [e.apply_symm_apply]; exact p.property.2)⟩
  exact (continuous_of_discreteTopology (f:=f)).comp (continuous_apply n)

theorem completed_bracket (e : OddFree ≃ₗ[ℚ] W) (h : Graded e)
    (he : ∀ a b,(e ⁅a,b⁆ : L)=ihara (e a) (e b))
    (a b : OddCompletion) (n : ℕ) :
    (e (∑ i ∈ Finset.range (n+1),⁅(a i : OddFree),(b (n-i) : OddFree)⁆) : L)=
      ∑ i ∈ Finset.range (n+1),ihara (completed e h a i) (completed e h b (n-i)) := by
  simp only [map_sum,Submodule.coe_sum,he]
  rfl

namespace GradedGeneration
open LieGrading

instance finite_Fn (n : ℕ) : Module.Finite ℚ (Fn n) := by
  change Module.Finite ℚ (weightPiece oddWeight n)
  rw [weightPiece_eq]
  infer_instance

theorem Fn_eq_bot {n : ℕ} (hn : n≤2) : Fn n=⊥ := by
  change weightPiece oddWeight n=⊥
  rw [weightPiece_eq]
  apply le_antisymm ?_ bot_le
  apply Submodule.span_le.mpr
  rintro p ⟨t,ht,rfl⟩
  have h := treeDegree_lower (m:=3) (wt:=oddWeight) (by intro k; simp [oddWeight]) t
  omega

variable (v : ℕ → L) (hv : ∀ k,v k∈Ln (oddWeight k))
include hv

 theorem homogeneous {n : ℕ} {p : OddFree} (hp : p∈Fn n) :
    GenericIhara.evalIhara v p∈Ln n := by
  change _∈weightPiece (fun _ => 1) n
  rw [weightPiece_eq]
  apply homogeneous_iff.mpr
  apply GenericIhara.evalIhara_homogeneous oddWeight v (fun k => ?_) (by
    change p∈weightPiece oddWeight n at hp
    rwa [weightPiece_eq] at hp)
  apply homogeneousLie_embed
  have h := hv k
  change v k∈weightPiece (fun _ => 1) (oddWeight k) at h
  rwa [weightPiece_eq] at h

variable (hW : ∀ p,GenericIhara.evalIhara v p∈W)

def valuePiece (n : ℕ) : Fn n →ₗ[ℚ] Wn n :=
  ((GenericIhara.evalIhara v).comp (Fn n).subtype).codRestrict _
    (fun p => ⟨hW p,homogeneous v hv p.property⟩)

variable (hi : ∀ n,2<n → Function.Injective (valuePiece v hv hW n))
include hW hi

theorem valuePiece_injective (n : ℕ) : Function.Injective (valuePiece v hv hW n) := by
  by_cases hn : 2<n
  · exact hi n hn
  · intro p q _
    have hp := p.property
    have hq := q.property
    simp only [Fn_eq_bot (show n≤2 by omega),Submodule.mem_bot] at hp hq
    exact Subtype.ext (hp.trans hq.symm)

theorem values_injective : Function.Injective (GenericIhara.evalIhara v) := by
  apply injective_of_homogeneous oddWeight (fun _ => 1) _ ?_ ?_
  · intro n p hp
    rw [←weightPiece_eq] at hp ⊢
    exact homogeneous v hv hp
  · intro n p q hp hq he
    rw [←weightPiece_eq] at hp hq
    exact congrArg Subtype.val (valuePiece_injective v hv hW hi n
      (Subtype.ext he : valuePiece v hv hW n ⟨p,hp⟩=valuePiece v hv hW n ⟨q,hq⟩))

theorem valuePiece_surjective (n : ℕ) : Function.Surjective (valuePiece v hv hW n) := by
  by_cases hn : 2<n
  · apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp (hi n hn)
    apply le_antisymm
    · exact LinearMap.finrank_le_finrank_of_injective (hi n hn)
    · exact RationalBound.finrank_Wn_le n hn
  · intro q
    refine ⟨0,?_⟩
    rw [map_zero]
    apply Subtype.ext
    have hq := q.property
    simp only [LowWeight.Wn_eq_bot (show n≤2 by omega),Submodule.mem_bot] at hq
    exact hq.symm

def valueMap : OddFree →ₗ[ℚ] W := (GenericIhara.evalIhara v).codRestrict _ hW

theorem valueMap_bijective : Function.Bijective (valueMap v hW) := by
  constructor
  · intro p q he
    exact values_injective v hv hW hi (congrArg Subtype.val he)
  · intro q
    classical
    have hs : ∀ n,∃ p : Fn n,valuePiece v hv hW n p=⟨piece (fun _ => 1) n q.val,
        SolutionGrading.piece_Wn q.property n⟩ := by
      intro n
      exact valuePiece_surjective v hv hW hi n _
    choose p hp using hs
    refine ⟨∑ n∈weightSupport (fun _ => 1) q.val,(p n).val,?_⟩
    apply Subtype.ext
    change GenericIhara.evalIhara v (∑ n∈weightSupport (fun _ => 1) q.val,(p n).val)=q.val
    rw [map_sum]
    calc
      _ = ∑ n∈weightSupport (fun _ => 1) q.val,piece (fun _ => 1) n q.val := by
        apply Finset.sum_congr rfl
        intro n _
        exact congrArg Subtype.val (hp n)
      _ = q.val := sum_pieces _ _

def equivalence : OddFree ≃ₗ[ℚ] W := LinearEquiv.ofBijective (valueMap v hW) (valueMap_bijective v hv hW hi)

theorem equivalence_graded : Graded (equivalence v hv hW hi) := by
  intro n p
  change GenericIhara.evalIhara v p∈Ln n ↔ p∈Fn n
  constructor
  · intro hp
    change _∈weightPiece oddWeight n
    rw [weightPiece_eq]
    have hhom : ∀ m {q},q∈homogeneousLie oddWeight m →
        GenericIhara.evalIhara v q∈homogeneousLie (fun _ => 1) m := by
      intro m q hq
      rw [←weightPiece_eq] at hq ⊢
      exact homogeneous v hv hq
    have hpx : GenericIhara.evalIhara v p∈homogeneousLie (fun _ => 1) n := by
      change _∈weightPiece (fun _ => 1) n at hp
      rwa [weightPiece_eq] at hp
    exact reflects_homogeneous oddWeight (fun _ => 1) (GenericIhara.evalIhara v)
      (hf := hhom) (values_injective v hv hW hi) hpx
  · exact homogeneous v hv

theorem main_of_values : MainStatement := by
  let e := equivalence v hv hW hi
  have hg : Graded e := equivalence_graded v hv hW hi
  have hb : ∀ a b,(e ⁅a,b⁆ : L)=ihara (e a) (e b) := by
    intro a b
    change GenericIhara.evalIhara v ⁅a,b⁆=ihara (GenericIhara.evalIhara v a) (GenericIhara.evalIhara v b)
    rw [GenericIhara.evalIhara_lie,GenericIhara.rational_ihara]
  exact ⟨e,hg,hb,completed_leftInverse e hg,completed_rightInverse e hg,
    completed_continuous e hg,completedInv_continuous e hg,completed_bracket e hg hb⟩

end GradedGeneration
end

namespace IntegralFamily
open LieGrading
variable {V : Values} (f : Family V)

def rangeValues : Values where
  space := (GenericIhara.evalIhara (cast f ℚ)).range
  le_W := by rintro p ⟨q,rfl⟩; exact V.le_W (rational_mem f q)
  bracket := by
    rintro p q ⟨a,rfl⟩ ⟨b,rfl⟩
    exact ⟨⁅a,b⁆,by rw [GenericIhara.evalIhara_lie,GenericIhara.rational_ihara]⟩

def rangeFamily : Family (rangeValues f) where
  value := f.value
  homogeneous := f.homogeneous
  member k := ⟨FreeLieAlgebra.of ℚ k,GenericIhara.evalIhara_of _ _⟩

def rangePiece (n : ℕ) : homogeneousLie (R:=ℚ) oddWeight n →ₗ[ℚ] piece (rangeValues f) n :=
  { toFun p := ⟨⟨GenericIhara.evalIhara (cast f ℚ) p.val,
      V.le_W (rational_mem f p.val),by
        change _∈weightPiece (fun _ => 1) n
        rw [weightPiece_eq]
        exact eval_homogeneous f ℚ p.property⟩,⟨p.val,rfl⟩⟩
    map_add' p q := by apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
    map_smul' c p := by apply Subtype.ext; apply Subtype.ext; exact map_smul _ _ _ }

theorem rangePiece_surjective (n : ℕ) : Function.Surjective (rangePiece f n) := by
  intro p
  obtain ⟨q,hq⟩ := p.property
  refine ⟨⟨LieGrading.piece oddWeight n q,(piece_spec oddWeight n q).1⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change GenericIhara.evalIhara (cast f ℚ) (LieGrading.piece oddWeight n q)=p.val.val
  rw [map_piece oddWeight (fun _ => 1) _ (fun _ _ hp => eval_homogeneous f ℚ hp),hq]
  have hp : p.val.val∈homogeneousLie (fun _ => 1) n := by
    have hp := p.val.property.2
    change _∈weightPiece (fun _ => 1) n at hp
    rwa [weightPiece_eq] at hp
  change LieGrading.piece (fun _ => 1) n p.val.val=p.val.val
  rw [piece_homogeneous hp,if_pos rfl]

variable (g : NormalizedFamily.Data) (hg : g.value=cast f K) (ha : ∀ k,g.active k)
include hg ha

theorem range_dimension_lower (n : ℕ) (hn : 2<n) :
    Module.finrank ℚ (homogeneousLie (R:=ℚ) oddWeight n)≤Module.finrank ℚ (piece (rangeValues f) n) := by
  let h : homogeneousLie (R:=K) oddWeight n →ₗ[K]
      SaturatedSolutions.reduction n (piece (rangeValues f) n) :=
    (reducedValue (rangeFamily f) n).codRestrict _ (reduced_mem (rangeFamily f))
  have hi : Function.Injective h := by
    intro p q hpq
    apply NormalizedFamily.valueMap_injective g n (by omega) ha
    apply Subtype.ext
    change GenericIhara.evalIhara g.value p.val=GenericIhara.evalIhara g.value q.val
    rw [hg]
    exact congrArg (fun z => z.val.val) hpq
  have he : Module.finrank ℚ (homogeneousLie (R:=ℚ) oddWeight n)=
      Module.finrank K (homogeneousLie (R:=K) oddWeight n) :=
    (LieDimension.finrank_homogeneous K oddWeight n).symm
  rw [he,←SaturatedSolutions.finrank_reduction n (piece (rangeValues f) n) hn]
  exact LinearMap.finrank_le_finrank_of_injective hi

theorem rangePiece_injective (n : ℕ) (hn : 2<n) : Function.Injective (rangePiece f n) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr (rangePiece_surjective f n)
  exact le_antisymm (range_dimension_lower f g hg ha n hn)
    (LinearMap.finrank_le_finrank_of_surjective (rangePiece_surjective f n))

theorem main_of_normalized : MainStatement := by
  have hv : ∀ k,cast f ℚ k∈Ln (oddWeight k) := by
    intro k
    change _∈weightPiece (fun _ => 1) (oddWeight k)
    rw [weightPiece_eq]
    exact cast_homogeneous f ℚ k
  have hW : ∀ p,GenericIhara.evalIhara (cast f ℚ) p∈W := fun p => V.le_W (rational_mem f p)
  apply GradedGeneration.main_of_values (cast f ℚ) hv hW
  intro n hn p q hpq
  apply Subtype.ext
  have hp : p.val∈homogeneousLie oddWeight n := by
    have hp := p.property
    change _∈weightPiece oddWeight n at hp
    rwa [weightPiece_eq] at hp
  have hq : q.val∈homogeneousLie oddWeight n := by
    have hq := q.property
    change _∈weightPiece oddWeight n at hq
    rwa [weightPiece_eq] at hq
  exact congrArg (fun z : homogeneousLie (R:=ℚ) oddWeight n => z.val) (rangePiece_injective f g hg ha n hn
    (show rangePiece f n ⟨p.val,hp⟩=rangePiece f n ⟨q.val,hq⟩ from
      Subtype.ext (Subtype.ext (congrArg Subtype.val hpq))))

omit hg ha in

theorem main_of_oddValues_oai (V : Values) (h : OddValues V) : MainStatement :=
  main_of_normalized (normalizedFamily V h) (normalizedData V h) rfl (fun _ => True.intro)

end IntegralFamily

open AssociativeElimination WordGrading

end DeligneDrinfeld

end

end OAI

end

section
open OAI.DeligneDrinfeld.IntegralFamily in
theorem solution : ∀ (V : OAI.DeligneDrinfeld.IntegralFamily.Values)
    (h : OAI.DeligneDrinfeld.IntegralFamily.OddValues V),
    OAI.DeligneDrinfeld.MainStatement :=
  @OAI.DeligneDrinfeld.IntegralFamily.main_of_oddValues_oai
end
