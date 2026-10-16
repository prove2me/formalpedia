-- Prove2me | solution 1 for OAI.TreeEdit.TorusTree.sampledWord_diagonal_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:54:26.234912+00:00
-- url     : https://prove2.me/submissions/8fe13ff8-d859-42b1-81ff-ae0fb1b316c8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/RandomCircle.lean:L165-L214
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.TorusTree.sampledWord_diagonal_step. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Theorems.Thm_OAI_TreeEdit_FiniteProbability_hom_uniform
import Theorems.Thm_OAI_TreeEdit_Words_cycles_val

-- ---- from OAI.Combinatorics.TreeEdit.FiniteProbability ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

namespace TreeEdit.FiniteProbability
open scoped BigOperators
open Classical

lemma mean_le {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    mean f ≤ mean g := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

lemma mean_mul_const {A : Type*} [Fintype A] (f : A → ℝ) (c : ℝ) :
    mean (fun a => f a * c) = mean f * c := by simp [mean, Finset.sum_mul, mul_assoc]

lemma mean_sum {A I : Type*} [Fintype A] (s : Finset I) (f : I → A → ℝ) :
    mean (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, mean (f i) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma mean_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℝ) :
    mean (fun a => f (e a)) = mean f := by
  simp only [mean, Fintype.card_congr e]
  congr 1
  exact e.sum_comp f

lemma mean_fiberwise {A B : Type*} [Fintype A] [Fintype B] (f : A → B) (g : B → ℝ) :
    mean (fun a => g (f a)) = ∑ b : B, probability (fun a => f a = b) * g b := by
  have he (a : A) : g (f a) = ∑ b : B, (if f a = b then (1 : ℝ) else 0) * g b := by simp
  simp_rw [probability, ← mean_mul_const]
  rw [← mean_sum]
  apply congrArg mean
  funext a
  exact he a

end TreeEdit.FiniteProbability

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.EditMetric ----
namespace OAI

namespace TreeEdit

universe u v

namespace EditStep

variable {α : Type u} {x y : List α}

protected theorem append_left (h : EditStep x y) (p : List α) :
    EditStep (p ++ x) (p ++ y) := by
  cases h with
  | insert q r a => simpa [List.append_assoc] using EditStep.insert (p ++ q) r a
  | delete q r a => simpa [List.append_assoc] using EditStep.delete (p ++ q) r a
  | substitute q r a b =>
      simpa [List.append_assoc] using EditStep.substitute (p ++ q) r a b

protected theorem append_right (h : EditStep x y) (r : List α) :
    EditStep (x ++ r) (y ++ r) := by
  cases h with
  | insert p q a => simpa [List.append_assoc] using EditStep.insert p (q ++ r) a
  | delete p q a => simpa [List.append_assoc] using EditStep.delete p (q ++ r) a
  | substitute p q a b =>
      simpa [List.append_assoc] using EditStep.substitute p (q ++ r) a b

end EditStep

namespace EditScript

variable {α : Type u} {x y z : List α} {m n : ℕ}

protected theorem append_left (h : EditScript x y n) (p : List α) :
    EditScript (p ++ x) (p ++ y) n := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_left p) ih

protected theorem append_right (h : EditScript x y n) (p : List α) :
    EditScript (x ++ p) (y ++ p) n := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_right p) ih

end EditScript

variable {α : Type u} {x y z : List α}

theorem ed_append (x y x' y' : List α) :
    ed (x ++ x') (y ++ y') ≤ ed x y + ed x' y' := by
  exact ed_le_of_script
    (((ed_script x y).append_right x').trans ((ed_script x' y').append_left y))

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CircleTree ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

lemma period_pos {I : Type} {g : ℕ} {r : I → ℕ} (hr : ∀ i, 0 < r i)
    (j : Fin g → I) (σ : Equiv.Perm I) : 0 < period r j σ := product_positive _ (fun _ => hr _)

lemma cast_hom_val {L r : ℕ} [NeZero L] (hrL : r ∣ L) (z : ZMod L) :
    ZMod.castHom hrL (ZMod r) z = (z.val : ZMod r) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  simp only [map_natCast]

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

end TreeEdit.TorusTree

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CircleSeparation ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical

lemma representative_coe (t : UnitAddCircle) : (representative t : UnitAddCircle) = t :=
  AddCircle.coe_equivIco

end TreeEdit.TorusTree

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.WordOperations ----
namespace OAI

namespace TreeEdit

universe u v

variable {α : Type u} {x y z : List α}

attribute [local instance] Classical.propDecidable

namespace EditStep

protected lemma map {β : Type*} (f : α → β) (h : EditStep x y) :
    EditStep (x.map f) (y.map f) := by
  cases h with
  | insert p q a => simpa using EditStep.insert (p.map f) (q.map f) (f a)
  | delete p q a => simpa using EditStep.delete (p.map f) (q.map f) (f a)
  | substitute p q a b => simpa using EditStep.substitute (p.map f) (q.map f) (f a) (f b)

end EditStep

namespace EditScript

protected lemma map {β : Type*} (f : α → β) {n : ℕ} (h : EditScript x y n) :
    EditScript (x.map f) (y.map f) n := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.map f) ih

end EditScript

lemma ed_map {β : Type*} (f : α → β) (x y : List α) : ed (x.map f) (y.map f) ≤ ed x y :=
  ed_le_of_script ((ed_script x y).map f)

lemma ed_flatten_ofFn {n : ℕ} (x y : Fin n → List α) :
    ed (List.ofFn x).flatten (List.ofFn y).flatten ≤ ∑ i, ed (x i) (y i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.flatten_cons, Fin.sum_univ_succ]
    exact (ed_append _ _ _ _).trans (Nat.add_le_add_left (ih _ _) _)

namespace Words

variable {β : Type v} {n : ℕ}

lemma ed_cycles {m T B : ℕ} {β : Fin m → Type*}
    (x y : Fin T → ∀ i, Word (β i) B) :
    ed (cycles x).val (cycles y).val ≤ ∑ a : Fin T, ∑ i : Fin m,
      ed (x a i).val (y a i).val := by
  rw [cycles_val, cycles_val]
  apply (ed_flatten_ofFn _ _).trans
  apply Finset.sum_le_sum
  intro a _
  apply (ed_flatten_ofFn _ _).trans
  exact Finset.sum_le_sum fun i _ => ed_map (Sigma.mk i) _ _

end Words

namespace Words

variable {β : Type v} {n : ℕ}

end Words

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.RandomCircle ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

lemma representative_toAddCircle {M : ℕ} [NeZero M] (a : ZMod M) :
    representative (ZMod.toAddCircle a) = (a.val : ℝ) / M := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hm : (a.val : ℝ) / M ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨by positivity, (div_lt_one hM).mpr (by exact_mod_cast a.val_lt)⟩
  have he : (representative (ZMod.toAddCircle a) : UnitAddCircle) = ((a.val : ℝ) / M : ℝ) :=
    (representative_coe _).trans (ZMod.toAddCircle_apply a)
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := (0 : ℝ)) (by simpa only [Set.mem_Ico, zero_add] using representative_mem (ZMod.toAddCircle a)) (by simpa only [zero_add] using hm)).mp he

lemma bin_grid {M R D : ℕ} [NeZero M] [NeZero R] (hD : 0 < D) (hM : M = R * D) (a : ZMod M) :
    (bin R (ZMod.toAddCircle a)).val = a.val / D := by
  have hR : (R : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne R)
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  change ⌊(R : ℝ) * representative (ZMod.toAddCircle a)⌋₊ = _
  rw [representative_toAddCircle]
  have he : (R : ℝ) * ((a.val : ℝ) / M) = (a.val : ℝ) / D := by
    have hMr : (M : ℝ) = (R : ℝ) * D := by exact_mod_cast hM
    rw [hMr]; field_simp
  rw [he]
  have hh := Nat.mul_cast_floor_div_cancel (R := ℝ) hD.ne' ((a.val : ℝ) / D)
  rw [div_mul_cancel₀ _ hDr, Nat.floor_natCast] at hh
  exact hh.symm

lemma bin_grid_step {M R D : ℕ} [NeZero M] [NeZero R] (hD : 0 < D) (hM : M = R * D) (a : ZMod M)
    (ha : a.val % D ≠ D - 1) : bin R (ZMod.toAddCircle a) = bin R (ZMod.toAddCircle (a + 1)) := by
  apply Fin.ext
  rw [bin_grid hD hM, bin_grid hD hM]
  have hval : (a + 1).val = a.val + 1 := by
    have hm : a.val + 1 < M := by
      by_contra hn
      have he : a.val = M - 1 := by have := a.val_lt; omega
      have hmod : (M - 1) % D = D - 1 := by
        have hR := NeZero.pos R
        have he : M - 1 = (R - 1) * D + (D - 1) := by
          have := Nat.sub_add_cancel (show 1 ≤ R from hR)
          have := Nat.sub_add_cancel (show 1 ≤ D from hD)
          have : M - 1 + 1 = M := Nat.sub_add_cancel (NeZero.pos M)
          nlinarith
        rw [he]
        simp only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt (by omega : D - 1 < D)]
      exact ha (he ▸ hmod)
    have hm1 : 1 < M := by omega
    let : Fact (1 < M) := ⟨hm1⟩
    rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt hm]
  rw [hval]
  symm
  apply Nat.div_eq_of_lt_le
  · exact (Nat.div_mul_le_self a.val D).trans (by omega)
  · have hh := Nat.div_add_mod a.val D
    have hr := Nat.mod_lt a.val hD
    have hr' : a.val % D + 1 < D := by omega
    nlinarith

lemma mean_comp_hom {A B : Type*} [Fintype A] [Fintype B] [AddGroup A] [AddGroup B]
    (f : A →+ B) (hf : Function.Surjective f) (g : B → ℝ) : mean (g ∘ f) = mean g := by
  change mean (fun a => g (f a)) = mean g
  rw [mean_fiberwise]
  simp_rw [hom_uniform f hf]
  rw [mean, Finset.mul_sum]

lemma mean_translate {A : Type*} [Fintype A] [AddGroup A] (y : A) (f : A → ℝ) :
    mean (fun x => f (x + y)) = mean f := mean_equiv (Equiv.addRight y) f

lemma mapState_diagonal {A B : Type} [AddCommGroup A] [AddCommGroup B] {m : ℕ}
    (f : A →+ B) (h : ℕ) (a : A) :
    mapState (m := m) f h (diagonal (A := A) (m := m) h a) = diagonal (A := B) (m := m) h (f a) := by
  induction h with
  | zero => rfl
  | succ h ih => exact funext fun _ => ih

lemma point_grid {M P : ℕ} [NeZero M] (hP : 0 < P) (hPM : P ∣ M) :
    ZMod.toAddCircle (M / P : ZMod M) = point P := by
  rw [ZMod.toAddCircle_natCast]
  dsimp [point]
  congr 1
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hPr : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have he : ((M / P : ℕ) : ℝ) * P = M := by exact_mod_cast Nat.div_mul_cancel hPM
  field_simp
  linarith

lemma bin_step_mean {M R D : ℕ} [NeZero M] [NeZero R] (hD : 0 < D) (hM : M = R * D) :
    mean (fun a : ZMod M => (ed [bin R (ZMod.toAddCircle a)] [bin R (ZMod.toAddCircle (a + 1))] : ℝ)) ≤ (D : ℝ)⁻¹ := by
  classical
  let : NeZero D := ⟨hD.ne'⟩
  have hDM : D ∣ M := by rw [hM]; exact dvd_mul_left _ _
  let f : ZMod M →+ ZMod D := (ZMod.castHom hDM (ZMod D)).toAddMonoidHom
  have he (a : ZMod M) : a.val % D = D - 1 ↔ f a = (D - 1 : ℕ) := by
    apply Iff.trans _ (ZMod.val_injective (n := D)).eq_iff
    change a.val % D = D - 1 ↔ (ZMod.castHom hDM (ZMod D) a).val = ((D-1 : ℕ) : ZMod D).val
    rw [cast_hom_val hDM, ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : D - 1 < D)]
  have hh := mean_le (fun a : ZMod M => show
      (ed [bin R (ZMod.toAddCircle a)] [bin R (ZMod.toAddCircle (a + 1))] : ℝ) ≤
        (if f a = (D - 1 : ℕ) then 1 else 0) from by
    by_cases ha : f a = (D - 1 : ℕ)
    · simp only [ha, ↓reduceIte]
      have hh : ed [bin R (ZMod.toAddCircle a)] [bin R (ZMod.toAddCircle (a + 1))] ≤ 1 :=
        ed_le_of_script (EditScript.cons (EditStep.substitute [] [] _ _) (EditScript.nil _))
      exact_mod_cast hh
    · simp only [ha, ↓reduceIte]
      rw [bin_grid_step hD hM a (fun hz => ha ((he a).mp hz)), ed_self]
      norm_num)
  have hp := hom_uniform f (ZMod.castHom_surjective hDM) (D - 1 : ℕ)
  apply hh.trans_eq
  calc
    _ = probability (fun a : ZMod M => f a = ((D-1 : ℕ) : ZMod D)) := by
      unfold probability
      congr 1
      funext a
      split_ifs <;> rfl
    _ = _ := by simpa only [ZMod.card] using hp

lemma mean_eval {A : Type*} [Fintype A] [AddCommGroup A]
    {m : ℕ} (i : Fin m) (f : A → ℝ) :
    mean (fun x : Fin m → A => f (x i)) = mean f := by
  exact mean_comp_hom (Pi.evalAddMonoidHom _ i) (fun a => ⟨fun _ => a, rfl⟩) f

lemma sampledWord_succ {I : Type} {g s L M T R : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M)
    (h : ℕ) (C : Config I L (g * s) (h + 1)) (x : State (ZMod M) (g * s) (h + 1)) :
    sampledWord r j T R (h+1) C x = Words.cycles (fun a i =>
      sampledWord r j T R h (C.2 i).2 (x i + a.val • cycle (M := M) r j h C i)) := by
  unfold sampledWord
  simp only [word]
  congr 1
  funext a i
  apply congrArg (word r j T R h (C.2 i).2)
  dsimp [cycle, sample]
  change sample (M := M) (m := g*s) h (x i) +
    diagonal (A := UnitAddCircle) (m := g*s) h ((a.val * coefficient r j C.1 (C.2 i).1 i) • point (period r j C.1)) = _
  dsimp only [sample]
  simp only [map_add, map_nsmul, mapState_diagonal, point_grid (period_pos hr j C.1) (hPM C.1), mul_smul]

lemma sampledWord_diagonal_step {I : Type} {g s L M T R D : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M)
    (hD : 0 < D) (hM : M = R * D)
    (h : ℕ) (C : Config I L (g * s) h) :
    mean (fun x : State (ZMod M) (g * s) h =>
      (ed (sampledWord r j T R h C x).val
        (sampledWord r j T R h C (x + diagonal (A := ZMod M) (m := g * s) h 1)).val : ℝ)) ≤
      (FiniteTree.length (g * s) T h : ℝ) / D := by
  induction h with
  | zero =>
    have hw (x : ZMod M) : (sampledWord r j T R 0 C x).val = [bin R (ZMod.toAddCircle x)] := by
      change List.ofFn (fun _ : Fin 1 => bin R (ZMod.toAddCircle x)) = _
      simp [List.ofFn_succ]
    simp only [hw]
    exact (bin_step_mean hD hM).trans_eq (by simp [FiniteTree.length, one_div])
  | succ h ih =>
    let f (i : Fin (g*s)) (x : State (ZMod M) (g*s) h) :=
      (ed (sampledWord r j T R h (C.2 i).2 x).val
        (sampledWord r j T R h (C.2 i).2 (x + diagonal (A := ZMod M) (m := g*s) h 1)).val : ℝ)
    have hp (x : State (ZMod M) (g*s) (h+1)) :
        (ed (sampledWord r j T R (h+1) C x).val
          (sampledWord r j T R (h+1) C (x + diagonal (A := ZMod M) (m := g*s) (h+1) 1)).val : ℝ) ≤
        ∑ a : Fin T, ∑ i : Fin (g*s), f i (x i + a.val • cycle (M := M) r j h C i) := by
      rw [sampledWord_succ r j hr hPM, sampledWord_succ r j hr hPM]
      have hh := Words.ed_cycles (T := T)
        (fun a i => sampledWord r j T R h (C.2 i).2 (x i + a.val • cycle (M := M) r j h C i))
        (fun a i => sampledWord r j T R h (C.2 i).2 ((x + diagonal (A := ZMod M) (m := g*s) (h+1) 1) i + a.val • cycle (M := M) r j h C i))
      have he (a : Fin T) (i : Fin (g*s)) :
          (x + diagonal (A := ZMod M) (m := g*s) (h+1) 1) i + a.val • cycle (M := M) r j h C i =
          (x i + a.val • cycle (M := M) r j h C i) + diagonal (A := ZMod M) (m := g*s) h 1 := by
        change x i + diagonal (A := ZMod M) (m := g*s) h 1 + _ = _
        abel
      simpa only [he, Nat.cast_sum] using (Nat.cast_le (α := ℝ)).mpr hh
    apply (mean_le hp).trans
    rw [mean_sum]
    calc
      _ = ∑ a : Fin T, ∑ i : Fin (g*s), mean (f i) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [mean_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact (mean_eval i (fun y => f i (y + a.val • cycle (M := M) r j h C i))).trans
          (mean_translate _ (f i))
      _ ≤ ∑ _a : Fin T, ∑ _i : Fin (g*s), (FiniteTree.length (g*s) T h : ℝ) / D := by
        apply Finset.sum_le_sum
        intro a _
        exact Finset.sum_le_sum fun i _ => ih (C.2 i).2
      _ = _ := by simp [FiniteTree.length, Finset.sum_const, Finset.card_univ]; ring

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

end TreeEdit.TorusTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability


theorem solution : type_of% @_root_.OAI.TreeEdit.TorusTree.sampledWord_diagonal_step := @_root_.OAI.TreeEdit.TorusTree.sampledWord_diagonal_step
