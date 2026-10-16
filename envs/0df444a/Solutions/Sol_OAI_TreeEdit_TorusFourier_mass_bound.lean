-- Prove2me | solution 1 for OAI.TreeEdit.TorusFourier.mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:08:36.270764+00:00
-- url     : https://prove2.me/submissions/39336f51-1cb4-4ba7-b11c-088df9ec41bc

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/SampledSpectrum.lean:L189-L258
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.TorusFourier.mass_bound. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
import Theorems.Thm_OAI_TreeEdit_FiniteFourier_sum_multiplier_period
import Theorems.Thm_OAI_TreeEdit_TorusFourier_branch_summaries
import Theorems.Thm_OAI_TreeEdit_TorusFourier_sum_chord_detect
import Theorems.Thm_OAI_TreeEdit_TorusTree_sampledWord_child_mean
import Theorems.Thm_OAI_TreeEdit_TorusTree_sampledWord_tiny
import Theorems.Thm_OAI_TreeEdit_Words_cycles_val

-- ---- from OAI.Combinatorics.TreeEdit.FiniteProbability ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

namespace TreeEdit.FiniteProbability
open scoped BigOperators
open Classical

lemma mean_le {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    mean f ≤ mean g := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

lemma mean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) : mean (fun _ : A => c) = c := by
  simp only [mean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

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

end EditStep

namespace EditScript

variable {α : Type u} {x y z : List α} {m n : ℕ}

protected theorem append_left (h : EditScript x y n) (p : List α) :
    EditScript (p ++ x) (p ++ y) n := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_left p) ih

end EditScript

variable {α : Type u} {x y z : List α}

theorem sublist_script (h : z.Sublist x) : EditScript x z (x.length - z.length) := by
  induction h with
  | slnil => exact .nil []
  | @cons l₁ l₂ a h ih =>
      have hl := h.length_le
      have he : (a :: l₂).length - l₁.length = (l₂.length - l₁.length) + 1 := by
        simp only [List.length_cons]; omega
      rw [he]
      exact .cons (.delete [] l₂ a) ih
  | cons_cons a h ih =>
      simpa using ih.append_left [a]

theorem ed_le_deficits (x y : List α) :
    ed x y ≤ (x.length - lcs x y) + (y.length - lcs x y) := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
  simpa [hz] using ed_le_of_script ((sublist_script hx).trans (sublist_script hy).symm)

theorem ed_le_twice_deficit (h : x.length = y.length) : ed x y ≤ 2 * deficit x y := by
  have := ed_le_deficits x y
  dsimp [deficit]
  omega

theorem substitution_script (h : x.length = y.length) : EditScript x y x.length := by
  induction x generalizing y with
  | nil =>
      have : y = [] := List.length_eq_zero_iff.mp h.symm
      subst y; exact .nil []
  | cons a x ih =>
      cases y with
      | nil => simp at h
      | cons b y =>
          have hh : x.length = y.length := by simpa using h
          exact .cons (.substitute [] x a b) (by simpa using (ih hh).append_left [b])

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

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

end TreeEdit.TorusTree

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.WordOperations ----
namespace OAI

namespace TreeEdit

universe u v

variable {α : Type u} {x y z : List α}

attribute [local instance] Classical.propDecidable

namespace EditStep

end EditStep

namespace EditScript

end EditScript

namespace Words

variable {β : Type v} {n : ℕ}

end Words

lemma sublist_ofFn_embedding {n N : ℕ} (f : Fin N → α) (e : Fin n ↪o Fin N) :
    (List.ofFn (fun i => f (e i))).Sublist (List.ofFn f) := by
  apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
  refine ⟨((Fin.castOrderIso List.length_ofFn).toOrderEmbedding.comp e).comp
    (Fin.castOrderIso List.length_ofFn.symm).toOrderEmbedding, ?_⟩
  intro i
  simp [List.get_eq_getElem, Fin.cast]

lemma length_flatten_ofFn {n C : ℕ} (x : Fin n → List α) (hx : ∀ i, (x i).length = C) :
    (List.ofFn x).flatten.length = n * C := by
  simp [List.length_flatten, List.map_ofFn, Function.comp_def, hx]

lemma ed_shifted_flatten {T C s : ℕ} (hs : s ≤ T) (x y : Fin T → List α)
    (hx : ∀ i, (x i).length = C) (hy : ∀ i, (y i).length = C)
    (he : ∀ a : Fin (T - s), x ⟨a.val + s, by have := a.isLt; omega⟩ =
      y ⟨a.val, by have := a.isLt; omega⟩) :
    ed (List.ofFn x).flatten (List.ofFn y).flatten ≤ 2 * s * C := by
  let f : Fin (T - s) ↪o Fin T := OrderEmbedding.ofStrictMono
    (fun a => ⟨a.val + s, by have := a.isLt; omega⟩) (by intro a b hab; simpa using hab)
  let g : Fin (T - s) ↪o Fin T := OrderEmbedding.ofStrictMono
    (fun a => ⟨a.val, by have := a.isLt; omega⟩) (by intro a b hab; exact hab)
  have hl := (sublist_ofFn_embedding x f).flatten
  have hr := (sublist_ofFn_embedding y g).flatten
  have he' : (fun a => x (f a)) = (fun a => y (g a)) := funext he
  rw [← he'] at hr
  have hlen := length_flatten_ofFn (fun a => x (f a)) (fun a => hx (f a))
  have hh := length_le_lcs hl hr
  rw [hlen] at hh
  have hc := ed_le_twice_deficit (x := (List.ofFn x).flatten) (y := (List.ofFn y).flatten)
    ((length_flatten_ofFn x hx).trans (length_flatten_ofFn y hy).symm)
  simp only [deficit, length_flatten_ofFn x hx] at hc
  have hmul : (T - s) * C + s * C = T * C := by rw [← Nat.add_mul, Nat.sub_add_cancel hs]
  have hdef : T * C - lcs (List.ofFn x).flatten (List.ofFn y).flatten ≤ s * C := by omega
  calc
    _ ≤ 2 * (T * C - lcs (List.ofFn x).flatten (List.ofFn y).flatten) := hc
    _ ≤ 2 * (s * C) := Nat.mul_le_mul_left 2 hdef
    _ = 2 * s * C := by ring

namespace Words

variable {β : Type v} {n : ℕ}

lemma ed_cycles_shift {m T B s : ℕ} {β : Fin m → Type*} (hs : s ≤ T)
    (x y : Fin T → ∀ i, Word (β i) B)
    (he : ∀ a : Fin (T - s), ∀ i,
      x ⟨a.val + s, by have := a.isLt; omega⟩ i =
      y ⟨a.val, by have := a.isLt; omega⟩ i) :
    ed (cycles x).val (cycles y).val ≤ 2 * s * (m * B) := by
  rw [cycles_val, cycles_val]
  apply ed_shifted_flatten hs
  · intro a; exact length_flatten_ofFn _ (fun i => by simp [(x a i).property])
  · intro a; exact length_flatten_ofFn _ (fun i => by simp [(y a i).property])
  · intro a
    congr 1
    apply congrArg List.ofFn
    funext i
    rw [he a i]

end Words

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.RandomCircle ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

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

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

lemma sampledWord_cycle_cost {I : Type} {g s L M T R : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M)
    (h : ℕ) (C : Config I L (g*s) (h+1)) (x : State (ZMod M) (g*s) (h+1))
    (a : ℕ) (ha : a ≤ T) :
    ed (sampledWord r j T R (h+1) C x).val
      (sampledWord r j T R (h+1) C (x + a • cycle (M := M) r j h C)).val ≤
        2 * a * ((g*s) * FiniteTree.length (g*s) T h) := by
  rw [sampledWord_succ r j hr hPM, sampledWord_succ r j hr hPM]
  apply Words.ed_cycles_shift ha
  intro b i
  apply congrArg (sampledWord r j T R h (C.2 i).2)
  change x i + (b.val + a) • cycle (M := M) r j h C i =
    (x i + a • cycle (M := M) r j h C i) + b.val • cycle (M := M) r j h C i
  rw [add_nsmul]
  abel

lemma cycle_period {I : Type} {g s L M : ℕ} [NeZero M]
    (r : I → ℕ) (j : Fin g → I) (h : ℕ) (C : Config I L (g*s) (h+1))
    (hPM : period r j C.1 ∣ M) : period r j C.1 • cycle (M := M) r j h C = 0 := by
  funext i
  change period r j C.1 • diagonal (A := ZMod M) (m := g*s) h
    ((coefficient r j C.1 (C.2 i).1 i) • (M / period r j C.1 : ZMod M)) = 0
  rw [← map_nsmul, smul_comm]
  have he : period r j C.1 • (M / period r j C.1 : ZMod M) = 0 := by
    rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hPM]
    exact ZMod.natCast_self M
  rw [he, smul_zero, map_zero]

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

end TreeEdit.TorusTree

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.FiniteFourier ----
namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace FiniteFourier

open scoped ComplexConjugate
open RCLike

variable {A : Type*} [Fintype A] [AddCommGroup A]

omit [Fintype A] in
lemma multiplier_nonneg (χ : AddChar A ℂ) (z : A) : 0 ≤ multiplier χ z := sq_nonneg _

lemma multiplier_eq (χ : AddChar A ℂ) (z : A) :
    multiplier χ z = 2 - 2 * (χ z).re := by
  rw [multiplier, Complex.sq_norm, Complex.normSq_sub]
  norm_num [Complex.normSq_eq_norm_sq, χ.norm_apply]

lemma average_const (c : ℝ) : average (fun _ : A => c) = c := by
  have hn : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [average, hn]

lemma average_multiplier (χ : AddChar A ℂ) :
    average (multiplier χ) = if χ = 0 then 0 else 2 := by
  classical
  by_cases hχ : χ = 0
  · subst χ; simp [average]
  · have hs : ∑ z, (χ z).re = 0 := by
      simpa [Complex.re_sum, hχ] using congr_arg Complex.re (χ.sum_eq_ite)
    have hn : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [average, multiplier_eq, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, hχ, hn]

end FiniteFourier

namespace FiniteFourier

variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

omit [Fintype B] in
lemma pushSpectrum_nonneg {H : AddChar A ℂ → ℝ} (hH : ∀ χ, 0 ≤ H χ) (f : B →+ A) :
    ∀ η, 0 ≤ pushSpectrum H f η := by
  classical
  intro η
  exact Finset.sum_nonneg fun χ _ => by split_ifs; exact hH χ; rfl

lemma pushSpectrum_sum (H : AddChar A ℂ → ℝ) (f : B →+ A) (g : AddChar B ℂ → ℝ) :
    ∑ η, g η * pushSpectrum H f η = ∑ χ, g (χ.compAddMonoidHom f) * H χ := by
  classical
  simp only [pushSpectrum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_eq_single (χ.compAddMonoidHom f)]
  · simp
  · intro η _ hη; simp [Ne.symm hη]
  · simp

lemma energy_push (H : AddChar A ℂ → ℝ) (f : B →+ A) (z : B) :
    energy (pushSpectrum H f) z = energy H (f z) := by
  rw [energy, pushSpectrum_sum]
  rfl

lemma average_energy (H : AddChar A ℂ → ℝ) :
    average (energy H) = 2 * ∑ χ, if χ = 0 then 0 else H χ := by
  classical
  calc
    _ = ∑ χ, average (multiplier χ) * H χ := by
      simp only [average, energy, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      simp only [average_multiplier, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      split_ifs <;> ring

end FiniteFourier

namespace FiniteFourier

variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

omit [Fintype A] in
lemma active_nonneg (χ : AddChar A ℂ) (v : A) : 0 ≤ active χ v := by
  unfold active; split_ifs <;> norm_num

lemma activeMass_nonneg {H : AddChar A ℂ → ℝ} (hH : ∀ χ, 0 ≤ H χ) (v : A) :
    0 ≤ activeMass H v := Finset.sum_nonneg fun χ _ => mul_nonneg (active_nonneg χ v) (hH χ)

lemma twice_activeMass_le_average {H : AddChar A ℂ → ℝ} (hH : ∀ χ, 0 ≤ H χ) (v : A) :
    2 * activeMass H v ≤ average (energy H) := by
  classical
  rw [average_energy, activeMass]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro χ _
  by_cases hχ : χ = 0
  · subst χ; simp [active]
  · by_cases hv : χ v = 1
    · simpa [active, hv, hχ] using hH χ
    · simp [active, hv, hχ]

end FiniteFourier

namespace FiniteFourier

variable {A : Type*} [Fintype A] [AddCommGroup A]

lemma average_mono {f g : A → ℝ} (h : ∀ x, f x ≤ g x) : average f ≤ average g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x) (by positivity)

lemma average_le {f : A → ℝ} {C : ℝ} (h : ∀ x, f x ≤ C) : average f ≤ C :=
  (average_mono h).trans_eq (average_const C)

end FiniteFourier

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CircleFourier ----
namespace OAI

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical
open TorusTree

lemma character_one {M : ℕ} [NeZero M] (χ : AddChar (ZMod M) ℂ) : χ 1 = 1 ↔ χ = 0 := by
  constructor
  · intro h
    ext x
    rw [← ZMod.natCast_zmod_val x,
      show (x.val : ZMod M) = x.val • (1 : ZMod M) by simp [nsmul_eq_mul],
      AddChar.map_nsmul_eq_pow, h, one_pow]
    rfl
  · rintro rfl
    rfl

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree

end TreeEdit.TorusFourier

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.SampledSpectrum ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree FiniteFourier FiniteProbability

lemma high_nonneg {M m : ℕ} [NeZero M] (h Q : ℕ) (χ : AddChar (State (ZMod M) m h) ℂ) : 0 ≤ high h Q χ := by
  unfold high; split_ifs <;> norm_num

lemma active_summary {M m : ℕ} [NeZero M] (h : ℕ) (χ : AddChar (State (ZMod M) m h) ℂ) :
    active χ (diagonal (A := ZMod M) (m := m) h 1) = if summary h χ = 0 then 0 else 1 := by
  have he : χ (diagonal (A := ZMod M) (m := m) h 1) = 1 ↔ summary h χ = 0 := character_one (summary h χ)
  unfold active
  simp only [he]

lemma branch_multiplier {I : Type} {g s L M b e K Q : ℕ} [NeZero M] (r : I → ℕ)
    (hr : ∀ i, Nat.Prime (r i)) (hinj : Function.Injective r) (j : Fin g ↪ I)
    (hb : 1 ≤ b) (hlower : ∀ i, b ≤ r i) (hQ : Q ≤ b^e) (hg : e+K ≤ g)
    (hM : (g*s+1)*Q < M) (h : ℕ) (C : Config I L (g*s) (h+1))
    (hPM : period r j C.1 ∣ M) (χ : AddChar (State (ZMod M) (g*s) (h+1)) ℂ) :
    (K : ℝ) * active χ (diagonal (A := ZMod M) (m := g*s) (h+1) 1) ≤
      (∑ i : Fin (g*s), active (χ.compAddMonoidHom (child (A := ZMod M) h i)) (diagonal (A := ZMod M) (m := g*s) h 1)) +
      K * (high (h+1) Q χ + (∑ i : Fin (g*s), high h Q (χ.compAddMonoidHom (child (A := ZMod M) h i))) +
        active χ (cycle (M := M) r j h C)) := by
  let S := ∑ i : Fin (g*s), active (χ.compAddMonoidHom (child (A := ZMod M) h i)) (diagonal (A := ZMod M) (m := g*s) h 1)
  let E := ∑ i : Fin (g*s), high h Q (χ.compAddMonoidHom (child (A := ZMod M) h i))
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => active_nonneg _ _
  have hE : 0 ≤ E := Finset.sum_nonneg fun i _ => high_nonneg _ _ _
  have hA := active_nonneg χ (cycle (M := M) r j h C)
  have hH := high_nonneg (h+1) Q χ
  change _ ≤ S + K * (high (h+1) Q χ + E + active χ (cycle (M := M) r j h C))
  rw [active_summary]
  split_ifs with hn
  · simp only [mul_zero]
    exact add_nonneg hS (mul_nonneg (Nat.cast_nonneg (α := ℝ) K) (add_nonneg (add_nonneg hH hE) hA))
  · simp only [mul_one]
    by_cases hp : (Q : ℝ) ≤ |(centered (summary (h+1) χ) : ℝ)|
    · rw [high, ite_eq_left hp]
      nlinarith [Nat.cast_nonneg (α := ℝ) K]
    by_cases hc : ∃ i : Fin (g*s), (Q : ℝ) ≤ |(centered (summary h (χ.compAddMonoidHom (child (A := ZMod M) h i))) : ℝ)|
    · obtain ⟨i, hi⟩ := hc
      have hei : 1 ≤ E := by
        calc
          1 = high h Q (χ.compAddMonoidHom (child (A := ZMod M) h i)) := by simp only [high, ite_eq_left hi]
          _ ≤ E := Finset.single_le_sum (f := fun v => high h Q (χ.compAddMonoidHom (child (A := ZMod M) h v))) (fun v _ => high_nonneg _ _ _) (Finset.mem_univ i)
      nlinarith [Nat.cast_nonneg (α := ℝ) K]
    by_cases hχ : χ (cycle (M := M) r j h C) = 1
    · have hh := branch_summaries r hr hinj j hb hlower hQ hg hM h C hPM χ (lt_of_not_ge hp)
        (fun i => lt_of_not_ge (fun hi => hc ⟨i,hi⟩)) hχ hn
      have hs : (K : ℝ) ≤ S := by
        dsimp [S]
        simp_rw [active_summary]
        have he : (∑ i : Fin (g*s), if summary h (χ.compAddMonoidHom (child (A := ZMod M) h i)) = 0 then (0 : ℝ) else 1) =
            ((Finset.univ.filter (fun i : Fin (g*s) => summary h (χ.compAddMonoidHom (child (A := ZMod M) h i)) ≠ 0)).card : ℝ) := by
          simpa only [ite_not] using (Finset.sum_boole (fun i : Fin (g*s) => summary h (χ.compAddMonoidHom (child (A := ZMod M) h i)) ≠ 0) Finset.univ)
        rw [he]
        exact_mod_cast hh
      nlinarith [Nat.cast_nonneg (α := ℝ) K]
    · rw [active, ite_eq_right hχ]
      nlinarith [Nat.cast_nonneg (α := ℝ) K]

lemma branch_mass {I : Type} {g s L M b e K Q : ℕ} [NeZero M] (r : I → ℕ)
    (hr : ∀ i, Nat.Prime (r i)) (hinj : Function.Injective r) (j : Fin g ↪ I)
    (hb : 1 ≤ b) (hlower : ∀ i, b ≤ r i) (hQ : Q ≤ b^e) (hg : e+K ≤ g)
    (hM : (g*s+1)*Q < M) (h : ℕ) (C : Config I L (g*s) (h+1))
    (hPM : period r j C.1 ∣ M) (H : AddChar (State (ZMod M) (g*s) (h+1)) ℂ → ℝ) (hH : ∀ χ, 0 ≤ H χ) :
    (K : ℝ) * activeMass H (diagonal (A := ZMod M) (m := g*s) (h+1) 1) ≤
      (∑ i : Fin (g*s), activeMass (pushSpectrum H (child (A := ZMod M) h i)) (diagonal (A := ZMod M) (m := g*s) h 1)) +
      K * (highMass (h+1) Q H + (∑ i : Fin (g*s), highMass h Q (pushSpectrum H (child (A := ZMod M) h i))) +
        activeMass H (cycle (M := M) r j h C)) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun χ _ => mul_le_mul_of_nonneg_right
    (branch_multiplier r hr hinj j hb hlower hQ hg hM h C hPM χ) (hH χ))
  simp only [activeMass, highMass, pushSpectrum_sum] at hh ⊢
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc, ← Finset.mul_sum] at hh
  rw [Finset.sum_comm, Finset.sum_comm (f := fun χ i => high h Q (χ.compAddMonoidHom (child (A := ZMod M) h i)) * H χ)] at hh
  exact hh

lemma SpectralBound.child {I : Type} {g s L M T R h : ℕ} [NeZero M] [NeZero R]
    {r : I → ℕ} {j : Fin g → I} (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M)
    {C : Config I L (g*s) (h+1)} {H : AddChar (State (ZMod M) (g*s) (h+1)) ℂ → ℝ} {D : ℝ}
    (hD : 0 ≤ D) (hb : SpectralBound (R := R) r j T (h+1) C H D) (i : Fin (g*s)) :
    SpectralBound (R := R) r j T h (C.2 i).2 (pushSpectrum H (child (A := ZMod M) h i)) (D*T) := by
  intro z
  rw [energy_push]
  exact (hb _).trans ((mul_le_mul_of_nonneg_left (sampledWord_child_mean r j hr hPM h C i z) hD).trans_eq (by ring))

lemma high_estimate {I : Type} {g s L M T R D Q J h : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M)
    (hD : 0 < D) (hQ : 0 < Q) (hMR : M = R*D) (hMQ : M = J*Q)
    (C : Config I L (g*s) h) (H : AddChar (State (ZMod M) (g*s) h) ℂ → ℝ) (a : ℝ)
    (hH : ∀ χ, 0 ≤ H χ) (ha : 0 ≤ a) (hb : SpectralBound (R := R) r j T h C H a) :
    highMass h Q H ≤ a * FiniteTree.length (g*s) T h * R / Q := by
  have hJ : 0 < J := by have := NeZero.pos M; nlinarith
  have hd (χ : AddChar (State (ZMod M) (g*s) h) ℂ) :
      (J : ℝ) * high h Q χ ≤ ∑ n ∈ Finset.range J, multiplier χ (diagonal (A := ZMod M) (m := g*s) h (n+1)) := by
    unfold high
    split_ifs with hc
    · simpa only [mul_one, multiplier_eq, summary, AddChar.compAddMonoidHom_apply] using sum_chord_detect hQ hMQ (summary h χ) hc
    · simp only [mul_zero]
      exact Finset.sum_nonneg fun n _ => multiplier_nonneg χ _
  have hcost (n : ℕ) (hn : n ∈ Finset.range J) :
      energy H (diagonal (A := ZMod M) (m := g*s) h (n+1)) ≤ a * FiniteTree.length (g*s) T h * R / Q := by
    apply (hb _).trans
    have ht := sampledWord_tiny (T := T) r j hr hPM hD hQ hMR hMQ h C (n+1) (Finset.mem_range.mp hn)
    exact (mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add, Nat.cast_one] using ht) ha).trans_eq (by ring)
  have hh : (J : ℝ) * highMass h Q H ≤ J * (a * FiniteTree.length (g*s) T h * R / Q) := by
    calc
      _ ≤ ∑ χ, (∑ n ∈ Finset.range J, multiplier χ (diagonal (A := ZMod M) (m := g*s) h (n+1))) * H χ := by
        rw [highMass, Finset.mul_sum]
        exact Finset.sum_le_sum fun χ _ => by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hd χ) (hH χ)
      _ = ∑ n ∈ Finset.range J, energy H (diagonal (A := ZMod M) (m := g*s) h (n+1)) := by
        simp only [energy, Finset.sum_mul]
        rw [Finset.sum_comm]
      _ ≤ ∑ _n ∈ Finset.range J, (a * FiniteTree.length (g*s) T h * R / Q) := Finset.sum_le_sum hcost
      _ = _ := by simp
  exact (mul_le_mul_iff_right₀ (by exact_mod_cast hJ : (0 : ℝ) < J)).mp hh

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree FiniteFourier FiniteProbability

lemma cycle_estimate {I : Type} {g s L M T R V h : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M) (hPV : ∀ σ : Equiv.Perm I, period r j σ ≤ V) (hVT : V ≤ T)
    (C : Config I L (g*s) (h+1)) (H : AddChar (State (ZMod M) (g*s) (h+1)) ℂ → ℝ) (a : ℝ)
    (hH : ∀ χ, 0 ≤ H χ) (ha : 0 ≤ a) (hb : SpectralBound (R := R) r j T (h+1) C H a) :
    activeMass H (cycle (M := M) r j h C) ≤ a * FiniteTree.length (g*s) T (h+1) * (2 * V) / T := by
  let P := period r j C.1
  let v := cycle (M := M) r j h C
  have hP : 0 < P := period_pos hr j C.1
  have hT : 0 < T := hP.trans_le ((hPV C.1).trans hVT)
  have hd (χ : AddChar (State (ZMod M) (g*s) (h+1)) ℂ) :
      (P : ℝ) * active χ v ≤ ∑ n ∈ Finset.range P, multiplier χ ((n+1) • v) := by
    by_cases hc : χ v = 1
    · simp only [active, ite_eq_left hc, mul_zero]
      exact Finset.sum_nonneg fun n _ => multiplier_nonneg χ _
    · have hper : (χ v)^P = 1 := by
        rw [← AddChar.map_nsmul_eq_pow, cycle_period r j h C (hPM C.1), AddChar.map_zero_eq_one]
      rw [sum_multiplier_period χ v P hc hper, active, ite_eq_right hc]
      nlinarith [Nat.cast_nonneg (α := ℝ) P]
  have hcost (n : ℕ) (hn : n ∈ Finset.range P) : energy H ((n+1) • v) ≤ a * (2 * V * ((g*s) * FiniteTree.length (g*s) T h)) := by
    apply (hb _).trans
    apply mul_le_mul_of_nonneg_left _ ha
    apply (mean_le (fun x => show
        (ed (sampledWord r j T R (h+1) C x).val (sampledWord r j T R (h+1) C (x+(n+1) • v)).val : ℝ) ≤
        (2 * V * ((g*s) * FiniteTree.length (g*s) T h) : ℝ) from by
      have hnV : n+1 ≤ V := (Finset.mem_range.mp hn).trans_le (hPV C.1)
      have hh := sampledWord_cycle_cost (R := R) (T := T) r j hr hPM h C x (n+1) (hnV.trans hVT)
      exact_mod_cast hh.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hnV)))).trans_eq
    exact mean_const _
  have hh : (P : ℝ) * activeMass H v ≤ P * (a * (2 * V * ((g*s) * FiniteTree.length (g*s) T h))) := by
    calc
      _ ≤ ∑ χ, (∑ n ∈ Finset.range P, multiplier χ ((n+1) • v)) * H χ := by
        rw [activeMass, Finset.mul_sum]
        exact Finset.sum_le_sum fun χ _ => by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hd χ) (hH χ)
      _ = ∑ n ∈ Finset.range P, energy H ((n+1) • v) := by
        simp only [energy, Finset.sum_mul]
        rw [Finset.sum_comm]
      _ ≤ ∑ _n ∈ Finset.range P, a * (2 * V * ((g*s) * FiniteTree.length (g*s) T h)) := Finset.sum_le_sum hcost
      _ = _ := by simp
  have hc := (mul_le_mul_iff_right₀ (by exact_mod_cast hP : (0 : ℝ) < P)).mp hh
  apply hc.trans_eq
  simp only [FiniteTree.length, Nat.cast_mul]
  have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp

lemma mass_bound {I : Type} {g s L M T R D Q J V b e K h : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g ↪ I) (hr : ∀ i, Nat.Prime (r i)) (hinj : Function.Injective r)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M) (hPV : ∀ σ : Equiv.Perm I, period r j σ ≤ V) (hVT : V ≤ T)
    (hD : 0 < D) (hQ : 0 < Q) (hMR : M = R*D) (hMQ : M = J*Q)
    (hb : 1 ≤ b) (hlower : ∀ i, b ≤ r i) (hQpow : Q ≤ b^e) (hg : e+K ≤ g) (hK : 1 ≤ K)
    (hM : (g*s+1)*Q < M)
    (C : Config I L (g*s) h) (H : AddChar (State (ZMod M) (g*s) h) ℂ → ℝ) (a : ℝ)
    (hH : ∀ χ, 0 ≤ H χ) (ha : 0 ≤ a) (hbound : SpectralBound (R := R) r j T h C H a) :
    activeMass H (diagonal (A := ZMod M) (m := g*s) h 1) ≤
      a * FiniteTree.length (g*s) T h * ((K : ℝ)⁻¹^h + h * (2*(R : ℝ)/Q + 2*(V : ℝ)/T)) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have herr : 0 ≤ 2*(R : ℝ)/Q + 2*(V : ℝ)/T := by positivity
  induction h generalizing a with
  | zero =>
    have hc (z : State (ZMod M) (g*s) 0) : energy H z ≤ a := by
      apply (hbound z).trans
      have hm : mean (fun x : State (ZMod M) (g*s) 0 =>
          (ed (sampledWord r j T R 0 C x).val (sampledWord r j T R 0 C (x+z)).val : ℝ)) ≤ 1 := by
        apply (mean_le (fun x => show
          (ed (sampledWord r j T R 0 C x).val (sampledWord r j T R 0 C (x+z)).val : ℝ) ≤ 1 from by
            have hh := ed_le_of_script (substitution_script
              (x := (sampledWord r j T R 0 C x).val) (y := (sampledWord r j T R 0 C (x+z)).val)
              (by simp [(sampledWord r j T R 0 C x).property, (sampledWord r j T R 0 C (x+z)).property]))
            simpa [(sampledWord r j T R 0 C x).property, FiniteTree.length] using (Nat.cast_le (α := ℝ)).mpr hh)).trans_eq
        exact mean_const 1
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hm ha
    have hh := (twice_activeMass_le_average hH (diagonal (A := ZMod M) (m := g*s) 0 1)).trans (average_le hc)
    simpa only [FiniteTree.length, Nat.cast_one, mul_one, pow_zero, Nat.cast_zero, zero_mul, add_zero] using
      (show activeMass H (diagonal (A := ZMod M) (m := g*s) 0 1) ≤ a by linarith [activeMass_nonneg hH (diagonal (A := ZMod M) (m := g*s) 0 1)])
  | succ h ih =>
    have hchild (i : Fin (g*s)) := ih (C.2 i).2 (pushSpectrum H (child (A := ZMod M) h i)) (a*T)
      (pushSpectrum_nonneg hH _) (mul_nonneg ha (Nat.cast_nonneg _)) (hbound.child (fun i => (hr i).pos) hPM ha i)
    have hs : (∑ i : Fin (g*s), activeMass (pushSpectrum H (child (A := ZMod M) h i))
        (diagonal (A := ZMod M) (m := g*s) h 1)) ≤
        a * FiniteTree.length (g*s) T (h+1) * ((K : ℝ)⁻¹^h + h * (2*(R : ℝ)/Q + 2*(V : ℝ)/T)) := by
      apply (Finset.sum_le_sum fun i _ => hchild i).trans_eq
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, FiniteTree.length, Nat.cast_mul]
      ring
    have hhi := high_estimate r j (fun i => (hr i).pos) hPM hD hQ hMR hMQ C H a hH ha hbound
    have hhis (i : Fin (g*s)) := high_estimate r j (fun i => (hr i).pos) hPM hD hQ hMR hMQ
      (C.2 i).2 (pushSpectrum H (child (A := ZMod M) h i)) (a*T) (pushSpectrum_nonneg hH _)
      (mul_nonneg ha (Nat.cast_nonneg _)) (hbound.child (fun i => (hr i).pos) hPM ha i)
    have hhs : (∑ i : Fin (g*s), highMass h Q (pushSpectrum H (child (A := ZMod M) h i))) ≤
        a * FiniteTree.length (g*s) T (h+1) * R / Q := by
      apply (Finset.sum_le_sum fun i _ => hhis i).trans_eq
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, FiniteTree.length, Nat.cast_mul]
      ring
    have hcy := cycle_estimate r j (fun i => (hr i).pos) hPM hPV hVT C H a hH ha hbound
    have hbr := branch_mass r hr hinj j hb hlower hQpow hg hM h C (hPM C.1) H hH
    have herror : highMass (h+1) Q H + (∑ i : Fin (g*s), highMass h Q (pushSpectrum H (child (A := ZMod M) h i))) +
        activeMass H (cycle (M := M) r j h C) ≤
      a * FiniteTree.length (g*s) T (h+1) * (2*(R : ℝ)/Q + 2*(V : ℝ)/T) := by
      calc
        _ ≤ a * FiniteTree.length (g*s) T (h+1) * R/Q + a * FiniteTree.length (g*s) T (h+1) * R/Q +
          a * FiniteTree.length (g*s) T (h+1) * (2*V)/T := add_le_add (add_le_add hhi hhs) hcy
        _ = _ := by ring
    have hmain := hbr.trans (add_le_add hs (mul_le_mul_of_nonneg_left herror hKpos.le))
    have hkn : 0 ≤ a * (FiniteTree.length (g*s) T (h+1) : ℝ) * h * (2*(R : ℝ)/Q + 2*(V : ℝ)/T) * ((K : ℝ)-1) := by positivity
    have he : (K : ℝ) * (a * FiniteTree.length (g*s) T (h+1) * ((K : ℝ)⁻¹^(h+1) + (h+1) * (2*(R : ℝ)/Q + 2*(V : ℝ)/T))) =
        (a * FiniteTree.length (g*s) T (h+1) * ((K : ℝ)⁻¹^h + h * (2*(R : ℝ)/Q + 2*(V : ℝ)/T)) +
          K * (a * FiniteTree.length (g*s) T (h+1) * (2*(R : ℝ)/Q + 2*(V : ℝ)/T))) +
        a * FiniteTree.length (g*s) T (h+1) * h * (2*(R : ℝ)/Q + 2*(V : ℝ)/T) * ((K : ℝ)-1) := by
      rw [pow_succ]
      field_simp
      ring
    apply (mul_le_mul_iff_right₀ hKpos).mp
    simp only [Nat.cast_add, Nat.cast_one]
    rw [he]
    linarith

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree FiniteFourier FiniteProbability

end TreeEdit.TorusFourier

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree FiniteFourier FiniteProbability


theorem solution : type_of% @_root_.OAI.TreeEdit.TorusFourier.mass_bound := @_root_.OAI.TreeEdit.TorusFourier.mass_bound
