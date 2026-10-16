-- Prove2me | solution 1 for OAI.TreeEdit.binary_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:26:06.091682+00:00
-- url     : https://prove2.me/submissions/7ed214e3-6f98-4fb0-98b5-ca5fd84cd033

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/DistortionTransfer.lean:L68-L138
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.binary_transfer. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleObstruction
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleParameters
import Definitions.Def_OAI_Combinatorics_TreeEdit_Delimiter
import Definitions.Def_OAI_Combinatorics_TreeEdit_DistortionTransfer

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

theorem encode_step {P : ℕ} {β : Type v} (c : α → Word β P) (h : EditStep x y) :
    EditScript (encode c x) (encode c y) P := by
  cases h with
  | insert p q a =>
      simpa [List.append_assoc, (c a).property] using
        (((EditScript.erase (c a).val).symm.append_right (encode c q)).append_left (encode c p))
  | delete p q a =>
      simpa [List.append_assoc, (c a).property] using
        (((EditScript.erase (c a).val).append_right (encode c q)).append_left (encode c p))
  | substitute p q a b =>
      have hh := substitution_script ((c a).property.trans (c b).property.symm)
      simpa [List.append_assoc, (c a).property] using
        ((hh.append_right (encode c q)).append_left (encode c p))

theorem encode_script {P n : ℕ} {β : Type v} (c : α → Word β P) (h : EditScript x y n) :
    EditScript (encode c x) (encode c y) (P * n) := by
  induction h with
  | nil => simpa using EditScript.nil (encode c _)
  | cons h _ ih =>
      simpa [Nat.mul_add, Nat.add_comm] using (encode_step c h).trans ih

theorem ed_encode_le {P : ℕ} {β : Type v} (c : α → Word β P) (x y : List α) :
    ed (encode c x) (encode c y) ≤ P * ed x y :=
  ed_le_of_script (encode_script c (ed_script x y))

end TreeEdit

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

lemma average_const (c : ℝ) : average (fun _ : A => c) = c := by
  have hn : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [average, hn]

end FiniteFourier

namespace FiniteFourier

variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

end FiniteFourier

namespace FiniteFourier

variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

end FiniteFourier

namespace FiniteFourier

variable {A : Type*} [Fintype A] [AddCommGroup A]

lemma average_mono {f g : A → ℝ} (h : ∀ x, f x ≤ g x) : average f ≤ average g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x) (by positivity)

end FiniteFourier

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.DistortionTransfer ----
namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

lemma ratio_set_finite {β : Type*} [Finite β] (f : β → β → ℝ) :
    {r | ∃ x y, x ≠ y ∧ r = f x y}.Finite := by
  apply (Set.finite_range (fun xy : β × β => f xy.1 xy.2)).subset
  rintro r ⟨x, y, _, rfl⟩
  exact ⟨(x,y), rfl⟩

lemma exists_realL1_injective (β : Type*) [Fintype β] : ∃ f : β → RealL1, Function.Injective f := by
  classical
  refine ⟨fun x => lp.single 1 0 ((Fintype.equivFin β x).val : ℝ), ?_⟩
  intro x y h
  have hh := congrArg (fun v : RealL1 => v 0) h
  simp only [lp.single_apply, Pi.single_eq_same] at hh
  exact (Fintype.equivFin β).injective (Fin.ext (Nat.cast_injective hh))

lemma c1_lower {W : Finset (List Bool)} {L : ℝ}
    (h : ∀ f : W → RealL1, Function.Injective f → L ≤ distortion W f) : L ≤ c1 W := by
  apply le_csInf
  · obtain ⟨f, hf⟩ := exists_realL1_injective W
    exact ⟨distortion W f, f, hf, rfl⟩
  · rintro D ⟨f, hf, rfl⟩
    exact h f hf

lemma stretch_nonneg {W : Finset (List Bool)} (hW : 2 ≤ W.card) (f : W → RealL1) : 0 ≤ stretch W f := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < W.card)
  apply le_trans (div_nonneg (dist_nonneg (x := f ⟨x,hx⟩) (y := f ⟨y,hy⟩)) (Nat.cast_nonneg _))
  apply le_csSup (ratio_set_finite _).bddAbove
  exact ⟨⟨x,hx⟩, ⟨y,hy⟩, fun h => hxy (congrArg Subtype.val h), rfl⟩

lemma contraction_nonneg {W : Finset (List Bool)} (hW : 2 ≤ W.card) (f : W → RealL1) : 0 ≤ contraction W f := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < W.card)
  apply le_trans (div_nonneg (Nat.cast_nonneg (ed x y)) (dist_nonneg (x := f ⟨x,hx⟩) (y := f ⟨y,hy⟩)))
  apply le_csSup (ratio_set_finite _).bddAbove
  exact ⟨⟨x,hx⟩, ⟨y,hy⟩, fun h => hxy (congrArg Subtype.val h), rfl⟩

lemma dist_le_stretch {W : Finset (List Bool)} (f : W → RealL1) (x y : W) :
    dist (f x) (f y) ≤ stretch W f * ed x.val y.val := by
  by_cases hxy : x = y
  · subst y; simp
  · have he : (0 : ℝ) < ed x.val y.val := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => hxy (Subtype.ext (ed_eq_zero_iff.mp h)))
    apply (div_le_iff₀ he).mp
    exact le_csSup (ratio_set_finite _).bddAbove ⟨x, y, hxy, rfl⟩

lemma ed_le_contraction {W : Finset (List Bool)} (f : W → RealL1) (hf : Function.Injective f) (x y : W) :
    (ed x.val y.val : ℝ) ≤ contraction W f * dist (f x) (f y) := by
  by_cases hxy : x = y
  · subst y; simp
  · have hd : 0 < dist (f x) (f y) := dist_pos.mpr (fun h => hxy (hf h))
    apply (div_le_iff₀ hd).mp
    exact le_csSup (ratio_set_finite _).bddAbove ⟨x, y, hxy, rfl⟩

theorem binary_transfer {A Γ : Type*} [Fintype A] [AddCommGroup A] [Fintype Γ]
    {M P : ℕ} (hM : 0 < M) (hP : 0 < P) (w : A → Word Γ M) (z : A)
    (c : Γ → Word Bool P) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hcode : ∀ x y : Word Γ M,
      (P : ℝ) / 804 * ed x.val y.val ≤ ed (encode c x.val) (encode c y.val))
    (hsep : ∀ x, (M : ℝ) ≤ a * ed (w x).val (w (x + z)).val)
    (hobs : ∀ (F : A → RealL1) (C : ℝ), 0 ≤ C →
      (∀ x y, dist (F x) (F y) ≤ C * ed (w x).val (w y).val) →
      FiniteFourier.average (fun x => dist (F x) (F (x + z))) ≤ C * M * b) :
    ∃ W : Finset (List Bool), 2 ≤ W.card ∧ (∀ v ∈ W, v.length = M * P) ∧
      (804 * a * b)⁻¹ ≤ c1 W := by
  classical
  let enc (x : A) := encode c (w x).val
  let W := Finset.univ.image enc
  have hmem (x : A) : enc x ∈ W := Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hne (x : A) : enc x ≠ enc (x + z) := by
    intro he
    have hc := hcode (w x) (w (x + z))
    rw [← show enc x = encode c (w x).val from rfl,
      ← show enc (x + z) = encode c (w (x + z)).val from rfl, he, ed_self] at hc
    have he0 : (ed (w x).val (w (x + z)).val : ℝ) = 0 := by
      have hp : (0 : ℝ) < P := by exact_mod_cast hP
      nlinarith only [hc, hp, (Nat.cast_nonneg (ed (w x).val (w (x + z)).val) : (0 : ℝ) ≤ ed (w x).val (w (x + z)).val)]
    have hh := hsep x
    rw [he0, mul_zero] at hh
    exact (not_le_of_gt (by exact_mod_cast hM : (0 : ℝ) < M)) hh
  have hW : 2 ≤ W.card := by
    have hh := Finset.one_lt_card.mpr ⟨enc 0, hmem 0, enc (0 + z), hmem _, hne 0⟩
    omega
  refine ⟨W, hW, ?_, ?_⟩
  · intro v hv
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
    simp [enc, length_encode, (w x).property]
  · apply c1_lower
    intro f hf
    let F : A → RealL1 := fun x => f ⟨enc x, hmem x⟩
    let S := stretch W f
    let D := contraction W f
    have hS : 0 ≤ S := stretch_nonneg hW f
    have hD : 0 ≤ D := contraction_nonneg hW f
    have hlip (x y : A) : dist (F x) (F y) ≤ (S * P) * ed (w x).val (w y).val := by
      calc
        _ ≤ S * ed (enc x) (enc y) := dist_le_stretch (W := W) f ⟨enc x, hmem x⟩ ⟨enc y, hmem y⟩
        _ ≤ S * (P * (ed (w x).val (w y).val : ℝ)) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast ed_encode_le c (w x).val (w y).val) hS
        _ = _ := by ring
    have hu := hobs F (S * P) (mul_nonneg hS (Nat.cast_nonneg _)) hlip
    have hl (x : A) : (P : ℝ) * M ≤ 804 * a * D * dist (F x) (F (x + z)) := by
      have hc := hcode (w x) (w (x + z))
      have hd := ed_le_contraction f hf ⟨enc x, hmem x⟩ ⟨enc (x + z), hmem _⟩
      calc
        _ ≤ P * (a * ed (w x).val (w (x + z)).val) := mul_le_mul_of_nonneg_left (hsep x) (by positivity)
        _ = a * (P * ed (w x).val (w (x + z)).val) := by ring
        _ ≤ a * (804 * ed (enc x) (enc (x + z))) := mul_le_mul_of_nonneg_left (by dsimp [enc]; linarith) ha.le
        _ ≤ a * (804 * (D * dist (F x) (F (x + z)))) := by gcongr
        _ = _ := by ring
    have hav := FiniteFourier.average_mono hl
    rw [FiniteFourier.average_const] at hav
    have he : FiniteFourier.average (fun x => 804 * a * D * dist (F x) (F (x + z))) =
      (804 * a * D) * FiniteFourier.average (fun x => dist (F x) (F (x + z))) := by
      simp only [FiniteFourier.average, ← Finset.mul_sum]
      ring
    rw [he] at hav
    have hh := hav.trans (mul_le_mul_of_nonneg_left hu (by positivity))
    have hPM : (0 : ℝ) < P * M := by positivity
    have hd : 1 ≤ 804 * a * b * distortion W f := by
      apply (mul_le_mul_iff_left₀ hPM).mp
      change 1 * (P * M : ℝ) ≤ (804 * a * b * (S * D)) * (P * M)
      convert hh using 1 <;> first | rfl | ring
    rw [inv_eq_one_div]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 804 * a * b)).mpr (by simpa only [mul_comm] using hd)

end TreeEdit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.TreeEdit.binary_transfer := @_root_.OAI.TreeEdit.binary_transfer
