-- Prove2me | solution 1 for OAI.TreeEdit.TorusTree.binary_witness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:30:57.82585+00:00
-- url     : https://prove2.me/submissions/b870d3dc-c0f1-4326-87e9-49831388762a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/TorusLowerBound.lean:L21-L95
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.TorusTree.binary_witness. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_TreeEdit_TorusLowerBound
import Theorems.Thm_OAI_TreeEdit_Delimiter_alignment_bound
import Theorems.Thm_OAI_TreeEdit_TorusFourier_displacement_bound
import Theorems.Thm_OAI_TreeEdit_TorusTree_binaryWidth_le
import Theorems.Thm_OAI_TreeEdit_TorusTree_fine_parameters
import Theorems.Thm_OAI_TreeEdit_TorusTree_sampled_separation
import Theorems.Thm_OAI_TreeEdit_binary_transfer
import Theorems.Thm_OAI_TreeEdit_get_encode_block
import Theorems.Thm_OAI_TreeEdit_segment_encode_block

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

theorem sublist_erase_one {a : α} {p q z : List α} (h : z.Sublist (p ++ a :: q)) :
    ∃ z' : List α, z'.Sublist z ∧ z'.Sublist (p ++ q) ∧ z.length ≤ z'.length + 1 := by
  obtain ⟨z₁, z₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp h
  rcases List.sublist_cons_iff.mp h₂ with h₂ | ⟨r, rfl, hr⟩
  · exact ⟨z₁ ++ z₂, List.Sublist.refl _, h₁.append h₂, Nat.le_succ _⟩
  · refine ⟨z₁ ++ r, (List.Sublist.refl z₁).append ((List.Sublist.refl r).cons a),
      h₁.append hr, ?_⟩
    simp only [List.length_append, List.length_cons]
    omega

theorem lcs_step_loss (z : List α) (h : EditStep x y) : lcs z x ≤ lcs z y + 1 := by
  obtain ⟨s, hz, hx, hs⟩ := exists_lcs z x
  cases h with
  | insert p q a =>
      have hxy : (p ++ q).Sublist (p ++ a :: q) :=
        (List.Sublist.refl p).append ((List.Sublist.refl q).cons a)
      have hh := length_le_lcs hz (hx.trans hxy)
      omega
  | delete p q a =>
      obtain ⟨s', hss, hp, hh⟩ := sublist_erase_one hx
      have := length_le_lcs (hss.trans hz) hp
      omega
  | substitute p q a b =>
      obtain ⟨s', hss, hp, hh⟩ := sublist_erase_one hx
      have hpq : (p ++ q).Sublist (p ++ b :: q) :=
        (List.Sublist.refl p).append ((List.Sublist.refl q).cons b)
      have := length_le_lcs (hss.trans hz) (hp.trans hpq)
      omega

theorem lcs_script_loss (z : List α) {n : ℕ} (h : EditScript x y n) :
    lcs z x ≤ lcs z y + n := by
  induction h with
  | nil => simp
  | cons h _ ih => have hh := lcs_step_loss z h; omega

theorem deficit_le_ed (x y : List α) : deficit x y ≤ ed x y := by
  have h := lcs_script_loss x (ed_script x y)
  simp only [lcs_self] at h
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

-- ---- from OAI.Combinatorics.TreeEdit.Alignments ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

namespace Alignment

variable {n : ℕ}

end Alignment

theorem exists_lcs_alignment (x y : List α) : Nonempty (Alignment x y (lcs x y)) := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx
  obtain ⟨g, hg⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hy
  refine ⟨⟨(Fin.castOrderIso hz.symm).toOrderEmbedding.comp f,
    (Fin.castOrderIso hz.symm).toOrderEmbedding.comp g, ?_⟩⟩
  intro i
  exact (hf (Fin.cast hz.symm i)).symm.trans (hg (Fin.cast hz.symm i))

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.SegmentComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

theorem length_segment {β : Type*} (x : List β) {start len : ℕ}
    (h : start + len ≤ x.length) : (segment x start len).length = len := by
  simp only [segment, List.length_take, List.length_drop]
  omega

theorem segment_get {β : Type*} (x : List β) (start len i : ℕ)
    (hi : i < (segment x start len).length) :
    (segment x start len)[i] = x[start + i]'(by
      simp only [segment, List.length_take, List.length_drop] at hi
      omega) := by
  simp only [segment, List.getElem_take, List.getElem_drop]

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.TreeArithmetic ----
namespace OAI

namespace TreeEdit.FiniteTree

universe u

attribute [local instance] Classical.propDecidable

lemma length_eq (m T h : ℕ) : length m T h = (m * T) ^ h := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [length, ih, pow_succ]; ring

end TreeEdit.FiniteTree

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CircleSeparation ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical

lemma symbol_card (m R h : ℕ) : Fintype.card (Symbol m R h) = m ^ h * R := by
  induction h with
  | zero => simp [Symbol]
  | succ h ih => simp only [Symbol, Fintype.card_sigma, ih, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, pow_succ]; ring

end TreeEdit.TorusTree

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CircleObstruction ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter FiniteProbability

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter

lemma period_upper {k : ℕ} (j : Fin (16*k) ↪ Pool k) (σ : Equiv.Perm (Pool k)) :
    period poolPrime j σ ≤ k^(48*k) := by
  calc
    _ ≤ ∏ _i : Fin (16*k), k^3 := Finset.prod_le_prod' (fun i _ => (pool_properties (σ (j i))).2.2)
    _ = k^(48*k) := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]; congr 1; omega

lemma spectrum_error {k : ℕ} (hk : 2 ≤ k) :
    4*((k : ℝ)⁻¹^k+k*(2*(resolution k : ℝ)/cutoff k+2*(k^(48*k) : ℕ)/repetitions k)) ≤
      20*(k : ℝ)⁻¹^k := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hkpos : (0 : ℝ) < k := by linarith
  have hr : (resolution k : ℝ)/cutoff k = (k : ℝ)⁻¹^(4*k) := by
    dsimp only [resolution, cutoff]
    have he : 12*k = 8*k+4*k := by omega
    rw [Nat.cast_pow, Nat.cast_pow, he, pow_add, div_mul_eq_div_div, div_self (pow_ne_zero _ hkpos.ne'), one_div, inv_pow]
  have ht : ((k^(48*k) : ℕ) : ℝ)/repetitions k = (k : ℝ)⁻¹^(4*k) := by
    dsimp only [repetitions]
    have he : 52*k = 48*k+4*k := by omega
    rw [Nat.cast_pow, Nat.cast_pow, he, pow_add, div_mul_eq_div_div, div_self (pow_ne_zero _ hkpos.ne'), one_div, inv_pow]
  have hi : (k : ℝ)*(k : ℝ)⁻¹^(4*k) ≤ (k : ℝ)⁻¹^k := by
    have hpow : (k : ℝ)^(k+1) ≤ (k : ℝ)^(4*k) := pow_le_pow_right₀ hkr (by omega)
    have hn : (k : ℝ)^k ≠ 0 := pow_ne_zero _ hkpos.ne'
    rw [inv_pow, inv_pow]
    apply (mul_le_mul_iff_left₀ (pow_pos hkpos k)).mp
    apply (mul_le_mul_iff_left₀ (pow_pos hkpos (4*k))).mp
    simpa only [mul_assoc, inv_mul_cancel₀ hn, mul_one, mul_inv_cancel₀ (pow_ne_zero _ hkpos.ne'), pow_succ, mul_left_comm, mul_comm] using hpow
  rw [mul_div_assoc, mul_div_assoc, hr, ht]
  nlinarith

theorem concrete_displacement {k : ℕ} (hk : 2 ≤ k) (j : Fin (16*k) ↪ Pool k)
    (C : Config (Pool k) (residueModulus k) (branching k) k)
    [NeZero (fineModulus j)] [NeZero (resolution k)]
    (F : State (ZMod (fineModulus j)) (branching k) k → RealL1) (a : ℝ) (ha : 0 ≤ a)
    (hlip : ∀ x y, dist (F x) (F y) ≤ a * ed (sampledWord poolPrime j (repetitions k) (resolution k) k C x).val
      (sampledWord poolPrime j (repetitions k) (resolution k) k C y).val) :
    FiniteFourier.average (fun x => dist (F x) (F (x + diagonal (A := ZMod (fineModulus j)) (m := branching k) k (fineModulus j/2 : ℕ)))) ≤
      a * FiniteTree.length (branching k) (repetitions k) k * (20*(k : ℝ)⁻¹^k) := by
  obtain ⟨_, _, hPM, hM, D, J, hD, hMR, hMQ⟩ := fine_parameters hk j
  have hQ : 0 < cutoff k := pow_pos (by omega) _
  have ht : k^(48*k) ≤ repetitions k := pow_le_pow_right₀ (by omega) (by omega)
  have hpow : cutoff k ≤ (k^2)^(6*k) := by dsimp only [cutoff]; rw [← pow_mul, show 2*(6*k) = 12*k by omega]
  have hh := TorusFourier.displacement_bound poolPrime j (fun i => (pool_properties i).1) Subtype.val_injective
    hPM (period_upper j) ht hD hQ hMR hMQ (one_le_pow₀ (by omega : 1 ≤ k) : 1 ≤ k^2)
    (fun i => (pool_properties i).2.1.le) hpow (by omega : 6*k+k ≤ 16*k) (by omega : 1 ≤ k) hM C
    (fineModulus j/2 : ℕ) F a ha hlip
  exact hh.trans (mul_le_mul_of_nonneg_left (spectrum_error hk) (mul_nonneg ha (Nat.cast_nonneg _)))

end TreeEdit.TorusTree

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CircleParameters ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter

lemma wordLength_ge {k : ℕ} (hk : 2 ≤ k) : k ≤ wordLength k := by
  have hT : 1 ≤ repetitions k := one_le_pow₀ (by omega)
  have hm : k ≤ branching k := by
    dsimp [branching]
    have hk2 : 1 ≤ k^2 := one_le_pow₀ (by omega)
    nlinarith
  have hbase : 1 ≤ branching k * repetitions k := (show 1 ≤ branching k by omega).trans (Nat.le_mul_of_pos_right _ hT)
  exact (hm.trans (Nat.le_mul_of_pos_right _ hT)).trans (le_self_pow₀ hbase (by omega))

end TreeEdit.TorusTree

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.Delimiter ----
namespace OAI

namespace TreeEdit.Delimiter
open scoped BigOperators
open Classical

end TreeEdit.Delimiter

namespace TreeEdit.Delimiter
open scoped BigOperators
open Classical

lemma deficit_bound {α : Type*} {M B : ℕ} (hB : 0 < B) (c : α → Word Bool B)
    (hc : Synchronizing c) (x y : Word α M) :
    deficit x.val y.val ≤ 2*deficit (encode c x.val) (encode c y.val) := by
  obtain ⟨A⟩ := exists_lcs_alignment (encode c x.val) (encode c y.val)
  have hx : (encode c x.val).length = M*B := by rw [length_encode, x.property]
  have hy : (encode c y.val).length = M*B := by rw [length_encode, y.property]
  let f := A.left.comp (Fin.castOrderIso hx).toOrderEmbedding
  let g := A.right.comp (Fin.castOrderIso hy).toOrderEmbedding
  have hfg : ∀ i, (encode c x.val).get (Fin.cast hx.symm (f i)) =
      (encode c y.val).get (Fin.cast hy.symm (g i)) := A.agree
  have hh := alignment_bound hB c hc x y f g hfg
  dsimp only [deficit]
  rw [hx, x.property]
  omega

lemma bit_true {t : ℕ} (label : Fin t → Bool) (i : Fin (2*t+3)) (h : bit label i = true) :
    i.val = 0 ∨ i.val % 2 = 1 := by
  unfold bit at h
  split_ifs at h with hi hi
  · omega
  · exact Or.inr hi

lemma bit_label {t : ℕ} (label : Fin t → Bool) (i : Fin t) :
    bit label ⟨3+2*i.val, by have := i.isLt; omega⟩ = label i := by
  have he : (3+2*i.val) % 2 = 1 := by omega
  simp only [bit, show ¬ 3+2*i.val < 2 by omega, dite_false, he, dite_true]
  congr 1
  apply Fin.ext
  change (3+2*i.val-3)/2 = i.val
  omega

lemma code_injective {α : Type*} {t : ℕ} (label : α → (Fin t → Bool)) (hl : Function.Injective label) :
    Function.Injective (code label) := by
  intro a b hab
  apply hl
  funext i
  have h := congrArg (fun w : Word Bool (2*t+3) =>
    w.val.get (Fin.cast w.property.symm ⟨3+2*i.val, by have := i.isLt; omega⟩)) hab
  simp only [code, vectorWord, List.get_eq_getElem, List.getElem_ofFn] at h
  change bit (label a) ⟨3+2*i.val, _⟩ = bit (label b) ⟨3+2*i.val, _⟩ at h
  simpa only [bit_label] using h

lemma get_position {α : Type*} {B : ℕ} (hB : 0 < B) (c : α → Word Bool B) (x : List α)
    (p : ℕ) (hp : p < (encode c x).length) :
    (encode c x)[p] = (c (x[p/B]'((Nat.div_lt_iff_lt_mul hB).mpr (by rwa [length_encode] at hp)))).val[p%B]'(by
      rw [(c _).property]; exact Nat.mod_lt _ hB) := by
  have hh := get_encode_block c x (p/B) (p%B) ((Nat.div_lt_iff_lt_mul hB).mpr (by rwa [length_encode] at hp)) (Nat.mod_lt p hB)
  simpa only [Nat.mul_comm (p/B) B, Nat.div_add_mod] using hh

lemma bit_position {α : Type*} {t : ℕ} (label : α → (Fin t → Bool)) (x : List α)
    (p : ℕ) (hp : p < (encode (code label) x).length) :
    (encode (code label) x)[p] = bit (label (x[p/(2*t+3)]'((Nat.div_lt_iff_lt_mul (by omega : 0 < 2*t+3)).mpr (by rwa [length_encode] at hp))))
      ⟨p%(2*t+3), Nat.mod_lt _ (by omega)⟩ := by
  rw [get_position (by omega)]
  simp only [code, vectorWord, List.getElem_ofFn]

lemma marker {α : Type*} {t : ℕ} (label : α → (Fin t → Bool)) (x : List α)
    (p : ℕ) (hp : p+1 < (encode (code label) x).length)
    (h0 : (encode (code label) x)[p]'(by omega) = true)
    (h1 : (encode (code label) x)[p+1] = true) : p%(2*t+3) = 0 := by
  rw [bit_position] at h0 h1
  have h0' := bit_true _ _ h0
  have h1' := bit_true _ _ h1
  change p%(2*t+3) = 0 ∨ p%(2*t+3)%2 = 1 at h0'
  change (p+1)%(2*t+3) = 0 ∨ (p+1)%(2*t+3)%2 = 1 at h1'
  have hr := Nat.mod_lt p (by omega : 0 < 2*t+3)
  have hr' := Nat.mod_lt (p+1) (by omega : 0 < 2*t+3)
  by_contra hn
  have ho : p%(2*t+3)%2 = 1 := h0'.resolve_left hn
  have hend : p%(2*t+3)+1 < 2*t+3 := by omega
  have he : (p+1)%(2*t+3) = p%(2*t+3)+1 := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < 2*t+3), Nat.mod_eq_of_lt hend]
  rw [he] at h1'
  omega

lemma code_synchronizing {α : Type*} {t : ℕ} (label : α → (Fin t → Bool)) (hl : Function.Injective label) :
    Synchronizing (code label) := by
  intro x a n hn he
  have h0 : (encode (code label) x)[n]'(by omega) = true := by
    have hh := congrArg (fun l : List Bool => l[0]?) he
    have hbit : (code label a).val[0]'(by rw [(code label a).property]; omega) = true := by simp only [code, vectorWord, List.getElem_ofFn, bit]; norm_num
    rw [List.getElem?_eq_getElem (by rw [length_segment _ hn]; omega),
      List.getElem?_eq_getElem (by rw [(code label a).property]; omega)] at hh
    simpa only [Option.some.injEq, segment_get, Nat.add_zero, hbit] using hh
  have h1 : (encode (code label) x)[n+1]'(by omega) = true := by
    have hh := congrArg (fun l : List Bool => l[1]?) he
    have hbit : (code label a).val[1]'(by rw [(code label a).property]; omega) = true := by simp only [code, vectorWord, List.getElem_ofFn, bit]; norm_num
    rw [List.getElem?_eq_getElem (by rw [length_segment _ hn]; omega),
      List.getElem?_eq_getElem (by rw [(code label a).property]; omega)] at hh
    simpa only [Option.some.injEq, segment_get, hbit] using hh
  have hm := marker label x n (by omega) h0 h1
  have hbi : n/(2*t+3) < x.length := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [← length_encode (code label) x]; omega)
  let b : Fin x.length := ⟨n/(2*t+3), hbi⟩
  have hstart : n = b.val*(2*t+3) := by
    have hd := Nat.div_add_mod n (2*t+3)
    rw [hm, Nat.add_zero, Nat.mul_comm] at hd
    exact hd.symm
  refine ⟨b, hstart, ?_⟩
  apply code_injective label hl
  apply Subtype.ext
  have hh := segment_encode_block (code label) x b.val 0 (2*t+3) b.isLt (by omega)
  have hs : segment (encode (code label) x) n (2*t+3) = (code label (x.get b)).val := by
    rw [hstart]
    simpa only [Nat.add_zero, segment, List.drop_zero, ← (code label x[b.val]).property, List.take_length, List.get_eq_getElem] using hh
  exact hs.symm.trans he

lemma exists_code (α : Type*) [Fintype α] :
    ∃ c : α → Word Bool (width (Fintype.card α)), Synchronizing c := by
  have hcard : Fintype.card α ≤ Fintype.card (Fin (Nat.clog 2 (Fintype.card α)) → Bool) := by
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using Nat.le_pow_clog (by norm_num : 1 < 2) (Fintype.card α)
  let label := (Fintype.equivFin α).toEmbedding.trans ((Fin.castLEEmb hcard).trans (Fintype.equivFin (Fin (Nat.clog 2 (Fintype.card α)) → Bool)).symm.toEmbedding)
  exact ⟨code label, code_synchronizing label label.injective⟩

theorem transfer (α : Type*) [Fintype α] :
    ∃ c : α → Word Bool (width (Fintype.card α)), ∀ (n : ℕ) (x y : Word α n),
      deficit x.val y.val ≤ 2*deficit (encode c x.val) (encode c y.val) ∧
      (deficit x.val y.val : ℝ)/2 ≤ ed (encode c x.val) (encode c y.val) ∧
      ed (encode c x.val) (encode c y.val) ≤ width (Fintype.card α)*ed x.val y.val := by
  obtain ⟨c, hc⟩ := exists_code α
  refine ⟨c, fun n x y => ?_⟩
  have hh := deficit_bound (by dsimp [width]; omega) c hc x y
  refine ⟨hh, ?_, ed_encode_le c x.val y.val⟩
  have he := deficit_le_ed (encode c x.val) (encode c y.val)
  have hhr : (deficit x.val y.val : ℝ) ≤ 2*deficit (encode c x.val) (encode c y.val) := by exact_mod_cast hh
  have her : (deficit (encode c x.val) (encode c y.val) : ℝ) ≤ ed (encode c x.val) (encode c y.val) := by exact_mod_cast he
  linarith

end TreeEdit.Delimiter

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.TorusLowerBound ----
namespace OAI

namespace TreeEdit

lemma encode_singletonCode (x : List Bool) : encode singletonCode x = x := by
  induction x with
  | nil => rfl
  | cons a x ih => simpa only [encode, List.flatMap_cons, singletonCode, List.singleton_append] using congrArg (List.cons a) ih

namespace TorusTree
open scoped BigOperators
open Classical Filter

theorem binary_witness {k : ℕ} (hk : 2 ≤ k) (j : Fin (16*k) ↪ Pool k)
    (C : Config (Pool k) (residueModulus k) (branching k) k)
    (hgood : Good (resolution k : ℝ)⁻¹ poolPrime j k C (point 2)) :
    ∃ W : Finset (List Bool), 2 ≤ W.card ∧ (∀ v ∈ W, v.length = binaryLength k) ∧
      ((k : ℝ)/128)^k / (1286400*(k : ℝ)^2) ≤ c1 W := by
  let : NeZero (fineModulus j) := ⟨(fine_parameters hk j).1.ne'⟩
  let : NeZero (resolution k) := ⟨(pow_pos (by omega : 0 < k) (8*k)).ne'⟩
  let A := State (ZMod (fineModulus j)) (branching k) k
  let Γ := Symbol (branching k) (resolution k) k
  let N := FiniteTree.length (branching k) (repetitions k) k
  let B := Delimiter.width (Fintype.card Γ)
  have hN : N = wordLength k := FiniteTree.length_eq _ _ _
  have hB : B = binaryWidth k := by
    dsimp only [B, Γ, Delimiter.width, binaryWidth, alphabetSize]
    rw [symbol_card]
  have hNp : 0 < N := lt_of_lt_of_le (by omega : 0 < k) (hN ▸ wordLength_ge hk)
  have hBp : 0 < B := by dsimp [B, Delimiter.width]; omega
  let w : A → Word Γ N := sampledWord poolPrime j (repetitions k) (resolution k) k C
  let z : A := diagonal (A := ZMod (fineModulus j)) (m := branching k) k (fineModulus j/2 : ℕ)
  obtain ⟨c, hc⟩ := Delimiter.transfer Γ
  let instG : AddCommGroup A := stateAddCommGroup (A := ZMod (fineModulus j)) (branching k) k
  let instF : Fintype A := stateFintype (A := ZMod (fineModulus j)) (branching k) k
  let wb (x : A) : Word Bool (N*B) :=
    ⟨encode c (w x).val, by rw [length_encode, (w x).property]⟩
  let hadd : HAdd A A A := ⟨@Add.add A instG.toAdd⟩
  have hsep (x : A) : (N*B : ℝ) ≤ (2*B*(128 : ℝ)^k) * ed (wb x).val (wb (@HAdd.hAdd A A A hadd x z)).val := by
    have hh : (N : ℝ) ≤ (128 : ℝ)^k * deficit (w x).val (w (@HAdd.hAdd A A A hadd x z)).val := by
      exact_mod_cast sampled_separation hk j C hgood x
    have he := (hc N (w x) (w (@HAdd.hAdd A A A hadd x z))).2.1
    calc
      _ ≤ B * ((128 : ℝ)^k * deficit (w x).val (w (@HAdd.hAdd A A A hadd x z)).val) := by nlinarith only [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg B)]
      _ ≤ B * ((128 : ℝ)^k * (2 * ed (wb x).val (wb (@HAdd.hAdd A A A hadd x z)).val)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B)
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
        dsimp only [wb]
        linarith
      _ = _ := by ring
  have hobs (F : A → RealL1) (a : ℝ) (ha : 0 ≤ a)
      (hlip : ∀ x y, dist (F x) (F y) ≤ a * ed (wb x).val (wb y).val) :
      @FiniteFourier.average A instF (fun x => dist (F x) (F (@HAdd.hAdd A A A hadd x z))) ≤
        a * (N*B : ℕ) * (20*(k : ℝ)⁻¹^k) := by
    have hlip' (x y : A) : dist (F x) (F y) ≤ (a*B) * ed (w x).val (w y).val := by
      calc
        _ ≤ a * ed (wb x).val (wb y).val := hlip x y
        _ ≤ a * (B * (ed (w x).val (w y).val : ℝ)) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast (hc N (w x) (w y)).2.2) ha
        _ = _ := by ring
    have hh := concrete_displacement hk j C F (a*B) (mul_nonneg ha (Nat.cast_nonneg B)) hlip'
    convert hh using 1
    push_cast
    ring
  obtain ⟨W, hW, hlen, hdist⟩ := @binary_transfer A Bool instF instG inferInstance (N*B) 1 (Nat.mul_pos hNp hBp) (by norm_num : 0 < 1)
    wb z singletonCode (2*B*(128 : ℝ)^k) (20*(k : ℝ)⁻¹^k)
    (by positivity) (by
      have hkreal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      exact mul_pos (by norm_num) (pow_pos (inv_pos.mpr hkreal) _))
    (fun x y => by
      rw [encode_singletonCode, encode_singletonCode]
      exact mul_le_of_le_one_left (Nat.cast_nonneg _) (by norm_num))
    (fun x => by simpa only [Nat.cast_mul] using hsep x) hobs
  refine ⟨W, hW, ?_, ?_⟩
  · intro v hv
    simpa only [mul_one, hN, hB, binaryLength] using hlen v hv
  · have hkreal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hBreal : (0 : ℝ) < B := by exact_mod_cast hBp
    have hwidth : (B : ℝ) ≤ 40*(k : ℝ)^2 := by rw [hB]; exact_mod_cast binaryWidth_le hk
    have heq : (804*(2*B*(128 : ℝ)^k)*(20*(k : ℝ)⁻¹^k))⁻¹ =
        ((k : ℝ)/128)^k / (32160*B) := by
      rw [div_pow, inv_pow]
      field_simp
      ring
    rw [heq] at hdist
    apply le_trans _ hdist
    apply div_le_div_of_nonneg_left (pow_nonneg (by positivity) _) (by positivity)
    nlinarith

end TorusTree

end TreeEdit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter


theorem solution : type_of% @_root_.OAI.TreeEdit.TorusTree.binary_witness := @_root_.OAI.TreeEdit.TorusTree.binary_witness
