-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.SegmentCode.comparisonBad_fraction_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:26:54.217773+00:00
-- url     : https://prove2.me/submissions/c24355fe-6eda-4e60-b5b7-7ed2f9eeabd3

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFamilyTransfer
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeNumerics
import Definitions.Def_OAI_Combinatorics_BinaryEdit_RandomMatching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentMatchingCount
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeUnionBound
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentCode

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.SegmentCode
open RandomMatching CodeUnionBound
theorem h49_choose_mul_pow_le (n k : ℕ) (hk : k ≤ n) (x : ℝ) (hx : 0 ≤ x) :
    (n.choose k : ℝ) * x^k ≤ (x+1)^n := by
  rw [add_pow]
  have ht : k ∈ Finset.range (n+1) := Finset.mem_range.2 (by omega)
  calc (n.choose k : ℝ) * x^k = x^k * 1^(n-k) * (n.choose k) := by ring
    _ ≤ ∑ m ∈ Finset.range (n+1), x^m * 1^(n-m) * (n.choose m) :=
      Finset.single_le_sum (f := fun m => x^m * 1^(n-m) * (n.choose m : ℝ))
        (fun m _ => by positivity) ht

theorem h49_nearly (a s : ℕ) (hs : s ≤ a) (hlarge : 99*a ≤ 100*s) :
    (a.choose s : ℝ)^2 * (1/2 : ℝ)^s ≤ (9/10 : ℝ)^a := by
  obtain ⟨t, rfl⟩ : ∃ t, a = s + t := ⟨a - s, by omega⟩
  have ht : 99 * t ≤ s := by omega
  rw [Nat.choose_symm_add]
  have hC := h49_choose_mul_pow_le (s+t) t (by omega) (1/100) (by norm_num)
  have hC' : ((s+t).choose t : ℝ) ≤ (101/100)^(s+t) * 100^t := by
    have h100 : (1/100:ℝ)^t * 100^t = 1 := by rw [← mul_pow]; norm_num
    calc ((s+t).choose t : ℝ) = ((s+t).choose t : ℝ) * (1/100)^t * 100^t := by
          rw [mul_assoc, h100, mul_one]
      _ ≤ (1/100 + 1)^(s+t) * 100^t := by gcongr
      _ = (101/100)^(s+t) * 100^t := by norm_num
  have hA : ((101/100:ℝ)^2 * (5/9))^s ≤ ((101/100:ℝ)^2 * (5/9))^(99*t) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) ht
  have hAB : ((101/100:ℝ)^2 * (5/9))^99 * ((101/100)^2 * (100000/9)) ≤ 1 := by norm_num
  have hkey : ((101/100:ℝ)^2 * (5/9))^s * ((101/100)^2 * (100000/9))^t ≤ 1 := by
    calc ((101/100:ℝ)^2 * (5/9))^s * ((101/100)^2 * (100000/9))^t
        ≤ ((101/100:ℝ)^2 * (5/9))^(99*t) * ((101/100)^2 * (100000/9))^t := by gcongr
      _ = (((101/100:ℝ)^2 * (5/9))^99 * ((101/100)^2 * (100000/9)))^t := by
          rw [pow_mul, ← mul_pow]
      _ ≤ 1 := pow_le_one₀ (by positivity) hAB
  have g1 : ∀ (p q r : ℝ), (p^(s+t) * q^t)^2 * r^s = (p^2*r)^s * (p^2*q^2)^t := by intros; ring
  have g2 : ∀ (c A B : ℝ), (c*A)^s * (c*B)^t = c^(s+t) * (A^s * B^t) := by intros; ring
  have hexp : ((101/100:ℝ)^(s+t) * 100^t)^2 * (1/2)^s
      = (9/10:ℝ)^(s+t) * (((101/100:ℝ)^2 * (5/9))^s * ((101/100)^2 * (100000/9))^t) := by
    rw [g1, ← g2]; norm_num
  calc ((s+t).choose t : ℝ)^2 * (1/2)^s ≤ ((101/100:ℝ)^(s+t) * 100^t)^2 * (1/2)^s := by gcongr
    _ = _ := hexp
    _ ≤ (9/10:ℝ)^(s+t) * 1 := by gcongr
    _ = _ := mul_one _

theorem h49_card_event {K P a s : ℕ} (i j : Fin K) (hne : i ≠ j) (u v : Fin a → Fin P)
    (hv : Function.Injective v) :
    (segmentMatchingEvent s i j u v).card ≤ (a.choose s) ^ 2 * 2 ^ (K * P - s) := by
  classical
  let E : IncreasingPositions a s × IncreasingPositions a s → Finset (Fin K → Fin P → Bool) :=
    fun fg => Finset.univ.filter fun c => ∀ t, c i (u (fg.1.1 t)) = c j (v (fg.2.1 t))
  have hsub : segmentMatchingEvent s i j u v ⊆ Finset.univ.biUnion E := by
    intro c hc
    simp only [segmentMatchingEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨f, g, h⟩ := hc
    exact Finset.mem_biUnion.mpr ⟨(f, g), Finset.mem_univ _, by simp [E, h]⟩
  have hE : ∀ fg, (E fg).card ≤ 2 ^ (K * P - s) := by
    rintro ⟨f, g⟩
    let T : Finset (Fin K × Fin P) := Finset.univ.image fun t => (j, v (g.1 t))
    have hT : T.card = s := by
      rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
      intro t1 t2 h
      simp only [Prod.mk.injEq] at h
      exact g.2.injective (hv h.2)
    have hcardT : Fintype.card {x : Fin K × Fin P // x ∉ T} = K * P - s := by
      rw [Fintype.card_subtype_compl, Fintype.card_coe, hT, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fin]
    let φ : (Fin K → Fin P → Bool) → ({x : Fin K × Fin P // x ∉ T} → Bool) :=
      fun c x => c x.1.1 x.1.2
    have hinj : Set.InjOn φ (E (f, g)) := by
      intro c hc c' hc' heq
      simp only [E, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hc hc'
      have hoff : ∀ x : Fin K × Fin P, x ∉ T → c x.1 x.2 = c' x.1 x.2 := fun x hx =>
        congrFun heq ⟨x, hx⟩
      funext k p
      by_cases hkp : (k, p) ∈ T
      · obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hkp
        simp only [Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        have hn : (i, u (f.1 t)) ∉ T := by
          intro hm
          obtain ⟨t', _, ht'⟩ := Finset.mem_image.mp hm
          simp only [Prod.mk.injEq] at ht'
          exact hne ht'.1.symm
        rw [← hc t, ← hc' t]
        exact hoff _ hn
      · exact hoff (k, p) hkp
    calc (E (f, g)).card ≤ (Finset.univ : Finset ({x : Fin K × Fin P // x ∉ T} → Bool)).card :=
          Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
      _ = 2 ^ (K * P - s) := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, hcardT]
  have hIP : Fintype.card (IncreasingPositions a s) = a.choose s := by
    rw [Fintype.card_congr (increasingPositionsEquiv a s), Fintype.card_finset_len, Fintype.card_fin]
  calc (segmentMatchingEvent s i j u v).card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card hsub
    _ ≤ ∑ fg, (E fg).card := Finset.card_biUnion_le
    _ ≤ ∑ _fg : IncreasingPositions a s × IncreasingPositions a s, 2 ^ (K * P - s) :=
        Finset.sum_le_sum fun fg _ => hE fg
    _ = (a.choose s) ^ 2 * 2 ^ (K * P - s) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, hIP, smul_eq_mul, sq]

theorem solution {K P : ℕ} (a₀ : ℕ)
    (t : SegmentComparison K (P+1)) :
    ((comparisonBad a₀ t).card : ℝ) / Fintype.card (Fin K → Fin P → Bool) ≤
      (9/10 : ℝ)^a₀ := by
  classical
  obtain ⟨k, l, a, i, j⟩ := t
  have hcardU : (Fintype.card (Fin K → Fin P → Bool) : ℝ) = 2 ^ (K * P) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin,
      ← pow_mul, mul_comm P K]; push_cast; ring
  rw [hcardU]
  unfold comparisonBad
  simp only
  split_ifs with h
  · obtain ⟨hkl, ha, hi, hj⟩ := h
    set s := a.val - a.val / 100 with hs
    have hinj : Function.Injective (window (P := P) a.val j.val hj) := by
      intro t1 t2 h; simp only [window, Fin.mk.injEq] at h; exact Fin.ext (by omega)
    have hc := h49_card_event k l hkl (window a.val i.val hi) (window a.val j.val hj) hinj (s := s)
    have hK : 1 ≤ K := by have := k.isLt; omega
    have hsP : s ≤ K * P := by
      calc s ≤ a.val := by omega
        _ ≤ P := by omega
        _ ≤ K * P := Nat.le_mul_of_pos_left _ (by omega)
    have hnb := h49_nearly a.val s (by omega) (by omega)
    have hpos : (0:ℝ) < 2 ^ (K * P) := by positivity
    rw [div_le_iff₀ hpos]
    have hc' : ((segmentMatchingEvent s k l (window a.val i.val hi) (window a.val j.val hj)).card : ℝ)
        ≤ (a.val.choose s : ℝ) ^ 2 * 2 ^ (K * P - s) := by exact_mod_cast hc
    have h2 : (2:ℝ) ^ (K * P - s) = (1/2 : ℝ)^s * 2 ^ (K * P) := by
      rw [show K * P = (K * P - s) + s from (Nat.sub_add_cancel hsP).symm, pow_add]
      rw [Nat.add_sub_cancel, mul_comm ((1/2:ℝ)^s), mul_assoc, ← mul_pow]; norm_num
    have h3 : (9/10 : ℝ)^(a.val) ≤ (9/10 : ℝ)^a₀ := pow_le_pow_of_le_one (by norm_num) (by norm_num) ha
    calc _ ≤ (a.val.choose s : ℝ) ^ 2 * 2 ^ (K * P - s) := hc'
      _ = ((a.val.choose s : ℝ) ^ 2 * (1/2 : ℝ)^s) * 2 ^ (K * P) := by rw [h2]; ring
      _ ≤ (9/10 : ℝ)^a₀ * 2 ^ (K * P) := by gcongr; exact hnb.trans h3
  · simp; positivity

