-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.RandomMatching.segmentMatchingEvent_fraction_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:30:25.048993+00:00
-- url     : https://prove2.me/submissions/b6ab5d25-c7ce-443c-b739-dfb17251be83

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.RandomMatching
theorem h49_card_sme {K P a s : ℕ}
    (i j : Fin K) (hne : i ≠ j) (u v : Fin a → Fin P)
    (hv : Function.Injective v) :
    (segmentMatchingEvent s i j u v).card ≤
      (a.choose s) ^ 2 * 2 ^ (K * P - s) := by
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

theorem solution {K P a s : ℕ}
    (i j : Fin K) (hne : i ≠ j) (u v : Fin a → Fin P)
    (hv : Function.Injective v) (hs : s ≤ a) :
    ((segmentMatchingEvent s i j u v).card : ℝ) / (2 : ℝ) ^ (K * P) ≤
      ((a.choose s : ℝ) ^ 2) / (2 : ℝ) ^ s := by
  have hc := h49_card_sme (s := s) i j hne u v hv
  have haP : a ≤ P := by simpa using Fintype.card_le_of_injective v hv
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.2 (fun h => by subst h; exact i.elim0)
  have hsKP : s ≤ K * P := by nlinarith
  have hc' : ((segmentMatchingEvent s i j u v).card : ℝ) ≤ ((a.choose s : ℝ))^2 * 2^(K*P - s) := by
    exact_mod_cast hc
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc ((segmentMatchingEvent s i j u v).card : ℝ) * 2^s ≤ ((a.choose s : ℝ))^2 * 2^(K*P - s) * 2^s := by
        gcongr
    _ = ((a.choose s : ℝ))^2 * 2^(K*P) := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hsKP]

