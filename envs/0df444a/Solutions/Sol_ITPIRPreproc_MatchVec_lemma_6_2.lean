-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.lemma_6_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T16:18:01.935745+00:00
-- url     : https://prove2.me/submissions/cdc2853c-edde-4038-8fd2-0286215594a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ITPIRPreproc_MatchVec_claim_6_2_1
import Theorems.Thm_ITPIRPreproc_MatchVec_claim_6_2_2
import Theorems.Thm_ITPIRPreproc_MatchVec_claim_6_2_3
import Theorems.Thm_ITPIRPreproc_MatchVec_claim_6_2_4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal
open Matrix Finset ITPIRPreproc.MatchVec MeasureTheory

namespace PIRAssembly
lemma bit_sum (n h : ℕ) :
    (∑ k : Fin h, (n.testBit k).toNat * 2 ^ (k:ℕ)) = n % 2^h := by
  induction h with
  | zero => simp only [Fin.sum_univ_zero, Nat.pow_zero, Nat.mod_one]
  | succ h ih =>
    simp only [Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last]
    rw [ih,Nat.toNat_testBit,pow_succ,Nat.mod_mul]
    ac_rfl

lemma col_roundtrip {h : ℕ} (c : Fin (2^h)) : colIdx (colVec c) = c := by
  apply Fin.ext
  change (∑ k : Fin h, ((if c.val.testBit k then (1:ZMod 2) else 0).val) * 2^(k:ℕ)) % 2^h = c.val
  have he : ∀ k : Fin h, (if c.val.testBit k then (1:ZMod 2) else 0).val = (c.val.testBit k).toNat := by
    intro k
    cases c.val.testBit k <;> decide
  simp_rw [he]
  rw [bit_sum, Nat.mod_mod, Nat.mod_eq_of_lt c.isLt]

lemma pos_injective (h : ℕ) : Function.Injective (posOf (h := h)) := by
  intro i j hij
  have he := congrArg (fun p : Pos h => (p.1,colIdx p.2)) hij
  simp only [posOf, col_roundtrip] at he
  exact finProdFinEquiv.symm.injective he

lemma target_bit {h : ℕ} (D : Fin (2^h*2^h) → Bool) (i : Fin (2^h*2^h)) :
    toDB D (posOf i).1 (colIdx (posOf i).2) = D i := by
  simp only [toDB,posOf,col_roundtrip,Prod.eta,Equiv.apply_symm_apply]

lemma bit_map (b : Bool) : toBitOpt (some (bitF3 b)) = some b := by
  cases b <;> norm_num [toBitOpt,bitF3]
lemma bit_map_iff (b : Bool) (x : Option (ZMod 3)) :
    toBitOpt x = some b ↔ x = some (bitF3 b) := by
  cases x with
  | none => simp [toBitOpt]
  | some x =>
    cases b <;> simp [toBitOpt,bitF3]
    split_ifs <;> simp_all

lemma compat {h d : ℕ} (u v : Fin (2^h) → Fin d → ZMod 6) (i : Fin (2^h*2^h)) :
    (actPrimitive d u v).compat i = actCompat v (posOf i) := by
  ext K
  simp [OCHP.compat,actPrimitive,actCompat]

lemma avg_mono {A : Type*} (s : Finset A) (f g : A → ℝ≥0∞)
    (hfg : ∀ a ∈ s, f a ≤ g a) : avgOver s f ≤ avgOver s g := by
  unfold avgOver
  exact mul_le_mul_of_nonneg_left (sum_le_sum hfg) zero_le

lemma probabilities {h d : ℕ} (u v : Fin (2^h) → Fin d → ZMod 6)
    (hh : 3 ≤ h) (hmv : IsMVFamily (2^h) d u v)
    (D : Fin (2^h*2^h) → Bool) (i : Fin (2^h*2^h)) :
    (actPrimitive d u v).probSound D i = 1 ∧
      (actPrimitive d u v).probRecover D i = 2⁻¹ := by
  have hc := claim_6_2_3 h d u v hh hmv (toDB D) (posOf i)
  rw [target_bit] at hc
  have hr : (actPrimitive d u v).probRecover D i = 2⁻¹ := by
    unfold OCHP.probRecover
    rw [compat]
    simpa only [OCHP.outcome,actPrimitive,bit_map_iff] using hc.2
  refine ⟨?_,hr⟩
  apply le_antisymm
  · unfold OCHP.probSound
    have hm : ∀ K ∈ (actPrimitive d u v).compat i,
        ((actPrimitive d u v).query i K).toOuterMeasure
        {p | (actPrimitive d u v).outcome D i K p = some (D i) ∨
          (actPrimitive d u v).outcome D i K p = none} ≤ 1 := by
      intro K hK
      exact le_trans (measure_mono (Set.subset_univ _))
        ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)).le
    have ha := avg_mono _ _ (fun _ => 1) hm
    refine ha.trans ?_
    unfold avgOver
    simp only [sum_const, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_le_one _
  · rw [← hc.1]
    unfold OCHP.probSound
    rw [compat]
    apply avg_mono
    intro K hK
    apply measure_mono
    intro p hp
    rcases hp with hp | hp
    · left
      change toBitOpt (actDecode u (posOf i) K (actHint v (toDB D) K) p.1 p.2
        (actAnswer v (toDB D) p.1)) = some (D i)
      rw [hp,bit_map]
    · right
      change toBitOpt (actDecode u (posOf i) K (actHint v (toDB D) K) p.1 p.2
        (actAnswer v (toDB D) p.1)) = none
      rw [hp]; rfl

lemma isOCHP {h d : ℕ} (u v : Fin (2^h) → Fin d → ZMod 6)
    (hh : 3 ≤ h) (hmv : IsMVFamily (2^h) d u v) :
    (actPrimitive d u v).IsOneCompatibleHint (2^h) := by
  have hpow : 1 < 2^h := one_lt_pow₀ (by norm_num) (by omega)
  letI : Nontrivial (Fin (2^h)) := Fin.nontrivial_iff_two_le.mpr hpow
  constructor
  · intro i
    obtain ⟨j,hj⟩ := exists_ne (posOf i)
    have hc := ((claim_6_2_1 h d u v hh hmv).1 (posOf i) j (Ne.symm hj)).1
    unfold OCHP.probSel
    rw [compat]
    simpa only [actPrimitive,Nat.cast_pow,Nat.cast_ofNat] using hc.ge
  · intro i j hji
    have hp : posOf i ≠ posOf j := fun he => hji ((pos_injective h) he).symm
    have hc := ((claim_6_2_1 h d u v hh hmv).1 (posOf i) (posOf j) hp).2
    unfold OCHP.probOverlap
    rw [compat]
    have hb : (2 * 2^h : ℝ≥0∞)⁻¹ ≤ 2 / ((2^h : ℕ) : ℝ≥0∞) := by
      rw [div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat,
        ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      gcongr
      exact (ENNReal.inv_le_one.mpr (by norm_num)).trans (by norm_num)
    refine le_trans ?_ hb
    simpa only [actPrimitive,mem_filter,mem_univ,true_and] using hc
  · intro i Q
    unfold OCHP.queryLaw
    rw [compat]
    exact claim_6_2_2 h d u v hh hmv (posOf i) Q
  · intro D i
    exact (probabilities u v hh hmv D i).1
  · intro D i
    exact (probabilities u v hh hmv D i).2.ge

lemma family_pow (dim : ℕ → ℕ) (u v : ∀ h : ℕ, Fin (2^h) → Fin (dim h) → ZMod 6) (h : ℕ) :
    actFamily dim u v (2^h) = actPrimitive (dim h) (u h) (v h) := by
  have he : Nat.log 2 (2^h) = h := Nat.log_pow (by norm_num) h
  have ht : ∀ a b : ℕ, a = b → HEq (actPrimitive (dim a) (u a) (v a))
      (actPrimitive (dim b) (u b) (v b)) := by
    intro a b hab
    subst b
    rfl
  unfold actFamily
  split_ifs with hp
  · apply eq_of_heq
    exact (cast_heq _ _).trans (ht _ _ he)
  · simp [he] at hp
end PIRAssembly

open WordRAM

theorem solution :
    ∀ (C₀ : ℝ) (c₀ : ℕ), ∃ (C : ℝ) (c : ℕ),
      ∀ (dim : ℕ → ℕ) (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6)
        (vecProg tableProg : Program),
        (∀ h : ℕ, 3 ≤ h → IsMVFamily (2 ^ h) (dim h) (u h) (v h)) →
        MVComputable dim u v C₀ c₀ vecProg tableProg →
        (∀ h : ℕ, 3 ≤ h →
          (actFamily dim u v (2 ^ h)).IsOneCompatibleHint (2 ^ h) ∧
          ∀ (D : Fin (2 ^ h * 2 ^ h) → Bool) (i : Fin (2 ^ h * 2 ^ h)),
            (actFamily dim u v (2 ^ h)).probRecover D i = 2⁻¹) ∧
        ∃ (I : OCHPImpl (actFamily dim u v)) (hintProg : Program),
          Deterministic hintProg ∧
          ∀ h : ℕ, 3 ≤ h →
            (Function.Injective (I.encKey (2 ^ h)) ∧
              ∀ K, (I.encKey (2 ^ h) K).length = (h + 1) * dim h) ∧
            (Function.Injective (I.encHint (2 ^ h)) ∧
              ∀ z, (I.encHint (2 ^ h) z).length = 2 * dim h) ∧
            (Function.Injective (I.encAns (2 ^ h)) ∧
              ∀ a, (I.encAns (2 ^ h) a).length = 2 * dim h) ∧
            I.Efficient (2 ^ h) (C * h * dim h) (C * dim h * (h : ℝ) ^ c) (C * h * dim h)
              (C * h * dim h) (C * 2 ^ h * dim h * (h : ℝ) ^ c) ((h + 1) * dim h) (2 * dim h) ∧
            ∀ (D : Fin (2 ^ h * 2 ^ h) → Bool) (K : (actFamily dim u v (2 ^ h)).Key),
              let inp := encNat (2 ^ h) ++ encBits (I.encKey (2 ^ h) K) ++ List.ofFn D
              Halts hintProg inp zeroTape ∧
              output hintProg inp zeroTape =
                I.encHint (2 ^ h) ((actFamily dim u v (2 ^ h)).hint D K) ∧
              (cost hintProg inp zeroTape : ℝ) ≤ C * 2 ^ h * dim h * (h : ℝ) ^ c  := by
  intro C₀ c₀
  obtain ⟨C,c,hC⟩ := claim_6_2_4 C₀ c₀
  refine ⟨C,c,?_⟩
  intro dim u v vecProg tableProg hmv hcomp
  refine ⟨?_,hC dim u v vecProg tableProg hmv hcomp⟩
  intro h hh
  rw [PIRAssembly.family_pow]
  exact ⟨PIRAssembly.isOCHP (u h) (v h) hh (hmv h hh),
    fun D i => (PIRAssembly.probabilities (u h) (v h) hh (hmv h hh) D i).2⟩

