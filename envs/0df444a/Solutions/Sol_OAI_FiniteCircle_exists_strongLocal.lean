-- Prove2me | solution 1 for OAI.FiniteCircle.exists_strongLocal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:39:21.520401+00:00
-- url     : https://prove2.me/submissions/670bafe9-ea73-4062-b7d6-30aa4efeb7b8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/RandomCodes.lean:L192-L241
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.exists_strongLocal. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Theorems.Thm_OAI_FiniteCircle_card_small_subsets_le
import Theorems.Thm_OAI_FiniteCircle_exists_disjoint_pair_subfamily

-- ---- from OAI.Combinatorics.FiniteCircle.BlockMatching ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem indexSpan_ofFn {w n : ℕ} (f : Fin n → Fin w) (hn : 0 < n) :
    indexSpan (List.ofFn f) = (f ⟨n-1, by omega⟩).val + 1 - (f ⟨0, hn⟩).val := by
  cases n with
  | zero => omega
  | succ n =>
    have he : List.ofFn f ≠ [] := by simp
    have hl := List.getLast_ofFn (f := f) he
    simp only [List.ofFn_succ, List.getLast_eq_getLastD] at hl
    simp only [List.ofFn_succ, indexSpan]
    rw [hl]
    rfl

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.BitCounting ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem card_bit_equalities_le {ι J : Type*} [Fintype J] [DecidableEq J] [DecidableEq ι]
    (I : Finset ι) (f g : ι → J) (hg : Function.Injective g)
    (hcross : ∀ i ∈ I, ∀ j ∈ I, f i ≠ g j) :
    (Finset.univ.filter (fun ω : J → Bool => ∀ i ∈ I, ω (f i) = ω (g i))).card ≤
      2 ^ (Fintype.card J - I.card) := by
  classical
  let T := I.image g
  let π : (J → Bool) → (↥(Tᶜ : Finset J) → Bool) := fun ω j => ω j.val
  have hinj : Set.InjOn π (↑(Finset.univ.filter (fun ω : J → Bool => ∀ i ∈ I, ω (f i) = ω (g i))) : Set (J → Bool)) := by
    intro ω hω η hη he
    have hω := (Finset.mem_filter.mp hω).2
    have hη := (Finset.mem_filter.mp hη).2
    funext j
    by_cases hj : j ∈ T
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      have hf : f i ∈ Tᶜ := by
        apply Finset.mem_compl.mpr
        intro hh
        obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hh
        exact hcross i hi k hk heq.symm
      have heq : ω (f i) = η (f i) := congrFun he ⟨f i, hf⟩
      exact (hω i hi).symm.trans (heq.trans (hη i hi))
    · exact congrFun he ⟨j, Finset.mem_compl.mpr hj⟩
  have hc := Finset.card_le_card_of_injOn π (fun _ _ => Finset.mem_univ _) hinj
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
    Finset.card_compl, Finset.card_image_of_injective I hg, T] using hc

theorem card_matching_equalities_le {ι J : Type*} [Fintype J] [DecidableEq J] [DecidableEq ι]
    (I : Finset ι) (f g : ι → J) (hf : Function.Injective f) (hg : Function.Injective g)
    (hne : ∀ i ∈ I, f i ≠ g i) (w : ℕ) (hw : w ≤ 16*I.card) :
    (Finset.univ.filter (fun ω : J → Bool => ∀ i ∈ I, ω (f i) = ω (g i))).card ≤
      2 ^ (Fintype.card J - w/64) := by
  classical
  obtain ⟨S, hSI, hcard, hcross⟩ := exists_disjoint_pair_subfamily f g hf hg I hne
  have hsub : (Finset.univ.filter (fun ω : J → Bool => ∀ i ∈ I, ω (f i) = ω (g i))) ⊆
      Finset.univ.filter (fun ω : J → Bool => ∀ i ∈ S, ω (f i) = ω (g i)) := by
    intro ω hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => (Finset.mem_filter.mp hω).2 i (hSI hi)⟩
  have hh : w/64 ≤ S.card := by omega
  exact (Finset.card_le_card hsub).trans ((card_bit_equalities_le S f g hg hcross).trans
    (Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_left hh _)))

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.RandomCodes ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

open Classical

theorem denseList_sorted {w : ℕ} (P : DenseParameters w) :
    (denseList P).Pairwise (fun i j => i.val < j.val) :=
  (Finset.sortedLT_sort (Finset.Icc P.1 P.2.1 \ P.2.2.val)).pairwise

theorem exists_denseParameters {w : ℕ} (is : List (Fin w))
    (hs : is.Pairwise (fun i j => i.val < j.val)) (hn : 0 < is.length)
    (hloss : (indexSpan is - is.length : ℕ) ≤ (w : ℝ)/1048576) :
    ∃ P : DenseParameters w, denseList P = is := by
  classical
  let lo := is.get ⟨0, hn⟩
  let hi := is.get ⟨is.length-1, by omega⟩
  let S := is.toFinset
  have hm : StrictMono is.get := List.pairwise_iff_get.mp hs
  have hsub : S ⊆ Finset.Icc lo hi := by
    intro i hiS
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hiS)
    subst i
    exact Finset.mem_Icc.mpr ⟨hm.monotone (by exact Nat.zero_le _), hm.monotone (by
      change k.val ≤ is.length-1; omega)⟩
  have hcard : S.card = is.length := List.toFinset_card_of_nodup hs.nodup
  have hspan : (Finset.Icc lo hi).card = indexSpan is := by
    rw [Fin.card_Icc]
    have hh := indexSpan_ofFn is.get hn
    simpa only [List.ofFn_get] using hh.symm
  let H := Finset.Icc lo hi \ S
  have hH : (H.card : ℝ) ≤ (w : ℝ)/1048576 := by
    simpa only [H, Finset.card_sdiff_of_subset hsub, hcard, hspan] using hloss
  refine ⟨(lo, hi, ⟨H, hH⟩), ?_⟩
  dsimp only [denseList]
  rw [show Finset.Icc lo hi \ H = S from Finset.sdiff_sdiff_eq_self hsub]
  exact (List.toFinset_sort (· ≤ ·) hs.nodup).mpr (hs.imp (fun h => h.le))

theorem card_badDenseWitness_le {α : Type*} [Fintype α] {w : ℕ}
    (W : DenseWitness α w) :
    (Finset.univ.filter (badDenseWitness W)).card ≤
      2^(Fintype.card α*w-w/64) := by
  classical
  let is := denseList W.1.2
  let js := denseList W.2.2
  by_cases hc : is.length = js.length ∧ w ≤ 16*is.length ∧
      (W.1.1 ≠ W.2.1 ∨ ∀ i : Fin w, (i,i) ∉ is.zip js)
  · obtain ⟨hlen, hw, hne⟩ := hc
    let f : Fin is.length → α × Fin w := fun k => (W.1.1, is.get k)
    let g : Fin is.length → α × Fin w := fun k => (W.2.1, js.get (Fin.cast hlen k))
    have his : StrictMono is.get := List.pairwise_iff_get.mp (denseList_sorted _)
    have hjs : StrictMono js.get := List.pairwise_iff_get.mp (denseList_sorted _)
    have hf : Function.Injective f := fun i j h => his.injective (congrArg Prod.snd h)
    have hg : Function.Injective g := by
      intro i j h
      have hh := hjs.injective (congrArg Prod.snd h)
      exact Fin.ext (show i.val = j.val from congrArg (fun k : Fin js.length => k.val) hh)
    have hpair (i : Fin is.length) : (is.get i, js.get (Fin.cast hlen i)) ∈ is.zip js := by
      apply List.mem_iff_get.mpr
      refine ⟨⟨i.val, by simp only [List.length_zip]; omega⟩, ?_⟩
      simp only [List.get_eq_getElem, List.getElem_zip, Fin.val_cast]
    have hn : ∀ i ∈ (Finset.univ : Finset (Fin is.length)), f i ≠ g i := by
      intro i _ he
      rcases hne with hne | hne
      · exact hne (show W.1.1 = W.2.1 from congrArg (fun x : α × Fin w => x.1) he)
      · have hh : is.get i = js.get (Fin.cast hlen i) := congrArg (fun x : α × Fin w => x.2) he
        exact hne (is.get i) (hh.symm ▸ hpair i)
    have hsub : Finset.univ.filter (badDenseWitness W) ⊆
        Finset.univ.filter (fun ω : α × Fin w → Bool => ∀ i ∈ (Finset.univ : Finset (Fin is.length)), ω (f i) = ω (g i)) := by
      intro ω hω
      have hω := (Finset.mem_filter.mp hω).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i _ => hω.2.2.2 _ (hpair i)⟩
    have hh := card_matching_equalities_le (Finset.univ : Finset (Fin is.length)) f g hf hg hn w (by simpa using hw)
    exact (Finset.card_le_card hsub).trans (by simpa [Fintype.card_prod, Fintype.card_fin] using hh)
  · have he : Finset.univ.filter (badDenseWitness W) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hω := (Finset.mem_filter.mp hω).2
      exact hc ⟨hω.1, hω.2.1, hω.2.2.1⟩
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

theorem card_denseWitness_le {α : Type*} [Fintype α] (w : ℕ) :
    (Fintype.card (DenseWitness α w) : ℝ) ≤
      (Fintype.card α : ℝ)^2 * (w : ℝ)^4 * Real.exp ((w : ℝ)/256) := by
  classical
  have hk : (Fintype.card (SmallHoles w) : ℝ) ≤ Real.exp ((w : ℝ)/512) := by
    simpa only [SmallHoles, Fintype.card_subtype] using card_small_subsets_le w
  have he : Real.exp ((w : ℝ)/256) = Real.exp ((w : ℝ)/512)^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hc : (Fintype.card (DenseWitness α w) : ℝ) =
      (Fintype.card α : ℝ)^2 * (w : ℝ)^4 * (Fintype.card (SmallHoles w) : ℝ)^2 := by
    simp only [DenseWitness, DenseParameters, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    ring
  rw [hc, he]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hk 2) (by positivity)

theorem dense_union_numerics {A w : ℕ} (hA : 2 ≤ A) (hw : 67108864 ≤ w)
    (hlog : 2048*Real.log (A : ℝ) ≤ w) (hd : 64 ∣ w) :
    (A : ℝ)^2 * (w : ℝ)^4 * Real.exp ((w : ℝ)/256) < (2 : ℝ)^(w/64) := by
  have hAp : (0 : ℝ) < A := by positivity
  have hwp : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hsqrt : 8192 ≤ Real.sqrt (w : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    exact_mod_cast hw
  have hlogw : Real.log (w : ℝ) ≤ 2*Real.sqrt (w : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hwp)
    rw [Real.log_sqrt hwp.le] at hh
    linarith
  have hsquare : (Real.sqrt (w : ℝ))^2 = w := Real.sq_sqrt hwp.le
  have hlogw' : 4096 * Real.log (w : ℝ) ≤ w := by
    nlinarith
  have hdiv : ((w/64 : ℕ) : ℝ)*64 = w := by
    exact_mod_cast Nat.div_mul_cancel hd
  have hlog2 : (1 : ℝ)/2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hexpl : (A : ℝ)^2 * (w : ℝ)^4 * Real.exp ((w : ℝ)/256) =
      Real.exp (2*Real.log (A : ℝ) + 4*Real.log (w : ℝ) + (w : ℝ)/256) := by
    rw [Real.exp_add, Real.exp_add]
    have h2 := Real.exp_nat_mul (Real.log (A : ℝ)) 2
    have h4 := Real.exp_nat_mul (Real.log (w : ℝ)) 4
    norm_num only [Nat.cast_ofNat, Real.exp_log hAp, Real.exp_log hwp] at h2 h4
    rw [h2, h4]
  have hexpr : (2 : ℝ)^(w/64) = Real.exp (((w/64 : ℕ) : ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hexpl, hexpr]
  apply Real.exp_lt_exp.mpr
  have hpos : (0 : ℝ) < (w/64 : ℕ) := by nlinarith
  have hm := mul_lt_mul_of_pos_left hlog2 hpos
  linarith

theorem exists_coding_width (A : ℕ) (hA : 2 ≤ A) :
    ∃ w : ℕ, 67108864 ≤ w ∧ 64 ∣ w ∧
      2048*Real.log (A : ℝ) ≤ w ∧
      (w : ℝ) ≤ 67108928 * Real.log (2*A) := by
  let t := Real.log (2*(A : ℝ))
  have hAp : (0 : ℝ) < A := by positivity
  have ht : 1 ≤ t := by
    have hh : (4 : ℝ) ≤ 2*A := by exact_mod_cast (by omega : 4 ≤ 2*A)
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hh
    have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    dsimp only [t]
    linarith [Real.log_two_gt_d9]
  have hAt : Real.log (A : ℝ) ≤ t := Real.log_le_log hAp (by nlinarith)
  let n := ⌈1048576*t⌉₊
  have hn : 1048576*t ≤ (n : ℝ) := Nat.le_ceil _
  have hn' : (n : ℝ) < 1048576*t+1 := Nat.ceil_lt_add_one (by positivity)
  refine ⟨64*n, ?_, dvd_mul_right _ _, ?_, ?_⟩
  · have hh : (67108864 : ℝ) ≤ 64*n := by nlinarith
    exact_mod_cast hh
  · push_cast
    nlinarith
  · push_cast
    change 64*(n : ℝ) ≤ 67108928*t
    nlinarith

theorem exists_strongLocal (α : Type*) [Fintype α] (hA : 2 ≤ Fintype.card α) :
    ∃ (w : ℕ) (c : α → Fin w → Bool), 67108864 ≤ w ∧ 64 ∣ w ∧
      (w : ℝ) ≤ 67108928 * Real.log (2*Fintype.card α) ∧ StrongLocal c := by
  classical
  obtain ⟨w, hw, hd, hlog, hwidth⟩ := exists_coding_width (Fintype.card α) hA
  let Ω := α × Fin w → Bool
  let B : Finset Ω := Finset.univ.biUnion (fun W : DenseWitness α w =>
    Finset.univ.filter (badDenseWitness W))
  have hcard : B.card ≤ Fintype.card (DenseWitness α w) * 2^(Fintype.card α*w-w/64) := by
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _W : DenseWitness α w, 2^(Fintype.card α*w-w/64) :=
        Finset.sum_le_sum (fun W _ => card_badDenseWitness_le W)
      _ = _ := by simp
  have hexp : (Fintype.card (DenseWitness α w) : ℝ) < (2 : ℝ)^(w/64) :=
    (card_denseWitness_le w).trans_lt (dense_union_numerics hA hw hlog hd)
  have hkn : w/64 ≤ Fintype.card α*w := by
    have hh : w ≤ Fintype.card α*w := by nlinarith
    exact (Nat.div_le_self _ _).trans hh
  have hstrict : (B.card : ℝ) < (2 : ℝ)^(Fintype.card α*w) := by
    have hc : (B.card : ℝ) ≤ (Fintype.card (DenseWitness α w) : ℝ) * (2 : ℝ)^(Fintype.card α*w-w/64) := by
      exact_mod_cast hcard
    calc
      _ ≤ _ := hc
      _ < (2 : ℝ)^(w/64) * (2 : ℝ)^(Fintype.card α*w-w/64) :=
        mul_lt_mul_of_pos_right hexp (by positivity)
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le hkn]
  have hB : B.card < (Finset.univ : Finset Ω).card := by
    have he : (Finset.univ : Finset Ω).card = 2^(Fintype.card α*w) := by
      simp [Ω, Fintype.card_prod]
    rw [he]
    exact_mod_cast hstrict
  obtain ⟨ω, _, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hB
  have hω' (W : DenseWitness α w) : ¬badDenseWitness W ω := by
    intro hh
    apply hω
    exact Finset.mem_biUnion.mpr ⟨W, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩
  refine ⟨w, fun a i => ω (a,i), hw, hd, hwidth, ?_⟩
  intro a b is js his hjs hlen hsize hli hlj hbits
  have hn : 0 < is.length := by omega
  obtain ⟨P, hP⟩ := exists_denseParameters is his hn hli
  obtain ⟨Q, hQ⟩ := exists_denseParameters js hjs (by omega) hlj
  by_contra hh
  apply hω' ((a,P),(b,Q))
  dsimp only [badDenseWitness]
  rw [hP, hQ]
  refine ⟨hlen, hsize, ?_, hbits⟩
  by_cases hab : a = b
  · exact Or.inr (fun i hi => hh ⟨hab, i, hi⟩)
  · exact Or.inl hab

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical


theorem solution : type_of% @_root_.OAI.FiniteCircle.exists_strongLocal := @_root_.OAI.FiniteCircle.exists_strongLocal
