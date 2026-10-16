-- Prove2me | solution 1 for OAI.TreeEdit.TorusFourier.branch_summaries
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:06:56.041996+00:00
-- url     : https://prove2.me/submissions/d3827ec1-181c-4844-9b0c-6b98e00eebee

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CircleFourier.lean:L278-L300
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.TorusFourier.branch_summaries. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_FiniteTree_few_prime_divisors

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

lemma group_prime_dvd {I : Type} {g : ℕ} (r : I → ℕ) (j : Fin g → I)
    (σ : Equiv.Perm I) (v : Fin g) : r (σ (j v)) ∣ period r j σ :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ v)

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

end TreeEdit.TorusTree

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CircleFourier ----
namespace OAI

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical

lemma character_apply {M : ℕ} [NeZero M] (χ : AddChar (ZMod M) ℂ) (a : ZMod M) :
    χ a = ZMod.stdAddChar (frequency χ * a) := by
  have hh := AddChar.zmodAddEquiv.apply_symm_apply χ
  change AddChar.zmodAddEquiv (frequency χ) = χ at hh
  calc
    χ a = (AddChar.zmodAddEquiv (frequency χ)) a := congrArg (fun η : AddChar (ZMod M) ℂ => η a) hh.symm
    _ = _ := rfl

lemma frequency_eq_zero {M : ℕ} [NeZero M] (χ : AddChar (ZMod M) ℂ) :
    frequency χ = 0 ↔ χ = 0 := by
  change AddChar.zmodAddEquiv.symm χ = 0 ↔ χ = 0
  exact (AddChar.zmodAddEquiv (n := M)).symm.map_eq_zero_iff

lemma centered_cast {M : ℕ} [NeZero M] (χ : AddChar (ZMod M) ℂ) :
    (centered χ : ZMod M) = frequency χ := ZMod.coe_valMinAbs _

lemma centered_eq_zero {M : ℕ} [NeZero M] (χ : AddChar (ZMod M) ℂ) :
    centered χ = 0 ↔ χ = 0 := by
  rw [centered, ZMod.valMinAbs_eq_zero, frequency_eq_zero]

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical
open TorusTree

lemma char_sum {A ι : Type*} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

lemma natAbs_real (a : ℤ) : (a.natAbs : ℝ) = |(a : ℝ)| := by
  have hh := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs a)
  simpa only [Int.cast_natCast, Int.cast_abs] using hh

lemma summary_add {M m : ℕ} [NeZero M] (h : ℕ) (χ : AddChar (State (ZMod M) m (h+1)) ℂ) :
    summary (h+1) χ = ∑ i : Fin m, summary h (χ.compAddMonoidHom (child (A := ZMod M) h i)) := by
  ext a
  change χ (diagonal (A := ZMod M) (m := m) (h+1) a) = _
  rw [AddChar.sum_apply]
  have he : diagonal (A := ZMod M) (m := m) (h+1) a =
      ∑ i : Fin m, child (A := ZMod M) h i (diagonal (A := ZMod M) (m := m) h a) := by
    change (fun _ : Fin m => diagonal (A := ZMod M) (m := m) h a) = ∑ i, Pi.single i _
    exact (Finset.univ_sum_single _).symm
  rw [he, char_sum]
  rfl

lemma centered_summary_add {M m Q : ℕ} [NeZero M] (h : ℕ)
    (χ : AddChar (State (ZMod M) m (h+1)) ℂ) (hM : (m+1)*Q < M)
    (hp : |(centered (summary (h+1) χ) : ℝ)| < Q)
    (hc : ∀ i : Fin m, |(centered (summary h (χ.compAddMonoidHom (child (A := ZMod M) h i))) : ℝ)| < Q) :
    centered (summary (h+1) χ) = ∑ i : Fin m, centered (summary h (χ.compAddMonoidHom (child (A := ZMod M) h i))) := by
  let a := centered (summary (h+1) χ)
  let b (i : Fin m) := centered (summary h (χ.compAddMonoidHom (child (A := ZMod M) h i)))
  have he : ((a - ∑ i, b i : ℤ) : ZMod M) = 0 := by
    simp only [Int.cast_sub, Int.cast_sum, a, b, centered_cast]
    rw [summary_add]
    exact sub_eq_zero.mpr (map_sum (AddChar.zmodAddEquiv.symm) _ _)
  have hd : (M : ℤ) ∣ a - ∑ i, b i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he
  have hb : |((∑ i, b i : ℤ) : ℝ)| ≤ (m : ℝ) * Q := by
    rw [Int.cast_sum]
    calc
      _ ≤ ∑ i : Fin m, |(b i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin m, (Q : ℝ) := Finset.sum_le_sum fun i _ => (hc i).le
      _ = _ := by simp
  have hab : |((a - ∑ i, b i : ℤ) : ℝ)| < M := by
    rw [Int.cast_sub]
    have hh := abs_sub (a : ℝ) ((∑ i, b i : ℤ) : ℝ)
    have hMr : ((m : ℝ)+1)*Q < M := by exact_mod_cast hM
    dsimp only [a] at hh ⊢
    nlinarith
  have hz : a - ∑ i, b i = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by
    rw [Int.natAbs_natCast]
    exact_mod_cast (show ((a - ∑ i, b i : ℤ).natAbs : ℝ) < M by rw [natAbs_real]; exact hab))
  exact sub_eq_zero.mp hz

lemma outside_coefficient_dvd {I : Type} {g s L : ℕ} (r : I → ℕ)
    (hr : ∀ i, 0 < r i) (j : Fin g → I) (σ : Equiv.Perm I)
    (z : ZMod L) (i : Fin (g*s)) (v : Fin g) (hvi : v ≠ group i) :
    (r (σ (j v)) : ℤ) ∣ (coefficient r j σ z i : ℤ) - 1 := by
  have hquot : period r j σ / r (σ (j (group i))) = ∏ a ∈ Finset.univ.erase (group i), r (σ (j a)) := by
    unfold period
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (group i)), Nat.mul_div_cancel_left _ (hr _)]
  have hd : r (σ (j v)) ∣ period r j σ / r (σ (j (group i))) := by
    rw [hquot]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hvi, Finset.mem_univ _⟩)
  have hdz : (r (σ (j v)) : ℤ) ∣ ((period r j σ / r (σ (j (group i))) : ℕ) : ℤ) := by exact_mod_cast hd
  simpa only [coefficient, Nat.cast_add, Nat.cast_one, Nat.cast_mul, add_sub_cancel_left] using dvd_mul_of_dvd_right hdz (((z.val % r (σ (j (group i)))) : ℕ) : ℤ)

lemma branch_integer {I : Type} {g s L b e K Q : ℕ} (r : I → ℕ)
    (hr : ∀ i, Nat.Prime (r i)) (hinj : Function.Injective r)
    (j : Fin g ↪ I) (σ : Equiv.Perm I) (z : Fin (g*s) → ZMod L)
    (hb : 1 ≤ b) (hlower : ∀ i, b ≤ r i) (hQ : Q ≤ b^e) (hg : e + K ≤ g)
    (a : ℤ) (t : Fin (g*s) → ℤ) (ha : a ≠ 0) (habs : a.natAbs < Q)
    (hsum : a = ∑ i, t i)
    (hcong : (period r j σ : ℤ) ∣ ∑ i, (coefficient r j σ (z i) i : ℤ) * t i) :
    K ≤ (Finset.univ.filter (fun i => t i ≠ 0)).card := by
  let S := Finset.univ.filter (fun i => t i ≠ 0)
  let O := S.image (group (g := g) (s := s))
  let E := Finset.univ \ O
  have hdiv (v : Fin g) (hv : v ∈ E) : (r (σ (j v)) : ℤ) ∣ a := by
    have hvo : v ∉ O := (Finset.mem_sdiff.mp hv).2
    have he (i : Fin (g*s)) : (r (σ (j v)) : ℤ) ∣ ((coefficient r j σ (z i) i : ℤ) - 1) * t i := by
      by_cases hi : group i = v
      · have ht : t i = 0 := by
          by_contra hn
          exact hvo (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, hi⟩)
        rw [ht, mul_zero]
        exact dvd_zero _
      · exact dvd_mul_of_dvd_left (outside_coefficient_dvd r (fun i => (hr i).pos) j σ (z i) i v (Ne.symm hi)) _
    have hdiff : (r (σ (j v)) : ℤ) ∣ (∑ i, (coefficient r j σ (z i) i : ℤ) * t i) - a := by
      rw [hsum, ← Finset.sum_sub_distrib]
      simp_rw [sub_mul, one_mul] at he
      exact Finset.dvd_sum (fun i _ => he i)
    have hdP : (r (σ (j v)) : ℤ) ∣ (period r j σ : ℤ) := by exact_mod_cast group_prime_dvd r j σ v
    exact (dvd_sub (hdP.trans hcong) hdiff) |> (by simpa only [sub_sub_cancel] using ·)
  have hcount := FiniteTree.few_prime_divisors (fun v : Fin g => r (σ (j v)))
    (fun v => hr _) (hinj.comp (σ.injective.comp j.injective)) hb (fun v => hlower _) hQ a ha habs
  have he : E.card < e := lt_of_le_of_lt (Finset.card_le_card (by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiv v hv⟩)) hcount
  have ho : O.card ≤ S.card := Finset.card_image_le
  have hpartition : E.card + O.card = g := by
    have hh := Finset.card_sdiff_add_card_eq_card (show O ⊆ Finset.univ from Finset.subset_univ O)
    simpa only [E, Finset.card_univ, Fintype.card_fin] using hh
  change K ≤ S.card
  omega

end TreeEdit.TorusFourier

namespace TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree

lemma character_state {A : Type} [AddCommGroup A] {m h : ℕ}
    (χ : AddChar (State A m (h+1)) ℂ) (x : State A m (h+1)) :
    χ x = ∏ i : Fin m, (χ.compAddMonoidHom (child (A := A) h i)) (x i) := by
  have he : x = ∑ i : Fin m, child (A := A) h i (x i) := (Finset.univ_sum_single x).symm
  conv_lhs => rw [he, char_sum]
  rfl

lemma cycle_congruence {I : Type} {g s L M : ℕ} [NeZero M] (r : I → ℕ)
    (j : Fin g → I) (hr : ∀ i, 0 < r i) (h : ℕ) (C : Config I L (g*s) (h+1))
    (hPM : period r j C.1 ∣ M) (χ : AddChar (State (ZMod M) (g*s) (h+1)) ℂ)
    (hχ : χ (cycle (M := M) r j h C) = 1) :
    (period r j C.1 : ℤ) ∣ ∑ i : Fin (g*s), (coefficient r j C.1 (C.2 i).1 i : ℤ) *
      centered (summary h (χ.compAddMonoidHom (child (A := ZMod M) h i))) := by
  let t (i : Fin (g*s)) := centered (summary h (χ.compAddMonoidHom (child (A := ZMod M) h i)))
  let S : ℤ := ∑ i : Fin (g*s), (coefficient r j C.1 (C.2 i).1 i : ℤ) * t i
  let P := period r j C.1
  have he : χ (cycle (M := M) r j h C) = ZMod.stdAddChar ((S : ZMod M) * (M/P : ZMod M)) := by
    rw [character_state]
    change (∏ i : Fin (g*s), summary h (χ.compAddMonoidHom (child (A := ZMod M) h i))
      ((coefficient r j C.1 (C.2 i).1 i) • (M/P : ZMod M))) = _
    dsimp only [S]
    rw [Int.cast_sum, Finset.sum_mul, char_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [character_apply, nsmul_eq_mul, ← centered_cast]
    congr 1
    simp only [Int.cast_mul, Int.cast_natCast, t]
    ring
  have hzero : (S : ZMod M) * (M/P : ZMod M) = 0 := by
    apply ZMod.injective_stdAddChar
    rw [← he, hχ, AddChar.map_zero_eq_one]
  have hd : (M : ℤ) ∣ S * ((M/P : ℕ) : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa only [Int.cast_mul, Int.cast_natCast] using hzero
  have hMP : 0 < M/P := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hPM) (period_pos hr j C.1)
  have hemp : (M : ℤ) = (P : ℤ) * ((M/P : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mul_div_cancel' hPM).symm
  rw [hemp] at hd
  exact (Int.mul_dvd_mul_iff_right (by exact_mod_cast hMP.ne' : ((M/P : ℕ) : ℤ) ≠ 0)).mp hd

lemma branch_summaries {I : Type} {g s L M b e K Q : ℕ} [NeZero M] (r : I → ℕ)
    (hr : ∀ i, Nat.Prime (r i)) (hinj : Function.Injective r) (j : Fin g ↪ I)
    (hb : 1 ≤ b) (hlower : ∀ i, b ≤ r i) (hQ : Q ≤ b^e) (hg : e+K ≤ g)
    (hM : (g*s+1)*Q < M) (h : ℕ) (C : Config I L (g*s) (h+1))
    (hPM : period r j C.1 ∣ M) (χ : AddChar (State (ZMod M) (g*s) (h+1)) ℂ)
    (hp : |(centered (summary (h+1) χ) : ℝ)| < Q)
    (hc : ∀ i : Fin (g*s), |(centered (summary h (χ.compAddMonoidHom (child (A := ZMod M) h i))) : ℝ)| < Q)
    (hχ : χ (cycle (M := M) r j h C) = 1) (hn : summary (h+1) χ ≠ 0) :
    K ≤ (Finset.univ.filter (fun i : Fin (g*s) => summary h (χ.compAddMonoidHom (child (A := ZMod M) h i)) ≠ 0)).card := by
  have hh := branch_integer r hr hinj j C.1 (fun i => (C.2 i).1) hb hlower hQ hg
    (centered (summary (h+1) χ))
    (fun i => centered (summary h (χ.compAddMonoidHom (child (A := ZMod M) h i))))
    ((centered_eq_zero _).not.mpr hn)
    (by exact_mod_cast (show ((centered (summary (h+1) χ)).natAbs : ℝ) < Q by rw [natAbs_real]; exact hp))
    (centered_summary_add h χ hM hp hc)
    (cycle_congruence r j (fun i => (hr i).pos) h C hPM χ hχ)
  have he : (Finset.univ.filter (fun i : Fin (g*s) => centered (summary h (χ.compAddMonoidHom (child (A := ZMod M) h i))) ≠ 0)) =
      (Finset.univ.filter (fun i : Fin (g*s) => summary h (χ.compAddMonoidHom (child (A := ZMod M) h i)) ≠ 0)) := by
    apply Finset.filter_congr
    intro i _
    exact (centered_eq_zero _).not
  rw [he] at hh
  exact hh

end TreeEdit.TorusFourier

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.TorusFourier
open scoped BigOperators
open Classical TorusTree


theorem solution : type_of% @_root_.OAI.TreeEdit.TorusFourier.branch_summaries := @_root_.OAI.TreeEdit.TorusFourier.branch_summaries
