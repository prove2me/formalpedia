-- Prove2me | solution 1 for OAI.Thorp.Current.first_reciprocal_main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:41:27.088836+00:00
-- url     : https://prove2.me/submissions/aed729eb-05c9-4330-9032-75a4c216a1a4

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/FirstMain.lean:L13-L33
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.Thorp.Current.first_reciprocal_main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_Thorp_Current_first_reciprocal_main) verbatim and is proved by it.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_PartitionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_DegreeBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_FirstMoment
import Definitions.Def_OAI_Probability_ThorpShuffle_Reynolds
import Definitions.Def_OAI_Probability_ThorpShuffle_FourierFamilies
import Definitions.Def_OAI_Probability_ThorpShuffle_JointProjectors
import Definitions.Def_OAI_Probability_ThorpShuffle_ProductProjectors
import Definitions.Def_OAI_Probability_ThorpShuffle_SymmetricFamilies
import Definitions.Def_OAI_Probability_ThorpShuffle_BlockEmbedding
import Theorems.Thm_OAI_Thorp_Current_eight_block_of_cap
import Theorems.Thm_OAI_Thorp_Specht_bulk_degree
import Theorems.Thm_OAI_Thorp_Specht_defect_card_bound
import Theorems.Thm_OAI_Thorp_Young_choose_row_le_extensions
import Theorems.Thm_OAI_Thorp_Young_extensions_card_ideal
import Theorems.Thm_OAI_Thorp_Young_partition_count_le_sqrt_pow

-- ---- from OAI.Probability.ThorpShuffle.Classification ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uG uI uV uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

lemma card_ofPartition {n : ℕ} (p : Nat.Partition n) : Fintype.card (Cells (ofPartition p)) = n := by
  rw [card_cells_eq_sum, rowLens_ofPartition]
  simpa only [← Multiset.sum_coe, Multiset.sort_eq] using p.parts_sum

end Thorp.Young

namespace Thorp.Fourier
open scoped Classical

variable {G : Type uG} [Group G] [Fintype G]

end Thorp.Fourier

namespace Thorp.Specht
open scoped Classical
variable {α : Type uα} [Fintype α]

end Thorp.Specht

namespace Thorp.Specht
open scoped Classical
variable {α : Type uα} [Fintype α]

end Thorp.Specht

end

end OAI

-- ---- from OAI.Probability.ThorpShuffle.LinearExtensions ----
namespace OAI

universe uA uα uI uB

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

variable (A : Type uA) [Fintype A] [PartialOrder A]

end Thorp.Young

namespace Thorp.Specht
open scoped Classical
variable {α : Type uα} [Fintype α]

end Thorp.Specht

namespace Thorp.Young
open scoped Classical
variable (A : Type uA) [Fintype A] [PartialOrder A]

end Thorp.Young

namespace Thorp.Specht
open scoped Classical
variable {n : ℕ} (D : YoungDiagram) (t : Fin n ≃ Thorp.Young.Cells D)

end Thorp.Specht

namespace Thorp.Young
open scoped Classical

lemma extensions_card_orderIso {A : Type uA} {B : Type uB} [Fintype A] [Fintype B] [PartialOrder A] [PartialOrder B]
    (e : A ≃o B) : Fintype.card (Extensions A) = Fintype.card (Extensions B) := by
  let c := finCongr (Fintype.card_congr e.toEquiv)
  let F : Extensions A ≃ Extensions B := {
    toFun := fun l => ⟨(e.symm.toEquiv.trans l.val).trans c, fun _ _ h => l.property (e.symm.strictMono h)⟩
    invFun := fun l => ⟨(e.toEquiv.trans l.val).trans c.symm, fun _ _ h => l.property (e.strictMono h)⟩
    left_inv := by intro l; apply Subtype.ext; ext x; simp [c]
    right_inv := by intro l; apply Subtype.ext; ext x; simp [c] }
  exact Fintype.card_congr F

end Thorp.Young

end

end OAI

-- ---- from OAI.Probability.ThorpShuffle.ExtensionBounds ----
namespace OAI

universe uA

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

end Thorp.Young

namespace Thorp.Young
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

end Thorp.Young

namespace Thorp.Young
open scoped Classical

lemma card_lower_add (D : YoungDiagram) :
    D.rowLen 0 + Fintype.card (Lower D) = Fintype.card (Cells D) := by
  have h := Fintype.card_congr (Equiv.sumCompl (fun x : Cells D => x.val.1 = 0))
  simpa only [Fintype.card_sum, card_row_subtype] using h

end Thorp.Young

end

end OAI

-- ---- from OAI.Probability.ThorpShuffle.PartitionBounds ----
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

lemma idealDiagram_extensions_le (D : YoungDiagram) (s : Set (Cells D)) (hs : IsLowerSet s) :
    Fintype.card (Extensions (Cells (idealDiagram D s hs))) ≤ Fintype.card (Extensions (Cells D)) := by
  rw [extensions_card_orderIso (idealCells D s hs)]
  exact extensions_card_ideal s hs

theorem exists_trimLower (D : YoungDiagram) (k : ℕ) (hk : k ≤ Fintype.card (Lower D)) :
    ∃ E : YoungDiagram, E.rowLen 0 = D.rowLen 0 ∧ Fintype.card (Lower E) = k ∧
      Fintype.card (Extensions (Cells E)) ≤ Fintype.card (Extensions (Cells D)) := by
  obtain ⟨e⟩ := extensions_nonempty (Lower D)
  let s : Set (Cells D) := {x | ∀ h : x.val.1 ≠ 0, (e.val ⟨x, h⟩).val < k}
  have hs : IsLowerSet s := by
    intro y x hxy hy hx
    have hy' : y.val.1 ≠ 0 := by have := hxy.1; omega
    exact lt_of_le_of_lt (e.property.monotone (show (⟨x, hx⟩ : Lower D) ≤ ⟨y, hy'⟩ from hxy)) (hy hy')
  let E := idealDiagram D s hs
  have htop : E.rowLen 0 = D.rowLen 0 := by
    apply eq_of_forall_lt_iff
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, ← YoungDiagram.mem_iff_lt_rowLen]
    change (0, j) ∈ idealDiagram D s hs ↔ (0, j) ∈ D
    rw [mem_idealDiagram]
    exact ⟨fun h => h.choose, fun h => ⟨h, fun hn => (hn rfl).elim⟩⟩
  let f : Lower E ≃ Fin k := {
    toFun := fun x =>
      let z := idealCells D s hs x.val
      ⟨(e.val ⟨z.val, x.property⟩).val, z.property x.property⟩
    invFun := fun j =>
      let z := e.val.symm ⟨j.val, j.isLt.trans_le hk⟩
      ⟨(idealCells D s hs).symm ⟨z.val, by
        intro h
        have hh : (⟨z.val, h⟩ : Lower D) = z := rfl
        rw [hh, Equiv.apply_symm_apply]
        exact j.isLt⟩, z.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply (idealCells D s hs).injective
      apply Subtype.ext
      have hh := e.val.symm_apply_apply ⟨(idealCells D s hs x.val).val, x.property⟩
      simpa only [OrderIso.apply_symm_apply] using congrArg Subtype.val hh
    right_inv := by
      intro j
      apply Fin.ext
      simpa only [OrderIso.apply_symm_apply] using congrArg Fin.val (e.val.apply_symm_apply ⟨j.val, j.isLt.trans_le hk⟩) }
  exact ⟨E, htop, (Fintype.card_congr f).trans (Fintype.card_fin k), idealDiagram_extensions_le D s hs⟩

theorem choose_le_extensions (D : YoungDiagram) (k : ℕ)
    (hk : k ≤ Fintype.card (Lower D)) (hL : k ≤ D.rowLen 0) :
    (D.rowLen 0).choose k ≤ Fintype.card (Extensions (Cells D)) := by
  obtain ⟨E, htop, hsize, hle⟩ := exists_trimLower D k hk
  have hh := choose_row_le_extensions E (by rw [hsize, htop]; exact hL)
  rw [htop, hsize] at hh
  exact hh.trans hle

end Thorp.Young

namespace Thorp.Young
open scoped Classical

lemma rowLen_le_card (D : YoungDiagram) (i : ℕ) : D.rowLen i ≤ Fintype.card (Cells D) := by
  rw [← card_row_subtype D i]
  exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

lemma colLen_le_card (D : YoungDiagram) (j : ℕ) : D.colLen j ≤ Fintype.card (Cells D) := by
  rw [← card_column D j]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ)

end Thorp.Young

namespace Thorp.Young
open scoped Classical

lemma pow_le_choose_mul (a k : ℕ) : a ^ k ≤ (k * a).choose k := by
  let X := Fin k × Fin a
  let S := {s : Finset X // s.card = k}
  let f (v : Fin k → Fin a) : S := ⟨Finset.univ.image (fun i => (i, v i)), by
    rw [Finset.card_image_of_injective _ (by intro i j h; exact congrArg Prod.fst h), Finset.card_univ, Fintype.card_fin]⟩
  have hf : Function.Injective f := by
    intro v w hvw
    funext i
    have he := congrArg Subtype.val hvw
    have hm : (i, v i) ∈ (f w).val := by rw [← he]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    have hji : j = i := congrArg Prod.fst hj
    subst j
    exact (congrArg Prod.snd hj).symm
  have hS : Fintype.card S = (k * a).choose k := by
    calc
      _ = ((Finset.univ : Finset X).powersetCard k).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext s
        simp
      _ = _ := by simp [X]
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fun, Fintype.card_fin, hS] using hh

lemma pow_le_choose_of_mul_le (a k L : ℕ) (h : a * k ≤ L) : a ^ k ≤ L.choose k := by
  exact (pow_le_choose_mul a k).trans (Nat.choose_le_choose k (by simpa only [Nat.mul_comm] using h))

lemma sub_add_one_le_choose (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) : n - k + 1 ≤ n.choose k := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hkn
  simp only [Nat.add_sub_cancel_left]
  induction r with
  | zero => simp
  | succ r ih =>
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [show j + 1 + (r + 1) = (j + 1 + r) + 1 by omega, Nat.choose_succ_succ]
      have hp : 1 ≤ (j + 1 + r).choose j := Nat.one_le_iff_ne_zero.mpr (Nat.choose_ne_zero (by omega))
      simp only [Nat.succ_eq_add_one] at ih ⊢
      omega

end Thorp.Young

end

end OAI

-- ---- from OAI.Probability.ThorpShuffle.DegreeBounds ----
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

lemma orient_rowLen (D : YoungDiagram) : (orient D).rowLen 0 = longest D := by
  unfold orient longest
  split_ifs with h
  · exact (max_eq_left h).symm
  · rw [YoungDiagram.rowLen_transpose, max_eq_right (by omega)]

lemma orient_card (D : YoungDiagram) : Fintype.card (Cells (orient D)) = Fintype.card (Cells D) := by
  unfold orient
  split_ifs
  · rfl
  · exact (Fintype.card_congr (transposeCells D).toEquiv).symm

lemma orient_extensions (D : YoungDiagram) :
    Fintype.card (Extensions (Cells (orient D))) = Fintype.card (Extensions (Cells D)) := by
  by_cases h : D.colLen 0 ≤ D.rowLen 0
  · exact congrArg (fun E : YoungDiagram => Fintype.card (Extensions (Cells E))) (show orient D = D by simp [orient, h])
  · exact (congrArg (fun E : YoungDiagram => Fintype.card (Extensions (Cells E)))
      (show orient D = D.transpose by simp [orient, h])).trans
      (extensions_card_orderIso (transposeCells D)).symm

lemma longest_le_card (D : YoungDiagram) : longest D ≤ Fintype.card (Cells D) :=
  max_le (rowLen_le_card D 0) (colLen_le_card D 0)

end Thorp.Young

namespace Thorp.Specht
open scoped Classical
open Thorp.Young

lemma diagram_card {n : ℕ} (p : NShape n) : Fintype.card (Cells (ofPartition p)) = n := by
  simpa only [Fintype.card_fin] using card_ofPartition p

lemma defect_add_longest {n : ℕ} (p : NShape n) : defect p + longest (ofPartition p) = n := by
  have h := longest_le_card (ofPartition p)
  rw [diagram_card] at h
  exact Nat.sub_add_cancel h

lemma choose_longest_le_degree {n : ℕ} (p : NShape n) (k : ℕ)
    (hk : k ≤ defect p) (hL : k ≤ longest (ofPartition p)) :
    (longest (ofPartition p)).choose k ≤ degree p := by
  have hc : Fintype.card (Lower (orient (ofPartition p))) = defect p := by
    have hh := card_lower_add (orient (ofPartition p))
    rw [orient_rowLen, orient_card, diagram_card] at hh
    have hd := defect_add_longest p
    omega
  have hh := choose_le_extensions (orient (ofPartition p)) k (by rwa [hc]) (by rwa [orient_rowLen])
  rw [orient_rowLen, orient_extensions] at hh
  exact hh.trans (extensions_le_degree p)

lemma small_defect_degree {n : ℕ} (p : NShape n) (h : 4 * defect p ≤ n) :
    3 ^ defect p ≤ degree p := by
  have hd := defect_add_longest p
  exact (pow_le_choose_of_mul_le 3 _ _ (by omega)).trans
    (choose_longest_le_degree p _ le_rfl (by omega))

lemma fixed_defect_degree {n : ℕ} (p : NShape n) (hp : 0 < defect p) (h : 2 * defect p ≤ n) :
    n - 2 * defect p + 1 ≤ degree p := by
  have hd := defect_add_longest p
  have hh := sub_add_one_le_choose (longest (ofPartition p)) (defect p) hp (by omega)
  have he : longest (ofPartition p) - defect p = n - 2 * defect p := by omega
  rw [he] at hh
  exact hh.trans (choose_longest_le_degree p _ le_rfl (by omega))

end Thorp.Specht

end

end OAI

-- ---- from OAI.Probability.ThorpShuffle.ReciprocalDegrees ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

open Filter Topology

namespace Thorp.Analysis

lemma sqrt_log_small (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log (n + 1) ≤ c * Real.sqrt (n + 1) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).tendsto_div_nhds_zero.comp ht
  have he := h.eventually (gt_mem_nhds hc)
  filter_upwards [he] with n hn
  dsimp only [Function.comp_apply] at hn
  rw [← Real.sqrt_eq_rpow] at hn
  exact ((div_lt_iff₀ (Real.sqrt_pos.mpr (by positivity))).mp hn).le

end Thorp.Analysis

namespace Thorp.Specht
open scoped Classical
open Filter Topology Thorp.Young

variable {n : ℕ}

end Thorp.Specht

namespace Thorp.Specht
open scoped Classical
open Filter Topology Thorp.Young

end Thorp.Specht

end

end OAI

-- ---- from OAI.Probability.ThorpShuffle.FirstMoment ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace Thorp.Current
open scoped BigOperators Classical ComplexConjugate InnerProductSpace
open Filter Topology

open Thorp.Specht Thorp.Young
variable {n : ℕ}

lemma partition_first_exponential_decay :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (2 * Nat.sqrt n) / (2 : ℝ) ^ (n / 16)) atTop (𝓝 0) := by
  have hc : 0 < Real.log 2 / 256 := by positivity
  have he := Thorp.Analysis.sqrt_log_small (Real.log 2 / 256) hc
  have ht : Tendsto (fun n : ℕ => Real.exp (-(Real.log 2 / 64) * n)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos (by positivity))
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _ ht
  filter_upwards [he, eventually_ge_atTop 32] with n hn hn32
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hs : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n + 1) := by
    apply Real.le_sqrt_of_sq_le
    have hh : ((Nat.sqrt n : ℝ)^2) ≤ n := by exact_mod_cast (show (Nat.sqrt n)^2 ≤ n by simpa only [pow_two] using Nat.sqrt_le n)
    linarith
  have hdiv : (n : ℝ) / 32 ≤ (n / 16 : ℕ) := by
    have hh : n ≤ 32 * (n / 16) := by omega
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr (by exact_mod_cast (by omega : n ≤ n / 16 * 32))
  have hp : 2 * (Nat.sqrt n : ℝ) * Real.log (n + 1) ≤ (Real.log 2 / 64) * n := by
    have hl : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by linarith)
    have h₁ := mul_le_mul_of_nonneg_right hs hl
    have h₂ := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg ((n : ℝ) + 1))
    have hh := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
    have hc0 : 0 ≤ Real.log 2 / 256 := hc.le
    have hsq : Real.sqrt (n + 1) * ((Real.log 2 / 256) * Real.sqrt (n + 1)) = (Real.log 2 / 256) * (n + 1) := by calc
      _ = (Real.log 2 / 256) * (Real.sqrt (n + 1))^2 := by ring
      _ = _ := by rw [hh]
    rw [hsq] at h₂
    have h₃ := mul_le_mul_of_nonneg_left (show (n : ℝ) + 1 ≤ 2 * n by linarith) hc0
    linarith only [h₁, h₂, h₃]
  have hq : -(Real.log 2 / 64) * n ≥
      (2 * Nat.sqrt n : ℕ) * Real.log (n + 1) - (n / 16 : ℕ) * Real.log 2 := by
    push_cast
    have hh := mul_le_mul_of_nonneg_right hdiv (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    linarith
  calc
    _ = Real.exp ((2 * Nat.sqrt n : ℕ) * Real.log (n + 1) - (n / 16 : ℕ) * Real.log 2) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by positivity), Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.exp_le_exp.mpr hq

lemma inverseFirst_nonneg (p : NShape n) : 0 ≤ inverseFirst p := by unfold inverseFirst; positivity
lemma slice_nonneg (n u : ℕ) : 0 ≤ slice n u := Finset.sum_nonneg (fun _ _ => inverseFirst_nonneg _)
lemma smallSlice_nonneg (n u : ℕ) : 0 ≤ smallSlice n u := by unfold smallSlice; split_ifs; exact slice_nonneg _ _; rfl

lemma slice_bound (n u : ℕ) (K : ℝ) (hK : 0 < K)
    (hk : ∀ p : NShape n, defect p = u → K ≤ degree p) :
    slice n u ≤ (2 : ℝ)^(u+1) / K := by
  have hI (p : {p : NShape n // defect p = u}) : inverseFirst p.val ≤ K⁻¹ := by
    exact inv_anti₀ hK (hk p.val p.property)
  calc
    _ ≤ ∑ _ : {p : NShape n // defect p = u}, K⁻¹ := Finset.sum_le_sum (fun p _ => hI p)
    _ = (Fintype.card {p : NShape n // defect p = u} : ℝ) * K⁻¹ := by simp
    _ ≤ (2 : ℝ)^(u+1) * K⁻¹ := mul_le_mul_of_nonneg_right (by exact_mod_cast defect_card_bound n u) (by positivity)
    _ = _ := rfl

lemma smallSlice_bound (n u : ℕ) : smallSlice n u ≤ 2 * (2 / 3 : ℝ)^u := by
  unfold smallSlice
  split_ifs with h
  · have hk : ∀ p : NShape n, defect p = u → (3 : ℝ)^u ≤ degree p := by
      intro p hp
      have hh := small_defect_degree p (by rw [hp]; exact h.2)
      rw [hp] at hh
      exact_mod_cast hh
    have hh := slice_bound n u (3^u) (by positivity) hk
    have he : (2 : ℝ)^(u+1) / 3^u = 2 * (2/3 :ℝ)^u := by
      rw [pow_succ, div_pow]
      ring
    exact hh.trans_eq he
  · positivity

lemma smallSlice_tendsto (u : ℕ) : Tendsto (fun n => smallSlice n u) atTop (𝓝 0) := by
  by_cases hu : 0 < u
  · have ht : Tendsto (fun n : ℕ => ((n - 2*u + 1 : ℕ) : ℝ)) atTop atTop := by
      exact (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        ((tendsto_add_atTop_nat 1).comp (tendsto_sub_atTop_nat (2*u)))
    have hi : Tendsto (fun n : ℕ => (((n - 2*u + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ht
    have he := hi.const_mul ((2 : ℝ)^(u+1))
    rw [mul_zero] at he
    apply squeeze_zero' (Eventually.of_forall (fun n => smallSlice_nonneg n u)) _ he
    filter_upwards [eventually_ge_atTop (4*u)] with n hn
    rw [smallSlice, ite_eq_left ⟨hu, hn⟩]
    exact slice_bound n u _ (by positivity) (fun p hp => by
      have hh := fixed_defect_degree p (by rwa [hp]) (by rw [hp]; omega)
      rw [hp] at hh
      exact_mod_cast hh)
  · simp only [smallSlice, hu, false_and, ↓reduceIte]
    exact tendsto_const_nhds

lemma smallSum_tendsto : Tendsto (fun n => ∑' u, smallSlice n u) atTop (𝓝 0) := by
  have hs : Summable (fun u : ℕ => 2 * (2/3 : ℝ)^u) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(2/3 : ℝ)‖ < 1)).mul_left 2
  have h := tendsto_tsum_of_dominated_convergence hs smallSlice_tendsto
    (Eventually.of_forall (fun n u => by rw [Real.norm_of_nonneg (smallSlice_nonneg n u)]; exact smallSlice_bound n u))
  simpa only [tsum_zero] using h

end Thorp.Current

namespace Thorp.Current
open scoped Classical
open Filter Topology Thorp.Young Thorp.Specht

lemma smallSlice_as_sum (n u : ℕ) :
    smallSlice n u = ∑ p : NShape n,
      if defect p = u ∧ 0 < defect p ∧ 4 * defect p ≤ n then inverseFirst p else 0 := by
  unfold smallSlice slice
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : NShape n => defect p = u)) (by simp), Finset.sum_filter]
  by_cases h : 0 < u ∧ 4 * u ≤ n
  · rw [ite_eq_left h]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : defect p = u
    · simp only [hp, h.1, h.2, true_and, ↓reduceIte]
    · simp only [hp, false_and, ↓reduceIte]
  · rw [ite_eq_right h]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro p _
    split_ifs with hp
    · exact (h (by simpa only [hp.1] using hp.2)).elim
    · rfl

lemma smallSlice_support (n u : ℕ) (hu : u ∉ Finset.range (n+1)) : smallSlice n u = 0 := by
  unfold smallSlice
  have hh : ¬(0 < u ∧ 4*u ≤ n) := by have := (Finset.mem_range.not.mp hu); omega
  exact ite_eq_right hh

lemma smallSum_eq (n : ℕ) :
    (∑' u, smallSlice n u) = ∑ p : NShape n,
      if 0 < defect p ∧ 4 * defect p ≤ n then inverseFirst p else 0 := by
  rw [tsum_eq_sum (smallSlice_support n)]
  simp_rw [smallSlice_as_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  have hd : defect p ∈ Finset.range (n+1) := Finset.mem_range.mpr (by have := defect_add_longest p; omega)
  have he (u : ℕ) : (if defect p = u ∧ 0 < defect p ∧ 4 * defect p ≤ n then inverseFirst p else 0) =
      if defect p = u then (if 0 < defect p ∧ 4 * defect p ≤ n then inverseFirst p else 0) else 0 := by
    split_ifs <;> tauto
  simp only [he, Finset.sum_ite_eq, hd, ↓reduceIte]

lemma bulkSum_bound (n : ℕ) (hn : 0 < n) :
    (∑ p : NShape n, if n < 4 * defect p then inverseFirst p else 0) ≤
      ((n : ℝ)+1)^(2*Nat.sqrt n) / (2:ℝ)^(n/16) := by
  have hb (p : NShape n) : (if n < 4*defect p then inverseFirst p else 0) ≤ ((2:ℝ)^(n/16))⁻¹ := by
    by_cases hp : n < 4*defect p
    · rw [ite_eq_left hp]
      have hh := bulk_degree p hn hp
      exact inv_anti₀ (by positivity) hh
    · rw [ite_eq_right hp]; positivity
  have hc : Fintype.card (NShape n) ≤ (n+1)^(2*Nat.sqrt n) := by
    rw [Fintype.card_eq_nat_card]
    change Nat.card (Nat.Partition (Fintype.card (Fin n))) ≤ _
    rw [Fintype.card_fin, ← Fintype.card_eq_nat_card]
    exact partition_count_le_sqrt_pow n
  calc
    _ ≤ ∑ _ : NShape n, ((2:ℝ)^(n/16))⁻¹ := Finset.sum_le_sum (fun p _ => hb p)
    _ = (Fintype.card (NShape n) : ℝ) * ((2:ℝ)^(n/16))⁻¹ := by simp
    _ ≤ ((n:ℝ)+1)^(2*Nat.sqrt n) * ((2:ℝ)^(n/16))⁻¹ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = _ := rfl

lemma exceptionalFirst_split (n : ℕ) : exceptionalFirst n =
    (∑' u, smallSlice n u) + (∑ p : NShape n, if n < 4 * defect p then inverseFirst p else 0) := by
  unfold exceptionalFirst
  change (∑ p : NShape n, if 0 < defect p then inverseFirst p else 0) = _
  rw [smallSum_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp_all
  all_goals omega

/-- The contribution of positive-defect Specht modules tends to zero. -/
theorem exceptionalFirst_tendsto : Tendsto exceptionalFirst atTop (𝓝 0) := by
  have hb : Tendsto (fun n => ∑ p : NShape n, if n < 4 * defect p then inverseFirst p else 0) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => Finset.sum_nonneg (fun p _ => by split_ifs; exact inverseFirst_nonneg p; rfl)))
      ((eventually_gt_atTop 0).mono (fun n hn => bulkSum_bound n hn)) Thorp.Current.partition_first_exponential_decay
  have he : exceptionalFirst = (fun n => (∑' u, smallSlice n u) + ∑ p : NShape n, if n < 4 * defect p then inverseFirst p else 0) := funext exceptionalFirst_split
  rw [he]
  simpa only [zero_add] using smallSum_tendsto.add hb

end Thorp.Current

namespace Thorp.Current
open scoped Classical
open Thorp.Specht Filter Topology

lemma full_reciprocalFirst_bound (n : ℕ) :
    reciprocalFirst n ≤ 2 + exceptionalFirst n := by
  have hzero : slice n 0 ≤ 2 := by
    have h := slice_bound n 0 1 (by norm_num)
      (fun p _ => by exact_mod_cast degree_pos p)
    norm_num at h
    exact h
  have he : reciprocalFirst n = slice n 0 + exceptionalFirst n := by
    unfold slice
    rw [← Finset.sum_subtype (Finset.univ.filter (fun p : NShape n => defect p = 0))
      (by simp), Finset.sum_filter]
    unfold exceptionalFirst reciprocalFirst
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    change inverseFirst p = _
    by_cases hp : defect p = 0
    · simp only [hp, lt_self_iff_false, ↓reduceIte, add_zero]
    · simp only [hp, Nat.pos_of_ne_zero hp, ↓reduceIte, zero_add]
      rfl
  rw [he]
  linarith

/-- Uniform first-moment bound, including the finitely many initial sizes. -/
lemma reciprocalFirst_bddAbove :
    BddAbove (Set.range (fun n : {n : ℕ // 1 ≤ n} => reciprocalFirst n.val)) := by
  obtain ⟨B, hB⟩ := exceptionalFirst_tendsto.bddAbove_range
  refine ⟨2 + B, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (full_reciprocalFirst_bound n).trans (add_le_add le_rfl (hB ⟨n.val, rfl⟩))

lemma reciprocalFirst_le_C1 (n : ℕ) (hn : 1 ≤ n) : reciprocalFirst n ≤ C1 :=
  le_csSup reciprocalFirst_bddAbove ⟨⟨n, hn⟩, rfl⟩

theorem reciprocal_degrees :
    BddAbove (Set.range (fun n : {n : ℕ // 1 ≤ n} => reciprocalFirst n.val)) ∧
    (∀ n : ℕ, 1 ≤ n → reciprocalFirst n ≤ C1) ∧
    Tendsto exceptionalFirst atTop (nhds 0) :=
  ⟨reciprocalFirst_bddAbove, reciprocalFirst_le_C1, exceptionalFirst_tendsto⟩

end Thorp.Current

end

end OAI

-- ---- from OAI.Probability.ThorpShuffle.FirstFourier ----
namespace OAI

universe uE

noncomputable section

namespace Thorp.Current
open scoped BigOperators Classical ComplexConjugate InnerProductSpace
open Thorp.Fourier

/-- The integrated operator norm bound for permutations of binary positions
under any equivalence with eight equal blocks. -/
theorem eight_block_fourier_bound
    (d : ℕ) (_hd : 3 ≤ d)
    (e : Position d ≃ Fin 8 × Fin (2 ^ (d - 3)))
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (Equiv.Perm (Position d)) E)
    [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (ν : Equiv.Perm (Position d) → ℝ)
    (hν : ∀ g, 0 ≤ ν g) (h1 : ∑ g, ν g = 1)
    (hcoset : ∀ (i : Fin 8) (g : Equiv.Perm (Position d)),
      ∑ h : Equiv.Perm (Fin (2 ^ (d - 3))),
          ν (g * Block.embedding e (Pi.mulSingle i h)) ≤
        4 * (Fintype.card (Equiv.Perm (Fin (2 ^ (d - 3)))) : ℝ) /
          Fintype.card (Equiv.Perm (Position d))) :
    ‖LinearMap.toContinuousLinearMap (Fourier.integrated ρ (fun g => (ν g : ℂ)))‖ ≤
      Real.sqrt (32 * C1) * (Module.finrank ℂ E : ℝ) ^ (-5 / 16 : ℝ) := by
  exact eight_block_of_cap (2 ^ (d - 3)) (Nat.one_le_pow _ _ (by norm_num)) ρ hu
    (Block.embedding e) ν hν h1 hcoset

end Thorp.Current

end

end OAI

-- ---- from OAI.Probability.ThorpShuffle.FirstMain ----
namespace OAI

universe uE

noncomputable section

namespace Thorp.Current
open scoped BigOperators Classical ComplexConjugate InnerProductSpace
open Filter Topology

theorem first_reciprocal_main :
    (BddAbove (Set.range (fun n : {n : ℕ // 1 ≤ n} => reciprocalFirst n.val)) ∧
    (∀ n : ℕ, 1 ≤ n → reciprocalFirst n ≤ C1) ∧
    Tendsto exceptionalFirst atTop (nhds 0)) ∧
    (∀ (d : ℕ) (_hd : 3 ≤ d)
    (e : Position d ≃ Fin 8 × Fin (2 ^ (d - 3)))
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (Equiv.Perm (Position d)) E)
    [Representation.IsIrreducible ρ]
    (_ : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (ν : Equiv.Perm (Position d) → ℝ)
    (_ : ∀ g, 0 ≤ ν g) (_ : ∑ g, ν g = 1)
    (_ : ∀ (i : Fin 8) (g : Equiv.Perm (Position d)),
      ∑ h : Equiv.Perm (Fin (2 ^ (d - 3))),
          ν (g * Block.embedding e (Pi.mulSingle i h)) ≤
        4 * (Fintype.card (Equiv.Perm (Fin (2 ^ (d - 3)))) : ℝ) /
          Fintype.card (Equiv.Perm (Position d))),
    ‖LinearMap.toContinuousLinearMap (Fourier.integrated ρ (fun g => (ν g : ℂ)))‖ ≤
      Real.sqrt (32 * C1) * (Module.finrank ℂ E : ℝ) ^ (-5 / 16 : ℝ)) := by
  exact ⟨reciprocal_degrees, eight_block_fourier_bound⟩

end Thorp.Current

end

end OAI

-- ---- mission target ----
open OAI OAI.Thorp OAI.Thorp.Current
universe uG uV uE uX uH uI uβ uα
open scoped BigOperators Classical ComplexConjugate InnerProductSpace
open Filter Topology

namespace OAI
namespace Thorp
namespace Current
theorem _root_.solution :
    (BddAbove (Set.range (fun n : {n : ℕ // 1 ≤ n} => reciprocalFirst n.val)) ∧
    (∀ n : ℕ, 1 ≤ n → reciprocalFirst n ≤ C1) ∧
    Tendsto exceptionalFirst atTop (nhds 0)) ∧
    (∀ (d : ℕ) (_hd : 3 ≤ d)
    (e : Position d ≃ Fin 8 × Fin (2 ^ (d - 3)))
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (Equiv.Perm (Position d)) E)
    [Representation.IsIrreducible ρ]
    (_ : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (ν : Equiv.Perm (Position d) → ℝ)
    (_ : ∀ g, 0 ≤ ν g) (_ : ∑ g, ν g = 1)
    (_ : ∀ (i : Fin 8) (g : Equiv.Perm (Position d)),
      ∑ h : Equiv.Perm (Fin (2 ^ (d - 3))),
          ν (g * Block.embedding e (Pi.mulSingle i h)) ≤
        4 * (Fintype.card (Equiv.Perm (Fin (2 ^ (d - 3)))) : ℝ) /
          Fintype.card (Equiv.Perm (Position d))),
    ‖LinearMap.toContinuousLinearMap (Fourier.integrated ρ (fun g => (ν g : ℂ)))‖ ≤
      Real.sqrt (32 * C1) * (Module.finrank ℂ E : ℝ) ^ (-5 / 16 : ℝ)) := by
  first
    | exact OAI.Thorp.Current.first_reciprocal_main
    | (apply OAI.Thorp.Current.first_reciprocal_main <;> assumption)
    | (intros; apply OAI.Thorp.Current.first_reciprocal_main <;> assumption)
end Current
end Thorp
end OAI
