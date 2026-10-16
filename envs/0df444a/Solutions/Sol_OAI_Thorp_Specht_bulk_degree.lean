-- Prove2me | solution 1 for OAI.Thorp.Specht.bulk_degree
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:12:29.429904+00:00
-- url     : https://prove2.me/submissions/da648fc4-4451-4976-87cb-3ea0adebcccc

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/DegreeBounds.lean:L203-L217
-- (upload_full_project.md Phase 4): solution for node OAI.Thorp.Specht.bulk_degree. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_Thorp_Young_choose_row_le_extensions
import Theorems.Thm_OAI_Thorp_Young_extensions_card_ideal

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

omit [PartialOrder A] in

lemma labelByKey (k : A → ℕ) (hk : Function.Injective k) :
    ∃ e : A ≃ Fin (Fintype.card A), ∀ x y, e x < e y ↔ k x < k y := by
  let e : A ≃ Set.range k := Equiv.ofInjective k hk
  let : Fintype (Set.range k) := Fintype.ofEquiv A e
  let o := (Fintype.orderIsoFinOfCardEq (Set.range k) (Fintype.card_congr e.symm)).symm
  exact ⟨e.trans o.toEquiv, fun x y => o.lt_iff_lt⟩

omit [PartialOrder A] in

lemma labelByRank (r : A → ℕ) :
    ∃ e : A ≃ Fin (Fintype.card A), ∀ x y, r x < r y → e x < e y := by
  let b := Fintype.equivFin A
  let k (x : A) := r x * (Fintype.card A + 1) + (b x).val
  have hk : Function.Injective k := by
    intro x y h
    have hx := (b x).isLt
    have hy := (b y).isLt
    have hr : r x = r y := by
      change r x * (Fintype.card A + 1) + (b x).val = r y * (Fintype.card A + 1) + (b y).val at h
      nlinarith
    apply b.injective
    apply Fin.ext
    change r x * (Fintype.card A + 1) + (b x).val = r y * (Fintype.card A + 1) + (b y).val at h
    rw [hr] at h
    omega
  obtain ⟨e, he⟩ := labelByKey A k hk
  refine ⟨e, fun x y hxy => (he x y).mpr ?_⟩
  dsimp [k]
  have hx := (b x).isLt
  nlinarith

lemma fiberPerm_le_extensions (r : A → ℕ) (hr : StrictMono r) :
    Fintype.card (Thorp.Specht.fiberGroup r) ≤ Fintype.card (Extensions A) := by
  obtain ⟨e, he⟩ := labelByRank A r
  let F (g : Thorp.Specht.fiberGroup r) : Extensions A := ⟨g.val.trans e, by
    intro x y hxy
    apply he
    rw [g.property x, g.property y]
    exact hr hxy⟩
  apply Fintype.card_le_of_injective F
  intro g h hgh
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply e.injective
  exact congrArg (fun z : Extensions A => z.val x) hgh

end Thorp.Young

namespace Thorp.Specht
open scoped Classical
variable {α : Type uα} [Fintype α]

lemma tabloid_card_mul (r : α → ℕ) :
    Fintype.card (Tabloid r) * Fintype.card (fiberGroup r) = (Fintype.card α).factorial := by
  let G := Equiv.Perm α
  let b := baseTabloid r
  let e : MulAction.orbit G b ≃ Tabloid r := {
    toFun := Subtype.val
    invFun := fun f => ⟨f, by
      obtain ⟨g, hg⟩ := f.property
      refine ⟨g⁻¹, ?_⟩
      apply Subtype.ext
      funext x
      change r ((g⁻¹ : Equiv.Perm α)⁻¹ x) = f.val x
      rw [inv_inv]
      exact (congrFun hg x).symm⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let u : MulAction.stabilizer G b ≃ fiberGroup r := {
    toFun := fun g => ⟨g.val, (stabilizes_tabloid_iff r g.val b).mp g.property⟩
    invFun := fun g => ⟨g.val, (stabilizes_tabloid_iff r g.val b).mpr g.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [← Fintype.card_congr e, ← Fintype.card_congr u,
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group, Fintype.card_perm]

lemma tabloid_card_le (r : α → ℕ) (m : ℕ) (hr : ∀ x, r x < m) :
    Fintype.card (Tabloid r) ≤ m ^ Fintype.card α := by
  have hb (f : Tabloid r) (x : α) : f.val x < m := by
    obtain ⟨g, hg⟩ := f.property
    rw [hg]
    exact hr (g x)
  let F (f : Tabloid r) : α → Fin m := fun x => ⟨f.val x, hb f x⟩
  have hi : Function.Injective F := by
    intro f h hfh
    apply Subtype.ext
    funext x
    exact congrArg Fin.val (congrFun hfh x)
  have hh := Fintype.card_le_of_injective F hi
  simpa only [Fintype.card_fun, Fintype.card_fin] using hh

end Thorp.Specht

namespace Thorp.Young
open scoped Classical
variable (A : Type uA) [Fintype A] [PartialOrder A]

theorem rank_extension_bound (r : A → ℕ) (hr : StrictMono r) (m : ℕ) (hm : ∀ x, r x < m) :
    (Fintype.card A).factorial ≤ m ^ Fintype.card A * Fintype.card (Extensions A) := by
  rw [← Thorp.Specht.tabloid_card_mul r]
  exact Nat.mul_le_mul (Thorp.Specht.tabloid_card_le r m hm) (fiberPerm_le_extensions A r hr)

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

lemma rank_strictMono (D : YoungDiagram) : StrictMono (fun x : Cells D => x.val.1 + x.val.2) := by
  intro x y hxy
  have hle := hxy.le
  have hn : x.val ≠ y.val := fun h => hxy.ne (Subtype.ext h)
  have he : x.val.1 ≠ y.val.1 ∨ x.val.2 ≠ y.val.2 := by
    by_contra hh
    push Not at hh
    exact hn (Prod.ext hh.1 hh.2)
  change x.val.1 + x.val.2 < y.val.1 + y.val.2
  rcases he with he | he <;> have := hle.1 <;> have := hle.2 <;> omega

lemma coord_lt_longest (D : YoungDiagram) (x : Cells D) :
    x.val.1 < longest D ∧ x.val.2 < longest D := by
  constructor
  · exact (YoungDiagram.mem_iff_lt_colLen.mp (D.up_left_mem le_rfl (Nat.zero_le _) x.property)).trans_le (le_max_right _ _)
  · exact (YoungDiagram.mem_iff_lt_rowLen.mp (D.up_left_mem (Nat.zero_le _) le_rfl x.property)).trans_le (le_max_left _ _)

theorem factorial_le_rank_degree {n : ℕ} (D : YoungDiagram) (t : Fin n ≃ Cells D) :
    n.factorial ≤ (2 * longest D) ^ n * Module.finrank ℂ (Thorp.Specht.module D t).toSubmodule := by
  have hh := rank_extension_bound (Cells D) (fun x => x.val.1 + x.val.2) (rank_strictMono D)
    (2 * longest D) (fun x => by have := coord_lt_longest D x; omega)
  have hc : Fintype.card (Cells D) = n := (Fintype.card_congr t.symm).trans (Fintype.card_fin n)
  rw [hc] at hh
  exact hh.trans (Nat.mul_le_mul_left _ (Thorp.Specht.extensions_card_le_degree D t))

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

lemma factorial_third_bound (n : ℕ) : ((n : ℝ) / 3) ^ n ≤ (n.factorial : ℝ) := by
  rcases n with _ | n
  · norm_num
  have hn : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hs : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (n + 1)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [Real.pi_gt_three]
  have he : (n + 1 : ℝ) / 3 ≤ (n + 1) / Real.exp 1 := by
    apply div_le_div_of_nonneg_left (by positivity) (Real.exp_pos 1) Real.exp_one_lt_three.le
  have hh := Stirling.le_factorial_stirling (n + 1)
  push_cast at hh
  simpa only [Nat.cast_add, Nat.cast_one] using (pow_le_pow_left₀ (by positivity) he (n+1)).trans
    ((le_mul_of_one_le_left (by positivity) hs).trans hh)

lemma small_longest_degree {n : ℕ} (p : NShape n) (hn : 0 < n)
    (hL : 8 * longest (ofPartition p) ≤ n) :
    (4 / 3 : ℝ) ^ n ≤ degree p := by
  have hf := factorial_le_rank_degree (ofPartition p) (canonicalTableau p)
  have hf' : (n.factorial : ℝ) ≤ (2 * (longest (ofPartition p) : ℝ)) ^ n * (degree p : ℝ) := by
    exact_mod_cast hf
  have he : (2 * (longest (ofPartition p) : ℝ)) ≤ (n : ℝ) / 4 := by
    have hh : (8 : ℝ) * longest (ofPartition p) ≤ n := by exact_mod_cast hL
    linarith
  have hd : (0 : ℝ) ≤ degree p := Nat.cast_nonneg _
  have hh := (factorial_third_bound n).trans (hf'.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) he n) hd))
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hid : ((n : ℝ) / 3) ^ n = ((n : ℝ) / 4) ^ n * (4 / 3 : ℝ)^n := by rw [← mul_pow]; congr 1; ring
  rw [hid] at hh
  exact le_of_mul_le_mul_left hh (pow_pos (by positivity : (0 : ℝ) < n / 4) n)

lemma bulk_degree {n : ℕ} (p : NShape n) (hn : 0 < n) (hu : n < 4 * defect p) :
    (2 : ℝ) ^ (n / 16) ≤ degree p := by
  by_cases hL : 8 * longest (ofPartition p) ≤ n
  · have hh : (2 : ℝ) ^ (n / 16) ≤ (4 / 3 : ℝ)^n := by
      have hbase : (2 : ℝ) ≤ (4 / 3 : ℝ)^16 := by norm_num
      calc
        _ ≤ ((4 / 3 : ℝ)^16)^(n/16) := pow_le_pow_left₀ (by norm_num) hbase _
        _ = (4 / 3 : ℝ)^(16 * (n/16)) := by rw [pow_mul]
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
    exact hh.trans (small_longest_degree p hn hL)
  · have hd := defect_add_longest p
    have hk : n / 16 ≤ defect p := by omega
    have hm : 2 * (n / 16) ≤ longest (ofPartition p) := by omega
    exact_mod_cast (pow_le_choose_of_mul_le 2 _ _ hm).trans
      (choose_longest_le_degree p _ hk (by omega))

end Thorp.Specht

end

end OAI

-- ---- platform node ----
open OAI OAI.Thorp OAI.Thorp.Specht
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter
open scoped Classical
open Thorp.Young


theorem solution : type_of% @_root_.OAI.Thorp.Specht.bulk_degree := @_root_.OAI.Thorp.Specht.bulk_degree
