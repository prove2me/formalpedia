-- Prove2me | solution 1 for OAI.MainGap.orthogonalSlots_of_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:24:19.282377+00:00
-- url     : https://prove2.me/submissions/bb94cf46-26d4-4b80-9c1d-6089da346bfd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/OrthogonalSlots.lean:L313-L329
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.orthogonalSlots_of_comparison. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Theorems.Thm_OAI_MainGap_RegularTransport_carrier_entryHer
import Theorems.Thm_OAI_MainGap_cornerHer_entries
import Theorems.Thm_OAI_MainGap_regularTransport_of_approx

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Comparison ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

attribute [local instance] OAI.MainGap.positivityOrder
attribute [local instance] OAI.MainGap.positivityStarOrder
lemma finiteCuntzLE_iff_closure {m n : ℕ} (d : CStarMatrix (Fin n) (Fin n) A)
    (v : CStarMatrix (Fin m) (Fin m) A) :
    FiniteCuntzLE d v ↔ d ∈ closure (Set.range
      (fun r : CStarMatrix (Fin m) (Fin n) A => r.conjTranspose * v * r)) := by
  rw [mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨_, fun j => ⟨r j, rfl⟩, hr⟩
  · rintro ⟨x, hx, ht⟩
    choose r hr using hx
    exact ⟨r, by simpa only [hr] using ht⟩

lemma FiniteCuntzLE.exists_approx {m n : ℕ} {d : CStarMatrix (Fin n) (Fin n) A}
    {v : CStarMatrix (Fin m) (Fin m) A} (h : FiniteCuntzLE d v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : CStarMatrix (Fin m) (Fin n) A, ‖d - r.conjTranspose * v * r‖ < ε := by
  rw [finiteCuntzLE_iff_closure, Metric.mem_closure_iff] at h
  obtain ⟨x, ⟨r, rfl⟩, hr⟩ := h ε hε
  exact ⟨r, by simpa only [dist_eq_norm] using hr⟩

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.OrthogonalSlots ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
open scoped CStarAlgebra
attribute [local instance] OAI.MainGap.orthogonalSlotsPartialOrder
attribute [local instance] OAI.MainGap.orthogonalSlotsStarOrderedRing
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixIsScalarTower
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixSMulCommClass
lemma cut_map {B : Type*} [NonUnitalCStarAlgebra B]
    (f : A →⋆ₙₐ[ℂ] B) (a : A) (ε : ℝ) (ha : IsSelfAdjoint a) (hε : 0 ≤ ε) :
    cut (f a) ε = f (cut a ε) :=
  (f.map_cfcₙ (q := IsSelfAdjoint) (fun t : ℝ => max (t-ε) 0) a
    (hf₀ := by simp [hε]) (ha := ha)).symm

lemma entry_mul_of_ne {n : ℕ} (i j k l : Fin n) (a b : A) (h : j ≠ k) :
    entry i j a * entry k l b = 0 :=
  Matrix.single_mul_single_of_ne a i j k h b

lemma diagonal_cut (n : ℕ) (a : A) (ε : ℝ) (ha : IsSelfAdjoint a) (hε : 0 ≤ ε) :
    cut (diagonalCorner n a) ε = diagonalCorner n (cut a ε) := by
  exact cut_map (diagonalHom n) a ε ha hε

lemma rowMatrix_conjugate {n : ℕ} (i : Fin n)
    (r : CStarMatrix (Fin 1) (Fin n) A) (v : A) :
    star (rowMatrix i r) * entry i i v * rowMatrix i r =
      r.conjTranspose * scalarCorner v * r := by
  apply CStarMatrix.ext
  intro j k
  change (∑ l : Fin n, (∑ p : Fin n,
      star (if p = i then r 0 j else 0) * (if i = p ∧ i = l then v else 0)) *
      (if l = i then r 0 k else 0)) =
    ∑ l : Fin 1, (∑ p : Fin 1, star (r p j) * v) * r l k
  simp [mul_ite]

lemma finiteCuntzLE_corner_approx {n : ℕ} (i : Fin n) {d : CStarMatrix (Fin n) (Fin n) A}
    {v : A} (hdv : FiniteCuntzLE d (scalarCorner v)) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : CStarMatrix (Fin n) (Fin n) A, ‖d - star s * entry i i v * s‖ < ε := by
  obtain ⟨r, hr⟩ := hdv.exists_approx hε
  exact ⟨rowMatrix i r, by rwa [rowMatrix_conjugate]⟩

lemma regularTransport_diagonal {n : ℕ} (i : Fin n) {d v : A} (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hdv : FiniteCuntzLE (diagonalCorner n d) (scalarCorner v)) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (RegularTransport (diagonalCorner n (cut d ε)) (entry i i v)) := by
  obtain ⟨s, hs⟩ := finiteCuntzLE_corner_approx i hdv hε
  have hd' : 0 ≤ diagonalCorner n d := map_nonneg (diagonalHom n) hd
  have hv' : 0 ≤ entry i i v := map_nonneg (cornerHom i) hv
  have ht := regularTransport_of_approx hd' hv' hε hs
  rwa [diagonal_cut n d ε (.of_nonneg hd) hε.le] at ht

namespace RegularTransport
variable {n : ℕ} {h v : A} (i₀ : Fin n)
    (T : RegularTransport (diagonalCorner n h) (entry i₀ i₀ v))

lemma slot_inner (i j : Fin n) (k l : Her h) :
    star (T.slot i₀ i k) * T.slot i₀ j l =
      if i = j then star (k : A) * (l : A) else 0 := by
  have hin := T.inner (entryHer i i₀ k) (entryHer j i₀ l)
  rw [T.carrier_entryHer i₀ i k, T.carrier_entryHer i₀ j l] at hin
  simp only [entryHer_val, star_entry, entry_mul] at hin
  change entry i₀ i₀ (star (T.slot i₀ i k) * T.slot i₀ j l) = _ at hin
  by_cases hij : i = j
  · subst j
    rw [entry_mul] at hin
    have he := congrArg (fun a : CStarMatrix (Fin n) (Fin n) A => a i₀ i₀) hin
    simpa only [entry_apply, and_self, ite_true] using he
  · rw [entry_mul_of_ne _ _ _ _ _ _ hij] at hin
    have he := congrArg (fun a : CStarMatrix (Fin n) (Fin n) A => a i₀ i₀) hin
    simpa only [entry_apply, and_self, ite_true, hij, ite_false, CStarMatrix.zero_apply] using he

lemma slot_outer_mem (i j : Fin n) (k l : Her h) :
    T.slot i₀ i k * star (T.slot i₀ j l) ∈ Her v := by
  have hout := T.outer (entryHer i i₀ k) (entryHer j i₀ l)
  have hm := T.image (entryHer i i₀ k * star (entryHer j i₀ l))
  rw [← hout, T.carrier_entryHer i₀ i k, T.carrier_entryHer i₀ j l,
    star_entry, entry_mul] at hm
  simpa only [slot, entry_apply, and_self, ite_true] using (cornerHer_entries i₀ hm i₀ i₀).1

lemma slot_mul (i : Fin n) (k l : Her h) :
    T.slot i₀ i (k*l) = T.slot i₀ i k * (l : A) := by
  have heq : entryHer i i₀ (k*l) = entryHer i i₀ k * entryHer i₀ i₀ l := by
    apply Subtype.ext
    exact (entry_mul i i₀ i₀ (k : A) (l : A)).symm
  have ht := T.mul (entryHer i i₀ k) (entryHer i₀ i₀ l)
  rw [← heq, T.carrier_entryHer i₀ i (k*l), T.carrier_entryHer i₀ i k, entryHer_val,
    entry_mul] at ht
  simpa only [slot, entry_apply, and_self, ite_true] using
    congrArg (fun a : CStarMatrix (Fin n) (Fin n) A => a i₀ i₀) ht

end RegularTransport

theorem orthogonalSlots_of_comparison {n : ℕ} {d v : A} (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hdv : FiniteCuntzLE (diagonalCorner n d) (scalarCorner v)) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (OrthogonalSlots n (cut d ε) v) := by
  by_cases hn : n = 0
  · subst n
    exact ⟨{
      carrier := fun i => Fin.elim0 i
      inner := fun i => Fin.elim0 i
      outer := fun i => Fin.elim0 i
      mul := fun i => Fin.elim0 i }⟩
  · let i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    obtain ⟨T⟩ := regularTransport_diagonal i₀ hd hv hdv hε
    exact ⟨{
      carrier := T.slotCLM i₀
      inner := T.slot_inner i₀
      outer := T.slot_outer_mem i₀
      mul := T.slot_mul i₀ }⟩

namespace OrthogonalSlots
variable {n : ℕ} {h v : A} (S : OrthogonalSlots n h v)

end OrthogonalSlots

section FiniteSum

end FiniteSum
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
open scoped CStarAlgebra
attribute [local instance] OAI.MainGap.orthogonalSlotsPartialOrder
attribute [local instance] OAI.MainGap.orthogonalSlotsStarOrderedRing
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixIsScalarTower
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixSMulCommClass


theorem solution : type_of% @_root_.OAI.MainGap.orthogonalSlots_of_comparison := @_root_.OAI.MainGap.orthogonalSlots_of_comparison
