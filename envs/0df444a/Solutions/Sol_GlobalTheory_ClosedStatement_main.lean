-- Prove2me | solution 1 for GlobalTheory.ClosedStatement.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:13:32.893912+00:00
-- url     : https://prove2.me/submissions/be3019cf-a000-4b00-aec6-dc1e8e8ac066

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsTer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedStatement
open Ideal Module
namespace GlobalTheory.ClosedStatement
theorem _root_.solution {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (m : Ideal R)
    [hm : Ideal.IsMaximal m] (hne : Ideal.map f m ≠ ⊤) :
    ∃ (ι : Type) (b : ι → A) (i₀ : ι), b i₀ = (1 : A) ∧
      (∀ x : A, ∃ a : ι →₀ R, (x - Finsupp.sum a fun (i : ι) (y : R) ↦ (f : R → A) y * b i)
        ∈ Ideal.map f m) ∧
      ∀ a : ι →₀ R, (Finsupp.sum a fun (i : ι) (y : R) ↦ (f : R → A) y * b i) ∈ Ideal.map f m →
        ∀ i : ι, (a : ι → R) i ∈ m := by
  classical
  letI : Algebra R A := f.toAlgebra
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hf : algebraMap R A = f := rfl
  rw [← hf] at hne ⊢
  haveI : Nontrivial (A ⧸ Ideal.map (algebraMap R A) m) := Ideal.Quotient.nontrivial_iff.mpr hne
  have hli : LinearIndepOn (R ⧸ m) id ({1} : Set (A ⧸ Ideal.map (algebraMap R A) m)) :=
    (linearIndepOn_singleton_iff (R ⧸ m)).mpr one_ne_zero
  let v := Basis.extend hli
  have h1mem : (1 : A ⧸ Ideal.map (algebraMap R A) m) ∈ hli.extend (Set.subset_univ _) :=
    Basis.subset_extend hli rfl
  let b : ↥(hli.extend (Set.subset_univ _)) → A := fun i =>
    if (i : A ⧸ Ideal.map (algebraMap R A) m) = 1 then 1
    else (Ideal.Quotient.mk_surjective (i : A ⧸ Ideal.map (algebraMap R A) m)).choose
  have hb : ∀ i, Ideal.Quotient.mk (Ideal.map (algebraMap R A) m) (b i) = v i := by
    intro i
    rw [Basis.coe_extend]
    simp only [b]
    split_ifs with h
    · rw [map_one, h]
    · exact (Ideal.Quotient.mk_surjective _).choose_spec
  have key : ∀ a : ↥(hli.extend (Set.subset_univ _)) →₀ R,
      Ideal.Quotient.mk (Ideal.map (algebraMap R A) m)
        (Finsupp.sum a fun i y ↦ (algebraMap R A) y * b i) =
      Finsupp.linearCombination (R ⧸ m) v (a.mapRange (Ideal.Quotient.mk m) (map_zero _)) := by
    intro a
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp), map_finsuppSum]
    refine Finsupp.sum_congr (fun i _ => ?_)
    rw [map_mul, hb, Algebra.smul_def, Ideal.Quotient.algebraMap_quotient_map_quotient]
  refine ⟨_, b, ⟨1, h1mem⟩, by simp [b], ?_, ?_⟩
  · intro x
    let g : R ⧸ m → R := fun c => if c = 0 then 0 else (Ideal.Quotient.mk_surjective c).choose
    have hg : ∀ c, Ideal.Quotient.mk m (g c) = c := by
      intro c
      simp only [g]
      split_ifs with h
      · rw [h, map_zero]
      · exact (Ideal.Quotient.mk_surjective c).choose_spec
    refine ⟨(v.repr (Ideal.Quotient.mk _ x)).mapRange g (by simp [g]), ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, key]
    have hc : ∀ c : ↥(hli.extend (Set.subset_univ _)) →₀ R ⧸ m,
        (c.mapRange g (by simp [g])).mapRange (Ideal.Quotient.mk m) (map_zero _) = c := by
      intro c; ext i; simp [hg]
    rw [hc, Basis.linearCombination_repr, sub_self]
  · intro a ha i
    rw [← Ideal.Quotient.eq_zero_iff_mem, key] at ha
    have h0 := linearIndependent_iff.mp v.linearIndependent _ ha
    have := congrArg (fun l => l i) h0
    simpa [Ideal.Quotient.eq_zero_iff_mem] using this
end GlobalTheory.ClosedStatement
