-- Prove2me | solution 1 for OAI.ComplexCancellation.nonpolynomiality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:50:46.318848+00:00
-- url     : https://prove2.me/submissions/1dd06f1d-8c35-4e5f-a4d9-f3d056cf4e0e

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Main.lean:L9-L29
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.nonpolynomiality. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_Modification
import Definitions.Def_OAI_Algebra_AffineCancellation_Bundle
import Definitions.Def_OAI_Algebra_AffineCancellation_ModificationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Extraction
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveObstruction
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorFrame
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorInverse
import Definitions.Def_OAI_Algebra_AffineCancellation_ReplicaLift
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentEuler
import Definitions.Def_OAI_Algebra_AffineCancellation_Intertwining
import Theorems.Thm_OAI_ComplexCancellation_AffineModification_extract
import Theorems.Thm_OAI_ComplexCancellation_AffineModification_piece_even
import Theorems.Thm_OAI_ComplexCancellation_AffineModification_piece_odd
import Theorems.Thm_OAI_ComplexCancellation_Bundle_fiberEuler_homogeneous
import Theorems.Thm_OAI_ComplexCancellation_Bundle_pullback_graded
import Theorems.Thm_OAI_ComplexCancellation_Determinant_rigidity
import Theorems.Thm_OAI_ComplexCancellation_GradedLND_component_locallyNilpotent
import Theorems.Thm_OAI_ComplexCancellation_GradedMap_mvpolynomial
import Theorems.Thm_OAI_ComplexCancellation_LND_kernel_factorially_closed
import Theorems.Thm_OAI_ComplexCancellation_PolynomialTorsor_exists_equivariant_lift
import Theorems.Thm_OAI_ComplexCancellation_Rees_clear_order
import Theorems.Thm_OAI_ComplexCancellation_Rees_primitive_reduction
import Theorems.Thm_OAI_ComplexCancellation_Rees_scaled_restriction

-- ---- from OAI.Algebra.AffineCancellation.Orbit ----
namespace OAI

noncomputable section

/-! Orbit polynomials and exponentiation of locally nilpotent derivations. -/
namespace ComplexCancellation.LND
open Polynomial

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

lemma iterate_add (D : Derivation k R R) (n : ℕ) (r s : R) :
    (D : R → R)^[n] (r + s) = (D : R → R)^[n] r + (D : R → R)^[n] s := by
  simpa only [Module.End.pow_apply, Derivation.coeFn_coe] using
    (D.toLinearMap ^ n).map_add r s

end ComplexCancellation.LND

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.Kernel ----
namespace OAI

noncomputable section

namespace ComplexCancellation.LND
open Polynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R]

end ComplexCancellation.LND
namespace ComplexCancellation.LND
open Polynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R] [IsDomain R]

end ComplexCancellation.LND

namespace ComplexCancellation.LND
variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

lemma nilpotent_add (D : Derivation k R R) {r s : R}
    (hr : ∃ n, (D : R → R)^[n] r = 0) (hs : ∃ n, (D : R → R)^[n] s = 0) :
    ∃ n, (D : R → R)^[n] (r+s) = 0 := by
  obtain ⟨n, hn⟩ := hr
  obtain ⟨m, hm⟩ := hs
  refine ⟨n+m, ?_⟩
  rw [iterate_add, iterate_eq_zero_of_le D hn (Nat.le_add_right _ _),
    iterate_eq_zero_of_le D hm (Nat.le_add_left _ _), add_zero]

lemma nilpotent_mul (D : Derivation k R R) {r s : R}
    (hr : ∃ n, (D : R → R)^[n] r = 0) (hs : ∃ n, (D : R → R)^[n] s = 0) :
    ∃ n, (D : R → R)^[n] (r*s) = 0 := by
  obtain ⟨n, hn⟩ := hr
  obtain ⟨m, hm⟩ := hs
  refine ⟨n+m, ?_⟩
  rw [iterate_leibniz]
  apply Finset.sum_eq_zero
  rintro ⟨i,j⟩ hij
  have hij' : i+j = n+m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hi : n ≤ i
  · rw [iterate_eq_zero_of_le D hn hi, zero_mul, nsmul_zero]
  · rw [iterate_eq_zero_of_le D hm (by omega : m ≤ j), mul_zero, nsmul_zero]

lemma mvPolynomial_locallyNilpotent {σ : Type*}
    (D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
    (hX : ∀ i, ∃ n : ℕ, (D : _ → _)^[n] (MvPolynomial.X i) = 0) :
    LocallyNilpotent D := by
  intro r
  induction r using MvPolynomial.induction_on with
  | C c => exact ⟨1, by simp⟩
  | add r s hr hs => exact nilpotent_add D hr hs
  | mul_X r i hr => exact nilpotent_mul D hr (hX i)

end ComplexCancellation.LND

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.GradedLND ----
namespace OAI

noncomputable section

namespace ComplexCancellation.GradedLND
open DirectSum
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
variable (G : ℤ → Submodule k R) [GradedAlgebra G]

lemma proj_mem (i : ℤ) (r : R) : proj G i r ∈ G i :=
  (decompose G r i).property

lemma proj_of_mem {r : R} {i : ℤ} (hr : r ∈ G i) : proj G i r = r :=
  decompose_of_mem_same G hr

lemma proj_of_mem_ne {r : R} {i j : ℤ} (hr : r ∈ G i) (hne : i ≠ j) :
    proj G j r = 0 := decompose_of_mem_ne G hr hne

lemma component_of_mem (D : Derivation k R R) (j : ℤ) {r : R} {i : ℤ}
    (hr : r ∈ G i) : component G D j r = proj G (i+j) (D r) :=
  componentLinear_of_mem G D.toLinearMap j hr

lemma component_homogeneous (D : Derivation k R R) (j : ℤ) {r : R} {i : ℤ}
    (hr : r ∈ G i) : component G D j r ∈ G (i+j) := by
  rw [component_of_mem G D j hr]
  exact proj_mem G _ _

omit [GradedAlgebra G] in
lemma mem_filtration {r : R} {i d : ℤ} (hr : r ∈ G i) (hid : i ≤ d) :
    r ∈ filtration G d := Submodule.mem_iSup_of_mem ⟨i, hid⟩ hr

omit [GradedAlgebra G] in
lemma filtration_mono {d e : ℤ} (h : d ≤ e) : filtration G d ≤ filtration G e := by
  apply iSup_le
  intro i
  exact fun r hr => mem_filtration G hr (i.2.trans h)

lemma proj_filtration {r : R} {d i : ℤ} (hr : r ∈ filtration G d) (hdi : d < i) :
    proj G i r = 0 := by
  refine Submodule.iSup_induction (fun t : {i : ℤ // i ≤ d} => G t)
    (motive := fun r => proj G i r = 0) hr ?_ ?_ ?_
  · intro t r hr
    exact proj_of_mem_ne G hr (by have ht := t.2; omega)
  · exact map_zero _
  · intro a b ha hb
    rw [map_add, ha, hb, add_zero]

lemma exists_filtration (r : R) : ∃ d, r ∈ filtration G d := by
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | @homogeneous i r => exact ⟨i, mem_filtration G r.2 le_rfl⟩
  | add r s hr hs =>
    obtain ⟨d, hd⟩ := hr
    obtain ⟨e, he⟩ := hs
    exact ⟨max d e, Submodule.add_mem _
      (filtration_mono G (le_max_left d e) hd) (filtration_mono G (le_max_right d e) he)⟩

lemma eq_zero_of_projections {r : R} (h : ∀ i, proj G i r = 0) : r = 0 := by
  apply (DirectSum.decompose G).injective
  ext i
  simpa [proj] using h i

lemma mem_filtration_iff {r : R} {d : ℤ} :
    r ∈ filtration G d ↔ ∀ i, d < i → proj G i r = 0 := by
  constructor
  · exact fun hr i hi => proj_filtration G hr hi
  · intro h
    classical
    rw [← DirectSum.sum_support_decompose G r]
    apply Submodule.sum_mem
    intro i hi
    by_cases hid : i ≤ d
    · exact mem_filtration G (proj_mem G i r) hid
    · have hz := h i (lt_of_not_ge hid)
      change proj G i r ∈ filtration G d
      rw [hz]
      exact Submodule.zero_mem _

lemma shiftBound_of_components {D : Derivation k R R} {j : ℤ}
    (hD : ∀ e, j < e → component G D e = 0) : ShiftBound G D j := by
  intro i r hr
  apply (mem_filtration_iff G).mpr
  intro b hb
  have h := DFunLike.congr_fun (hD (b-i) (by omega)) r
  rw [component_of_mem G D (b-i) hr] at h
  simpa only [add_sub_cancel, Derivation.zero_apply] using h

lemma component_exists {D : Derivation k R R} (hD : D ≠ 0) :
    ∃ j, component G D j ≠ 0 := by
  by_contra h
  push Not at h
  apply hD
  apply Derivation.ext
  intro r
  change D r = 0
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => exact map_zero D
  | @homogeneous i r =>
    apply eq_zero_of_projections G
    intro j
    have he := DFunLike.congr_fun (h (j-i)) (r : R)
    rw [component_of_mem G D (j-i) r.2] at he
    simpa only [add_sub_cancel, Derivation.zero_apply] using he
  | add r s hr hs => rw [map_add, hr, hs, add_zero]

lemma homogeneous_generators [Algebra.FiniteType k R] :
    ∃ s : Finset R, Algebra.adjoin k (s : Set R) = ⊤ ∧
      ∀ r ∈ s, ∃ i, r ∈ G i := by
  classical
  obtain ⟨F, hF⟩ := Algebra.FiniteType.out (R := k) (A := R)
  let ι₀ := Σ (r : F), (DirectSum.decompose G r.1).support
  let v (i : ι₀) : R := (DirectSum.decompose G i.1 i.2).1
  refine ⟨Finset.univ.image v, ?_, ?_⟩
  · rw [← top_le_iff, ← hF, Algebra.adjoin_le_iff]
    intro r hr
    rw [← DirectSum.sum_support_decompose G r]
    apply sum_mem
    intro i hi
    exact Algebra.subset_adjoin (by
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      exact ⟨⟨⟨r, hr⟩, i, hi⟩, rfl⟩)
  · intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨i.2, (DirectSum.decompose G i.1 i.2).property⟩

lemma component_bounded [Algebra.FiniteType k R] (D : Derivation k R R) :
    ∃ J : ℤ, ∀ j, component G D j ≠ 0 → j ≤ J := by
  classical
  obtain ⟨s, hs, hg⟩ := homogeneous_generators G
  choose deg hdeg using fun r : s => hg r r.2
  choose bound hbound using fun r : s => exists_filtration G (D r)
  have hfinite : (Set.range (fun r : s => bound r - deg r)).Finite := Set.finite_range _
  obtain ⟨J, hJ⟩ := hfinite.bddAbove
  refine ⟨J, ?_⟩
  intro j hj
  by_contra h
  apply hj
  apply Derivation.ext_of_adjoin_eq_top (s : Set R) hs
  intro r hr
  have hbound' := hJ (Set.mem_range_self (⟨r, hr⟩ : s))
  rw [component_of_mem G D j (hdeg ⟨r, hr⟩)]
  exact proj_filtration G (hbound ⟨r, hr⟩) (by omega)

/-- Every nonzero locally nilpotent derivation of a finite type graded algebra
has a nonzero highest component, itself locally nilpotent. -/
theorem highest [Algebra.FiniteType k R] (D : Derivation k R R) (hD : D ≠ 0)
    (hln : ∀ r : R, ∃ n : ℕ, (D : R → R)^[n] r = 0) :
    ∃ j, component G D j ≠ 0 ∧ ShiftBound G D j ∧
      ∀ r : R, ∃ n : ℕ, (component G D j : R → R)^[n] r = 0 := by
  obtain ⟨j, hj, hmax⟩ := Int.exists_greatest_of_bdd
    (component_bounded G D) (component_exists G hD)
  have hb : ShiftBound G D j := shiftBound_of_components G (by
    intro e he
    by_contra h
    exact (not_le_of_gt he) (hmax e h))
  exact ⟨j, hj, hb, component_locallyNilpotent G hb hln⟩

end ComplexCancellation.GradedLND

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.ReesClearing ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial
lemma embedding_q : embedding q=T 1 := by simp [q,eval,values]
end ComplexCancellation.Rees

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.GradedMap ----
namespace OAI

noncomputable section

namespace ComplexCancellation.GradedMap
open MvPolynomial
variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]
lemma projection (G : ℤ → Submodule k R) (H : ℤ → Submodule k S)
    [GradedAlgebra G] [GradedAlgebra H] (f : R →ₐ[k] S)
    (hf : ∀ e r, r ∈ G e → f r ∈ H e) (e : ℤ) (r : R) :
    f (GradedAlgebra.proj G e r)=GradedAlgebra.proj H e (f r) := by
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => simp only [map_zero]
  | @homogeneous i r =>
    by_cases hi : i=e
    · subst i
      rw [show GradedAlgebra.proj G e (r : R)=r from DirectSum.decompose_of_mem_same G r.2,
        show GradedAlgebra.proj H e (f r)=f r from DirectSum.decompose_of_mem_same H (hf e r r.2)]
    · rw [show GradedAlgebra.proj G e (r : R)=0 from DirectSum.decompose_of_mem_ne G r.2 hi,
        show GradedAlgebra.proj H e (f r)=0 from DirectSum.decompose_of_mem_ne H (hf i r r.2) hi,map_zero]
  | add r s hr hs => simp only [map_add,hr,hs]
lemma reflect (G : ℤ → Submodule k R) (H : ℤ → Submodule k S)
    [GradedAlgebra G] [GradedAlgebra H] (f : R →ₐ[k] S)
    (hf : Function.Injective f) (hm : ∀ e r, r ∈ G e → f r ∈ H e)
    {e : ℤ} {r : R} (hr : f r ∈ H e) : r ∈ G e := by
  have he : GradedAlgebra.proj G e r=r := by
    apply hf
    rw [projection G H f hm,show GradedAlgebra.proj H e (f r)=f r from DirectSum.decompose_of_mem_same H hr]
  rw [← he]
  exact (DirectSum.decompose G r e).property
end ComplexCancellation.GradedMap

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.DegenerationGrading ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Degeneration
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
lemma X_mem (i : Fin 5) : π (X i) ∈ pieces (weight i) := ⟨X i,isWeightedHomogeneous_X ℂ weight i,rfl⟩
end ComplexCancellation.Degeneration

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.ReesGrading ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
lemma laurentMonomial_mem (r : A) (e : ℤ) : LaurentPolynomial.C r*T e ∈ laurentPieces e := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  exact AddMonoidAlgebra.single_mem_grade e r
lemma embedding_graded (e : ℤ) (b : B) (hb : b ∈ pieces e) : embedding b ∈ laurentPieces e := by
  obtain ⟨p,hp,rfl⟩ := hb
  change embedding (π p) ∈ _
  rw [embedding_π]
  apply GradedMap.mvpolynomial (k := ℂ) (R := L) laurentPieces weight eval _ hp
  intro i
  fin_cases i <;> simp only [eval,aeval_X,values,weight]
  · simpa using laurentMonomial_mem 1 1
  · exact laurentMonomial_mem _ _
  · change c (aπ (X 1)) ∈ laurentPieces 0
    have h := laurentMonomial_mem (aπ (X 1)) 0
    rw [T_zero,mul_one] at h
    exact h
  · change c (aπ (X 2)) ∈ laurentPieces 0
    have h := laurentMonomial_mem (aπ (X 2)) 0
    rw [T_zero,mul_one] at h
    exact h
  · exact laurentMonomial_mem _ _
  · exact laurentMonomial_mem _ _
lemma red_graded (e : ℤ) (b : B) (hb : b ∈ pieces e) : red b ∈ Degeneration.pieces e := by
  obtain ⟨p,hp,rfl⟩ := hb
  change red (π p) ∈ _
  rw [red_π]
  apply GradedMap.mvpolynomial Degeneration.pieces weight redEval _ hp
  intro i
  fin_cases i <;> simp only [redEval,aeval_X,redValues,weight]
  · exact (Degeneration.pieces 1).zero_mem
  · exact Degeneration.X_mem 0
  · exact Degeneration.X_mem 1
  · exact Degeneration.X_mem 2
  · exact Degeneration.X_mem 3
  · exact Degeneration.X_mem 4
lemma red_monomial_mem (s : B) (r : A) (i : ℤ) (hs : embedding s=T i*c r) :
    red s ∈ Degeneration.pieces i := by
  apply red_graded
  apply GradedMap.reflect (k := ℂ) (R := B) (S := L) pieces laurentPieces embedding embedding_injective embedding_graded
  rw [hs,mul_comm (T i : L) (c r)]
  exact laurentMonomial_mem _ _
end ComplexCancellation.Rees

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.PositiveInvariant ----
namespace OAI

noncomputable section

namespace ComplexCancellation.LND
variable {k R S : Type*} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
lemma conjugate_apply (e : R ≃ₐ[k] S) (D : Derivation k S S) (r : R) :
    conjugate e D r=e.symm (D (e r)) := rfl
lemma conjugate_iterate (e : R ≃ₐ[k] S) (D : Derivation k S S) (r : R) (n : ℕ) :
    (conjugate e D : R → R)^[n] r=e.symm ((D : S → S)^[n] (e r)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',ih,conjugate_apply,AlgEquiv.apply_symm_apply,Function.iterate_succ_apply']
lemma conjugate_ln (e : R ≃ₐ[k] S) (D : Derivation k S S) (hD : LocallyNilpotent D) :
    LocallyNilpotent (conjugate e D) := by
  intro r
  obtain ⟨n,hn⟩ := hD (e r)
  exact ⟨n,by rw [conjugate_iterate,hn,map_zero]⟩
lemma pderiv_ln {ι : Type*} (i : ι) : LocallyNilpotent (MvPolynomial.pderiv (R := k) i) := by
  classical
  apply mvPolynomial_locallyNilpotent
  intro j
  refine ⟨2,?_⟩
  simp only [Function.iterate_succ_apply',Function.iterate_zero_apply,MvPolynomial.pderiv_X]
  by_cases hij : j=i
  · subst j; simp
  · simp [hij]
end ComplexCancellation.LND

namespace ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial
lemma F_ne_zero : Degeneration.F ≠ 0 := by
  let f : Degeneration.P →ₐ[ℂ] ℂ := aeval (fun i => if i=3 then 1 else 0)
  have hf : f Degeneration.relation=0 := by
    norm_num [f,Degeneration.relation,Degeneration.xp,Fin.ext_iff]
  let g : Degeneration.G →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ _ f (by
    intro r hr
    obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
    rw [map_mul,hf,zero_mul])
  have hg : g Degeneration.F=1 := by
    change f (X 3)=1
    norm_num [f]
  intro hz
  rw [hz,map_zero] at hg
  exact zero_ne_one hg

lemma coefficient_not_mem : c (aπ (X 3)) ∉ embedding.range := by
  rintro ⟨b,hb⟩
  change embedding b=c (aπ (X 3)) at hb
  have he : π (X 4)=q^2*b := by
    apply embedding_injective
    rw [map_mul,map_pow,embedding_q,T_pow,hb,embedding_π]
    simp only [eval,aeval_X,values,Matrix.cons_val]
    change c (aπ (X 3))*T 2=T 2*c (aπ (X 3))
    exact mul_comm (c (aπ (X 3))) (T 2 : L)
  have hr := congrArg red he
  simp only [map_mul,map_pow,red_q,zero_pow (by decide : 2 ≠ 0),zero_mul] at hr
  have hF : red (π (X 4))=Degeneration.F := by simp [redEval,redValues,Matrix.cons_val]
  exact F_ne_zero (hF.symm.trans hr)
lemma positive_clear (r : A) (hr : c r ∉ embedding.range) :
    ∃ (i : ℤ) (s : B), 0 < i ∧ red s ≠ 0 ∧ embedding s=T i*c r := by
  have hcr : c r ≠ 0 := by
    intro hz
    apply hr
    rw [hz]
    exact embedding.range.zero_mem
  obtain ⟨i,s,hs,he⟩ := clear_order (c r) hcr
  refine ⟨i,s,?_,hs,he⟩
  by_contra hn
  have hi : 0 ≤ -i := by omega
  apply hr
  use q^(-i).toNat*s
  change embedding (q^(-i).toNat*s)=c r
  rw [map_mul,map_pow,embedding_q,T_pow,Int.toNat_of_nonneg hi,mul_one,he,← mul_assoc,← T_add]
  simp
lemma polynomial_bad_coordinate (e : A ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ) :
    ∃ i : Fin 4, c (e.symm (X i)) ∉ embedding.range := by
  by_contra hn
  push Not at hn
  apply coefficient_not_mem
  rw [← e.symm_apply_apply (aπ (X 3))]
  generalize e (aπ (X 3))=r
  induction r using MvPolynomial.induction_on with
  | C z =>
    have he : c (e.symm (MvPolynomial.C z))=algebraMap ℂ L z := by
      rw [MvPolynomial.C_eq_algebraMap,AlgEquiv.commutes,c.commutes]
    rw [he]
    exact embedding.range.algebraMap_mem z
  | add r s hr hs => rw [map_add,map_add]; exact add_mem hr hs
  | mul_X r i hr => rw [map_mul,map_mul]; exact mul_mem hr (hn i)
lemma bad_invariant (e : A ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ) :
    ∃ (r : A) (D : Derivation ℂ A A), c r ∉ embedding.range ∧ LND.LocallyNilpotent D ∧ D ≠ 0 ∧ D r=0 := by
  classical
  obtain ⟨i,hi⟩ := polynomial_bad_coordinate e
  obtain ⟨j,hj⟩ : ∃ j : Fin 4, j ≠ i := exists_ne i
  let D := LND.conjugate e (MvPolynomial.pderiv j)
  refine ⟨e.symm (X i),D,hi,LND.conjugate_ln e _ (LND.pderiv_ln j),?_,?_⟩
  · intro hz
    have he := DFunLike.congr_fun hz (e.symm (X j))
    have ho : D (e.symm (X j))=1 := by simp [D,LND.conjugate_apply]
    rw [ho,Derivation.zero_apply] at he
    exact one_ne_zero he
  · simp [D,LND.conjugate_apply,MvPolynomial.pderiv_X,hj]
lemma positive_invariant_of_polynomial (e : A ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ) :
    ∃ (i : ℤ) (r : Degeneration.G) (D : Derivation ℂ Degeneration.G Degeneration.G),
      0 < i ∧ r ≠ 0 ∧ r ∈ Degeneration.pieces i ∧ LND.LocallyNilpotent D ∧ D ≠ 0 ∧ D r=0 := by
  obtain ⟨r,D,hr,hD,hDn,hDr⟩ := bad_invariant e
  obtain ⟨i,s,hi,hs,he⟩ := positive_clear r hr
  obtain ⟨E,hE,hEn,hEq,hEs⟩ := scaled_restriction D hD hDn r hDr i s he
  obtain ⟨D',hD',hDn',hDr'⟩ := primitive_reduction E hE hEn hEq s hEs
  exact ⟨i,red s,D',hi,hs,red_monomial_mem s r i he,hD',hDn',hDr'⟩
end ComplexCancellation.Rees

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.Modification ----
namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable (R : Type*) [CommRing R] [IsDomain R] (v : R)

lemma isDomain (hv : v ≠ 0) : IsDomain (T R v) :=
  Function.Injective.isDomain (embedding R v) (embedding_injective R v hv)

end ComplexCancellation.AffineModification

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.ModificationGrading ----
namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable (R : Type*) [CommRing R] (v : R)
attribute [local instance] MvPolynomial.weightedGradedAlgebra
lemma degree_cases (e : ℤ) :
    (∃ n : ℕ, e=-(n+1:ℤ)) ∨ (∃ n : ℕ, e=2*(n:ℤ)) ∨ (∃ n : ℕ, e=2*(n:ℤ)+1) := by
  by_cases hn : e < 0
  · exact Or.inl ⟨(-e-1).toNat,by omega⟩
  · by_cases hm : e%2=0
    · exact Or.inr (Or.inl ⟨(e/2).toNat,by omega⟩)
    · exact Or.inr (Or.inr ⟨(e/2).toNat,by omega⟩)
lemma V_dvd_of_positive {r : T R v} {e : ℤ} (he : 0 < e) (hr : r ∈ pieces R v e) :
    V R v ∣ r := by
  rcases degree_cases e with ⟨n,hen⟩ | ⟨n,hen⟩ | ⟨n,hen⟩
  · omega
  · rw [hen] at hr
    have hn : 1 ≤ n := by omega
    obtain ⟨s,rfl⟩ := piece_even R v n hr
    exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega : n ≠ 0)) _
  · rw [hen] at hr
    obtain ⟨s,rfl⟩ := piece_odd R v n hr
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self _ (by omega : n+1 ≠ 0)) _) _
end ComplexCancellation.AffineModification

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.Extraction ----
namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]
variable (v : R) (hv : v ≠ 0)
lemma coefficient_injective : Function.Injective (algebraMap R (T R v)) := by
  apply Function.Injective.of_comp (f := embedding R v)
  intro r s he
  change embedding R v (algebraMap R (T R v) r)=embedding R v (algebraMap R (T R v) s) at he
  rw [AlgHom.commutes,AlgHom.commutes] at he
  exact ((RatFunc.C_injective).comp (IsFractionRing.injective R (F R))) he
include hv in
lemma V_nonzero : V R v ≠ 0 := by
  intro h
  have he := equation R v
  rw [h,mul_zero] at he
  exact hv ((coefficient_injective v) (he.symm.trans (map_zero _).symm))

end ComplexCancellation.AffineModification

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.HomogeneousExtraction ----
namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]
variable (v : R) (hv : v ≠ 0)
include hv

lemma fixed_V_of_positive_invariant
    (D : Derivation k (T R v) (T R v)) (hD : LND.LocallyNilpotent D)
    (w : T R v) (hw : w ≠ 0) (e : ℤ) (he : 0 < e)
    (hwg : w ∈ pieces R v e) (hDw : D w=0) : D (V R v)=0 := by
  let := isDomain R v hv
  obtain ⟨z,hz⟩ := V_dvd_of_positive R v he hwg
  have hzn : z ≠ 0 := by intro he; rw [he,mul_zero] at hz; exact hw hz
  apply (LND.kernel_factorially_closed D hD (V_nonzero v hv) hzn _).1
  rwa [← hz]
end ComplexCancellation.AffineModification

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.PositiveObstruction ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Determinant
end ComplexCancellation.Determinant
namespace ComplexCancellation.Bundle
open Determinant
/-- The positive-invariant obstruction on the pullback ring. -/
theorem no_positive_invariant
    (D : Derivation ℂ B B) (hD : LND.LocallyNilpotent D) (hDn : D ≠ 0)
    (j : ℤ) (hshift : ∀ e r, r ∈ valuationPieces e → D r ∈ valuationPieces (e+j))
    (hcomm : ∀ z, fiberEuler (D z)=D (fiberEuler z))
    (w : B) (hw : w ≠ 0) (e : ℤ) (he : 0 < e)
    (hwg : w ∈ valuationPieces e) (hDw : D w=0) : False := by
  have hV := AffineModification.fixed_V_of_positive_invariant v v_ne_zero D hD w hw e he hwg hDw
  obtain ⟨E,n,hEn,hEl,hshiftE,hEv⟩ :=
    AffineModification.extract v v_ne_zero Euler Euler_v D hD hDn j hshift hcomm hV
  apply hEn
  apply rigidity E hEl (-(n : ℤ)) (by omega) _ hEv
  intro r
  rw [hshiftE]
  simp only [Int.cast_neg,Int.cast_natCast,neg_smul,Nat.cast_smul_eq_nsmul]
end ComplexCancellation.Bundle

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.GradedCommutation ----
namespace OAI

noncomputable section

namespace ComplexCancellation.GradedLND
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
variable (G : ℤ → Submodule k R) [GradedAlgebra G]
lemma linear_projection (H : R →ₗ[k] R) (hH : ∀ i r, r ∈ G i → H r ∈ G i) (i : ℤ) (r : R) :
    H (proj G i r)=proj G i (H r) := by
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => simp only [map_zero]
  | @homogeneous j r =>
    by_cases hj : j=i
    · subst j
      rw [proj_of_mem G r.2,proj_of_mem G (hH i r r.2)]
    · rw [proj_of_mem_ne G r.2 hj,proj_of_mem_ne G (hH j r r.2) hj,map_zero]
  | add r s hr hs => simp only [map_add,hr,hs]
lemma component_commute (D H : Derivation k R R) (hH : ∀ i r, r ∈ G i → H r ∈ G i)
    (hc : ∀ r, H (D r)=D (H r)) (j : ℤ) (r : R) :
    H (component G D j r)=component G D j (H r) := by
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => simp only [map_zero]
  | @homogeneous i r =>
    rw [component_of_mem G D j r.2,component_of_mem G D j (hH i r r.2)]
    exact (linear_projection G H.toLinearMap hH (i+j) (D r)).trans (congrArg (proj G (i+j)) (hc r))
  | add r s hr hs => simp only [map_add,hr,hs]
end ComplexCancellation.GradedLND

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.Main ----
namespace OAI

noncomputable section

namespace ComplexCancellation
/-- The hypersurface algebra is not a polynomial algebra over ℂ. -/
theorem nonpolynomiality : ¬ Nonempty (A ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ) := by
  rintro ⟨e⟩
  obtain ⟨i,r,D,hi,hrn,hr,hD,hDn,hDr⟩ := Rees.positive_invariant_of_polynomial e
  obtain ⟨c,E,hcn,hE,hEn,he,hcomm⟩ := PolynomialTorsor.exists_equivariant_lift D hD hDn
  let w := Bundle.pullback r
  have hw : w ≠ 0 := by
    intro hz
    apply hrn
    exact Bundle.pullback_injective (by simpa only [map_zero] using hz)
  have hwg : w ∈ Bundle.valuationPieces i := Bundle.pullback_graded i r hr
  have hEw : E w=0 := by rw [he,hDr,mul_zero,map_zero]
  obtain ⟨j,hjn,_hb,hjln⟩ := GradedLND.highest Bundle.valuationPieces E hEn hE
  have hcw : GradedLND.component Bundle.valuationPieces E j w=0 := by
    rw [GradedLND.component_of_mem Bundle.valuationPieces E j hwg,hEw,map_zero]
  exact Bundle.no_positive_invariant (GradedLND.component Bundle.valuationPieces E j)
    hjln hjn j
    (fun _ _ hz => GradedLND.component_homogeneous Bundle.valuationPieces E j hz)
    (GradedLND.component_commute Bundle.valuationPieces E Bundle.fiberEuler
      Bundle.fiberEuler_homogeneous hcomm j)
    w hw i hi hwg hcw

end ComplexCancellation

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation


theorem solution : type_of% @_root_.OAI.ComplexCancellation.nonpolynomiality := @_root_.OAI.ComplexCancellation.nonpolynomiality
