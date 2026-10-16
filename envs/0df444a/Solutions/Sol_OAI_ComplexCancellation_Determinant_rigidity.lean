-- Prove2me | solution 1 for OAI.ComplexCancellation.Determinant.rigidity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:51:18.923934+00:00
-- url     : https://prove2.me/submissions/a6790726-81ac-4825-84dc-7df35d70a4dc

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/DeterminantRigidity.lean:L250-L271
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.Determinant.rigidity. The node keeps its source
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
import Theorems.Thm_OAI_ComplexCancellation_Determinant_Euler_aux
import Theorems.Thm_OAI_ComplexCancellation_Determinant_fixed_coefficients_contradiction
import Theorems.Thm_OAI_ComplexCancellation_GradedLND_component_locallyNilpotent
import Theorems.Thm_OAI_ComplexCancellation_LND_fixed_of_square_cube

-- ---- from OAI.Algebra.AffineCancellation.Rigidity ----
namespace OAI

noncomputable section

/-! Polynomial orbit rigidity from the Mason–Stothers theorem. -/
namespace ComplexCancellation.Rigidity
open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain

variable {k : Type*} [Field k]

end ComplexCancellation.Rigidity

namespace ComplexCancellation.Rigidity

lemma ratFunc_intDegree_pow {K : Type*} [Field K] {z : RatFunc K}
    (hz : z ≠ 0) (n : ℕ) : (z ^ n).intDegree = (n : ℤ) * z.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hz) hz, ih]
    push_cast
    ring

/-- The cube of the rational parameter is not the negative of a square. -/
theorem ratFunc_X_cube_nonsquare {K : Type*} [Field K] (z : RatFunc K) :
    z ^ 2 ≠ -(RatFunc.X : RatFunc K) ^ 3 := by
  intro hz
  have hz0 : z ≠ 0 := by
    intro h
    simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_eq_neg, pow_eq_zero_iff] at hz
    exact RatFunc.X_ne_zero hz
  have he := congrArg RatFunc.intDegree hz
  rw [ratFunc_intDegree_pow hz0, RatFunc.intDegree_neg,
    ratFunc_intDegree_pow RatFunc.X_ne_zero, RatFunc.intDegree_X] at he
  omega

end ComplexCancellation.Rigidity

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

omit [GradedAlgebra G] in
lemma map_filtration {D : Derivation k R R} {j : ℤ} (hD : ShiftBound G D j)
    {r : R} {d : ℤ} (hr : r ∈ filtration G d) : D r ∈ filtration G (d+j) := by
  refine Submodule.iSup_induction (fun t : {i : ℤ // i ≤ d} => G t)
    (motive := fun r => D r ∈ filtration G (d+j)) hr ?_ ?_ ?_
  · intro i r hr
    exact filtration_mono G (by have ht := i.2; omega) (hD i r hr)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb
    rw [map_add]; exact Submodule.add_mem _ ha hb

lemma top_map {D : Derivation k R R} {j : ℤ} (hD : ShiftBound G D j)
    {r : R} {d : ℤ} (hr : r ∈ filtration G d) :
    proj G (d+j) (D r) = component G D j (proj G d r) := by
  refine Submodule.iSup_induction (fun t : {i : ℤ // i ≤ d} => G t)
    (motive := fun r => proj G (d+j) (D r) = component G D j (proj G d r))
    hr ?_ ?_ ?_
  · intro i r hr
    by_cases hi : (i : ℤ) = d
    · have hr' : r ∈ G d := hi ▸ hr
      rw [proj_of_mem G hr', component_of_mem G D j hr']
    · have hid : (i : ℤ) < d := lt_of_le_of_ne i.2 hi
      rw [proj_of_mem_ne G hr hi, map_zero]
      exact proj_filtration G (hD i r hr) (by omega)
  · simp
  · intro a b ha hb
    simp only [map_add, ha, hb]

lemma iterate_top {D : Derivation k R R} {j : ℤ} (hD : ShiftBound G D j)
    {r : R} {i : ℤ} (hr : r ∈ G i) (n : ℕ) :
    (D : R → R)^[n] r ∈ filtration G (i+n*j) ∧
    proj G (i+n*j) ((D : R → R)^[n] r) = ((component G D j : R → R)^[n] r) := by
  induction n with
  | zero => simpa using And.intro (mem_filtration G hr le_rfl) (proj_of_mem G hr)
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hn : i+(↑(n+1) : ℤ)*j = (i+n*j)+j := by push_cast; ring
    rw [hn]
    exact ⟨map_filtration G hD ih.1, (top_map G hD ih.1).trans (congrArg _ ih.2)⟩

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

-- ---- from OAI.Algebra.AffineCancellation.Determinant ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Determinant
open MvPolynomial

lemma baseEmbedding_X_zero : baseEmbedding (X 0) = RatFunc.X := by
  change algebraMap (Polynomial K₀) K
    (Polynomial.map (algebraMap Coeff K₀) ((finSuccEquiv ℂ 3) (X 0))) = _
  rw [finSuccEquiv_X_zero, Polynomial.map_X, RatFunc.algebraMap_X]

end ComplexCancellation.Determinant

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.DeterminantRigidity ----
namespace OAI

noncomputable section

namespace ComplexCancellation.Determinant
open MvPolynomial

end ComplexCancellation.Determinant

namespace ComplexCancellation.Determinant
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra

lemma aux_X (i : Fin 5) : π (X i) ∈ aux (auxWeight i) :=
  ⟨X i, isWeightedHomogeneous_X (R := ℂ) auxWeight i, rfl⟩
lemma aux_a : a ∈ aux 0 := aux_X 0
lemma aux_d : d ∈ aux 3 := aux_X 1
lemma aux_b : b ∈ aux (-3) := aux_X 2
lemma aux_u : u ∈ aux 2 := aux_X 4
lemma aux_N : d ^ 2 + a ^ 2 * u ^ 3 ∈ aux 6 := by
  have hd := SetLike.pow_mem_graded 2 aux_d
  have ha := SetLike.pow_mem_graded 2 aux_a
  have hu := SetLike.pow_mem_graded 3 aux_u
  have hi := SetLike.mul_mem_graded ha hu
  norm_num at hd hi
  exact Submodule.add_mem _ hd hi
lemma aux_a3b : a ^ 3 * b ∈ aux (-3) := by
  have ha := SetLike.pow_mem_graded 3 aux_a
  have hi := SetLike.mul_mem_graded ha aux_b
  norm_num at hi
  exact hi

lemma Euler_proj (r : T) (i : ℤ) :
    Euler (GradedLND.proj aux i r) = GradedLND.proj aux i (Euler r) := by
  induction r using DirectSum.Decomposition.inductionOn aux with
  | zero => simp
  | @homogeneous j r =>
    by_cases hji : j = i
    · subst j
      rw [GradedLND.proj_of_mem aux r.2, GradedLND.proj_of_mem aux (Euler_aux r.2)]
    · rw [GradedLND.proj_of_mem_ne aux r.2 hji,
        GradedLND.proj_of_mem_ne aux (Euler_aux r.2) hji, map_zero]
  | add r s hr hs => simp only [map_add, hr, hs]

lemma component_fiberShift {E : Derivation ℂ T T} {e : ℤ} (hE : FiberShift E e)
    (j : ℤ) : FiberShift (GradedLND.component aux E j) e := by
  intro r
  induction r using DirectSum.Decomposition.inductionOn aux with
  | zero => simp
  | @homogeneous i r =>
    rw [GradedLND.component_of_mem aux E j r.2,
      GradedLND.component_of_mem aux E j (Euler_aux r.2), Euler_proj,
      ← map_sub, hE, map_smul]
  | add r s hr hs => simp only [map_add, smul_add]; linear_combination hr + hs

lemma nonzero_base_X (i : Fin 4) : baseMap (X i) ≠ 0 := by
  intro h
  exact X_ne_zero i (baseMap_injective (h.trans (map_zero _).symm))
lemma a_ne_zero : a ≠ 0 := by simpa [baseMap, baseValues] using nonzero_base_X 1
lemma d_ne_zero : d ≠ 0 := by simpa [baseMap, baseValues] using nonzero_base_X 2
lemma u_ne_zero : u ≠ 0 := by simpa [baseMap, baseValues] using nonzero_base_X 0
lemma N_ne_zero : d ^ 2 + a ^ 2 * u ^ 3 ≠ 0 := by
  intro h
  have he : baseMap (X 2 ^ 2 + X 1 ^ 2 * X 0 ^ 3) = 0 := by
    simpa [baseMap, baseValues] using h
  have hp : (X 2 ^ 2 + X 1 ^ 2 * X 0 ^ 3 : Base) = 0 :=
    baseMap_injective (he.trans (map_zero _).symm)
  have hz := congrArg (MvPolynomial.eval (fun i : Fin 4 => if i = 2 then (1 : ℂ) else 0)) hp
  simp at hz

lemma nonsquare_u (z : K) : z ^ 2 ≠ -(embedding u) ^ 3 := by
  have he : embedding u = RatFunc.X := by
    change embedding (π (X 4)) = _
    rw [embedding_π]
    simp only [eval, aeval_X]
    change baseEmbedding (X 0) = _
    exact baseEmbedding_X_zero
  rw [he]
  exact Rigidity.ratFunc_X_cube_nonsquare z

/-- Rigidity for the determinant algebra with its fiber Euler operator. -/
theorem rigidity (E : Derivation ℂ T T) (hln : LND.LocallyNilpotent E)
    (e : ℤ) (he : e ≤ 0) (hshift : FiberShift E e) (hv : E (E v) = 0) : E = 0 := by
  by_contra hE
  obtain ⟨j, hj, hbound, htopln⟩ := GradedLND.highest aux E hE hln
  let E' := GradedLND.component aux E j
  have hN : E' (E' (d ^ 2 + a ^ 2 * u ^ 3)) = 0 := by
    have ht := (GradedLND.iterate_top aux hbound aux_N 2).2
    have hl := (GradedLND.iterate_top aux hbound aux_a3b 2).1
    have hlow : GradedLND.proj aux (6+2*j) (E (E (a^3*b))) = 0 := by
      apply GradedLND.proj_filtration aux hl
      omega
    have heq : E (E (d ^ 2 + a ^ 2 * u ^ 3)) = E (E (a^3*b)) := by
      dsimp [v] at hv
      simp only [map_sub, map_add] at hv ⊢
      linear_combination -hv
    change GradedLND.proj aux (6+2*j) (E (E (d^2+a^2*u^3))) = E' (E' _) at ht
    rw [heq, hlow] at ht
    exact ht.symm
  obtain ⟨ha, hd, hu⟩ := LND.fixed_of_square_cube E' htopln embedding embedding_injective
    a_ne_zero d_ne_zero u_ne_zero N_ne_zero hN nonsquare_u
  exact fixed_coefficients_contradiction E' hj htopln e he (component_fiberShift hshift j) ha hd hu

end ComplexCancellation.Determinant

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Determinant
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra


theorem solution : type_of% @_root_.OAI.ComplexCancellation.Determinant.rigidity := @_root_.OAI.ComplexCancellation.Determinant.rigidity
