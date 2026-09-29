-- Prove2me | solution 1 for MTT.Eigenform.exists_adic_matrix_representation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-24T16:22:16.982999+00:00
-- url     : https://prove2.me/submissions/ef79afdc-a847-45f3-bf21-1b5a8b5a45cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GaloisRep_Residual
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Definitions.Def_MTT_EigenformCoefficientCompletion
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Theorems.Thm_MTT_Eigenform_exists_continuous_localField_representation

-- From Solutions/AdicCompactDenominators.lean
section BundleAdicCompactDenominators

set_option autoImplicit false

open scoped nonZeroDivisors

namespace AdicIntegralModel

/-- A compact subset of a fraction field has a common integral denominator when the
coefficient ring is open. -/
theorem exists_denominator_of_isCompact
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [TopologicalSpace K] [IsTopologicalRing K]
    (hopen : IsOpen (Set.range (algebraMap R K)))
    {S : Set K} (hS : IsCompact S) :
    ∃ d : R, d ≠ 0 ∧ ∀ x ∈ S,
      algebraMap R K d * x ∈ Set.range (algebraMap R K) := by
  classical
  let U : R⁰ → Set K := fun d ↦ {x | algebraMap R K d * x ∈ Set.range (algebraMap R K)}
  have hU (d : R⁰) : IsOpen (U d) :=
    hopen.preimage (continuous_const.mul continuous_id)
  have hcover : S ⊆ ⋃ d, U d := by
    intro x _
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
    refine Set.mem_iUnion.mpr ⟨⟨b, hb⟩, a, ?_⟩
    dsimp
    rw [mul_div_cancel₀ _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb)]
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover U hU hcover
  refine ⟨∏ d ∈ t, (d : R), ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun d _ ↦ nonZeroDivisors.ne_zero d.property
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := Set.mem_iUnion₂.mp (ht hx)
    obtain ⟨a, ha⟩ := hdx
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun d : R⁰ ↦ (d : R)) hd
    refine ⟨c * a, ?_⟩
    rw [hc, map_mul, map_mul, ha]
    ring

/-- Finitely many continuous matrix entries on a compact parameter space have a
single nonzero denominator. -/
theorem exists_matrix_denominator_of_continuous
    {R K G n : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [TopologicalSpace K] [IsTopologicalRing K]
    [TopologicalSpace G] [CompactSpace G] [Finite n]
    (hopen : IsOpen (Set.range (algebraMap R K)))
    (ρ : G → Matrix n n K) (hρ : ∀ i j, Continuous (fun g ↦ ρ g i j)) :
    ∃ d : R, d ≠ 0 ∧ ∀ g i j,
      algebraMap R K d * ρ g i j ∈ Set.range (algebraMap R K) := by
  let S : Set K := ⋃ ij : n × n, Set.range (fun g ↦ ρ g ij.1 ij.2)
  have hS : IsCompact S := isCompact_iUnion fun ij ↦ isCompact_range (hρ ij.1 ij.2)
  obtain ⟨d, hd, h⟩ := exists_denominator_of_isCompact hopen hS
  refine ⟨d, hd, fun g i j ↦ h _ ?_⟩
  exact Set.mem_iUnion.mpr ⟨(i, j), g, rfl⟩

end AdicIntegralModel

end BundleAdicCompactDenominators

-- From Solutions/AdicStableLattice.lean
/-! # Stable lattices for bounded matrix representations

The lattice argument adapts the generic PID core of the existing Prove2Me proof of
`Matrix.exists_generalLinearGroup_forall_conj_apply_mem_adicCompletionIntegers_of_subring`
(Prove2Me author `Claude`, submission e101bfdf-6566-537e-9aa5-a5a1d286637d;
Anthropic FLT revision aa2d8b34692b16c70f699536de0d8e75b9a3e9ef).
The core requires only a matrix submonoid,
not a scalar-stable subring, and works in every finite dimension.
-/

set_option autoImplicit false
noncomputable section BundleAdicStableLattice
open scoped BigOperators

namespace AdicStableLattice

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {n : ℕ}

/-- A uniformly denominator-bounded matrix submonoid over the fraction field of a PID
preserves a full integral lattice; a lattice basis conjugates every matrix to integral entries. -/
theorem exists_isUnit_conj_integral
    (O : Submonoid (Matrix (Fin n) (Fin n) K))
    (d : R) (hd : d ≠ 0)
    (hbdd : ∀ x ∈ O, ∀ i j, ∃ r : R, algebraMap R K r = algebraMap R K d * x i j) :
    ∃ h : Matrix (Fin n) (Fin n) K, IsUnit h ∧ ∀ x ∈ O, ∀ i j, ∃ r : R,
      algebraMap R K r = (h⁻¹ * x * h) i j := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have : Module.IsTorsionFree R K := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have hdK : algebraMap R K d ≠ 0 := fun h0 ↦ hd (hinj (h0.trans (map_zero _).symm))

  let gen : Set (Fin n → K) := {y | ∃ x ∈ O, ∃ i : Fin n, y = x.mulVec (Pi.single i 1)}
  let L : Submodule R (Fin n → K) := Submodule.span R gen
  have hgenL : ∀ x ∈ O, ∀ i, x.mulVec (Pi.single i 1) ∈ L :=
    fun x hx i ↦ Submodule.subset_span ⟨x, hx, i, rfl⟩
  have heL : ∀ i : Fin n, (Pi.single i (1 : K) : Fin n → K) ∈ L := by
    intro i
    have := hgenL 1 O.one_mem i
    rwa [Matrix.one_mulVec] at this

  have hstab : ∀ x ∈ O, ∀ y ∈ L, x.mulVec y ∈ L := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x', hx', i, rfl⟩ := hy
      rw [Matrix.mulVec_mulVec]
      exact hgenL _ (O.mul_mem hx hx') i
    | zero => rw [Matrix.mulVec_zero]; exact L.zero_mem
    | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact L.add_mem hy hz
    | smul r y _ hy =>
      rw [← algebraMap_smul K r y, Matrix.mulVec_smul, algebraMap_smul]
      exact L.smul_mem r hy

  let N : Submodule R (Fin n → K) :=
    Submodule.span R (Set.range fun j : Fin n ↦
      ((algebraMap R K d)⁻¹ • Pi.single j (1 : K) : Fin n → K))
  have hLN : L ≤ N := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, i, rfl⟩
    have hcol : x.mulVec (Pi.single i 1) =
        ∑ j, x j i • (Pi.single j (1 : K) : Fin n → K) := by
      ext k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
    rw [hcol]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    obtain ⟨r, hr⟩ := hbdd x hx j i
    have : x j i • (Pi.single j (1 : K) : Fin n → K) =
        r • ((algebraMap R K d)⁻¹ • Pi.single j (1 : K)) := by
      rw [← algebraMap_smul K r, smul_smul, hr, mul_comm, ← mul_assoc,
        inv_mul_cancel₀ hdK, one_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

  have hNfg : N.FG := Submodule.fg_span (Set.finite_range _)
  have hLfg : L.FG := by
    have : IsNoetherian R N := isNoetherian_of_fg_of_noetherian _ hNfg
    have h1 : (L.comap N.subtype).FG := IsNoetherian.noetherian _
    have h2 : (L.comap N.subtype).map N.subtype = L := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hLN]
    rw [← h2]
    exact h1.map _
  have : Module.Finite R L := Module.Finite.iff_fg.mpr hLfg
  have : Module.Free R L := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex R L
  let b : Module.Basis ι R L := Module.Free.chooseBasis R L

  let col : ι → (Fin n → K) := fun i ↦ (b i : Fin n → K)

  have hli : LinearIndependent K col := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    obtain ⟨⟨s, hs⟩, hsc⟩ :=
      IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) c
    choose r hr using hsc
    have hr' : ∀ i, algebraMap R K (r i) = algebraMap R K s * c i := fun i ↦ by
      have h := hr i
      rw [Algebra.smul_def] at h
      exact h
    have hsum : (∑ i, r i • b i : L) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero]
      have : (∑ i, ((r i • b i : L) : Fin n → K)) =
          (algebraMap R K s) • ∑ i, c i • col i := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Submodule.coe_smul, ← algebraMap_smul K (r i), hr' i, smul_smul]
      rw [this, hc, smul_zero]
    have hri : r i = 0 := by
      have := b.linearIndependent
      rw [Fintype.linearIndependent_iff] at this
      exact this r hsum i
    have hs0 : algebraMap R K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have : algebraMap R K s * c i = 0 := by
      have h := hr' i
      rw [hri, map_zero] at h
      exact h.symm
    exact (mul_eq_zero.mp this).resolve_left hs0

  have hsp : ⊤ ≤ Submodule.span K (Set.range col) := by
    have hLle : ∀ y ∈ L, y ∈ Submodule.span K (Set.range col) := by
      intro y hy
      have : y = ∑ i, (b.repr ⟨y, hy⟩ i) • col i := by
        have h := congrArg (fun z : L ↦ (z : Fin n → K)) (b.sum_repr ⟨y, hy⟩).symm
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h
        exact h
      rw [this]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      rw [← algebraMap_smul K]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply]
    exact hLle _ (heL j)
  let B : Module.Basis ι K (Fin n → K) := Module.Basis.mk hli hsp
  have hcard : Fintype.card ι = n := by
    have := Module.finrank_eq_card_basis B
    rw [Module.finrank_fin_fun] at this
    exact this.symm
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard

  let h : Matrix (Fin n) (Fin n) K := Matrix.of fun i j ↦ col (e.symm j) i
  have hcols : LinearIndependent K (fun j ↦ h.transpose j) := by
    have : (fun j ↦ h.transpose j) = col ∘ e.symm := by
      funext j; ext i; rfl
    rw [this]
    exact hli.comp _ e.symm.injective
  have hU : IsUnit h := Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  refine ⟨h, hU, fun x hx i j ↦ ?_⟩

  let C : Matrix (Fin n) (Fin n) R := Matrix.of fun k j ↦
    b.repr ⟨x.mulVec (col (e.symm j)), hstab x hx _ (b (e.symm j)).2⟩ (e.symm k)
  have hxh : x * h = h * C.map (algebraMap R K) := by
    ext i' j'
    have hrepr := congrArg (fun z : L ↦ (z : Fin n → K) i')
      (b.sum_repr ⟨x.mulVec (col (e.symm j')), hstab x hx _ (b (e.symm j')).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply] at hrepr

    have hl : (x * h) i' j' = (x.mulVec (col (e.symm j'))) i' := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, h]
    rw [hl, ← hrepr, Matrix.mul_apply]
    rw [← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [Matrix.map_apply, h, C, Matrix.of_apply, Algebra.smul_def]
    ring
  refine ⟨C i j, ?_⟩
  rw [Matrix.mul_assoc, hxh, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU),
    Matrix.one_mul, Matrix.map_apply]

/-- A representation with one common denominator is conjugate to an integral representation. -/
theorem exists_isUnit_conj_integral_representation
    {G : Type*} [Monoid G] (ρ : G →* Matrix (Fin n) (Fin n) K)
    (d : R) (hd : d ≠ 0)
    (hbdd : ∀ g i j, ∃ r : R, algebraMap R K r = algebraMap R K d * ρ g i j) :
    ∃ h : Matrix (Fin n) (Fin n) K, IsUnit h ∧
      ∀ g i j, ∃ r : R, algebraMap R K r = (h⁻¹ * ρ g * h) i j := by
  obtain ⟨h, hh, hint⟩ := exists_isUnit_conj_integral (MonoidHom.mrange ρ) d hd (by
    rintro x ⟨g, rfl⟩ i j
    exact hbdd g i j)
  exact ⟨h, hh, fun g i j ↦ hint (ρ g) ⟨g, rfl⟩ i j⟩

end AdicStableLattice

end BundleAdicStableLattice

-- From Solutions/AdicIntegralModel.lean
set_option autoImplicit false
noncomputable section BundleAdicIntegralModel

namespace AdicIntegralModel

/-- A continuous representation over a fraction field with open integral subring has
an integral conjugate. Compactness bounds denominators and the PID lattice argument
supplies a basis; the coefficient injection determines the integral homomorphism. -/
theorem exists_integral_conjugate
    {R K G : Type*} {n : ℕ} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [TopologicalSpace K] [IsTopologicalRing K]
    [Monoid G] [TopologicalSpace G] [CompactSpace G]
    (hopen : IsOpen (Set.range (algebraMap R K)))
    (ρ : G →* Matrix (Fin n) (Fin n) K) (hρ : Continuous ρ) :
    ∃ ρR : G →* Matrix (Fin n) (Fin n) R,
      ∃ h : Matrix (Fin n) (Fin n) K, IsUnit h ∧
        (∀ g, (algebraMap R K).mapMatrix (ρR g) = h⁻¹ * ρ g * h) ∧
        (∀ i j, Continuous (fun g ↦ algebraMap R K (ρR g i j))) := by
  classical
  have hentries : ∀ i j, Continuous (fun g ↦ ρ g i j) :=
    fun i j ↦ (continuous_apply j).comp ((continuous_apply i).comp hρ)
  obtain ⟨d, hd, hbdd⟩ := exists_matrix_denominator_of_continuous hopen ρ hentries
  obtain ⟨h, hh, hint⟩ :=
    AdicStableLattice.exists_isUnit_conj_integral_representation ρ d hd hbdd
  choose F hF using hint
  let A : G → Matrix (Fin n) (Fin n) R := fun g ↦ Matrix.of (F g)
  have hmap (g : G) : (algebraMap R K).mapMatrix (A g) = h⁻¹ * ρ g * h := by
    ext i j
    exact hF g i j
  have hinj : Function.Injective ((algebraMap R K).mapMatrix (m := Fin n)) := by
    intro A B hAB
    ext i j
    exact IsFractionRing.injective R K (congr_fun (congr_fun hAB i) j)
  have hdet : IsUnit h.det := (Matrix.isUnit_iff_isUnit_det _).mp hh
  have hinv : h⁻¹ * h = 1 := Matrix.nonsing_inv_mul _ hdet
  have hmul : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  let ρR : G →* Matrix (Fin n) (Fin n) R :=
    { toFun := A
      map_one' := by
        apply hinj
        rw [hmap, map_one, map_one, Matrix.mul_one, hinv]
      map_mul' := fun g g' ↦ by
        apply hinj
        rw [hmap, map_mul, map_mul, hmap, hmap]
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc h h⁻¹, hmul, Matrix.one_mul] }
  refine ⟨ρR, h, hh, hmap, ?_⟩
  have hc : Continuous (fun g ↦ h⁻¹ * ρ g * h) :=
    (continuous_const.mul hρ).mul continuous_const
  intro i j
  have heq : (fun g ↦ algebraMap R K (ρR g i j)) =
      (fun g ↦ (h⁻¹ * ρ g * h) i j) := by
    funext g
    exact hF g i j
  rw [heq]
  exact (continuous_apply j).comp ((continuous_apply i).comp hc)

end AdicIntegralModel

end BundleAdicIntegralModel

-- From Solutions/AdicFiniteContinuity.lean
/-! Elementary continuity-to-finite-level bridges for absolute Galois representations.
The proof uses the finite-field neighborhood basis of the Krull topology. -/

set_option autoImplicit false
noncomputable section BundleAdicFiniteContinuity

open scoped Topology

namespace GaloisFactorsThroughFiniteLevel

/-- A homomorphism whose identity fiber is a neighborhood factors through a finite level. -/
theorem of_one_fiber_mem_nhds
    {M : Type} [MulOneClass M]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M)
    (hρ : ρ ⁻¹' {1} ∈ 𝓝 1) : GaloisFactorsThroughFiniteLevel ρ := by
  obtain ⟨L, hL, hsub⟩ :=
    (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) _).mp hρ
  exact ⟨L, hL, fun σ hσ ↦ hsub ((L.mem_fixingSubgroup_iff σ).mpr hσ)⟩

/-- A continuous homomorphism to a discrete monoid factors through a finite level.
Neither finiteness nor a topological multiplication hypothesis on the target is needed. -/
theorem of_continuous
    {M : Type} [MulOneClass M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M)
    (hρ : Continuous ρ) : GaloisFactorsThroughFiniteLevel ρ := by
  apply of_one_fiber_mem_nhds ρ
  exact ((isOpen_discrete ({1} : Set M)).preimage hρ).mem_nhds (by simp)

/-- Entrywise continuity suffices for a matrix representation with discrete coefficients. -/
theorem of_continuous_matrix_entries
    {R : Type} [Semiring R] [TopologicalSpace R] [DiscreteTopology R]
    {d : Type} [Fintype d] [DecidableEq d]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix d d R)
    (hρ : ∀ i j, Continuous (fun σ ↦ ρ σ i j)) : GaloisFactorsThroughFiniteLevel ρ := by
  exact of_continuous ρ (continuous_pi fun i ↦ continuous_pi fun j ↦ hρ i j)

/-- Entrywise continuity after a coefficient map gives finite-level factorization. -/
theorem mapMatrix_of_continuous_entries
    {R A : Type} [Semiring R] [Semiring A] [TopologicalSpace A] [DiscreteTopology A]
    {d : Type} [Fintype d] [DecidableEq d]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix d d R)
    (φ : R →+* A) (hρ : ∀ i j, Continuous (fun σ ↦ φ (ρ σ i j))) :
    GaloisFactorsThroughFiniteLevel ((φ.mapMatrix (m := d)).toMonoidHom.comp ρ) := by
  exact of_continuous_matrix_entries _ hρ

/-- A nonzero principal ideal in the coefficient-map kernel gives finite-level
factorization when the coefficient ring is an open subring of a topological field.
The codomain of the coefficient map requires neither topology nor finiteness. -/
theorem mapMatrix_of_continuous_open_embedding
    {R K A : Type} [CommRing R] [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [CommRing A] {d : Type} [Fintype d] [DecidableEq d]
    (i : R →+* K) (hi : Function.Injective i) (hopen : IsOpen (Set.range i))
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix d d R)
    (hρ : ∀ r c, Continuous (fun σ ↦ i (ρ σ r c)))
    (φ : R →+* A) (hker : ∃ a : R, a ≠ 0 ∧ φ a = 0) :
    GaloisFactorsThroughFiniteLevel ((φ.mapMatrix (m := d)).toMonoidHom.comp ρ) := by
  obtain ⟨a, ha, hφa⟩ := hker
  have hia : i a ≠ 0 := (map_ne_zero_iff i hi).mpr ha
  let V : Set K := (fun x : K ↦ i a * x) '' Set.range i
  have hV : IsOpen V := (Homeomorph.mulLeft₀ (i a) hia).isOpenMap _ hopen
  have hzero : (0 : K) ∈ V := ⟨0, ⟨0, map_zero i⟩, mul_zero _⟩
  let U : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    ⋂ r, ⋂ c, (fun σ ↦ i (ρ σ r c) - i ((1 : Matrix d d R) r c)) ⁻¹' V
  have hU : IsOpen U :=
    isOpen_iInter_of_finite fun r ↦ isOpen_iInter_of_finite fun c ↦
      hV.preimage ((hρ r c).sub continuous_const)
  have hone : (1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ U := by
    apply Set.mem_iInter.mpr
    intro r
    apply Set.mem_iInter.mpr
    intro c
    simpa only [Set.mem_preimage, map_one, sub_self] using hzero
  obtain ⟨L, hL, hsub⟩ :=
    (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) U).mp (hU.mem_nhds hone)
  refine ⟨L, hL, fun σ hσ ↦ ?_⟩
  have hσU := hsub ((L.mem_fixingSubgroup_iff σ).mpr hσ)
  change φ.mapMatrix (ρ σ) = 1
  rw [← map_one φ.mapMatrix]
  ext r c
  change φ (ρ σ r c) = φ ((1 : Matrix d d R) r c)
  have hentry := Set.mem_iInter.mp (Set.mem_iInter.mp hσU r) c
  obtain ⟨x, ⟨b, rfl⟩, hb⟩ := hentry
  have hdiff : ρ σ r c - (1 : Matrix d d R) r c = a * b := by
    apply hi
    simpa only [map_sub, map_mul] using hb.symm
  apply sub_eq_zero.mp
  rw [← map_sub, hdiff, map_mul, hφa, zero_mul]

end GaloisFactorsThroughFiniteLevel

end BundleAdicFiniteContinuity

-- From Solutions/AdicFieldTopology.lean
/-! The fraction-field realization of a DVR is an open subring for its adic valuation. -/

set_option autoImplicit false
noncomputable section BundleAdicFieldTopology

open scoped WithZero

namespace IsDiscreteValuationRing

/-- A DVR has open image in its fraction field equipped with its maximal-ideal valuation. -/
theorem isOpen_range_algebraMap_of_valued
    (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Valued K ℤᵐ⁰]
    (hval : (Valued.v : Valuation K ℤᵐ⁰) = (maximalIdeal R).valuation K) :
    IsOpen (Set.range (algebraMap R K)) := by
  have hrange : Set.range (algebraMap R K) =
      (((maximalIdeal R).valuation K).valuationSubring : Set K) := by
    have h := congrArg (fun S : Subring K ↦ (S : Set K))
      (map_algebraMap_eq_valuationSubring (A := R) (K := K))
    have h' : Set.range (algebraMap R K) =
        (((maximalIdeal R).valuation K).valuationSubring.toSubring : Set K) := by
      simpa only [Subring.coe_map, Subring.coe_top, Set.image_univ] using h
    exact h'.trans (by ext x; exact ValuationSubring.mem_toSubring _ x)
  rw [hrange, ← hval]
  exact Valued.isOpen_valuationSubring K

end IsDiscreteValuationRing

/-- Compactness for the exact absolute Galois group, resolving its rational-algebra instance. -/
theorem AlgebraicClosure.compactSpace_rat_galoisGroup :
    CompactSpace (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := by
  have : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  have : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩
  infer_instance

end BundleAdicFieldTopology

-- From Solutions/ResidualEigenformBridge.lean
set_option autoImplicit false
noncomputable section BundleResidualEigenformBridge

open NumberField

namespace MTT.Eigenform

/-- The canonical coefficient residue field has the expected residue characteristic. -/
theorem coefficientResidueField_charP
    {N k p : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    CharP (f.coefficientResidueField ιp) p := by
  let : Field (f.coefficientResidueField ιp) := f.coefficientResidueFieldField hN hk ιp
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  change Ideal.Quotient.mk (f.coefficientPrime ιp) (p : 𝓞 f.coefficientField) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (f.p_mem_coefficientPrime ιp)

/-- The coefficient ring embeds in its integral completion. -/
theorem coefficientCompletion_algebraMap_injective
    {N k p : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    Function.Injective (algebraMap (𝓞 f.coefficientField) (f.coefficientCompletion ιp)) := by
  let : NumberField f.coefficientField := MTT.numberField_coefficientField hN hk ι f
  let : IsHausdorff (f.coefficientPrime ιp) (𝓞 f.coefficientField) :=
    IsHausdorff.of_isDomain (f.coefficientPrime ιp) (f.coefficientPrime_isMaximal hN hk ιp).ne_top
  exact AdicCompletion.of_injective (f.coefficientPrime ιp) (𝓞 f.coefficientField)

/-- The canonical integral completion has characteristic zero. -/
theorem coefficientCompletion_charZero
    {N k p : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    CharZero (f.coefficientCompletion ιp) :=
  charZero_of_injective_algebraMap (f.coefficientCompletion_algebraMap_injective hN hk ιp)

end MTT.Eigenform

end BundleResidualEigenformBridge

-- From Solutions/AdicRepresentationSolution.lean
set_option autoImplicit false
noncomputable section BundleAdicRepresentationSolution

open NumberField

/-- Deligne's representation on a stable integral lattice at the chosen coefficient prime. -/
theorem solution
    {N k p : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (ιp : MTT.Qbar →+* ℂ_[p]) :
    ∃ ρ : (MTT.Qbar ≃ₐ[ℚ] MTT.Qbar) →*
        Matrix (Fin 2) (Fin 2) (f.coefficientCompletion ιp),
      (∀ n : ℕ, GaloisFactorsThroughFiniteLevel
        (((AdicCompletion.evalₐ (f.coefficientPrime ιp) n).toRingHom.mapMatrix
          (m := Fin 2)).toMonoidHom.comp ρ)) ∧
      (∀ (l : ℕ), l.Prime → Nat.Coprime l (N * p) →
        ∀ A : ValuationSubring MTT.Qbar, A.LiesOverPrime l →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
      (∀ (l : ℕ), l.Prime → Nat.Coprime l (N * p) →
        ∀ A : ValuationSubring MTT.Qbar, A.LiesOverPrime l →
          ∀ σ : MTT.Qbar ≃ₐ[ℚ] MTT.Qbar, A.IsFrobeniusAt σ l →
            Matrix.trace (ρ σ) =
              algebraMap (𝓞 f.coefficientField) (f.coefficientCompletion ιp)
                (f.integralCoeff hN hk l) ∧
            Matrix.det (ρ σ) =
              algebraMap (𝓞 f.coefficientField) (f.coefficientCompletion ιp)
                (f.integralNebentype (l : ZMod N) *
                  (l : 𝓞 f.coefficientField) ^ (k - 1)))  := by
  let R := f.coefficientCompletion ιp
  let K := f.coefficientLocalField ιp
  let := f.coefficientCompletion_isDomain hN hk ιp
  let := f.coefficientCompletion_isDiscreteValuationRing hN hk ιp
  let := f.coefficientLocalFieldValued ιp
  let := f.coefficientCompletion_charZero hN hk ιp
  have : CompactSpace (MTT.Qbar ≃ₐ[ℚ] MTT.Qbar) :=
    AlgebraicClosure.compactSpace_rat_galoisGroup
  have hopen : IsOpen (Set.range (algebraMap R K)) :=
    IsDiscreteValuationRing.isOpen_range_algebraMap_of_valued R K rfl
  obtain ⟨ρ, hρ, hram, hfrob⟩ :=
    f.exists_continuous_localField_representation hN hk ι ιp
  obtain ⟨ρR, h, hh, hmap, hcont⟩ :=
    AdicIntegralModel.exists_integral_conjugate hopen ρ hρ
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hinjM : Function.Injective ((algebraMap R K).mapMatrix (m := Fin 2)) := by
    intro A B hAB
    exact Matrix.ext fun i j ↦ hinj (congr_fun (congr_fun hAB i) j)
  refine ⟨ρR, ?_, ?_, ?_⟩
  · intro n
    apply GaloisFactorsThroughFiniteLevel.mapMatrix_of_continuous_open_embedding
      (algebraMap R K) hinj hopen ρR hcont
    refine ⟨(p : R) ^ n, pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero), ?_⟩
    have hp := Ideal.pow_mem_pow (f.p_mem_coefficientPrime ιp) n
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hp
    change (AdicCompletion.evalₐ (f.coefficientPrime ιp) n)
      ((p : f.coefficientCompletion ιp) ^ n) = 0
    rw [map_pow, map_natCast]
    simpa only [map_pow, map_natCast] using hz
  · intro l hl hlNp A hA σ hσ
    apply hinjM
    rw [hmap, hram l hl hlNp A hA σ hσ, map_one, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hh)]
  · intro l hl hlNp A hA σ hσ
    obtain ⟨htrace, hdet⟩ := hfrob l hl hlNp A hA σ hσ
    constructor
    · apply hinj
      calc
        algebraMap R K (Matrix.trace (ρR σ)) =
            Matrix.trace ((algebraMap R K).mapMatrix (ρR σ)) :=
          AddMonoidHom.map_trace (algebraMap R K) _
        _ = Matrix.trace (ρ σ) := by rw [hmap, Matrix.trace_conj' hh]
        _ = _ := htrace
    · apply hinj
      calc
        algebraMap R K (Matrix.det (ρR σ)) =
            Matrix.det ((algebraMap R K).mapMatrix (ρR σ)) :=
          RingHom.map_det (algebraMap R K) _
        _ = Matrix.det (ρ σ) := by rw [hmap, Matrix.det_conj' hh]
        _ = _ := hdet

end BundleAdicRepresentationSolution
