-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_pairing_transposeInv3_of_isIrreducibleRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/79f08ab9-3137-5f56-941b-ee7c8aa8b78f

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.Group.Semiconj.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.Algebra.Ring.Commute
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.Finite.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Separation.Hausdorff
import Theorems.Thm_BrauerNesbitt_case_irreducible_irreducible
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep

set_option Elab.async false

set_option autoImplicit false

noncomputable section

section InvariantStep

namespace InvariantFunctional

open LinearMap

section Step

variable {R : Type*} [Field R]
variable {MO : Type*} [AddCommGroup MO] [Module R MO]
variable {MZ : Type*} [AddCommGroup MZ] [Module R MZ]
variable {MZ' : Type*} [AddCommGroup MZ'] [Module R MZ']
variable {ι : Type*}

private theorem comp_isInvariant_of_normalises (AZ : ι → Module.End R MZ) (TZ : Module.End R MZ)
    (hnorm : ∀ i, ∃ j, TZ ∘ₗ AZ i = AZ j ∘ₗ TZ) (φ : Module.Dual R MZ) (hφ : ∀ i, φ ∘ₗ AZ i = φ)
    (i : ι) : (φ ∘ₗ TZ) ∘ₗ AZ i = φ ∘ₗ TZ := by
  obtain ⟨j, hj⟩ := hnorm i
  rw [LinearMap.comp_assoc, hj, ← LinearMap.comp_assoc, hφ j]

private theorem eq_zero_of_eq_neg [CharZero R] (χ : Module.Dual R MZ') (h : χ = -χ) : χ = 0 := by
  refine LinearMap.ext fun m => ?_
  have hm : χ m = -χ m := by
    have := congrArg (fun f : Module.Dual R MZ' => f m) h
    simpa only [LinearMap.neg_apply] using this
  have h2 : (2 : R) * χ m = 0 := by
    rw [two_mul, add_eq_zero_iff_eq_neg]
    exact hm
  rw [LinearMap.zero_apply]
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

private theorem comp_eq_self_of_step [CharZero R] (AO : ι → Module.End R MO) (AZ : ι → Module.End R MZ)
    (AZ' : ι → Module.End R MZ') (TO : Module.End R MO) (TZ : Module.End R MZ)
    (TZ' : Module.End R MZ') (e : MO →ₗ[R] MZ) (r : MZ →ₗ[R] MZ') (hr : Function.Surjective r)
    (hex : Function.Exact e r) (heA : ∀ i, e ∘ₗ AO i = AZ i ∘ₗ e)
    (hrA : ∀ i, r ∘ₗ AZ i = AZ' i ∘ₗ r) (heT : e ∘ₗ TO = TZ ∘ₗ e) (hrT : r ∘ₗ TZ = TZ' ∘ₗ r)
    (hTT : TZ ∘ₗ TZ = LinearMap.id) (hnorm : ∀ i, ∃ j, TZ ∘ₗ AZ i = AZ j ∘ₗ TZ)
    (hO : ∀ φ : Module.Dual R MO, (∀ i, φ ∘ₗ AO i = φ) → φ ∘ₗ TO = φ)
    (hZ' : ∀ φ : Module.Dual R MZ', (∀ i, φ ∘ₗ AZ' i = φ) → φ ∘ₗ TZ' = φ)
    (φ : Module.Dual R MZ) (hφ : ∀ i, φ ∘ₗ AZ i = φ) : φ ∘ₗ TZ = φ := by

  set ψ : Module.Dual R MZ := φ - φ ∘ₗ TZ with hψ
  have hφT : ∀ i, (φ ∘ₗ TZ) ∘ₗ AZ i = φ ∘ₗ TZ := comp_isInvariant_of_normalises AZ TZ hnorm φ hφ
  have hψA : ∀ i, ψ ∘ₗ AZ i = ψ := by
    intro i
    rw [hψ, LinearMap.sub_comp, hφ i, hφT i]
  have hψT : ψ ∘ₗ TZ = -ψ := by
    rw [hψ, LinearMap.sub_comp, LinearMap.comp_assoc, hTT, LinearMap.comp_id, neg_sub]

  have hψe : ψ ∘ₗ e = 0 := by
    have hinv : ∀ i, (φ ∘ₗ e) ∘ₗ AO i = φ ∘ₗ e := by
      intro i
      rw [LinearMap.comp_assoc, heA i, ← LinearMap.comp_assoc, hφ i]
    have h := hO (φ ∘ₗ e) hinv
    rw [hψ, LinearMap.sub_comp, LinearMap.comp_assoc, ← heT, ← LinearMap.comp_assoc, h, sub_self]

  have hker : LinearMap.ker r ≤ LinearMap.ker ψ := by
    intro m hm
    rw [hex.linearMap_ker_eq, LinearMap.mem_range] at hm
    obtain ⟨o, rfl⟩ := hm
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hψe, LinearMap.zero_apply]
  set χ : Module.Dual R MZ' :=
    (LinearMap.ker r).liftQ ψ hker ∘ₗ (r.quotKerEquivOfSurjective hr).symm.toLinearMap with hχ
  have hχr : χ ∘ₗ r = ψ := by
    refine LinearMap.ext fun m => ?_
    have hsymm : (r.quotKerEquivOfSurjective hr).symm (r m) = Submodule.Quotient.mk m := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    rw [hχ, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hsymm,
      Submodule.liftQ_apply]
  have hχA : ∀ i, χ ∘ₗ AZ' i = χ := by
    intro i
    rw [← LinearMap.cancel_right hr, LinearMap.comp_assoc, ← hrA i, ← LinearMap.comp_assoc, hχr,
      hψA i]
  have hχT : χ ∘ₗ TZ' = -χ := by
    rw [← LinearMap.cancel_right hr, LinearMap.comp_assoc, ← hrT, ← LinearMap.comp_assoc,
      LinearMap.neg_comp, hχr, hψT]

  have hχ0 : χ = 0 := eq_zero_of_eq_neg χ ((hZ' χ hχA).symm.trans hχT)
  have hψ0 : ψ = 0 := by rw [← hχr, hχ0, LinearMap.zero_comp]
  rw [hψ] at hψ0
  exact (sub_eq_zero.mp hψ0).symm

private theorem comp_eq_self_of_subsingleton {M : Type*} [AddCommGroup M] [Module R M] [Subsingleton M]
    (T : Module.End R M) (φ : Module.Dual R M) : φ ∘ₗ T = φ :=
  LinearMap.ext fun m => by rw [LinearMap.comp_apply, Subsingleton.elim (T m) m]

end Step

section Coinvariants

variable {R : Type*} [Field R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {M' : Type*} [AddCommGroup M'] [Module R M']
variable {ι : Type*}

private def _root_.InvariantFunctional.coinvariants (A : ι → Module.End R M) : Submodule R M :=
  Submodule.span R {x | ∃ (i : ι) (m : M), x = A i m - m}

p2m_export "InvariantFunctional" "coinvariants"
private theorem sub_mem_coinvariants (A : ι → Module.End R M) (i : ι) (m : M) :
    A i m - m ∈ coinvariants A :=
  Submodule.subset_span ⟨i, m, rfl⟩

private theorem forall_comp_eq_iff_le_ker (A : ι → Module.End R M) (φ : Module.Dual R M) :
    (∀ i, φ ∘ₗ A i = φ) ↔ coinvariants A ≤ LinearMap.ker φ := by
  constructor
  · intro h
    rw [coinvariants, Submodule.span_le]
    rintro x ⟨i, m, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply, h i, sub_self]
  · intro h i
    refine LinearMap.ext fun m => ?_
    have hm := h (sub_mem_coinvariants A i m)
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hm
    rw [LinearMap.comp_apply]
    exact hm

private theorem mem_of_forall_dual (N : Submodule R M) (v : M)
    (h : ∀ φ : Module.Dual R M, N ≤ LinearMap.ker φ → φ v = 0) : v ∈ N := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff R (Submodule.Quotient.mk v)]
  intro φ
  have hle : N ≤ LinearMap.ker (φ ∘ₗ N.mkQ) := by
    intro n hn
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero N).mpr hn, map_zero]
  have := h (φ ∘ₗ N.mkQ) hle
  rwa [LinearMap.comp_apply, Submodule.mkQ_apply] at this

private theorem sub_mem_coinvariants_of_forall_comp_eq (A : ι → Module.End R M) (T : Module.End R M)
    (h : ∀ φ : Module.Dual R M, (∀ i, φ ∘ₗ A i = φ) → φ ∘ₗ T = φ) (m : M) :
    T m - m ∈ coinvariants A := by
  refine mem_of_forall_dual (coinvariants A) (T m - m) fun φ hφ => ?_
  have hT := h φ ((forall_comp_eq_iff_le_ker A φ).mpr hφ)
  rw [map_sub, ← LinearMap.comp_apply, hT, sub_self]

private theorem coinvariants_map_of_surjective (A : ι → Module.End R M) (A' : ι → Module.End R M')
    (r : M →ₗ[R] M') (hr : Function.Surjective r) (hrA : ∀ i, r ∘ₗ A i = A' i ∘ₗ r) :
    (coinvariants A).map r = coinvariants A' := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, coinvariants, Submodule.span_le]
    rintro x ⟨i, m, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, ← LinearMap.comp_apply, hrA i,
      LinearMap.comp_apply]
    exact sub_mem_coinvariants A' i (r m)
  · rw [coinvariants, Submodule.span_le]
    rintro x ⟨i, m', rfl⟩
    obtain ⟨m, rfl⟩ := hr m'
    rw [SetLike.mem_coe, Submodule.mem_map]
    refine ⟨A i m - m, sub_mem_coinvariants A i m, ?_⟩
    rw [map_sub, ← LinearMap.comp_apply, hrA i, LinearMap.comp_apply]

private theorem exists_mem_coinvariants_map_eq (A : ι → Module.End R M) (A' : ι → Module.End R M')
    (T : Module.End R M) (T' : Module.End R M') (r : M →ₗ[R] M') (hr : Function.Surjective r)
    (hrA : ∀ i, r ∘ₗ A i = A' i ∘ₗ r) (hrT : r ∘ₗ T = T' ∘ₗ r)
    (h : ∀ φ : Module.Dual R M', (∀ i, φ ∘ₗ A' i = φ) → φ ∘ₗ T' = φ) (m : M) :
    ∃ n ∈ coinvariants A, r n = r (T m - m) := by
  have hmem : T' (r m) - r m ∈ coinvariants A' := sub_mem_coinvariants_of_forall_comp_eq A' T' h (r m)
  rw [← coinvariants_map_of_surjective A A' r hr hrA, Submodule.mem_map] at hmem
  obtain ⟨n, hn, hrn⟩ := hmem
  refine ⟨n, hn, ?_⟩
  rw [hrn, map_sub, ← LinearMap.comp_apply, ← hrT, LinearMap.comp_apply]

end Coinvariants

end InvariantFunctional

end InvariantStep

section SignArgument

namespace InvariantFunctional

open LinearMap

variable {ι : Type*} {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem comp_isInvariant_of_normalises' (A : ι → Module.End ℂ V) (T : Module.End ℂ V) (τ : ι → ι)
    (hnorm : ∀ i, T ∘ₗ A i = A (τ i) ∘ₗ T) (ν : Module.Dual ℂ V) (hν : ∀ i, ν ∘ₗ A i = ν) (i : ι) :
    (ν ∘ₗ T) ∘ₗ A i = ν ∘ₗ T := by
  rw [LinearMap.comp_assoc, hnorm i, ← LinearMap.comp_assoc, hν (τ i)]

private theorem eq_one_of_pos_of_mul_self_eq_one {r : ℝ} (hr : 0 < r) (h : (r : ℂ) * r = 1) : (r : ℂ) = 1 := by
  have hrr : r * r = 1 := by exact_mod_cast h
  rcases mul_self_eq_one_iff.mp hrr with h1 | h1
  · rw [h1, Complex.ofReal_one]
  · exfalso
    linarith

private theorem comp_eq_self_of_forall_eq_zero_of_forall_pos (A : ι → Module.End ℂ V) (T : Module.End ℂ V)
    (τ : ι → ι) (hTT : T ∘ₗ T = LinearMap.id) (hnorm : ∀ i, T ∘ₗ A i = A (τ i) ∘ₗ T) (b : V)
    (hinj : ∀ μ : Module.Dual ℂ V, (∀ i, μ ∘ₗ A i = μ) → μ b = 0 → μ = 0)
    (hpos : ∀ μ : Module.Dual ℂ V, (∀ i, μ ∘ₗ A i = μ) → μ b = 1 → ∃ r : ℝ, 0 < r ∧ μ (T b) = r)
    (μ : Module.Dual ℂ V) (hμ : ∀ i, μ ∘ₗ A i = μ) : μ ∘ₗ T = μ := by
  by_cases hb : μ b = 0
  · rw [hinj μ hμ hb, LinearMap.zero_comp]
  ·
    obtain ⟨μ₁, hμ₁⟩ : ∃ μ₁ : Module.Dual ℂ V, μ₁ = (μ b)⁻¹ • μ := ⟨_, rfl⟩
    have hμ₁A : ∀ i, μ₁ ∘ₗ A i = μ₁ := by
      intro i
      rw [hμ₁, LinearMap.smul_comp, hμ i]
    have hμ₁b : μ₁ b = 1 := by
      rw [hμ₁, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hb]

    obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (μ₁ ∘ₗ T) b := ⟨_, rfl⟩
    have hμ₁T : μ₁ ∘ₗ T = c • μ₁ := by
      have hinv : ∀ i, (μ₁ ∘ₗ T - c • μ₁) ∘ₗ A i = μ₁ ∘ₗ T - c • μ₁ := by
        intro i
        rw [LinearMap.sub_comp, LinearMap.smul_comp, comp_isInvariant_of_normalises' A T τ hnorm μ₁ hμ₁A i,
          hμ₁A i]
      have h0 : (μ₁ ∘ₗ T - c • μ₁) b = 0 := by
        rw [LinearMap.sub_apply, LinearMap.smul_apply, hμ₁b, smul_eq_mul, mul_one, hc, sub_self]
      exact sub_eq_zero.mp (hinj _ hinv h0)

    have hcc : c * c = 1 := by
      have h1 : μ₁ = (c * c) • μ₁ := by
        calc μ₁ = (μ₁ ∘ₗ T) ∘ₗ T := by rw [LinearMap.comp_assoc, hTT, LinearMap.comp_id]
          _ = (c • μ₁) ∘ₗ T := by rw [hμ₁T]
          _ = c • (μ₁ ∘ₗ T) := by rw [LinearMap.smul_comp]
          _ = (c * c) • μ₁ := by rw [hμ₁T, smul_smul]
      have h2 := congrArg (fun ν : Module.Dual ℂ V => ν b) h1
      simp only [LinearMap.smul_apply, smul_eq_mul, hμ₁b, mul_one] at h2
      exact h2.symm

    obtain ⟨r, hr, hcr⟩ := hpos μ₁ hμ₁A hμ₁b
    have hcr' : c = r := by
      rw [hc, LinearMap.comp_apply]
      exact hcr
    have hc1 : c = 1 := by
      rw [hcr'] at hcc ⊢
      exact eq_one_of_pos_of_mul_self_eq_one hr hcc
    have hμ₁T' : μ₁ ∘ₗ T = μ₁ := by rw [hμ₁T, hc1, one_smul]

    have hμeq : μ = (μ b) • μ₁ := by rw [hμ₁, smul_smul, mul_inv_cancel₀ hb, one_smul]
    rw [hμeq, LinearMap.smul_comp, hμ₁T']

end InvariantFunctional

end SignArgument

section LocalisationPrinciple

open Set Function

namespace Localisation

variable {X Y ι : Type*} (φ : X → Y) (A : ι → (X → ℂ) →ₗ[ℂ] (X → ℂ)) (S : Submodule ℂ (X → ℂ))

section Algebra

private noncomputable def _root_.Localisation.coinvariants : Submodule ℂ (X → ℂ) :=
  Submodule.span ℂ {g | ∃ i : ι, ∃ f ∈ S, A i f - f = g}

p2m_export "Localisation" "coinvariants"
private theorem sub_mem_coinvariants (i : ι) {f : X → ℂ} (hf : f ∈ S) : A i f - f ∈ coinvariants A S :=
  Submodule.subset_span ⟨i, f, hf, rfl⟩

private theorem coinvariants_le (hAS : ∀ i : ι, ∀ f ∈ S, A i f ∈ S) : coinvariants A S ≤ S := by
  refine Submodule.span_le.mpr ?_
  rintro g ⟨i, f, hf, rfl⟩
  exact S.sub_mem (hAS i f hf) hf

private theorem apply_eq_zero_of_mem_coinvariants (T : (X → ℂ) →ₗ[ℂ] ℂ)
    (hT : ∀ i : ι, ∀ f ∈ S, T (A i f) = T f) {g : X → ℂ} (hg : g ∈ coinvariants A S) : T g = 0 := by
  unfold coinvariants at hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨i, f, hf, rfl⟩ := hg
    rw [map_sub, hT i f hf, sub_self]
  | zero => exact map_zero T
  | add g₁ g₂ _ _ ih₁ ih₂ => rw [map_add, ih₁, ih₂, add_zero]
  | smul c g _ ih => rw [map_smul, ih, smul_zero]

end Algebra

section Multipliers

variable [TopologicalSpace Y]

private theorem indicator_preimage_mem_coinvariants
    (hS₃ : ∀ f ∈ S, ∀ V : Set Y, IsClopen V → (φ ⁻¹' V).indicator f ∈ S)
    (hA : ∀ i : ι, ∀ V : Set Y, IsClopen V → ∀ f ∈ S,
      A i ((φ ⁻¹' V).indicator f) = (φ ⁻¹' V).indicator (A i f))
    {V : Set Y} (hV : IsClopen V) {n : X → ℂ} (hn : n ∈ coinvariants A S) :
    (φ ⁻¹' V).indicator n ∈ coinvariants A S := by
  unfold coinvariants at hn
  induction hn using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨i, f, hf, rfl⟩ := hg
    rw [Set.indicator_sub', ← hA i V hV f hf]
    exact sub_mem_coinvariants A S i (hS₃ f hf V hV)
  | zero =>
    rw [Set.indicator_zero']
    exact (coinvariants A S).zero_mem
  | add g₁ g₂ _ _ ih₁ ih₂ =>
    rw [Set.indicator_add']
    exact (coinvariants A S).add_mem ih₁ ih₂
  | smul c g _ ih =>
    have hsm : (φ ⁻¹' V).indicator (c • g) = c • (φ ⁻¹' V).indicator g := by
      funext x
      by_cases hx : x ∈ φ ⁻¹' V <;> simp [hx]
    rw [hsm]
    exact (coinvariants A S).smul_mem c ih

end Multipliers

section Topological

variable [TopologicalSpace X] [TopologicalSpace Y]

private theorem isCompact_image_support (hφ : Continuous φ) {h : X → ℂ} (hloc : IsLocallyConstant h)
    (hcs : HasCompactSupport h) : IsCompact (φ '' support h) := by
  have hclosed : IsClosed (support h) := by
    have hsupp : support h = {x | h x = 0}ᶜ := by
      ext x
      simp [mem_support]
    rw [hsupp]
    exact isClosed_compl_iff.mpr (hloc.isOpen_fiber 0)
  exact ((hasCompactSupport_def.mp hcs).of_isClosed_subset hclosed subset_closure).image hφ

private theorem exists_isClopen_of_forall_fibre [T2Space Y] (hφ : Continuous φ)
    (hY : ∀ y : Y, ∀ U : Set Y, IsOpen U → y ∈ U → ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ V ⊆ U)
    {h : X → ℂ} (hloc : IsLocallyConstant h) (hcs : HasCompactSupport h) {y : Y}
    (hy : ∀ x, φ x = y → h x = 0) :
    ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ ∀ x, φ x ∈ V → h x = 0 := by
  have himg : IsClosed (φ '' support h) := (isCompact_image_support φ hφ hloc hcs).isClosed
  have hyU : y ∈ (φ '' support h)ᶜ := by
    rintro ⟨x, hx, rfl⟩
    exact hx (hy x rfl)
  obtain ⟨V, hV, hyV, hVU⟩ := hY y _ himg.isOpen_compl hyU
  refine ⟨V, hV, hyV, fun x hx => ?_⟩
  by_contra hne
  exact hVU hx ⟨x, hne, rfl⟩

private theorem mem_coinvariants_of_forall_fibre [T2Space Y] (hφ : Continuous φ)
    (hY : ∀ y : Y, ∀ U : Set Y, IsOpen U → y ∈ U → ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ V ⊆ U)
    (hS₁ : ∀ f ∈ S, IsLocallyConstant f) (hS₂ : ∀ f ∈ S, HasCompactSupport f)
    (hS₃ : ∀ f ∈ S, ∀ V : Set Y, IsClopen V → (φ ⁻¹' V).indicator f ∈ S)
    (hAS : ∀ i : ι, ∀ f ∈ S, A i f ∈ S)
    (hA : ∀ i : ι, ∀ V : Set Y, IsClopen V → ∀ f ∈ S,
      A i ((φ ⁻¹' V).indicator f) = (φ ⁻¹' V).indicator (A i f))
    {h : X → ℂ} (hh : h ∈ S)
    (hfib : ∀ y ∈ range φ, ∃ n ∈ coinvariants A S, ∀ x, φ x = y → h x = n x) :
    h ∈ coinvariants A S := by
  have hNS : coinvariants A S ≤ S := coinvariants_le A S hAS
  have key : ∀ y : Y, ∃ V : Set Y, IsClopen V ∧ (y ∈ range φ → y ∈ V) ∧
      (φ ⁻¹' V).indicator h ∈ coinvariants A S := by
    intro y
    by_cases hy : y ∈ range φ
    · obtain ⟨n, hn, hxn⟩ := hfib y hy
      have hd : h - n ∈ S := S.sub_mem hh (hNS hn)
      obtain ⟨V, hV, hyV, hV0⟩ := exists_isClopen_of_forall_fibre φ hφ hY (hS₁ _ hd) (hS₂ _ hd)
        (y := y) (fun x hx => by rw [Pi.sub_apply, hxn x hx, sub_self])
      refine ⟨V, hV, fun _ => hyV, ?_⟩
      have hcongr : (φ ⁻¹' V).indicator h = (φ ⁻¹' V).indicator n := by
        refine Set.indicator_congr fun x hx => ?_
        have hx0 := hV0 x hx
        rw [Pi.sub_apply] at hx0
        exact sub_eq_zero.mp hx0
      rw [hcongr]
      exact indicator_preimage_mem_coinvariants φ A S hS₃ hA hV hn
    · refine ⟨∅, isClopen_empty, fun hy' => (hy hy').elim, ?_⟩
      rw [Set.preimage_empty, Set.indicator_empty']
      exact (coinvariants A S).zero_mem
  choose V hVc hVmem hVN using key
  have hcpt : IsCompact (φ '' support h) := isCompact_image_support φ hφ (hS₁ h hh) (hS₂ h hh)
  obtain ⟨b, -, hbfin, hcover⟩ := hcpt.elim_finite_subcover_image (b := φ '' support h) (c := V)
    (fun y _ => (hVc y).isOpen)
    (fun z hz => Set.mem_biUnion hz (hVmem z (Set.image_subset_range φ _ hz)))
  have hunion : ∀ (t : Set Y), t.Finite → (φ ⁻¹' (⋃ y ∈ t, V y)).indicator h ∈ coinvariants A S := by
    intro t ht
    refine Set.Finite.induction_on
      (motive := fun t _ => (φ ⁻¹' (⋃ y ∈ t, V y)).indicator h ∈ coinvariants A S) t ht ?_ ?_
    · beta_reduce
      rw [Set.biUnion_empty, Set.preimage_empty, Set.indicator_empty']
      exact (coinvariants A S).zero_mem
    · intro a s _ hs ih
      rw [Set.biUnion_insert]
      have hWc : IsClopen (⋃ y ∈ s, V y) := hs.isClopen_biUnion fun y _ => hVc y
      have hsplit : φ ⁻¹' (V a ∪ ⋃ y ∈ s, V y) =
          φ ⁻¹' (V a \ ⋃ y ∈ s, V y) ∪ φ ⁻¹' (⋃ y ∈ s, V y) := by
        rw [← Set.preimage_union, Set.diff_union_self]
      rw [hsplit, Set.indicator_union_of_disjoint (Set.disjoint_sdiff_left.preimage φ)]
      refine (coinvariants A S).add_mem ?_ ih
      have hnest : (φ ⁻¹' (V a \ ⋃ y ∈ s, V y)).indicator h =
          (φ ⁻¹' (V a \ ⋃ y ∈ s, V y)).indicator ((φ ⁻¹' V a).indicator h) := by
        rw [Set.indicator_indicator, Set.inter_eq_left.mpr (Set.preimage_mono Set.diff_subset)]
      rw [hnest]
      exact indicator_preimage_mem_coinvariants φ A S hS₃ hA ((hVc a).diff hWc) (hVN a)
  have hfinal := hunion b hbfin
  have hself : (φ ⁻¹' (⋃ y ∈ b, V y)).indicator h = h :=
    Set.indicator_eq_self.mpr fun x hx => hcover ⟨x, hx, rfl⟩
  rwa [hself] at hfinal

private theorem sub_apply_mem_coinvariants_of_forall_fibre [T2Space Y] (hφ : Continuous φ)
    (hY : ∀ y : Y, ∀ U : Set Y, IsOpen U → y ∈ U → ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ V ⊆ U)
    (hS₁ : ∀ f ∈ S, IsLocallyConstant f) (hS₂ : ∀ f ∈ S, HasCompactSupport f)
    (hS₃ : ∀ f ∈ S, ∀ V : Set Y, IsClopen V → (φ ⁻¹' V).indicator f ∈ S)
    (hAS : ∀ i : ι, ∀ f ∈ S, A i f ∈ S)
    (hA : ∀ i : ι, ∀ V : Set Y, IsClopen V → ∀ f ∈ S,
      A i ((φ ⁻¹' V).indicator f) = (φ ⁻¹' V).indicator (A i f))
    (Θ : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (hΘS : ∀ f ∈ S, Θ f ∈ S) {f : X → ℂ} (hf : f ∈ S)
    (hfib : ∀ y ∈ range φ, ∃ n ∈ coinvariants A S, ∀ x, φ x = y → (f - Θ f) x = n x) :
    f - Θ f ∈ coinvariants A S :=
  mem_coinvariants_of_forall_fibre φ A S hφ hY hS₁ hS₂ hS₃ hAS hA (S.sub_mem hf (hΘS f hf)) hfib

private theorem apply_eq_of_forall_fibre [T2Space Y] (hφ : Continuous φ)
    (hY : ∀ y : Y, ∀ U : Set Y, IsOpen U → y ∈ U → ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ V ⊆ U)
    (hS₁ : ∀ f ∈ S, IsLocallyConstant f) (hS₂ : ∀ f ∈ S, HasCompactSupport f)
    (hS₃ : ∀ f ∈ S, ∀ V : Set Y, IsClopen V → (φ ⁻¹' V).indicator f ∈ S)
    (hAS : ∀ i : ι, ∀ f ∈ S, A i f ∈ S)
    (hA : ∀ i : ι, ∀ V : Set Y, IsClopen V → ∀ f ∈ S,
      A i ((φ ⁻¹' V).indicator f) = (φ ⁻¹' V).indicator (A i f))
    (Θ : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (hΘS : ∀ f ∈ S, Θ f ∈ S)
    (hfib : ∀ f ∈ S, ∀ y ∈ range φ, ∃ n ∈ coinvariants A S, ∀ x, φ x = y → (f - Θ f) x = n x)
    (T : (X → ℂ) →ₗ[ℂ] ℂ) (hT : ∀ i : ι, ∀ f ∈ S, T (A i f) = T f) {f : X → ℂ} (hf : f ∈ S) :
    T (Θ f) = T f := by
  have hmem : f - Θ f ∈ coinvariants A S :=
    sub_apply_mem_coinvariants_of_forall_fibre φ A S hφ hY hS₁ hS₂ hS₃ hAS hA Θ hΘS hf (hfib f hf)
  have h0 := apply_eq_zero_of_mem_coinvariants A S T hT hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0.symm

end Topological

end Localisation

end LocalisationPrinciple

section CharpolyCoeffs

namespace Localisation

section Continuity

variable {X S n : Type*} [TopologicalSpace X] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
variable [Fintype n] [DecidableEq n]

private theorem continuous_charpoly_coeff {B : X → Matrix n n S} (hB : Continuous B) (i : ℕ) :
    Continuous fun x => (B x).charpoly.coeff i := by
  have hcont : Continuous fun x =>
      MvPolynomial.eval (fun ij : n × n => B x ij.1 ij.2) ((Matrix.charpoly.univ S n).coeff i) :=
    (MvPolynomial.continuous_eval _).comp (continuous_pi fun ij => hB.matrix_elem ij.1 ij.2)
  refine hcont.congr fun x => ?_
  exact Matrix.charpoly.univ_coeff_eval₂Hom n (RingHom.id S) (fun ij : n × n => B x ij.1 ij.2) i

private theorem continuous_charpoly_coeff_units (i : ℕ) :
    Continuous fun g : (Matrix n n S)ˣ => (g : Matrix n n S).charpoly.coeff i :=
  continuous_charpoly_coeff Units.continuous_val i

end Continuity

section Cubic

variable {S : Type*} [CommRing S]

private noncomputable def charpolyCoeffs (A : Matrix (Fin 3) (Fin 3) S) : Fin 3 → S :=
  fun k => A.charpoly.coeff k

private theorem charpolyCoeffs_apply (A : Matrix (Fin 3) (Fin 3) S) (k : Fin 3) :
    charpolyCoeffs A k = A.charpoly.coeff k :=
  rfl

private theorem continuous_charpolyCoeffs [TopologicalSpace S] [IsTopologicalRing S] {X : Type*}
    [TopologicalSpace X] {B : X → Matrix (Fin 3) (Fin 3) S} (hB : Continuous B) :
    Continuous fun x => charpolyCoeffs (B x) :=
  continuous_pi fun k => continuous_charpoly_coeff hB k

private theorem continuous_charpolyCoeffs_units [TopologicalSpace S] [IsTopologicalRing S] :
    Continuous fun g : (Matrix (Fin 3) (Fin 3) S)ˣ => charpolyCoeffs (g : Matrix (Fin 3) (Fin 3) S) :=
  continuous_charpolyCoeffs Units.continuous_val

private theorem charpoly_eq_of_charpolyCoeffs_eq [Nontrivial S] {A A' : Matrix (Fin 3) (Fin 3) S}
    (h : charpolyCoeffs A = charpolyCoeffs A') : A.charpoly = A'.charpoly := by
  have hdA : A.charpoly.natDegree = 3 := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hdA' : A'.charpoly.natDegree = 3 := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  refine Polynomial.ext fun m => ?_
  rcases lt_trichotomy m 3 with hm | rfl | hm
  · have hk := congr_fun h ⟨m, hm⟩
    simpa [charpolyCoeffs_apply] using hk
  · have h1 : A.charpoly.coeff A.charpoly.natDegree = 1 := (Matrix.charpoly_monic A).coeff_natDegree
    have h2 : A'.charpoly.coeff A'.charpoly.natDegree = 1 :=
      (Matrix.charpoly_monic A').coeff_natDegree
    rw [hdA] at h1
    rw [hdA'] at h2
    rw [h1, h2]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdA]; exact hm),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdA']; exact hm)]

private theorem charpolyCoeffs_eq_iff [Nontrivial S] {A A' : Matrix (Fin 3) (Fin 3) S} :
    charpolyCoeffs A = charpolyCoeffs A' ↔ A.charpoly = A'.charpoly :=
  ⟨charpoly_eq_of_charpolyCoeffs_eq, fun h => by
    funext k
    rw [charpolyCoeffs_apply, charpolyCoeffs_apply, h]⟩

end Cubic

end Localisation

end CharpolyCoeffs

section CoinvariantsBridge

namespace Localisation

variable {X ι : Type*} {A : ι → (X → ℂ) →ₗ[ℂ] (X → ℂ)} {S : Submodule ℂ (X → ℂ)}

private theorem coinvariants_map_subtype_le (B : ι → Module.End ℂ S)
    (hB : ∀ (i : ι) (s : S), ((B i s : S) : X → ℂ) = A i s) :
    (InvariantFunctional.coinvariants B).map S.subtype ≤ coinvariants A S := by
  unfold InvariantFunctional.coinvariants
  rw [Submodule.map_span_le]
  rintro x ⟨i, m, rfl⟩
  rw [Submodule.subtype_apply, Submodule.coe_sub, hB]
  exact sub_mem_coinvariants A S i m.2

private theorem exists_mem_coinvariants_of_forall_eq {Y : Type*} (φ : X → Y) (B : ι → Module.End ℂ S)
    (hB : ∀ (i : ι) (s : S), ((B i s : S) : X → ℂ) = A i s) (Θ : (X → ℂ) →ₗ[ℂ] (X → ℂ))
    (f : X → ℂ) (y : Y) {n : S} (hn : n ∈ InvariantFunctional.coinvariants B)
    (hagree : ∀ x, φ x = y → (n : X → ℂ) x = (Θ f - f) x) :
    ∃ n' ∈ coinvariants A S, ∀ x, φ x = y → (f - Θ f) x = n' x := by
  refine ⟨-(n : X → ℂ),
    neg_mem (coinvariants_map_subtype_le B hB (Submodule.mem_map_of_mem hn)), ?_⟩
  intro x hx
  rw [Pi.neg_apply, hagree x hx, Pi.sub_apply, Pi.sub_apply, neg_sub]

end Localisation

end CoinvariantsBridge

section DualExtension

namespace InvariantFunctional

open Pointwise

section Extension

variable {R : Type*} [Field R] {M : Type*} [AddCommGroup M] [Module R M]

private theorem exists_dual_extension (S : Submodule R M) (μ : Module.Dual R S) :
    ∃ ν : Module.Dual R M, ∀ (m : M) (hm : m ∈ S), ν m = μ ⟨m, hm⟩ := by
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective S.subtype S.ker_subtype
  refine ⟨μ ∘ₗ P, fun m hm => ?_⟩
  have h := LinearMap.congr_fun hP ⟨m, hm⟩
  rw [LinearMap.comp_apply, LinearMap.id_apply, Submodule.subtype_apply] at h
  rw [LinearMap.comp_apply, h]

end Extension

section Transfer

variable {G : Type*} [Group G] {X : Type*} [TopologicalSpace X] [MulAction G X]
variable {R : Type*} [Field R]

private structure IndicatorAction (S : Submodule R (X → R)) (act : G → Module.End R S) : Prop where
  indicator_mem : ∀ A : Set X, IsCompact A → IsOpen A → A.indicator (1 : X → R) ∈ S
  isCompact_smul : ∀ (g : G) (A : Set X), IsCompact A → IsOpen A → IsCompact (g • A)
  isOpen_smul : ∀ (g : G) (A : Set X), IsCompact A → IsOpen A → IsOpen (g • A)
  act_indicator : ∀ (g : G) (A : Set X) (hc : IsCompact A) (ho : IsOpen A),
    ((act g ⟨A.indicator 1, indicator_mem A hc ho⟩ : S) : X → R) = (g • A).indicator 1

variable {S : Submodule R (X → R)} {act : G → Module.End R S}

private theorem IndicatorAction.extension_apply_indicator_smul (hS : IndicatorAction S act) (μ : Module.Dual R S)
    (hμ : ∀ g, μ ∘ₗ act g = μ) (ν : Module.Dual R (X → R)) (hν : ∀ (f : X → R) (hf : f ∈ S), ν f = μ ⟨f, hf⟩)
    (g : G) (A : Set X) (hc : IsCompact A) (ho : IsOpen A) :
    ν ((g • A).indicator 1) = ν (A.indicator 1) := by
  rw [hν _ (hS.indicator_mem _ (hS.isCompact_smul g A hc ho) (hS.isOpen_smul g A hc ho)),
    hν _ (hS.indicator_mem A hc ho)]
  have h1 : (⟨(g • A).indicator 1,
      hS.indicator_mem _ (hS.isCompact_smul g A hc ho) (hS.isOpen_smul g A hc ho)⟩ : S) =
        act g ⟨A.indicator 1, hS.indicator_mem A hc ho⟩ :=
    Subtype.ext (hS.act_indicator g A hc ho).symm
  rw [h1, ← LinearMap.comp_apply, hμ]

private theorem
    IndicatorAction.dual_eq_zero (hS : IndicatorAction S act) (b : Set X) (hbc : IsCompact b) (hbo : IsOpen b)
    (hC : ∀ ν : Module.Dual R (X → R),
      (∀ (g : G) (A : Set X), IsCompact A → IsOpen A → ν ((g • A).indicator 1) = ν (A.indicator 1)) →
      ν (b.indicator 1) = 0 → ∀ f ∈ S, ν f = 0)
    (μ : Module.Dual R S) (hμ : ∀ g, μ ∘ₗ act g = μ) (hb : μ ⟨b.indicator 1, hS.indicator_mem b hbc hbo⟩ = 0) :
    μ = 0 := by
  obtain ⟨ν, hν⟩ := exists_dual_extension S μ
  have hν0 : ν (b.indicator 1) = 0 := by rw [hν _ (hS.indicator_mem b hbc hbo), hb]
  ext ⟨f, hf⟩
  rw [LinearMap.zero_apply, ← hν f hf]
  exact hC ν (hS.extension_apply_indicator_smul μ hμ ν hν) hν0 f hf

end Transfer

section TransferPos

variable {G : Type*} [Group G] {X : Type*} [TopologicalSpace X] [MulAction G X]
variable {S : Submodule ℂ (X → ℂ)} {act : G → Module.End ℂ S}

private theorem IndicatorAction.exists_pos_apply_indicator (hS : IndicatorAction S act) (b : Set X) (hbc : IsCompact b)
    (hbo : IsOpen b)
    (hC : ∀ ν : Module.Dual ℂ (X → ℂ),
      (∀ (g : G) (A : Set X), IsCompact A → IsOpen A → ν ((g • A).indicator 1) = ν (A.indicator 1)) →
      ν (b.indicator 1) = 1 →
      ∀ A : Set X, A.Nonempty → IsCompact A → IsOpen A → ∃ r : ℝ, 0 < r ∧ ν (A.indicator 1) = r)
    (μ : Module.Dual ℂ S) (hμ : ∀ g, μ ∘ₗ act g = μ) (hb : μ ⟨b.indicator 1, hS.indicator_mem b hbc hbo⟩ = 1)
    (A : Set X) (hAn : A.Nonempty) (hAc : IsCompact A) (hAo : IsOpen A) :
    ∃ r : ℝ, 0 < r ∧ μ ⟨A.indicator 1, hS.indicator_mem A hAc hAo⟩ = r := by
  obtain ⟨ν, hν⟩ := exists_dual_extension S μ
  have hν1 : ν (b.indicator 1) = 1 := by rw [hν _ (hS.indicator_mem b hbc hbo), hb]
  obtain ⟨r, hr, hrA⟩ := hC ν (hS.extension_apply_indicator_smul μ hμ ν hν) hν1 A hAn hAc hAo
  exact ⟨r, hr, by rw [← hν _ (hS.indicator_mem A hAc hAo), hrA]⟩

end TransferPos

end InvariantFunctional

end DualExtension

section TestSubmodule

namespace InvariantFunctional

open Pointwise

section Submodule

variable (X : Type*) [TopologicalSpace X] (R : Type*) [Field R]

private def testSubmodule : Submodule R (X → R) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' := fun c _ hf => ⟨hf.1.comp (fun y => c • y), hf.2.comp_left (g := fun y => c • y) (smul_zero c)⟩

variable {X R}

private theorem mem_testSubmodule {f : X → R} : f ∈ testSubmodule X R ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl

private theorem isLocallyConstant_indicator [T2Space X] {A : Set X} (hc : IsCompact A) (ho : IsOpen A) :
    IsLocallyConstant (A.indicator (1 : X → R)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ A
  · exact ⟨A, ho, hx, fun y hy => by simp only [Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]⟩
  · exact ⟨Aᶜ, hc.isClosed.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

private theorem hasCompactSupport_indicator [T2Space X] {A : Set X} (hc : IsCompact A) :
    HasCompactSupport (A.indicator (1 : X → R)) :=
  HasCompactSupport.of_support_subset_isCompact hc fun _ hx =>
    Classical.by_contradiction fun h => hx (Set.indicator_of_notMem h _)

private theorem indicator_mem_testSubmodule [T2Space X] {A : Set X} (hc : IsCompact A) (ho : IsOpen A) :
    A.indicator (1 : X → R) ∈ testSubmodule X R :=
  ⟨isLocallyConstant_indicator hc ho, hasCompactSupport_indicator hc⟩

end Submodule

section Translation

variable {G : Type*} [Group G] [TopologicalSpace G] {X : Type*} [TopologicalSpace X] [MulAction G X]
  [ContinuousSMul G X] {R : Type*} [Field R]

private theorem comp_inv_smul_mem_testSubmodule (g : G) {f : X → R} (hf : f ∈ testSubmodule X R) :
    (fun x => f (g⁻¹ • x)) ∈ testSubmodule X R :=
  ⟨hf.1.comp_continuous (continuous_const_smul g⁻¹), hf.2.comp_homeomorph (Homeomorph.smul g⁻¹)⟩

variable (G X R) in

private def translationAction (g : G) : Module.End R (testSubmodule X R) where
  toFun f := ⟨fun x => (f : X → R) (g⁻¹ • x), comp_inv_smul_mem_testSubmodule g f.2⟩
  map_add' _ _ := Subtype.ext (funext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (funext fun _ => rfl)

private theorem translationAction_apply (g : G) (f : testSubmodule X R) (x : X) :
    ((translationAction G X R g f : testSubmodule X R) : X → R) x = (f : X → R) (g⁻¹ • x) :=
  rfl

private theorem coe_translationAction (g : G) (f : testSubmodule X R) :
    ((translationAction G X R g f : testSubmodule X R) : X → R) = fun x => (f : X → R) (g⁻¹ • x) :=
  rfl

private theorem coe_translationAction_indicator [T2Space X] (g : G) (A : Set X) (hc : IsCompact A) (ho : IsOpen A) :
    ((translationAction G X R g ⟨A.indicator 1, indicator_mem_testSubmodule hc ho⟩ : testSubmodule X R) : X → R) =
      (g • A).indicator 1 := by
  funext x
  rw [translationAction_apply]
  by_cases h : g⁻¹ • x ∈ A
  · simp only [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_smul_set_iff_inv_smul_mem.2 h), Pi.one_apply]
  · simp only [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (fun h' => h (Set.mem_smul_set_iff_inv_smul_mem.1 h'))]

variable (G X R) in

private theorem indicatorAction_translationAction [T2Space X] :
    IndicatorAction (testSubmodule X R) (translationAction G X R) where
  indicator_mem _ hc ho := indicator_mem_testSubmodule hc ho
  isCompact_smul g _ hc _ := hc.smul g
  isOpen_smul g _ _ ho := ho.smul g
  act_indicator g A hc ho := coe_translationAction_indicator g A hc ho

private theorem forall_mem_testSubmodule (f : X → R) (hf : f ∈ testSubmodule X R) :
    IsLocallyConstant f ∧ HasCompactSupport f :=
  hf

end Translation

end InvariantFunctional

end TestSubmodule

section ExactSequence

open Set Topology

namespace InvariantFunctional

variable {G : Type*} [TopologicalSpace G] {R : Type*} [Field R]
variable {X Z U : Set G}

section Restriction

private def restrictTo (hZX : Z ⊆ X) (hZ : IsClosed Z) : testSubmodule X R →ₗ[R] testSubmodule Z R where
  toFun f := ⟨fun z => (f : X → R) (inclusion hZX z), by
    obtain ⟨hf, hfc⟩ := mem_testSubmodule.mp f.2
    refine mem_testSubmodule.mpr ⟨hf.comp_continuous (continuous_inclusion hZX), ?_⟩
    exact hfc.comp_isClosedEmbedding
      (IsClosedEmbedding.inclusion hZX (hZ.preimage continuous_subtype_val))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem restrictTo_apply (hZX : Z ⊆ X) (hZ : IsClosed Z) (f : testSubmodule X R) (z : Z) :
    (restrictTo hZX hZ f : Z → R) z = (f : X → R) (inclusion hZX z) :=
  rfl

end Restriction

section Extension

private theorem isOpen_preimage_val_of_eq_diff (hZ : IsClosed Z) (hU : U = X \ Z) :
    IsOpen (Subtype.val ⁻¹' U : Set X) := by
  have h : (Subtype.val ⁻¹' U : Set X) = (Subtype.val ⁻¹' Z)ᶜ := by
    ext x
    simp [hU]
  rw [h]
  exact (hZ.preimage continuous_subtype_val).isOpen_compl

omit [TopologicalSpace G] in
private theorem subset_of_eq_diff (hU : U = X \ Z) : U ⊆ X := by
  rw [hU]
  exact diff_subset

open scoped Classical in

private noncomputable def extendFun (_hU : U = X \ Z) (f : U → R) (x : X) : R :=
  if h : (x : G) ∈ U then f ⟨x, h⟩ else 0

omit [TopologicalSpace G] in
private theorem extendFun_of_mem (hU : U = X \ Z) (f : U → R) {x : X} (h : (x : G) ∈ U) :
    extendFun hU f x = f ⟨x, h⟩ :=
  dif_pos h

omit [TopologicalSpace G] in
private theorem extendFun_of_notMem (hU : U = X \ Z) (f : U → R) {x : X} (h : (x : G) ∉ U) :
    extendFun hU f x = 0 :=
  dif_neg h

omit [TopologicalSpace G] in
private theorem extendFun_inclusion (hU : U = X \ Z) (f : U → R) (u : U) :
    extendFun hU f (inclusion (subset_of_eq_diff hU) u) = f u :=
  extendFun_of_mem hU f (x := inclusion (subset_of_eq_diff hU) u) u.2

private theorem extendFun_mem [T2Space G] (hZ : IsClosed Z) (hU : U = X \ Z) (f : testSubmodule U R) :
    extendFun hU (f : U → R) ∈ testSubmodule X R := by
  obtain ⟨hf, hfc⟩ := mem_testSubmodule.mp f.2
  have hUX : U ⊆ X := subset_of_eq_diff hU
  have hι : IsOpenEmbedding (inclusion hUX) :=
    IsOpenEmbedding.inclusion hUX (isOpen_preimage_val_of_eq_diff hZ hU)
  have hK : IsCompact (inclusion hUX '' tsupport (f : U → R)) :=
    IsCompact.image hfc (continuous_inclusion hUX)
  refine mem_testSubmodule.mpr ⟨?_, HasCompactSupport.of_support_subset_isCompact hK ?_⟩
  · refine (IsLocallyConstant.iff_exists_open _).mpr fun x => ?_
    by_cases hx : (x : G) ∈ U
    · obtain ⟨V, hV, hxV, hVf⟩ := (IsLocallyConstant.iff_exists_open _).mp hf ⟨x, hx⟩
      refine ⟨inclusion hUX '' V, hι.isOpenMap V hV, ⟨⟨x, hx⟩, hxV, rfl⟩, ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      rw [extendFun_inclusion, extendFun_of_mem hU _ hx]
      exact hVf u hu
    · refine ⟨(inclusion hUX '' tsupport (f : U → R))ᶜ, hK.isClosed.isOpen_compl, ?_, ?_⟩
      · rintro ⟨u, -, hux⟩
        refine hx ?_
        rw [← hux]
        exact u.2
      · intro x' hx'
        rw [extendFun_of_notMem hU _ hx]
        by_cases hx'U : (x' : G) ∈ U
        · rw [extendFun_of_mem hU _ hx'U]
          exact image_eq_zero_of_notMem_tsupport fun h => hx' ⟨⟨x', hx'U⟩, h, rfl⟩
        · exact extendFun_of_notMem hU _ hx'U
  · intro x hx
    by_cases hxU : (x : G) ∈ U
    · refine ⟨⟨x, hxU⟩, subset_tsupport _ ?_, rfl⟩
      rwa [Function.mem_support, ← extendFun_of_mem hU (f : U → R) hxU]
    · exact absurd (extendFun_of_notMem hU (f : U → R) hxU) hx

private noncomputable def extendByZero [T2Space G] (hZ : IsClosed Z) (hU : U = X \ Z) :
    testSubmodule U R →ₗ[R] testSubmodule X R where
  toFun f := ⟨extendFun hU (f : U → R), extendFun_mem hZ hU f⟩
  map_add' f g := by
    ext x
    by_cases h : (x : G) ∈ U
    · simp [extendFun_of_mem hU _ h]
    · simp [extendFun_of_notMem hU _ h]
  map_smul' c f := by
    ext x
    by_cases h : (x : G) ∈ U
    · simp [extendFun_of_mem hU _ h]
    · simp [extendFun_of_notMem hU _ h]

private theorem extendByZero_apply [T2Space G] (hZ : IsClosed Z) (hU : U = X \ Z) (f : testSubmodule U R)
    (x : X) :
    (extendByZero hZ hU f : X → R) x = extendFun hU (f : U → R) x :=
  rfl

end Extension

section Exactness

omit [TopologicalSpace G] in
private theorem notMem_of_mem_of_eq_diff (hU : U = X \ Z) {z : G} (hz : z ∈ Z) : z ∉ U := by
  rw [hU]
  exact fun h => h.2 hz

omit [TopologicalSpace G] in
private theorem mem_of_mem_of_notMem (hU : U = X \ Z) {x : G} (hx : x ∈ X) (hxU : x ∉ U) : x ∈ Z := by
  by_contra h
  exact hxU (hU ▸ ⟨hx, h⟩)

private theorem exact_extendByZero_restrictTo [T2Space G] (hZX : Z ⊆ X) (hZ : IsClosed Z) (hU : U = X \ Z) :
    Function.Exact (extendByZero (R := R) hZ hU) (restrictTo hZX hZ) := by
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
  · ext f z
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, restrictTo_apply, extendByZero_apply,
      ZeroMemClass.coe_zero, Pi.zero_apply]
    exact extendFun_of_notMem hU _ (x := inclusion hZX z) (notMem_of_mem_of_eq_diff hU z.2)
  · intro f hf
    rw [LinearMap.mem_ker] at hf
    have hfZ : ∀ x : X, (x : G) ∈ Z → (f : X → R) x = 0 := fun x hx => by
      have := congrArg (fun g : testSubmodule Z R => (g : Z → R) ⟨x, hx⟩) hf
      simpa [restrictTo_apply] using this
    obtain ⟨hfl, hfc⟩ := mem_testSubmodule.mp f.2
    have hUX : U ⊆ X := subset_of_eq_diff hU
    have hι : IsOpenEmbedding (inclusion hUX) :=
      IsOpenEmbedding.inclusion hUX (isOpen_preimage_val_of_eq_diff hZ hU)

    have hcl : IsCompact {x : X | (f : X → R) x ≠ 0} :=
      IsCompact.of_isClosed_subset hfc (isClosed_compl_iff.mpr (hfl.isOpen_fiber 0))
        fun x hx => subset_tsupport _ hx
    have himage :
        inclusion hUX '' Function.support ((f : X → R) ∘ inclusion hUX) =
          {x : X | (f : X → R) x ≠ 0} := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro hx
        have hxU : (x : G) ∈ U := by
          by_contra hxU
          exact hx (hfZ x (mem_of_mem_of_notMem hU x.2 hxU))
        exact ⟨⟨x, hxU⟩, hx, rfl⟩
    have hg : (f : X → R) ∘ inclusion hUX ∈ testSubmodule U R := by
      refine mem_testSubmodule.mpr ⟨hfl.comp_continuous (continuous_inclusion hUX), ?_⟩
      refine HasCompactSupport.of_support_subset_isCompact ?_ subset_rfl
      rw [hι.isEmbedding.isCompact_iff, himage]
      exact hcl
    refine LinearMap.mem_range.mpr ⟨⟨_, hg⟩, ?_⟩
    ext x
    rw [extendByZero_apply]
    by_cases hx : (x : G) ∈ U
    · rw [extendFun_of_mem hU _ hx]
      rfl
    · rw [extendFun_of_notMem hU _ hx, hfZ x (mem_of_mem_of_notMem hU x.2 hx)]

end Exactness

section Surjectivity

private def HasCompactTraces (X Z : Set G) : Prop :=
  ∀ C : Set G, C ⊆ Z → IsCompact C → IsOpen (Subtype.val ⁻¹' C : Set Z) →
    ∃ W : Set G, W ⊆ X ∧ IsCompact W ∧ IsOpen (Subtype.val ⁻¹' W : Set X) ∧ W ∩ Z = C

private theorem hasCompactTraces_of_basis (hZX : Z ⊆ X) (hX : IsClosed X)
    (hbasis : ∀ x : G, ∀ O ∈ 𝓝 x, ∃ V : Set G, IsCompact V ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ O) :
    HasCompactTraces X Z := by
  intro C hCZ hC hCo
  obtain ⟨O, hO, hOC⟩ := isOpen_induced_iff.mp hCo
  have hOZ : O ∩ Z = C := by
    ext z
    constructor
    · rintro ⟨hzO, hzZ⟩
      have h : (⟨z, hzZ⟩ : Z) ∈ (Subtype.val ⁻¹' O : Set Z) := hzO
      rw [hOC] at h
      exact h
    · intro hz
      have h : (⟨z, hCZ hz⟩ : Z) ∈ (Subtype.val ⁻¹' C : Set Z) := hz
      rw [← hOC] at h
      exact ⟨h, hCZ hz⟩
  have hCO : ∀ x ∈ C, x ∈ O := fun x hx => by
    rw [← hOZ] at hx
    exact hx.1
  choose V hVc hVo hxV hVO using fun x (hx : x ∈ C) => hbasis x O (hO.mem_nhds (hCO x hx))
  obtain ⟨t, ht⟩ := hC.elim_nhds_subcover' V fun x hx => (hVo x hx).mem_nhds (hxV x hx)
  have hVt : IsCompact (⋃ x ∈ t, V (x : G) x.2) := t.isCompact_biUnion fun x _ => hVc x x.2
  have hVt' : IsOpen (⋃ x ∈ t, V (x : G) x.2) := isOpen_iUnion fun x => isOpen_iUnion fun _ => hVo x x.2
  refine ⟨(⋃ x ∈ t, V (x : G) x.2) ∩ X, inter_subset_right, hVt.inter_right hX, ?_, ?_⟩
  · have h : (Subtype.val ⁻¹' ((⋃ x ∈ t, V (x : G) x.2) ∩ X) : Set X) =
        Subtype.val ⁻¹' (⋃ x ∈ t, V (x : G) x.2) := by
      ext x
      simp
    rw [h]
    exact hVt'.preimage continuous_subtype_val
  · ext z
    constructor
    · rintro ⟨⟨hzV, -⟩, hzZ⟩
      rw [← hOZ]
      refine ⟨?_, hzZ⟩
      simp only [mem_iUnion] at hzV
      obtain ⟨x, -, hzx⟩ := hzV
      exact hVO x x.2 hzx
    · intro hz
      exact ⟨⟨ht hz, hZX (hCZ hz)⟩, hCZ hz⟩

open scoped Classical in

private theorem restrictTo_surjective [T2Space G] (hZX : Z ⊆ X) (hZ : IsClosed Z) (htr : HasCompactTraces X Z) :
    Function.Surjective (restrictTo (R := R) hZX hZ) := by
  intro h
  obtain ⟨hh, hhc⟩ := mem_testSubmodule.mp h.2

  have hfin : (range fun t : tsupport (h : Z → R) => (h : Z → R) t).Finite := by
    haveI : CompactSpace (tsupport (h : Z → R)) := isCompact_iff_compactSpace.mp hhc
    exact (hh.comp_continuous continuous_subtype_val).range_finite

  have hfibre : ∀ c : R, c ≠ 0 → ∃ W : Set G, W ⊆ X ∧ IsCompact W ∧
      IsOpen (Subtype.val ⁻¹' W : Set X) ∧ W ∩ Z = Subtype.val '' {z : Z | (h : Z → R) z = c} := by
    intro c hc
    have hsub : {z : Z | (h : Z → R) z = c} ⊆ tsupport (h : Z → R) :=
      fun z (hz : (h : Z → R) z = c) => subset_tsupport _ (by rw [Function.mem_support, hz]; exact hc)
    refine htr _ ?_ ?_ ?_
    · rintro _ ⟨z, -, rfl⟩
      exact z.2
    · exact (IsCompact.of_isClosed_subset hhc (hh.isClosed_fiber c) hsub).image continuous_subtype_val
    · rw [Subtype.val_injective.preimage_image]
      exact hh.isOpen_fiber c
  choose W hWX hWc hWo hWZ using hfibre
  have hpc : ∀ c (hc : c ≠ 0), IsCompact (Subtype.val ⁻¹' W c hc : Set X) := by
    intro c hc
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr (hWX c hc)]
    exact hWc c hc

  let piece : R → testSubmodule X R := fun c =>
    if hc : c = 0 then 0 else
      c • ⟨(Subtype.val ⁻¹' W c hc : Set X).indicator 1, indicator_mem_testSubmodule (hpc c hc) (hWo c hc)⟩
  refine ⟨∑ c ∈ hfin.toFinset, piece c, ?_⟩
  ext z
  rw [restrictTo_apply]

  have hpiece : ∀ c : R, (piece c : X → R) (inclusion hZX z) = if (h : Z → R) z = c then c else 0 := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp [piece]
    · have hmem : (inclusion hZX z : X) ∈ (Subtype.val ⁻¹' W c hc : Set X) ↔ (h : Z → R) z = c := by
        change (z : G) ∈ W c hc ↔ _
        constructor
        · intro hzW
          have hz : (z : G) ∈ W c hc ∩ Z := ⟨hzW, z.2⟩
          rw [hWZ c hc] at hz
          obtain ⟨z', hz', hzz'⟩ := hz
          rwa [Subtype.val_injective hzz'] at hz'
        · intro hz
          have hz' : (z : G) ∈ W c hc ∩ Z := by
            rw [hWZ c hc]
            exact ⟨z, hz, rfl⟩
          exact hz'.1
      simp only [piece, dif_neg hc, Submodule.coe_smul, Pi.smul_apply, indicator_apply, Pi.one_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases hz : (h : Z → R) z = c
      · rw [if_pos (hmem.mpr hz), if_pos hz]
      · rw [if_neg (fun hzW => hz (hmem.mp hzW)), if_neg hz]
  rw [Submodule.coe_sum, Finset.sum_apply]
  simp only [hpiece]
  by_cases hz0 : (h : Z → R) z = 0
  · rw [hz0]
    refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs with hc
    · exact hc.symm
    · rfl
  · have hmemV : (h : Z → R) z ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨⟨z, subset_tsupport _ hz0⟩, rfl⟩
    simp [Finset.sum_ite_eq, hmemV]

end Surjectivity

section Equivariance

variable (hZX : Z ⊆ X) (hZ : IsClosed Z) (hU : U = X \ Z)
variable {σ : G → G} (hσX : MapsTo σ X X) (hσU : MapsTo σ U U) (hσZ : MapsTo σ Z Z)

omit [TopologicalSpace G] in
include hU hσU hσZ in
private theorem mem_iff_of_mapsTo (x : X) : σ x ∈ U ↔ (x : G) ∈ U := by
  constructor
  · intro hσx
    by_contra hx
    exact notMem_of_mem_of_eq_diff hU (hσZ (mem_of_mem_of_notMem hU x.2 hx)) hσx
  · exact fun hx => hσU hx

include hσZ in

private theorem extendByZero_comp [T2Space G] (PU : Module.End R (testSubmodule U R))
    (PX : Module.End R (testSubmodule X R))
    (hPU : ∀ (f : testSubmodule U R) (u : U), (PU f : U → R) u = (f : U → R) ⟨σ u, hσU u.2⟩)
    (hPX : ∀ (f : testSubmodule X R) (x : X), (PX f : X → R) x = (f : X → R) ⟨σ x, hσX x.2⟩) :
    extendByZero hZ hU ∘ₗ PU = PX ∘ₗ extendByZero hZ hU := by
  ext f x
  simp only [LinearMap.comp_apply, extendByZero_apply]
  rw [hPX, extendByZero_apply]
  by_cases hx : (x : G) ∈ U
  · simp only [extendFun_of_mem hU _ hx, extendFun_of_mem hU _ (x := ⟨σ x, hσX x.2⟩) (hσU hx), hPU]
  · rw [extendFun_of_notMem hU _ hx,
      extendFun_of_notMem hU _ (x := ⟨σ x, hσX x.2⟩)
        fun hσx => hx ((mem_iff_of_mapsTo hU hσU hσZ x).mp hσx)]

private theorem restrictTo_comp (PX : Module.End R (testSubmodule X R)) (PZ : Module.End R (testSubmodule Z R))
    (hPX : ∀ (f : testSubmodule X R) (x : X), (PX f : X → R) x = (f : X → R) ⟨σ x, hσX x.2⟩)
    (hPZ : ∀ (f : testSubmodule Z R) (z : Z), (PZ f : Z → R) z = (f : Z → R) ⟨σ z, hσZ z.2⟩) :
    restrictTo hZX hZ ∘ₗ PX = PZ ∘ₗ restrictTo hZX hZ := by
  ext f z
  simp only [LinearMap.comp_apply, restrictTo_apply]
  rw [hPX, hPZ, restrictTo_apply]

end Equivariance

end InvariantFunctional

end ExactSequence

section RestrictUniv

open Set Topology

namespace InvariantFunctional

variable {G : Type*} [TopologicalSpace G] {R : Type*} [Field R] {Z : Set G}

private def restrictUniv (hZ : IsClosed Z) : testSubmodule G R →ₗ[R] testSubmodule Z R where
  toFun f := ⟨fun z => (f : G → R) z, by
    obtain ⟨hf, hfc⟩ := mem_testSubmodule.mp f.2
    exact mem_testSubmodule.mpr ⟨hf.comp_continuous continuous_subtype_val,
      hfc.comp_isClosedEmbedding hZ.isClosedEmbedding_subtypeVal⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem restrictUniv_apply (hZ : IsClosed Z) (f : testSubmodule G R) (z : Z) :
    (restrictUniv hZ f : Z → R) z = (f : G → R) z :=
  rfl

private def ofUniv : testSubmodule (univ : Set G) R →ₗ[R] testSubmodule G R where
  toFun f := ⟨fun x => (f : ↥(univ : Set G) → R) ⟨x, mem_univ x⟩, by
    obtain ⟨hf, hfc⟩ := mem_testSubmodule.mp f.2
    refine mem_testSubmodule.mpr ⟨hf.comp_continuous (continuous_id.subtype_mk fun x => mem_univ x), ?_⟩
    exact hfc.comp_homeomorph (Homeomorph.Set.univ G).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem restrictUniv_ofUniv (hZ : IsClosed Z) (f : testSubmodule (univ : Set G) R) :
    restrictUniv hZ (ofUniv f) = restrictTo (subset_univ Z) hZ f :=
  rfl

private theorem restrictUniv_surjective [T2Space G] (hZ : IsClosed Z)
    (hbasis : ∀ x : G, ∀ O ∈ 𝓝 x, ∃ V : Set G, IsCompact V ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ O) :
    Function.Surjective (restrictUniv (R := R) hZ) := by
  intro h
  obtain ⟨f, hf⟩ := restrictTo_surjective (subset_univ Z) hZ
    (hasCompactTraces_of_basis (subset_univ Z) isClosed_univ hbasis) h
  exact ⟨ofUniv f, (restrictUniv_ofUniv hZ f).trans hf⟩

private theorem restrictUniv_comp (hZ : IsClosed Z) {σ : G → G} (hσZ : MapsTo σ Z Z)
    (PG : Module.End R (testSubmodule G R)) (PZ : Module.End R (testSubmodule Z R))
    (hPG : ∀ (f : testSubmodule G R) (x : G), (PG f : G → R) x = (f : G → R) (σ x))
    (hPZ : ∀ (f : testSubmodule Z R) (z : Z), (PZ f : Z → R) z = (f : Z → R) ⟨σ z, hσZ z.2⟩) :
    restrictUniv hZ ∘ₗ PG = PZ ∘ₗ restrictUniv hZ := by
  ext f z
  simp only [LinearMap.comp_apply, restrictUniv_apply]
  rw [hPG, hPZ, restrictUniv_apply]

end InvariantFunctional

end RestrictUniv

section Cells

namespace HomogeneousCells

open MulAction Set Filter Topology

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

private theorem orbit_subgroup_eq_image (K : Subgroup G) (x : X) :
    orbit K x = (fun g : G => g • x) '' (K : Set G) := by
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

variable [TopologicalSpace G] [TopologicalSpace X]

private theorem
    isCompact_orbit_of_isCompact [ContinuousSMul G X] (K : Subgroup G) (hK : IsCompact (K : Set G)) (x : X) :
    IsCompact (orbit K x) := by
  rw [orbit_subgroup_eq_image]
  exact hK.image (continuous_id.smul continuous_const)

private theorem isOpen_orbit_of_isOpenMap (K : Subgroup G) (hK : IsOpen (K : Set G)) (x : X)
    (hx : IsOpenMap fun g : G => g • x) : IsOpen (orbit K x) := by
  rw [orbit_subgroup_eq_image]
  exact hx _ hK

variable [ContinuousSMul G X]

private theorem exists_nhds_forall_smul_apply_eq {Y : Type*} (f : X → Y) (hf : IsLocallyConstant f) (x : X) :
    ∃ U ∈ 𝓝 (1 : G), ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∀ g ∈ U, ∀ y ∈ W, f (g • y) = f x ∧ f y = f x := by
  have hV : f ⁻¹' {f x} ∈ 𝓝 x := (hf.isOpen_fiber (f x)).mem_nhds rfl
  have hcont : ContinuousAt (fun p : G × X => p.1 • p.2) ((1 : G), x) := continuous_smul.continuousAt
  have hpre : (fun p : G × X => p.1 • p.2) ⁻¹' (f ⁻¹' {f x}) ∈ 𝓝 ((1 : G), x) := by
    apply hcont.preimage_mem_nhds
    show f ⁻¹' {f x} ∈ 𝓝 ((1 : G) • x)
    rw [one_smul]
    exact hV
  rw [mem_nhds_prod_iff] at hpre
  obtain ⟨U, hU, W₀, hW₀, hUW⟩ := hpre
  obtain ⟨W, hWW₀, hWo, hxW⟩ := mem_nhds_iff.mp (Filter.inter_mem hW₀ hV)
  refine ⟨U, hU, W, hWo, hxW, fun g hg y hy => ⟨?_, ?_⟩⟩
  · have h2 : (g, y) ∈ (fun p : G × X => p.1 • p.2) ⁻¹' (f ⁻¹' {f x}) := hUW ⟨hg, (hWW₀ hy).1⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h2
    exact h2
  · have h2 : y ∈ f ⁻¹' {f x} := (hWW₀ hy).2
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h2
    exact h2

private theorem exists_subgroup_forall_smul_apply_eq {Y : Type*} [Zero Y]
    (hbasis : ∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ (K : Set G) ⊆ U)
    (f : X → Y) (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ k ∈ K, ∀ y : X, f (k • y) = f y := by
  choose U hU W hWo hxW hUW using fun x : X => exists_nhds_forall_smul_apply_eq (G := G) f hf x
  obtain ⟨s, hs⟩ :=
    hfc.isCompact.elim_finite_subcover W hWo fun x _ => Set.mem_iUnion.mpr ⟨x, hxW x⟩
  have hUs : (⋂ x ∈ s, U x) ∈ 𝓝 (1 : G) := (Filter.biInter_finset_mem s).mpr fun x _ => hU x
  obtain ⟨K, hKo, hKU⟩ := hbasis _ hUs
  refine ⟨K, hKo, fun k hk y => ?_⟩
  have hkU : ∀ x ∈ s, k ∈ U x := fun x hx => Set.mem_iInter₂.mp (hKU hk) x hx
  have hk'U : ∀ x ∈ s, k⁻¹ ∈ U x := fun x hx => Set.mem_iInter₂.mp (hKU (K.inv_mem hk)) x hx
  by_cases hy : y ∈ ⋃ x ∈ s, W x
  · obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp hy
    obtain ⟨h1, h2⟩ := hUW x k (hkU x hx) y hyx
    rw [h1, h2]
  · by_cases hky : k • y ∈ ⋃ x ∈ s, W x
    · obtain ⟨x, hx, hkyx⟩ := Set.mem_iUnion₂.mp hky
      obtain ⟨h1, h2⟩ := hUW x k⁻¹ (hk'U x hx) (k • y) hkyx
      rw [inv_smul_smul] at h1
      rw [h1, h2]
    · have hy0 : f y = 0 := by
        by_contra hne
        exact hy (hs (subset_tsupport f (Function.mem_support.mpr hne)))
      have hky0 : f (k • y) = 0 := by
        by_contra hne
        exact hky (hs (subset_tsupport f (Function.mem_support.mpr hne)))
      rw [hy0, hky0]

end HomogeneousCells

end Cells

section IndexLaw

namespace HomogeneousCells

open MulAction Set Pointwise

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

private theorem smul_orbit_eq_orbit_smul (K' : Subgroup G) (k : G) (hk : ∀ k' ∈ K', k * k' * k⁻¹ ∈ K')
    (hk' : ∀ k' ∈ K', k⁻¹ * k' * k ∈ K') (x : X) : k • orbit K' x = orbit K' (k • x) := by
  ext y
  constructor
  · rintro ⟨z, ⟨k', rfl⟩, rfl⟩
    refine ⟨⟨k * k' * k⁻¹, hk k' k'.2⟩, ?_⟩
    show (k * (k' : G) * k⁻¹) • (k • x) = k • ((k' : G) • x)
    rw [mul_smul, mul_smul, inv_smul_smul]
  · rintro ⟨k', rfl⟩
    refine ⟨(k⁻¹ * (k' : G) * k) • x, ⟨⟨k⁻¹ * k' * k, hk' k' k'.2⟩, rfl⟩, ?_⟩
    show k • ((k⁻¹ * (k' : G) * k) • x) = (k' : G) • (k • x)
    rw [mul_smul, mul_smul, smul_inv_smul]

private theorem orbit_eq_or_disjoint (K' : Subgroup G) (a b : X) :
    orbit K' a = orbit K' b ∨ Disjoint (orbit K' a) (orbit K' b) := by
  by_cases h : orbit K' a = orbit K' b
  · exact Or.inl h
  · refine Or.inr (Set.disjoint_left.mpr fun y hya hyb => h ?_)
    exact (orbit_eq_iff.mpr hya).symm.trans (orbit_eq_iff.mpr hyb)

variable [TopologicalSpace G] [TopologicalSpace X] [ContinuousSMul G X]

private theorem exists_apply_indicator_orbit_eq_mul {R : Type*} [CommRing R] (K K' : Subgroup G) (hle : K' ≤ K)
    (hN : ∀ k ∈ K, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') (hK : IsCompact (K : Set G))
    (hK'o : IsOpen (K' : Set G)) (hK'c : IsCompact (K' : Set G)) (hopen : ∀ y : X, IsOpenMap fun g : G => g • y)
    (x : X) (μ : (X → R) →ₗ[R] R)
    (hμ : ∀ k ∈ K, ∀ A : Set X, IsCompact A → IsOpen A → μ ((k • A).indicator 1) = μ (A.indicator 1)) :
    ∃ n : ℕ, 0 < n ∧ μ ((orbit K x).indicator 1) = n * μ ((orbit K' x).indicator 1) := by
  classical
  set cell : K → Set X := fun k => orbit K' ((k : G) • x) with hcell
  have hcello : ∀ k, IsOpen (cell k) := fun k => isOpen_orbit_of_isOpenMap K' hK'o _ (hopen _)
  have hcover : orbit K x = ⋃ k : K, cell k := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact Set.mem_iUnion.mpr ⟨k, mem_orbit_self _⟩
    · intro hy
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
      obtain ⟨k', rfl⟩ := hk
      exact ⟨⟨(k' : G) * k, K.mul_mem (hle k'.2) k.2⟩, mul_smul _ _ _⟩

  have hCfin : (Set.range cell).Finite := by
    obtain ⟨t, ht⟩ := (isCompact_orbit_of_isCompact K hK x).elim_finite_subcover cell hcello hcover.subset
    apply (t.finite_toSet.image cell).subset
    rintro c ⟨k, rfl⟩
    have hkx : ((k : G) • x) ∈ orbit K x := ⟨k, rfl⟩
    obtain ⟨k'', hk''t, hk''⟩ := Set.mem_iUnion₂.mp (ht hkx)
    exact ⟨k'', Finset.mem_coe.mpr hk''t, (orbit_eq_iff.mpr hk'').symm⟩

  have hU : orbit K x = ⋃ c ∈ hCfin.toFinset, c := by
    rw [hcover]
    ext y
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, Set.mem_range, exists_prop]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨cell k, ⟨k, rfl⟩, hk⟩
    · rintro ⟨c, ⟨k, rfl⟩, hk⟩
      exact ⟨k, hk⟩

  have hdisj : (↑hCfin.toFinset : Set (Set X)).PairwiseDisjoint id := by
    intro c hc d hd hcd
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hc hd
    obtain ⟨k, rfl⟩ := hc
    obtain ⟨l, rfl⟩ := hd
    rcases orbit_eq_or_disjoint K' ((k : G) • x) ((l : G) • x) with h | h
    · exact absurd h hcd
    · exact h

  have hind : (orbit K x).indicator (1 : X → R) = ∑ c ∈ hCfin.toFinset, c.indicator 1 := by
    rw [hU]
    have h := Finset.indicator_biUnion hCfin.toFinset id (f := (1 : X → R)) hdisj
    simp only [id] at h
    rw [h]
    ext a
    simp only [Finset.sum_apply]

  have hval : ∀ c ∈ hCfin.toFinset, μ (c.indicator 1) = μ ((orbit K' x).indicator 1) := by
    intro c hc
    rw [Set.Finite.mem_toFinset] at hc
    obtain ⟨k, rfl⟩ := hc
    have hk' : ∀ k' ∈ K', (k : G)⁻¹ * k' * k ∈ K' := fun k' hk' => by
      simpa only [inv_inv] using hN (k : G)⁻¹ (K.inv_mem k.2) k' hk'
    have hk : cell k = (k : G) • orbit K' x := by
      show orbit K' ((k : G) • x) = (k : G) • orbit K' x
      exact (smul_orbit_eq_orbit_smul K' (k : G) (hN k k.2) hk' x).symm
    rw [hk]
    exact hμ k k.2 _ (isCompact_orbit_of_isCompact K' hK'c x) (isOpen_orbit_of_isOpenMap K' hK'o x (hopen x))
  refine ⟨hCfin.toFinset.card, ?_, ?_⟩
  · rw [Finset.card_pos]
    exact ⟨cell 1, by rw [Set.Finite.mem_toFinset]; exact ⟨1, rfl⟩⟩
  · rw [hind, map_sum, Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]

end HomogeneousCells

end IndexLaw

section LadderFurniture

namespace HomogeneousCells

open MulAction Set Pointwise

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

private def conjSubgroup (g : G) (K : Subgroup G) : Subgroup G where
  carrier := {x | g * x * g⁻¹ ∈ K}
  one_mem' := by
    show g * 1 * g⁻¹ ∈ K
    rw [mul_one, mul_inv_cancel]
    exact K.one_mem
  mul_mem' := by
    intro a b ha hb
    show g * (a * b) * g⁻¹ ∈ K
    have h : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [h]
    exact K.mul_mem ha hb
  inv_mem' := by
    intro a ha
    show g * a⁻¹ * g⁻¹ ∈ K
    have h : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [h]
    exact K.inv_mem ha

private theorem mem_conjSubgroup {g : G} {K : Subgroup G} {x : G} : x ∈ conjSubgroup g K ↔ g * x * g⁻¹ ∈ K :=
  Iff.rfl

private theorem isOpen_conjSubgroup [TopologicalSpace G] [ContinuousMul G] (g : G) {K : Subgroup G}
    (hK : IsOpen (K : Set G)) : IsOpen (conjSubgroup g K : Set G) :=
  hK.preimage ((continuous_const.mul continuous_id).mul continuous_const)

private theorem coe_conjSubgroup_eq_image (g : G) (K : Subgroup G) :
    (conjSubgroup g K : Set G) = (fun y : G => g⁻¹ * y * g) '' (K : Set G) := by
  ext x
  constructor
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    show g⁻¹ * (g * x * g⁻¹) * g = x
    group
  · rintro ⟨y, hy, rfl⟩
    show g * (g⁻¹ * y * g) * g⁻¹ ∈ K
    have h : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [h]
    exact hy

private theorem isCompact_conjSubgroup [TopologicalSpace G] [ContinuousMul G] (g : G) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) : IsCompact (conjSubgroup g K : Set G) := by
  rw [coe_conjSubgroup_eq_image]
  exact hK.image ((continuous_const.mul continuous_id).mul continuous_const)

private theorem orbit_smul_eq_smul_orbit_conjSubgroup (K : Subgroup G) (g : G) (x : X) :
    orbit K (g • x) = g • orbit (conjSubgroup g K) x := by
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    have hmem : g⁻¹ * (k : G) * g ∈ conjSubgroup g K := by
      rw [mem_conjSubgroup]
      have h : g * (g⁻¹ * (k : G) * g) * g⁻¹ = k := by group
      rw [h]
      exact k.2
    refine ⟨(g⁻¹ * (k : G) * g) • x, ⟨⟨g⁻¹ * (k : G) * g, hmem⟩, rfl⟩, ?_⟩
    show g • ((g⁻¹ * (k : G) * g) • x) = (k : G) • (g • x)
    rw [mul_smul, mul_smul, smul_inv_smul]
  · rintro ⟨z, ⟨c, rfl⟩, rfl⟩
    refine ⟨⟨g * (c : G) * g⁻¹, (mem_conjSubgroup.mp c.2)⟩, ?_⟩
    show (g * (c : G) * g⁻¹) • (g • x) = g • ((c : G) • x)
    rw [mul_smul, mul_smul, inv_smul_smul]

private def relCore (K₁ H : Subgroup G) : Subgroup G where
  carrier := {x | ∀ k ∈ K₁, k⁻¹ * x * k ∈ H}
  one_mem' := by
    intro k _
    show k⁻¹ * 1 * k ∈ H
    rw [mul_one, inv_mul_cancel]
    exact H.one_mem
  mul_mem' := by
    intro a b ha hb k hk
    show k⁻¹ * (a * b) * k ∈ H
    have h : k⁻¹ * (a * b) * k = (k⁻¹ * a * k) * (k⁻¹ * b * k) := by group
    rw [h]
    exact H.mul_mem (ha k hk) (hb k hk)
  inv_mem' := by
    intro a ha k hk
    show k⁻¹ * a⁻¹ * k ∈ H
    have h : k⁻¹ * a⁻¹ * k = (k⁻¹ * a * k)⁻¹ := by group
    rw [h]
    exact H.inv_mem (ha k hk)

private theorem mem_relCore {K₁ H : Subgroup G} {x : G} : x ∈ relCore K₁ H ↔ ∀ k ∈ K₁, k⁻¹ * x * k ∈ H :=
  Iff.rfl

private theorem relCore_le (K₁ H : Subgroup G) : relCore K₁ H ≤ H := by
  intro x hx
  have h := (mem_relCore.mp hx) 1 K₁.one_mem
  rwa [inv_one, one_mul, mul_one] at h

private theorem mul_mul_inv_mem_relCore {K₁ H : Subgroup G} {k : G} (hk : k ∈ K₁) {x : G}
    (hx : x ∈ relCore K₁ H) : k * x * k⁻¹ ∈ relCore K₁ H := by
  rw [mem_relCore]
  intro k' hk'
  have h := (mem_relCore.mp hx) (k⁻¹ * k') (K₁.mul_mem (K₁.inv_mem hk) hk')
  have e : k'⁻¹ * (k * x * k⁻¹) * k' = (k⁻¹ * k')⁻¹ * x * (k⁻¹ * k') := by group
  rw [e]
  exact h

private theorem
    isOpen_relCore [TopologicalSpace G] [ContinuousMul G] {K₁ H : Subgroup G} (hK₁ : IsCompact (K₁ : Set G))
    (hH : IsOpen (H : Set G)) : IsOpen (relCore K₁ H : Set G) := by
  classical

  set U : K₁ → Set G := fun k => (fun g : G => (k : G)⁻¹ * g) ⁻¹' (H : Set G) with hU
  have hUo : ∀ k, IsOpen (U k) := fun k => hH.preimage (continuous_const.mul continuous_id)
  have hcover : (K₁ : Set G) ⊆ ⋃ k, U k := by
    intro g hg
    refine Set.mem_iUnion.mpr ⟨⟨g, hg⟩, ?_⟩
    show (g⁻¹ * g) ∈ (H : Set G)
    rw [inv_mul_cancel]
    exact H.one_mem
  obtain ⟨t, ht⟩ := hK₁.elim_finite_subcover U hUo hcover

  have hcore : (relCore K₁ H : Set G) =
      ⋂ k ∈ t, (fun x : G => (k : G)⁻¹ * x * k) ⁻¹' (H : Set G) := by
    ext x
    rw [Set.mem_iInter₂]
    constructor
    · intro hx k _
      exact (mem_relCore.mp hx) k k.2
    · intro hx
      rw [SetLike.mem_coe, mem_relCore]
      intro k hk
      obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp (ht hk)
      have hh : (i : G)⁻¹ * k ∈ H := hki
      have e : k⁻¹ * x * k = ((i : G)⁻¹ * k)⁻¹ * ((i : G)⁻¹ * x * i) * ((i : G)⁻¹ * k) := by group
      rw [e]
      exact H.mul_mem (H.mul_mem (H.inv_mem hh) (hx i hi)) hh
  rw [hcore]
  exact isOpen_biInter_finset fun k _ =>
    hH.preimage ((continuous_const.mul continuous_id).mul continuous_const)

private theorem
    isCompact_relCore [TopologicalSpace G] [ContinuousMul G] {K₁ H : Subgroup G} (hK₁ : IsCompact (K₁ : Set G))
    (hHle : H ≤ K₁) (hH : IsOpen (H : Set G)) : IsCompact (relCore K₁ H : Set G) :=
  hK₁.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (isOpen_relCore hK₁ hH))
    fun _ hx => hHle (relCore_le K₁ H hx)

private theorem
    exists_finset_orbit_eq_sum_indicator [TopologicalSpace G] [TopologicalSpace X] {R : Type*} [AddCommMonoid R]
    (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hopen : ∀ y : X, IsOpenMap fun g : G => g • y) (f : X → R)
    (hfc : HasCompactSupport f) :
    ∃ C : Finset (Set X), (∀ c ∈ C, ∃ y : X, c = orbit K y) ∧ (C : Set (Set X)).PairwiseDisjoint id ∧
      f = fun a => ∑ c ∈ C, c.indicator f a := by
  classical
  have hcello : ∀ y : X, IsOpen (orbit K y) := fun y => isOpen_orbit_of_isOpenMap K hKo y (hopen y)
  have hcover : tsupport f ⊆ ⋃ y : X, orbit K y := fun a _ => Set.mem_iUnion.mpr ⟨a, mem_orbit_self a⟩
  obtain ⟨t, ht⟩ := hfc.isCompact.elim_finite_subcover (fun y : X => orbit K y) hcello hcover
  set C : Finset (Set X) := t.image (fun y => orbit K y) with hC
  have hdisj : (C : Set (Set X)).PairwiseDisjoint id := by
    intro c hc d hd hcd
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hc)
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hd)
    rcases orbit_eq_or_disjoint K y z with h | h
    · exact absurd h hcd
    · exact h
  refine ⟨C, ?_, hdisj, ?_⟩
  · intro c hc
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨y, rfl⟩
  · have hsum := Finset.indicator_biUnion C id (f := f) hdisj
    funext a
    have ha : f a = (⋃ c ∈ C, id c).indicator f a := by
      by_cases hmem : a ∈ ⋃ c ∈ C, id c
      · rw [Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hmem]
        by_contra hne
        apply hmem
        have hsupp : a ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr hne)
        obtain ⟨y, hy, hay⟩ := Set.mem_iUnion₂.mp (ht hsupp)
        exact Set.mem_iUnion₂.mpr ⟨orbit K y, Finset.mem_image_of_mem (fun y => orbit K y) hy, hay⟩
    exact ha.trans (congrFun hsum a)

private theorem indicator_orbit_eq_smul_indicator_one {R : Type*} [Semiring R] (K : Subgroup G) (f : X → R)
    (hf : ∀ k ∈ K, ∀ a : X, f (k • a) = f a) (y : X) :
    (orbit K y).indicator f = f y • (orbit K y).indicator (1 : X → R) := by
  funext a
  by_cases ha : a ∈ orbit K y
  · rw [Set.indicator_of_mem ha, Pi.smul_apply, Set.indicator_of_mem ha, Pi.one_apply, smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := ha
    exact hf k k.2 y
  · rw [Set.indicator_of_notMem ha, Pi.smul_apply, Set.indicator_of_notMem ha, smul_zero]

end HomogeneousCells

end LadderFurniture

section Ladder

namespace HomogeneousCells

open MulAction Set Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {X : Type*} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

private theorem isCompact_isOpen_inf [ContinuousMul G] {K₁ K₂ : Subgroup G} (hK₁c : IsCompact (K₁ : Set G))
    (hK₁o : IsOpen (K₁ : Set G)) (hK₂o : IsOpen (K₂ : Set G)) :
    IsCompact ((K₁ ⊓ K₂ : Subgroup G) : Set G) ∧ IsOpen ((K₁ ⊓ K₂ : Subgroup G) : Set G) := by
  have ho : IsOpen ((K₁ ⊓ K₂ : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact hK₁o.inter hK₂o
  refine ⟨hK₁c.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) ?_, ho⟩
  rw [Subgroup.coe_inf]
  exact Set.inter_subset_left

private theorem exists_pos_rat_apply_indicator_orbit_eq_mul [ContinuousMul G] {R : Type*} [Field R] [CharZero R]
    (K₁ K₂ : Subgroup G) (hK₁c : IsCompact (K₁ : Set G)) (hK₁o : IsOpen (K₁ : Set G))
    (hK₂c : IsCompact (K₂ : Set G)) (hK₂o : IsOpen (K₂ : Set G))
    (hopen : ∀ y : X, IsOpenMap fun g : G => g • y) (x : X) (μ : (X → R) →ₗ[R] R)
    (hμ : ∀ g : G, ∀ A : Set X, IsCompact A → IsOpen A → μ ((g • A).indicator 1) = μ (A.indicator 1)) :
    ∃ q : ℚ, 0 < q ∧
      μ ((orbit K₁ x).indicator 1) = (q : R) * μ ((orbit K₂ x).indicator 1) := by
  set H : Subgroup G := K₁ ⊓ K₂ with hH
  obtain ⟨hHc, hHo⟩ := isCompact_isOpen_inf hK₁c hK₁o hK₂o
  have hHK₁ : H ≤ K₁ := inf_le_left
  have hHK₂ : H ≤ K₂ := inf_le_right
  have hμ' : ∀ K : Subgroup G, ∀ k ∈ K, ∀ A : Set X, IsCompact A → IsOpen A →
      μ ((k • A).indicator 1) = μ (A.indicator 1) := fun _ k _ A hAc hAo => hμ k A hAc hAo

  have hN₁o := isOpen_relCore hK₁c hHo
  have hN₁c := isCompact_relCore hK₁c hHK₁ hHo
  have hN₂o := isOpen_relCore hK₂c hHo
  have hN₂c := isCompact_relCore hK₂c hHK₂ hHo

  obtain ⟨a, ha, h₁⟩ := exists_apply_indicator_orbit_eq_mul K₁ (relCore K₁ H)
    ((relCore_le K₁ H).trans hHK₁) (fun k hk _ hn => mul_mul_inv_mem_relCore hk hn) hK₁c hN₁o hN₁c
    hopen x μ (hμ' K₁)
  obtain ⟨a', ha', h₂⟩ := exists_apply_indicator_orbit_eq_mul H (relCore K₁ H) (relCore_le K₁ H)
    (fun k hk _ hn => mul_mul_inv_mem_relCore (hHK₁ hk) hn) hHc hN₁o hN₁c hopen x μ (hμ' H)
  obtain ⟨b, hb, h₃⟩ := exists_apply_indicator_orbit_eq_mul K₂ (relCore K₂ H)
    ((relCore_le K₂ H).trans hHK₂) (fun k hk _ hn => mul_mul_inv_mem_relCore hk hn) hK₂c hN₂o hN₂c
    hopen x μ (hμ' K₂)
  obtain ⟨b', hb', h₄⟩ := exists_apply_indicator_orbit_eq_mul H (relCore K₂ H) (relCore_le K₂ H)
    (fun k hk _ hn => mul_mul_inv_mem_relCore (hHK₂ hk) hn) hHc hN₂o hN₂c hopen x μ (hμ' H)

  refine ⟨((a : ℚ) * b') / ((a' : ℚ) * b), ?_, ?_⟩
  · exact div_pos (mul_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb'))
      (mul_pos (Nat.cast_pos.mpr ha') (Nat.cast_pos.mpr hb))
  · have hcast : ((((a : ℚ) * b') / ((a' : ℚ) * b) : ℚ) : R) = ((a : R) * b') / ((a' : R) * b) := by
      rw [Rat.cast_div, Rat.cast_mul, Rat.cast_mul, Rat.cast_natCast, Rat.cast_natCast, Rat.cast_natCast,
        Rat.cast_natCast]
    have ha'0 : (a' : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp ha')
    have hb0 : (b : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hb)
    rw [hcast, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero ha'0 hb0)]
    linear_combination ((a' : R) * b) * h₁ - ((a : R) * b) * h₂ + ((a : R) * b) * h₄ - ((a : R) * b') * h₃

private theorem apply_indicator_orbit_smul_eq [ContinuousMul G] {R : Type*} [Semiring R] (K : Subgroup G)
    (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (hopen : ∀ y : X, IsOpenMap fun g : G => g • y) (g : G) (x : X) (μ : (X → R) →ₗ[R] R)
    (hμ : ∀ g : G, ∀ A : Set X, IsCompact A → IsOpen A → μ ((g • A).indicator 1) = μ (A.indicator 1)) :
    μ ((orbit K (g • x)).indicator 1) = μ ((orbit (conjSubgroup g K) x).indicator 1) := by
  rw [orbit_smul_eq_smul_orbit_conjSubgroup]
  exact hμ g _ (isCompact_orbit_of_isCompact _ (isCompact_conjSubgroup g hKc) x)
    (isOpen_orbit_of_isOpenMap _ (isOpen_conjSubgroup g hKo) x (hopen x))

private theorem exists_pos_rat_apply_indicator_orbit_eq_mul_base [IsPretransitive G X] [ContinuousMul G]
    {R : Type*} [Field R] [CharZero R] (K₀ : Subgroup G) (hK₀c : IsCompact (K₀ : Set G))
    (hK₀o : IsOpen (K₀ : Set G)) (x₀ : X) (K : Subgroup G) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (hopen : ∀ y : X, IsOpenMap fun g : G => g • y) (y : X)
    (μ : (X → R) →ₗ[R] R)
    (hμ : ∀ g : G, ∀ A : Set X, IsCompact A → IsOpen A → μ ((g • A).indicator 1) = μ (A.indicator 1)) :
    ∃ q : ℚ, 0 < q ∧ μ ((orbit K y).indicator 1) = (q : R) * μ ((orbit K₀ x₀).indicator 1) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (M := G) x₀ y
  rw [apply_indicator_orbit_smul_eq K hKc hKo hopen g x₀ μ hμ]
  exact exists_pos_rat_apply_indicator_orbit_eq_mul (conjSubgroup g K) K₀ (isCompact_conjSubgroup g hKc)
    (isOpen_conjSubgroup g hKo) hK₀c hK₀o hopen x₀ μ hμ

private theorem exists_subgroup_finset_eq_sum_indicator [ContinuousMul G] {R : Type*} [AddCommMonoid R]
    (hbasis : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ (K : Set G) ⊆ U)
    (hopen : ∀ y : X, IsOpenMap fun g : G => g • y) (K₀ : Subgroup G) (hK₀c : IsCompact (K₀ : Set G))
    (hK₀o : IsOpen (K₀ : Set G)) (f : X → R) (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ (∀ k ∈ K, ∀ a : X, f (k • a) = f a) ∧
      ∃ C : Finset (Set X), (∀ c ∈ C, ∃ y : X, c = orbit K y) ∧ f = ∑ c ∈ C, c.indicator f := by
  obtain ⟨K₁, hK₁o, hK₁inv⟩ := exists_subgroup_forall_smul_apply_eq hbasis f hf hfc
  obtain ⟨hKc, hKo⟩ := isCompact_isOpen_inf hK₀c hK₀o hK₁o
  refine ⟨K₀ ⊓ K₁, hKc, hKo, fun k hk a => hK₁inv k (inf_le_right (a := K₀) hk) a, ?_⟩
  obtain ⟨C, hC, -, hsum⟩ := exists_finset_orbit_eq_sum_indicator (K₀ ⊓ K₁) hKo hopen f hfc
  refine ⟨C, hC, ?_⟩
  conv_lhs => rw [hsum]
  funext a
  rw [Finset.sum_apply]

private theorem apply_eq_zero_of_apply_indicator_orbit_eq_zero [IsPretransitive G X] [ContinuousMul G]
    {R : Type*} [Field R] [CharZero R]
    (hbasis : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ (K : Set G) ⊆ U)
    (hopen : ∀ y : X, IsOpenMap fun g : G => g • y) (K₀ : Subgroup G) (hK₀c : IsCompact (K₀ : Set G))
    (hK₀o : IsOpen (K₀ : Set G)) (x₀ : X) (μ : (X → R) →ₗ[R] R)
    (hμ : ∀ g : G, ∀ A : Set X, IsCompact A → IsOpen A → μ ((g • A).indicator 1) = μ (A.indicator 1))
    (h₀ : μ ((orbit K₀ x₀).indicator 1) = 0) (f : X → R) (hf : IsLocallyConstant f)
    (hfc : HasCompactSupport f) : μ f = 0 := by
  obtain ⟨K, hKc, hKo, hKinv, C, hC, hsum⟩ :=
    exists_subgroup_finset_eq_sum_indicator hbasis hopen K₀ hK₀c hK₀o f hf hfc
  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun c hc => ?_
  obtain ⟨y, rfl⟩ := hC c hc
  obtain ⟨q, -, hq⟩ := exists_pos_rat_apply_indicator_orbit_eq_mul_base K₀ hK₀c hK₀o x₀ K hKc hKo hopen y μ hμ
  rw [indicator_orbit_eq_smul_indicator_one K f hKinv y, map_smul, hq, h₀, mul_zero, smul_zero]

private theorem exists_pos_rat_apply_indicator_eq [IsPretransitive G X] [ContinuousMul G] [T2Space X]
    {R : Type*} [Field R] [CharZero R]
    (hbasis : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ (K : Set G) ⊆ U)
    (hopen : ∀ y : X, IsOpenMap fun g : G => g • y) (K₀ : Subgroup G) (hK₀c : IsCompact (K₀ : Set G))
    (hK₀o : IsOpen (K₀ : Set G)) (x₀ : X) (μ : (X → R) →ₗ[R] R)
    (hμ : ∀ g : G, ∀ A : Set X, IsCompact A → IsOpen A → μ ((g • A).indicator 1) = μ (A.indicator 1))
    (h₁ : μ ((orbit K₀ x₀).indicator 1) = 1) (A : Set X) (hAne : A.Nonempty) (hAc : IsCompact A)
    (hAo : IsOpen A) : ∃ q : ℚ, 0 < q ∧ μ (A.indicator 1) = (q : R) := by
  classical
  set f : X → R := A.indicator 1 with hfdef

  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ A
    · refine ⟨A, hAo, hx, fun x' hx' => ?_⟩
      simp only [hfdef, Set.indicator_of_mem hx', Set.indicator_of_mem hx, Pi.one_apply]
    · refine ⟨Aᶜ, hAc.isClosed.isOpen_compl, hx, fun x' hx' => ?_⟩
      simp only [hfdef, Set.indicator_of_notMem (Set.notMem_of_mem_compl hx'), Set.indicator_of_notMem hx]
  have hfc : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact hAc Set.support_indicator_subset
  obtain ⟨K, hKc, hKo, hKinv, C, hC, hsum⟩ :=
    exists_subgroup_finset_eq_sum_indicator hbasis hopen K₀ hK₀c hK₀o f hf hfc
  haveI : Nonempty X := ⟨hAne.some⟩
  choose! y hy using hC

  have hcell : ∀ c ∈ C, ∃ q : ℚ, 0 < q ∧ μ ((orbit K (y c)).indicator 1) = (q : R) := by
    intro c hc
    obtain ⟨q, hq, hqeq⟩ :=
      exists_pos_rat_apply_indicator_orbit_eq_mul_base K₀ hK₀c hK₀o x₀ K hKc hKo hopen (y c) μ hμ
    exact ⟨q, hq, by rw [hqeq, h₁, mul_one]⟩
  choose! q hqpos hqeq using hcell

  set e : Set X → ℚ := fun c => if y c ∈ A then 1 else 0 with hedef
  have hcoef : ∀ c ∈ C, f (y c) = ((e c : ℚ) : R) := by
    intro c _
    by_cases hyc : y c ∈ A
    · simp only [hfdef, hedef, Set.indicator_of_mem hyc, Pi.one_apply, if_pos hyc, Rat.cast_one]
    · simp only [hfdef, hedef, Set.indicator_of_notMem hyc, if_neg hyc, Rat.cast_zero]
  refine ⟨∑ c ∈ C, e c * q c, ?_, ?_⟩
  ·
    obtain ⟨a, ha⟩ := hAne
    have hfa : f a ≠ 0 := by
      rw [hfdef, Set.indicator_of_mem ha, Pi.one_apply]
      exact one_ne_zero
    have hsum_a : f a = ∑ c ∈ C, c.indicator f a := by
      conv_lhs => rw [hsum]
      rw [Finset.sum_apply]
    rw [hsum_a] at hfa
    obtain ⟨c, hc, hca⟩ := Finset.exists_ne_zero_of_sum_ne_zero hfa
    have hac : a ∈ c := by
      by_contra hnot
      exact hca (Set.indicator_of_notMem hnot f)
    have hyc : y c ∈ A := by
      rw [hy c hc] at hac
      obtain ⟨k, hk⟩ := hac
      by_contra hnot
      have h1 : f a = 1 := by
        rw [hfdef, Set.indicator_of_mem ha, Pi.one_apply]
      have hk' : (k : G) • y c = a := hk
      have h2 : f a = 0 := by
        rw [← hk', hKinv k k.2, hfdef, Set.indicator_of_notMem hnot]
      exact one_ne_zero (h1.symm.trans h2)
    refine Finset.sum_pos' (fun d hd => ?_) ⟨c, hc, ?_⟩
    · by_cases hyd : y d ∈ A
      · simp only [hedef, if_pos hyd, one_mul]
        exact (hqpos d hd).le
      · simp only [hedef, if_neg hyd, zero_mul, le_refl]
    · simp only [hedef, if_pos hyc, one_mul]
      exact hqpos c hc
  · rw [hsum, map_sum, Rat.cast_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hcind : c.indicator f = f (y c) • c.indicator (1 : X → R) := by
      have h := indicator_orbit_eq_smul_indicator_one K f hKinv (y c)
      rwa [← hy c hc] at h
    have hq : μ (c.indicator 1) = (q c : R) := by
      have h := hqeq c hc
      rwa [← hy c hc] at h
    rw [hcind, map_smul, hcoef c hc, hq, smul_eq_mul, Rat.cast_mul]

private theorem exists_pos_real_apply_indicator_eq [IsPretransitive G X] [ContinuousMul G] [T2Space X]
    (hbasis : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ (K : Set G) ⊆ U)
    (hopen : ∀ y : X, IsOpenMap fun g : G => g • y) (K₀ : Subgroup G) (hK₀c : IsCompact (K₀ : Set G))
    (hK₀o : IsOpen (K₀ : Set G)) (x₀ : X) (μ : (X → ℂ) →ₗ[ℂ] ℂ)
    (hμ : ∀ g : G, ∀ A : Set X, IsCompact A → IsOpen A → μ ((g • A).indicator 1) = μ (A.indicator 1))
    (h₁ : μ ((orbit K₀ x₀).indicator 1) = 1) (A : Set X) (hAne : A.Nonempty) (hAc : IsCompact A)
    (hAo : IsOpen A) : ∃ r : ℝ, 0 < r ∧ μ (A.indicator 1) = (r : ℂ) := by
  obtain ⟨q, hq, hμA⟩ :=
    exists_pos_rat_apply_indicator_eq hbasis hopen K₀ hK₀c hK₀o x₀ μ hμ h₁ A hAne hAc hAo
  exact ⟨(q : ℝ), Rat.cast_pos.mpr hq, by rw [hμA, Complex.ofReal_ratCast]⟩

end HomogeneousCells

end Ladder

section PerOrbitInput

namespace InvariantFunctional

open MulAction Set Pointwise HomogeneousCells

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MulAction G X] [ContinuousSMul G X] [IsPretransitive G X]

private theorem comp_eq_self_of_indicatorAction
    (hbasis : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ (K : Set G) ⊆ U)
    (hopen : ∀ y : X, IsOpenMap fun g : G => g • y) (K₀ : Subgroup G) (hK₀c : IsCompact (K₀ : Set G))
    (hK₀o : IsOpen (K₀ : Set G)) (x₀ : X) {S : Submodule ℂ (X → ℂ)} {act : G → Module.End ℂ S}
    (hS : IndicatorAction S act) (hS' : ∀ f ∈ S, IsLocallyConstant f ∧ HasCompactSupport f)
    (T : Module.End ℂ S) (τ : G → G) (hTT : T ∘ₗ T = LinearMap.id) (hnorm : ∀ g, T ∘ₗ act g = act (τ g) ∘ₗ T)
    (A' : Set X) (hA'n : A'.Nonempty) (hA'c : IsCompact A') (hA'o : IsOpen A')
    (hTb : ((T ⟨(orbit K₀ x₀).indicator 1, hS.indicator_mem _ (isCompact_orbit_of_isCompact K₀ hK₀c x₀)
      (isOpen_orbit_of_isOpenMap K₀ hK₀o x₀ (hopen x₀))⟩ : S) : X → ℂ) = A'.indicator 1)
    (μ : Module.Dual ℂ S) (hμ : ∀ g, μ ∘ₗ act g = μ) : μ ∘ₗ T = μ := by
  have hbc : IsCompact (orbit K₀ x₀) := isCompact_orbit_of_isCompact K₀ hK₀c x₀
  have hbo : IsOpen (orbit K₀ x₀) := isOpen_orbit_of_isOpenMap K₀ hK₀o x₀ (hopen x₀)
  refine comp_eq_self_of_forall_eq_zero_of_forall_pos act T τ hTT hnorm
    ⟨(orbit K₀ x₀).indicator 1, hS.indicator_mem _ hbc hbo⟩ ?_ ?_ μ hμ
  ·
    intro ν hν hb
    refine hS.dual_eq_zero (orbit K₀ x₀) hbc hbo ?_ ν hν hb
    intro ν' hν'inv hν'0 f hf
    exact apply_eq_zero_of_apply_indicator_orbit_eq_zero hbasis hopen K₀ hK₀c hK₀o x₀ ν' hν'inv hν'0 f
      (hS' f hf).1 (hS' f hf).2
  ·
    intro ν hν hb
    have hT : T ⟨(orbit K₀ x₀).indicator 1, hS.indicator_mem _ hbc hbo⟩ =
        ⟨A'.indicator 1, hS.indicator_mem A' hA'c hA'o⟩ := Subtype.ext hTb
    rw [hT]
    refine hS.exists_pos_apply_indicator (orbit K₀ x₀) hbc hbo ?_ ν hν hb A' hA'n hA'c hA'o
    intro ν' hν'inv hν'1 A hAn hAc hAo
    exact exists_pos_real_apply_indicator_eq hbasis hopen K₀ hK₀c hK₀o x₀ ν' hν'inv hν'1 A hAn hAc hAo

end InvariantFunctional

end PerOrbitInput

section PullbackInvolution

namespace InvariantFunctional

open MulAction

section Sets

variable {X : Type*} (θ : X → X) (hθθ : Function.Involutive θ)

include hθθ in
private theorem preimage_nonempty {B : Set X} (hB : B.Nonempty) : (θ ⁻¹' B).Nonempty := by
  obtain ⟨b, hb⟩ := hB
  refine ⟨θ b, ?_⟩
  rw [Set.mem_preimage, hθθ b]
  exact hb

include hθθ in
private theorem preimage_eq_image (B : Set X) : θ ⁻¹' B = θ '' B := by
  ext y
  constructor
  · intro hy
    exact ⟨θ y, hy, hθθ y⟩
  · rintro ⟨b, hb, rfl⟩
    rw [Set.mem_preimage, hθθ b]
    exact hb

end Sets

section Pullback

variable {X : Type*} [TopologicalSpace X] {R : Type*} [Field R]
variable (θ : X → X) (hθc : Continuous θ) (hθθ : Function.Involutive θ)

private def involutionHomeomorph : X ≃ₜ X where
  toEquiv := hθθ.toPerm θ
  continuous_toFun := hθc
  continuous_invFun := hθc

private theorem involutionHomeomorph_apply (x : X) : involutionHomeomorph θ hθc hθθ x = θ x :=
  rfl

include hθc hθθ in
private theorem comp_mem_testSubmodule {f : X → R} (hf : f ∈ testSubmodule X R) : (f ∘ θ) ∈ testSubmodule X R :=
  ⟨hf.1.comp_continuous hθc, hf.2.comp_homeomorph (involutionHomeomorph θ hθc hθθ)⟩

variable (R) in

private def pullback : Module.End R (testSubmodule X R) where
  toFun f := ⟨(f : X → R) ∘ θ, comp_mem_testSubmodule θ hθc hθθ f.2⟩
  map_add' _ _ := Subtype.ext (funext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (funext fun _ => rfl)

private theorem pullback_apply (f : testSubmodule X R) (x : X) :
    ((pullback R θ hθc hθθ f : testSubmodule X R) : X → R) x = (f : X → R) (θ x) :=
  rfl

private theorem pullback_comp_pullback : pullback R θ hθc hθθ ∘ₗ pullback R θ hθc hθθ = LinearMap.id :=
  LinearMap.ext fun f => Subtype.ext (funext fun x =>
    show (f : X → R) (θ (θ x)) = (f : X → R) x from congrArg (f : X → R) (hθθ x))

private theorem coe_pullback_indicator (B : Set X) (hB : B.indicator (1 : X → R) ∈ testSubmodule X R) :
    ((pullback R θ hθc hθθ ⟨B.indicator 1, hB⟩ : testSubmodule X R) : X → R) = (θ ⁻¹' B).indicator 1 := by
  funext x
  rw [pullback_apply]
  by_cases h : θ x ∈ B
  · simp only [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_preimage.2 h), Pi.one_apply]
  · simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (Set.mem_preimage.1 h'))]

include hθc hθθ in
private theorem _root_.InvariantFunctional.isCompact_preimage {B : Set X} (hB : IsCompact B) : IsCompact (θ ⁻¹' B) := by
  rw [preimage_eq_image θ hθθ]
  exact hB.image hθc

p2m_export "InvariantFunctional" "isCompact_preimage"
include hθc in
private theorem _root_.InvariantFunctional.isOpen_preimage {B : Set X} (hB : IsOpen B) : IsOpen (θ ⁻¹' B) :=
  hB.preimage hθc

p2m_export "InvariantFunctional" "isOpen_preimage"
end Pullback

section Normalise

variable {G : Type*} [Group G] [TopologicalSpace G] {X : Type*} [TopologicalSpace X] [MulAction G X]
  [ContinuousSMul G X] {R : Type*} [Field R]

private theorem
    pullback_comp_translationAction (θ : X → X) (hθc : Continuous θ) (hθθ : Function.Involutive θ) (τ : G → G)
    (hτ : ∀ g : G, τ g⁻¹ = (τ g)⁻¹) (hττ : ∀ g : G, τ (τ g) = g) (hθ : ∀ (g : G) (x : X), θ (g • x) = τ g • θ x)
    (g : G) :
    pullback R θ hθc hθθ ∘ₗ translationAction G X R g = translationAction G X R (τ g) ∘ₗ pullback R θ hθc hθθ :=
  LinearMap.ext fun f => Subtype.ext (funext fun x => by
    show (f : X → R) (g⁻¹ • θ x) = (f : X → R) (θ ((τ g)⁻¹ • x))
    rw [hθ, hτ, hττ])

end Normalise

section Conclusion

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MulAction G X] [ContinuousSMul G X] [IsPretransitive G X]

private theorem comp_pullback_eq_self
    (hbasis : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ (K : Set G) ⊆ U)
    (hopen : ∀ y : X, IsOpenMap fun g : G => g • y) (K₀ : Subgroup G) (hK₀c : IsCompact (K₀ : Set G))
    (hK₀o : IsOpen (K₀ : Set G)) (x₀ : X) (θ : X → X) (hθc : Continuous θ) (hθθ : Function.Involutive θ)
    (τ : G → G) (hτ : ∀ g : G, τ g⁻¹ = (τ g)⁻¹) (hττ : ∀ g : G, τ (τ g) = g)
    (hθ : ∀ (g : G) (x : X), θ (g • x) = τ g • θ x) (μ : Module.Dual ℂ (testSubmodule X ℂ))
    (hμ : ∀ g : G, μ ∘ₗ translationAction G X ℂ g = μ) : μ ∘ₗ pullback ℂ θ hθc hθθ = μ :=
  comp_eq_self_of_indicatorAction hbasis hopen K₀ hK₀c hK₀o x₀ (indicatorAction_translationAction G X ℂ)
    forall_mem_testSubmodule (pullback ℂ θ hθc hθθ) τ (pullback_comp_pullback θ hθc hθθ)
    (pullback_comp_translationAction θ hθc hθθ τ hτ hττ hθ) (θ ⁻¹' orbit K₀ x₀)
    (preimage_nonempty θ hθθ ⟨x₀, mem_orbit_self x₀⟩)
    (isCompact_preimage θ hθc hθθ (HomogeneousCells.isCompact_orbit_of_isCompact K₀ hK₀c x₀))
    (isOpen_preimage θ hθc (HomogeneousCells.isOpen_orbit_of_isOpenMap K₀ hK₀o x₀ (hopen x₀)))
    (coe_pullback_indicator θ hθc hθθ (orbit K₀ x₀) _) μ hμ

end Conclusion

end InvariantFunctional

end PullbackInvolution

section AmbientActions

namespace InvariantFunctional

open Set Topology

section Indicator

variable {X Y : Type*} (R : Type*) [Semiring R]

private theorem funLeft_indicator_preimage (σ : X → X) (φ : X → Y) (hφ : ∀ x, φ (σ x) = φ x) (V : Set Y) (f : X → R) :
    LinearMap.funLeft R R σ ((φ ⁻¹' V).indicator f) = (φ ⁻¹' V).indicator (LinearMap.funLeft R R σ f) := by
  funext x
  classical
  simp only [LinearMap.funLeft_apply, indicator_apply, mem_preimage, hφ]

private theorem exists_isClopen_subset_of_isTopologicalBasis [TopologicalSpace Y]
    (hb : TopologicalSpace.IsTopologicalBasis {s : Set Y | IsClopen s}) (y : Y) (U : Set Y) (hU : IsOpen U)
    (hy : y ∈ U) : ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ V ⊆ U := by
  obtain ⟨V, hV, hyV, hVU⟩ := hb.exists_subset_of_mem_open hy hU
  exact ⟨V, hV, hyV, hVU⟩

end Indicator

section Test

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {R : Type*} [Field R]

private theorem indicator_preimage_mem_testSubmodule {φ : X → Y} (hφ : Continuous φ) {V : Set Y} (hV : IsClopen V)
    {f : X → R} (hf : f ∈ testSubmodule X R) : (φ ⁻¹' V).indicator f ∈ testSubmodule X R := by
  have hW : IsClopen (φ ⁻¹' V) := hV.preimage hφ
  refine ⟨?_, hf.2.mono fun x hx => ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ φ ⁻¹' V
    · obtain ⟨U, hU, hxU, hc⟩ := (IsLocallyConstant.iff_exists_open _).1 hf.1 x
      refine ⟨U ∩ φ ⁻¹' V, hU.inter hW.isOpen, ⟨hxU, hx⟩, fun y hy => ?_⟩
      rw [indicator_of_mem hy.2, indicator_of_mem hx, hc y hy.1]
    · exact ⟨(φ ⁻¹' V)ᶜ, hW.compl.isOpen, hx, fun y hy => by rw [indicator_of_notMem hy, indicator_of_notMem hx]⟩
  · rw [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    by_cases hxs : x ∈ φ ⁻¹' V
    · rw [indicator_of_mem hxs, h0]
    · rw [indicator_of_notMem hxs]

private theorem funLeft_mem_testSubmodule (θ : X → X) (hθc : Continuous θ) (hθθ : Function.Involutive θ) {f : X → R}
    (hf : f ∈ testSubmodule X R) : LinearMap.funLeft R R θ f ∈ testSubmodule X R :=
  comp_mem_testSubmodule θ hθc hθθ hf

private theorem coe_pullback_eq_funLeft (θ : X → X) (hθc : Continuous θ) (hθθ : Function.Involutive θ)
    (f : testSubmodule X R) :
    ((pullback R θ hθc hθθ f : testSubmodule X R) : X → R) = LinearMap.funLeft R R θ f :=
  rfl

private theorem comp_pullback_eq_iff (θ : X → X) (hθc : Continuous θ) (hθθ : Function.Involutive θ)
    (T : Module.Dual R (X → R)) (μ : Module.Dual R (testSubmodule X R))
    (hT : ∀ (f : X → R) (hf : f ∈ testSubmodule X R), T f = μ ⟨f, hf⟩) :
    μ ∘ₗ pullback R θ hθc hθθ = μ ↔ ∀ f ∈ testSubmodule X R, T (LinearMap.funLeft R R θ f) = T f := by
  constructor
  · intro h f hf
    rw [hT f hf, hT _ (funLeft_mem_testSubmodule θ hθc hθθ hf)]
    exact LinearMap.congr_fun h ⟨f, hf⟩
  · intro h
    ext f
    rw [LinearMap.comp_apply]
    have h' := h f f.2
    rw [hT _ f.2, hT _ (funLeft_mem_testSubmodule θ hθc hθθ f.2)] at h'
    exact h'

end Test

section Action

variable {G : Type*} [Group G] [TopologicalSpace G] {X : Type*} [TopologicalSpace X] [MulAction G X]
  [ContinuousSMul G X] {R : Type*} [Field R]

private theorem funLeft_inv_smul_mem_testSubmodule (g : G) {f : X → R} (hf : f ∈ testSubmodule X R) :
    LinearMap.funLeft R R (fun x => g⁻¹ • x) f ∈ testSubmodule X R :=
  comp_inv_smul_mem_testSubmodule g hf

private theorem coe_translationAction_eq_funLeft (g : G) (f : testSubmodule X R) :
    ((translationAction G X R g f : testSubmodule X R) : X → R) = LinearMap.funLeft R R (fun x => g⁻¹ • x) f :=
  rfl

private theorem apply_funLeft_inv_smul_eq (T : Module.Dual R (X → R)) (μ : Module.Dual R (testSubmodule X R))
    (hT : ∀ (f : X → R) (hf : f ∈ testSubmodule X R), T f = μ ⟨f, hf⟩) (g : G)
    (hμ : μ ∘ₗ translationAction G X R g = μ) {f : X → R} (hf : f ∈ testSubmodule X R) :
    T (LinearMap.funLeft R R (fun x => g⁻¹ • x) f) = T f := by
  rw [hT f hf, hT _ (funLeft_inv_smul_mem_testSubmodule g hf)]
  exact LinearMap.congr_fun hμ ⟨f, hf⟩

end Action

end InvariantFunctional

end AmbientActions

section BiInvarianceSubgroup

open Topology

namespace HomogeneousCells

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {Y : Type*} [Zero Y]

private theorem exists_subgroup_forall_apply_mul_eq
    (hbasis : ∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ (K : Set G) ⊆ U)
    (f : G → Y) (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ k ∈ K, ∀ x : G, f (x * k) = f x := by
  obtain ⟨K, hKo, hK⟩ := exists_subgroup_forall_smul_apply_eq hbasis (f ∘ Homeomorph.inv G)
    (hf.comp_continuous (Homeomorph.inv G).continuous) (hfc.comp_homeomorph (Homeomorph.inv G))
  refine ⟨K, hKo, fun k hk x => ?_⟩
  have h := hK k⁻¹ (K.inv_mem hk) x⁻¹
  change f (k⁻¹ * x⁻¹)⁻¹ = f x⁻¹⁻¹ at h
  simp only [mul_inv_rev, inv_inv] at h
  exact h

private theorem exists_compact_open_subgroup_forall_apply_eq
    (hK : ∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧
      (K : Set G) ⊆ U)
    (f : G → Y) (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) (g : G) :
    ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ ∀ k ∈ K,
      (∀ x : G, f (k * x) = f x ∧ f (x * k) = f x) ∧
      (∀ x : G, f (g⁻¹ * k * g * x) = f x ∧ f (x * (g⁻¹ * k * g)) = f x) ∧
      (∀ x : G, f (g * k * g⁻¹ * x) = f x ∧ f (x * (g * k * g⁻¹)) = f x) := by
  have hbasis : ∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ (K : Set G) ⊆ U := by
    intro U hU
    obtain ⟨K, _, hKo, hKU⟩ := hK U hU
    exact ⟨K, hKo, hKU⟩
  obtain ⟨L, hLo, hL⟩ := exists_subgroup_forall_smul_apply_eq hbasis f hf hfc
  obtain ⟨R, hRo, hR⟩ := exists_subgroup_forall_apply_mul_eq hbasis f hf hfc
  have hbi : ∀ u ∈ L ⊓ R, ∀ x : G, f (u * x) = f x ∧ f (x * u) = f x := fun u hu x =>
    ⟨hL u (Subgroup.mem_inf.mp hu).1 x, hR u (Subgroup.mem_inf.mp hu).2 x⟩
  have hUo : IsOpen ((L ⊓ R : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact hLo.inter hRo
  have hc₁ : Continuous fun k : G => g⁻¹ * k * g := (continuous_const.mul continuous_id).mul continuous_const
  have hc₂ : Continuous fun k : G => g * k * g⁻¹ := (continuous_const.mul continuous_id).mul continuous_const
  have hNo : IsOpen (((L ⊓ R : Subgroup G) : Set G) ∩ (fun k : G => g⁻¹ * k * g) ⁻¹' (L ⊓ R : Subgroup G) ∩
      (fun k : G => g * k * g⁻¹) ⁻¹' (L ⊓ R : Subgroup G)) :=
    (hUo.inter (hUo.preimage hc₁)).inter (hUo.preimage hc₂)
  have h1N : (1 : G) ∈ ((L ⊓ R : Subgroup G) : Set G) ∩ (fun k : G => g⁻¹ * k * g) ⁻¹' (L ⊓ R : Subgroup G) ∩
      (fun k : G => g * k * g⁻¹) ⁻¹' (L ⊓ R : Subgroup G) := by
    refine ⟨⟨(L ⊓ R).one_mem, ?_⟩, ?_⟩
    · show g⁻¹ * 1 * g ∈ L ⊓ R
      rw [mul_one, inv_mul_cancel]
      exact (L ⊓ R).one_mem
    · show g * 1 * g⁻¹ ∈ L ⊓ R
      rw [mul_one, mul_inv_cancel]
      exact (L ⊓ R).one_mem
  obtain ⟨K, hKc, hKo, hKN⟩ := hK _ (hNo.mem_nhds h1N)
  refine ⟨K, hKc, hKo, fun k hk => ?_⟩
  have hkN := hKN hk
  exact ⟨hbi k hkN.1.1, hbi (g⁻¹ * k * g) hkN.1.2, hbi (g * k * g⁻¹) hkN.2⟩

end HomogeneousCells

end BiInvarianceSubgroup

section ConjOrbitInstances

namespace ConjOrbit

section Topology

variable {H : Type*} [Group H] [TopologicalSpace H]

private scoped instance instTopologicalSpace : TopologicalSpace (ConjAct H) := ‹TopologicalSpace H›

private scoped instance instIsTopologicalGroup [IsTopologicalGroup H] : IsTopologicalGroup (ConjAct H) :=
  inferInstanceAs (IsTopologicalGroup H)

private scoped instance instSigmaCompactSpace [SigmaCompactSpace H] : SigmaCompactSpace (ConjAct H) :=
  inferInstanceAs (SigmaCompactSpace H)

private scoped instance instContinuousSMul [IsTopologicalGroup H] : ContinuousSMul (ConjAct H) H where
  continuous_smul := by
    show Continuous fun p : ConjAct H × H =>
      ConjAct.ofConjAct p.1 * p.2 * (ConjAct.ofConjAct p.1)⁻¹
    have h1 : Continuous fun p : ConjAct H × H => ConjAct.ofConjAct p.1 := continuous_fst
    have h2 : Continuous fun p : ConjAct H × H => p.2 := continuous_snd
    exact (h1.mul h2).mul h1.inv

private scoped instance instContinuousSMulOrbit [IsTopologicalGroup H] (h : H) :
    ContinuousSMul (ConjAct H) (MulAction.orbit (ConjAct H) h) where
  continuous_smul := by
    apply continuous_induced_rng.2
    show Continuous fun p : ConjAct H × MulAction.orbit (ConjAct H) h => p.1 • (p.2 : H)
    exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)

private theorem baireSpace_orbit_of_isLocallyClosed [T2Space H] [LocallyCompactSpace H] (h : H)
    (hlc : IsLocallyClosed (MulAction.orbit (ConjAct H) h : Set H)) :
    BaireSpace (MulAction.orbit (ConjAct H) h) := by
  haveI : LocallyCompactSpace (MulAction.orbit (ConjAct H) h) := hlc.locallyCompactSpace
  infer_instance

end Topology

section Conjugacy

private theorem mem_orbit_iff_isConj {G : Type*} [Group G] (g g' : G) :
    g' ∈ MulAction.orbit (ConjAct G) g ↔ IsConj g g' := by
  rw [MulAction.mem_orbit_iff, isConj_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨ConjAct.ofConjAct x, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨ConjAct.toConjAct c, rfl⟩

private theorem isConj_val_iff {M : Type*} [Monoid M] (g g' : Mˣ) :
    IsConj (g : M) (g' : M) ↔ IsConj g g' := by
  constructor
  · rintro ⟨c, hc⟩
    have h : SemiconjBy c g g' := SemiconjBy.units_val_iff.1 hc
    rw [isConj_iff]
    exact ⟨c, by rw [h.eq, mul_inv_cancel_right]⟩
  · intro hc
    exact (Units.coeHom M).map_isConj hc

private theorem orbit_eq_setOf_isConj_val {M : Type*} [Monoid M] (g : Mˣ) :
    (MulAction.orbit (ConjAct Mˣ) g : Set Mˣ) = {g' : Mˣ | IsConj (g : M) (g' : M)} := by
  ext g'
  rw [Set.mem_setOf_eq, isConj_val_iff, mem_orbit_iff_isConj]

end Conjugacy

end ConjOrbit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit"

end ConjOrbitInstances
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit"

section SigmaCompactUnits

open Topology

namespace SigmaCompactUnits

private theorem sigmaCompactSpace_of_compact_of_forall_exists_mem_image {X : Type*} [TopologicalSpace X]
    {C : Set X} (hC : IsCompact C) (f : ℕ → X → X) (hf : ∀ n, Continuous (f n))
    (hcov : ∀ x, ∃ n, x ∈ f n '' C) : SigmaCompactSpace X := by
  refine SigmaCompactSpace.of_countable (Set.range fun n => f n '' C) (Set.countable_range _) ?_ ?_
  · rintro _ ⟨n, rfl⟩
    exact hC.image (hf n)
  · rw [Set.sUnion_range]
    exact Set.iUnion_eq_univ_iff.2 hcov

private scoped instance instSigmaCompactSpaceMatrix {m n R : Type*} [Finite m] [Finite n] [TopologicalSpace R]
    [SigmaCompactSpace R] : SigmaCompactSpace (Matrix m n R) :=
  inferInstanceAs (SigmaCompactSpace (m → n → R))

private theorem sigmaCompactSpace_mulOpposite {M : Type*} [TopologicalSpace M] [SigmaCompactSpace M] :
    SigmaCompactSpace Mᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace

private theorem sigmaCompactSpace_units {M : Type*} [Monoid M] [TopologicalSpace M] [T1Space M]
    [ContinuousMul M] [SigmaCompactSpace M] : SigmaCompactSpace Mˣ :=
  haveI : SigmaCompactSpace Mᵐᵒᵖ := sigmaCompactSpace_mulOpposite
  (Units.isClosedEmbedding_embedProduct (α := M)).sigmaCompactSpace

private scoped instance instSigmaCompactSpaceUnitsMatrix {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R]
    [TopologicalSpace R] [IsTopologicalSemiring R] [T2Space R] [SigmaCompactSpace R] :
    SigmaCompactSpace (Matrix n n R)ˣ :=
  sigmaCompactSpace_units

end SigmaCompactUnits
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

end SigmaCompactUnits
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

section OrbitHomeomorph

open MulAction

namespace OrbitHomeomorph

variable {G X : Type*} [Group G] [MulAction G X]

variable (G) (x : X)

private theorem ofQuotientStabilizer_comp_mk :
    ofQuotientStabilizer G x ∘ (QuotientGroup.mk : G → G ⧸ stabilizer G x) = fun g : G => g • x :=
  funext fun g => ofQuotientStabilizer_mk G x g

section Bijective

variable [IsPretransitive G X]

private theorem bijective_ofQuotientStabilizer : Function.Bijective (ofQuotientStabilizer G x) := by
  refine ⟨injective_ofQuotientStabilizer G x, fun y => ?_⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := G) x y
  exact ⟨QuotientGroup.mk g, by rw [ofQuotientStabilizer_mk, hg]⟩

end Bijective
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

section Continuous

variable [TopologicalSpace G] [TopologicalSpace X] [ContinuousSMul G X]

private theorem continuous_ofQuotientStabilizer : Continuous (ofQuotientStabilizer G x) := by
  rw [(QuotientGroup.isQuotientMap_mk (stabilizer G x)).continuous_iff, ofQuotientStabilizer_comp_mk]
  exact continuous_id.smul continuous_const

end Continuous
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

section Homeomorph

variable [TopologicalSpace G] [TopologicalSpace X] [IsTopologicalGroup G] [SigmaCompactSpace G]
  [BaireSpace X] [T2Space X] [ContinuousSMul G X] [IsPretransitive G X]

private theorem isOpenMap_ofQuotientStabilizer : IsOpenMap (ofQuotientStabilizer G x) := by
  intro U hU
  have hpre : IsOpen ((QuotientGroup.mk : G → G ⧸ stabilizer G x) ⁻¹' U) :=
    hU.preimage QuotientGroup.continuous_mk
  have himg := isOpenMap_smul_of_sigmaCompact x _ hpre
  have h : ofQuotientStabilizer G x '' U =
      (fun g : G => g • x) '' ((QuotientGroup.mk : G → G ⧸ stabilizer G x) ⁻¹' U) := by
    conv_lhs => rw [← Set.image_preimage_eq U QuotientGroup.mk_surjective]
    rw [← Set.image_comp, ofQuotientStabilizer_comp_mk]
  rw [h]
  exact himg

private noncomputable def orbitHomeomorph : G ⧸ stabilizer G x ≃ₜ X :=
  (Equiv.ofBijective _ (bijective_ofQuotientStabilizer G x)).toHomeomorphOfContinuousOpen
    (continuous_ofQuotientStabilizer G x) (isOpenMap_ofQuotientStabilizer G x)

private theorem orbitHomeomorph_apply (q : G ⧸ stabilizer G x) :
    orbitHomeomorph G x q = ofQuotientStabilizer G x q :=
  rfl

private theorem orbitHomeomorph_apply_mk (g : G) : orbitHomeomorph G x (QuotientGroup.mk g) = g • x :=
  ofQuotientStabilizer_mk G x g

private theorem orbitHomeomorph_smul (g : G) (q : G ⧸ stabilizer G x) :
    orbitHomeomorph G x (g • q) = g • orbitHomeomorph G x q :=
  ofQuotientStabilizer_smul G x g q

variable {G x}

private theorem comp_orbitHomeomorph_comp_smul {α : Type*} (f : X → α) (g : G) :
    (fun q : G ⧸ stabilizer G x => f (orbitHomeomorph G x (g • q))) =
      fun q => f (g • orbitHomeomorph G x q) := by
  funext q
  rw [orbitHomeomorph_smul]

private theorem comp_orbitHomeomorph_invariant_iff {α : Type*} (f : X → α) :
    (∀ g : G, ∀ y : X, f (g • y) = f y) ↔
      ∀ g : G, ∀ q : G ⧸ stabilizer G x, f (orbitHomeomorph G x (g • q)) = f (orbitHomeomorph G x q) := by
  constructor
  · intro hf g q
    rw [orbitHomeomorph_smul]
    exact hf g _
  · intro hf g y
    obtain ⟨q, rfl⟩ := (orbitHomeomorph G x).surjective y
    rw [← orbitHomeomorph_smul]
    exact hf g q

end Homeomorph
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

end OrbitHomeomorph
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

end OrbitHomeomorph
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

section ConjOrbitHomeomorph

open IsDedekindDomain NumberField MulAction

namespace ConjOrbit

private scoped instance instLocallyCompactSpaceMatrix {m n R : Type*} [Finite m] [Finite n] [TopologicalSpace R]
    [LocallyCompactSpace R] : LocallyCompactSpace (Matrix m n R) :=
  inferInstanceAs (LocallyCompactSpace (m → n → R))

section Generic

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SigmaCompactSpace H]

private noncomputable def conjOrbitHomeomorph (h : H) (hlc : IsLocallyClosed (orbit (ConjAct H) h : Set H)) :
    ConjAct H ⧸ stabilizer (ConjAct H) (⟨h, mem_orbit_self h⟩ : orbit (ConjAct H) h) ≃ₜ
      orbit (ConjAct H) h :=
  haveI := baireSpace_orbit_of_isLocallyClosed h hlc
  OrbitHomeomorph.orbitHomeomorph (ConjAct H) (⟨h, mem_orbit_self h⟩ : orbit (ConjAct H) h)

private theorem conjOrbitHomeomorph_apply_mk (h : H) (hlc : IsLocallyClosed (orbit (ConjAct H) h : Set H))
    (c : ConjAct H) :
    ((conjOrbitHomeomorph h hlc (QuotientGroup.mk c) : orbit (ConjAct H) h) : H) = c • h := by
  haveI := baireSpace_orbit_of_isLocallyClosed h hlc
  exact congrArg Subtype.val
    (OrbitHomeomorph.orbitHomeomorph_apply_mk (ConjAct H) (⟨h, mem_orbit_self h⟩ : orbit (ConjAct H) h) c)

end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

section LocalField

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

set_option synthInstance.maxHeartbeats 1600000 in

private noncomputable def conjOrbitHomeomorphGL (g : (Matrix (Fin 3) (Fin 3) (v.adicCompletion K))ˣ)
    (hlc : IsLocallyClosed (orbit (ConjAct (Matrix (Fin 3) (Fin 3) (v.adicCompletion K))ˣ) g :
      Set (Matrix (Fin 3) (Fin 3) (v.adicCompletion K))ˣ)) :
    ConjAct (Matrix (Fin 3) (Fin 3) (v.adicCompletion K))ˣ ⧸
        stabilizer (ConjAct (Matrix (Fin 3) (Fin 3) (v.adicCompletion K))ˣ)
          (⟨g, mem_orbit_self g⟩ : orbit (ConjAct (Matrix (Fin 3) (Fin 3) (v.adicCompletion K))ˣ) g) ≃ₜ
      orbit (ConjAct (Matrix (Fin 3) (Fin 3) (v.adicCompletion K))ˣ) g :=
  conjOrbitHomeomorph g hlc

end LocalField
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

end ConjOrbit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

end ConjOrbitHomeomorph
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

section ClopenBasis

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.localMaximalCompact3 CubicInduction.mem_localMaximalCompact3_iff CubicInduction.transposeInv3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localMaximalCompact3 mem_localMaximalCompact3_iff transposeInv3 LocalGL3"
namespace ClopenBasis
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
open Valued

open Set Topology

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued R Γ₀]

private theorem exists_isClopen_subset {x : R} {U : Set R} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set R, IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp (hU.mem_nhds hx)
  refine ⟨{y | v.restrict (y - x) < γ.1}, ?_, ?_, hγ⟩
  · exact (Valued.isClopen_ball R γ.1).preimage (continuous_id.sub continuous_const)
  · show v.restrict (x - x) < γ.1
    rw [sub_self, map_zero]
    exact zero_lt_iff.mpr γ.ne_zero

private theorem exists_isClopen_subset_pi {ι : Type*} [Finite ι] (y : ι → R) (U : Set (ι → R)) (hU : IsOpen U)
    (hy : y ∈ U) : ∃ V : Set (ι → R), IsClopen V ∧ y ∈ V ∧ V ⊆ U := by
  obtain ⟨u, hu, huU⟩ := isOpen_pi_iff'.mp hU y hy
  choose V hVc hyV hVu using fun a => exists_isClopen_subset (hu a).1 (hu a).2
  refine ⟨⋂ a, (fun z : ι → R => z a) ⁻¹' V a, isClopen_iInter_of_finite fun a => (hVc a).preimage
    (continuous_apply a), mem_iInter.mpr fun a => hyV a, fun z hz => huU (mem_univ_pi.mpr fun a => ?_)⟩
  exact hVu a (mem_iInter.mp hz a)

end LanglandsTunnell.CubicInduction.ClopenBasis
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

end ClopenBasis
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

section CongruenceSubgroups

open Filter Topology MulOpposite

namespace MatrixUnitsBasis

variable {R : Type*} {n : Type*}

private def entrySet (B : Set R) : Set (Matrix n n R) :=
  Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => B

private theorem mem_entrySet {B : Set R} {X : Matrix n n R} : X ∈ entrySet B ↔ ∀ i j, X i j ∈ B :=
  ⟨fun h i j => h i (Set.mem_univ i) j (Set.mem_univ j), fun h i _ j _ => h i j⟩

private theorem isOpen_entrySet [TopologicalSpace R] [Finite n] {B : Set R} (hB : IsOpen B) :
    IsOpen (entrySet B : Set (Matrix n n R)) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hB

private theorem isCompact_entrySet [TopologicalSpace R] {B : Set R} (hB : IsCompact B) :
    IsCompact (entrySet B : Set (Matrix n n R)) :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hB

private theorem entrySet_mono {B B' : Set R} (h : B ⊆ B') : (entrySet B : Set (Matrix n n R)) ⊆ entrySet B' := by
  intro X hX
  rw [mem_entrySet] at hX ⊢
  exact fun i j => h (hX i j)

private theorem exists_entrySet_subset_of_mem_nhds [Ring R] [TopologicalSpace R] [Finite n] {V : Set (Matrix n n R)}
    (hV : V ∈ 𝓝 (0 : Matrix n n R)) :
    ∃ B ∈ 𝓝 (0 : R), entrySet B ⊆ V := by
  have hV' : V ∈ 𝓝 (0 : n → n → R) := hV
  rw [nhds_pi] at hV'
  obtain ⟨I, -, t, ht, htV⟩ := Filter.mem_pi.1 hV'
  have ht' : ∀ i, ∃ s : n → Set R, (∀ j, s j ∈ 𝓝 (0 : R)) ∧ Set.pi Set.univ s ⊆ t i := by
    intro i
    have hi := ht i
    rw [nhds_pi] at hi
    obtain ⟨J, -, s, hs, hst⟩ := Filter.mem_pi.1 hi
    exact ⟨s, hs, fun x hx => hst fun j _ => hx j (Set.mem_univ j)⟩
  choose s hs hst using ht'
  refine ⟨⋂ i, ⋂ j, s i j, ?_, ?_⟩
  · exact Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => hs i j
  · intro X hX
    rw [mem_entrySet] at hX
    refine htV fun i _ => hst i fun j _ => ?_
    have := hX i j
    exact Set.mem_iInter.1 (Set.mem_iInter.1 this i) j

private theorem add_mem_entrySet [Ring R] (B : AddSubgroup R) {X Y : Matrix n n R} (hX : X ∈ entrySet (B : Set R))
    (hY : Y ∈ entrySet (B : Set R)) : X + Y ∈ entrySet (B : Set R) := by
  rw [mem_entrySet] at hX hY ⊢
  intro i j
  rw [Matrix.add_apply]
  exact B.add_mem (hX i j) (hY i j)

private theorem mul_mem_entrySet [Ring R] [Fintype n] (B : AddSubgroup R) (hmul : ∀ x ∈ B, ∀ y ∈ B, x * y ∈ B)
    {X Y : Matrix n n R} (hX : X ∈ entrySet (B : Set R)) (hY : Y ∈ entrySet (B : Set R)) :
    X * Y ∈ entrySet (B : Set R) := by
  rw [mem_entrySet] at hX hY ⊢
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => hmul _ (hX i k) _ (hY k j)

private theorem mul_sub_one_eq [Ring R] [Fintype n] [DecidableEq n] (X Y : Matrix n n R) :
    X * Y - 1 = (X - 1) * (Y - 1) + (X - 1) + (Y - 1) := by
  noncomm_ring

section Congruence

variable [Ring R] [Fintype n] [DecidableEq n]

private theorem mul_sub_one_mem_entrySet (B : AddSubgroup R) (hmul : ∀ x ∈ B, ∀ y ∈ B, x * y ∈ B)
    {X Y : Matrix n n R} (hX : X - 1 ∈ entrySet (B : Set R)) (hY : Y - 1 ∈ entrySet (B : Set R)) :
    X * Y - 1 ∈ entrySet (B : Set R) := by
  rw [mul_sub_one_eq]
  exact add_mem_entrySet B (add_mem_entrySet B (mul_mem_entrySet B hmul hX hY) hX) hY

private def congruenceSubgroup (B : AddSubgroup R) (hmul : ∀ x ∈ B, ∀ y ∈ B, x * y ∈ B) :
    Subgroup (Matrix n n R)ˣ where
  carrier := (fun g : (Matrix n n R)ˣ => (g : Matrix n n R) - 1) ⁻¹' entrySet (B : Set R) ∩
    (fun g : (Matrix n n R)ˣ => ((g⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) - 1) ⁻¹' entrySet (B : Set R)
  one_mem' := by
    have h0 : (0 : Matrix n n R) ∈ entrySet (B : Set R) := mem_entrySet.2 fun _ _ => B.zero_mem
    refine ⟨?_, ?_⟩
    · show ((1 : (Matrix n n R)ˣ) : Matrix n n R) - 1 ∈ entrySet (B : Set R)
      rw [Units.val_one, sub_self]
      exact h0
    · show (((1 : (Matrix n n R)ˣ)⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) - 1 ∈ entrySet (B : Set R)
      rw [inv_one, Units.val_one, sub_self]
      exact h0
  mul_mem' := by
    rintro g h ⟨hg₁, hg₂⟩ ⟨hh₁, hh₂⟩
    refine ⟨?_, ?_⟩
    · show ((g * h : (Matrix n n R)ˣ) : Matrix n n R) - 1 ∈ entrySet (B : Set R)
      rw [Units.val_mul]
      exact mul_sub_one_mem_entrySet B hmul hg₁ hh₁
    · show (((g * h)⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) - 1 ∈ entrySet (B : Set R)
      rw [mul_inv_rev, Units.val_mul]
      exact mul_sub_one_mem_entrySet B hmul hh₂ hg₂
  inv_mem' := by
    rintro g ⟨hg₁, hg₂⟩
    refine ⟨hg₂, ?_⟩
    show (((g⁻¹)⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) - 1 ∈ entrySet (B : Set R)
    rw [inv_inv]
    exact hg₁

private theorem mem_congruenceSubgroup {B : AddSubgroup R} {hmul : ∀ x ∈ B, ∀ y ∈ B, x * y ∈ B}
    {g : (Matrix n n R)ˣ} :
    g ∈ congruenceSubgroup B hmul ↔ (g : Matrix n n R) - 1 ∈ entrySet (B : Set R) ∧
      ((g⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) - 1 ∈ entrySet (B : Set R) :=
  Iff.rfl

end Congruence
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

section Topology

variable [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [Fintype n] [DecidableEq n]

private theorem isOpen_congruenceSubgroup (B : AddSubgroup R) (hmul : ∀ x ∈ B, ∀ y ∈ B, x * y ∈ B)
    (hB : IsOpen (B : Set R)) :
    IsOpen ((congruenceSubgroup B hmul : Subgroup (Matrix n n R)ˣ) : Set (Matrix n n R)ˣ) := by
  have hE : IsOpen (entrySet (B : Set R) : Set (Matrix n n R)) := isOpen_entrySet hB
  exact (hE.preimage (Units.continuous_val.sub continuous_const)).inter
    (hE.preimage (Units.continuous_coe_inv.sub continuous_const))

private theorem isCompact_congruenceSubgroup [T2Space R] (B : AddSubgroup R) (hmul : ∀ x ∈ B, ∀ y ∈ B, x * y ∈ B)
    (hB : IsCompact (B : Set R)) :
    IsCompact ((congruenceSubgroup B hmul : Subgroup (Matrix n n R)ˣ) : Set (Matrix n n R)ˣ) := by
  set E : Set (Matrix n n R) := entrySet (B : Set R)
  have hEc : IsCompact E := isCompact_entrySet hB
  have hEcl : IsClosed E := hEc.isClosed

  have himage : Units.embedProduct (Matrix n n R) ''
      ((congruenceSubgroup B hmul : Subgroup (Matrix n n R)ˣ) : Set (Matrix n n R)ˣ) =
      {p : Matrix n n R × (Matrix n n R)ᵐᵒᵖ |
        p.1 - 1 ∈ E ∧ unop p.2 - 1 ∈ E ∧ p.1 * unop p.2 = 1 ∧ unop p.2 * p.1 = 1} := by
    ext p
    rw [Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨hg₁, hg₂⟩ := mem_congruenceSubgroup.1 hg
      exact ⟨hg₁, hg₂, Units.mul_inv g, Units.inv_mul g⟩
    · rintro ⟨h₁, h₂, h₃, h₄⟩
      exact ⟨⟨p.1, unop p.2, h₃, h₄⟩, mem_congruenceSubgroup.2 ⟨h₁, h₂⟩, Prod.ext rfl (op_unop p.2)⟩
  rw [Units.isEmbedding_embedProduct.isCompact_iff, himage]

  have hK : IsCompact (((fun X : Matrix n n R => 1 + X) '' E) ×ˢ
      (op '' ((fun X : Matrix n n R => 1 + X) '' E))) :=
    (hEc.image (continuous_const.add continuous_id)).prod
      ((hEc.image (continuous_const.add continuous_id)).image continuous_op)
  have hScl : IsClosed {p : Matrix n n R × (Matrix n n R)ᵐᵒᵖ |
      p.1 - 1 ∈ E ∧ unop p.2 - 1 ∈ E ∧ p.1 * unop p.2 = 1 ∧ unop p.2 * p.1 = 1} := by
    have h₁ : IsClosed {p : Matrix n n R × (Matrix n n R)ᵐᵒᵖ | p.1 - 1 ∈ E} :=
      hEcl.preimage (continuous_fst.sub continuous_const)
    have h₂ : IsClosed {p : Matrix n n R × (Matrix n n R)ᵐᵒᵖ | unop p.2 - 1 ∈ E} :=
      hEcl.preimage ((continuous_unop.comp continuous_snd).sub continuous_const)
    have h₃ : IsClosed {p : Matrix n n R × (Matrix n n R)ᵐᵒᵖ | p.1 * unop p.2 = 1} :=
      isClosed_eq (continuous_fst.mul (continuous_unop.comp continuous_snd)) continuous_const
    have h₄ : IsClosed {p : Matrix n n R × (Matrix n n R)ᵐᵒᵖ | unop p.2 * p.1 = 1} :=
      isClosed_eq ((continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const
    exact h₁.inter (h₂.inter (h₃.inter h₄))
  refine hK.of_isClosed_subset hScl ?_
  intro p hp
  rw [Set.mem_setOf_eq] at hp
  obtain ⟨h₁, h₂, -, -⟩ := hp
  exact Set.mk_mem_prod ⟨p.1 - 1, h₁, add_sub_cancel 1 p.1⟩
    ⟨unop p.2, ⟨unop p.2 - 1, h₂, add_sub_cancel 1 (unop p.2)⟩, op_unop p.2⟩

private theorem exists_congruenceSubgroup_subset
    (hR : ∀ U ∈ 𝓝 (0 : R), ∃ B : AddSubgroup R, IsCompact (B : Set R) ∧ IsOpen (B : Set R) ∧
      (∀ x ∈ B, ∀ y ∈ B, x * y ∈ B) ∧ (B : Set R) ⊆ U)
    {U : Set (Matrix n n R)ˣ} (hU : U ∈ 𝓝 (1 : (Matrix n n R)ˣ)) :
    ∃ (B : AddSubgroup R) (hmul : ∀ x ∈ B, ∀ y ∈ B, x * y ∈ B), IsCompact (B : Set R) ∧ IsOpen (B : Set R) ∧
      ((congruenceSubgroup B hmul : Subgroup (Matrix n n R)ˣ) : Set (Matrix n n R)ˣ) ⊆ U := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  rw [map_one, Prod.one_eq_mk, mem_nhds_prod_iff] at hV
  obtain ⟨V₁, hV₁, V₂, hV₂, hV₁₂⟩ := hV

  have hW₂ : op ⁻¹' V₂ ∈ 𝓝 (1 : Matrix n n R) := by
    have h : ContinuousAt (op : Matrix n n R → (Matrix n n R)ᵐᵒᵖ) 1 := continuous_op.continuousAt
    rw [← op_one] at hV₂
    exact h.preimage_mem_nhds hV₂
  have hW : V₁ ∩ op ⁻¹' V₂ ∈ 𝓝 (1 : Matrix n n R) := Filter.inter_mem hV₁ hW₂

  have hW' : (fun X : Matrix n n R => 1 + X) ⁻¹' (V₁ ∩ op ⁻¹' V₂) ∈ 𝓝 (0 : Matrix n n R) := by
    have h : ContinuousAt (fun X : Matrix n n R => 1 + X) 0 :=
      (continuous_const.add continuous_id).continuousAt
    exact h.preimage_mem_nhds (by simpa using hW)
  obtain ⟨B₀, hB₀, hB₀W⟩ := exists_entrySet_subset_of_mem_nhds (n := n) hW'
  obtain ⟨B, hBc, hBo, hmul, hBB₀⟩ := hR B₀ hB₀
  refine ⟨B, hmul, hBc, hBo, fun g hg => ?_⟩
  obtain ⟨hg₁, hg₂⟩ := mem_congruenceSubgroup.1 hg
  have hg₁' : (g : Matrix n n R) ∈ V₁ ∩ op ⁻¹' V₂ := by
    have h := hB₀W (entrySet_mono hBB₀ hg₁)
    rwa [Set.mem_preimage, add_sub_cancel] at h
  have hg₂' : ((g⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) ∈ V₁ ∩ op ⁻¹' V₂ := by
    have h := hB₀W (entrySet_mono hBB₀ hg₂)
    rwa [Set.mem_preimage, add_sub_cancel] at h
  apply hVU
  show Units.embedProduct (Matrix n n R) g ∈ V
  apply hV₁₂
  show ((g : Matrix n n R), op ((g⁻¹ : (Matrix n n R)ˣ) : Matrix n n R)) ∈ V₁ ×ˢ V₂
  exact Set.mk_mem_prod hg₁'.1 hg₂'.2

private theorem exists_compact_open_subgroup_subset [T2Space R]
    (hR : ∀ U ∈ 𝓝 (0 : R), ∃ B : AddSubgroup R, IsCompact (B : Set R) ∧ IsOpen (B : Set R) ∧
      (∀ x ∈ B, ∀ y ∈ B, x * y ∈ B) ∧ (B : Set R) ⊆ U) :
    ∀ U ∈ 𝓝 (1 : (Matrix n n R)ˣ), ∃ K : Subgroup (Matrix n n R)ˣ,
      IsCompact (K : Set (Matrix n n R)ˣ) ∧ IsOpen (K : Set (Matrix n n R)ˣ) ∧ (K : Set (Matrix n n R)ˣ) ⊆ U := by
  intro U hU
  obtain ⟨B, hmul, hBc, hBo, hsub⟩ := exists_congruenceSubgroup_subset hR hU
  exact ⟨congruenceSubgroup B hmul, isCompact_congruenceSubgroup B hmul hBc, isOpen_congruenceSubgroup B hmul hBo,
    hsub⟩

end Topology
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

end MatrixUnitsBasis
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

end CongruenceSubgroups
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

section AdicCompletionBasis

open Filter Topology IsDedekindDomain

namespace MatrixUnitsBasis

section Ball

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued R Γ₀]

private theorem exists_compact_open_addSubgroup_subset {S : Set R} (hS : IsCompact S)
    (hS₁ : ∀ x : R, (Valued.v : Valuation R Γ₀) x ≤ 1 → x ∈ S) {U : Set R} (hU : U ∈ 𝓝 (0 : R)) :
    ∃ B : AddSubgroup R, IsCompact (B : Set R) ∧ IsOpen (B : Set R) ∧ (∀ x ∈ B, ∀ y ∈ B, x * y ∈ B) ∧
      (B : Set R) ⊆ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hU
  set β := min γ 1
  have hβγ := Units.val_le_val.2 (min_le_left γ 1)
  have hβ₁ := Units.val_le_val.2 (min_le_right γ 1)
  rw [Units.val_one] at hβ₁
  refine ⟨(Valued.v : Valuation R Γ₀).restrict.ltAddSubgroup β, ?_, ?_, ?_, ?_⟩
  · refine hS.of_isClosed_subset ?_ ?_
    · rw [Valuation.coe_ltAddSubgroup]
      exact Valued.isClosed_ball R _
    · intro x hx
      rw [SetLike.mem_coe, Valuation.mem_ltAddSubgroup_iff] at hx
      exact hS₁ x ((Valued.v : Valuation R Γ₀).restrict_le_one_iff.1 (hx.le.trans hβ₁))
  · rw [Valuation.coe_ltAddSubgroup]
    exact Valued.isOpen_ball R _
  · intro x hx y hy
    rw [Valuation.mem_ltAddSubgroup_iff] at hx hy ⊢
    rw [Valuation.map_mul]
    exact (mul_le_of_le_one_right' (hy.le.trans hβ₁)).trans_lt hx
  · intro x hx
    rw [SetLike.mem_coe, Valuation.mem_ltAddSubgroup_iff] at hx
    exact hγ (lt_of_lt_of_le hx hβγ)

end Ball
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

section Completion

open NumberField

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem exists_compact_open_subgroup_subset_adicCompletion :
    ∀ U ∈ 𝓝 (1 : GL (Fin 3) (v.adicCompletion K)), ∃ H : Subgroup (GL (Fin 3) (v.adicCompletion K)),
      IsCompact (H : Set (GL (Fin 3) (v.adicCompletion K))) ∧ IsOpen (H : Set (GL (Fin 3) (v.adicCompletion K))) ∧
        (H : Set (GL (Fin 3) (v.adicCompletion K))) ⊆ U :=
  exists_compact_open_subgroup_subset fun _ hU =>
    exists_compact_open_addSubgroup_subset (isCompactAdicCompletionIntegers K v) (fun _ hx => hx) hU

private def integersAddSubgroup : AddSubgroup (v.adicCompletion K) :=
  (v.adicCompletionIntegers K).toSubring.toAddSubgroup

private theorem mem_integersAddSubgroup {x : v.adicCompletion K} :
    x ∈ integersAddSubgroup K v ↔ Valued.v x ≤ (1 : WithZero (Multiplicative ℤ)) :=
  Iff.rfl

private theorem mul_mem_integersAddSubgroup : ∀ x ∈ integersAddSubgroup K v, ∀ y ∈ integersAddSubgroup K v,
    x * y ∈ integersAddSubgroup K v := fun _ hx _ hy =>
  (v.adicCompletionIntegers K).toSubring.mul_mem hx hy

private theorem valued_one_apply_le (i j : Fin 3) :
    Valued.v ((1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) ≤ (1 : WithZero (Multiplicative ℤ)) := by
  rw [Matrix.one_apply]
  split_ifs
  · rw [Valuation.map_one]
  · rw [Valuation.map_zero]
    exact zero_le'

private theorem forall_sub_one_apply_mem_iff (X : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) :
    (∀ i j, (X - 1) i j ∈ (integersAddSubgroup K v : Set (v.adicCompletion K))) ↔
      ∀ i j, Valued.v (X i j) ≤ (1 : WithZero (Multiplicative ℤ)) := by
  simp only [SetLike.mem_coe, mem_integersAddSubgroup, Matrix.sub_apply]
  constructor
  · intro h i j
    calc Valued.v (X i j) = Valued.v ((X i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) +
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (X i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j))
          (Valued.v ((1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j)) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le (h i j) (valued_one_apply_le K v i j)
  · intro h i j
    calc Valued.v (X i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j)
        ≤ max (Valued.v (X i j)) (Valued.v ((1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j)) :=
          Valuation.map_sub _ _ _
      _ ≤ 1 := max_le (h i j) (valued_one_apply_le K v i j)

private theorem congruenceSubgroup_integers_eq :
    congruenceSubgroup (integersAddSubgroup K v) (mul_mem_integersAddSubgroup K v) =
      LanglandsTunnell.CubicInduction.localMaximalCompact3 (𝓞 K) K v := by
  ext g
  rw [mem_congruenceSubgroup, LanglandsTunnell.CubicInduction.mem_localMaximalCompact3_iff, mem_entrySet,
    mem_entrySet, forall_sub_one_apply_mem_iff, forall_sub_one_apply_mem_iff]

end Completion
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

end MatrixUnitsBasis
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

end AdicCompletionBasis
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

section TransposeInv3Twist

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.localMaximalCompact3 CubicInduction.mem_localMaximalCompact3_iff CubicInduction.transposeInv3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localMaximalCompact3 mem_localMaximalCompact3_iff transposeInv3 LocalGL3"
namespace TransposeTwist
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction"

p2m_open "Matrix P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Matrix FLT.SmoothAdmissibleSchurCommutant"

section Algebra

variable {F : Type*} [Field F]

@[scoped simp] private theorem coe_transposeInv3 (g : GL (Fin 3) F) :
    ((transposeInv3 g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ := rfl

@[scoped simp] private theorem coe_transposeInv3_inv (g : GL (Fin 3) F) :
    (((transposeInv3 g)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ := rfl

private theorem transposeInv3_transposeInv3 (g : GL (Fin 3) F) : transposeInv3 (transposeInv3 g) = g :=
  Units.ext (by rw [coe_transposeInv3, coe_transposeInv3_inv, Matrix.transpose_transpose])

private theorem transposeInv3_mul (g h : GL (Fin 3) F) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h :=
  Units.ext (by simp only [coe_transposeInv3, _root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul])

private theorem transposeInv3_one : transposeInv3 (1 : GL (Fin 3) F) = 1 :=
  Units.ext (by simp only [coe_transposeInv3, inv_one, Units.val_one, Matrix.transpose_one])

private def transposeInv3Equiv : GL (Fin 3) F ≃* GL (Fin 3) F where
  toFun := transposeInv3
  invFun := transposeInv3
  left_inv := transposeInv3_transposeInv3
  right_inv := transposeInv3_transposeInv3
  map_mul' := transposeInv3_mul

@[scoped simp] private theorem transposeInv3Equiv_apply (g : GL (Fin 3) F) : transposeInv3Equiv g = transposeInv3 g := rfl

private theorem transposeInv3_inv (g : GL (Fin 3) F) : transposeInv3 g⁻¹ = (transposeInv3 g)⁻¹ :=
  map_inv (transposeInv3Equiv : GL (Fin 3) F ≃* GL (Fin 3) F) g

private theorem coe_transposeInv3_of_inv (g : GL (Fin 3) F) :
    ((transposeInv3 g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ := by
  rw [transposeInv3_inv, coe_transposeInv3_inv]

private theorem transposeInv3_image_eq_preimage (s : Set (GL (Fin 3) F)) :
    transposeInv3 '' s = transposeInv3 ⁻¹' s := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Set.mem_preimage, transposeInv3_transposeInv3]
    exact hk
  · intro hx
    exact ⟨transposeInv3 x, hx, transposeInv3_transposeInv3 x⟩

end Algebra
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

section Continuity

variable {F : Type*} [Field F] [TopologicalSpace F]

private theorem continuous_transposeInv3 : Continuous (transposeInv3 : GL (Fin 3) F → GL (Fin 3) F) := by
  rw [Units.continuous_iff]
  constructor
  · have h : (Units.val ∘ (transposeInv3 : GL (Fin 3) F → GL (Fin 3) F)) =
        fun g : GL (Fin 3) F => (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ := rfl
    rw [h]
    exact Units.continuous_coe_inv.matrix_transpose
  · have h : (fun g : GL (Fin 3) F => (((transposeInv3 g)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =
        fun g : GL (Fin 3) F => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ := rfl
    rw [h]
    exact Units.continuous_val.matrix_transpose

private theorem continuous_transposeInv3_inv :
    Continuous (fun g : GL (Fin 3) F => (transposeInv3 g)⁻¹) := by
  rw [Units.continuous_iff]
  constructor
  · have h : (Units.val ∘ fun g : GL (Fin 3) F => (transposeInv3 g)⁻¹) =
        fun g : GL (Fin 3) F => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ := rfl
    rw [h]
    exact Units.continuous_val.matrix_transpose
  · have h : (fun g : GL (Fin 3) F => ((((transposeInv3 g)⁻¹)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =
        fun g : GL (Fin 3) F => (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ := rfl
    rw [h]
    exact Units.continuous_coe_inv.matrix_transpose

private theorem continuous_conj [IsTopologicalRing F] (g : GL (Fin 3) F) :
    Continuous (fun x : GL (Fin 3) F => g * x * g⁻¹) :=
  (continuous_const.mul continuous_id).mul continuous_const

end Continuity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

section Twist

variable {F : Type*} [Field F] {R : Type*} [Field R]
variable {V : Type*} [AddCommGroup V] [Module R V]

private def twistTransposeInv3 (π : GL (Fin 3) F →* Module.End R V) : GL (Fin 3) F →* Module.End R V :=
  π.comp (transposeInv3Equiv : GL (Fin 3) F ≃* GL (Fin 3) F).toMonoidHom

@[scoped simp] private theorem twistTransposeInv3_apply (π : GL (Fin 3) F →* Module.End R V) (g : GL (Fin 3) F) :
    twistTransposeInv3 π g = π (transposeInv3 g) := rfl

private theorem twistTransposeInv3_twistTransposeInv3 (π : GL (Fin 3) F →* Module.End R V) :
    twistTransposeInv3 (twistTransposeInv3 π) = π := by
  apply MonoidHom.ext
  intro g
  show π (transposeInv3 (transposeInv3 g)) = π g
  rw [transposeInv3_transposeInv3]

private theorem isIrreducibleRep_twistTransposeInv3_iff (π : GL (Fin 3) F →* Module.End R V) :
    IsIrreducibleRep (twistTransposeInv3 π) ↔ IsIrreducibleRep π := by
  constructor
  · rintro ⟨hne, hinv⟩
    refine ⟨hne, fun W hW => ?_⟩
    apply hinv W
    intro g v hv
    exact hW (transposeInv3 g) v hv
  · rintro ⟨hne, hinv⟩
    refine ⟨hne, fun W hW => ?_⟩
    apply hinv W
    intro g v hv
    have h := hW (transposeInv3 g) v hv
    rw [twistTransposeInv3_apply, transposeInv3_transposeInv3] at h
    exact h

private theorem fixedVectors_twistTransposeInv3 (π : GL (Fin 3) F →* Module.End R V) (K : Subgroup (GL (Fin 3) F)) :
    fixedVectors (twistTransposeInv3 π) K =
      fixedVectors π (K.map (transposeInv3Equiv : GL (Fin 3) F ≃* GL (Fin 3) F).toMonoidHom) := by
  ext v
  simp only [mem_fixedVectors, Subgroup.mem_map]
  constructor
  · rintro h u ⟨k, hk, rfl⟩
    exact h k hk
  · intro h k hk
    exact h (transposeInv3 k) ⟨k, hk, rfl⟩

variable [TopologicalSpace F]

private theorem isSmoothRep_twistTransposeInv3_of {π : GL (Fin 3) F →* Module.End R V} (hsm : IsSmoothRep π) :
    IsSmoothRep (twistTransposeInv3 π) := by
  intro v
  have hset : ((repStabilizer (twistTransposeInv3 π) v : Subgroup (GL (Fin 3) F)) : Set (GL (Fin 3) F)) =
      transposeInv3 ⁻¹' ((repStabilizer π v : Subgroup (GL (Fin 3) F)) : Set (GL (Fin 3) F)) := by
    ext g
    simp only [SetLike.mem_coe, mem_repStabilizer, Set.mem_preimage]
    exact Iff.rfl
  rw [hset]
  exact (hsm v).preimage continuous_transposeInv3

private theorem isSmoothRep_twistTransposeInv3_iff (π : GL (Fin 3) F →* Module.End R V) :
    IsSmoothRep (twistTransposeInv3 π) ↔ IsSmoothRep π := by
  constructor
  · intro h
    have h2 := isSmoothRep_twistTransposeInv3_of h
    rwa [twistTransposeInv3_twistTransposeInv3] at h2
  · exact isSmoothRep_twistTransposeInv3_of

private theorem isAdmissibleRep_twistTransposeInv3_of {π : GL (Fin 3) F →* Module.End R V}
    (hadm : IsAdmissibleRep π) : IsAdmissibleRep (twistTransposeInv3 π) := by
  intro K hKc hKo
  rw [fixedVectors_twistTransposeInv3]
  apply hadm
  · rw [Subgroup.coe_map]
    exact hKc.image continuous_transposeInv3
  · rw [Subgroup.coe_map]
    have h : ((transposeInv3Equiv : GL (Fin 3) F ≃* GL (Fin 3) F).toMonoidHom '' (K : Set (GL (Fin 3) F))) =
        transposeInv3 '' (K : Set (GL (Fin 3) F)) := rfl
    rw [h, transposeInv3_image_eq_preimage]
    exact hKo.preimage continuous_transposeInv3

private theorem isAdmissibleRep_twistTransposeInv3_iff (π : GL (Fin 3) F →* Module.End R V) :
    IsAdmissibleRep (twistTransposeInv3 π) ↔ IsAdmissibleRep π := by
  constructor
  · intro h
    have h2 := isAdmissibleRep_twistTransposeInv3_of h
    rwa [twistTransposeInv3_twistTransposeInv3] at h2
  · exact isAdmissibleRep_twistTransposeInv3_of

end Twist
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits"

end LanglandsTunnell.CubicInduction.TransposeTwist
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell"

end TransposeInv3Twist
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

section Fin3ConjCurrency

open Polynomial

namespace Matrix
p2m_export "Matrix" "transvection_mul_transvection_same J transpose diagonal_apply det_fin_three transpose_one diagonal_one sub_mulVec transvection_zero ext vecMul_diagonal swap charpoly_transpose add sub_apply smul_mulVec transvection det_diagonal sub zero IsIrreducible coe_units_inv map_smul' trace_conj' inv_def scalar one_mulVec trace_one transpose_transpose comp GeneralLinearGroup.det_ne_zero charpoly trace_mul_comm mulVecLin add_mulVec map_map toLin'_mul minpoly_toLin' mulVecLin_apply charpoly_natDegree_eq_dim transpose_pow rank smul det_transvection_of_ne transpose_eq_zero mulVec_mulVec compl zero_apply of_apply single GeneralLinearGroup charpoly_toLin' map_id ext_iff diagonal_mul one_apply neg_apply semiring smul_apply transpose_zero charpoly_monic toLinearEquiv det minpoly_dvd_charpoly toLin'_apply' GeneralLinearGroup.mkOfDetNeZero diagonal add_apply zero_mulVec comp_apply of sum_apply transpose_smul inv diagonal_transvection_induction_of_det_ne_zero toLin'_apply map GeneralLinearGroup.ext mulVec_zero toLin' one mul_apply unique trace transpose_mul charpoly.univ_coeff_eval₂Hom charpoly_units_conj charpoly.univ module nonempty transpose_add diagonal_mul_diagonal mul_diagonal mul_inv_rev"
namespace Fin3Conj
p2m_open "Matrix"

variable {F : Type} [Field F]

section transport

variable {n : Type} [Fintype n] [DecidableEq n]

private theorem isConj_toMatrix_toLin' (A : Matrix n n F) (b : Module.Basis n F (n → F)) :
    IsConj (LinearMap.toMatrix b b (Matrix.toLin' A)) A := by
  set e : Module.Basis n F (n → F) := Pi.basisFun F n
  have h : LinearMap.toMatrix b b (Matrix.toLin' A) = b.toMatrix e * A * e.toMatrix b := by
    rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := b) (c := b) (b' := e) (c' := e),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  have hQP : e.toMatrix b * b.toMatrix e = 1 := Module.Basis.toMatrix_mul_toMatrix_flip (b := e) (b' := b)
  have hPQ : b.toMatrix e * e.toMatrix b = 1 := Module.Basis.toMatrix_mul_toMatrix_flip (b := b) (b' := e)
  refine ⟨Units.mk (e.toMatrix b) (b.toMatrix e) hQP hPQ, ?_⟩
  show e.toMatrix b * LinearMap.toMatrix b b (Matrix.toLin' A) = A * e.toMatrix b
  rw [h, ← mul_assoc, ← mul_assoc, hQP, one_mul]

private theorem isConj_of_toMatrix_eq {A C : Matrix n n F} (b : Module.Basis n F (n → F))
    (hb : LinearMap.toMatrix b b (Matrix.toLin' A) = C) : IsConj C A :=
  hb ▸ isConj_toMatrix_toLin' A b

private theorem aeval_transpose (A : Matrix n n F) (p : F[X]) : aeval Aᵀ p = (aeval A p)ᵀ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, transpose_add]
  | monomial k c =>
    rw [aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_one_mul, smul_one_mul, transpose_smul,
      transpose_pow]

private theorem minpoly_transpose (A : Matrix n n F) : minpoly F Aᵀ = minpoly F A := by
  have h₁ : minpoly F Aᵀ ∣ minpoly F A := minpoly.dvd F Aᵀ (by rw [aeval_transpose, minpoly.aeval, transpose_zero])
  have h₂ : minpoly F A ∣ minpoly F Aᵀ := by
    refine minpoly.dvd F A ?_
    have h := minpoly.aeval F Aᵀ
    rw [aeval_transpose, transpose_eq_zero] at h
    exact h
  exact eq_of_monic_of_associated (minpoly.monic (IsIntegral.of_finite (R := F) Aᵀ))
    (minpoly.monic (IsIntegral.of_finite (R := F) A)) (associated_of_dvd_dvd h₁ h₂)

end transport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

section strata

private theorem minpoly_natDegree_le_one_iff (A : Matrix (Fin 3) (Fin 3) F) :
    (minpoly F A).natDegree ≤ 1 ↔ ∃ a : F, A = a • (1 : Matrix (Fin 3) (Fin 3) F) := by
  constructor
  · intro h
    obtain ⟨c, d, hcd⟩ : ∃ c d : F, minpoly F A = C c * X + C d := ⟨_, _, eq_X_add_C_of_natDegree_le_one h⟩
    have hint : IsIntegral F A := IsIntegral.of_finite (R := F) A
    have hmonic := minpoly.monic hint
    have hpos := minpoly.natDegree_pos hint
    rw [hcd] at hmonic hpos
    have hc : c = 1 := by
      rcases eq_or_ne c 0 with rfl | hc0
      · simp at hpos
      · have h1 := hmonic.leadingCoeff
        rwa [leadingCoeff_linear hc0] at h1
    have h0 := minpoly.aeval F A
    rw [hcd, hc, map_add, map_mul, aeval_C, aeval_X, aeval_C, map_one, one_mul, Algebra.algebraMap_eq_smul_one] at h0
    exact ⟨-d, by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h0⟩
  · rintro ⟨a, rfl⟩
    rw [← Algebra.algebraMap_eq_smul_one, minpoly.eq_X_sub_C]
    exact (natDegree_X_sub_C a).le

private theorem minpoly_natDegree_le_two_iff (A : Matrix (Fin 3) (Fin 3) F) :
    (minpoly F A).natDegree ≤ 2 ↔ ¬ LinearIndependent F ![(1 : Matrix (Fin 3) (Fin 3) F), A, A ^ 2] := by
  have hint : IsIntegral F A := IsIntegral.of_finite (R := F) A
  constructor
  · intro h hli
    rw [Fintype.linearIndependent_iff] at hli
    have h0 := minpoly.aeval F A
    rw [aeval_eq_sum_range' (Nat.lt_succ_of_le h)] at h0
    have hd3 : (minpoly F A).natDegree < 3 := Nat.lt_succ_of_le h
    have hzero := hli (fun i : Fin 3 => (minpoly F A).coeff i)
      (by simpa [Fin.sum_univ_three, Finset.sum_range_succ] using h0) ⟨(minpoly F A).natDegree, hd3⟩
    have hlead := (minpoly.monic hint).leadingCoeff
    rw [← coeff_natDegree] at hlead
    exact one_ne_zero (hlead.symm.trans hzero)
  · intro hdep
    rw [Fintype.linearIndependent_iff] at hdep
    push Not at hdep
    obtain ⟨g, hg, i, hi⟩ := hdep
    set q : F[X] := C (g 0) + C (g 1) * X + C (g 2) * X ^ 2 with hq
    have hq0 : q ≠ 0 := by
      intro h0
      apply hi
      have h0' : ∀ k, q.coeff k = 0 := fun k => by rw [h0, coeff_zero]
      fin_cases i
      · simpa [hq, coeff_X, coeff_C, coeff_X_pow] using h0' 0
      · simpa [hq, coeff_X, coeff_C, coeff_X_pow] using h0' 1
      · simpa [hq, coeff_X, coeff_C, coeff_X_pow] using h0' 2
    have hqA : aeval A q = 0 := by
      have : ∑ j : Fin 3, g j • ![(1 : Matrix (Fin 3) (Fin 3) F), A, A ^ 2] j = 0 := hg
      rw [Fin.sum_univ_three] at this
      change g 0 • (1 : Matrix (Fin 3) (Fin 3) F) + g 1 • A + g 2 • A ^ 2 = 0 at this
      rw [hq, map_add, map_add, map_mul, map_mul, aeval_C, aeval_C, aeval_C, aeval_X, map_pow, aeval_X,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_one_mul,
        smul_one_mul]
      exact this
    have hdvd := minpoly.dvd F A hqA
    calc (minpoly F A).natDegree ≤ q.natDegree := natDegree_le_of_dvd hdvd hq0
      _ ≤ 2 := by
        rw [hq]
        refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
        · exact (natDegree_C _).le.trans (by norm_num)
        · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by norm_num))
        · exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le 2)

end strata
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

end Matrix.Fin3Conj
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

end Fin3ConjCurrency
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

section Fin3ConjAnnihilator

open Polynomial UniqueFactorizationMonoid

namespace Matrix
p2m_export "Matrix" "transvection_mul_transvection_same J transpose diagonal_apply det_fin_three transpose_one diagonal_one sub_mulVec transvection_zero ext vecMul_diagonal swap charpoly_transpose add sub_apply smul_mulVec transvection det_diagonal sub zero IsIrreducible coe_units_inv map_smul' trace_conj' inv_def scalar one_mulVec trace_one transpose_transpose comp GeneralLinearGroup.det_ne_zero charpoly trace_mul_comm mulVecLin add_mulVec map_map toLin'_mul minpoly_toLin' mulVecLin_apply charpoly_natDegree_eq_dim transpose_pow rank smul det_transvection_of_ne transpose_eq_zero mulVec_mulVec compl zero_apply of_apply single GeneralLinearGroup charpoly_toLin' map_id ext_iff diagonal_mul one_apply neg_apply semiring smul_apply transpose_zero charpoly_monic toLinearEquiv det minpoly_dvd_charpoly toLin'_apply' GeneralLinearGroup.mkOfDetNeZero diagonal add_apply zero_mulVec comp_apply of sum_apply transpose_smul inv diagonal_transvection_induction_of_det_ne_zero toLin'_apply map GeneralLinearGroup.ext mulVec_zero toLin' one mul_apply unique trace transpose_mul charpoly.univ_coeff_eval₂Hom charpoly_units_conj charpoly.univ module nonempty transpose_add diagonal_mul_diagonal mul_diagonal mul_inv_rev"
namespace Fin3Conj
p2m_open "Matrix"

variable {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n]

private theorem aeval_mul_mulVec (A : Matrix n n F) (a b : F[X]) (v : n → F) :
    aeval A (a * b) *ᵥ v = aeval A a *ᵥ (aeval A b *ᵥ v) := by
  rw [map_mul, mulVec_mulVec]

private theorem exists_forall_aeval_mulVec_eq_zero_imp_minpoly_dvd [Nonempty n] [Infinite F] (A : Matrix n n F) :
    ∃ v : n → F, ∀ r : F[X], aeval A r *ᵥ v = 0 → minpoly F A ∣ r := by
  classical
  have hint : IsIntegral F A := IsIntegral.of_finite (R := F) A
  have hm0' : minpoly F A ≠ 0 := minpoly.ne_zero hint
  have hmaeval' : aeval A (minpoly F A) = 0 := minpoly.aeval F A
  have hmdvd' : ∀ p : F[X], aeval A p = 0 → minpoly F A ∣ p := fun p hp => minpoly.dvd F A hp
  generalize hm : minpoly F A = m at hm0' hmaeval' hmdvd' ⊢

  let P : (normalizedFactors m).toFinset → Submodule F (n → F) := fun q =>
    LinearMap.ker (Matrix.mulVecLin (aeval A (m / (q : F[X]))))
  have hq_mem : ∀ q : (normalizedFactors m).toFinset, (q : F[X]) ∈ normalizedFactors m := fun q =>
    Multiset.mem_toFinset.1 q.2
  have hq_irr : ∀ q : (normalizedFactors m).toFinset, Irreducible (q : F[X]) := fun q =>
    irreducible_of_normalized_factor _ (hq_mem q)
  have hq_mul : ∀ q : (normalizedFactors m).toFinset, (q : F[X]) * (m / (q : F[X])) = m := fun q =>
    EuclideanDomain.mul_div_cancel' (hq_irr q).ne_zero (dvd_of_mem_normalizedFactors (hq_mem q))
  have hP : ∀ q, P q ≠ ⊤ := by
    intro q hq
    have hq' : LinearMap.ker (Matrix.mulVecLin (aeval A (m / (q : F[X])))) = ⊤ := hq
    have hzero : aeval A (m / (q : F[X])) = 0 := by
      have h1 : Matrix.mulVecLin (aeval A (m / (q : F[X]))) = 0 := LinearMap.ker_eq_top.1 hq'
      refine Matrix.toLin'.injective ?_
      rw [map_zero, Matrix.toLin'_apply']
      exact h1
    have hmq0 : m / (q : F[X]) ≠ 0 := by
      intro h
      apply hm0'
      rw [← hq_mul q, h, mul_zero]
    have hle : m.natDegree ≤ (m / (q : F[X])).natDegree := natDegree_le_of_dvd (hmdvd' _ hzero) hmq0
    have heq : m.natDegree = (q : F[X]).natDegree + (m / (q : F[X])).natDegree := by
      conv_lhs => rw [← hq_mul q]
      exact natDegree_mul (hq_irr q).ne_zero hmq0
    have hpos : 0 < (q : F[X]).natDegree := natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible (hq_irr q))
    omega
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top P hP
  refine ⟨v, fun r hr => ?_⟩

  set d : F[X] := EuclideanDomain.gcd m r with hd_def
  have hdv : aeval A d *ᵥ v = 0 := by
    rw [hd_def, EuclideanDomain.gcd_eq_gcd_ab, map_add, add_mulVec, mul_comm m, mul_comm r, aeval_mul_mulVec,
      aeval_mul_mulVec, hmaeval', zero_mulVec, mulVec_zero, hr, mulVec_zero, add_zero]
  have hdm : d ∣ m := EuclideanDomain.gcd_dvd_left m r
  have hdr : d ∣ r := EuclideanDomain.gcd_dvd_right m r
  suffices hmd : m ∣ d from hmd.trans hdr
  by_contra hmd
  obtain ⟨e, he⟩ := hdm
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hm0' (by rw [he, mul_zero])
  have heu : ¬ IsUnit e := by
    intro hu
    apply hmd
    have h1 : m ∣ d * e := ⟨1, by rw [mul_one, he]⟩
    exact hu.dvd_mul_right.1 h1
  obtain ⟨q₀, hq₀, hq₀e⟩ := WfDvdMonoid.exists_irreducible_factor heu he0
  have hq₀m : q₀ ∣ m := hq₀e.trans ⟨d, by rw [he, mul_comm]⟩
  obtain ⟨q, hqS, hqq₀⟩ := exists_mem_normalizedFactors_of_dvd hm0' hq₀ hq₀m
  have hq0 : q ≠ 0 := (irreducible_of_normalized_factor q hqS).ne_zero
  have hqm : q * (m / q) = m := EuclideanDomain.mul_div_cancel' hq0 (dvd_of_mem_normalizedFactors hqS)
  obtain ⟨e', he'⟩ : q ∣ e := hqq₀.dvd'.trans hq₀e
  have hdiv : m / q = d * e' := by
    apply mul_left_cancel₀ hq0
    rw [hqm, he, he']
    ring
  apply hv ⟨q, Multiset.mem_toFinset.2 hqS⟩
  show v ∈ LinearMap.ker (Matrix.mulVecLin (aeval A (m / q)))
  rw [LinearMap.mem_ker, mulVecLin_apply, hdiv, mul_comm d e', aeval_mul_mulVec, hdv, mulVec_zero]

end Matrix.Fin3Conj
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

end Fin3ConjAnnihilator
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

section Fin3ConjCompanion

open Polynomial

namespace Matrix
p2m_export "Matrix" "transvection_mul_transvection_same J transpose diagonal_apply det_fin_three transpose_one diagonal_one sub_mulVec transvection_zero ext vecMul_diagonal swap charpoly_transpose add sub_apply smul_mulVec transvection det_diagonal sub zero IsIrreducible coe_units_inv map_smul' trace_conj' inv_def scalar one_mulVec trace_one transpose_transpose comp GeneralLinearGroup.det_ne_zero charpoly trace_mul_comm mulVecLin add_mulVec map_map toLin'_mul minpoly_toLin' mulVecLin_apply charpoly_natDegree_eq_dim transpose_pow rank smul det_transvection_of_ne transpose_eq_zero mulVec_mulVec compl zero_apply of_apply single GeneralLinearGroup charpoly_toLin' map_id ext_iff diagonal_mul one_apply neg_apply semiring smul_apply transpose_zero charpoly_monic toLinearEquiv det minpoly_dvd_charpoly toLin'_apply' GeneralLinearGroup.mkOfDetNeZero diagonal add_apply zero_mulVec comp_apply of sum_apply transpose_smul inv diagonal_transvection_induction_of_det_ne_zero toLin'_apply map GeneralLinearGroup.ext mulVec_zero toLin' one mul_apply unique trace transpose_mul charpoly.univ_coeff_eval₂Hom charpoly_units_conj charpoly.univ module nonempty transpose_add diagonal_mul_diagonal mul_diagonal mul_inv_rev"
namespace Fin3Conj
p2m_open "Matrix"

variable {F : Type} [Field F]

private def companion (p : F[X]) : Matrix (Fin 3) (Fin 3) F :=
  !![0, 0, -p.coeff 0; 1, 0, -p.coeff 1; 0, 1, -p.coeff 2]

private theorem isConj_companion_of_minpoly_natDegree_eq_three [Infinite F] (A : Matrix (Fin 3) (Fin 3) F)
    (h3 : (minpoly F A).natDegree = 3) : IsConj (companion (minpoly F A)) A := by
  obtain ⟨v, hv⟩ := exists_forall_aeval_mulVec_eq_zero_imp_minpoly_dvd A
  set w : Fin 3 → (Fin 3 → F) := ![v, A *ᵥ v, A *ᵥ (A *ᵥ v)] with hw

  have hli : LinearIndependent F w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fin.sum_univ_three] at hg
    change g 0 • v + g 1 • (A *ᵥ v) + g 2 • (A *ᵥ (A *ᵥ v)) = 0 at hg
    set r : F[X] := C (g 0) + C (g 1) * X + C (g 2) * X ^ 2 with hr
    have hrA : aeval A r *ᵥ v = 0 := by
      rw [hr, map_add, map_add, map_mul, map_mul, aeval_C, aeval_C, aeval_C, aeval_X, map_pow, aeval_X,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_one_mul,
        smul_one_mul, add_mulVec, add_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, one_mulVec, pow_two,
        ← mulVec_mulVec]
      exact hg
    have hdvd := hv r hrA
    have hr0 : r = 0 := by
      by_contra hr0
      have h1 : (minpoly F A).natDegree ≤ r.natDegree := natDegree_le_of_dvd hdvd hr0
      have h2 : r.natDegree ≤ 2 := by
        rw [hr]
        refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
        · exact (natDegree_C _).le.trans (by norm_num)
        · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by norm_num))
        · exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le 2)
      omega
    have hcoeff : ∀ k, r.coeff k = 0 := fun k => by rw [hr0, coeff_zero]
    fin_cases i
    · simpa [hr] using hcoeff 0
    · simpa [hr] using hcoeff 1
    · simpa [hr] using hcoeff 2
  let b : Module.Basis (Fin 3) F (Fin 3 → F) := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : ⇑b = w := coe_basisOfLinearIndependentOfCardEqFinrank hli _

  have hrel : (minpoly F A).coeff 0 • v + (minpoly F A).coeff 1 • (A *ᵥ v) + (minpoly F A).coeff 2 • (A *ᵥ (A *ᵥ v))
      + A *ᵥ (A *ᵥ (A *ᵥ v)) = 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M *ᵥ v) (minpoly.aeval F A)
    have hc3 : (minpoly F A).coeff 3 = 1 := by
      have := (minpoly.monic (IsIntegral.of_finite (R := F) A)).coeff_natDegree
      rwa [h3] at this
    simp only [aeval_eq_sum_range, h3, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_succ,
      one_mul, hc3, one_smul, add_mulVec, smul_mulVec, one_mulVec, zero_mulVec, ← mulVec_mulVec] at h
    exact h
  refine isConj_of_toMatrix_eq b ?_
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply]
  have hcol : A *ᵥ b j = ∑ k, companion (minpoly F A) k j • b k := by
    rw [hb, Fin.sum_univ_three]
    fin_cases j
    · change A *ᵥ v = (0 : F) • v + (1 : F) • (A *ᵥ v) + (0 : F) • (A *ᵥ (A *ᵥ v))
      module
    · change A *ᵥ (A *ᵥ v) = (0 : F) • v + (0 : F) • (A *ᵥ v) + (1 : F) • (A *ᵥ (A *ᵥ v))
      module
    · change A *ᵥ (A *ᵥ (A *ᵥ v)) = (-(minpoly F A).coeff 0) • v + (-(minpoly F A).coeff 1) • (A *ᵥ v)
          + (-(minpoly F A).coeff 2) • (A *ᵥ (A *ᵥ v))
      linear_combination (norm := module) hrel
  rw [hcol, b.repr_sum_self]

end Matrix.Fin3Conj
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

end Fin3ConjCompanion
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

section Fin3ConjDegreeTwo

open Polynomial Module

namespace Matrix
p2m_export "Matrix" "transvection_mul_transvection_same J transpose diagonal_apply det_fin_three transpose_one diagonal_one sub_mulVec transvection_zero ext vecMul_diagonal swap charpoly_transpose add sub_apply smul_mulVec transvection det_diagonal sub zero IsIrreducible coe_units_inv map_smul' trace_conj' inv_def scalar one_mulVec trace_one transpose_transpose comp GeneralLinearGroup.det_ne_zero charpoly trace_mul_comm mulVecLin add_mulVec map_map toLin'_mul minpoly_toLin' mulVecLin_apply charpoly_natDegree_eq_dim transpose_pow rank smul det_transvection_of_ne transpose_eq_zero mulVec_mulVec compl zero_apply of_apply single GeneralLinearGroup charpoly_toLin' map_id ext_iff diagonal_mul one_apply neg_apply semiring smul_apply transpose_zero charpoly_monic toLinearEquiv det minpoly_dvd_charpoly toLin'_apply' GeneralLinearGroup.mkOfDetNeZero diagonal add_apply zero_mulVec comp_apply of sum_apply transpose_smul inv diagonal_transvection_induction_of_det_ne_zero toLin'_apply map GeneralLinearGroup.ext mulVec_zero toLin' one mul_apply unique trace transpose_mul charpoly.univ_coeff_eval₂Hom charpoly_units_conj charpoly.univ module nonempty transpose_add diagonal_mul_diagonal mul_diagonal mul_inv_rev"
namespace Fin3Conj
p2m_open "Matrix"

variable {F : Type} [Field F]

private theorem aeval_X_sub_C_eq {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n F) (a : F) :
    aeval A (X - C a) = A - a • (1 : Matrix n n F) := by
  rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]

private theorem isRoot_minpoly_of_isRoot_charpoly {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n F) {c : F}
    (h : A.charpoly.IsRoot c) : (minpoly F A).IsRoot c := by
  have h1 : Module.End.HasEigenvalue (Matrix.toLin' A) c := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, charpoly_toLin']
    exact h
  have h2 := (Module.End.hasEigenvalue_iff_isRoot (f := Matrix.toLin' A) (μ := c)).1 h1
  rwa [minpoly_toLin' (M := A)] at h2

private noncomputable def extraRoot (p m : F[X]) : F := -((p /ₘ m).coeff 0)

private theorem charpoly_eq_minpoly_mul_X_sub_C (A : Matrix (Fin 3) (Fin 3) F) (h2 : (minpoly F A).natDegree = 2) :
    A.charpoly = minpoly F A * (X - C (extraRoot A.charpoly (minpoly F A))) := by
  have hmonic : (minpoly F A).Monic := minpoly.monic (IsIntegral.of_finite (R := F) A)
  have hq : minpoly F A * (A.charpoly /ₘ minpoly F A) = A.charpoly := by
    have h := modByMonic_add_div A.charpoly (minpoly F A)
    rwa [(modByMonic_eq_zero_iff_dvd hmonic).2 (minpoly_dvd_charpoly A), zero_add] at h
  have hqmonic : (A.charpoly /ₘ minpoly F A).Monic := hmonic.of_mul_monic_left (by rw [hq]; exact charpoly_monic A)
  have hqdeg : (A.charpoly /ₘ minpoly F A).natDegree = 1 := by
    rw [natDegree_divByMonic _ hmonic, charpoly_natDegree_eq_dim, Fintype.card_fin, h2]
  have hqX : A.charpoly /ₘ minpoly F A = X - C (extraRoot A.charpoly (minpoly F A)) := by
    conv_lhs => rw [hqmonic.eq_X_add_C hqdeg]
    rw [extraRoot, map_neg, sub_neg_eq_add]
  rw [← hqX, hq]

private theorem isRoot_minpoly_extraRoot (A : Matrix (Fin 3) (Fin 3) F) (h2 : (minpoly F A).natDegree = 2) :
    (minpoly F A).IsRoot (extraRoot A.charpoly (minpoly F A)) := by
  refine isRoot_minpoly_of_isRoot_charpoly A ?_
  have h := charpoly_eq_minpoly_mul_X_sub_C A h2
  generalize extraRoot A.charpoly (minpoly F A) = c at h ⊢
  rw [h]
  show eval c (minpoly F A * (X - C c)) = 0
  rw [eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero]

private noncomputable def canonTwo (p m : F[X]) : Matrix (Fin 3) (Fin 3) F :=
  !![extraRoot p m, 0, 0; 0, 0, -m.coeff 0; 0, 1, -m.coeff 1]

private theorem isConj_canonTwo_of_minpoly_natDegree_eq_two [Infinite F] (A : Matrix (Fin 3) (Fin 3) F)
    (h2 : (minpoly F A).natDegree = 2) : IsConj (canonTwo A.charpoly (minpoly F A)) A := by
  classical
  obtain ⟨v, hv⟩ := exists_forall_aeval_mulVec_eq_zero_imp_minpoly_dvd A
  have hmonic : (minpoly F A).Monic := minpoly.monic (IsIntegral.of_finite (R := F) A)
  have hmaeval : aeval A (minpoly F A) = 0 := minpoly.aeval F A
  have hpfac := charpoly_eq_minpoly_mul_X_sub_C A h2
  have hcroot := isRoot_minpoly_extraRoot A h2
  have hφchar : (Matrix.toLin' A).charpoly = A.charpoly := charpoly_toLin' A
  generalize hm : minpoly F A = m at h2 hv hmonic hmaeval hpfac hcroot ⊢
  generalize hp : A.charpoly = p at hpfac hcroot hφchar ⊢
  generalize hc : extraRoot p m = c at hpfac hcroot

  have hm1 : (X - C c) * (m /ₘ (X - C c)) = m := mul_divByMonic_eq_iff_isRoot.2 hcroot
  have hm1monic : (m /ₘ (X - C c)).Monic := (monic_X_sub_C c).of_mul_monic_left (by rw [hm1]; exact hmonic)
  have hm1deg : (m /ₘ (X - C c)).natDegree = 1 := by
    rw [natDegree_divByMonic m (monic_X_sub_C c), h2, natDegree_X_sub_C]
  obtain ⟨b, hb⟩ : ∃ b : F, m /ₘ (X - C c) = X - C b := by
    refine ⟨-((m /ₘ (X - C c)).coeff 0), ?_⟩
    conv_lhs => rw [hm1monic.eq_X_add_C hm1deg]
    rw [map_neg, sub_neg_eq_add]
  have hmfac : m = (X - C c) * (X - C b) := by rw [← hb, hm1]
  have hmA : (A - c • (1 : Matrix (Fin 3) (Fin 3) F)) * (A - b • (1 : Matrix (Fin 3) (Fin 3) F)) = 0 := by
    have h := hmaeval
    rwa [hmfac, map_mul, aeval_X_sub_C_eq, aeval_X_sub_C_eq] at h
  have hmA' : (A - b • (1 : Matrix (Fin 3) (Fin 3) F)) * (A - c • (1 : Matrix (Fin 3) (Fin 3) F)) = 0 := by
    have h := hmaeval
    rwa [hmfac, mul_comm, map_mul, aeval_X_sub_C_eq, aeval_X_sub_C_eq] at h

  obtain ⟨E, hE⟩ : ∃ E : Submodule F (Fin 3 → F), E = Module.End.eigenspace (Matrix.toLin' A) c := ⟨_, rfl⟩
  have hmemE : ∀ x, x ∈ E ↔ A *ᵥ x = c • x := fun x => by
    rw [hE, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hEdim : 2 ≤ finrank F E := by
    by_cases hbc : b = c
    · rw [hbc] at hmA
      set N : (Fin 3 → F) →ₗ[F] (Fin 3 → F) := Matrix.toLin' (A - c • (1 : Matrix (Fin 3) (Fin 3) F)) with hN
      have hN2 : N ∘ₗ N = 0 := by rw [hN, ← Matrix.toLin'_mul, hmA, map_zero]
      have hrk : LinearMap.range N ≤ LinearMap.ker N := LinearMap.range_le_ker_iff.2 hN2
      have hker : LinearMap.ker N = E := by
        ext x
        rw [LinearMap.mem_ker, hN, Matrix.toLin'_apply, sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero, hmemE]
      have hsum := LinearMap.finrank_range_add_finrank_ker N
      rw [Module.finrank_fin_fun, hker] at hsum
      have hle := Submodule.finrank_mono hrk
      rw [hker] at hle
      omega
    · have hcb : c - b ≠ 0 := sub_ne_zero.2 fun h => hbc h.symm
      have hmemEb : ∀ x, x ∈ Module.End.eigenspace (Matrix.toLin' A) b ↔ A *ᵥ x = b • x := fun x => by
        rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      have hsup : E ⊔ Module.End.eigenspace (Matrix.toLin' A) b = ⊤ := by
        rw [eq_top_iff]
        intro x _
        set y : Fin 3 → F := (A - b • (1 : Matrix (Fin 3) (Fin 3) F)) *ᵥ x with hy
        set z : Fin 3 → F := (A - c • (1 : Matrix (Fin 3) (Fin 3) F)) *ᵥ x with hz
        have hyE : y ∈ E := by
          rw [hmemE]
          have h0 : (A - c • (1 : Matrix (Fin 3) (Fin 3) F)) *ᵥ y = 0 := by rw [hy, mulVec_mulVec, hmA, zero_mulVec]
          rwa [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at h0
        have hzEb : z ∈ Module.End.eigenspace (Matrix.toLin' A) b := by
          rw [hmemEb]
          have h0 : (A - b • (1 : Matrix (Fin 3) (Fin 3) F)) *ᵥ z = 0 := by rw [hz, mulVec_mulVec, hmA', zero_mulVec]
          rwa [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at h0
        have hx : (c - b) • x = y - z := by
          rw [hy, hz, sub_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, one_mulVec]
          module
        have hx' : x = (c - b)⁻¹ • (y - z) := by rw [← hx, smul_smul, inv_mul_cancel₀ hcb, one_smul]
        rw [hx', sub_eq_add_neg y z]
        exact Submodule.smul_mem _ _ (Submodule.add_mem_sup hyE (Submodule.neg_mem _ hzEb))
      have h3 := Submodule.finrank_add_le_finrank_add_finrank E (Module.End.eigenspace (Matrix.toLin' A) b)
      rw [hsup, finrank_top, Module.finrank_fin_fun] at h3
      have h4 := LinearMap.finrank_eigenspace_le (Matrix.toLin' A) b
      rw [hφchar] at h4
      have hnot : ¬ (X - C c).IsRoot b := by
        intro h
        apply hbc
        have h' : eval b (X - C c) = 0 := h
        rw [eval_sub, eval_X, eval_C] at h'
        exact sub_eq_zero.1 h'
      have h5 : rootMultiplicity b p = 1 := by
        rw [hpfac, hmfac, rootMultiplicity_mul (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero c) (X_sub_C_ne_zero b))
          (X_sub_C_ne_zero c)), rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero c) (X_sub_C_ne_zero b)),
          rootMultiplicity_X_sub_C_self, rootMultiplicity_eq_zero hnot]
      omega

  have hli2 : LinearIndependent F ![v, A *ᵥ v] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fin.sum_univ_two] at hg
    change g 0 • v + g 1 • (A *ᵥ v) = 0 at hg
    set r : F[X] := C (g 0) + C (g 1) * X with hr
    have hrA : aeval A r *ᵥ v = 0 := by
      rw [hr, map_add, map_mul, aeval_C, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, smul_one_mul, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec]
      exact hg
    have hr0 : r = 0 := by
      by_contra hr0
      have h1 : m.natDegree ≤ r.natDegree := natDegree_le_of_dvd (hv r hrA) hr0
      have h1' : r.natDegree ≤ 1 := by
        rw [hr]
        exact (natDegree_add_le _ _).trans
          (max_le ((natDegree_C _).le.trans (Nat.zero_le 1)) ((natDegree_C_mul_le _ _).trans natDegree_X_le))
      omega
    have hcoeff : ∀ k, r.coeff k = 0 := fun k => by rw [hr0, coeff_zero]
    fin_cases i
    · simpa [hr] using hcoeff 0
    · simpa [hr] using hcoeff 1
  have hW : finrank F (Submodule.span F (Set.range ![v, A *ᵥ v])) = 2 := by
    rw [finrank_span_eq_card hli2, Fintype.card_fin]
  have hEW : ¬ E ≤ Submodule.span F (Set.range ![v, A *ᵥ v]) := by
    intro hle
    have heq : E = Submodule.span F (Set.range ![v, A *ᵥ v]) :=
      Submodule.eq_of_le_of_finrank_le hle (by rw [hW]; exact hEdim)
    have hvE : v ∈ E := by
      rw [heq]
      exact Submodule.subset_span ⟨0, rfl⟩
    rw [hmemE] at hvE
    have hkill : aeval A (X - C c) *ᵥ v = 0 := by
      rw [aeval_X_sub_C_eq, sub_mulVec, smul_mulVec, one_mulVec, hvE, sub_self]
    have hdeg := natDegree_le_of_dvd (hv _ hkill) (X_sub_C_ne_zero c)
    rw [natDegree_X_sub_C] at hdeg
    omega
  obtain ⟨w, hwE, hwW⟩ := SetLike.not_le_iff_exists.1 hEW
  have hAw : A *ᵥ w = c • w := (hmemE w).1 hwE
  have hli3 : LinearIndependent F ![w, v, A *ᵥ v] := linearIndependent_finCons.2 ⟨hli2, hwW⟩
  let bb : Basis (Fin 3) F (Fin 3 → F) := basisOfLinearIndependentOfCardEqFinrank hli3 (by simp)
  have hbb : ⇑bb = ![w, v, A *ᵥ v] := coe_basisOfLinearIndependentOfCardEqFinrank hli3 _

  have hrel : m.coeff 0 • v + m.coeff 1 • (A *ᵥ v) + A *ᵥ (A *ᵥ v) = 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M *ᵥ v) hmaeval
    have hc2 : m.coeff 2 = 1 := by
      have h' := hmonic.coeff_natDegree
      rwa [h2] at h'
    simp only [aeval_eq_sum_range, h2, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_succ,
      one_mul, hc2, one_smul, add_mulVec, smul_mulVec, one_mulVec, zero_mulVec, ← mulVec_mulVec] at h
    exact h
  refine isConj_of_toMatrix_eq bb ?_
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply]
  have hcol : A *ᵥ bb j = ∑ k, canonTwo p m k j • bb k := by
    rw [hbb, Fin.sum_univ_three]
    fin_cases j
    · change A *ᵥ w = extraRoot p m • w + (0 : F) • v + (0 : F) • (A *ᵥ v)
      rw [hAw, hc]
      module
    · change A *ᵥ v = (0 : F) • w + (0 : F) • v + (1 : F) • (A *ᵥ v)
      module
    · change A *ᵥ (A *ᵥ v) = (0 : F) • w + (-m.coeff 0) • v + (-m.coeff 1) • (A *ᵥ v)
      linear_combination (norm := module) hrel
  rw [hcol, bb.repr_sum_self]

end Matrix.Fin3Conj
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

end Fin3ConjDegreeTwo
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

section Fin3ConjEngine

open Polynomial

namespace Matrix
p2m_export "Matrix" "transvection_mul_transvection_same J transpose diagonal_apply det_fin_three transpose_one diagonal_one sub_mulVec transvection_zero ext vecMul_diagonal swap charpoly_transpose add sub_apply smul_mulVec transvection det_diagonal sub zero IsIrreducible coe_units_inv map_smul' trace_conj' inv_def scalar one_mulVec trace_one transpose_transpose comp GeneralLinearGroup.det_ne_zero charpoly trace_mul_comm mulVecLin add_mulVec map_map toLin'_mul minpoly_toLin' mulVecLin_apply charpoly_natDegree_eq_dim transpose_pow rank smul det_transvection_of_ne transpose_eq_zero mulVec_mulVec compl zero_apply of_apply single GeneralLinearGroup charpoly_toLin' map_id ext_iff diagonal_mul one_apply neg_apply semiring smul_apply transpose_zero charpoly_monic toLinearEquiv det minpoly_dvd_charpoly toLin'_apply' GeneralLinearGroup.mkOfDetNeZero diagonal add_apply zero_mulVec comp_apply of sum_apply transpose_smul inv diagonal_transvection_induction_of_det_ne_zero toLin'_apply map GeneralLinearGroup.ext mulVec_zero toLin' one mul_apply unique trace transpose_mul charpoly.univ_coeff_eval₂Hom charpoly_units_conj charpoly.univ module nonempty transpose_add diagonal_mul_diagonal mul_diagonal mul_inv_rev"
namespace Fin3Conj
p2m_open "Matrix"

variable {F : Type} [Field F]

private theorem minpoly_natDegree_le_three (A : Matrix (Fin 3) (Fin 3) F) : (minpoly F A).natDegree ≤ 3 := by
  have h := natDegree_le_of_dvd (minpoly_dvd_charpoly A) (charpoly_monic A).ne_zero
  rwa [charpoly_natDegree_eq_dim, Fintype.card_fin] at h

private theorem minpoly_natDegree_pos (A : Matrix (Fin 3) (Fin 3) F) : 0 < (minpoly F A).natDegree :=
  minpoly.natDegree_pos (IsIntegral.of_finite (R := F) A)

private theorem isConj_of_charpoly_eq_of_minpoly_eq [Infinite F] (A B : Matrix (Fin 3) (Fin 3) F)
    (hp : A.charpoly = B.charpoly) (hm : minpoly F A = minpoly F B) : IsConj A B := by
  have hle := minpoly_natDegree_le_three A
  have hpos := minpoly_natDegree_pos A
  rcases (show (minpoly F A).natDegree = 1 ∨ (minpoly F A).natDegree = 2 ∨ (minpoly F A).natDegree = 3 by omega)
    with h1 | h2 | h3
  ·
    have hmonic : (minpoly F A).Monic := minpoly.monic (IsIntegral.of_finite (R := F) A)
    have hX := hmonic.eq_X_add_C h1
    have hA : A = (-(minpoly F A).coeff 0) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      have h := minpoly.aeval F A
      rw [hX, map_add, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left h
    have hB : B = (-(minpoly F A).coeff 0) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      have h := minpoly.aeval F B
      rw [← hm, hX, map_add, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left h
    have hAB : A = B := hA.trans hB.symm
    rw [hAB]
  · have hA := isConj_canonTwo_of_minpoly_natDegree_eq_two A h2
    have hB := isConj_canonTwo_of_minpoly_natDegree_eq_two B (by rw [← hm]; exact h2)
    rw [← hp, ← hm] at hB
    exact hA.symm.trans hB
  · have hA := isConj_companion_of_minpoly_natDegree_eq_three A h3
    have hB := isConj_companion_of_minpoly_natDegree_eq_three B (by rw [← hm]; exact h3)
    rw [← hm] at hB
    exact hA.symm.trans hB

private theorem isConj_transpose [Infinite F] (A : Matrix (Fin 3) (Fin 3) F) : IsConj Aᵀ A :=
  isConj_of_charpoly_eq_of_minpoly_eq Aᵀ A (charpoly_transpose A) (minpoly_transpose A)

end Matrix.Fin3Conj
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

end Fin3ConjEngine
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

section Fin3ConjFibre

open Polynomial

namespace Matrix
p2m_export "Matrix" "transvection_mul_transvection_same J transpose diagonal_apply det_fin_three transpose_one diagonal_one sub_mulVec transvection_zero ext vecMul_diagonal swap charpoly_transpose add sub_apply smul_mulVec transvection det_diagonal sub zero IsIrreducible coe_units_inv map_smul' trace_conj' inv_def scalar one_mulVec trace_one transpose_transpose comp GeneralLinearGroup.det_ne_zero charpoly trace_mul_comm mulVecLin add_mulVec map_map toLin'_mul minpoly_toLin' mulVecLin_apply charpoly_natDegree_eq_dim transpose_pow rank smul det_transvection_of_ne transpose_eq_zero mulVec_mulVec compl zero_apply of_apply single GeneralLinearGroup charpoly_toLin' map_id ext_iff diagonal_mul one_apply neg_apply semiring smul_apply transpose_zero charpoly_monic toLinearEquiv det minpoly_dvd_charpoly toLin'_apply' GeneralLinearGroup.mkOfDetNeZero diagonal add_apply zero_mulVec comp_apply of sum_apply transpose_smul inv diagonal_transvection_induction_of_det_ne_zero toLin'_apply map GeneralLinearGroup.ext mulVec_zero toLin' one mul_apply unique trace transpose_mul charpoly.univ_coeff_eval₂Hom charpoly_units_conj charpoly.univ module nonempty transpose_add diagonal_mul_diagonal mul_diagonal mul_inv_rev"
namespace Fin3Conj
p2m_open "Matrix"

variable {F : Type} [Field F]

private theorem eq_of_two_le_rootMultiplicity {p : F[X]} (hp : p.natDegree ≤ 3) {a b : F}
    (ha : 2 ≤ rootMultiplicity a p) (hb : 2 ≤ rootMultiplicity b p) : a = b := by
  classical
  by_contra hab
  have ha' : a ∈ p.roots := Multiset.count_pos.1 (by rw [count_roots]; omega)
  have hb' : b ∈ p.roots := Multiset.count_pos.1 (by rw [count_roots]; omega)
  have hsub : ({a, b} : Finset F) ⊆ p.roots.toFinset :=
    Finset.insert_subset (Multiset.mem_toFinset.2 ha') (Finset.singleton_subset_iff.2 (Multiset.mem_toFinset.2 hb'))
  have h1 := Finset.sum_le_sum_of_subset (f := fun x => p.roots.count x) hsub
  rw [Multiset.toFinset_sum_count_eq, Finset.sum_pair hab] at h1
  simp only [count_roots] at h1
  have h2 := card_roots' p
  omega

private theorem
    minpoly_eq_of_charpoly_eq_of_natDegree_eq (A B : Matrix (Fin 3) (Fin 3) F) (hp : A.charpoly = B.charpoly)
    (hd : (minpoly F A).natDegree = (minpoly F B).natDegree) : minpoly F A = minpoly F B := by
  have hAm : (minpoly F A).Monic := minpoly.monic (IsIntegral.of_finite (R := F) A)
  have hBm : (minpoly F B).Monic := minpoly.monic (IsIntegral.of_finite (R := F) B)
  have hAdvd : minpoly F A ∣ A.charpoly := minpoly_dvd_charpoly A
  have hBdvd : minpoly F B ∣ A.charpoly := by
    rw [hp]
    exact minpoly_dvd_charpoly B
  have hpdeg : A.charpoly.natDegree = 3 := by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hle := minpoly_natDegree_le_three A
  have hpos := minpoly_natDegree_pos A
  rcases (show (minpoly F A).natDegree = 1 ∨ (minpoly F A).natDegree = 2 ∨ (minpoly F A).natDegree = 3 by omega)
    with h1 | h2 | h3
  ·
    obtain ⟨k, hk⟩ : ∃ k : F, minpoly F A = X + C k := ⟨_, hAm.eq_X_add_C h1⟩
    obtain ⟨l, hl⟩ : ∃ l : F, minpoly F B = X + C l := ⟨_, hBm.eq_X_add_C (by rw [← hd]; exact h1)⟩
    have hrootA : (minpoly F A).IsRoot (-k) := by
      rw [hk]
      show eval (-k) (X + C k) = 0
      rw [eval_add, eval_X, eval_C, neg_add_cancel]
    have hrootB : (minpoly F B).IsRoot (-k) := by
      refine isRoot_minpoly_of_isRoot_charpoly B ?_
      rw [← hp]
      exact hrootA.dvd hAdvd
    rw [hl] at hrootB
    have h' : eval (-k) (X + C l) = 0 := hrootB
    rw [eval_add, eval_X, eval_C] at h'
    have hlk : l = k := by linear_combination h'
    rw [hk, hl, hlk]
  ·
    have hA1 := charpoly_eq_minpoly_mul_X_sub_C A h2
    have hA2 := isRoot_minpoly_extraRoot A h2
    have h2B : (minpoly F B).natDegree = 2 := by rw [← hd]; exact h2
    have hB1 := charpoly_eq_minpoly_mul_X_sub_C B h2B
    have hB2 := isRoot_minpoly_extraRoot B h2B
    rw [← hp] at hB1 hB2
    generalize extraRoot A.charpoly (minpoly F A) = a at hA1 hA2
    generalize extraRoot A.charpoly (minpoly F B) = b at hB1 hB2
    have hp0 : A.charpoly ≠ 0 := (charpoly_monic A).ne_zero
    have hma : 2 ≤ rootMultiplicity a A.charpoly := by
      have hne : minpoly F A * (X - C a) ≠ 0 := by rw [← hA1]; exact hp0
      have h0 := (rootMultiplicity_pos hAm.ne_zero).2 hA2
      rw [hA1, rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_self]
      omega
    have hmb : 2 ≤ rootMultiplicity b A.charpoly := by
      have hne : minpoly F B * (X - C b) ≠ 0 := by rw [← hB1]; exact hp0
      have h0 := (rootMultiplicity_pos hBm.ne_zero).2 hB2
      rw [hB1, rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_self]
      omega
    have hab : a = b := eq_of_two_le_rootMultiplicity hpdeg.le hma hmb
    subst hab
    exact mul_right_cancel₀ (X_sub_C_ne_zero _) (hA1.symm.trans hB1)
  ·
    have h3B : (minpoly F B).natDegree = 3 := by rw [← hd]; exact h3
    have hA' := eq_of_monic_of_dvd_of_natDegree_le hAm (charpoly_monic A) hAdvd (le_of_eq (by rw [hpdeg, h3]))
    have hB' := eq_of_monic_of_dvd_of_natDegree_le hBm (charpoly_monic A) hBdvd (le_of_eq (by rw [hpdeg, h3B]))
    exact hA'.symm.trans hB'

private theorem isConj_of_charpoly_eq_of_minpoly_natDegree_eq [Infinite F] (A B : Matrix (Fin 3) (Fin 3) F)
    (hp : A.charpoly = B.charpoly) (hd : (minpoly F A).natDegree = (minpoly F B).natDegree) : IsConj A B :=
  isConj_of_charpoly_eq_of_minpoly_eq A B hp (minpoly_eq_of_charpoly_eq_of_natDegree_eq A B hp hd)

private def minpolySet (p : F[X]) : Set F[X] :=
  {m | ∃ A : Matrix (Fin 3) (Fin 3) F, A.charpoly = p ∧ minpoly F A = m}

private theorem subsingleton_setOf_mem_minpolySet_natDegree_eq (p : F[X]) (k : ℕ) :
    {m | m ∈ minpolySet p ∧ m.natDegree = k}.Subsingleton := by
  rintro m ⟨⟨A, hA, rfl⟩, hk⟩ m' ⟨⟨B, hB, rfl⟩, hk'⟩
  exact minpoly_eq_of_charpoly_eq_of_natDegree_eq A B (hA.trans hB.symm) (hk.trans hk'.symm)

private theorem finite_minpolySet (p : F[X]) : (minpolySet p).Finite := by
  have h : ∀ k : ℕ, {m | m ∈ minpolySet p ∧ m.natDegree = k}.Finite := fun k =>
    (subsingleton_setOf_mem_minpolySet_natDegree_eq p k).finite
  refine (((h 1).union (h 2)).union (h 3)).subset ?_
  rintro m ⟨A, hA, rfl⟩
  have hle := minpoly_natDegree_le_three A
  have hpos := minpoly_natDegree_pos A
  rcases (show (minpoly F A).natDegree = 1 ∨ (minpoly F A).natDegree = 2 ∨ (minpoly F A).natDegree = 3 by omega)
    with h1 | h2 | h3
  · exact Or.inl (Or.inl ⟨⟨A, hA, rfl⟩, h1⟩)
  · exact Or.inl (Or.inr ⟨⟨A, hA, rfl⟩, h2⟩)
  · exact Or.inr ⟨⟨A, hA, rfl⟩, h3⟩

private theorem minpoly_natDegree_le_iff (p : F[X]) (k : ℕ) (A : Matrix (Fin 3) (Fin 3) F) (hA : A.charpoly = p) :
    (minpoly F A).natDegree ≤ k ↔ ∃ m ∈ minpolySet p, m.natDegree ≤ k ∧ aeval A m = 0 := by
  constructor
  · intro h
    exact ⟨minpoly F A, ⟨A, hA, rfl⟩, h, minpoly.aeval F A⟩
  · rintro ⟨m, ⟨B, -, rfl⟩, hk, hm⟩
    have hdvd : minpoly F A ∣ minpoly F B := minpoly.dvd F A hm
    have hne : minpoly F B ≠ 0 := (minpoly.monic (IsIntegral.of_finite (R := F) B)).ne_zero
    exact (natDegree_le_of_dvd hdvd hne).trans hk

end Matrix.Fin3Conj
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

end Fin3ConjFibre
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

section Strata
open LanglandsTunnell.CubicInduction.TransposeTwist

open Polynomial MulAction

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.localMaximalCompact3 CubicInduction.mem_localMaximalCompact3_iff CubicInduction.transposeInv3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localMaximalCompact3 mem_localMaximalCompact3_iff transposeInv3 LocalGL3"
namespace Strata
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable {F : Type} [Field F]

private def stratumLE (y : Fin 3 → F) (k : ℕ) : Set (GL (Fin 3) F) :=
  {g | Localisation.charpolyCoeffs (g : Matrix (Fin 3) (Fin 3) F) = y ∧
    (minpoly F (g : Matrix (Fin 3) (Fin 3) F)).natDegree ≤ k}

private def stratum (y : Fin 3 → F) (k : ℕ) : Set (GL (Fin 3) F) :=
  {g | Localisation.charpolyCoeffs (g : Matrix (Fin 3) (Fin 3) F) = y ∧
    (minpoly F (g : Matrix (Fin 3) (Fin 3) F)).natDegree = k}

private theorem mem_stratumLE {y : Fin 3 → F} {k : ℕ} {g : GL (Fin 3) F} :
    g ∈ stratumLE y k ↔ Localisation.charpolyCoeffs (g : Matrix (Fin 3) (Fin 3) F) = y ∧
      (minpoly F (g : Matrix (Fin 3) (Fin 3) F)).natDegree ≤ k :=
  Iff.rfl

private theorem mem_stratum {y : Fin 3 → F} {k : ℕ} {g : GL (Fin 3) F} :
    g ∈ stratum y k ↔ Localisation.charpolyCoeffs (g : Matrix (Fin 3) (Fin 3) F) = y ∧
      (minpoly F (g : Matrix (Fin 3) (Fin 3) F)).natDegree = k :=
  Iff.rfl

private theorem stratum_zero (y : Fin 3 → F) : stratum y 0 = ∅ := by
  ext g
  rw [mem_stratum]
  constructor
  · rintro ⟨-, h⟩
    exact absurd h (Matrix.Fin3Conj.minpoly_natDegree_pos (g : Matrix (Fin 3) (Fin 3) F)).ne'
  · intro h
    exact absurd h (Set.notMem_empty g)

private theorem stratumLE_three (y : Fin 3 → F) :
    stratumLE y 3 = {g : GL (Fin 3) F | Localisation.charpolyCoeffs (g : Matrix (Fin 3) (Fin 3) F) = y} := by
  ext g
  rw [mem_stratumLE, Set.mem_setOf_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, Matrix.Fin3Conj.minpoly_natDegree_le_three _⟩⟩

private theorem stratumLE_diff_eq_stratum (y : Fin 3 → F) (k : ℕ) :
    stratumLE y (k + 1) \ stratumLE y k = stratum y (k + 1) := by
  ext g
  rw [Set.mem_diff, mem_stratumLE, mem_stratumLE, mem_stratum]
  constructor
  · rintro ⟨⟨hy, hle⟩, hnot⟩
    refine ⟨hy, ?_⟩
    have hk : ¬ (minpoly F (g : Matrix (Fin 3) (Fin 3) F)).natDegree ≤ k := fun h => hnot ⟨hy, h⟩
    omega
  · rintro ⟨hy, hk⟩
    exact ⟨⟨hy, hk.le⟩, fun h => by omega⟩

private theorem charpolyCoeffs_transpose (A : Matrix (Fin 3) (Fin 3) F) :
    Localisation.charpolyCoeffs A.transpose = Localisation.charpolyCoeffs A := by
  funext i
  rw [Localisation.charpolyCoeffs_apply, Localisation.charpolyCoeffs_apply, Matrix.charpoly_transpose]

private theorem transposeInv3_inv_transposeInv3_inv (g : GL (Fin 3) F) :
    (transposeInv3 (transposeInv3 g)⁻¹)⁻¹ = g := by
  rw [transposeInv3_inv, transposeInv3_transposeInv3, inv_inv]

private theorem transposeInv3_inv_mem_stratumLE_iff (y : Fin 3 → F) (k : ℕ) (g : GL (Fin 3) F) :
    (transposeInv3 g)⁻¹ ∈ stratumLE y k ↔ g ∈ stratumLE y k := by
  rw [mem_stratumLE, mem_stratumLE, coe_transposeInv3_inv, charpolyCoeffs_transpose,
    Matrix.Fin3Conj.minpoly_transpose]

private theorem transposeInv3_inv_mem_stratum_iff (y : Fin 3 → F) (k : ℕ) (g : GL (Fin 3) F) :
    (transposeInv3 g)⁻¹ ∈ stratum y k ↔ g ∈ stratum y k := by
  rw [mem_stratum, mem_stratum, coe_transposeInv3_inv, charpolyCoeffs_transpose,
    Matrix.Fin3Conj.minpoly_transpose]

private theorem minpoly_units_conj (u : (Matrix (Fin 3) (Fin 3) F)ˣ) (A : Matrix (Fin 3) (Fin 3) F) :
    minpoly F ((u : Matrix (Fin 3) (Fin 3) F) * A * ((u⁻¹ : (Matrix (Fin 3) (Fin 3) F)ˣ) :
      Matrix (Fin 3) (Fin 3) F)) = minpoly F A := by
  have h := minpoly.algEquiv_eq
    (MulSemiringAction.toAlgEquiv F (Matrix (Fin 3) (Fin 3) F) (ConjAct.toConjAct u)) A
  have he : MulSemiringAction.toAlgEquiv F (Matrix (Fin 3) (Fin 3) F) (ConjAct.toConjAct u) A =
      (u : Matrix (Fin 3) (Fin 3) F) * A * ((u⁻¹ : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F) := by
    show ConjAct.toConjAct u • A = _
    rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  rwa [he] at h

private theorem charpolyCoeffs_units_conj (u : (Matrix (Fin 3) (Fin 3) F)ˣ) (A : Matrix (Fin 3) (Fin 3) F) :
    Localisation.charpolyCoeffs ((u : Matrix (Fin 3) (Fin 3) F) * A *
      ((u⁻¹ : (Matrix (Fin 3) (Fin 3) F)ˣ) : Matrix (Fin 3) (Fin 3) F)) = Localisation.charpolyCoeffs A := by
  funext i
  rw [Localisation.charpolyCoeffs_apply, Localisation.charpolyCoeffs_apply, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj]

private theorem orbit_subset_stratum (y : Fin 3 → F) (k : ℕ) {g : GL (Fin 3) F} (hg : g ∈ stratum y k) :
    orbit (ConjAct (GL (Fin 3) F)) g ⊆ stratum y k := by
  rintro _ ⟨c, rfl⟩
  show c • g ∈ stratum y k
  obtain ⟨hy, hk⟩ := mem_stratum.mp hg
  rw [mem_stratum, ConjAct.smul_def, Units.val_mul, Units.val_mul, charpolyCoeffs_units_conj, minpoly_units_conj]
  exact ⟨hy, hk⟩

private theorem stratum_eq_orbit [Infinite F] (y : Fin 3 → F) (k : ℕ) {g : GL (Fin 3) F} (hg : g ∈ stratum y k) :
    stratum y k = orbit (ConjAct (GL (Fin 3) F)) g := by
  refine Set.Subset.antisymm (fun h hh => ?_) (orbit_subset_stratum y k hg)
  obtain ⟨hgy, hgk⟩ := mem_stratum.mp hg
  obtain ⟨hhy, hhk⟩ := mem_stratum.mp hh
  rw [ConjOrbit.mem_orbit_iff_isConj, ← ConjOrbit.isConj_val_iff]
  exact Matrix.Fin3Conj.isConj_of_charpoly_eq_of_minpoly_natDegree_eq _ _
    (Localisation.charpoly_eq_of_charpolyCoeffs_eq (hgy.trans hhy.symm)) (hgk.trans hhk.symm)

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]

private theorem isClosed_setOf_charpolyCoeffs_eq_and_minpoly_natDegree_le (y : Fin 3 → F) (k : ℕ) :
    IsClosed {A : Matrix (Fin 3) (Fin 3) F |
      Localisation.charpolyCoeffs A = y ∧ (minpoly F A).natDegree ≤ k} := by
  have hfib : IsClosed {A : Matrix (Fin 3) (Fin 3) F | Localisation.charpolyCoeffs A = y} :=
    isClosed_singleton.preimage (Localisation.continuous_charpolyCoeffs continuous_id)
  by_cases hne : ∃ A₀ : Matrix (Fin 3) (Fin 3) F, Localisation.charpolyCoeffs A₀ = y
  · obtain ⟨A₀, hA₀⟩ := hne
    set S : Set F[X] := {m | m ∈ Matrix.Fin3Conj.minpolySet A₀.charpoly ∧ m.natDegree ≤ k} with hS
    have hSfin : S.Finite := (Matrix.Fin3Conj.finite_minpolySet A₀.charpoly).subset fun m hm => hm.1
    have hZ : IsClosed (⋃ m ∈ S, {A : Matrix (Fin 3) (Fin 3) F | aeval A m = 0}) :=
      hSfin.isClosed_biUnion fun m _ => isClosed_singleton.preimage (Polynomial.continuous_aeval m)
    have hcharpoly : ∀ A : Matrix (Fin 3) (Fin 3) F, Localisation.charpolyCoeffs A = y →
        A.charpoly = A₀.charpoly := fun A hA =>
      Localisation.charpoly_eq_of_charpolyCoeffs_eq (hA.trans hA₀.symm)
    have heq : {A : Matrix (Fin 3) (Fin 3) F | Localisation.charpolyCoeffs A = y ∧ (minpoly F A).natDegree ≤ k} =
        {A : Matrix (Fin 3) (Fin 3) F | Localisation.charpolyCoeffs A = y} ∩
          ⋃ m ∈ S, {A : Matrix (Fin 3) (Fin 3) F | aeval A m = 0} := by
      ext A
      rw [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hy, hk⟩
        obtain ⟨m, hm, hmk, hm0⟩ :=
          (Matrix.Fin3Conj.minpoly_natDegree_le_iff A₀.charpoly k A (hcharpoly A hy)).1 hk
        exact ⟨hy, Set.mem_iUnion₂.2 ⟨m, ⟨hm, hmk⟩, hm0⟩⟩
      · rintro ⟨hy, hmem⟩
        obtain ⟨m, ⟨hm, hmk⟩, hm0⟩ := Set.mem_iUnion₂.1 hmem
        exact ⟨hy, (Matrix.Fin3Conj.minpoly_natDegree_le_iff A₀.charpoly k A (hcharpoly A hy)).2
          ⟨m, hm, hmk, hm0⟩⟩
    rw [heq]
    exact hfib.inter hZ
  · have hempty : {A : Matrix (Fin 3) (Fin 3) F |
        Localisation.charpolyCoeffs A = y ∧ (minpoly F A).natDegree ≤ k} = ∅ := by
      ext A
      rw [Set.mem_setOf_eq]
      exact ⟨fun h => hne ⟨A, h.1⟩, fun h => absurd h (Set.notMem_empty A)⟩
    rw [hempty]
    exact isClosed_empty

private theorem isClosed_stratumLE (y : Fin 3 → F) (k : ℕ) : IsClosed (stratumLE y k) :=
  (isClosed_setOf_charpolyCoeffs_eq_and_minpoly_natDegree_le y k).preimage Units.continuous_val

private theorem isLocallyClosed_stratum (y : Fin 3 → F) (k : ℕ) : IsLocallyClosed (stratum y k) := by
  cases k with
  | zero =>
    rw [stratum_zero]
    exact ⟨∅, ∅, isOpen_empty, isClosed_empty, (Set.empty_inter ∅).symm⟩
  | succ k =>
    rw [← stratumLE_diff_eq_stratum]
    exact ⟨(stratumLE y k)ᶜ, stratumLE y (k + 1), (isClosed_stratumLE y k).isOpen_compl,
      isClosed_stratumLE y (k + 1), Set.diff_eq_compl_inter⟩

private theorem isLocallyClosed_orbit_of_mem_stratum [Infinite F] (y : Fin 3 → F) (k : ℕ) {g : GL (Fin 3) F}
    (hg : g ∈ stratum y k) : IsLocallyClosed (orbit (ConjAct (GL (Fin 3) F)) g : Set (GL (Fin 3) F)) := by
  rw [← stratum_eq_orbit y k hg]
  exact isLocallyClosed_stratum y k

end Topology
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

end LanglandsTunnell.CubicInduction.Strata
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

end Strata
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

section ClassInvariance
open LanglandsTunnell.CubicInduction.TransposeTwist

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.localMaximalCompact3 CubicInduction.mem_localMaximalCompact3_iff CubicInduction.transposeInv3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localMaximalCompact3 mem_localMaximalCompact3_iff transposeInv3 LocalGL3"
namespace ClassInvariance
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open MulAction InvariantFunctional

section Group

variable {F : Type*} [Field F]

private theorem transposeInv3_inv_conj (a y : GL (Fin 3) F) :
    (transposeInv3 (a * y * a⁻¹))⁻¹ = transposeInv3 a * (transposeInv3 y)⁻¹ * (transposeInv3 a)⁻¹ := by
  rw [transposeInv3_mul, transposeInv3_mul, transposeInv3_inv]
  group

private def tauConj (c : ConjAct (GL (Fin 3) F)) : ConjAct (GL (Fin 3) F) :=
  ConjAct.toConjAct (transposeInv3 (ConjAct.ofConjAct c))

private theorem ofConjAct_tauConj (c : ConjAct (GL (Fin 3) F)) :
    ConjAct.ofConjAct (tauConj c) = transposeInv3 (ConjAct.ofConjAct c) :=
  ConjAct.ofConjAct_toConjAct _

private theorem tauConj_inv (c : ConjAct (GL (Fin 3) F)) : tauConj c⁻¹ = (tauConj c)⁻¹ := by
  unfold tauConj
  rw [ConjAct.ofConjAct_inv, transposeInv3_inv, ConjAct.toConjAct_inv]

private theorem tauConj_tauConj (c : ConjAct (GL (Fin 3) F)) : tauConj (tauConj c) = c := by
  unfold tauConj
  rw [ConjAct.ofConjAct_toConjAct, transposeInv3_transposeInv3, ConjAct.toConjAct_ofConjAct]

private theorem transposeInv3_inv_smul (c : ConjAct (GL (Fin 3) F)) (y : GL (Fin 3) F) :
    (transposeInv3 (c • y))⁻¹ = tauConj c • (transposeInv3 y)⁻¹ := by
  rw [ConjAct.smul_def, ConjAct.smul_def, ofConjAct_tauConj, transposeInv3_inv_conj]

end Group
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

section Carrier

variable {F : Type*} [Field F] (S : SubMulAction (ConjAct (GL (Fin 3) F)) (GL (Fin 3) F))
  (hθS : ∀ y ∈ S, (transposeInv3 y)⁻¹ ∈ S)

private def thetaS (y : ↥S) : ↥S :=
  ⟨(transposeInv3 (y : GL (Fin 3) F))⁻¹, hθS _ y.2⟩

@[scoped simp] private theorem coe_thetaS (y : ↥S) :
    (thetaS S hθS y : GL (Fin 3) F) = (transposeInv3 (y : GL (Fin 3) F))⁻¹ :=
  rfl

private theorem thetaS_involutive : Function.Involutive (thetaS S hθS) := fun y =>
  Subtype.ext (by
    show (transposeInv3 (transposeInv3 (y : GL (Fin 3) F))⁻¹)⁻¹ = (y : GL (Fin 3) F)
    rw [transposeInv3_inv, transposeInv3_transposeInv3, inv_inv])

private theorem thetaS_smul (c : ConjAct (GL (Fin 3) F)) (y : ↥S) :
    thetaS S hθS (c • y) = tauConj c • thetaS S hθS y :=
  Subtype.ext (by
    simp only [coe_thetaS, SetLike.val_smul, transposeInv3_inv_smul])

variable [TopologicalSpace F]

private theorem continuous_thetaS : Continuous (thetaS S hθS) :=
  (continuous_transposeInv3_inv.comp continuous_subtype_val).subtype_mk fun y => hθS _ y.2

variable {S} in

private scoped instance instContinuousSMul [IsTopologicalGroup (GL (Fin 3) F)] :
    ContinuousSMul (ConjAct (GL (Fin 3) F)) ↥S :=
  ⟨(SMulMemClass.continuousSMul S).continuous_smul⟩

end Carrier
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

section Class

variable {F : Type*} [Field F] (S : SubMulAction (ConjAct (GL (Fin 3) F)) (GL (Fin 3) F)) (x₀ : GL (Fin 3) F)
  (hS : (S : Set (GL (Fin 3) F)) = orbit (ConjAct (GL (Fin 3) F)) x₀)

include hS

private theorem mem_of_coe_eq_orbit : x₀ ∈ S := by
  rw [← SetLike.mem_coe, hS]
  exact mem_orbit_self x₀

private theorem isPretransitive_of_coe_eq_orbit : IsPretransitive (ConjAct (GL (Fin 3) F)) ↥S := by
  constructor
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  have ha' : a ∈ orbit (ConjAct (GL (Fin 3) F)) x₀ := by
    rw [← hS]
    exact ha
  have hb' : b ∈ orbit (ConjAct (GL (Fin 3) F)) x₀ := by
    rw [← hS]
    exact hb
  obtain ⟨c, rfl⟩ := MulAction.mem_orbit_iff.1 ha'
  obtain ⟨d, rfl⟩ := MulAction.mem_orbit_iff.1 hb'
  refine ⟨d * c⁻¹, Subtype.ext ?_⟩
  show (d * c⁻¹) • (c • x₀) = d • x₀
  rw [mul_smul, inv_smul_smul]

end Class
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

section Topology

variable {F : Type*} [Field F] [TopologicalSpace F]

private theorem exists_compact_open_subgroup_conjAct
    (hKb : ∀ U ∈ nhds (1 : GL (Fin 3) F), ∃ K : Subgroup (GL (Fin 3) F),
      IsCompact (K : Set (GL (Fin 3) F)) ∧ IsOpen (K : Set (GL (Fin 3) F)) ∧ (K : Set (GL (Fin 3) F)) ⊆ U)
    (U : Set (ConjAct (GL (Fin 3) F))) (hU : U ∈ nhds (1 : ConjAct (GL (Fin 3) F))) :
    ∃ K : Subgroup (ConjAct (GL (Fin 3) F)), IsCompact (K : Set (ConjAct (GL (Fin 3) F))) ∧
      IsOpen (K : Set (ConjAct (GL (Fin 3) F))) ∧ (K : Set (ConjAct (GL (Fin 3) F))) ⊆ U := by
  obtain ⟨K, hKc, hKo, hKU⟩ := hKb U hU
  exact ⟨K.comap (ConjAct.ofConjAct : ConjAct (GL (Fin 3) F) ≃* GL (Fin 3) F).toMonoidHom, hKc, hKo, hKU⟩

variable [T2Space (GL (Fin 3) F)] [IsTopologicalGroup (GL (Fin 3) F)] [LocallyCompactSpace (GL (Fin 3) F)]
  [SigmaCompactSpace (GL (Fin 3) F)]

private theorem isOpenMap_smul_of_isLocallyClosed (S : SubMulAction (ConjAct (GL (Fin 3) F)) (GL (Fin 3) F))
    [IsPretransitive (ConjAct (GL (Fin 3) F)) ↥S] (hlc : IsLocallyClosed (S : Set (GL (Fin 3) F))) (y : ↥S) :
    IsOpenMap fun c : ConjAct (GL (Fin 3) F) => c • y := by
  haveI : LocallyCompactSpace ↥S := hlc.locallyCompactSpace
  rw [← OrbitHomeomorph.ofQuotientStabilizer_comp_mk (ConjAct (GL (Fin 3) F)) y]
  exact (OrbitHomeomorph.isOpenMap_ofQuotientStabilizer (ConjAct (GL (Fin 3) F)) y).comp
    QuotientGroup.isOpenMap_coe

private theorem comp_pullback_thetaS_eq_self_of_coe_eq_orbit
    (hKb : ∀ U ∈ nhds (1 : GL (Fin 3) F), ∃ K : Subgroup (GL (Fin 3) F),
      IsCompact (K : Set (GL (Fin 3) F)) ∧ IsOpen (K : Set (GL (Fin 3) F)) ∧ (K : Set (GL (Fin 3) F)) ⊆ U)
    (S : SubMulAction (ConjAct (GL (Fin 3) F)) (GL (Fin 3) F)) (hθS : ∀ y ∈ S, (transposeInv3 y)⁻¹ ∈ S)
    (hlc : IsLocallyClosed (S : Set (GL (Fin 3) F))) (x₀ : GL (Fin 3) F)
    (hS : (S : Set (GL (Fin 3) F)) = orbit (ConjAct (GL (Fin 3) F)) x₀) (μ : Module.Dual ℂ (testSubmodule ↥S ℂ))
    (hμ : ∀ c : ConjAct (GL (Fin 3) F), μ ∘ₗ translationAction (ConjAct (GL (Fin 3) F)) ↥S ℂ c = μ) :
    μ ∘ₗ pullback ℂ (thetaS S hθS) (continuous_thetaS S hθS) (thetaS_involutive S hθS) = μ := by
  haveI := isPretransitive_of_coe_eq_orbit S x₀ hS
  obtain ⟨K₀, hK₀c, hK₀o, -⟩ := exists_compact_open_subgroup_conjAct hKb Set.univ Filter.univ_mem
  refine comp_pullback_eq_self (fun U hU => ?_) (isOpenMap_smul_of_isLocallyClosed S hlc) K₀ hK₀c hK₀o
    ⟨x₀, mem_of_coe_eq_orbit S x₀ hS⟩ (thetaS S hθS) (continuous_thetaS S hθS) (thetaS_involutive S hθS) tauConj
    tauConj_inv tauConj_tauConj (thetaS_smul S hθS) μ hμ
  obtain ⟨K, -, hKo, hKU⟩ := exists_compact_open_subgroup_conjAct hKb U hU
  exact ⟨K, hKo, hKU⟩

end Topology
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

end LanglandsTunnell.CubicInduction.ClassInvariance
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist"

end ClassInvariance
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance"

section FibreInduction

open MulAction InvariantFunctional Topology
open LanglandsTunnell.CubicInduction.ClassInvariance

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.localMaximalCompact3 CubicInduction.mem_localMaximalCompact3_iff CubicInduction.transposeInv3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localMaximalCompact3 mem_localMaximalCompact3_iff transposeInv3 LocalGL3"
namespace Strata
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Basis

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]

private theorem exists_compact_open_nhds_of_subgroups
    (hKb : ∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ (K : Set G) ⊆ U)
    (x : G) (O : Set G) (hO : O ∈ 𝓝 x) : ∃ V : Set G, IsCompact V ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ O := by
  have h1 : (fun k => x * k) ⁻¹' O ∈ 𝓝 (1 : G) :=
    (continuous_const_mul x).continuousAt.preimage_mem_nhds (by simpa only [mul_one] using hO)
  obtain ⟨K, hKc, hKo, hKO⟩ := hKb _ h1
  refine ⟨(fun k => x * k) '' (K : Set G), hKc.image (continuous_const_mul x), isOpenMap_mul_left x _ hKo,
    ⟨1, K.one_mem, mul_one x⟩, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  exact hKO hk

end Basis
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance"

section Strata

variable {F : Type} [Field F]

private theorem stratumLE_zero (y : Fin 3 → F) : stratumLE y 0 = ∅ := by
  ext g
  rw [mem_stratumLE]
  constructor
  · rintro ⟨-, h⟩
    exact absurd (Nat.le_zero.mp h) (Matrix.Fin3Conj.minpoly_natDegree_pos (g : Matrix (Fin 3) (Fin 3) F)).ne'
  · intro h
    exact absurd h (Set.notMem_empty g)

private theorem stratumLE_mono (y : Fin 3 → F) (k : ℕ) : stratumLE y k ⊆ stratumLE y (k + 1) := fun _ hg =>
  mem_stratumLE.mpr ⟨(mem_stratumLE.mp hg).1, (mem_stratumLE.mp hg).2.trans (Nat.le_succ k)⟩

private theorem stratumLE_three_eq_preimage (y : Fin 3 → F) :
    stratumLE y 3 =
      (fun g : GL (Fin 3) F => Localisation.charpolyCoeffs (g : Matrix (Fin 3) (Fin 3) F)) ⁻¹' {y} := by
  rw [stratumLE_three]
  rfl

private def subMulAction_stratumLE (y : Fin 3 → F) (k : ℕ) : SubMulAction (ConjAct (GL (Fin 3) F)) (GL (Fin 3) F) where
  carrier := stratumLE y k
  smul_mem' c g hg := by
    obtain ⟨hy, hk⟩ := mem_stratumLE.mp hg
    rw [mem_stratumLE, ConjAct.smul_def, Units.val_mul, Units.val_mul, charpolyCoeffs_units_conj,
      minpoly_units_conj]
    exact ⟨hy, hk⟩

@[scoped simp]
private theorem coe_subMulAction_stratumLE (y : Fin 3 → F) (k : ℕ) :
    (subMulAction_stratumLE y k : Set (GL (Fin 3) F)) = stratumLE y k :=
  rfl

private def subMulAction_stratum (y : Fin 3 → F) (k : ℕ) : SubMulAction (ConjAct (GL (Fin 3) F)) (GL (Fin 3) F) where
  carrier := stratum y k
  smul_mem' c g hg := orbit_subset_stratum y k hg (mem_orbit g c)

@[scoped simp]
private theorem coe_subMulAction_stratum (y : Fin 3 → F) (k : ℕ) :
    (subMulAction_stratum y k : Set (GL (Fin 3) F)) = stratum y k :=
  rfl

private theorem transposeInv3_inv_mem_subMulAction_stratumLE (y : Fin 3 → F) (k : ℕ) :
    ∀ g ∈ subMulAction_stratumLE y k, (transposeInv3 g)⁻¹ ∈ subMulAction_stratumLE y k :=
  fun g hg => (transposeInv3_inv_mem_stratumLE_iff y k g).2 hg

private theorem transposeInv3_inv_mem_subMulAction_stratum (y : Fin 3 → F) (k : ℕ) :
    ∀ g ∈ subMulAction_stratum y k, (transposeInv3 g)⁻¹ ∈ subMulAction_stratum y k :=
  fun g hg => (transposeInv3_inv_mem_stratum_iff y k g).2 hg

end Strata
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance"

section Transpose

variable {F : Type} [Field F] [TopologicalSpace F] (y : Fin 3 → F)

private abbrev transposeLE (k : ℕ) : Module.End ℂ (testSubmodule ↥(subMulAction_stratumLE y k) ℂ) :=
  pullback ℂ (thetaS (subMulAction_stratumLE y k) (transposeInv3_inv_mem_subMulAction_stratumLE y k))
    (continuous_thetaS _ _) (thetaS_involutive _ _)

private abbrev transposeStratum (k : ℕ) : Module.End ℂ (testSubmodule ↥(subMulAction_stratum y k) ℂ) :=
  pullback ℂ (thetaS (subMulAction_stratum y k) (transposeInv3_inv_mem_subMulAction_stratum y k))
    (continuous_thetaS _ _) (thetaS_involutive _ _)

end Transpose
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance"

section Invariance

variable {F : Type} [Field F] [Infinite F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
  [T2Space (GL (Fin 3) F)] [IsTopologicalGroup (GL (Fin 3) F)] [LocallyCompactSpace (GL (Fin 3) F)]
  [SigmaCompactSpace (GL (Fin 3) F)]
  (hKb : ∀ U ∈ 𝓝 (1 : GL (Fin 3) F), ∃ K : Subgroup (GL (Fin 3) F),
    IsCompact (K : Set (GL (Fin 3) F)) ∧ IsOpen (K : Set (GL (Fin 3) F)) ∧ (K : Set (GL (Fin 3) F)) ⊆ U)
  (y : Fin 3 → F)

include hKb in

private theorem comp_pullback_eq_self_stratum (k : ℕ) (φ : Module.Dual ℂ (testSubmodule ↥(subMulAction_stratum y k) ℂ))
    (hφ : ∀ c : ConjAct (GL (Fin 3) F),
      φ ∘ₗ translationAction (ConjAct (GL (Fin 3) F)) ↥(subMulAction_stratum y k) ℂ c = φ) :
    φ ∘ₗ transposeStratum y k = φ := by
  by_cases hne : (stratum y k).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    exact comp_pullback_thetaS_eq_self_of_coe_eq_orbit hKb (subMulAction_stratum y k)
      (transposeInv3_inv_mem_subMulAction_stratum y k) (isLocallyClosed_stratum y k) x₀
      (stratum_eq_orbit y k hx₀) φ hφ
  · haveI : IsEmpty ↥(subMulAction_stratum y k) := ⟨fun u => hne ⟨u, u.2⟩⟩
    haveI : Subsingleton (testSubmodule ↥(subMulAction_stratum y k) ℂ) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact comp_eq_self_of_subsingleton _ φ

include hKb in

private theorem comp_pullback_eq_self_stratumLE (k : ℕ) :
    ∀ (μ : Module.Dual ℂ (testSubmodule ↥(subMulAction_stratumLE y k) ℂ)),
      (∀ c : ConjAct (GL (Fin 3) F),
        μ ∘ₗ translationAction (ConjAct (GL (Fin 3) F)) ↥(subMulAction_stratumLE y k) ℂ c = μ) →
      μ ∘ₗ transposeLE y k = μ := by
  induction k with
  | zero =>
    intro μ _
    haveI : IsEmpty ↥(subMulAction_stratumLE y 0) := ⟨fun u => by
      have h : (u : GL (Fin 3) F) ∈ stratumLE y 0 := u.2
      rw [stratumLE_zero] at h
      exact h⟩
    haveI : Subsingleton (testSubmodule ↥(subMulAction_stratumLE y 0) ℂ) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact comp_eq_self_of_subsingleton _ μ
  | succ k ih =>
    intro μ hμ

    have hZX : stratumLE y k ⊆ stratumLE y (k + 1) := stratumLE_mono y k
    have hZ : IsClosed (stratumLE y k) := isClosed_stratumLE y k
    have hU : stratum y (k + 1) = stratumLE y (k + 1) \ stratumLE y k := (stratumLE_diff_eq_stratum y k).symm
    have htr : HasCompactTraces (stratumLE y (k + 1)) (stratumLE y k) :=
      hasCompactTraces_of_basis hZX (isClosed_stratumLE y (k + 1)) (exists_compact_open_nhds_of_subgroups hKb)

    have hcX : ∀ c : ConjAct (GL (Fin 3) F),
        Set.MapsTo (fun g => c⁻¹ • g) (stratumLE y (k + 1)) (stratumLE y (k + 1)) :=
      fun c g hg => (subMulAction_stratumLE y (k + 1)).smul_mem c⁻¹ hg
    have hcU : ∀ c : ConjAct (GL (Fin 3) F), Set.MapsTo (fun g => c⁻¹ • g) (stratum y (k + 1)) (stratum y (k + 1)) :=
      fun c g hg => (subMulAction_stratum y (k + 1)).smul_mem c⁻¹ hg
    have hcZ : ∀ c : ConjAct (GL (Fin 3) F), Set.MapsTo (fun g => c⁻¹ • g) (stratumLE y k) (stratumLE y k) :=
      fun c g hg => (subMulAction_stratumLE y k).smul_mem c⁻¹ hg
    have htX : Set.MapsTo (fun g : GL (Fin 3) F => (transposeInv3 g)⁻¹) (stratumLE y (k + 1)) (stratumLE y (k + 1)) :=
      fun g hg => (transposeInv3_inv_mem_stratumLE_iff y (k + 1) g).2 hg
    have htU : Set.MapsTo (fun g : GL (Fin 3) F => (transposeInv3 g)⁻¹) (stratum y (k + 1)) (stratum y (k + 1)) :=
      fun g hg => (transposeInv3_inv_mem_stratum_iff y (k + 1) g).2 hg
    have htZ : Set.MapsTo (fun g : GL (Fin 3) F => (transposeInv3 g)⁻¹) (stratumLE y k) (stratumLE y k) :=
      fun g hg => (transposeInv3_inv_mem_stratumLE_iff y k g).2 hg
    exact comp_eq_self_of_step
      (translationAction (ConjAct (GL (Fin 3) F)) ↥(subMulAction_stratum y (k + 1)) ℂ)
      (translationAction (ConjAct (GL (Fin 3) F)) ↥(subMulAction_stratumLE y (k + 1)) ℂ)
      (translationAction (ConjAct (GL (Fin 3) F)) ↥(subMulAction_stratumLE y k) ℂ)
      (transposeStratum y (k + 1)) (transposeLE y (k + 1)) (transposeLE y k)
      (extendByZero (R := ℂ) hZ hU) (restrictTo (R := ℂ) hZX hZ) (restrictTo_surjective hZX hZ htr)
      (exact_extendByZero_restrictTo hZX hZ hU)
      (fun c => extendByZero_comp hZ hU (hcX c) (hcU c) (hcZ c)
        (translationAction (ConjAct (GL (Fin 3) F)) ↥(subMulAction_stratum y (k + 1)) ℂ c)
        (translationAction (ConjAct (GL (Fin 3) F)) ↥(subMulAction_stratumLE y (k + 1)) ℂ c)
        (fun _ _ => rfl) (fun _ _ => rfl))
      (fun c => restrictTo_comp hZX hZ (hcX c) (hcZ c)
        (translationAction (ConjAct (GL (Fin 3) F)) ↥(subMulAction_stratumLE y (k + 1)) ℂ c)
        (translationAction (ConjAct (GL (Fin 3) F)) ↥(subMulAction_stratumLE y k) ℂ c)
        (fun _ _ => rfl) (fun _ _ => rfl))
      (extendByZero_comp hZ hU htX htU htZ (transposeStratum y (k + 1)) (transposeLE y (k + 1))
        (fun _ _ => rfl) (fun _ _ => rfl))
      (restrictTo_comp hZX hZ htX htZ (transposeLE y (k + 1)) (transposeLE y k) (fun _ _ => rfl) (fun _ _ => rfl))
      (pullback_comp_pullback _ _ _)
      (fun c => ⟨tauConj c, pullback_comp_translationAction _ _ _ tauConj tauConj_inv tauConj_tauConj
        (thetaS_smul (subMulAction_stratumLE y (k + 1))
          (transposeInv3_inv_mem_subMulAction_stratumLE y (k + 1))) c⟩)
      (comp_pullback_eq_self_stratum hKb y (k + 1)) ih μ hμ

end Invariance
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance"

end LanglandsTunnell.CubicInduction.Strata
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance"

end FibreInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section TranspositionInvariance
open LanglandsTunnell.CubicInduction.TransposeTwist

open MulAction InvariantFunctional Topology
open LanglandsTunnell.CubicInduction.ClassInvariance LanglandsTunnell.CubicInduction.Strata

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.localMaximalCompact3 CubicInduction.mem_localMaximalCompact3_iff CubicInduction.transposeInv3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localMaximalCompact3 mem_localMaximalCompact3_iff transposeInv3 LocalGL3"
namespace Transposition
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction"

section Transpose

variable {F : Type} [Field F]

private def transposeGL3 (g : GL (Fin 3) F) : GL (Fin 3) F :=
  (transposeInv3 g)⁻¹

private theorem transposeGL3_apply (g : GL (Fin 3) F) : transposeGL3 g = (transposeInv3 g)⁻¹ :=
  rfl

private theorem transposeGL3_involutive : Function.Involutive (transposeGL3 (F := F)) :=
  transposeInv3_inv_transposeInv3_inv

private theorem charpolyCoeffs_smul (c : ConjAct (GL (Fin 3) F)) (g : GL (Fin 3) F) :
    Localisation.charpolyCoeffs ((c • g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Localisation.charpolyCoeffs (g : Matrix (Fin 3) (Fin 3) F) := by
  rw [ConjAct.smul_def, Units.val_mul, Units.val_mul, charpolyCoeffs_units_conj]

variable [TopologicalSpace F]

private theorem continuous_transposeGL3 : Continuous (transposeGL3 (F := F)) :=
  continuous_transposeInv3_inv

end Transpose
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section Fibre

variable {F : Type} [Field F] [Infinite F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
  [T2Space (GL (Fin 3) F)] [IsTopologicalGroup (GL (Fin 3) F)] [LocallyCompactSpace (GL (Fin 3) F)]
  [SigmaCompactSpace (GL (Fin 3) F)]
  (hKb : ∀ U ∈ 𝓝 (1 : GL (Fin 3) F), ∃ K : Subgroup (GL (Fin 3) F),
    IsCompact (K : Set (GL (Fin 3) F)) ∧ IsOpen (K : Set (GL (Fin 3) F)) ∧ (K : Set (GL (Fin 3) F)) ⊆ U)

include hKb in

private theorem exists_mem_coinvariants_forall_charpolyCoeffs_eq (f : GL (Fin 3) F → ℂ)
    (hf : f ∈ testSubmodule (GL (Fin 3) F) ℂ) (y : Fin 3 → F) :
    ∃ n ∈ Localisation.coinvariants
        (fun c : ConjAct (GL (Fin 3) F) => LinearMap.funLeft ℂ ℂ fun g : GL (Fin 3) F => c⁻¹ • g)
        (testSubmodule (GL (Fin 3) F) ℂ),
      ∀ x : GL (Fin 3) F, Localisation.charpolyCoeffs (x : Matrix (Fin 3) (Fin 3) F) = y →
        (f - LinearMap.funLeft ℂ ℂ transposeGL3 f) x = n x := by
  have hZ : IsClosed (stratumLE y 3) := isClosed_stratumLE y 3
  have hcZ : ∀ c : ConjAct (GL (Fin 3) F), Set.MapsTo (fun g => c⁻¹ • g) (stratumLE y 3) (stratumLE y 3) :=
    fun c g hg => (subMulAction_stratumLE y 3).smul_mem c⁻¹ hg
  have htZ : Set.MapsTo (transposeGL3 (F := F)) (stratumLE y 3) (stratumLE y 3) :=
    fun g hg => (transposeInv3_inv_mem_stratumLE_iff y 3 g).2 hg

  obtain ⟨n, hn, hrn⟩ := InvariantFunctional.exists_mem_coinvariants_map_eq
    (translationAction (ConjAct (GL (Fin 3) F)) (GL (Fin 3) F) ℂ)
    (translationAction (ConjAct (GL (Fin 3) F)) ↥(subMulAction_stratumLE y 3) ℂ)
    (pullback ℂ transposeGL3 continuous_transposeGL3 transposeGL3_involutive) (transposeLE y 3)
    (restrictUniv (R := ℂ) hZ) (restrictUniv_surjective hZ (exists_compact_open_nhds_of_subgroups hKb))
    (fun c => restrictUniv_comp hZ (hcZ c) (translationAction (ConjAct (GL (Fin 3) F)) (GL (Fin 3) F) ℂ c)
      (translationAction (ConjAct (GL (Fin 3) F)) ↥(subMulAction_stratumLE y 3) ℂ c) (fun _ _ => rfl)
      (fun _ _ => rfl))
    (restrictUniv_comp hZ htZ (pullback ℂ transposeGL3 continuous_transposeGL3 transposeGL3_involutive)
      (transposeLE y 3) (fun _ _ => rfl) (fun _ _ => rfl))
    (comp_pullback_eq_self_stratumLE hKb y 3) ⟨f, hf⟩

  refine Localisation.exists_mem_coinvariants_of_forall_eq
    (A := fun c : ConjAct (GL (Fin 3) F) => LinearMap.funLeft ℂ ℂ fun g : GL (Fin 3) F => c⁻¹ • g)
    (fun x : GL (Fin 3) F => Localisation.charpolyCoeffs (x : Matrix (Fin 3) (Fin 3) F))
    (translationAction (ConjAct (GL (Fin 3) F)) (GL (Fin 3) F) ℂ) (fun c s => coe_translationAction_eq_funLeft c s)
    (LinearMap.funLeft ℂ ℂ transposeGL3) f y hn fun x hx => ?_
  have hxZ : x ∈ stratumLE y 3 := by
    rw [stratumLE_three_eq_preimage]
    exact hx

  have h1 := congrArg (fun h : testSubmodule ↥(stratumLE y 3) ℂ => (h : ↥(stratumLE y 3) → ℂ) ⟨x, hxZ⟩) hrn
  exact h1

end Fibre
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section Main

variable {F : Type} [Field F] [Infinite F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
  [T2Space (GL (Fin 3) F)] [IsTopologicalGroup (GL (Fin 3) F)] [LocallyCompactSpace (GL (Fin 3) F)]
  [SigmaCompactSpace (GL (Fin 3) F)]

private theorem comp_transpose_eq_of_forall_comp_conj_eq
    (hKb : ∀ U ∈ 𝓝 (1 : GL (Fin 3) F), ∃ K : Subgroup (GL (Fin 3) F),
      IsCompact (K : Set (GL (Fin 3) F)) ∧ IsOpen (K : Set (GL (Fin 3) F)) ∧ (K : Set (GL (Fin 3) F)) ⊆ U)
    (hY : ∀ (y : Fin 3 → F) (U : Set (Fin 3 → F)), IsOpen U → y ∈ U →
      ∃ V : Set (Fin 3 → F), IsClopen V ∧ y ∈ V ∧ V ⊆ U)
    (μ : Module.Dual ℂ (testSubmodule (GL (Fin 3) F) ℂ))
    (hμ : ∀ c : ConjAct (GL (Fin 3) F),
      μ ∘ₗ translationAction (ConjAct (GL (Fin 3) F)) (GL (Fin 3) F) ℂ c = μ) :
    μ ∘ₗ pullback ℂ transposeGL3 continuous_transposeGL3 transposeGL3_involutive = μ := by
  obtain ⟨T, hT⟩ := exists_dual_extension (testSubmodule (GL (Fin 3) F) ℂ) μ
  refine (comp_pullback_eq_iff transposeGL3 continuous_transposeGL3 transposeGL3_involutive T μ hT).2
    fun f hf => ?_
  have hφ : Continuous fun g : GL (Fin 3) F => Localisation.charpolyCoeffs (g : Matrix (Fin 3) (Fin 3) F) :=
    Localisation.continuous_charpolyCoeffs_units
  exact Localisation.apply_eq_of_forall_fibre
    (fun g : GL (Fin 3) F => Localisation.charpolyCoeffs (g : Matrix (Fin 3) (Fin 3) F))
    (fun c : ConjAct (GL (Fin 3) F) => LinearMap.funLeft ℂ ℂ fun g : GL (Fin 3) F => c⁻¹ • g)
    (testSubmodule (GL (Fin 3) F) ℂ) hφ hY (fun _ hf => hf.1) (fun _ hf => hf.2)
    (fun _ hf V hV => indicator_preimage_mem_testSubmodule hφ hV hf)
    (fun c _ hf => funLeft_inv_smul_mem_testSubmodule c hf)
    (fun c V _ f _ => funLeft_indicator_preimage ℂ (fun g : GL (Fin 3) F => c⁻¹ • g)
      (fun g : GL (Fin 3) F => Localisation.charpolyCoeffs (g : Matrix (Fin 3) (Fin 3) F))
      (charpolyCoeffs_smul c⁻¹) V f)
    (LinearMap.funLeft ℂ ℂ transposeGL3)
    (fun _ hf => funLeft_mem_testSubmodule transposeGL3 continuous_transposeGL3 transposeGL3_involutive hf)
    (fun f hf y _ => exists_mem_coinvariants_forall_charpolyCoeffs_eq hKb f hf y) T
    (fun c _ hf => apply_funLeft_inv_smul_eq T μ hT c (hμ c) hf) hf

end Main
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end LanglandsTunnell.CubicInduction.Transposition
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end TranspositionInvariance
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section AdicCompletionSigmaCompact

open IsDedekindDomain NumberField

namespace SigmaCompactUnits

private scoped instance instSigmaCompactSpaceAdicCompletion (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : SigmaCompactSpace (v.adicCompletion K) :=
  inferInstance

end SigmaCompactUnits
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end AdicCompletionSigmaCompact
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section ConvolutionLaw

universe u v

namespace Character

private def IsConvolutionHom {S : Type u} {M : Type v} [Mul M] (conv : S → S → S) (H : S → M) : Prop :=
  ∀ φ ψ, H (conv φ ψ) = H φ * H ψ

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end ConvolutionLaw
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section MulConvolution

namespace MulConvolution

open MeasureTheory Set Filter Topology

variable {G : Type*} [Group G] [MeasurableSpace G]

private def mulConv (μ : Measure G) (f g : G → ℂ) : G → ℂ := fun x => ∫ y, f y * g (y⁻¹ * x) ∂μ

private theorem mulConv_apply (μ : Measure G) (f g : G → ℂ) (x : G) :
    mulConv μ f g x = ∫ y, f y * g (y⁻¹ * x) ∂μ := rfl

section Integrable

variable [TopologicalSpace G] [IsTopologicalGroup G] [OpensMeasurableSpace G] {μ : Measure G}
  [IsFiniteMeasureOnCompacts μ]

private theorem integrable_mul_comp {f g : G → ℂ} (hf : IsLocallyConstant f) (hfc : HasCompactSupport f)
    (hg : IsLocallyConstant g) (x : G) : Integrable (fun y => f y * g (y⁻¹ * x)) μ := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact hf.continuous.mul (hg.continuous.comp (continuous_inv.mul continuous_const))
  · exact hfc.mul_right

private theorem mulConv_add_left {f₁ f₂ g : G → ℂ} (hf₁ : IsLocallyConstant f₁) (hf₁c : HasCompactSupport f₁)
    (hf₂ : IsLocallyConstant f₂) (hf₂c : HasCompactSupport f₂) (hg : IsLocallyConstant g) :
    mulConv μ (f₁ + f₂) g = mulConv μ f₁ g + mulConv μ f₂ g := by
  funext x
  simp only [mulConv, Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_comp hf₁ hf₁c hg x) (integrable_mul_comp hf₂ hf₂c hg x)

private theorem mulConv_add_right {f g₁ g₂ : G → ℂ} (hf : IsLocallyConstant f) (hfc : HasCompactSupport f)
    (hg₁ : IsLocallyConstant g₁) (hg₂ : IsLocallyConstant g₂) :
    mulConv μ f (g₁ + g₂) = mulConv μ f g₁ + mulConv μ f g₂ := by
  funext x
  simp only [mulConv, Pi.add_apply, mul_add]
  exact integral_add (integrable_mul_comp hf hfc hg₁ x) (integrable_mul_comp hf hfc hg₂ x)

end Integrable
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

private theorem mulConv_smul_left (μ : Measure G) (c : ℂ) (f g : G → ℂ) : mulConv μ (c • f) g = c • mulConv μ f g := by
  funext x
  simp only [mulConv, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

private theorem mulConv_smul_right (μ : Measure G) (c : ℂ) (f g : G → ℂ) :
    mulConv μ f (c • g) = c • mulConv μ f g := by
  funext x
  simp only [mulConv, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul c _

section Support

variable [TopologicalSpace G]

private theorem hasCompactSupport_mulConv [IsTopologicalGroup G] [T2Space G] (μ : Measure G) {f g : G → ℂ}
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) : HasCompactSupport (mulConv μ f g) := by
  refine HasCompactSupport.intro (hfc.mul hgc) fun x hx => ?_
  have h0 : (fun y => f y * g (y⁻¹ * x)) = fun _ => 0 := by
    funext y
    by_cases hfy : f y = 0
    · rw [hfy, zero_mul]
    · have hgy : g (y⁻¹ * x) = 0 := by
        by_contra hgy
        exact hx (Set.mem_mul.mpr ⟨y, subset_tsupport _ (Function.mem_support.mpr hfy), y⁻¹ * x,
          subset_tsupport _ (Function.mem_support.mpr hgy), mul_inv_cancel_left y x⟩)
      rw [hgy, mul_zero]
  rw [mulConv_apply, h0, integral_zero]

private theorem isLocallyConstant_mulConv [ContinuousMul G] (μ : Measure G) (f g : G → ℂ)
    (hg : ∃ U ∈ 𝓝 (1 : G), ∀ u ∈ U, ∀ x, g (x * u) = g x) : IsLocallyConstant (mulConv μ f g) := by
  obtain ⟨U, hU, hgU⟩ := hg
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hN : (fun y => x⁻¹ * y) ⁻¹' U ∈ 𝓝 x := by
    refine (continuous_const_mul x⁻¹).continuousAt.preimage_mem_nhds ?_
    show U ∈ 𝓝 (x⁻¹ * x)
    rwa [inv_mul_cancel]
  filter_upwards [hN] with y hy
  rw [← mul_inv_cancel_left x y, mulConv_apply, mulConv_apply]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show f z * g (z⁻¹ * (x * (x⁻¹ * y))) = f z * g (z⁻¹ * x)
  rw [← mul_assoc z⁻¹ x, hgU (x⁻¹ * y) hy]

end Support
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end MulConvolution
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end MulConvolution
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section CosetIdentities

namespace MulConvolution

open MeasureTheory Set Filter Topology

variable {G : Type*} [Group G] [MeasurableSpace G]

section Apply

variable (μ : Measure G)

private theorem mulConv_indicator_apply (f : G → ℂ) {B : Set G} (x : G) (hB : MeasurableSet {y | y⁻¹ * x ∈ B}) :
    mulConv μ f (B.indicator 1) x = ∫ y in {y | y⁻¹ * x ∈ B}, f y ∂μ := by
  rw [mulConv_apply]
  have h : (fun y => f y * B.indicator (1 : G → ℂ) (y⁻¹ * x)) = {y | y⁻¹ * x ∈ B}.indicator f := by
    funext y
    by_cases hy : y⁻¹ * x ∈ B
    · rw [indicator_of_mem hy, Pi.one_apply, mul_one, indicator_of_mem (show y ∈ {y | y⁻¹ * x ∈ B} from hy)]
    · rw [indicator_of_notMem hy, mul_zero, indicator_of_notMem (show y ∉ {y | y⁻¹ * x ∈ B} from hy)]
  rw [h, integral_indicator hB]

private theorem indicator_mulConv_apply {A : Set G} (hA : MeasurableSet A) (h : G → ℂ) (x : G) :
    mulConv μ (A.indicator 1) h x = ∫ y in A, h (y⁻¹ * x) ∂μ := by
  rw [mulConv_apply]
  have h' : (fun y => A.indicator (1 : G → ℂ) y * h (y⁻¹ * x)) = A.indicator fun y => h (y⁻¹ * x) := by
    funext y
    by_cases hy : y ∈ A
    · rw [indicator_of_mem hy, indicator_of_mem hy, Pi.one_apply, one_mul]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_mul]
  rw [h', integral_indicator hA]

end Apply
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section Cosets

variable [TopologicalSpace G] [BorelSpace G] (μ : Measure G) (K : Subgroup G) (hK : IsOpen (K : Set G))

include hK

private theorem measurableSet_preimage {φ : G → G} (hφ : Continuous φ) : MeasurableSet (φ ⁻¹' (K : Set G)) :=
  (hK.preimage hφ).measurableSet

variable [IsTopologicalGroup G] [μ.IsMulLeftInvariant] (g : G)

omit hK in
private theorem measureReal_preimage_mul (x : G) (A : Set G) : μ.real ((fun y => x * y) ⁻¹' A) = μ.real A :=
  congrArg ENNReal.toReal (measure_preimage_mul μ x A)

private theorem mulConv_indicator_leftCoset (f : G → ℂ) (hr : ∀ k ∈ K, ∀ x, f (x * (g⁻¹ * k * g)) = f x) :
    mulConv μ f ({y | g * y ∈ K}.indicator 1) =
      fun x => (μ.real {y : G | y * g⁻¹ ∈ K} : ℂ) * f (x * g) := by
  funext x
  have hmeas : MeasurableSet {y : G | y⁻¹ * x ∈ {y : G | g * y ∈ K}} :=
    measurableSet_preimage K hK (φ := fun y => g * (y⁻¹ * x)) (by fun_prop)
  rw [mulConv_indicator_apply μ f x hmeas]
  have hEq : EqOn f (fun _ => f (x * g)) {y : G | y⁻¹ * x ∈ {y : G | g * y ∈ K}} := by
    intro y hy
    have hy' : g * (y⁻¹ * x) ∈ K := hy
    have h := hr _ (K.inv_mem hy') (x * g)
    rw [← h]
    congr 1
    group
  have hset : {y : G | y⁻¹ * x ∈ {y : G | g * y ∈ K}} = (fun y => x⁻¹ * y) ⁻¹' {y : G | y * g⁻¹ ∈ K} := by
    ext y
    show g * (y⁻¹ * x) ∈ K ↔ x⁻¹ * y * g⁻¹ ∈ K
    rw [← K.inv_mem_iff (x := x⁻¹ * y * g⁻¹)]
    exact Iff.of_eq (congrArg (· ∈ K) (by group))
  rw [setIntegral_congr_fun hmeas hEq, setIntegral_const, Complex.real_smul, hset, measureReal_preimage_mul]

private theorem indicator_mulConv_mulConv_indicator (f : G → ℂ) (hl : ∀ k ∈ K, ∀ x, f (g⁻¹ * k * g * x) = f x)
    (hr : ∀ k ∈ K, ∀ x, f (x * (g⁻¹ * k * g)) = f x) :
    mulConv μ ({y | y * g⁻¹ ∈ K}.indicator 1) (mulConv μ f ({y | g * y ∈ K}.indicator 1)) =
      ((μ.real {y : G | y * g⁻¹ ∈ K} : ℂ) ^ 2) • fun x => f (g⁻¹ * x * g) := by
  rw [mulConv_indicator_leftCoset μ K hK g f hr]
  funext x
  have hA : MeasurableSet {y : G | y * g⁻¹ ∈ K} := measurableSet_preimage K hK (φ := fun y => y * g⁻¹) (by fun_prop)
  rw [indicator_mulConv_apply μ hA, Pi.smul_apply, smul_eq_mul]
  have hEq : EqOn (fun y => (μ.real {y : G | y * g⁻¹ ∈ K} : ℂ) * f (y⁻¹ * x * g))
      (fun _ => (μ.real {y : G | y * g⁻¹ ∈ K} : ℂ) * f (g⁻¹ * x * g)) {y : G | y * g⁻¹ ∈ K} := by
    intro y hy
    have hy' : y * g⁻¹ ∈ K := hy
    have h := hl _ hy' (y⁻¹ * x * g)
    show (μ.real {y : G | y * g⁻¹ ∈ K} : ℂ) * f (y⁻¹ * x * g) = (μ.real {y : G | y * g⁻¹ ∈ K} : ℂ) * f (g⁻¹ * x * g)
    rw [← h]
    congr 2
    group
  rw [setIntegral_congr_fun hA hEq, setIntegral_const, Complex.real_smul]
  ring

private theorem indicator_mulConv_indicator :
    mulConv μ ({y | g * y ∈ K}.indicator 1) ({y | y * g⁻¹ ∈ K}.indicator 1) =
      (μ.real (K : Set G) : ℂ) • ({x | g * x * g⁻¹ ∈ K}.indicator (1 : G → ℂ)) := by
  funext x
  have hB : MeasurableSet {y : G | g * y ∈ K} := measurableSet_preimage K hK (φ := fun y => g * y) (by fun_prop)
  rw [indicator_mulConv_apply μ hB, Pi.smul_apply, smul_eq_mul]
  have hμB : μ.real {y : G | g * y ∈ K} = μ.real (K : Set G) := measureReal_preimage_mul μ g K
  by_cases hx : g * x * g⁻¹ ∈ K
  · have hEq : EqOn (fun y => {y : G | y * g⁻¹ ∈ K}.indicator (1 : G → ℂ) (y⁻¹ * x)) (fun _ => 1)
        {y : G | g * y ∈ K} := by
      intro y hy
      have hy' : g * y ∈ K := hy
      have hm : y⁻¹ * x * g⁻¹ ∈ K := by
        have h := K.mul_mem (K.inv_mem hy') hx
        rw [show (g * y)⁻¹ * (g * x * g⁻¹) = y⁻¹ * x * g⁻¹ by group] at h
        exact h
      exact indicator_of_mem (show y⁻¹ * x ∈ {y : G | y * g⁻¹ ∈ K} from hm) _
    rw [setIntegral_congr_fun hB hEq, setIntegral_const, Complex.real_smul, mul_one, hμB,
      indicator_of_mem (show x ∈ {x : G | g * x * g⁻¹ ∈ K} from hx), Pi.one_apply, mul_one]
  · have hEq : EqOn (fun y => {y : G | y * g⁻¹ ∈ K}.indicator (1 : G → ℂ) (y⁻¹ * x)) (fun _ => 0)
        {y : G | g * y ∈ K} := by
      intro y hy
      have hy' : g * y ∈ K := hy
      have hm : y⁻¹ * x * g⁻¹ ∉ K := by
        intro hm
        apply hx
        have h := K.mul_mem hy' hm
        rw [show g * y * (y⁻¹ * x * g⁻¹) = g * x * g⁻¹ by group] at h
        exact h
      exact indicator_of_notMem (show y⁻¹ * x ∉ {y : G | y * g⁻¹ ∈ K} from hm) _
    rw [setIntegral_congr_fun hB hEq, setIntegral_const, smul_zero,
      indicator_of_notMem (show x ∉ {x : G | g * x * g⁻¹ ∈ K} from hx), mul_zero]

private theorem mulConv_mulConv_indicator (f : G → ℂ) (hr : ∀ k ∈ K, ∀ x, f (x * (g⁻¹ * k * g)) = f x) :
    mulConv μ f (mulConv μ ({y | g * y ∈ K}.indicator 1) ({y | y * g⁻¹ ∈ K}.indicator 1)) =
      ((μ.real (K : Set G) : ℂ) * (μ.real {y : G | y * g⁻¹ ∈ K} : ℂ)) • f := by
  rw [indicator_mulConv_indicator μ K hK g, mulConv_smul_right]
  funext x
  have hmeas : MeasurableSet {y : G | y⁻¹ * x ∈ {x : G | g * x * g⁻¹ ∈ K}} :=
    measurableSet_preimage K hK (φ := fun y => g * (y⁻¹ * x) * g⁻¹) (by fun_prop)
  rw [Pi.smul_apply, smul_eq_mul, mulConv_indicator_apply μ f x hmeas, Pi.smul_apply, smul_eq_mul]
  have hEq : EqOn f (fun _ => f x) {y : G | y⁻¹ * x ∈ {x : G | g * x * g⁻¹ ∈ K}} := by
    intro y hy
    have hy' : g * (y⁻¹ * x) * g⁻¹ ∈ K := hy
    have h := hr _ (K.inv_mem hy') x
    rw [← h]
    congr 1
    group
  have hset : {y : G | y⁻¹ * x ∈ {x : G | g * x * g⁻¹ ∈ K}} =
      (fun y => x⁻¹ * y) ⁻¹' ((fun y => g * y) ⁻¹' {y : G | y * g⁻¹ ∈ K}) := by
    ext y
    show g * (y⁻¹ * x) * g⁻¹ ∈ K ↔ g * (x⁻¹ * y) * g⁻¹ ∈ K
    rw [← K.inv_mem_iff (x := g * (x⁻¹ * y) * g⁻¹)]
    exact Iff.of_eq (congrArg (· ∈ K) (by group))
  rw [setIntegral_congr_fun hmeas hEq, setIntegral_const, Complex.real_smul, hset, measureReal_preimage_mul,
    measureReal_preimage_mul]
  ring

end Cosets
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end MulConvolution
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end CosetIdentities
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section AbsorptionUnits

namespace MulConvolution

open MeasureTheory Set

variable {G : Type*} [Group G]

section Invariance

variable (c : ℂ) (K : Subgroup G)

private theorem smul_indicator_left_invariant : ∀ k ∈ K, ∀ x : G,
    (c • (K : Set G).indicator (1 : G → ℂ)) (k * x) = (c • (K : Set G).indicator (1 : G → ℂ)) x := by
  intro k hk x
  by_cases hx : x ∈ K
  · simp only [Pi.smul_apply, indicator_of_mem ((K.mul_mem_cancel_left hk).mpr hx), indicator_of_mem hx,
      Pi.one_apply]
  · simp only [Pi.smul_apply, indicator_of_notMem (fun h => hx ((K.mul_mem_cancel_left hk).mp h)),
      indicator_of_notMem hx]

private theorem smul_indicator_right_invariant : ∀ k ∈ K, ∀ x : G,
    (c • (K : Set G).indicator (1 : G → ℂ)) (x * k) = (c • (K : Set G).indicator (1 : G → ℂ)) x := by
  intro k hk x
  by_cases hx : x ∈ K
  · simp only [Pi.smul_apply, indicator_of_mem ((K.mul_mem_cancel_right hk).mpr hx), indicator_of_mem hx,
      Pi.one_apply]
  · simp only [Pi.smul_apply, indicator_of_notMem (fun h => hx ((K.mul_mem_cancel_right hk).mp h)),
      indicator_of_notMem hx]

end Invariance
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section Absorption

variable [MeasurableSpace G] [TopologicalSpace G] [BorelSpace G] [IsTopologicalGroup G] (μ : Measure G)
  [μ.IsMulLeftInvariant] {K : Subgroup G} (hK : IsOpen (K : Set G)) {c : ℂ}
  (hc : c * (μ.real (K : Set G) : ℂ) = 1) (φ : G → ℂ)

include hK hc

omit [IsTopologicalGroup G] [μ.IsMulLeftInvariant] in

private theorem smul_indicator_mulConv_of_left_invariant (hl : ∀ k ∈ K, ∀ x : G, φ (k * x) = φ x) :
    mulConv μ (c • (K : Set G).indicator 1) φ = φ := by
  rw [mulConv_smul_left]
  funext x
  rw [Pi.smul_apply, indicator_mulConv_apply μ hK.measurableSet φ x, smul_eq_mul]
  have hEq : EqOn (fun y : G => φ (y⁻¹ * x)) (fun _ => φ x) (K : Set G) := fun y hy => hl y⁻¹ (K.inv_mem hy) x
  rw [show (∫ y in (K : Set G), φ (y⁻¹ * x) ∂μ) = ∫ _ in (K : Set G), φ x ∂μ from
      setIntegral_congr_fun hK.measurableSet hEq,
    setIntegral_const, Complex.real_smul, ← mul_assoc, hc, one_mul]

private theorem mulConv_smul_indicator_of_right_invariant (hr : ∀ k ∈ K, ∀ x : G, φ (x * k) = φ x) :
    mulConv μ φ (c • (K : Set G).indicator 1) = φ := by
  rw [mulConv_smul_right]
  funext x
  have hset : {y : G | y⁻¹ * x ∈ (K : Set G)} = (fun y : G => x⁻¹ * y) ⁻¹' (K : Set G) := by
    ext y
    simp only [mem_setOf_eq, mem_preimage, SetLike.mem_coe]
    constructor
    · intro h
      simpa using K.inv_mem h
    · intro h
      simpa using K.inv_mem h
  have hmeas : MeasurableSet {y : G | y⁻¹ * x ∈ (K : Set G)} := by
    rw [hset]
    exact (hK.preimage (by fun_prop : Continuous fun y : G => x⁻¹ * y)).measurableSet
  rw [Pi.smul_apply, mulConv_indicator_apply μ φ x hmeas, smul_eq_mul]
  have hEq : EqOn φ (fun _ => φ x) {y : G | y⁻¹ * x ∈ (K : Set G)} := by
    intro y hy
    have hk : x⁻¹ * y ∈ K := by simpa using K.inv_mem hy
    have h : φ (x * (x⁻¹ * y)) = φ x := hr _ hk x
    simpa using h
  have hμ : μ.real ((fun y : G => x⁻¹ * y) ⁻¹' (K : Set G)) = μ.real (K : Set G) :=
    congrArg ENNReal.toReal (measure_preimage_mul μ x⁻¹ (K : Set G))
  rw [show (∫ y in {y : G | y⁻¹ * x ∈ (K : Set G)}, φ y ∂μ) = ∫ _ in {y : G | y⁻¹ * x ∈ (K : Set G)}, φ x ∂μ from
      setIntegral_congr_fun hmeas hEq,
    setIntegral_const, Complex.real_smul, hset, hμ, ← mul_assoc, hc, one_mul]

end Absorption
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section Normalised

variable [MeasurableSpace G] [TopologicalSpace G] [BorelSpace G] [IsTopologicalGroup G] (μ : Measure G)
  [μ.IsMulLeftInvariant] {K : Subgroup G} (hK : IsOpen (K : Set G)) (h0 : μ.real (K : Set G) ≠ 0) (φ : G → ℂ)

include hK h0

omit [IsTopologicalGroup G] [μ.IsMulLeftInvariant] in

private theorem inv_measureReal_smul_indicator_mulConv_of_left_invariant (hl : ∀ k ∈ K, ∀ x : G, φ (k * x) = φ x) :
    mulConv μ (((μ.real (K : Set G) : ℂ)⁻¹) • (K : Set G).indicator 1) φ = φ :=
  smul_indicator_mulConv_of_left_invariant μ hK (inv_mul_cancel₀ (by exact_mod_cast h0)) φ hl

private theorem mulConv_inv_measureReal_smul_indicator_of_right_invariant (hr : ∀ k ∈ K, ∀ x : G, φ (x * k) = φ x) :
    mulConv μ φ (((μ.real (K : Set G) : ℂ)⁻¹) • (K : Set G).indicator 1) = φ :=
  mulConv_smul_indicator_of_right_invariant μ hK (inv_mul_cancel₀ (by exact_mod_cast h0)) φ hr

end Normalised
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end MulConvolution
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end AbsorptionUnits
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section ConvInvolutions

namespace MulConvolution

open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G)

private theorem mulConv_fun_inv [MeasurableMul G] [μ.IsMulLeftInvariant] (f g : G → ℂ) :
    mulConv μ (fun y => g y⁻¹) (fun y => f y⁻¹) = fun x => mulConv μ f g x⁻¹ := by
  funext x
  rw [mulConv_apply, mulConv_apply]
  calc (∫ y, g y⁻¹ * f (y⁻¹ * x)⁻¹ ∂μ)
      = ∫ y, g (x * y)⁻¹ * f ((x * y)⁻¹ * x)⁻¹ ∂μ :=
        (integral_mul_left_eq_self (fun y => g y⁻¹ * f (y⁻¹ * x)⁻¹) x).symm
    _ = ∫ y, f y * g (y⁻¹ * x⁻¹) ∂μ := by
        congr 1
        funext y
        simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right, inv_mul_cancel_left]
        exact mul_comm _ _

variable [TopologicalSpace G] [BorelSpace G]

private theorem mulConv_comp_of_map_eq (θ : G →* G) (hθc : Continuous θ) (hθθ : Function.Involutive θ)
    (hμ : Measure.map θ μ = μ) (f g : G → ℂ) :
    mulConv μ (fun y => f (θ y)) (fun y => g (θ y)) = fun x => mulConv μ f g (θ x) := by
  funext x
  let e : G ≃ᵐ G := Homeomorph.toMeasurableEquiv
    { toFun := θ, invFun := θ, left_inv := hθθ, right_inv := hθθ, continuous_toFun := hθc,
      continuous_invFun := hθc }
  have hμe : Measure.map (e : G → G) μ = μ := hμ
  have h := integral_map_equiv (μ := μ) e fun z => f z * g (z⁻¹ * θ x)
  rw [hμe] at h
  rw [mulConv_apply, mulConv_apply]
  calc (∫ y, f (θ y) * g (θ (y⁻¹ * x)) ∂μ)
      = ∫ y, f (e y) * g ((e y)⁻¹ * θ x) ∂μ := by
        congr 1
        funext y
        show f (θ y) * g (θ (y⁻¹ * x)) = f (θ y) * g ((θ y)⁻¹ * θ x)
        rw [map_mul, map_inv]
    _ = ∫ y, f y * g (y⁻¹ * θ x) ∂μ := h.symm

end MulConvolution
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end ConvInvolutions
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section Gl3HomTrivial

p2m_open "Matrix P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Matrix"

namespace GL3Hom

section Generic

variable {G : Type*} [Group G] {M : Type*} [CommMonoid M] (Δ : G →* M)

private theorem map_mul_map_inv (a : G) : Δ a * Δ a⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

private theorem map_conj_eq (a b : G) : Δ (a * b * a⁻¹) = Δ b := by
  rw [map_mul, map_mul, mul_right_comm, map_mul_map_inv, one_mul]

private theorem map_commutator_eq_one (a b : G) : Δ (a * b * a⁻¹ * b⁻¹) = 1 := by
  rw [map_mul, map_conj_eq, map_mul_map_inv]

end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

private theorem eq_one_of_pow_three_eq_one {x : NNReal} (h : x ^ 3 = 1) : x = 1 :=
  (pow_eq_one_iff_of_nonneg (zero_le : (0 : NNReal) ≤ x) (by norm_num)).1 h

section GL3

variable {F : Type*} [Field F]

private def diagonalUnit (d : Fin 3 → Fˣ) : GL (Fin 3) F :=
  GeneralLinearGroup.mkOfDetNeZero (diagonal fun k => (d k : F)) (by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun k _ => (d k).ne_zero)

private theorem diagonalUnit_val (d : Fin 3 → Fˣ) :
    (diagonalUnit d : Matrix (Fin 3) (Fin 3) F) = diagonal fun k => (d k : F) :=
  rfl

private theorem diagonalUnit_inv (d : Fin 3 → Fˣ) : (diagonalUnit d)⁻¹ = diagonalUnit fun k => (d k)⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul, diagonalUnit_val, diagonalUnit_val, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
  congr 1
  funext k
  exact Units.mul_inv (d k)

private theorem diagonalUnit_const_mul_comm (c : Fˣ) (x : GL (Fin 3) F) :
    diagonalUnit (fun _ => c) * x = x * diagonalUnit fun _ => c := by
  apply GeneralLinearGroup.ext
  intro i j
  rw [Units.val_mul, Units.val_mul, diagonalUnit_val, diagonal_mul, mul_diagonal, mul_comm]

private def coordinateUnit (k : Fin 3) (x : Fˣ) : GL (Fin 3) F :=
  diagonalUnit (Function.update (fun _ => (1 : Fˣ)) k x)

private theorem diagonalUnit_eq_prod (d : Fin 3 → Fˣ) :
    diagonalUnit d = coordinateUnit 0 (d 0) * coordinateUnit 1 (d 1) * coordinateUnit 2 (d 2) := by
  apply GeneralLinearGroup.ext
  intro i j
  simp only [coordinateUnit, Units.val_mul, diagonalUnit_val, diagonal_mul_diagonal, diagonal_apply]
  split_ifs with hij
  · fin_cases i <;> simp
  · rfl

private def swapMatrix₀₁ : Matrix (Fin 3) (Fin 3) F :=
  of ![![0, 1, 0], ![1, 0, 0], ![0, 0, 1]]

private def swapMatrix₀₂ : Matrix (Fin 3) (Fin 3) F :=
  of ![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]]

private theorem det_swapMatrix₀₁_ne_zero : (swapMatrix₀₁ : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
  rw [det_fin_three]
  simp [swapMatrix₀₁]

private theorem det_swapMatrix₀₂_ne_zero : (swapMatrix₀₂ : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
  rw [det_fin_three]
  simp [swapMatrix₀₂]

private def swapUnit₀₁ : GL (Fin 3) F := GeneralLinearGroup.mkOfDetNeZero swapMatrix₀₁ det_swapMatrix₀₁_ne_zero

private def swapUnit₀₂ : GL (Fin 3) F := GeneralLinearGroup.mkOfDetNeZero swapMatrix₀₂ det_swapMatrix₀₂_ne_zero

private theorem swapUnit₀₁_val : ((swapUnit₀₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = swapMatrix₀₁ := rfl

private theorem swapUnit₀₂_val : ((swapUnit₀₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = swapMatrix₀₂ := rfl

private theorem swapUnit₀₁_inv : (swapUnit₀₁ : GL (Fin 3) F)⁻¹ = swapUnit₀₁ := by
  apply inv_eq_of_mul_eq_one_right
  apply GeneralLinearGroup.ext
  intro i j
  rw [Units.val_mul, swapUnit₀₁_val, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp [swapMatrix₀₁, Matrix.mul_apply, Fin.sum_univ_three]

private theorem swapUnit₀₂_inv : (swapUnit₀₂ : GL (Fin 3) F)⁻¹ = swapUnit₀₂ := by
  apply inv_eq_of_mul_eq_one_right
  apply GeneralLinearGroup.ext
  intro i j
  rw [Units.val_mul, swapUnit₀₂_val, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp [swapMatrix₀₂, Matrix.mul_apply, Fin.sum_univ_three]

private theorem swapUnit₀₁_mul_coordinateUnit_mul_inv (x : Fˣ) :
    swapUnit₀₁ * coordinateUnit 0 x * swapUnit₀₁⁻¹ = coordinateUnit 1 x := by
  rw [swapUnit₀₁_inv]
  apply GeneralLinearGroup.ext
  intro i j
  rw [Units.val_mul, Units.val_mul, swapUnit₀₁_val, coordinateUnit, coordinateUnit, diagonalUnit_val,
    diagonalUnit_val]
  fin_cases i <;> fin_cases j <;>
    simp [swapMatrix₀₁, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul_diagonal, Function.update_apply]

private theorem swapUnit₀₂_mul_coordinateUnit_mul_inv (x : Fˣ) :
    swapUnit₀₂ * coordinateUnit 0 x * swapUnit₀₂⁻¹ = coordinateUnit 2 x := by
  rw [swapUnit₀₂_inv]
  apply GeneralLinearGroup.ext
  intro i j
  rw [Units.val_mul, Units.val_mul, swapUnit₀₂_val, coordinateUnit, coordinateUnit, diagonalUnit_val,
    diagonalUnit_val]
  fin_cases i <;> fin_cases j <;>
    simp [swapMatrix₀₂, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul_diagonal, Function.update_apply]

variable {N : Type*} [CommMonoid N]

private theorem map_coordinateUnit_eq (Δ : GL (Fin 3) F →* N) (k : Fin 3) (x : Fˣ) :
    Δ (coordinateUnit k x) = Δ (coordinateUnit 0 x) := by
  fin_cases k
  · rfl
  · show Δ (coordinateUnit 1 x) = Δ (coordinateUnit 0 x)
    rw [← swapUnit₀₁_mul_coordinateUnit_mul_inv x, map_conj_eq]
  · show Δ (coordinateUnit 2 x) = Δ (coordinateUnit 0 x)
    rw [← swapUnit₀₂_mul_coordinateUnit_mul_inv x, map_conj_eq]

private theorem map_coordinateUnit_eq_one (Δ : GL (Fin 3) F →* NNReal)
    (hcentral : ∀ z : GL (Fin 3) F, (∀ x, z * x = x * z) → Δ z = 1) (x : Fˣ) :
    Δ (coordinateUnit 0 x) = 1 := by
  apply eq_one_of_pow_three_eq_one
  have h := hcentral (diagonalUnit fun _ => x) (diagonalUnit_const_mul_comm x)
  rw [diagonalUnit_eq_prod, map_mul, map_mul, map_coordinateUnit_eq Δ 1, map_coordinateUnit_eq Δ 2] at h
  rw [pow_succ, pow_two]
  exact h

private theorem map_diagonalUnit_eq_one (Δ : GL (Fin 3) F →* NNReal)
    (hcentral : ∀ z : GL (Fin 3) F, (∀ x, z * x = x * z) → Δ z = 1) (d : Fin 3 → Fˣ) :
    Δ (diagonalUnit d) = 1 := by
  rw [diagonalUnit_eq_prod, map_mul, map_mul, map_coordinateUnit_eq Δ 1, map_coordinateUnit_eq Δ 2,
    map_coordinateUnit_eq_one Δ hcentral, map_coordinateUnit_eq_one Δ hcentral,
    map_coordinateUnit_eq_one Δ hcentral, mul_one, mul_one]

private def transvectionUnit (i j : Fin 3) (hij : i ≠ j) (c : F) : GL (Fin 3) F :=
  GeneralLinearGroup.mkOfDetNeZero (transvection i j c) (by
    rw [det_transvection_of_ne i j hij]
    exact one_ne_zero)

private theorem transvectionUnit_val (i j : Fin 3) (hij : i ≠ j) (c : F) :
    (transvectionUnit i j hij c : Matrix (Fin 3) (Fin 3) F) = transvection i j c :=
  rfl

private theorem transvectionUnit_mul (i j : Fin 3) (hij : i ≠ j) (c c' : F) :
    transvectionUnit i j hij c * transvectionUnit i j hij c' = transvectionUnit i j hij (c + c') := by
  apply Units.ext
  rw [Units.val_mul, transvectionUnit_val, transvectionUnit_val, transvectionUnit_val,
    transvection_mul_transvection_same i j hij]

private theorem transvectionUnit_zero (i j : Fin 3) (hij : i ≠ j) : transvectionUnit i j hij (0 : F) = 1 := by
  apply Units.ext
  rw [transvectionUnit_val, transvection_zero, Units.val_one]

private theorem transvectionUnit_inv (i j : Fin 3) (hij : i ≠ j) (c : F) :
    (transvectionUnit i j hij c)⁻¹ = transvectionUnit i j hij (-c) := by
  apply inv_eq_of_mul_eq_one_right
  rw [transvectionUnit_mul, add_neg_cancel, transvectionUnit_zero]

private theorem coordinateUnit_mul_transvectionUnit_mul_inv (i j : Fin 3) (hij : i ≠ j) (t : Fˣ) (b : F) :
    coordinateUnit i t * transvectionUnit i j hij b * (coordinateUnit i t)⁻¹ =
      transvectionUnit i j hij ((t : F) * b) := by
  rw [coordinateUnit, diagonalUnit_inv]
  apply GeneralLinearGroup.ext
  intro a a'
  rw [Units.val_mul, Units.val_mul, diagonalUnit_val, diagonalUnit_val, transvectionUnit_val,
    transvectionUnit_val, mul_diagonal, diagonal_mul]
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single, of_apply, Function.update_apply]
  by_cases ha : a = i
  · subst ha
    by_cases ha' : a' = a
    · subst ha'
      simp [hij.symm]
    · by_cases hj : a' = j
      · subst hj
        simp [ha', Ne.symm ha']
      · simp [ha', Ne.symm ha', Ne.symm hj]
  · by_cases ha' : a' = i
    · subst ha'
      simp [ha, Ne.symm ha]
    · simp [ha, Ne.symm ha, ha']

private theorem transvectionUnit_eq_commutator (i j : Fin 3) (hij : i ≠ j) (c : F) (t : Fˣ) (ht : (t : F) ≠ 1) :
    transvectionUnit i j hij c =
      coordinateUnit i t * transvectionUnit i j hij (c / ((t : F) - 1)) * (coordinateUnit i t)⁻¹ *
        (transvectionUnit i j hij (c / ((t : F) - 1)))⁻¹ := by
  rw [coordinateUnit_mul_transvectionUnit_mul_inv, transvectionUnit_inv, transvectionUnit_mul]
  have h1 : (t : F) - 1 ≠ 0 := sub_ne_zero.2 ht
  have h2 : (t : F) * (c / ((t : F) - 1)) + -(c / ((t : F) - 1)) = c := by
    rw [← sub_eq_add_neg, ← sub_one_mul]
    field_simp
  exact congrArg (transvectionUnit i j hij) h2.symm

private theorem map_transvectionUnit_eq_one (Δ : GL (Fin 3) F →* N) (ht : ∃ t : F, t ≠ 0 ∧ t ≠ 1) (i j : Fin 3)
    (hij : i ≠ j) (c : F) : Δ (transvectionUnit i j hij c) = 1 := by
  obtain ⟨t, ht0, ht1⟩ := ht
  have ht1' : ((Units.mk0 t ht0 : Fˣ) : F) ≠ 1 := by
    rw [Units.val_mk0]
    exact ht1
  rw [transvectionUnit_eq_commutator i j hij c (Units.mk0 t ht0) ht1', map_mul, map_conj_eq, map_mul_map_inv]

private theorem map_eq_one (Δ : GL (Fin 3) F →* NNReal) (ht : ∃ t : F, t ≠ 0 ∧ t ≠ 1)
    (hcentral : ∀ z : GL (Fin 3) F, (∀ x, z * x = x * z) → Δ z = 1) (g : GL (Fin 3) F) : Δ g = 1 := by
  have key : ∀ A : Matrix (Fin 3) (Fin 3) F, A.det ≠ 0 →
      ∀ g' : GL (Fin 3) F, (g' : Matrix (Fin 3) (Fin 3) F) = A → Δ g' = 1 := by
    intro A hA
    refine diagonal_transvection_induction_of_det_ne_zero
      (fun B => ∀ g' : GL (Fin 3) F, (g' : Matrix (Fin 3) (Fin 3) F) = B → Δ g' = 1) A hA ?_ ?_ ?_
    · intro D hD g' hg'
      rw [det_diagonal] at hD
      have hD' : ∀ k, D k ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hD k (Finset.mem_univ k)
      have hg'' : g' = diagonalUnit fun k => Units.mk0 (D k) (hD' k) := by
        apply Units.ext
        rw [hg', diagonalUnit_val]
        simp only [Units.val_mk0]
      rw [hg'']
      exact map_diagonalUnit_eq_one Δ hcentral _
    · intro s g' hg'
      have hg'' : g' = transvectionUnit s.i s.j s.hij s.c := by
        apply Units.ext
        rw [hg', transvectionUnit_val]
        rfl
      rw [hg'']
      exact map_transvectionUnit_eq_one Δ ht _ _ _ _
    · intro B C hB hC hPB hPC g' hg'
      have hg'' : g' = GeneralLinearGroup.mkOfDetNeZero B hB * GeneralLinearGroup.mkOfDetNeZero C hC := by
        apply Units.ext
        rw [hg', Units.val_mul]
        rfl
      rw [hg'', map_mul, hPB _ rfl, hPC _ rfl, mul_one]
  exact key _ (GeneralLinearGroup.det_ne_zero g) g rfl

end GL3
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end GL3Hom
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end Gl3HomTrivial
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section RightInvariance

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace Unimodular

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]

private theorem modularCharacter_apply (g : G) : modularCharacter g = modularCharacterFun g :=
  rfl

section Measure

variable [MeasurableSpace G] [BorelSpace G]

private theorem modularCharacterFun_eq_one_of_central (μ : Measure G) [IsHaarMeasure μ] {z : G}
    (hz : ∀ x, z * x = x * z) : modularCharacterFun z = 1 := by
  rw [modularCharacterFun_eq_haarScalarFactor μ z]
  have h : (fun x : G => x * z) = fun x : G => z * x := funext fun x => (hz x).symm
  have hm : Measure.map (fun x : G => x * z) μ = μ := by
    rw [h]
    exact map_mul_left_eq_self μ z
  have key : ∀ (ν : Measure G) [IsHaarMeasure ν], ν = μ → haarScalarFactor ν μ = 1 := by
    rintro ν _ rfl
    exact haarScalarFactor_self ν
  exact key _ hm

private theorem isMulRightInvariant_of_forall_modularCharacterFun_eq_one (μ : Measure G) [IsHaarMeasure μ]
    [μ.InnerRegular] (h : ∀ g : G, modularCharacterFun g = 1) : IsMulRightInvariant μ :=
  ⟨fun g => by rw [map_right_mul_eq_modularCharacterFun_smul μ g, h g, one_smul]⟩

private theorem isMulRightInvariant_of_forall_hom_eq_one (μ : Measure G) [IsHaarMeasure μ] [μ.InnerRegular]
    (halg : ∀ Δ : G →* ℝ≥0, (∀ z : G, (∀ x, z * x = x * z) → Δ z = 1) → ∀ g, Δ g = 1) :
    IsMulRightInvariant μ :=
  isMulRightInvariant_of_forall_modularCharacterFun_eq_one μ fun g =>
    (modularCharacter_apply g).symm.trans
      (halg modularCharacter
        (fun z hz => (modularCharacter_apply z).trans (modularCharacterFun_eq_one_of_central μ hz)) g)

end Measure
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end Unimodular
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end RightInvariance
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section Gl3Unimodular

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace Unimodular

variable {F : Type*} [Field F] [TopologicalSpace (GL (Fin 3) F)] [IsTopologicalGroup (GL (Fin 3) F)]
  [LocallyCompactSpace (GL (Fin 3) F)] [MeasurableSpace (GL (Fin 3) F)] [BorelSpace (GL (Fin 3) F)]

private theorem isMulRightInvariant_generalLinearGroup (ht : ∃ t : F, t ≠ 0 ∧ t ≠ 1)
    (μ : Measure (GL (Fin 3) F)) [IsHaarMeasure μ] [μ.InnerRegular] : IsMulRightInvariant μ :=
  isMulRightInvariant_of_forall_hom_eq_one μ fun Δ h g => GL3Hom.map_eq_one Δ ht h g

end Unimodular
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end Gl3Unimodular
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section HaarInvolution
open LanglandsTunnell.CubicInduction.TransposeTwist

p2m_open "MeasureTheory Measure MeasureTheory.Measure"
open scoped NNReal ENNReal

namespace HaarInvolution

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

private theorem eq_one_of_mul_self_smul_eq (μ : Measure G) [μ.IsHaarMeasure] {c : ℝ≥0}
    (h : (c * c) • μ = μ) : c = 1 := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have h0 : μ K ≠ 0 := (measure_pos_of_mem_nhds μ hK1).ne'
  have htop : μ K ≠ ∞ := hK.measure_lt_top.ne
  have hK' : ((c * c : ℝ≥0) : ℝ≥0∞) * μ K = 1 * μ K := by
    have := congrArg (fun ν : Measure G => ν K) h
    simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, one_mul] using this
  have hcc : c * c = 1 := ENNReal.coe_eq_one.1 ((ENNReal.mul_left_inj h0 htop).1 hK')
  exact (pow_eq_one_iff_of_nonneg (zero_le : (0 : ℝ≥0) ≤ c) two_ne_zero).1 (by rw [sq]; exact hcc)

private theorem isInvInvariant_of_isMulRightInvariant (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegular]
    [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  have h1 : μ.inv = μ.inv.haarScalarFactor μ • μ := isMulLeftInvariant_eq_smul_of_innerRegular μ.inv μ
  have h2 : (μ.inv.haarScalarFactor μ * μ.inv.haarScalarFactor μ) • μ = μ := by
    calc (μ.inv.haarScalarFactor μ * μ.inv.haarScalarFactor μ) • μ
        = μ.inv.haarScalarFactor μ • (μ.inv.haarScalarFactor μ • μ) := mul_smul _ _ _
      _ = μ.inv.haarScalarFactor μ • μ.inv := by rw [← h1]
      _ = (μ.inv.haarScalarFactor μ • μ).inv := by
            simp only [Measure.inv_def, Measure.map_smul]
      _ = μ.inv.inv := by rw [← h1]
      _ = μ := Measure.inv_inv μ
  refine ⟨?_⟩
  rw [h1, eq_one_of_mul_self_smul_eq μ h2, one_smul]

private theorem map_eq_self_of_involutive (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegular] (τ : G ≃ₜ* G)
    (hτ : ∀ g, τ (τ g) = g) : Measure.map τ μ = μ := by
  have hτc : Continuous τ := (τ : G ≃ₜ G).continuous
  haveI : (Measure.map τ μ).InnerRegular := InnerRegular.map_of_continuous hτc
  have h1 : Measure.map τ μ = (Measure.map τ μ).haarScalarFactor μ • μ :=
    isMulLeftInvariant_eq_smul_of_innerRegular _ μ
  have h2 : ((Measure.map τ μ).haarScalarFactor μ * (Measure.map τ μ).haarScalarFactor μ) • μ = μ := by
    have hττ : (⇑τ ∘ ⇑τ) = id := funext hτ
    calc ((Measure.map τ μ).haarScalarFactor μ * (Measure.map τ μ).haarScalarFactor μ) • μ
        = (Measure.map τ μ).haarScalarFactor μ • ((Measure.map τ μ).haarScalarFactor μ • μ) :=
          mul_smul _ _ _
      _ = (Measure.map τ μ).haarScalarFactor μ • Measure.map τ μ := by rw [← h1]
      _ = Measure.map τ ((Measure.map τ μ).haarScalarFactor μ • μ) := (Measure.map_smul _ _ _).symm
      _ = Measure.map τ (Measure.map τ μ) := by rw [← h1]
      _ = Measure.map (⇑τ ∘ ⇑τ) μ := Measure.map_map hτc.measurable hτc.measurable
      _ = μ := by rw [hττ, Measure.map_id]
  rw [h1, eq_one_of_mul_self_smul_eq μ h2, one_smul]

end HaarInvolution
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.localMaximalCompact3 CubicInduction.mem_localMaximalCompact3_iff CubicInduction.transposeInv3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localMaximalCompact3 mem_localMaximalCompact3_iff transposeInv3 LocalGL3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable {F : Type*} [Field F] [TopologicalSpace F]

private def transposeInv3ContinuousMulEquiv : GL (Fin 3) F ≃ₜ* GL (Fin 3) F :=
  { transposeInv3Equiv with
    continuous_toFun := continuous_transposeInv3
    continuous_invFun := continuous_transposeInv3 }

private theorem map_transposeInv3_eq_self [IsTopologicalGroup (GL (Fin 3) F)]
    [LocallyCompactSpace (GL (Fin 3) F)] [MeasurableSpace (GL (Fin 3) F)]
    [BorelSpace (GL (Fin 3) F)] (μ : Measure (GL (Fin 3) F)) [μ.IsHaarMeasure] [μ.InnerRegular] :
    Measure.map (transposeInv3 : GL (Fin 3) F → GL (Fin 3) F) μ = μ :=
  HaarInvolution.map_eq_self_of_involutive μ transposeInv3ContinuousMulEquiv
    transposeInv3_transposeInv3

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

end HaarInvolution
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata"

section RankTrace

namespace Character

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private def corestrict (A : Module.End ℂ V) (U : Submodule ℂ V) (h : ∀ x, A x ∈ U) : Module.End ℂ U :=
  LinearMap.codRestrict U (A ∘ₗ U.subtype) fun x => h x

@[scoped simp]
private theorem corestrict_apply_coe (A : Module.End ℂ V) (U : Submodule ℂ V) (h : ∀ x, A x ∈ U) (x : U) :
    (corestrict A U h x : V) = A x :=
  rfl

private theorem corestrict_add (A B : Module.End ℂ V) (U : Submodule ℂ V) (hA : ∀ x, A x ∈ U)
    (hB : ∀ x, B x ∈ U) :
    corestrict (A + B) U (fun x => U.add_mem (hA x) (hB x)) = corestrict A U hA + corestrict B U hB := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  simp

private theorem corestrict_smul (c : ℂ) (A : Module.End ℂ V) (U : Submodule ℂ V) (hA : ∀ x, A x ∈ U) :
    corestrict (c • A) U (fun x => U.smul_mem c (hA x)) = c • corestrict A U hA := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  simp

private theorem trace_corestrict_eq (A : Module.End ℂ V) {U W : Submodule ℂ V} (hUW : U ≤ W)
    (hU : ∀ x, A x ∈ U) [FiniteDimensional ℂ U] [FiniteDimensional ℂ W] :
    LinearMap.trace ℂ W (corestrict A W fun x => hUW (hU x)) =
      LinearMap.trace ℂ U (corestrict A U hU) := by
  let c : W →ₗ[ℂ] U := LinearMap.codRestrict U (A ∘ₗ W.subtype) fun x => hU x
  have h1 : corestrict A W (fun x => hUW (hU x)) = Submodule.inclusion hUW ∘ₗ c :=
    LinearMap.ext fun x => Subtype.ext rfl
  have h2 : corestrict A U hU = c ∘ₗ Submodule.inclusion hUW :=
    LinearMap.ext fun x => Subtype.ext rfl
  rw [h1, h2, LinearMap.trace_comp_comm']

private noncomputable def rankTrace (A : Module.End ℂ V) (U : Submodule ℂ V) (h : ∀ x, A x ∈ U)
    [FiniteDimensional ℂ U] : ℂ :=
  LinearMap.trace ℂ U (corestrict A U h)

private theorem rankTrace_eq (A : Module.End ℂ V) {U U' : Submodule ℂ V} (hU : ∀ x, A x ∈ U)
    (hU' : ∀ x, A x ∈ U') [FiniteDimensional ℂ U] [FiniteDimensional ℂ U'] :
    rankTrace A U hU = rankTrace A U' hU' := by
  have h1 := trace_corestrict_eq A (le_sup_left : U ≤ U ⊔ U') hU
  have h2 := trace_corestrict_eq A (le_sup_right : U' ≤ U ⊔ U') hU'
  exact h1.symm.trans h2

private theorem rankTrace_add (A B : Module.End ℂ V) (U : Submodule ℂ V) (hA : ∀ x, A x ∈ U)
    (hB : ∀ x, B x ∈ U) [FiniteDimensional ℂ U] :
    rankTrace (A + B) U (fun x => U.add_mem (hA x) (hB x)) = rankTrace A U hA + rankTrace B U hB := by
  unfold rankTrace
  rw [corestrict_add, map_add]

private theorem rankTrace_smul (c : ℂ) (A : Module.End ℂ V) (U : Submodule ℂ V) (hA : ∀ x, A x ∈ U)
    [FiniteDimensional ℂ U] :
    rankTrace (c • A) U (fun x => U.smul_mem c (hA x)) = c • rankTrace A U hA := by
  unfold rankTrace
  rw [corestrict_smul, map_smul]

private theorem conj_apply_mem_map (g : V ≃ₗ[ℂ] V) (A : Module.End ℂ V) (U : Submodule ℂ V)
    (hA : ∀ x, A x ∈ U) (x : V) :
    ((g : V →ₗ[ℂ] V) ∘ₗ A ∘ₗ (g.symm : V →ₗ[ℂ] V)) x ∈ U.map (g : V →ₗ[ℂ] V) :=
  Submodule.mem_map.mpr ⟨A (g.symm x), hA _, rfl⟩

private theorem corestrict_conj (g : V ≃ₗ[ℂ] V) (A : Module.End ℂ V) (U : Submodule ℂ V)
    (hA : ∀ x, A x ∈ U) :
    corestrict ((g : V →ₗ[ℂ] V) ∘ₗ A ∘ₗ (g.symm : V →ₗ[ℂ] V)) (U.map (g : V →ₗ[ℂ] V))
        (conj_apply_mem_map g A U hA) =
      (g.submoduleMap U).conj (corestrict A U hA) := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  obtain ⟨y, rfl⟩ := (g.submoduleMap U).surjective x
  simp [LinearEquiv.submoduleMap_apply]

private theorem rankTrace_conj (g : V ≃ₗ[ℂ] V) (A : Module.End ℂ V) (U : Submodule ℂ V)
    (hA : ∀ x, A x ∈ U) [FiniteDimensional ℂ U] [FiniteDimensional ℂ (U.map (g : V →ₗ[ℂ] V))] :
    rankTrace ((g : V →ₗ[ℂ] V) ∘ₗ A ∘ₗ (g.symm : V →ₗ[ℂ] V)) (U.map (g : V →ₗ[ℂ] V))
        (conj_apply_mem_map g A U hA) =
      rankTrace A U hA := by
  unfold rankTrace
  rw [corestrict_conj, LinearMap.trace_conj']

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end RankTrace
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section Character

namespace Character

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem rankTrace_congr {A A' : Module.End ℂ V} (hAA' : A = A') (U : Submodule ℂ V)
    (hA : ∀ x, A x ∈ U) (hA' : ∀ x, A' x ∈ U) [FiniteDimensional ℂ U] :
    rankTrace A U hA = rankTrace A' U hA' := by
  subst hAA'
  rfl

variable {S : Type*} [AddCommGroup S] [Module ℂ S] {ι : Type*}

private def HasLevel (H : S →ₗ[ℂ] Module.End ℂ V) (e : ι → S) (φ : S) (i : ι) : Prop :=
  H φ = H (e i) * H φ * H (e i)

private structure IsLevelFamily (H : S →ₗ[ℂ] Module.End ℂ V) (e : ι → S) : Prop where
  idem : ∀ i, IsIdempotentElem (H (e i))
  finite : ∀ i, FiniteDimensional ℂ (LinearMap.range (H (e i)))
  directed : ∀ i j, ∃ k, (H (e k) * H (e i) = H (e i) ∧ H (e i) * H (e k) = H (e i)) ∧
    (H (e k) * H (e j) = H (e j) ∧ H (e j) * H (e k) = H (e j))
  exhaustive : ∀ φ : S, ∃ i, HasLevel H e φ i

variable {H : S →ₗ[ℂ] Module.End ℂ V} {e : ι → S}

private theorem HasLevel.apply_mem_range {φ : S} {i : ι} (h : HasLevel H e φ i) (x : V) :
    H φ x ∈ LinearMap.range (H (e i)) := by
  have hx := congrArg (fun T : Module.End ℂ V => T x) h
  simp only [Module.End.mul_apply] at hx
  rw [hx]
  exact LinearMap.mem_range_self _ _

private theorem HasLevel.of_absorb {φ : S} {i k : ι} (h : HasLevel H e φ i)
    (hk : H (e k) * H (e i) = H (e i) ∧ H (e i) * H (e k) = H (e i)) : HasLevel H e φ k := by
  unfold HasLevel at h ⊢
  calc H φ = H (e i) * H φ * H (e i) := h
    _ = H (e k) * H (e i) * H φ * (H (e i) * H (e k)) := by rw [hk.1, hk.2]
    _ = H (e k) * (H (e i) * H φ * H (e i)) * H (e k) := by simp only [mul_assoc]
    _ = H (e k) * H φ * H (e k) := by rw [← h]

private theorem HasLevel.add {φ ψ : S} {k : ι} (hφ : HasLevel H e φ k) (hψ : HasLevel H e ψ k) :
    HasLevel H e (φ + ψ) k := by
  unfold HasLevel at hφ hψ ⊢
  rw [map_add, mul_add, add_mul, ← hφ, ← hψ]

private theorem HasLevel.smul {φ : S} {k : ι} (c : ℂ) (hφ : HasLevel H e φ k) : HasLevel H e (c • φ) k := by
  unfold HasLevel at hφ ⊢
  rw [map_smul, mul_smul_comm, smul_mul_assoc, ← hφ]

private theorem IsLevelFamily.exists_common_level (L : IsLevelFamily H e) (φ ψ : S) :
    ∃ k, HasLevel H e φ k ∧ HasLevel H e ψ k := by
  obtain ⟨i, hi⟩ := L.exhaustive φ
  obtain ⟨j, hj⟩ := L.exhaustive ψ
  obtain ⟨k, hki, hkj⟩ := L.directed i j
  exact ⟨k, hi.of_absorb hki, hj.of_absorb hkj⟩

private noncomputable def characterAt (L : IsLevelFamily H e) (φ : S) (i : ι) (h : HasLevel H e φ i) : ℂ :=
  @rankTrace V _ _ (H φ) (LinearMap.range (H (e i))) h.apply_mem_range (L.finite i)

private theorem characterAt_eq (L : IsLevelFamily H e) {φ : S} {i j : ι} (hi : HasLevel H e φ i)
    (hj : HasLevel H e φ j) : characterAt L φ i hi = characterAt L φ j hj :=
  @rankTrace_eq V _ _ (H φ) _ _ hi.apply_mem_range hj.apply_mem_range (L.finite i) (L.finite j)

private theorem characterAt_add (L : IsLevelFamily H e) {φ ψ : S} {k : ι} (hφ : HasLevel H e φ k)
    (hψ : HasLevel H e ψ k) :
    characterAt L (φ + ψ) k (hφ.add hψ) = characterAt L φ k hφ + characterAt L ψ k hψ := by
  unfold characterAt
  rw [@rankTrace_congr V _ _ (H (φ + ψ)) (H φ + H ψ) (map_add H φ ψ) (LinearMap.range (H (e k)))
    (hφ.add hψ).apply_mem_range
    (fun x => (LinearMap.range (H (e k))).add_mem (hφ.apply_mem_range x) (hψ.apply_mem_range x))
    (L.finite k)]
  exact @rankTrace_add V _ _ (H φ) (H ψ) (LinearMap.range (H (e k))) hφ.apply_mem_range
    hψ.apply_mem_range (L.finite k)

private theorem characterAt_smul (L : IsLevelFamily H e) {φ : S} {k : ι} (c : ℂ) (hφ : HasLevel H e φ k) :
    characterAt L (c • φ) k (hφ.smul c) = c • characterAt L φ k hφ := by
  unfold characterAt
  rw [@rankTrace_congr V _ _ (H (c • φ)) (c • H φ) (map_smul H c φ) (LinearMap.range (H (e k)))
    (hφ.smul c).apply_mem_range
    (fun x => (LinearMap.range (H (e k))).smul_mem c (hφ.apply_mem_range x)) (L.finite k)]
  exact @rankTrace_smul V _ _ c (H φ) (LinearMap.range (H (e k))) hφ.apply_mem_range (L.finite k)

private noncomputable def character (L : IsLevelFamily H e) : S →ₗ[ℂ] ℂ where
  toFun φ := characterAt L φ (L.exhaustive φ).choose (L.exhaustive φ).choose_spec
  map_add' φ ψ := by
    show characterAt L (φ + ψ) _ _ = characterAt L φ _ _ + characterAt L ψ _ _
    obtain ⟨k, hφ, hψ⟩ := L.exists_common_level φ ψ
    rw [characterAt_eq L _ (hφ.add hψ), characterAt_eq L (L.exhaustive φ).choose_spec hφ,
      characterAt_eq L (L.exhaustive ψ).choose_spec hψ]
    exact characterAt_add L hφ hψ
  map_smul' c φ := by
    show characterAt L (c • φ) _ _ = c • characterAt L φ _ _
    obtain ⟨i, hi⟩ := L.exhaustive φ
    rw [characterAt_eq L _ (hi.smul c), characterAt_eq L (L.exhaustive φ).choose_spec hi]
    exact characterAt_smul L c hi

private theorem character_apply (L : IsLevelFamily H e) (φ : S) :
    character L φ = characterAt L φ (L.exhaustive φ).choose (L.exhaustive φ).choose_spec :=
  rfl

private theorem character_eq_rankTrace (L : IsLevelFamily H e) {φ : S} {i : ι} (hi : HasLevel H e φ i) :
    character L φ =
      @rankTrace V _ _ (H φ) (LinearMap.range (H (e i))) hi.apply_mem_range (L.finite i) :=
  characterAt_eq L (L.exhaustive φ).choose_spec hi

section Conjugation

variable {G : Type*} [Group G]

private def toLinearEquiv (π : G →* Module.End ℂ V) (g : G) : V ≃ₗ[ℂ] V :=
  LinearEquiv.ofLinear (π g) (π g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one, Module.End.one_eq_id])
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one, Module.End.one_eq_id])

private theorem coe_toLinearEquiv (π : G →* Module.End ℂ V) (g : G) :
    (toLinearEquiv π g : V →ₗ[ℂ] V) = π g :=
  rfl

private theorem coe_toLinearEquiv_symm (π : G →* Module.End ℂ V) (g : G) :
    ((toLinearEquiv π g).symm : V →ₗ[ℂ] V) = π g⁻¹ :=
  rfl

private theorem character_conj (L : IsLevelFamily H e) (π : G →* Module.End ℂ V) (Lt Rt : G → S →ₗ[ℂ] S)
    (law_left : ∀ (n : G) (φ : S), H (Lt n φ) = π n * H φ)
    (law_right : ∀ (m : G) (φ : S), H (Rt m φ) = H φ * π m⁻¹) (g : G) (φ : S) :
    character L (Lt g (Rt g φ)) = character L φ := by
  obtain ⟨i, hi⟩ := L.exhaustive φ
  obtain ⟨j, hj⟩ := L.exhaustive (Lt g (Rt g φ))
  have hop : H (Lt g (Rt g φ)) =
      (toLinearEquiv π g : V →ₗ[ℂ] V) ∘ₗ H φ ∘ₗ ((toLinearEquiv π g).symm : V →ₗ[ℂ] V) := by
    rw [law_left, law_right, coe_toLinearEquiv, coe_toLinearEquiv_symm, ← Module.End.mul_eq_comp,
      ← Module.End.mul_eq_comp]
  haveI : FiniteDimensional ℂ (LinearMap.range (H (e i))) := L.finite i
  have instMap :
      FiniteDimensional ℂ ((LinearMap.range (H (e i))).map (toLinearEquiv π g : V →ₗ[ℂ] V)) :=
    Module.Finite.map _ _
  have hmem : ∀ x, H (Lt g (Rt g φ)) x ∈
      (LinearMap.range (H (e i))).map (toLinearEquiv π g : V →ₗ[ℂ] V) := by
    intro x
    rw [hop]
    exact conj_apply_mem_map (toLinearEquiv π g) (H φ) _ hi.apply_mem_range x
  rw [character_eq_rankTrace L hj, character_eq_rankTrace L hi,
    @rankTrace_eq V _ _ (H (Lt g (Rt g φ))) _ _ hj.apply_mem_range hmem (L.finite j) instMap,
    @rankTrace_congr V _ _ _ _ hop _ hmem
      (conj_apply_mem_map (toLinearEquiv π g) (H φ) _ hi.apply_mem_range) instMap]
  exact @rankTrace_conj V _ _ (toLinearEquiv π g) (H φ) _ hi.apply_mem_range (L.finite i) instMap

end Conjugation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section FixedVectors

namespace Character

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Type*} [AddCommGroup S] [Module ℂ S]

variable (H : S →ₗ[ℂ] Module.End ℂ V)

private def hSpan (M : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ φ : S, ∃ m ∈ M, H φ m = v}

private def IsStable (N : Submodule ℂ V) : Prop :=
  ∀ φ : S, ∀ v ∈ N, H φ v ∈ N

private def _root_.Character.IsIrreducible : Prop :=
  Nontrivial V ∧ ∀ N : Submodule ℂ V, IsStable H N → N = ⊥ ∨ N = ⊤

p2m_export "Character" "IsIrreducible"

private def IsLevelStable (ε : S) (M : Submodule ℂ V) : Prop :=
  ∀ φ : S, ∀ m ∈ M, (H ε * H φ * H ε) m ∈ M

private def levelSpan (ε : S) (M : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ φ : S, ∃ m ∈ M, (H ε * H φ * H ε) m = v}

variable {H}

private theorem hSpan_isStable (hconv : ∀ φ ψ : S, ∃ χ : S, H φ * H ψ = H χ) (M : Submodule ℂ V) :
    IsStable H (hSpan H M) := by
  intro ψ v hv
  have key : (hSpan H M).map (H ψ) ≤ hSpan H M := by
    unfold hSpan
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨φ, m, hm, rfl⟩, rfl⟩
    obtain ⟨χ, hχ⟩ := hconv ψ φ
    refine Submodule.subset_span ⟨χ, m, hm, ?_⟩
    exact ((Module.End.mul_apply (H ψ) (H φ) m).symm.trans
      (congrArg (fun T : Module.End ℂ V => T m) hχ)).symm
  exact key (Submodule.mem_map_of_mem hv)

private theorem apply_eq_self_of_mem_range {p : Module.End ℂ V} (hp : IsIdempotentElem p) {x : V}
    (hx : x ∈ LinearMap.range p) : p x = x := by
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  exact LinearMap.congr_fun hp.eq y

private theorem le_hSpan {ε : S} (hε : IsIdempotentElem (H ε)) {M : Submodule ℂ V}
    (hM : M ≤ LinearMap.range (H ε)) : M ≤ hSpan H M := by
  intro m hm
  exact Submodule.subset_span ⟨ε, m, hm, apply_eq_self_of_mem_range hε (hM hm)⟩

private theorem map_hSpan_eq_levelSpan {ε : S} (hε : IsIdempotentElem (H ε)) {M : Submodule ℂ V}
    (hM : M ≤ LinearMap.range (H ε)) : (hSpan H M).map (H ε) = levelSpan H ε M := by
  unfold hSpan levelSpan
  rw [Submodule.map_span]
  refine congrArg (Submodule.span ℂ) (Set.ext fun v => ?_)
  constructor
  · rintro ⟨_, ⟨φ, m, hm, rfl⟩, rfl⟩
    refine ⟨φ, m, hm, ?_⟩
    show H ε (H φ (H ε m)) = H ε (H φ m)
    rw [apply_eq_self_of_mem_range hε (hM hm)]
  · rintro ⟨φ, m, hm, rfl⟩
    refine ⟨H φ m, ⟨φ, m, hm, rfl⟩, ?_⟩
    show H ε (H φ m) = H ε (H φ (H ε m))
    rw [apply_eq_self_of_mem_range hε (hM hm)]

private theorem levelSpan_eq_self_of_isLevelStable {ε : S} (hε : IsIdempotentElem (H ε))
    {M : Submodule ℂ V} (hM : M ≤ LinearMap.range (H ε)) (hst : IsLevelStable H ε M) :
    levelSpan H ε M = M := by
  apply le_antisymm
  · unfold levelSpan
    rw [Submodule.span_le]
    rintro _ ⟨φ, m, hm, rfl⟩
    exact hst φ m hm
  · intro m hm
    have hfix : H ε m = m := apply_eq_self_of_mem_range hε (hM hm)
    refine Submodule.subset_span ⟨ε, m, hm, ?_⟩
    show H ε (H ε (H ε m)) = m
    rw [hfix, hfix, hfix]

private theorem eq_range_of_isLevelStable (hconv : ∀ φ ψ : S, ∃ χ : S, H φ * H ψ = H χ)
    (hirr : IsIrreducible H) {ε : S} (hε : IsIdempotentElem (H ε)) {M : Submodule ℂ V}
    (hM : M ≤ LinearMap.range (H ε)) (hst : IsLevelStable H ε M) (hM0 : M ≠ ⊥) :
    M = LinearMap.range (H ε) := by
  have htop : hSpan H M = ⊤ := by
    rcases hirr.2 _ (hSpan_isStable hconv M) with h | h
    · exact absurd (eq_bot_iff.mpr (h ▸ le_hSpan hε hM)) hM0
    · exact h
  have h1 := map_hSpan_eq_levelSpan hε hM
  rw [htop, Submodule.map_top, levelSpan_eq_self_of_isLevelStable hε hM hst] at h1
  exact h1.symm

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end FixedVectors
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section GraphLemma

namespace Character

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  {S : Type*} [AddCommGroup S] [Module ℂ S]

section ProdAction

variable (H₁ : S →ₗ[ℂ] Module.End ℂ V₁) (H₂ : S →ₗ[ℂ] Module.End ℂ V₂)

private def prodAction : S →ₗ[ℂ] Module.End ℂ (V₁ × V₂) where
  toFun φ := (H₁ φ).prodMap (H₂ φ)
  map_add' φ ψ := by
    show (H₁ (φ + ψ)).prodMap (H₂ (φ + ψ)) = (H₁ φ).prodMap (H₂ φ) + (H₁ ψ).prodMap (H₂ ψ)
    rw [map_add, map_add, LinearMap.prodMap_add]
  map_smul' c φ := by
    show (H₁ (c • φ)).prodMap (H₂ (c • φ)) = c • (H₁ φ).prodMap (H₂ φ)
    rw [map_smul, map_smul, LinearMap.prodMap_smul]

private theorem prodAction_apply (φ : S) (x : V₁ × V₂) : prodAction H₁ H₂ φ x = (H₁ φ x.1, H₂ φ x.2) :=
  LinearMap.prodMap_apply _ _ _

private theorem prodAction_mul (φ ψ : S) :
    prodAction H₁ H₂ φ * prodAction H₁ H₂ ψ = (H₁ φ * H₁ ψ).prodMap (H₂ φ * H₂ ψ) :=
  LinearMap.prodMap_mul _ _ _ _

private theorem range_prodAction (ε : S) :
    LinearMap.range (prodAction H₁ H₂ ε) =
      (LinearMap.range (H₁ ε)).prod (LinearMap.range (H₂ ε)) :=
  LinearMap.range_prodMap _ _

variable {H₁ H₂}

private theorem isIdempotentElem_prodAction {ε : S} (hε₁ : IsIdempotentElem (H₁ ε))
    (hε₂ : IsIdempotentElem (H₂ ε)) : IsIdempotentElem (prodAction H₁ H₂ ε) := by
  unfold IsIdempotentElem
  rw [prodAction_mul, hε₁.eq, hε₂.eq]
  rfl

private theorem prodAction_closed (conv : S → S → S) (hc₁ : ∀ φ ψ, H₁ (conv φ ψ) = H₁ φ * H₁ ψ)
    (hc₂ : ∀ φ ψ, H₂ (conv φ ψ) = H₂ φ * H₂ ψ) (φ ψ : S) :
    ∃ χ : S, prodAction H₁ H₂ φ * prodAction H₁ H₂ ψ = prodAction H₁ H₂ χ := by
  refine ⟨conv φ ψ, ?_⟩
  rw [prodAction_mul]
  show (H₁ φ * H₁ ψ).prodMap (H₂ φ * H₂ ψ) = (H₁ (conv φ ψ)).prodMap (H₂ (conv φ ψ))
  rw [hc₁, hc₂]

private structure IsLevelGraph (ε : S) (Γ : Submodule ℂ (V₁ × V₂)) : Prop where
  le_prod : Γ ≤ (LinearMap.range (H₁ ε)).prod (LinearMap.range (H₂ ε))
  levelStable : IsLevelStable (prodAction H₁ H₂) ε Γ
  map_fst : Γ.map (LinearMap.fst ℂ V₁ V₂) = LinearMap.range (H₁ ε)
  map_snd : Γ.map (LinearMap.snd ℂ V₁ V₂) = LinearMap.range (H₂ ε)
  snd_eq_zero : ∀ y : V₂, ((0 : V₁), y) ∈ Γ → y = 0
  fst_eq_zero : ∀ x : V₁, (x, (0 : V₂)) ∈ Γ → x = 0

namespace IsLevelGraph

variable {ε : S} {Γ : Submodule ℂ (V₁ × V₂)}

private theorem range_ne_bot (hg : IsLevelGraph (H₁ := H₁) (H₂ := H₂) ε Γ)
    (h₁ : LinearMap.range (H₁ ε) ≠ ⊥) : LinearMap.range (H₂ ε) ≠ ⊥ := by
  intro h₂
  apply h₁
  rw [← hg.map_fst, Submodule.eq_bot_iff]
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  have hy : y = 0 := by
    have hmem : y ∈ LinearMap.range (H₂ ε) := (Submodule.mem_prod.mp (hg.le_prod hxy)).2
    rw [h₂] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  subst hy
  exact hg.fst_eq_zero x hxy

private theorem le_range_prodAction (hg : IsLevelGraph (H₁ := H₁) (H₂ := H₂) ε Γ) :
    Γ ≤ LinearMap.range (prodAction H₁ H₂ ε) := by
  rw [range_prodAction]
  exact hg.le_prod

private theorem map_hSpan (hg : IsLevelGraph (H₁ := H₁) (H₂ := H₂) ε Γ) (hε₁ : IsIdempotentElem (H₁ ε))
    (hε₂ : IsIdempotentElem (H₂ ε)) :
    (hSpan (prodAction H₁ H₂) Γ).map (prodAction H₁ H₂ ε) = Γ := by
  rw [map_hSpan_eq_levelSpan (isIdempotentElem_prodAction hε₁ hε₂) hg.le_range_prodAction,
    levelSpan_eq_self_of_isLevelStable (isIdempotentElem_prodAction hε₁ hε₂)
      hg.le_range_prodAction hg.levelStable]

private theorem prodAction_apply_mem (hg : IsLevelGraph (H₁ := H₁) (H₂ := H₂) ε Γ)
    (hε₁ : IsIdempotentElem (H₁ ε)) (hε₂ : IsIdempotentElem (H₂ ε)) {z : V₁ × V₂}
    (hz : z ∈ hSpan (prodAction H₁ H₂) Γ) : prodAction H₁ H₂ ε z ∈ Γ := by
  have h := Submodule.mem_map_of_mem (f := prodAction H₁ H₂ ε) hz
  rwa [hg.map_hSpan hε₁ hε₂] at h

end IsLevelGraph
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end ProdAction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section Graph

variable {H₁ : S →ₗ[ℂ] Module.End ℂ V₁} {H₂ : S →ₗ[ℂ] Module.End ℂ V₂}
  (conv : S → S → S) (hc₁ : ∀ φ ψ, H₁ (conv φ ψ) = H₁ φ * H₁ ψ)
  (hc₂ : ∀ φ ψ, H₂ (conv φ ψ) = H₂ φ * H₂ ψ)
  (hirr₁ : IsIrreducible H₁) (hirr₂ : IsIrreducible H₂)
  {ε : S} (hε₁ : IsIdempotentElem (H₁ ε)) (hε₂ : IsIdempotentElem (H₂ ε))
  {Γ : Submodule ℂ (V₁ × V₂)} (hg : IsLevelGraph (H₁ := H₁) (H₂ := H₂) ε Γ)
  (h₁ : LinearMap.range (H₁ ε) ≠ ⊥)

include hc₁ hc₂ hirr₂ hε₁ hε₂ hg h₁ in

private theorem snd_eq_zero_of_mem_hSpan (y : V₂) (hy : ((0 : V₁), y) ∈ hSpan (prodAction H₁ H₂) Γ) :
    y = 0 := by
  set Z := hSpan (prodAction H₁ H₂) Γ with hZ
  have hstable : IsStable (prodAction H₁ H₂) Z := hSpan_isStable (prodAction_closed conv hc₁ hc₂) Γ
  let K : Submodule ℂ V₂ := Z.comap (LinearMap.inr ℂ V₁ V₂)
  have hK : IsStable H₂ K := by
    intro φ v hv
    rw [Submodule.mem_comap, LinearMap.inr_apply] at hv ⊢
    have h := hstable φ _ hv
    rwa [prodAction_apply, map_zero] at h
  rcases hirr₂.2 K hK with hbot | htop
  · have hyK : y ∈ K := by
      rw [Submodule.mem_comap, LinearMap.inr_apply]
      exact hy
    rw [hbot] at hyK
    exact (Submodule.mem_bot ℂ).mp hyK
  · exfalso
    apply hg.range_ne_bot h₁
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hvK : v ∈ K := by
      rw [htop]
      exact Submodule.mem_top
    rw [Submodule.mem_comap, LinearMap.inr_apply] at hvK
    have hfix := hg.prodAction_apply_mem hε₁ hε₂ hvK
    rw [prodAction_apply, map_zero, apply_eq_self_of_mem_range hε₂ hv] at hfix
    exact hg.snd_eq_zero v hfix

include hc₁ hc₂ hirr₁ hε₁ hε₂ hg h₁ in

private theorem fst_eq_zero_of_mem_hSpan (x : V₁) (hx : (x, (0 : V₂)) ∈ hSpan (prodAction H₁ H₂) Γ) :
    x = 0 := by
  set Z := hSpan (prodAction H₁ H₂) Γ with hZ
  have hstable : IsStable (prodAction H₁ H₂) Z := hSpan_isStable (prodAction_closed conv hc₁ hc₂) Γ
  let K : Submodule ℂ V₁ := Z.comap (LinearMap.inl ℂ V₁ V₂)
  have hK : IsStable H₁ K := by
    intro φ v hv
    rw [Submodule.mem_comap, LinearMap.inl_apply] at hv ⊢
    have h := hstable φ _ hv
    rwa [prodAction_apply, map_zero] at h
  rcases hirr₁.2 K hK with hbot | htop
  · have hxK : x ∈ K := by
      rw [Submodule.mem_comap, LinearMap.inl_apply]
      exact hx
    rw [hbot] at hxK
    exact (Submodule.mem_bot ℂ).mp hxK
  · exfalso
    apply h₁
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hvK : v ∈ K := by
      rw [htop]
      exact Submodule.mem_top
    rw [Submodule.mem_comap, LinearMap.inl_apply] at hvK
    have hfix := hg.prodAction_apply_mem hε₁ hε₂ hvK
    rw [prodAction_apply, map_zero, apply_eq_self_of_mem_range hε₁ hv] at hfix
    exact hg.fst_eq_zero v hfix

include hc₁ hc₂ hirr₁ hε₁ hε₂ hg h₁ in

private theorem map_fst_hSpan_eq_top : (hSpan (prodAction H₁ H₂) Γ).map (LinearMap.fst ℂ V₁ V₂) = ⊤ := by
  set Z := hSpan (prodAction H₁ H₂) Γ with hZ
  have hstable : IsStable (prodAction H₁ H₂) Z := hSpan_isStable (prodAction_closed conv hc₁ hc₂) Γ
  have hst : IsStable H₁ (Z.map (LinearMap.fst ℂ V₁ V₂)) := by
    rintro φ _ ⟨z, hz, rfl⟩
    refine ⟨prodAction H₁ H₂ φ z, hstable φ z hz, ?_⟩
    rw [prodAction_apply]
    rfl
  have hle : LinearMap.range (H₁ ε) ≤ Z.map (LinearMap.fst ℂ V₁ V₂) := by
    rw [← hg.map_fst]
    exact Submodule.map_mono (le_hSpan (isIdempotentElem_prodAction hε₁ hε₂) hg.le_range_prodAction)
  rcases hirr₁.2 _ hst with hbot | htop
  · exact absurd (eq_bot_iff.mpr (hbot ▸ hle)) h₁
  · exact htop

include hc₁ hc₂ hirr₂ hε₁ hε₂ hg h₁ in

private theorem map_snd_hSpan_eq_top : (hSpan (prodAction H₁ H₂) Γ).map (LinearMap.snd ℂ V₁ V₂) = ⊤ := by
  set Z := hSpan (prodAction H₁ H₂) Γ with hZ
  have hstable : IsStable (prodAction H₁ H₂) Z := hSpan_isStable (prodAction_closed conv hc₁ hc₂) Γ
  have hst : IsStable H₂ (Z.map (LinearMap.snd ℂ V₁ V₂)) := by
    rintro φ _ ⟨z, hz, rfl⟩
    refine ⟨prodAction H₁ H₂ φ z, hstable φ z hz, ?_⟩
    rw [prodAction_apply]
    rfl
  have hle : LinearMap.range (H₂ ε) ≤ Z.map (LinearMap.snd ℂ V₁ V₂) := by
    rw [← hg.map_snd]
    exact Submodule.map_mono (le_hSpan (isIdempotentElem_prodAction hε₁ hε₂) hg.le_range_prodAction)
  rcases hirr₂.2 _ hst with hbot | htop
  · exact absurd (eq_bot_iff.mpr (hbot ▸ hle)) (hg.range_ne_bot h₁)
  · exact htop

include hc₁ hc₂ hirr₁ hirr₂ hε₁ hε₂ hg h₁ in

private theorem exists_equiv_of_isLevelGraph :
    ∃ f : V₁ ≃ₗ[ℂ] V₂, ∀ (φ : S) (v : V₁), f (H₁ φ v) = H₂ φ (f v) := by
  set Z := hSpan (prodAction H₁ H₂) Γ with hZ
  have hstable : IsStable (prodAction H₁ H₂) Z := hSpan_isStable (prodAction_closed conv hc₁ hc₂) Γ
  have hK₂ := snd_eq_zero_of_mem_hSpan conv hc₁ hc₂ hirr₂ hε₁ hε₂ hg h₁
  have hK₁ := fst_eq_zero_of_mem_hSpan conv hc₁ hc₂ hirr₁ hε₁ hε₂ hg h₁
  have hfst := map_fst_hSpan_eq_top conv hc₁ hc₂ hirr₁ hε₁ hε₂ hg h₁
  have hsnd := map_snd_hSpan_eq_top conv hc₁ hc₂ hirr₂ hε₁ hε₂ hg h₁

  let p₁ : Z →ₗ[ℂ] V₁ := (LinearMap.fst ℂ V₁ V₂) ∘ₗ Z.subtype
  let p₂ : Z →ₗ[ℂ] V₂ := (LinearMap.snd ℂ V₁ V₂) ∘ₗ Z.subtype
  have hp₁ : Function.Bijective p₁ := by
    constructor
    · intro w w' hww'
      have hd : ((w - w' : Z) : V₁ × V₂).1 = 0 := by
        change (w : V₁ × V₂).1 - (w' : V₁ × V₂).1 = 0
        exact sub_eq_zero.mpr hww'
      have hmem : ((0 : V₁), ((w - w' : Z) : V₁ × V₂).2) ∈ Z := by
        have he : ((w - w' : Z) : V₁ × V₂) = ((0 : V₁), ((w - w' : Z) : V₁ × V₂).2) :=
          Prod.ext hd rfl
        rw [← he]
        exact (w - w').2
      have h2 := hK₂ _ hmem
      have hzero : ((w - w' : Z) : V₁ × V₂) = 0 := Prod.ext hd h2
      exact sub_eq_zero.mp (Subtype.ext hzero)
    · intro x
      have hx : x ∈ Z.map (LinearMap.fst ℂ V₁ V₂) := by
        rw [hfst]
        exact Submodule.mem_top
      obtain ⟨z, hz, hzx⟩ := hx
      exact ⟨⟨z, hz⟩, hzx⟩
  have hp₂ : Function.Bijective p₂ := by
    constructor
    · intro w w' hww'
      have hd : ((w - w' : Z) : V₁ × V₂).2 = 0 := by
        change (w : V₁ × V₂).2 - (w' : V₁ × V₂).2 = 0
        exact sub_eq_zero.mpr hww'
      have hmem : (((w - w' : Z) : V₁ × V₂).1, (0 : V₂)) ∈ Z := by
        have he : ((w - w' : Z) : V₁ × V₂) = (((w - w' : Z) : V₁ × V₂).1, (0 : V₂)) :=
          Prod.ext rfl hd
        rw [← he]
        exact (w - w').2
      have h1 := hK₁ _ hmem
      have hzero : ((w - w' : Z) : V₁ × V₂) = 0 := Prod.ext h1 hd
      exact sub_eq_zero.mp (Subtype.ext hzero)
    · intro y
      have hy : y ∈ Z.map (LinearMap.snd ℂ V₁ V₂) := by
        rw [hsnd]
        exact Submodule.mem_top
      obtain ⟨z, hz, hzy⟩ := hy
      exact ⟨⟨z, hz⟩, hzy⟩
  let e₁ : Z ≃ₗ[ℂ] V₁ := LinearEquiv.ofBijective p₁ hp₁
  let e₂ : Z ≃ₗ[ℂ] V₂ := LinearEquiv.ofBijective p₂ hp₂
  refine ⟨e₁.symm.trans e₂, fun φ x => ?_⟩

  set w : Z := e₁.symm x with hw
  have hwx : ((w : V₁ × V₂)).1 = x := by
    have h : e₁ w = x := by
      rw [hw]
      exact e₁.apply_symm_apply x
    exact h
  let w' : Z := ⟨prodAction H₁ H₂ φ (w : V₁ × V₂), hstable φ _ w.2⟩
  have hw' : e₁.symm (H₁ φ x) = w' := by
    rw [LinearEquiv.symm_apply_eq]
    show H₁ φ x = (prodAction H₁ H₂ φ (w : V₁ × V₂)).1
    rw [prodAction_apply, hwx]
  show e₂ (e₁.symm (H₁ φ x)) = H₂ φ (e₂ (e₁.symm x))
  rw [hw', ← hw]
  show (prodAction H₁ H₂ φ (w : V₁ × V₂)).2 = H₂ φ (w : V₁ × V₂).2
  rw [prodAction_apply]

end Graph
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end GraphLemma
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section LevelGraphOfTrace

namespace Character

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  {S : Type*} [AddCommGroup S] [Module ℂ S]

section Corestrict

variable {A B : Module.End ℂ V₁} {U : Submodule ℂ V₁}

private theorem corestrict_mul (hA : ∀ x, A x ∈ U) (hB : ∀ x, B x ∈ U) :
    corestrict (A * B) U (fun x => hA (B x)) = corestrict A U hA * corestrict B U hB := by
  ext x
  rfl

private theorem corestrict_congr (h : A = B) (hA : ∀ x, A x ∈ U) (hB : ∀ x, B x ∈ U) :
    corestrict A U hA = corestrict B U hB := by
  subst h
  rfl

end Corestrict
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section LevelOp

variable (H : S →ₗ[ℂ] Module.End ℂ V₁) (ε : S)

private theorem levelOp_mem (φ : S) (x : V₁) : (H ε * H φ * H ε) x ∈ LinearMap.range (H ε) :=
  ⟨H φ (H ε x), rfl⟩

private def levelOp (φ : S) : Module.End ℂ (LinearMap.range (H ε)) :=
  corestrict (H ε * H φ * H ε) (LinearMap.range (H ε)) (levelOp_mem H ε φ)

private theorem levelOp_apply_coe (φ : S) (x : LinearMap.range (H ε)) :
    (levelOp H ε φ x : V₁) = H ε (H φ (H ε x)) :=
  rfl

variable {H ε}

private theorem levelOp_mul (hε : IsIdempotentElem (H ε)) (conv : S → S → S)
    (hc : ∀ φ ψ, H (conv φ ψ) = H φ * H ψ) (φ ψ : S) :
    levelOp H ε φ * levelOp H ε ψ = levelOp H ε (conv φ (conv ε ψ)) := by
  unfold levelOp
  rw [← corestrict_mul]
  apply corestrict_congr
  rw [hc, hc]
  simp only [mul_assoc]
  rw [← mul_assoc (H ε) (H ε), hε.eq]

private theorem levelOp_level (hε : IsIdempotentElem (H ε)) : levelOp H ε ε = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hx : H ε (x : V₁) = x := apply_eq_self_of_mem_range hε x.2
  show H ε (H ε (H ε (x : V₁))) = x
  rw [hx, hx, hx]

private theorem isIrreducible_of_forall_exists_eq_levelOp {G : Type*} [Monoid G]
    (ρ : Representation ℂ G (LinearMap.range (H ε)))
    (hρ : ∀ φ : S, ∃ g : G, ρ g = levelOp H ε φ) (hconv : ∀ φ ψ : S, ∃ χ : S, H φ * H ψ = H χ)
    (hirr : IsIrreducible H) (hε : IsIdempotentElem (H ε)) (hne : LinearMap.range (H ε) ≠ ⊥) :
    ρ.IsIrreducible where
  exists_pair_ne := by
    haveI : Nontrivial (LinearMap.range (H ε)) := Submodule.nontrivial_iff_ne_bot.mpr hne
    exact ⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
  eq_bot_or_eq_top σ := by
    set M : Submodule ℂ V₁ := σ.toSubmodule.map (LinearMap.range (H ε)).subtype with hMdef
    have hM : M ≤ LinearMap.range (H ε) := Submodule.map_subtype_le _ _
    have hst : IsLevelStable H ε M := by
      intro φ m hm
      obtain ⟨n, hn, rfl⟩ := Submodule.mem_map.mp hm
      obtain ⟨g, hg⟩ := hρ φ
      refine Submodule.mem_map.mpr ⟨ρ g n, σ.apply_mem_toSubmodule g hn, ?_⟩
      rw [hg]
      rfl
    by_cases hM0 : M = ⊥
    · left
      apply Subrepresentation.toSubmodule_injective
      apply eq_bot_iff.mpr
      intro n hn
      apply (Submodule.mem_bot ℂ).mpr
      apply Subtype.ext
      have hmem : (n : V₁) ∈ M := Submodule.mem_map_of_mem hn
      rw [hM0] at hmem
      exact (Submodule.mem_bot ℂ).mp hmem
    · right
      apply Subrepresentation.toSubmodule_injective
      apply eq_top_iff.mpr
      intro w _
      have hw : (w : V₁) ∈ M := by
        rw [eq_range_of_isLevelStable hconv hirr hε hM hst hM0]
        exact w.2
      obtain ⟨n, hn, hnw⟩ := Submodule.mem_map.mp hw
      have hnw' : n = w := Subtype.ext hnw
      rw [← hnw']
      exact hn

end LevelOp
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section LevelMonoid

variable {H₁ : S →ₗ[ℂ] Module.End ℂ V₁} {H₂ : S →ₗ[ℂ] Module.End ℂ V₂} {ε : S}
  (hε₁ : IsIdempotentElem (H₁ ε)) (hε₂ : IsIdempotentElem (H₂ ε)) (conv : S → S → S)
  (hc₁ : ∀ φ ψ, H₁ (conv φ ψ) = H₁ φ * H₁ ψ) (hc₂ : ∀ φ ψ, H₂ (conv φ ψ) = H₂ φ * H₂ ψ)

private def levelMonoid :
    Submonoid (Module.End ℂ (LinearMap.range (H₁ ε)) × Module.End ℂ (LinearMap.range (H₂ ε))) where
  carrier := Set.range fun φ : S => (levelOp H₁ ε φ, levelOp H₂ ε φ)
  mul_mem' := by
    rintro _ _ ⟨φ, rfl⟩ ⟨ψ, rfl⟩
    exact ⟨conv φ (conv ε ψ), Prod.ext (levelOp_mul hε₁ conv hc₁ φ ψ).symm
      (levelOp_mul hε₂ conv hc₂ φ ψ).symm⟩
  one_mem' := ⟨ε, Prod.ext (levelOp_level hε₁) (levelOp_level hε₂)⟩

private def levelElem (φ : S) : levelMonoid hε₁ hε₂ conv hc₁ hc₂ :=
  ⟨(levelOp H₁ ε φ, levelOp H₂ ε φ), ⟨φ, rfl⟩⟩

private def levelRep₁ : Representation ℂ (levelMonoid hε₁ hε₂ conv hc₁ hc₂) (LinearMap.range (H₁ ε)) :=
  (MonoidHom.fst _ _).comp (levelMonoid hε₁ hε₂ conv hc₁ hc₂).subtype

private def levelRep₂ : Representation ℂ (levelMonoid hε₁ hε₂ conv hc₁ hc₂) (LinearMap.range (H₂ ε)) :=
  (MonoidHom.snd _ _).comp (levelMonoid hε₁ hε₂ conv hc₁ hc₂).subtype

private theorem levelRep₁_levelElem (φ : S) :
    levelRep₁ hε₁ hε₂ conv hc₁ hc₂ (levelElem hε₁ hε₂ conv hc₁ hc₂ φ) = levelOp H₁ ε φ :=
  rfl

private theorem levelRep₂_levelElem (φ : S) :
    levelRep₂ hε₁ hε₂ conv hc₁ hc₂ (levelElem hε₁ hε₂ conv hc₁ hc₂ φ) = levelOp H₂ ε φ :=
  rfl

private theorem trace_levelRep
    (htr : ∀ φ : S, LinearMap.trace ℂ (LinearMap.range (H₁ ε)) (levelOp H₁ ε φ) =
      LinearMap.trace ℂ (LinearMap.range (H₂ ε)) (levelOp H₂ ε φ))
    (g : levelMonoid hε₁ hε₂ conv hc₁ hc₂) :
    LinearMap.trace ℂ (LinearMap.range (H₁ ε)) (levelRep₁ hε₁ hε₂ conv hc₁ hc₂ g) =
      LinearMap.trace ℂ (LinearMap.range (H₂ ε)) (levelRep₂ hε₁ hε₂ conv hc₁ hc₂ g) := by
  obtain ⟨φ, hφ⟩ := g.2
  have h1 : g.1.1 = levelOp H₁ ε φ := congrArg Prod.fst hφ.symm
  have h2 : g.1.2 = levelOp H₂ ε φ := congrArg Prod.snd hφ.symm
  show LinearMap.trace ℂ _ g.1.1 = LinearMap.trace ℂ _ g.1.2
  rw [h1, h2]
  exact htr φ

include hε₁ hε₂ in

private theorem range_ne_bot_of_trace_eq [FiniteDimensional ℂ (LinearMap.range (H₁ ε))]
    [FiniteDimensional ℂ (LinearMap.range (H₂ ε))]
    (htr : ∀ φ : S, LinearMap.trace ℂ (LinearMap.range (H₁ ε)) (levelOp H₁ ε φ) =
      LinearMap.trace ℂ (LinearMap.range (H₂ ε)) (levelOp H₂ ε φ))
    (h₁ : LinearMap.range (H₁ ε) ≠ ⊥) : LinearMap.range (H₂ ε) ≠ ⊥ := by
  have h := htr ε
  rw [levelOp_level hε₁, levelOp_level hε₂, LinearMap.trace_one, LinearMap.trace_one] at h
  have hdim := Nat.cast_inj.mp h
  intro h₂
  apply h₁
  apply Submodule.finrank_eq_zero.mp
  rw [hdim]
  exact Submodule.finrank_eq_zero.mpr h₂

end LevelMonoid
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section Graph

variable {H₁ : S →ₗ[ℂ] Module.End ℂ V₁} {H₂ : S →ₗ[ℂ] Module.End ℂ V₂} {ε : S}

private def graphOfEquiv (e : LinearMap.range (H₁ ε) ≃ₗ[ℂ] LinearMap.range (H₂ ε)) : Submodule ℂ (V₁ × V₂) :=
  LinearMap.range ((LinearMap.range (H₁ ε)).subtype.prod
    ((LinearMap.range (H₂ ε)).subtype ∘ₗ (e : LinearMap.range (H₁ ε) →ₗ[ℂ] LinearMap.range (H₂ ε))))

private theorem mem_graphOfEquiv {e : LinearMap.range (H₁ ε) ≃ₗ[ℂ] LinearMap.range (H₂ ε)} {p : V₁ × V₂} :
    p ∈ graphOfEquiv e ↔ ∃ w : LinearMap.range (H₁ ε), ((w : V₁), ((e w : LinearMap.range (H₂ ε)) : V₂)) = p :=
  LinearMap.mem_range

private theorem isLevelGraph_graphOfEquiv (e : LinearMap.range (H₁ ε) ≃ₗ[ℂ] LinearMap.range (H₂ ε))
    (he : ∀ (φ : S) (w : LinearMap.range (H₁ ε)), e (levelOp H₁ ε φ w) = levelOp H₂ ε φ (e w)) :
    IsLevelGraph (H₁ := H₁) (H₂ := H₂) ε (graphOfEquiv e) where
  le_prod := by
    intro p hp
    obtain ⟨w, rfl⟩ := mem_graphOfEquiv.mp hp
    exact Submodule.mem_prod.mpr ⟨w.2, (e w).2⟩
  levelStable := by
    intro φ p hp
    obtain ⟨w, rfl⟩ := mem_graphOfEquiv.mp hp
    refine mem_graphOfEquiv.mpr ⟨levelOp H₁ ε φ w, ?_⟩
    rw [he]
    rfl
  map_fst := by
    apply le_antisymm
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨w, rfl⟩ := mem_graphOfEquiv.mp hp
      exact w.2
    · intro v hv
      exact Submodule.mem_map.mpr ⟨((v : V₁), ((e ⟨v, hv⟩ : LinearMap.range (H₂ ε)) : V₂)),
        mem_graphOfEquiv.mpr ⟨⟨v, hv⟩, rfl⟩, rfl⟩
  map_snd := by
    apply le_antisymm
    · intro y hy
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
      obtain ⟨w, rfl⟩ := mem_graphOfEquiv.mp hp
      exact (e w).2
    · intro y hy
      exact Submodule.mem_map.mpr ⟨(((e.symm ⟨y, hy⟩ : LinearMap.range (H₁ ε)) : V₁),
        ((e (e.symm ⟨y, hy⟩) : LinearMap.range (H₂ ε)) : V₂)),
        mem_graphOfEquiv.mpr ⟨e.symm ⟨y, hy⟩, rfl⟩, congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)⟩
  snd_eq_zero := by
    intro y hy
    obtain ⟨w, hw⟩ := mem_graphOfEquiv.mp hy
    have hw1 : (w : V₁) = 0 := congrArg Prod.fst hw
    have hw2 : ((e w : LinearMap.range (H₂ ε)) : V₂) = y := congrArg Prod.snd hw
    have hw0 : w = 0 := Subtype.ext hw1
    rw [← hw2, hw0, map_zero]
    rfl
  fst_eq_zero := by
    intro x hx
    obtain ⟨w, hw⟩ := mem_graphOfEquiv.mp hx
    have hw1 : (w : V₁) = x := congrArg Prod.fst hw
    have hw2 : ((e w : LinearMap.range (H₂ ε)) : V₂) = 0 := congrArg Prod.snd hw
    have hew : e w = 0 := Subtype.ext hw2
    have hw0 : w = 0 := e.map_eq_zero_iff.mp hew
    rw [← hw1, hw0]
    rfl

end Graph
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section Head

variable {H₁ : S →ₗ[ℂ] Module.End ℂ V₁} {H₂ : S →ₗ[ℂ] Module.End ℂ V₂} {ε : S}

private theorem exists_isLevelGraph_of_forall_trace_eq (conv : S → S → S)
    (hc₁ : ∀ φ ψ, H₁ (conv φ ψ) = H₁ φ * H₁ ψ) (hc₂ : ∀ φ ψ, H₂ (conv φ ψ) = H₂ φ * H₂ ψ)
    (hirr₁ : IsIrreducible H₁) (hirr₂ : IsIrreducible H₂)
    (hε₁ : IsIdempotentElem (H₁ ε)) (hε₂ : IsIdempotentElem (H₂ ε))
    [FiniteDimensional ℂ (LinearMap.range (H₁ ε))] [FiniteDimensional ℂ (LinearMap.range (H₂ ε))]
    (h₁ : LinearMap.range (H₁ ε) ≠ ⊥)
    (htr : ∀ φ : S, LinearMap.trace ℂ (LinearMap.range (H₁ ε)) (levelOp H₁ ε φ) =
      LinearMap.trace ℂ (LinearMap.range (H₂ ε)) (levelOp H₂ ε φ)) :
    ∃ Γ : Submodule ℂ (V₁ × V₂), IsLevelGraph (H₁ := H₁) (H₂ := H₂) ε Γ := by
  have hconv₁ : ∀ φ ψ : S, ∃ χ : S, H₁ φ * H₁ ψ = H₁ χ := fun φ ψ => ⟨conv φ ψ, (hc₁ φ ψ).symm⟩
  have hconv₂ : ∀ φ ψ : S, ∃ χ : S, H₂ φ * H₂ ψ = H₂ χ := fun φ ψ => ⟨conv φ ψ, (hc₂ φ ψ).symm⟩
  have h₂ : LinearMap.range (H₂ ε) ≠ ⊥ := range_ne_bot_of_trace_eq hε₁ hε₂ htr h₁
  haveI : (levelRep₁ hε₁ hε₂ conv hc₁ hc₂).IsIrreducible :=
    isIrreducible_of_forall_exists_eq_levelOp _ (fun φ => ⟨levelElem hε₁ hε₂ conv hc₁ hc₂ φ, rfl⟩)
      hconv₁ hirr₁ hε₁ h₁
  haveI : (levelRep₂ hε₁ hε₂ conv hc₁ hc₂).IsIrreducible :=
    isIrreducible_of_forall_exists_eq_levelOp _ (fun φ => ⟨levelElem hε₁ hε₂ conv hc₁ hc₂ φ, rfl⟩)
      hconv₂ hirr₂ hε₂ h₂
  obtain ⟨e, he⟩ := BrauerNesbitt.case_irreducible_irreducible (levelRep₁ hε₁ hε₂ conv hc₁ hc₂)
    (levelRep₂ hε₁ hε₂ conv hc₁ hc₂) (trace_levelRep hε₁ hε₂ conv hc₁ hc₂ htr)
  exact ⟨graphOfEquiv e, isLevelGraph_graphOfEquiv e fun φ w => he (levelElem hε₁ hε₂ conv hc₁ hc₂ φ) w⟩

end Head
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end LevelGraphOfTrace
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section CharactersDetermine

namespace Character

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  {S : Type*} [AddCommGroup S] [Module ℂ S] {ι : Type*}

section OneSide

variable {H : S →ₗ[ℂ] Module.End ℂ V₁} {e : ι → S}

private theorem map_conv_level (conv : S → S → S) (hc : ∀ φ ψ, H (conv φ ψ) = H φ * H ψ) (i : ι) (φ : S) :
    H (conv (e i) (conv φ (e i))) = H (e i) * H φ * H (e i) := by
  rw [hc, hc, mul_assoc]

private theorem hasLevel_conv (conv : S → S → S) (hc : ∀ φ ψ, H (conv φ ψ) = H φ * H ψ) {i : ι}
    (hidem : IsIdempotentElem (H (e i))) (φ : S) : HasLevel H e (conv (e i) (conv φ (e i))) i := by
  unfold HasLevel
  rw [map_conv_level conv hc i φ]
  simp only [mul_assoc]
  rw [hidem.eq, ← mul_assoc (H (e i)) (H (e i)), hidem.eq]

private theorem trace_levelOp_eq_character (L : IsLevelFamily H e) (conv : S → S → S)
    (hc : ∀ φ ψ, H (conv φ ψ) = H φ * H ψ) (i : ι) (φ : S) :
    LinearMap.trace ℂ (LinearMap.range (H (e i))) (levelOp H (e i) φ) =
      character L (conv (e i) (conv φ (e i))) := by
  rw [character_eq_rankTrace L (hasLevel_conv conv hc (L.idem i) φ)]
  unfold rankTrace levelOp
  exact congrArg (LinearMap.trace ℂ _) (corestrict_congr (map_conv_level conv hc i φ).symm _ _)

end OneSide
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section Head

variable {H₁ : S →ₗ[ℂ] Module.End ℂ V₁} {H₂ : S →ₗ[ℂ] Module.End ℂ V₂} {e : ι → S}

private theorem exists_equiv_of_character_eq (L₁ : IsLevelFamily H₁ e) (L₂ : IsLevelFamily H₂ e)
    (conv : S → S → S) (hc₁ : ∀ φ ψ, H₁ (conv φ ψ) = H₁ φ * H₁ ψ)
    (hc₂ : ∀ φ ψ, H₂ (conv φ ψ) = H₂ φ * H₂ ψ) (hirr₁ : IsIrreducible H₁) (hirr₂ : IsIrreducible H₂)
    {i : ι} (h₁ : LinearMap.range (H₁ (e i)) ≠ ⊥) (hchar : character L₁ = character L₂) :
    ∃ f : V₁ ≃ₗ[ℂ] V₂, ∀ (φ : S) (v : V₁), f (H₁ φ v) = H₂ φ (f v) := by
  haveI := L₁.finite i
  haveI := L₂.finite i
  have htr : ∀ φ : S, LinearMap.trace ℂ (LinearMap.range (H₁ (e i))) (levelOp H₁ (e i) φ) =
      LinearMap.trace ℂ (LinearMap.range (H₂ (e i))) (levelOp H₂ (e i) φ) := by
    intro φ
    rw [trace_levelOp_eq_character L₁ conv hc₁ i φ, trace_levelOp_eq_character L₂ conv hc₂ i φ, hchar]
  obtain ⟨Γ, hΓ⟩ := exists_isLevelGraph_of_forall_trace_eq conv hc₁ hc₂ hirr₁ hirr₂ (L₁.idem i)
    (L₂.idem i) h₁ htr
  exact exists_equiv_of_isLevelGraph conv hc₁ hc₂ hirr₁ hirr₂ (L₁.idem i) (L₂.idem i) hΓ h₁

end Head
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end CharactersDetermine
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section CharacterConvComm

namespace Character

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Type*} [AddCommGroup S] [Module ℂ S]
  {ι : Type*} {H : S →ₗ[ℂ] Module.End ℂ V} {e : ι → S}

private theorem HasLevel.level_mul {φ : S} {i : ι} (h : HasLevel H e φ i) (hp : IsIdempotentElem (H (e i))) :
    H (e i) * H φ = H φ := by
  conv_lhs => rw [h]
  rw [← mul_assoc, ← mul_assoc, hp.eq]
  exact h.symm

private theorem HasLevel.conv {conv : S → S → S} {φ ψ : S} {i : ι} (hφ : HasLevel H e φ i)
    (hc : ∀ φ ψ, H (conv φ ψ) = H φ * H ψ) (hp : IsIdempotentElem (H (e i)))
    (hψ : HasLevel H e ψ i) : HasLevel H e (conv φ ψ) i := by
  have hψ' : H ψ * H (e i) = H ψ := by
    conv_lhs => rw [hψ]
    rw [mul_assoc, hp.eq]
    exact hψ.symm
  unfold HasLevel
  rw [hc, ← mul_assoc, hφ.level_mul hp, mul_assoc, hψ']

private theorem character_conv_comm (L : IsLevelFamily H e) {conv : S → S → S}
    (hc : ∀ φ ψ, H (conv φ ψ) = H φ * H ψ) (φ ψ : S) :
    character L (conv φ ψ) = character L (conv ψ φ) := by
  obtain ⟨i, hφ, hψ⟩ := L.exists_common_level φ ψ
  rw [character_eq_rankTrace L (hφ.conv hc (L.idem i) hψ), character_eq_rankTrace L (hψ.conv hc (L.idem i) hφ)]
  unfold rankTrace
  haveI := L.finite i
  have h₁ : corestrict (H (conv φ ψ)) (LinearMap.range (H (e i))) (hφ.conv hc (L.idem i) hψ).apply_mem_range =
      corestrict (H φ) _ hφ.apply_mem_range * corestrict (H ψ) _ hψ.apply_mem_range :=
    (corestrict_congr (hc φ ψ) _ _).trans (corestrict_mul _ _)
  have h₂ : corestrict (H (conv ψ φ)) (LinearMap.range (H (e i))) (hψ.conv hc (L.idem i) hφ).apply_mem_range =
      corestrict (H ψ) _ hψ.apply_mem_range * corestrict (H φ) _ hφ.apply_mem_range :=
    (corestrict_congr (hc ψ φ) _ _).trans (corestrict_mul _ _)
  rw [h₁, h₂, LinearMap.trace_mul_comm]

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end CharacterConvComm
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section CharacterConjugation

namespace Character

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Type*} [AddCommGroup S] [Module ℂ S]
  {ι : Type*} {H : S →ₗ[ℂ] Module.End ℂ V} {e : ι → S}

private theorem character_eq_of_map_eq (L : IsLevelFamily H e) {φ ψ : S} (h : H φ = H ψ) :
    character L φ = character L ψ := by
  obtain ⟨i, hi⟩ := L.exhaustive φ
  have hψ : HasLevel H e ψ i := by
    unfold HasLevel at hi ⊢
    rw [← h]
    exact hi
  rw [character_eq_rankTrace L hi, character_eq_rankTrace L hψ]
  unfold rankTrace
  exact congrArg (LinearMap.trace ℂ _) (corestrict_congr h _ _)

private theorem smul_character_eq_of_conv_eq_smul (L : IsLevelFamily H e) {conv : S → S → S}
    (hc : ∀ φ ψ, H (conv φ ψ) = H φ * H ψ) {a b f f' : S} {c₁ c₂ : ℂ}
    (h₁ : conv a (conv f b) = c₁ • f') (h₂ : conv f (conv b a) = c₂ • f) :
    c₁ • character L f' = c₂ • character L f := by
  rw [← map_smul (character L) c₁ f', ← h₁, ← map_smul (character L) c₂ f, ← h₂,
    character_conv_comm L hc a (conv f b)]
  apply character_eq_of_map_eq L
  simp only [hc, mul_assoc]

private theorem character_eq_of_conv_eq_smul (L : IsLevelFamily H e) {conv : S → S → S}
    (hc : ∀ φ ψ, H (conv φ ψ) = H φ * H ψ) {a b f f' : S} {c : ℂ} (hc0 : c ≠ 0)
    (h₁ : conv a (conv f b) = c • f') (h₂ : conv f (conv b a) = c • f) :
    character L f' = character L f := by
  have h := smul_character_eq_of_conv_eq_smul L hc h₁ h₂
  rw [smul_eq_mul, smul_eq_mul] at h
  exact mul_left_cancel₀ hc0 h

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end CharacterConjugation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section CharacterConjTest

open MeasureTheory Topology

namespace Character

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

private noncomputable def testConv (μ : Measure G) (S : Submodule ℂ (G → ℂ))
    (hS : ∀ f ∈ S, ∀ h ∈ S, MulConvolution.mulConv μ f h ∈ S) (φ ψ : S) : S :=
  ⟨MulConvolution.mulConv μ φ ψ, hS φ φ.2 ψ ψ.2⟩

variable [IsTopologicalGroup G] [BorelSpace G] {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*}

private theorem character_conj_eq (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (hKb : ∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧
      (K : Set G) ⊆ U)
    {S : Submodule ℂ (G → ℂ)} (hS₁ : ∀ f ∈ S, IsLocallyConstant f)
    (hS₂ : ∀ f ∈ S, HasCompactSupport f)
    (hS₃ : ∀ A : Set G, IsCompact A → IsOpen A → A.indicator (1 : G → ℂ) ∈ S)
    (hS₄ : ∀ f ∈ S, ∀ h ∈ S, MulConvolution.mulConv μ f h ∈ S)
    {H : S →ₗ[ℂ] Module.End ℂ V} {e : ι → S} (L : IsLevelFamily H e)
    (hc : ∀ φ ψ, H (testConv μ S hS₄ φ ψ) = H φ * H ψ) (f : S) (g : G)
    (hfg : (fun x => (f : G → ℂ) (g⁻¹ * x * g)) ∈ S) :
    character L (⟨fun x => (f : G → ℂ) (g⁻¹ * x * g), hfg⟩ : S) = character L f := by
  obtain ⟨K, hKc, hKo, hKK⟩ := HomogeneousCells.exists_compact_open_subgroup_forall_apply_eq hKb
    (f : G → ℂ) (hS₁ f f.2) (hS₂ f f.2) g
  have hA : IsCompact {y : G | y * g⁻¹ ∈ K} := (Homeomorph.mulRight g⁻¹).isCompact_preimage.mpr hKc
  have hA' : IsOpen {y : G | y * g⁻¹ ∈ K} := (Homeomorph.mulRight g⁻¹).isOpen_preimage.mpr hKo
  have hB : IsCompact {y : G | g * y ∈ K} := (Homeomorph.mulLeft g).isCompact_preimage.mpr hKc
  have hB' : IsOpen {y : G | g * y ∈ K} := (Homeomorph.mulLeft g).isOpen_preimage.mpr hKo
  have hμ : μ {y : G | y * g⁻¹ ∈ K} = μ (K : Set G) := measure_preimage_mul_right μ g⁻¹ (K : Set G)
  have hreal : μ.real (K : Set G) = μ.real {y : G | y * g⁻¹ ∈ K} := (congrArg ENNReal.toReal hμ).symm
  have h0 : μ.real {y : G | y * g⁻¹ ∈ K} ≠ 0 := by
    rw [← hreal]
    exact (measureReal_ne_zero_iff hKc.measure_lt_top.ne).mpr (hKo.measure_ne_zero μ ⟨1, K.one_mem⟩)
  have hl : ∀ k ∈ K, ∀ x, (f : G → ℂ) (g⁻¹ * k * g * x) = (f : G → ℂ) x :=
    fun k hk x => ((hKK k hk).2.1 x).1
  have hr : ∀ k ∈ K, ∀ x, (f : G → ℂ) (x * (g⁻¹ * k * g)) = (f : G → ℂ) x :=
    fun k hk x => ((hKK k hk).2.1 x).2
  have h₂ := MulConvolution.mulConv_mulConv_indicator μ K hKo g (f : G → ℂ) hr
  rw [hreal, ← sq] at h₂
  exact character_eq_of_conv_eq_smul L hc (a := ⟨_, hS₃ _ hA hA'⟩) (b := ⟨_, hS₃ _ hB hB'⟩)
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr h0))
    (Subtype.ext (MulConvolution.indicator_mulConv_mulConv_indicator μ K hKo g (f : G → ℂ) hl hr))
    (Subtype.ext h₂)

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end CharacterConjTest
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section CharacterConjTestFunctions

open MeasureTheory Topology InvariantFunctional

namespace Character

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem mulConv_mem_testSubmodule [T2Space G] [MeasurableSpace G] (μ : Measure G)
    (hKb : ∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧
      (K : Set G) ⊆ U)
    {f h : G → ℂ} (hf : f ∈ testSubmodule G ℂ) (hh : h ∈ testSubmodule G ℂ) :
    MulConvolution.mulConv μ f h ∈ testSubmodule G ℂ := by
  obtain ⟨-, hfc⟩ := mem_testSubmodule.mp hf
  obtain ⟨hh₁, hhc⟩ := mem_testSubmodule.mp hh
  obtain ⟨K, -, hKo, hKK⟩ := HomogeneousCells.exists_compact_open_subgroup_forall_apply_eq hKb h hh₁ hhc 1
  refine mem_testSubmodule.mpr ⟨MulConvolution.isLocallyConstant_mulConv μ f h ?_,
    MulConvolution.hasCompactSupport_mulConv μ hfc hhc⟩
  exact ⟨(K : Set G), hKo.mem_nhds K.one_mem, fun u hu x => ((hKK u hu).1 x).2⟩

private theorem conj_mem_testSubmodule {f : G → ℂ} (hf : f ∈ testSubmodule G ℂ) (g : G) :
    (fun x => f (g⁻¹ * x * g)) ∈ testSubmodule G ℂ := by
  obtain ⟨hf₁, hfc⟩ := mem_testSubmodule.mp hf
  refine mem_testSubmodule.mpr ⟨hf₁.comp_continuous (by fun_prop : Continuous fun x : G => g⁻¹ * x * g), ?_⟩
  exact hfc.comp_homeomorph ((Homeomorph.mulLeft g⁻¹).trans (Homeomorph.mulRight g))

variable [T2Space G] [MeasurableSpace G] [BorelSpace G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ι : Type*}

private theorem character_conj_eq_testSubmodule (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (hKb : ∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧
      (K : Set G) ⊆ U)
    {H : testSubmodule G ℂ →ₗ[ℂ] Module.End ℂ V} {e : ι → testSubmodule G ℂ} (L : IsLevelFamily H e)
    (hc : ∀ φ ψ, H (testConv μ (testSubmodule G ℂ) (fun _ hf _ hh => mulConv_mem_testSubmodule μ hKb hf hh)
      φ ψ) = H φ * H ψ)
    (f : testSubmodule G ℂ) (g : G) :
    character L (⟨fun x => (f : G → ℂ) (g⁻¹ * x * g), conj_mem_testSubmodule f.2 g⟩ : testSubmodule G ℂ) =
      character L f :=
  character_conj_eq μ hKb (S := testSubmodule G ℂ) (fun _ hf => (mem_testSubmodule.mp hf).1)
    (fun _ hf => (mem_testSubmodule.mp hf).2)
    (fun _ hA hA' => indicator_mem_testSubmodule hA hA') (fun _ hf _ hh => mulConv_mem_testSubmodule μ hKb hf hh)
    L hc f g (conj_mem_testSubmodule f.2 g)

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end CharacterConjTestFunctions
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section TestConvPullbacks

open MeasureTheory InvariantFunctional

namespace Character

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G)
  (hS : ∀ f ∈ testSubmodule G ℂ, ∀ h ∈ testSubmodule G ℂ, MulConvolution.mulConv μ f h ∈ testSubmodule G ℂ)

private theorem pullback_testConv [BorelSpace G] (θ : G →* G) (hθc : Continuous θ) (hθθ : Function.Involutive θ)
    (hμ : Measure.map θ μ = μ) (φ ψ : testSubmodule G ℂ) :
    pullback ℂ θ hθc hθθ (testConv μ (testSubmodule G ℂ) hS φ ψ) =
      testConv μ (testSubmodule G ℂ) hS (pullback ℂ θ hθc hθθ φ) (pullback ℂ θ hθc hθθ ψ) :=
  Subtype.ext (MulConvolution.mulConv_comp_of_map_eq μ θ hθc hθθ hμ φ ψ).symm

private theorem pullback_inv_testConv [ContinuousInv G] [MeasurableMul G] [μ.IsMulLeftInvariant]
    (φ ψ : testSubmodule G ℂ) :
    pullback ℂ (fun g : G => g⁻¹) continuous_inv inv_involutive (testConv μ (testSubmodule G ℂ) hS φ ψ) =
      testConv μ (testSubmodule G ℂ) hS (pullback ℂ (fun g : G => g⁻¹) continuous_inv inv_involutive ψ)
        (pullback ℂ (fun g : G => g⁻¹) continuous_inv inv_involutive φ) :=
  Subtype.ext (MulConvolution.mulConv_fun_inv μ φ ψ).symm

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end TestConvPullbacks
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section InvariantPairing

namespace Contragredient

variable {G : Type*} [Group G] {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {Vt : Type*} [AddCommGroup Vt] [Module R Vt]

private def IsInvariantPairing (π : G →* Module.End R V) (πT : G →* Module.End R Vt)
    (B : V →ₗ[R] Vt →ₗ[R] R) : Prop :=
  ∀ (g : G) (v : V) (vt : Vt), B (π g v) (πT g vt) = B v vt

private def dualRep (π : G →* Module.End R V) : G →* Module.End R (Module.Dual R V) where
  toFun g := (π g⁻¹).dualMap
  map_one' := by
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro v
    simp only [inv_one, map_one, LinearMap.dualMap_apply, Module.End.one_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro v
    simp only [_root_.mul_inv_rev, map_mul, LinearMap.dualMap_apply, Module.End.mul_apply]

@[scoped simp] private theorem dualRep_apply (π : G →* Module.End R V) (g : G) (φ : Module.Dual R V)
    (v : V) : dualRep π g φ v = φ (π g⁻¹ v) :=
  LinearMap.dualMap_apply _ _ _

private theorem isInvariantPairing_dualRep (π : G →* Module.End R V) :
    IsInvariantPairing π (dualRep π) (Module.Dual.eval R V) := by
  intro g v φ
  rw [Module.Dual.eval_apply, Module.Dual.eval_apply, dualRep_apply, ← Module.End.mul_apply,
    ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem dualEval_separatingLeft {R : Type*} [Field R] {V : Type*} [AddCommGroup V]
    [Module R V] :
    ∀ v : V, (∀ φ : Module.Dual R V, Module.Dual.eval R V v φ = 0) → v = 0 := by
  intro v hv
  refine (Module.forall_dual_apply_eq_zero_iff R v).mp ?_
  intro φ
  have h := hv φ
  rwa [Module.Dual.eval_apply] at h

private theorem dualEval_separatingRight :
    ∀ φ : Module.Dual R V, (∀ v : V, Module.Dual.eval R V v φ = 0) → φ = 0 := by
  intro φ hφ
  apply LinearMap.ext
  intro v
  have h := hφ v
  rwa [Module.Dual.eval_apply] at h

section PairingOfMap

variable {W : Type*} [AddCommGroup W] [Module R W]

private def pairingOf (f : W →ₗ[R] Module.Dual R V) : V →ₗ[R] W →ₗ[R] R :=
  f.flip

private theorem pairingOf_apply (f : W →ₗ[R] Module.Dual R V) (x : V) (y : W) :
    pairingOf f x y = f y x :=
  rfl

private theorem pairingOf_apply_apply (π : G →* Module.End R V) (π' : G →* Module.End R W)
    (f : W →ₗ[R] Module.Dual R V) (hf : ∀ (g : G) (y : W), f (π' g y) = dualRep π g (f y))
    (g : G) (x : V) (y : W) : pairingOf f (π g x) (π' g y) = pairingOf f x y := by
  rw [pairingOf_apply, pairingOf_apply, hf, dualRep_apply, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel, map_one, Module.End.one_apply]

private theorem eq_zero_of_forall_pairingOf_eq_zero {f : W →ₗ[R] Module.Dual R V}
    (hf : Function.Injective f) (y : W) (hy : ∀ x : V, pairingOf f x y = 0) : y = 0 := by
  apply hf
  rw [map_zero]
  apply LinearMap.ext
  intro x
  exact hy x

private theorem exists_forall_eq_pairingOf {f : W →ₗ[R] Module.Dual R V} {D : Submodule R (Module.Dual R V)}
    (hD : D ≤ LinearMap.range f) (L : Module.Dual R V) (hL : L ∈ D) :
    ∃ y : W, ∀ x : V, L x = pairingOf f x y := by
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp (hD hL)
  exact ⟨y, fun x => rfl⟩

end PairingOfMap
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

end Contragredient
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

end InvariantPairing
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

section DualLevels

namespace Character

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Type*} [AddCommGroup S] [Module ℂ S]
  {ι : Type*}

section Absorption

variable {H : S →ₗ[ℂ] Module.End ℂ V} {e : ι → S}

private theorem HasLevel.mul_level {φ : S} {i : ι} (h : HasLevel H e φ i) (hp : IsIdempotentElem (H (e i))) :
    H φ * H (e i) = H φ := by
  conv_lhs => rw [h]
  rw [mul_assoc, hp.eq]
  exact h.symm

private theorem level_apply_of_mem_range (L : IsLevelFamily H e) (i : ι) {y : V}
    (hy : y ∈ LinearMap.range (H (e i))) : H (e i) y = y := by
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy
  exact LinearMap.congr_fun (L.idem i).eq z

private theorem comp_eq_self_of_absorb {l : Module.Dual ℂ V} {i k : ι} (hl : l ∘ₗ H (e i) = l)
    (hik : H (e i) * H (e k) = H (e i)) : l ∘ₗ H (e k) = l := by
  rw [← hl, LinearMap.comp_assoc, ← Module.End.mul_eq_comp, hik]

end Absorption
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

section DualSpace

variable (H : S →ₗ[ℂ] Module.End ℂ V) {e : ι → S} (L : IsLevelFamily H e) [Nonempty ι]

private def heckeDual : Submodule ℂ (Module.Dual ℂ V) where
  carrier := {l | ∃ i : ι, l ∘ₗ H (e i) = l}
  zero_mem' := ⟨Classical.arbitrary ι, LinearMap.zero_comp _⟩
  add_mem' := by
    rintro l m ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, ⟨_, hik⟩, ⟨_, hjk⟩⟩ := L.directed i j
    exact ⟨k, by rw [LinearMap.add_comp, comp_eq_self_of_absorb hi hik, comp_eq_self_of_absorb hj hjk]⟩
  smul_mem' := by
    rintro c l ⟨i, hi⟩
    exact ⟨i, by rw [LinearMap.smul_comp, hi]⟩

private theorem mem_heckeDual_iff {l : Module.Dual ℂ V} : l ∈ heckeDual H L ↔ ∃ i : ι, l ∘ₗ H (e i) = l :=
  Iff.rfl

private theorem dualMap_mem_heckeDual (ψ : S) (l : Module.Dual ℂ V) : (H ψ).dualMap l ∈ heckeDual H L := by
  obtain ⟨j, hj⟩ := L.exhaustive ψ
  refine (mem_heckeDual_iff H L).mpr ⟨j, ?_⟩
  rw [LinearMap.dualMap_apply', LinearMap.comp_assoc, ← Module.End.mul_eq_comp,
    hj.mul_level (L.idem j)]

private theorem comp_level_mem_heckeDual (l : Module.Dual ℂ V) (i : ι) : l ∘ₗ H (e i) ∈ heckeDual H L :=
  (mem_heckeDual_iff H L).mpr ⟨i, by rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, (L.idem i).eq]⟩

variable (inv : S →ₗ[ℂ] S)

private def heckeDualAction : S →ₗ[ℂ] Module.End ℂ (heckeDual H L) where
  toFun φ := (H (inv φ)).dualMap.restrict fun l _ => dualMap_mem_heckeDual H L (inv φ) l
  map_add' φ ψ := by
    ext
    simp
  map_smul' c φ := by
    ext
    simp

private theorem heckeDualAction_apply_coe (φ : S) (l : heckeDual H L) :
    (heckeDualAction H L inv φ l : Module.Dual ℂ V) = (l : Module.Dual ℂ V) ∘ₗ H (inv φ) :=
  rfl

variable {H L inv}

private theorem heckeDualAction_conv (conv : S → S → S) (hc : ∀ φ ψ, H (conv φ ψ) = H φ * H ψ)
    (hinv : ∀ φ ψ, inv (conv φ ψ) = conv (inv ψ) (inv φ)) (φ ψ : S) :
    heckeDualAction H L inv (conv φ ψ) = heckeDualAction H L inv φ * heckeDualAction H L inv ψ := by
  apply LinearMap.ext
  intro l
  apply Subtype.ext
  show (l : Module.Dual ℂ V) ∘ₗ H (inv (conv φ ψ)) =
    ((l : Module.Dual ℂ V) ∘ₗ H (inv ψ)) ∘ₗ H (inv φ)
  rw [hinv, hc, Module.End.mul_eq_comp, LinearMap.comp_assoc]

private theorem heckeDualAction_level_mul (hinv_e : ∀ i, inv (e i) = e i) {i k : ι}
    (hik : H (e i) * H (e k) = H (e i)) :
    heckeDualAction H L inv (e k) * heckeDualAction H L inv (e i) = heckeDualAction H L inv (e i) := by
  apply LinearMap.ext
  intro l
  apply Subtype.ext
  show ((l : Module.Dual ℂ V) ∘ₗ H (inv (e i))) ∘ₗ H (inv (e k)) =
    (l : Module.Dual ℂ V) ∘ₗ H (inv (e i))
  simp only [hinv_e]
  rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, hik]

private theorem heckeDualAction_mul_level (hinv_e : ∀ i, inv (e i) = e i) {i k : ι}
    (hki : H (e k) * H (e i) = H (e i)) :
    heckeDualAction H L inv (e i) * heckeDualAction H L inv (e k) = heckeDualAction H L inv (e i) := by
  apply LinearMap.ext
  intro l
  apply Subtype.ext
  show ((l : Module.Dual ℂ V) ∘ₗ H (inv (e k))) ∘ₗ H (inv (e i)) =
    (l : Module.Dual ℂ V) ∘ₗ H (inv (e i))
  simp only [hinv_e]
  rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, hki]

private theorem hasLevel_heckeDual (hinv_e : ∀ i, inv (e i) = e i) {φ : S} {i : ι}
    (hi : HasLevel H e (inv φ) i) : HasLevel (heckeDualAction H L inv) e φ i := by
  unfold HasLevel
  apply LinearMap.ext
  intro l
  apply Subtype.ext
  show (l : Module.Dual ℂ V) ∘ₗ H (inv φ) =
    (((l : Module.Dual ℂ V) ∘ₗ H (inv (e i))) ∘ₗ H (inv φ)) ∘ₗ H (inv (e i))
  simp only [hinv_e]
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp,
    ← mul_assoc, ← hi]

section DualLevel

variable (H L inv) (i : ι)

private def restrictLevel :
    LinearMap.range (heckeDualAction H L inv (e i)) →ₗ[ℂ] Module.Dual ℂ (LinearMap.range (H (e i))) :=
  (LinearMap.range (H (e i))).subtype.dualMap ∘ₗ (heckeDual H L).subtype ∘ₗ
    (LinearMap.range (heckeDualAction H L inv (e i))).subtype

private theorem restrictLevel_apply (m : LinearMap.range (heckeDualAction H L inv (e i)))
    (w : LinearMap.range (H (e i))) :
    restrictLevel H L inv i m w = ((m : heckeDual H L) : Module.Dual ℂ V) w :=
  rfl

variable {H L inv}

private theorem coe_comp_level_of_mem_range (hinv_e : ∀ i, inv (e i) = e i)
    (m : LinearMap.range (heckeDualAction H L inv (e i))) :
    ((m : heckeDual H L) : Module.Dual ℂ V) ∘ₗ H (e i) = ((m : heckeDual H L) : Module.Dual ℂ V) := by
  obtain ⟨n, hn⟩ := LinearMap.mem_range.mp m.2
  have habs : ((m : heckeDual H L) : Module.Dual ℂ V) =
      ((n : heckeDual H L) : Module.Dual ℂ V) ∘ₗ H (inv (e i)) := by
    rw [← hn]
    rfl
  rw [hinv_e] at habs
  rw [habs, LinearMap.comp_assoc, ← Module.End.mul_eq_comp, (L.idem i).eq]

private theorem restrictLevel_injective (hinv_e : ∀ i, inv (e i) = e i) :
    Function.Injective (restrictLevel H L inv i) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  apply Subtype.ext
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  have hv : ((m : heckeDual H L) : Module.Dual ℂ V) (H (e i) v) =
      ((m : heckeDual H L) : Module.Dual ℂ V) v :=
    LinearMap.congr_fun (coe_comp_level_of_mem_range i hinv_e m) v
  rw [← hv]
  exact LinearMap.congr_fun hm ⟨H (e i) v, LinearMap.mem_range_self _ _⟩

private theorem restrictLevel_surjective (hinv_e : ∀ i, inv (e i) = e i) :
    Function.Surjective (restrictLevel H L inv i) := by
  intro μ
  have hfix : ∀ v : V, μ ((H (e i)).rangeRestrict (H (e i) v)) = μ ((H (e i)).rangeRestrict v) := by
    intro v
    apply congrArg μ
    apply Subtype.ext
    show H (e i) (H (e i) v) = H (e i) v
    rw [← Module.End.mul_apply, (L.idem i).eq]
  have hmem : μ ∘ₗ (H (e i)).rangeRestrict ∈ heckeDual H L := by
    refine (mem_heckeDual_iff H L).mpr ⟨i, ?_⟩
    apply LinearMap.ext
    intro v
    exact hfix v
  have hrange : (⟨μ ∘ₗ (H (e i)).rangeRestrict, hmem⟩ : heckeDual H L) ∈
      LinearMap.range (heckeDualAction H L inv (e i)) := by
    refine LinearMap.mem_range.mpr ⟨⟨μ ∘ₗ (H (e i)).rangeRestrict, hmem⟩, ?_⟩
    apply Subtype.ext
    show (μ ∘ₗ (H (e i)).rangeRestrict) ∘ₗ H (inv (e i)) = μ ∘ₗ (H (e i)).rangeRestrict
    rw [hinv_e]
    apply LinearMap.ext
    intro v
    exact hfix v
  refine ⟨⟨_, hrange⟩, ?_⟩
  apply LinearMap.ext
  intro w
  show μ ((H (e i)).rangeRestrict (w : V)) = μ w
  apply congrArg μ
  apply Subtype.ext
  exact level_apply_of_mem_range L i w.2

private noncomputable def dualLevelEquiv (hinv_e : ∀ i, inv (e i) = e i) :
    LinearMap.range (heckeDualAction H L inv (e i)) ≃ₗ[ℂ] Module.Dual ℂ (LinearMap.range (H (e i))) :=
  LinearEquiv.ofBijective (restrictLevel H L inv i)
    ⟨restrictLevel_injective i hinv_e, restrictLevel_surjective i hinv_e⟩

private theorem dualLevelEquiv_apply (hinv_e : ∀ i, inv (e i) = e i)
    (m : LinearMap.range (heckeDualAction H L inv (e i))) (w : LinearMap.range (H (e i))) :
    dualLevelEquiv i hinv_e m w = ((m : heckeDual H L) : Module.Dual ℂ V) w :=
  rfl

end DualLevel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

private theorem isLevelFamily_heckeDual (hinv_e : ∀ i, inv (e i) = e i) :
    IsLevelFamily (heckeDualAction H L inv) e where
  idem i := by
    unfold IsIdempotentElem
    exact heckeDualAction_level_mul hinv_e (L.idem i).eq
  finite i := by
    haveI := L.finite i
    exact FiniteDimensional.of_injective (restrictLevel H L inv i) (restrictLevel_injective i hinv_e)
  directed i j := by
    obtain ⟨k, ⟨hki, hik⟩, ⟨hkj, hjk⟩⟩ := L.directed i j
    exact ⟨k, ⟨heckeDualAction_level_mul hinv_e hik, heckeDualAction_mul_level hinv_e hki⟩,
      ⟨heckeDualAction_level_mul hinv_e hjk, heckeDualAction_mul_level hinv_e hkj⟩⟩
  exhaustive φ := by
    obtain ⟨i, hi⟩ := L.exhaustive (inv φ)
    exact ⟨i, hasLevel_heckeDual hinv_e hi⟩

private theorem nontrivial_heckeDual (hne : ∃ i : ι, LinearMap.range (H (e i)) ≠ ⊥) :
    Nontrivial (heckeDual H L) := by
  obtain ⟨i, hi⟩ := hne
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hi
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ V, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 ((Module.forall_dual_apply_eq_zero_iff ℂ v).mp h)
  refine ⟨⟨⟨f ∘ₗ H (e i), comp_level_mem_heckeDual H L f i⟩, 0, fun h => hf ?_⟩⟩
  have h1 : (f ∘ₗ H (e i)) v = 0 := by
    have h2 := congrArg (fun x : heckeDual H L => (x : Module.Dual ℂ V) v) h
    exact h2
  rw [LinearMap.comp_apply, level_apply_of_mem_range L i hv] at h1
  exact h1

private theorem isIrreducible_heckeDual (hinv_inv : ∀ φ, inv (inv φ) = φ) (hinv_e : ∀ i, inv (e i) = e i)
    (hirr : IsIrreducible H) (hne : ∃ i : ι, LinearMap.range (H (e i)) ≠ ⊥) :
    IsIrreducible (heckeDualAction H L inv) := by
  refine ⟨nontrivial_heckeDual hne, ?_⟩
  intro N hN
  set N' : Submodule ℂ (Module.Dual ℂ V) := N.map (heckeDual H L).subtype
  have hst : IsStable H N'.dualCoannihilator := by
    intro φ v hv
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro m hm
    obtain ⟨n, hnN, rfl⟩ := Submodule.mem_map.mp hm
    have h := hv _ (Submodule.mem_map_of_mem (f := (heckeDual H L).subtype) (hN (inv φ) n hnN))
    have h3 : ((n : heckeDual H L) : Module.Dual ℂ V) (H (inv (inv φ)) v) = 0 := h
    rw [hinv_inv] at h3
    exact h3
  rcases hirr.2 _ hst with hA | hA
  · right
    apply eq_top_iff.mpr
    intro l _
    obtain ⟨i, hi⟩ := (mem_heckeDual_iff H L).mp l.2
    haveI := L.finite i
    haveI : FiniteDimensional ℂ (Module.Dual ℂ (LinearMap.range (H (e i)))) := inferInstance
    set E : Submodule ℂ V := LinearMap.range (H (e i))
    set Φ : Submodule ℂ (Module.Dual ℂ E) := N'.map E.subtype.dualMap
    haveI : FiniteDimensional ℂ Φ := FiniteDimensional.finiteDimensional_submodule Φ
    have hΦ : Φ.dualCoannihilator = ⊥ := by
      apply eq_bot_iff.mpr
      intro w hw
      rw [Submodule.mem_dualCoannihilator] at hw
      have hwA : (w : V) ∈ N'.dualCoannihilator := by
        rw [Submodule.mem_dualCoannihilator]
        intro m hm
        have h := hw _ (Submodule.mem_map_of_mem (f := E.subtype.dualMap) hm)
        rw [LinearMap.dualMap_apply] at h
        exact h
      rw [hA] at hwA
      exact (Submodule.mem_bot ℂ).mpr (Subtype.ext ((Submodule.mem_bot ℂ).mp hwA))
    have hΦtop : Φ = ⊤ := by
      have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Φ)
      rw [hΦ, Submodule.dualAnnihilator_bot] at h
      exact h.symm
    have hlΦ : E.subtype.dualMap (l : Module.Dual ℂ V) ∈ Φ := by
      rw [hΦtop]
      exact Submodule.mem_top
    obtain ⟨m, hmN', hml⟩ := Submodule.mem_map.mp hlΦ
    obtain ⟨n, hnN, rfl⟩ := Submodule.mem_map.mp hmN'
    have hlp : (l : Module.Dual ℂ V) ∘ₗ H (e i) = ((n : heckeDual H L) : Module.Dual ℂ V) ∘ₗ H (e i) := by
      apply LinearMap.ext
      intro v
      have h := LinearMap.congr_fun hml ⟨H (e i) v, LinearMap.mem_range_self _ _⟩
      rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply] at h
      exact h.symm
    have hnp : ((n : heckeDual H L) : Module.Dual ℂ V) ∘ₗ H (e i) ∈ N' := by
      have h := Submodule.mem_map_of_mem (f := (heckeDual H L).subtype) (hN (e i) n hnN)
      have h2 : ((n : heckeDual H L) : Module.Dual ℂ V) ∘ₗ H (inv (e i)) ∈ N' := h
      rw [hinv_e] at h2
      exact h2
    have hlN' : (l : Module.Dual ℂ V) ∈ N' := by
      rw [← hi, hlp]
      exact hnp
    obtain ⟨r, hrN, hrl⟩ := Submodule.mem_map.mp hlN'
    have hrl' : r = l := Subtype.ext hrl
    rw [← hrl']
    exact hrN
  · left
    apply eq_bot_iff.mpr
    intro n hn
    apply (Submodule.mem_bot ℂ).mpr
    apply Subtype.ext
    rw [Submodule.coe_zero]
    apply LinearMap.ext
    intro v
    rw [LinearMap.zero_apply]
    have hv : v ∈ N'.dualCoannihilator := by
      rw [hA]
      exact Submodule.mem_top
    rw [Submodule.mem_dualCoannihilator] at hv
    exact hv _ (Submodule.mem_map_of_mem (f := (heckeDual H L).subtype) hn)

end DualSpace
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

end DualLevels
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

section CharacterDual

namespace Character

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Type*} [AddCommGroup S] [Module ℂ S]
  {ι : Type*} {H : S →ₗ[ℂ] Module.End ℂ V} {e : ι → S} {L : IsLevelFamily H e} [Nonempty ι]
  {inv : S →ₗ[ℂ] S}

private theorem dualLevelEquiv_conj_corestrict (hinv_e : ∀ i, inv (e i) = e i) {φ : S} {i : ι}
    (hi : HasLevel H e (inv φ) i) :
    (dualLevelEquiv (L := L) i hinv_e).conj
        (corestrict (heckeDualAction H L inv φ) (LinearMap.range (heckeDualAction H L inv (e i)))
          (hasLevel_heckeDual (L := L) hinv_e hi).apply_mem_range) =
      (corestrict (H (inv φ)) (LinearMap.range (H (e i))) hi.apply_mem_range).dualMap := by
  apply LinearMap.ext
  intro μ
  obtain ⟨m, rfl⟩ := (dualLevelEquiv (L := L) i hinv_e).surjective μ
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  apply LinearMap.ext
  intro w
  rfl

private theorem character_heckeDual (hinv_e : ∀ i, inv (e i) = e i) (φ : S) :
    character (isLevelFamily_heckeDual (L := L) hinv_e) φ = character L (inv φ) := by
  obtain ⟨i, hi⟩ := L.exhaustive (inv φ)
  rw [character_eq_rankTrace (isLevelFamily_heckeDual (L := L) hinv_e) (hasLevel_heckeDual (L := L) hinv_e hi),
    character_eq_rankTrace L hi]
  unfold rankTrace
  haveI := L.finite i
  haveI := (isLevelFamily_heckeDual (L := L) hinv_e).finite i
  rw [← LinearMap.trace_conj' (M := LinearMap.range (heckeDualAction H L inv (e i)))
      (N := Module.Dual ℂ (LinearMap.range (H (e i)))) _ (dualLevelEquiv (L := L) i hinv_e),
    dualLevelEquiv_conj_corestrict hinv_e hi, LinearMap.dualMap_def, LinearMap.trace_transpose']

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

end CharacterDual
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

section SmoothPart

namespace Character

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Type*} [AddCommGroup S] [Module ℂ S] {ι : Type*}
variable {H : S →ₗ[ℂ] Module.End ℂ V} {e : ι → S}

section Level

private def pairingToLevelDual (P : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (i : ι) :
    LinearMap.range (H (e i)) →ₗ[ℂ] Module.Dual ℂ (LinearMap.range (H (e i))) :=
  (LinearMap.range (H (e i))).subtype.dualMap ∘ₗ P.flip ∘ₗ (LinearMap.range (H (e i))).subtype

private theorem pairingToLevelDual_apply (P : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (i : ι) (y w : LinearMap.range (H (e i))) :
    pairingToLevelDual (H := H) P i y w = P w y :=
  rfl

private theorem pairingToLevelDual_injective (L : IsLevelFamily H e) (P : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hadj : ∀ (i : ι) (x y : V), P (H (e i) x) y = P x (H (e i) y))
    (hsep : ∀ y : V, (∀ x : V, P x y = 0) → y = 0) (i : ι) :
    Function.Injective (pairingToLevelDual (H := H) (e := e) P i) := by
  intro y y' hyy'
  rw [← sub_eq_zero, ← map_sub] at hyy'
  rw [← sub_eq_zero]
  apply Subtype.ext
  rw [Submodule.coe_zero]
  refine hsep _ fun x => ?_
  have h := LinearMap.congr_fun hyy' ⟨H (e i) x, LinearMap.mem_range_self _ x⟩
  simp only [pairingToLevelDual_apply, LinearMap.zero_apply] at h
  rw [hadj, level_apply_of_mem_range L i (y - y').2] at h
  exact h

private theorem exists_eq_pairing_of_comp_level_eq (L : IsLevelFamily H e) (P : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hadj : ∀ (i : ι) (x y : V), P (H (e i) x) y = P x (H (e i) y))
    (hsep : ∀ y : V, (∀ x : V, P x y = 0) → y = 0) {l : Module.Dual ℂ V} {i : ι}
    (hl : l ∘ₗ H (e i) = l) : ∃ y : V, ∀ x : V, l x = P x y := by
  haveI : FiniteDimensional ℂ (LinearMap.range (H (e i))) := L.finite i
  have hsurj : Function.Surjective (pairingToLevelDual (H := H) (e := e) P i) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).mp
      (pairingToLevelDual_injective L P hadj hsep i)
  obtain ⟨y, hy⟩ := hsurj ((LinearMap.range (H (e i))).subtype.dualMap l)
  refine ⟨y, fun x => ?_⟩
  have h := LinearMap.congr_fun hy ⟨H (e i) x, LinearMap.mem_range_self _ x⟩
  simp only [pairingToLevelDual_apply, LinearMap.dualMap_apply, Submodule.subtype_apply] at h
  calc l x = l (H (e i) x) := (LinearMap.congr_fun hl x).symm
    _ = P (H (e i) x) y := h.symm
    _ = P x y := by rw [hadj, level_apply_of_mem_range L i y.2]

end Level
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

section Dual

variable [Nonempty ι]

private theorem exists_eq_pairing_of_mem_heckeDual (L : IsLevelFamily H e) (P : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hadj : ∀ (i : ι) (x y : V), P (H (e i) x) y = P x (H (e i) y))
    (hsep : ∀ y : V, (∀ x : V, P x y = 0) → y = 0) {l : Module.Dual ℂ V} (hl : l ∈ heckeDual H L) :
    ∃ y : V, ∀ x : V, l x = P x y := by
  obtain ⟨i, hi⟩ := (mem_heckeDual_iff H L).mp hl
  exact exists_eq_pairing_of_comp_level_eq L P hadj hsep hi

end Dual
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

section Smooth

variable {G : Type*} [Group G] [TopologicalSpace G]

private theorem exists_eq_pairing_of_forall_open_subgroup (π : G →* Module.End ℂ V) (L : IsLevelFamily H e)
    (hlev : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ i : ι, ∀ l : Module.Dual ℂ V,
      (∀ u ∈ U, ∀ x : V, l (π u x) = l x) → l ∘ₗ H (e i) = l)
    (P : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hadj : ∀ (i : ι) (x y : V), P (H (e i) x) y = P x (H (e i) y))
    (hsep : ∀ y : V, (∀ x : V, P x y = 0) → y = 0) (l : V →ₗ[ℂ] ℂ)
    (hl : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, ∀ x : V, l (π u x) = l x) :
    ∃ y : V, ∀ x : V, l x = P x y := by
  obtain ⟨U, hU, hlU⟩ := hl
  obtain ⟨i, hi⟩ := hlev U hU
  exact exists_eq_pairing_of_comp_level_eq L P hadj hsep (hi l hlU)

end Smooth
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

end Character
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

end SmoothPart
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

section HeckeSmulTestFunctions

open MeasureTheory
open scoped Topology

namespace TestFunctionAction

section OpenStabilizer

variable {G : Type*} [Group G] [TopologicalSpace G] {M : Type*}

private abbrev HasOpenStabilizer (G : Type*) {M : Type*} [Group G] [TopologicalSpace G] [MulAction G M]
    (v : M) : Prop :=
  IsOpen ((MulAction.stabilizer G v : Subgroup G) : Set G)

variable [MulAction G M]

private theorem hasOpenStabilizer_iff_exists_isOpen_subgroup [ContinuousMul G] {v : M} :
    HasOpenStabilizer G v ↔ ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, u • v = v := by
  constructor
  · intro hv
    exact ⟨MulAction.stabilizer G v, hv, fun u hu => MulAction.mem_stabilizer_iff.mp hu⟩
  · rintro ⟨U, hUo, hUv⟩
    exact Subgroup.isOpen_mono (fun u hu => MulAction.mem_stabilizer_iff.mpr (hUv u hu)) hUo

private theorem hasOpenStabilizer_iff_exists_isCompact_isOpen_subgroup [ContinuousMul G]
    (hex : ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G)) {v : M} :
    HasOpenStabilizer G v ↔
      ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ ∀ u ∈ K, u • v = v := by
  constructor
  · intro hv
    obtain ⟨K₀, hK₀c, hK₀o⟩ := hex
    refine ⟨K₀ ⊓ MulAction.stabilizer G v, ?_, ?_, ?_⟩
    · rw [Subgroup.coe_inf]
      exact hK₀c.inter_right (Subgroup.isClosed_of_isOpen _ hv)
    · rw [Subgroup.coe_inf]
      exact hK₀o.inter hv
    · intro u hu
      exact MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hu).2
  · rintro ⟨K, -, hKo, hKv⟩
    exact hasOpenStabilizer_iff_exists_isOpen_subgroup.mpr ⟨K, hKo, hKv⟩

private theorem HasOpenStabilizer.smul [ContinuousMul G] {v : M} (hv : HasOpenStabilizer G v) (g : G) :
    HasOpenStabilizer G (g • v) := by
  have hset : ((MulAction.stabilizer G (g • v) : Subgroup G) : Set G)
      = (fun h : G => g⁻¹ * h * g) ⁻¹' ((MulAction.stabilizer G v : Subgroup G) : Set G) := by
    ext h
    simp only [SetLike.mem_coe, Set.mem_preimage, MulAction.mem_stabilizer_iff]
    constructor
    · intro hh
      calc (g⁻¹ * h * g) • v = g⁻¹ • h • g • v := by rw [mul_smul, mul_smul]
        _ = g⁻¹ • g • v := by rw [hh]
        _ = v := inv_smul_smul g v
    · intro hh
      calc h • g • v = g • g⁻¹ • h • g • v := (smul_inv_smul g _).symm
        _ = g • (g⁻¹ * h * g) • v := by rw [mul_smul, mul_smul]
        _ = g • v := by rw [hh]
  show IsOpen ((MulAction.stabilizer G (g • v) : Subgroup G) : Set G)
  rw [hset]
  exact hv.preimage (by fun_prop)

private theorem HasOpenStabilizer.const_smul [ContinuousMul G] {R : Type*} [SMul R M] [SMulCommClass G R M]
    {v : M} (hv : HasOpenStabilizer G v) (r : R) : HasOpenStabilizer G (r • v) := by
  refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer G v) (fun g hg => ?_) hv
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [smul_comm, hg]

private theorem isLocallyConstant_indicator_const_of_isClopen {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsClopen s) {N : Type*} [Zero N] (c : N) :
    IsLocallyConstant (s.indicator fun _ => c) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ s
  · exact ⟨s, hs.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨sᶜ, hs.compl.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

end OpenStabilizer
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

section MeasureCoeff

variable (𝕜 : Type*) [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {X : Type*} [MeasurableSpace X]

private noncomputable def measureCoeff (μ : Measure X) (s : Set X) : 𝕜 :=
  algebraMap ℝ 𝕜 (μ s).toReal

private theorem measureCoeff_def (μ : Measure X) (s : Set X) :
    measureCoeff 𝕜 μ s = algebraMap ℝ 𝕜 (μ s).toReal := rfl

private theorem measureCoeff_congr (μ : Measure X) {s t : Set X} (h : μ s = μ t) :
    measureCoeff 𝕜 μ s = measureCoeff 𝕜 μ t := by
  rw [measureCoeff_def, measureCoeff_def, h]

@[scoped simp]
private theorem measureCoeff_empty (μ : Measure X) : measureCoeff 𝕜 μ (∅ : Set X) = 0 := by
  simp [measureCoeff_def]

end MeasureCoeff
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

section FiniteRangeIntegral

variable (𝕜 : Type*) [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {X : Type*} [MeasurableSpace X]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

open Classical in
private noncomputable def finiteRangeIntegral (μ : Measure X) (F : X → V) : V :=
  if h : (Set.range F).Finite then
    ∑ w ∈ h.toFinset, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w
  else 0

private theorem finiteRangeIntegral_of_finite (μ : Measure X) {F : X → V}
    (h : (Set.range F).Finite) :
    finiteRangeIntegral 𝕜 μ F = ∑ w ∈ h.toFinset, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w := by
  unfold finiteRangeIntegral
  exact dif_pos h

private theorem finiteRangeIntegral_eq_sum (μ : Measure X) {F : X → V} (hF : (Set.range F).Finite)
    {T : Finset V} (hT : ∀ x : X, F x ≠ 0 → F x ∈ T) :
    finiteRangeIntegral 𝕜 μ F = ∑ w ∈ T, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w := by
  classical
  rw [finiteRangeIntegral_of_finite 𝕜 μ hF]
  have hzero₁ : ∀ w ∈ hF.toFinset ∪ T, w ∉ hF.toFinset →
      measureCoeff 𝕜 μ (F ⁻¹' {w}) • w = 0 := by
    intro w _ hw
    have hempty : F ⁻¹' {w} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hw (hF.mem_toFinset.mpr ⟨x, hx⟩)
    rw [hempty, measureCoeff_empty, zero_smul]
  have hzero₂ : ∀ w ∈ hF.toFinset ∪ T, w ∉ T →
      measureCoeff 𝕜 μ (F ⁻¹' {w}) • w = 0 := by
    intro w hw hwT
    rcases Finset.mem_union.mp hw with hw₁ | hw₂
    · obtain ⟨x, hx⟩ := hF.mem_toFinset.mp hw₁
      by_cases hx0 : F x = 0
      · rw [← hx, hx0, smul_zero]
      · exact absurd (hx ▸ hT x hx0) hwT
    · exact absurd hw₂ hwT
  calc ∑ w ∈ hF.toFinset, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w
      = ∑ w ∈ hF.toFinset ∪ T, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w :=
        Finset.sum_subset Finset.subset_union_left hzero₁
    _ = ∑ w ∈ T, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w :=
        (Finset.sum_subset Finset.subset_union_right hzero₂).symm

private theorem finiteRangeIntegral_zero (μ : Measure X) :
    finiteRangeIntegral 𝕜 μ (fun _ : X => (0 : V)) = 0 := by
  classical
  have hfin : (Set.range fun _ : X => (0 : V)).Finite :=
    (Set.finite_singleton (0 : V)).subset (by rintro _ ⟨x, rfl⟩; exact rfl)
  rw [finiteRangeIntegral_eq_sum 𝕜 μ hfin (T := ∅) (fun x hx => absurd rfl hx)]
  simp

private theorem finiteRangeIntegral_indicator_const (μ : Measure X) (s : Set X) (x : V) :
    finiteRangeIntegral 𝕜 μ (s.indicator fun _ => x) = measureCoeff 𝕜 μ s • x := by
  classical
  have hfin : (Set.range (s.indicator fun _ : X => x)).Finite := by
    refine ((Set.finite_singleton x).insert 0).subset ?_
    rintro _ ⟨y, rfl⟩
    by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hy]
      exact Set.mem_insert_of_mem _ rfl
    · rw [Set.indicator_of_notMem hy]
      exact Set.mem_insert _ _
  have hT : ∀ y : X, (s.indicator fun _ : X => x) y ≠ 0 →
      (s.indicator fun _ : X => x) y ∈ ({x} : Finset V) := by
    intro y hy
    by_cases hys : y ∈ s
    · rw [Set.indicator_of_mem hys]
      exact Finset.mem_singleton_self x
    · exact absurd (Set.indicator_of_notMem hys _) hy
  rw [finiteRangeIntegral_eq_sum 𝕜 μ hfin hT, Finset.sum_singleton]
  by_cases hx : x = 0
  · rw [hx, smul_zero, smul_zero]
  · have hpre : (s.indicator fun _ : X => x) ⁻¹' {x} = s := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      by_cases hys : y ∈ s
      · simp [Set.indicator_of_mem hys, hys]
      · simp [Set.indicator_of_notMem hys, hys, Ne.symm hx]
    rw [hpre]

private theorem finiteRangeIntegral_comp_eq_sum {W : Type*} (μ : Measure X) {P : X → W}
    (hP : (Set.range P).Finite) (hmeas : ∀ w : W, MeasurableSet (P ⁻¹' {w})) (φ : W → V)
    (hfin : ∀ w : W, φ w ≠ 0 → μ (P ⁻¹' {w}) ≠ ⊤) :
    finiteRangeIntegral 𝕜 μ (fun x => φ (P x))
      = ∑ w ∈ hP.toFinset, measureCoeff 𝕜 μ (P ⁻¹' {w}) • φ w := by
  classical
  have hrange : (Set.range fun x => φ (P x)).Finite := by
    refine (hP.image φ).subset ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨P x, ⟨x, rfl⟩, rfl⟩
  have hT : ∀ x : X, φ (P x) ≠ 0 → φ (P x) ∈ hP.toFinset.image φ := fun x _ =>
    Finset.mem_image_of_mem φ (hP.mem_toFinset.mpr ⟨x, rfl⟩)
  calc finiteRangeIntegral 𝕜 μ (fun x => φ (P x))
      = ∑ v ∈ hP.toFinset.image φ,
          measureCoeff 𝕜 μ ((fun x => φ (P x)) ⁻¹' {v}) • v :=
        finiteRangeIntegral_eq_sum 𝕜 μ hrange hT
    _ = ∑ v ∈ hP.toFinset.image φ, ∑ w ∈ hP.toFinset.filter (fun w => φ w = v),
          measureCoeff 𝕜 μ (P ⁻¹' {w}) • φ w := by
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases hv0 : v = 0
        · subst hv0
          rw [smul_zero]
          refine (Finset.sum_eq_zero fun w hw => ?_).symm
          rw [(Finset.mem_filter.mp hw).2, smul_zero]
        · have hseteq : (fun x => φ (P x)) ⁻¹' {v}
              = ⋃ w ∈ hP.toFinset.filter (fun w => φ w = v), P ⁻¹' {w} := by
            ext x
            simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
              Finset.mem_filter, Set.Finite.mem_toFinset, exists_prop]
            constructor
            · intro hx
              exact ⟨P x, ⟨⟨x, rfl⟩, hx⟩, rfl⟩
            · rintro ⟨w, ⟨-, hφw⟩, hPx⟩
              rw [hPx]
              exact hφw
          have hmeasure : μ ((fun x => φ (P x)) ⁻¹' {v})
              = ∑ w ∈ hP.toFinset.filter (fun w => φ w = v), μ (P ⁻¹' {w}) := by
            rw [hseteq]
            exact measure_biUnion_finset (Set.pairwiseDisjoint_fiber P _) fun w _ => hmeas w
          have hne : ∀ w ∈ hP.toFinset.filter (fun w => φ w = v), μ (P ⁻¹' {w}) ≠ ⊤ := by
            intro w hw
            refine hfin w ?_
            rw [(Finset.mem_filter.mp hw).2]
            exact hv0
          have hcoeff : measureCoeff 𝕜 μ ((fun x => φ (P x)) ⁻¹' {v})
              = ∑ w ∈ hP.toFinset.filter (fun w => φ w = v),
                  measureCoeff 𝕜 μ (P ⁻¹' {w}) := by
            simp only [measureCoeff_def]
            rw [hmeasure, ENNReal.toReal_sum hne, map_sum]
          rw [hcoeff, Finset.sum_smul]
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [(Finset.mem_filter.mp hw).2]
    _ = ∑ w ∈ hP.toFinset, measureCoeff 𝕜 μ (P ⁻¹' {w}) • φ w :=
        Finset.sum_fiberwise_of_maps_to (fun w hw => Finset.mem_image_of_mem φ hw) _

private theorem finiteRangeIntegral_add (μ : Measure X) {F G : X → V}
    (hF : (Set.range F).Finite) (hG : (Set.range G).Finite)
    (hFm : ∀ w : V, MeasurableSet (F ⁻¹' {w})) (hGm : ∀ w : V, MeasurableSet (G ⁻¹' {w}))
    (hFfin : ∀ w : V, w ≠ 0 → μ (F ⁻¹' {w}) ≠ ⊤) (hGfin : ∀ w : V, w ≠ 0 → μ (G ⁻¹' {w}) ≠ ⊤) :
    finiteRangeIntegral 𝕜 μ (fun x => F x + G x)
      = finiteRangeIntegral 𝕜 μ F + finiteRangeIntegral 𝕜 μ G := by
  classical
  have hP : (Set.range fun x => (F x, G x)).Finite := by
    refine (hF.prod hG).subset ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩
  have hPm : ∀ w : V × V, MeasurableSet ((fun x => (F x, G x)) ⁻¹' {w}) := by
    intro w
    have hset : (fun x => (F x, G x)) ⁻¹' {w} = F ⁻¹' {w.1} ∩ G ⁻¹' {w.2} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Prod.ext_iff]
    rw [hset]
    exact (hFm w.1).inter (hGm w.2)
  have hsub1 : ∀ w : V × V, (fun x => (F x, G x)) ⁻¹' {w} ⊆ F ⁻¹' {w.1} := by
    intro w x hx
    have hx' : (F x, G x) = w := hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← hx']
  have hsub2 : ∀ w : V × V, (fun x => (F x, G x)) ⁻¹' {w} ⊆ G ⁻¹' {w.2} := by
    intro w x hx
    have hx' : (F x, G x) = w := hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← hx']
  have hPfst : ∀ w : V × V, w.1 ≠ 0 → μ ((fun x => (F x, G x)) ⁻¹' {w}) ≠ ⊤ := fun w hw =>
    ne_top_of_le_ne_top (hFfin w.1 hw) (measure_mono (hsub1 w))
  have hPsnd : ∀ w : V × V, w.2 ≠ 0 → μ ((fun x => (F x, G x)) ⁻¹' {w}) ≠ ⊤ := fun w hw =>
    ne_top_of_le_ne_top (hGfin w.2 hw) (measure_mono (hsub2 w))
  have e1 : finiteRangeIntegral 𝕜 μ (fun x => F x + G x)
      = ∑ w ∈ hP.toFinset, measureCoeff 𝕜 μ ((fun x => (F x, G x)) ⁻¹' {w}) • (w.1 + w.2) := by
    refine finiteRangeIntegral_comp_eq_sum 𝕜 μ hP hPm (fun w => w.1 + w.2) ?_
    intro w hw
    by_cases h1 : w.1 = 0
    · refine hPsnd w ?_
      intro h2
      exact hw (by show w.1 + w.2 = 0; rw [h1, h2, add_zero])
    · exact hPfst w h1
  have e2 : finiteRangeIntegral 𝕜 μ F
      = ∑ w ∈ hP.toFinset, measureCoeff 𝕜 μ ((fun x => (F x, G x)) ⁻¹' {w}) • w.1 :=
    finiteRangeIntegral_comp_eq_sum 𝕜 μ hP hPm Prod.fst hPfst
  have e3 : finiteRangeIntegral 𝕜 μ G
      = ∑ w ∈ hP.toFinset, measureCoeff 𝕜 μ ((fun x => (F x, G x)) ⁻¹' {w}) • w.2 :=
    finiteRangeIntegral_comp_eq_sum 𝕜 μ hP hPm Prod.snd hPsnd
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [smul_add]

private theorem finiteRangeIntegral_const_smul (μ : Measure X) {F : X → V}
    (hF : (Set.range F).Finite) (hFm : ∀ w : V, MeasurableSet (F ⁻¹' {w}))
    (hFfin : ∀ w : V, w ≠ 0 → μ (F ⁻¹' {w}) ≠ ⊤) (c : 𝕜) :
    finiteRangeIntegral 𝕜 μ (fun x => c • F x) = c • finiteRangeIntegral 𝕜 μ F := by
  classical
  have h1 : finiteRangeIntegral 𝕜 μ (fun x => c • F x)
      = ∑ w ∈ hF.toFinset, measureCoeff 𝕜 μ (F ⁻¹' {w}) • (c • w) :=
    finiteRangeIntegral_comp_eq_sum 𝕜 μ hF hFm (fun w => c • w)
      (fun w hw => hFfin w (fun h0 => hw (by rw [h0]; exact smul_zero c)))
  have h2 : finiteRangeIntegral 𝕜 μ F
      = ∑ w ∈ hF.toFinset, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w :=
    finiteRangeIntegral_comp_eq_sum 𝕜 μ hF hFm (fun w => w) (fun w hw => hFfin w hw)
  rw [h1, h2, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [smul_comm]

private theorem finiteRangeIntegral_distrib_smul {M : Type*} [Monoid M] [DistribMulAction M V]
    [SMulCommClass M 𝕜 V] (μ : Measure X) {F : X → V}
    (hF : (Set.range F).Finite) (hFm : ∀ w : V, MeasurableSet (F ⁻¹' {w}))
    (hFfin : ∀ w : V, w ≠ 0 → μ (F ⁻¹' {w}) ≠ ⊤) (m : M) :
    finiteRangeIntegral 𝕜 μ (fun x => m • F x) = m • finiteRangeIntegral 𝕜 μ F := by
  classical
  have h1 : finiteRangeIntegral 𝕜 μ (fun x => m • F x)
      = ∑ w ∈ hF.toFinset, measureCoeff 𝕜 μ (F ⁻¹' {w}) • (m • w) :=
    finiteRangeIntegral_comp_eq_sum 𝕜 μ hF hFm (fun w => m • w)
      (fun w hw => hFfin w (fun h0 => hw (by rw [h0]; exact smul_zero m)))
  have h2 : finiteRangeIntegral 𝕜 μ F
      = ∑ w ∈ hF.toFinset, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w :=
    finiteRangeIntegral_comp_eq_sum 𝕜 μ hF hFm (fun w => w) (fun w hw => hFfin w hw)
  rw [h1, h2, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  exact (smul_comm m (measureCoeff 𝕜 μ (F ⁻¹' {w})) w).symm

private theorem finiteRangeIntegral_comp_mulLeft {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] {F : G → V}
    (hF : (Set.range F).Finite) (a : G) :
    finiteRangeIntegral 𝕜 μ (fun x => F (a * x)) = finiteRangeIntegral 𝕜 μ F := by
  classical
  have hreq : (Set.range fun x => F (a * x)) = Set.range F := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨a * x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨a⁻¹ * x, by show F (a * (a⁻¹ * x)) = F x; rw [mul_inv_cancel_left]⟩
  have hrange : (Set.range fun x => F (a * x)).Finite := by
    rw [hreq]
    exact hF
  rw [finiteRangeIntegral_eq_sum 𝕜 μ hrange (T := hF.toFinset)
      (fun x _ => hF.mem_toFinset.mpr ⟨a * x, rfl⟩),
    finiteRangeIntegral_eq_sum 𝕜 μ hF (T := hF.toFinset)
      (fun x _ => hF.mem_toFinset.mpr ⟨x, rfl⟩)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hμ : μ ((fun x => F (a * x)) ⁻¹' {w}) = μ (F ⁻¹' {w}) := by
    have hset : (fun x => F (a * x)) ⁻¹' {w} = (fun x => a * x) ⁻¹' (F ⁻¹' {w}) := rfl
    rw [hset]
    exact measure_preimage_mul μ a _
  rw [measureCoeff_congr 𝕜 μ hμ]

private theorem finiteRangeIntegral_comp_mulRight {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulRightInvariant] {F : G → V}
    (hF : (Set.range F).Finite) (a : G) :
    finiteRangeIntegral 𝕜 μ (fun x => F (x * a)) = finiteRangeIntegral 𝕜 μ F := by
  classical
  have hreq : (Set.range fun x => F (x * a)) = Set.range F := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x * a, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x * a⁻¹, by show F (x * a⁻¹ * a) = F x; rw [inv_mul_cancel_right]⟩
  have hrange : (Set.range fun x => F (x * a)).Finite := by
    rw [hreq]
    exact hF
  rw [finiteRangeIntegral_eq_sum 𝕜 μ hrange (T := hF.toFinset)
      (fun x _ => hF.mem_toFinset.mpr ⟨x * a, rfl⟩),
    finiteRangeIntegral_eq_sum 𝕜 μ hF (T := hF.toFinset)
      (fun x _ => hF.mem_toFinset.mpr ⟨x, rfl⟩)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hμ : μ ((fun x => F (x * a)) ⁻¹' {w}) = μ (F ⁻¹' {w}) := by
    have hset : (fun x => F (x * a)) ⁻¹' {w} = (fun x => x * a) ⁻¹' (F ⁻¹' {w}) := rfl
    rw [hset]
    exact measure_preimage_mul_right μ a _
  rw [measureCoeff_congr 𝕜 μ hμ]

end FiniteRangeIntegral
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

section Integrand

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

private theorem finite_range_of_isLocallyConstant_of_hasCompactSupport {X : Type*} [TopologicalSpace X]
    {E : Type*} [Zero E] {F : X → E} (hlc : IsLocallyConstant F) (hsupp : HasCompactSupport F) :
    (Set.range F).Finite := by
  have hcs : IsCompact (tsupport F) := hsupp
  haveI hcsp : CompactSpace (tsupport F) := isCompact_iff_compactSpace.mp hcs
  have h1 : IsLocallyConstant fun x : tsupport F => F (x : X) :=
    hlc.comp_continuous continuous_subtype_val
  have h2 : (F '' tsupport F).Finite := by
    rw [Set.image_eq_range]
    exact h1.range_finite
  refine (h2.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport F
  · exact Set.mem_insert_of_mem _ (Set.mem_image_of_mem _ hx)
  · rw [image_eq_zero_of_notMem_tsupport hx]
    exact Set.mem_insert _ _

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
variable [DistribMulAction G V] [SMulCommClass G 𝕜 V]

private theorem isLocallyConstant_heckeIntegrand {f : G → 𝕜} (hf : IsLocallyConstant f) {v : V}
    (hv : HasOpenStabilizer G v) :
    IsLocallyConstant fun g => f g • g • v := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g₀
  refine ⟨{g : G | f g = f g₀} ∩
    (fun g : G => g₀⁻¹ * g) ⁻¹' ((MulAction.stabilizer G v : Subgroup G) : Set G), ?_, ?_, ?_⟩
  · exact (hf.isOpen_fiber (f g₀)).inter
      (hv.preimage (continuous_const.mul continuous_id))
  · refine ⟨rfl, ?_⟩
    show g₀⁻¹ * g₀ ∈ ((MulAction.stabilizer G v : Subgroup G) : Set G)
    rw [inv_mul_cancel]
    exact (MulAction.stabilizer G v).one_mem
  · rintro g ⟨hg1, hg2⟩
    have hstab : (g₀⁻¹ * g) • v = v := MulAction.mem_stabilizer_iff.mp hg2
    have hgv : g • v = g₀ • v := by
      calc g • v = (g₀ * (g₀⁻¹ * g)) • v := by rw [mul_inv_cancel_left]
        _ = g₀ • (g₀⁻¹ * g) • v := by rw [mul_smul]
        _ = g₀ • v := by rw [hstab]
    have hfg : f g = f g₀ := hg1
    rw [hfg, hgv]

private theorem support_heckeIntegrand_subset (f : G → 𝕜) (v : V) :
    (Function.support fun g => f g • g • v) ⊆ Function.support f := by
  intro g hg
  rw [Function.mem_support] at hg ⊢
  intro h0
  exact hg (by rw [h0, zero_smul])

private theorem hasCompactSupport_heckeIntegrand {f : G → 𝕜} (hf : HasCompactSupport f) (v : V) :
    HasCompactSupport fun g => f g • g • v :=
  hf.mono (support_heckeIntegrand_subset f v)

private theorem finite_range_heckeIntegrand {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {v : V} (hv : HasOpenStabilizer G v) :
    (Set.range fun g => f g • g • v).Finite :=
  finite_range_of_isLocallyConstant_of_hasCompactSupport
    (isLocallyConstant_heckeIntegrand hf hv) (hasCompactSupport_heckeIntegrand hf' v)

private theorem measurableSet_fiber_heckeIntegrand [MeasurableSpace G] [OpensMeasurableSpace G]
    {f : G → 𝕜} (hf : IsLocallyConstant f) {v : V} (hv : HasOpenStabilizer G v) (w : V) :
    MeasurableSet ((fun g => f g • g • v) ⁻¹' {w}) :=
  ((isLocallyConstant_heckeIntegrand hf hv).isOpen_fiber w).measurableSet

private theorem measure_fiber_heckeIntegrand_ne_top [MeasurableSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f : G → 𝕜} (hf' : HasCompactSupport f) (v : V) {w : V}
    (hw : w ≠ 0) : μ ((fun g => f g • g • v) ⁻¹' {w}) ≠ ⊤ := by
  have hK : IsCompact (tsupport f) := hf'
  have hsub : (fun g => f g • g • v) ⁻¹' {w} ⊆ tsupport f := by
    intro g hg
    have hgw : f g • g • v = w := hg
    refine subset_tsupport f ?_
    rw [Function.mem_support]
    intro h0
    exact hw (by rw [← hgw, h0, zero_smul])
  exact ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono hsub)

end Integrand
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

section HeckeSmul

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable [DistribMulAction G V] [SMulCommClass G 𝕜 V]

private noncomputable def heckeSmul (μ : Measure G) (f : G → 𝕜) (v : V) : V :=
  finiteRangeIntegral 𝕜 μ fun g => f g • g • v

private theorem heckeSmul_def (μ : Measure G) (f : G → 𝕜) (v : V) :
    heckeSmul μ f v = finiteRangeIntegral 𝕜 μ fun g => f g • g • v := rfl

private theorem heckeSmul_zero_vector (μ : Measure G) (f : G → 𝕜) :
    heckeSmul μ f (0 : V) = 0 := by
  have h : (fun g => f g • g • (0 : V)) = fun _ : G => (0 : V) := by
    funext g
    rw [smul_zero, smul_zero]
  rw [heckeSmul_def, h]
  exact finiteRangeIntegral_zero 𝕜 μ

variable [TopologicalSpace G] [ContinuousMul G]

private theorem heckeSmul_eq_sum (μ : Measure G) {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {v : V} (hv : HasOpenStabilizer G v) {T : Finset V}
    (hT : ∀ g : G, f g • g • v ≠ 0 → f g • g • v ∈ T) :
    heckeSmul μ f v = ∑ w ∈ T, measureCoeff 𝕜 μ ((fun g => f g • g • v) ⁻¹' {w}) • w :=
  finiteRangeIntegral_eq_sum 𝕜 μ (finite_range_heckeIntegrand hf hf' hv) hT

private theorem heckeSmul_add_right [OpensMeasurableSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {v w : V} (hv : HasOpenStabilizer G v) (hw : HasOpenStabilizer G w) :
    heckeSmul μ f (v + w) = heckeSmul μ f v + heckeSmul μ f w := by
  have h : (fun g => f g • g • (v + w)) = fun g => (f g • g • v) + (f g • g • w) := by
    funext g
    rw [smul_add, smul_add]
  rw [heckeSmul_def, h]
  exact finiteRangeIntegral_add 𝕜 μ
    (finite_range_heckeIntegrand hf hf' hv) (finite_range_heckeIntegrand hf hf' hw)
    (measurableSet_fiber_heckeIntegrand hf hv) (measurableSet_fiber_heckeIntegrand hf hw)
    (fun x hx => measure_fiber_heckeIntegrand_ne_top μ hf' v hx)
    (fun x hx => measure_fiber_heckeIntegrand_ne_top μ hf' w hx)

private theorem heckeSmul_smul_right [OpensMeasurableSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {v : V} (hv : HasOpenStabilizer G v) (c : 𝕜) :
    heckeSmul μ f (c • v) = c • heckeSmul μ f v := by
  have h : (fun g => f g • g • (c • v)) = fun g => c • (f g • g • v) := by
    funext g
    rw [smul_comm (g : G) c v, smul_comm (f g) c (g • v)]
  rw [heckeSmul_def, h]
  exact finiteRangeIntegral_const_smul 𝕜 μ (finite_range_heckeIntegrand hf hf' hv)
    (measurableSet_fiber_heckeIntegrand hf hv)
    (fun x hx => measure_fiber_heckeIntegrand_ne_top μ hf' v hx) c

private theorem heckeSmul_neg_right [OpensMeasurableSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {w : V} (hw : HasOpenStabilizer G w) :
    heckeSmul μ f (-w) = -heckeSmul μ f w := by
  have h := heckeSmul_smul_right μ hf hf' hw (-1 : 𝕜)
  rwa [neg_one_smul, neg_one_smul] at h

private theorem heckeSmul_sub_right [OpensMeasurableSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {v w : V} (hv : HasOpenStabilizer G v) (hw : HasOpenStabilizer G w) :
    heckeSmul μ f (v - w) = heckeSmul μ f v - heckeSmul μ f w := by
  have hneg : HasOpenStabilizer G (-w) := by
    have h := hw.const_smul (-1 : 𝕜)
    rwa [neg_one_smul] at h
  rw [sub_eq_add_neg, heckeSmul_add_right μ hf hf' hv hneg,
    heckeSmul_neg_right μ hf hf' hw, ← sub_eq_add_neg]

private theorem heckeSmul_add_left [OpensMeasurableSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f₁ f₂ : G → 𝕜} (hf₁ : IsLocallyConstant f₁)
    (hf₁' : HasCompactSupport f₁) (hf₂ : IsLocallyConstant f₂) (hf₂' : HasCompactSupport f₂)
    {v : V} (hv : HasOpenStabilizer G v) :
    heckeSmul μ (f₁ + f₂) v = heckeSmul μ f₁ v + heckeSmul μ f₂ v := by
  have h : (fun g => (f₁ + f₂) g • g • v) = fun g => (f₁ g • g • v) + (f₂ g • g • v) := by
    funext g
    rw [Pi.add_apply, add_smul]
  rw [heckeSmul_def, h]
  exact finiteRangeIntegral_add 𝕜 μ
    (finite_range_heckeIntegrand hf₁ hf₁' hv) (finite_range_heckeIntegrand hf₂ hf₂' hv)
    (measurableSet_fiber_heckeIntegrand hf₁ hv) (measurableSet_fiber_heckeIntegrand hf₂ hv)
    (fun x hx => measure_fiber_heckeIntegrand_ne_top μ hf₁' v hx)
    (fun x hx => measure_fiber_heckeIntegrand_ne_top μ hf₂' v hx)

private theorem heckeSmul_smul_left [OpensMeasurableSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {v : V} (hv : HasOpenStabilizer G v) (c : 𝕜) :
    heckeSmul μ (c • f) v = c • heckeSmul μ f v := by
  have h : (fun g => (c • f) g • g • v) = fun g => c • (f g • g • v) := by
    funext g
    rw [Pi.smul_apply, smul_eq_mul, mul_smul]
  rw [heckeSmul_def, h]
  exact finiteRangeIntegral_const_smul 𝕜 μ (finite_range_heckeIntegrand hf hf' hv)
    (measurableSet_fiber_heckeIntegrand hf hv)
    (fun x hx => measure_fiber_heckeIntegrand_ne_top μ hf' v hx) c

private theorem heckeSmul_translate_left [OpensMeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {v : V} (hv : HasOpenStabilizer G v) (g : G) :
    heckeSmul μ (fun h => f (g⁻¹ * h)) v = g • heckeSmul μ f v := by

  have hB : heckeSmul μ (fun h => f (g⁻¹ * h)) v
      = finiteRangeIntegral 𝕜 μ fun h => g • (f (g⁻¹ * h) • (g⁻¹ * h) • v) := by
    rw [heckeSmul_def]
    congr 1
    funext h
    rw [smul_comm g (f (g⁻¹ * h)) ((g⁻¹ * h) • v), ← mul_smul, mul_inv_cancel_left]

  have hFg : (Set.range fun x : G => g • (f x • x • v)).Finite := by
    refine ((finite_range_heckeIntegrand hf hf' hv).image (fun w => g • w)).subset ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨f x • x • v, ⟨x, rfl⟩, rfl⟩
  have hC : finiteRangeIntegral 𝕜 μ (fun h => g • (f (g⁻¹ * h) • (g⁻¹ * h) • v))
      = finiteRangeIntegral 𝕜 μ fun x => g • (f x • x • v) :=
    finiteRangeIntegral_comp_mulLeft 𝕜 μ (F := fun x => g • (f x • x • v)) hFg g⁻¹

  have hD : finiteRangeIntegral 𝕜 μ (fun x => g • (f x • x • v))
      = g • finiteRangeIntegral 𝕜 μ fun x => f x • x • v := by
    refine finiteRangeIntegral_distrib_smul 𝕜 μ ?_ ?_ ?_ g
    · exact finite_range_heckeIntegrand hf hf' hv
    · exact measurableSet_fiber_heckeIntegrand hf hv
    · exact fun x hx => measure_fiber_heckeIntegrand_ne_top μ hf' v hx
  rw [hB, hC, hD, heckeSmul_def]

private theorem heckeSmul_smul_vector [MeasurableMul G] (μ : Measure G)
    [μ.IsMulRightInvariant] {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {v : V} (hv : HasOpenStabilizer G v) (k : G) :
    heckeSmul μ f (k • v) = heckeSmul μ (fun h => f (h * k⁻¹)) v := by

  have hlc' : IsLocallyConstant fun h : G => f (h * k⁻¹) :=
    hf.comp_continuous (continuous_id.mul continuous_const)
  have hcs' : HasCompactSupport fun h : G => f (h * k⁻¹) := by
    have h := hf'.comp_homeomorph (Homeomorph.mulRight k⁻¹)
    simpa only [Homeomorph.coe_mulRight, Function.comp_def] using h

  have hB : heckeSmul μ f (k • v)
      = finiteRangeIntegral 𝕜 μ fun h => f (h * k * k⁻¹) • (h * k) • v := by
    rw [heckeSmul_def]
    congr 1
    funext h
    rw [mul_inv_cancel_right, ← mul_smul]

  have hC : finiteRangeIntegral 𝕜 μ (fun h => f (h * k * k⁻¹) • (h * k) • v)
      = finiteRangeIntegral 𝕜 μ fun x => f (x * k⁻¹) • x • v :=
    finiteRangeIntegral_comp_mulRight 𝕜 μ (finite_range_heckeIntegrand hlc' hcs' hv) k
  rw [hB, hC, heckeSmul_def]

end HeckeSmul
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

section Idempotent

variable (𝕜 : Type*) [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {G : Type*}

private noncomputable def heckeIdempotent [MeasurableSpace G] (μ : Measure G) (K : Set G) : G → 𝕜 :=
  K.indicator fun _ => algebraMap ℝ 𝕜 ((μ K).toReal)⁻¹

private theorem heckeIdempotent_def [MeasurableSpace G] (μ : Measure G) (K : Set G) :
    heckeIdempotent 𝕜 μ K = K.indicator fun _ => algebraMap ℝ 𝕜 ((μ K).toReal)⁻¹ := rfl

private theorem heckeIdempotent_apply_of_mem [MeasurableSpace G] (μ : Measure G) {K : Set G} {g : G}
    (hg : g ∈ K) : heckeIdempotent 𝕜 μ K g = algebraMap ℝ 𝕜 ((μ K).toReal)⁻¹ :=
  Set.indicator_of_mem hg _

private theorem heckeIdempotent_apply_of_notMem [MeasurableSpace G] (μ : Measure G) {K : Set G} {g : G}
    (hg : g ∉ K) : heckeIdempotent 𝕜 μ K g = 0 :=
  Set.indicator_of_notMem hg _

private theorem isLocallyConstant_heckeIdempotent [MeasurableSpace G] [TopologicalSpace G]
    (μ : Measure G) {K : Set G} (hK : IsClopen K) :
    IsLocallyConstant (heckeIdempotent 𝕜 μ K) :=
  isLocallyConstant_indicator_const_of_isClopen hK _

private theorem hasCompactSupport_heckeIdempotent [MeasurableSpace G] [TopologicalSpace G]
    (μ : Measure G) {K : Set G} (hKc : IsCompact K) (hKcl : IsClosed K) :
    HasCompactSupport (heckeIdempotent 𝕜 μ K) :=
  HasCompactSupport.intro' hKc hKcl fun _x hx => Set.indicator_of_notMem hx _

variable {𝕜}
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable [Group G] [MeasurableSpace G] [DistribMulAction G V] [SMulCommClass G 𝕜 V]

private theorem heckeSmul_indicator_of_forall_smul_eq (μ : Measure G) {K : Set G} (c : 𝕜) {v : V}
    (hfix : ∀ k ∈ K, k • v = v) :
    heckeSmul μ (K.indicator fun _ => c) v = (measureCoeff 𝕜 μ K * c) • v := by
  have h : (fun g => (K.indicator fun _ => c) g • g • v)
      = K.indicator fun _ => c • v := by
    funext g
    by_cases hg : g ∈ K
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, hfix g hg]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_smul]
  rw [heckeSmul_def, h, finiteRangeIntegral_indicator_const, smul_smul]

private theorem heckeSmul_heckeIdempotent_of_forall_smul_eq (μ : Measure G) {K : Set G}
    (hKne : μ K ≠ 0) (hKfin : μ K ≠ ⊤) {v : V} (hfix : ∀ k ∈ K, k • v = v) :
    heckeSmul μ (heckeIdempotent 𝕜 μ K) v = v := by
  have h := heckeSmul_indicator_of_forall_smul_eq μ
    (K := K) (algebraMap ℝ 𝕜 ((μ K).toReal)⁻¹) hfix
  rw [heckeIdempotent_def, h, measureCoeff_def, ← map_mul,
    mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hKne, hKfin⟩), map_one, one_smul]

variable [TopologicalSpace G] [ContinuousMul G]

private theorem exists_isLocallyConstant_hasCompactSupport_heckeSmul_eq_self
    (μ : Measure G) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    (hex : ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G)) {v : V}
    (hv : HasOpenStabilizer G v) :
    ∃ f : G → 𝕜, IsLocallyConstant f ∧ HasCompactSupport f ∧ heckeSmul μ f v = v := by
  obtain ⟨K, hKc, hKo, hKfix⟩ :=
    (hasOpenStabilizer_iff_exists_isCompact_isOpen_subgroup hex).mp hv
  have hKne : μ (K : Set G) ≠ 0 := hKo.measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKfin : μ (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne
  refine ⟨heckeIdempotent 𝕜 μ (K : Set G), ?_, ?_, ?_⟩
  · exact isLocallyConstant_heckeIdempotent 𝕜 μ ⟨Subgroup.isClosed_of_isOpen _ hKo, hKo⟩
  · exact hasCompactSupport_heckeIdempotent 𝕜 μ hKc (Subgroup.isClosed_of_isOpen _ hKo)
  · exact heckeSmul_heckeIdempotent_of_forall_smul_eq μ hKne hKfin
      (fun k hk => hKfix k hk)

end Idempotent
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

section Projection

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G]
variable [DistribMulAction G V] [SMulCommClass G 𝕜 V]

variable (𝕜) in
private def fixedPointsSubmodule (K : Subgroup G) : Submodule 𝕜 V where
  carrier := {v : V | ∀ k ∈ K, k • v = v}
  zero_mem' := fun k _ => smul_zero k
  add_mem' := by
    intro v w hv hw k hk
    rw [smul_add, hv k hk, hw k hk]
  smul_mem' := by
    intro c v hv k hk
    rw [smul_comm, hv k hk]

variable (𝕜) in
private def augmentationSubmodule (K : Subgroup G) : Submodule 𝕜 V :=
  Submodule.span 𝕜 {x : V | ∃ k ∈ K, ∃ u : V, k • u - u = x}

private theorem mem_fixedPointsSubmodule_iff {K : Subgroup G} {v : V} :
    v ∈ fixedPointsSubmodule 𝕜 K ↔ ∀ k ∈ K, k • v = v := Iff.rfl

private theorem smul_sub_self_mem_augmentationSubmodule {K : Subgroup G} {k : G} (hk : k ∈ K) (u : V) :
    k • u - u ∈ augmentationSubmodule 𝕜 K :=
  Submodule.subset_span ⟨k, hk, u, rfl⟩

private theorem hasOpenStabilizer_of_mem_fixedPointsSubmodule {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) {v : V} (hv : v ∈ fixedPointsSubmodule 𝕜 K) :
    HasOpenStabilizer G v :=
  (hasOpenStabilizer_iff_exists_isOpen_subgroup).mpr ⟨K, hKo, hv⟩

private theorem heckeSmul_heckeIdempotent_mem_fixedPoints [OpensMeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) {w : V} (hw : HasOpenStabilizer G w) :
    heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) w ∈ fixedPointsSubmodule 𝕜 K := by
  refine (mem_fixedPointsSubmodule_iff).mpr fun k hk => ?_
  have hlc : IsLocallyConstant (heckeIdempotent 𝕜 μ (K : Set G)) :=
    isLocallyConstant_heckeIdempotent 𝕜 μ ⟨Subgroup.isClosed_of_isOpen _ hKo, hKo⟩
  have hcs : HasCompactSupport (heckeIdempotent 𝕜 μ (K : Set G)) :=
    hasCompactSupport_heckeIdempotent 𝕜 μ hKc (Subgroup.isClosed_of_isOpen _ hKo)
  have htrans := heckeSmul_translate_left μ hlc hcs hw k
  have hinv : (fun h => heckeIdempotent 𝕜 μ (K : Set G) (k⁻¹ * h))
      = heckeIdempotent 𝕜 μ (K : Set G) := by
    funext h
    by_cases hh : h ∈ (K : Set G)
    · rw [heckeIdempotent_apply_of_mem 𝕜 μ hh,
        heckeIdempotent_apply_of_mem 𝕜 μ (by exact (mul_mem_cancel_left (K.inv_mem hk)).mpr hh)]
    · rw [heckeIdempotent_apply_of_notMem 𝕜 μ hh, heckeIdempotent_apply_of_notMem 𝕜 μ
        (by exact fun hmem => hh ((mul_mem_cancel_left (K.inv_mem hk)).mp hmem))]
  rw [hinv] at htrans
  exact htrans.symm

private theorem heckeSmul_heckeIdempotent_idem [OpensMeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hKne : μ (K : Set G) ≠ 0)
    {w : V} (hw : HasOpenStabilizer G w) :
    heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G))
        (heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) w)
      = heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) w :=
  heckeSmul_heckeIdempotent_of_forall_smul_eq μ hKne hKc.measure_lt_top.ne
    (fun k hk => (mem_fixedPointsSubmodule_iff.mp
      (heckeSmul_heckeIdempotent_mem_fixedPoints μ hKo hKc hw)) k hk)

private theorem measureCoeff_smul_sub_heckeSmul_indicator_mem_augmentation [OpensMeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) {u : V}
    (hu : HasOpenStabilizer G u) :
    measureCoeff 𝕜 μ (K : Set G) • u
        - heckeSmul μ ((K : Set G).indicator fun _ => (1 : 𝕜)) u
      ∈ augmentationSubmodule 𝕜 K := by
  classical
  by_cases hu0 : u = 0
  · subst hu0
    rw [heckeSmul_zero_vector, smul_zero, sub_zero]
    exact Submodule.zero_mem _
  have hKclopen : IsClopen (K : Set G) := ⟨Subgroup.isClosed_of_isOpen _ hKo, hKo⟩
  have hlc : IsLocallyConstant ((K : Set G).indicator fun _ => (1 : 𝕜)) :=
    isLocallyConstant_indicator_const_of_isClopen hKclopen _
  have hcs : HasCompactSupport ((K : Set G).indicator fun _ => (1 : 𝕜)) :=
    HasCompactSupport.intro' hKc hKclopen.1 fun _x hx => Set.indicator_of_notMem hx _
  have hKfin : μ (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne
  have hFrange : (Set.range fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u).Finite :=
    finite_range_heckeIntegrand hlc hcs hu
  have hFmeas : ∀ x : V,
      MeasurableSet ((fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u) ⁻¹' {x}) :=
    measurableSet_fiber_heckeIntegrand hlc hu

  have hFmem : ∀ g ∈ (K : Set G),
      ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u = g • u := by
    intro g hg
    rw [Set.indicator_of_mem hg, one_smul]
  have hFnotMem : ∀ g : G, g ∉ (K : Set G) →
      ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u = 0 := by
    intro g hg
    rw [Set.indicator_of_notMem hg, zero_smul]
  have hFne : ∀ g ∈ (K : Set G),
      ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u ≠ 0 := by
    intro g hg h0
    rw [hFmem g hg] at h0
    exact hu0 (by simpa using congrArg (fun x => g⁻¹ • x) h0)

  have hTmem : ∀ g : G, ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u ≠ 0 →
      ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u ∈ hFrange.toFinset.erase 0 := by
    intro g hg
    exact Finset.mem_erase.mpr ⟨hg, hFrange.mem_toFinset.mpr ⟨g, rfl⟩⟩
  have hTne : ∀ x ∈ hFrange.toFinset.erase 0, x ≠ 0 := fun x hx => (Finset.mem_erase.mp hx).1
  have hTrep : ∀ x ∈ hFrange.toFinset.erase 0, ∃ g ∈ (K : Set G), g • u = x := by
    intro x hx
    obtain ⟨g, hg⟩ := hFrange.mem_toFinset.mp (Finset.mem_of_mem_erase hx)
    by_cases hgK : g ∈ (K : Set G)
    · exact ⟨g, hgK, (hFmem g hgK).symm.trans hg⟩
    · exact absurd (by rw [← hg]; exact hFnotMem g hgK) (hTne x hx)

  have hcover : (K : Set G)
      = ⋃ x ∈ hFrange.toFinset.erase 0,
          (fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u) ⁻¹' {x} := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hg
      exact ⟨((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u, hTmem g (hFne g hg), rfl⟩
    · rintro ⟨x, hxT, hgx⟩
      by_contra hgK
      exact hTne x hxT (by rw [← hgx]; exact hFnotMem g hgK)
  have hfibsub : ∀ x ∈ hFrange.toFinset.erase 0,
      (fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u) ⁻¹' {x} ⊆ (K : Set G) := by
    intro x hx g hg
    by_contra hgK
    exact hTne x hx (by rw [← Set.mem_singleton_iff.mp hg]; exact hFnotMem g hgK)
  have hfibtop : ∀ x ∈ hFrange.toFinset.erase 0,
      μ ((fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u) ⁻¹' {x}) ≠ ⊤ :=
    fun x hx => ne_top_of_le_ne_top hKfin (measure_mono (hfibsub x hx))

  have hmass : μ (K : Set G) = ∑ x ∈ hFrange.toFinset.erase 0,
      μ ((fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u) ⁻¹' {x}) := by
    conv_lhs => rw [hcover]
    exact measure_biUnion_finset
      (Set.pairwiseDisjoint_fiber (fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u) _)
      fun x _ => hFmeas x
  have hcoeffsum : measureCoeff 𝕜 μ (K : Set G)
      = ∑ x ∈ hFrange.toFinset.erase 0,
          measureCoeff 𝕜 μ
            ((fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u) ⁻¹' {x}) := by
    simp only [measureCoeff_def]
    rw [hmass, ENNReal.toReal_sum hfibtop, map_sum]

  have hsum : heckeSmul μ ((K : Set G).indicator fun _ => (1 : 𝕜)) u
      = ∑ x ∈ hFrange.toFinset.erase 0,
          measureCoeff 𝕜 μ
            ((fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u) ⁻¹' {x}) • x :=
    finiteRangeIntegral_eq_sum 𝕜 μ hFrange hTmem

  rw [hsum, hcoeffsum, Finset.sum_smul, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun x hx => ?_
  obtain ⟨g, hgK, hgx⟩ := hTrep x hx
  rw [← hgx, ← smul_sub, ← neg_sub (g • u) u]
  exact Submodule.smul_mem _ _
    (Submodule.neg_mem _ (smul_sub_self_mem_augmentationSubmodule hgK u))

private theorem sub_heckeSmul_heckeIdempotent_mem_augmentation [OpensMeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hKne : μ (K : Set G) ≠ 0)
    {w : V} (hw : HasOpenStabilizer G w) :
    w - heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) w ∈ augmentationSubmodule 𝕜 K := by
  have hKfin : μ (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne

  have hpoint : (fun g => heckeIdempotent 𝕜 μ (K : Set G) g • g • w)
      = fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g •
          (algebraMap ℝ 𝕜 ((μ (K : Set G)).toReal)⁻¹ • w) := by
    funext g
    by_cases hg : g ∈ (K : Set G)
    · rw [heckeIdempotent_apply_of_mem 𝕜 μ hg, Set.indicator_of_mem hg, one_smul]
      exact (smul_comm g (algebraMap ℝ 𝕜 ((μ (K : Set G)).toReal)⁻¹) w).symm
    · rw [heckeIdempotent_apply_of_notMem 𝕜 μ hg, Set.indicator_of_notMem hg, zero_smul,
        zero_smul]
  have h1 : heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) w
      = heckeSmul μ ((K : Set G).indicator fun _ => (1 : 𝕜))
          (algebraMap ℝ 𝕜 ((μ (K : Set G)).toReal)⁻¹ • w) := by
    rw [heckeSmul_def, heckeSmul_def, hpoint]
  have h2 : measureCoeff 𝕜 μ (K : Set G) • (algebraMap ℝ 𝕜 ((μ (K : Set G)).toReal)⁻¹ • w)
      = w := by
    rw [measureCoeff_def, smul_smul, ← map_mul,
      mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hKne, hKfin⟩), map_one, one_smul]
  have h3 := measureCoeff_smul_sub_heckeSmul_indicator_mem_augmentation (𝕜 := 𝕜) μ hKo hKc
    (hw.const_smul (algebraMap ℝ 𝕜 ((μ (K : Set G)).toReal)⁻¹))
  rw [h2] at h3
  rw [h1]
  exact h3

private theorem fixedPoints_sup_augmentation_eq_top [OpensMeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (hsm : ∀ v : V, HasOpenStabilizer G v) {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hKne : μ (K : Set G) ≠ 0) :
    (fixedPointsSubmodule 𝕜 K) ⊔ (augmentationSubmodule 𝕜 K) = (⊤ : Submodule 𝕜 V) := by
  rw [Submodule.eq_top_iff']
  intro w
  have hw : HasOpenStabilizer G w := hsm w
  have hsplit : w = heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) w
      + (w - heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) w) := by
    abel
  rw [hsplit]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (heckeSmul_heckeIdempotent_mem_fixedPoints μ hKo hKc hw))
    (Submodule.mem_sup_right (sub_heckeSmul_heckeIdempotent_mem_augmentation μ hKo hKc hKne hw))

private theorem heckeSmul_heckeIdempotent_eq_zero_of_mem_augmentation [OpensMeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ]
    (hsm : ∀ v : V, HasOpenStabilizer G v) {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) {x : V}
    (hx : x ∈ augmentationSubmodule 𝕜 K) :
    heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) x = 0 := by
  have hlc : IsLocallyConstant (heckeIdempotent 𝕜 μ (K : Set G)) :=
    isLocallyConstant_heckeIdempotent 𝕜 μ ⟨Subgroup.isClosed_of_isOpen _ hKo, hKo⟩
  have hcs : HasCompactSupport (heckeIdempotent 𝕜 μ (K : Set G)) :=
    hasCompactSupport_heckeIdempotent 𝕜 μ hKc (Subgroup.isClosed_of_isOpen _ hKo)
  refine Submodule.span_induction
    (p := fun y _ => heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) y = 0) ?_ ?_ ?_ ?_ hx
  ·
    rintro _ ⟨k, hk, u, rfl⟩
    have hu : HasOpenStabilizer G u := hsm u
    have hku : HasOpenStabilizer G (k • u) := hu.smul k
    rw [heckeSmul_sub_right μ hlc hcs hku hu]
    have hρ := heckeSmul_smul_vector μ hlc hcs hu k
    have hinv : (fun h => heckeIdempotent 𝕜 μ (K : Set G) (h * k⁻¹))
        = heckeIdempotent 𝕜 μ (K : Set G) := by
      funext h
      by_cases hh : h ∈ (K : Set G)
      · rw [heckeIdempotent_apply_of_mem 𝕜 μ hh, heckeIdempotent_apply_of_mem 𝕜 μ
          (by exact (mul_mem_cancel_right (K.inv_mem hk)).mpr hh)]
      · rw [heckeIdempotent_apply_of_notMem 𝕜 μ hh, heckeIdempotent_apply_of_notMem 𝕜 μ
          (by exact fun hmem => hh ((mul_mem_cancel_right (K.inv_mem hk)).mp hmem))]
    rw [hinv] at hρ
    rw [hρ, sub_self]
  ·
    exact heckeSmul_zero_vector μ _
  ·
    intro y z _ _ hy hz
    have hys : HasOpenStabilizer G y := hsm y
    have hzs : HasOpenStabilizer G z := hsm z
    rw [heckeSmul_add_right μ hlc hcs hys hzs, hy, hz, add_zero]
  ·
    intro a y _ hy
    have hys : HasOpenStabilizer G y := hsm y
    rw [heckeSmul_smul_right μ hlc hcs hys a, hy, smul_zero]

private theorem disjoint_fixedPoints_augmentation [OpensMeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ]
    (hsm : ∀ v : V, HasOpenStabilizer G v) {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hKne : μ (K : Set G) ≠ 0) :
    Disjoint (fixedPointsSubmodule 𝕜 K) (augmentationSubmodule 𝕜 K : Submodule 𝕜 V) := by
  rw [Submodule.disjoint_def]
  intro x hxfix hxaug
  have h1 : heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) x = x :=
    heckeSmul_heckeIdempotent_of_forall_smul_eq μ hKne hKc.measure_lt_top.ne
      (fun k hk => (mem_fixedPointsSubmodule_iff.mp hxfix) k hk)
  have h2 : heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) x = 0 :=
    heckeSmul_heckeIdempotent_eq_zero_of_mem_augmentation μ hsm hKo hKc hxaug
  rw [h1] at h2
  exact h2

private theorem isCompl_fixedPoints_augmentation [OpensMeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μ] (hsm : ∀ v : V, HasOpenStabilizer G v) {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hKne : μ (K : Set G) ≠ 0) :
    IsCompl (fixedPointsSubmodule 𝕜 K) (augmentationSubmodule 𝕜 K : Submodule 𝕜 V) := by
  constructor
  · exact disjoint_fixedPoints_augmentation μ hsm hKo hKc hKne
  · rw [codisjoint_iff]
    exact fixedPoints_sup_augmentation_eq_top μ hsm hKo hKc hKne

end Projection
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient"

end TestFunctionAction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"
end HeckeSmulTestFunctions
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"

section InvariantFunctionalLevel
namespace TestFunctionAction

section FunctionalInvariance

open MeasureTheory

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G]
variable [DistribMulAction G V] [SMulCommClass G 𝕜 V]

omit [Algebra ℝ 𝕜] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G]
  [SMulCommClass G 𝕜 V] in

private theorem augmentationSubmodule_le_ker {K : Subgroup G} {W : Type*} [AddCommGroup W]
    [Module 𝕜 W] (ℓ : V →ₗ[𝕜] W) (hℓ : ∀ k ∈ K, ∀ u : V, ℓ (k • u) = ℓ u) :
    augmentationSubmodule 𝕜 K ≤ LinearMap.ker ℓ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, hk, u, rfl⟩
  simp [LinearMap.mem_ker, hℓ k hk u]

private theorem apply_heckeSmul_heckeIdempotent_of_forall_apply_smul_eq [OpensMeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hKne : μ (K : Set G) ≠ 0)
    {W : Type*} [AddCommGroup W] [Module 𝕜 W] (ℓ : V →ₗ[𝕜] W)
    (hℓ : ∀ k ∈ K, ∀ u : V, ℓ (k • u) = ℓ u) {w : V} (hw : HasOpenStabilizer G w) :
    ℓ (heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) w) = ℓ w := by
  have h := augmentationSubmodule_le_ker ℓ hℓ
    (sub_heckeSmul_heckeIdempotent_mem_augmentation μ hKo hKc hKne hw)
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h
  exact h.symm

end FunctionalInvariance
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"

end TestFunctionAction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"
end InvariantFunctionalLevel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"

section RightInvarianceNeighbourhood
open Filter Topology

namespace LocallyConstantStabilizer

variable {G : Type*} [Group G]

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem exists_mem_nhds_one_right_invariant {φ : G → ℂ} (hlc : IsLocallyConstant φ)
    (hcs : HasCompactSupport φ) :
    ∃ W ∈ 𝓝 (1 : G), ∀ k ∈ W, ∀ g, φ (g * k) = φ g := by
  have hloc : ∀ x : G, ∃ V ∈ 𝓝 x, ∃ W ∈ 𝓝 (1 : G), ∀ g ∈ V, ∀ k ∈ W, φ (g * k) = φ g := by
    intro x
    obtain ⟨U, hUo, hxU, hUc⟩ := hlc.exists_open x
    have hpre : (fun p : G × G => p.1 * p.2) ⁻¹' U ∈ 𝓝 ((x, 1) : G × G) :=
      (hUo.preimage continuous_mul).mem_nhds (by simpa using hxU)
    obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.1 hpre
    refine ⟨V, hV, W, hW, fun g hg k hk => ?_⟩
    have h1 : g * k ∈ U := hVW (Set.mk_mem_prod hg hk)
    have h2 : g * 1 ∈ U := hVW (Set.mk_mem_prod hg (mem_of_mem_nhds hW))
    rw [hUc _ h1, ← hUc _ h2, mul_one]
  choose V hV W hW hVW using hloc
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover (s := tsupport φ) hcs V fun x _ => hV x
  set W₀ : Set G := ⋂ x ∈ t, W x with hW₀
  have hW₀n : W₀ ∈ 𝓝 (1 : G) := (biInter_finset_mem t).2 fun x _ => hW x
  have hkey : ∀ k ∈ W₀, ∀ g ∈ tsupport φ, φ (g * k) = φ g := by
    intro k hk g hg
    obtain ⟨x, hxt, hgx⟩ := Set.mem_iUnion₂.1 (ht hg)
    exact hVW x g hgx k (Set.mem_iInter₂.1 hk x hxt)
  refine ⟨W₀ ∩ W₀⁻¹, inter_mem hW₀n (inv_mem_nhds_one G hW₀n), fun k hk g => ?_⟩
  by_cases hg : g ∈ tsupport φ
  · exact hkey k hk.1 g hg
  · by_cases hgk : g * k ∈ tsupport φ
    · have := hkey k⁻¹ (Set.mem_inv.1 hk.2) (g * k) hgk
      rwa [mul_inv_cancel_right, eq_comm] at this
    · rw [image_eq_zero_of_notMem_tsupport hg, image_eq_zero_of_notMem_tsupport hgk]

end LocallyConstantStabilizer
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"
end RightInvarianceNeighbourhood
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"

section HeckeConvolutionLaw
open MeasureTheory
open scoped Topology
open MulConvolution

namespace TestFunctionAction

section Helpers

variable {X : Type*} [MeasurableSpace X]

private theorem measureCoeff_complex (μ : Measure X) (s : Set X) :
    measureCoeff ℂ μ s = ((μ.real s : ℝ) : ℂ) := by
  rw [measureCoeff_def, Algebra.algebraMap_eq_smul_one, Complex.real_smul, mul_one,
    measureReal_def]

omit [MeasurableSpace X] in

private theorem hasCompactSupport_sub {f g : X → ℂ} [TopologicalSpace X]
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (f - g) := by
  have hsub : Function.support (f - g) ⊆ tsupport f ∪ tsupport g := by
    intro x hx
    rw [Function.mem_support] at hx
    by_cases hfx : f x = 0
    · refine Or.inr (subset_tsupport g ?_)
      rw [Function.mem_support]
      intro hgx
      exact hx (by rw [Pi.sub_apply, hfx, hgx, sub_zero])
    · exact Or.inl (subset_tsupport f (Function.mem_support.mpr hfx))
  have hcl : IsClosed (tsupport f ∪ tsupport g) := (isClosed_tsupport f).union (isClosed_tsupport g)
  have hcpt : IsCompact (tsupport f ∪ tsupport g) := hf.union hg
  exact IsCompact.of_isClosed_subset hcpt (isClosed_tsupport _)
    (closure_minimal hsub hcl)

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable [DistribMulAction G V] [SMulCommClass G ℂ V]

private theorem heckeSmul_zero_left (μ : Measure G) (w : V) :
    heckeSmul μ (0 : G → ℂ) w = 0 := by
  have h : (fun g : G => (0 : G → ℂ) g • g • w) = fun _ : G => (0 : V) := by
    funext g
    rw [Pi.zero_apply, zero_smul]
  rw [heckeSmul_def, h]
  exact finiteRangeIntegral_zero ℂ μ

private theorem mulConv_zero_left (μ : Measure G) (f₂ : G → ℂ) : mulConv μ (0 : G → ℂ) f₂ = 0 := by
  funext h
  simp [mulConv]

end Helpers
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"

section TranslatedIndicator

variable {G : Type*} [Group G] [TopologicalSpace G]

private noncomputable def translatedIndicator (K : Set G) (x : G) : G → ℂ :=
  fun h => K.indicator (fun _ => (1 : ℂ)) (x⁻¹ * h)

omit [TopologicalSpace G] in
private theorem translatedIndicator_apply_of_mem {K : Set G} {x h : G} (hh : x⁻¹ * h ∈ K) :
    translatedIndicator K x h = 1 :=
  Set.indicator_of_mem hh _

omit [TopologicalSpace G] in
private theorem translatedIndicator_apply_of_notMem {K : Set G} {x h : G} (hh : x⁻¹ * h ∉ K) :
    translatedIndicator K x h = 0 :=
  Set.indicator_of_notMem hh _

omit [TopologicalSpace G] in

private theorem preimage_mulLeft_inv_eq_image (K : Set G) (x : G) :
    (fun h => x⁻¹ * h) ⁻¹' K = (fun k => x * k) '' K := by
  ext h
  constructor
  · intro hh
    exact ⟨x⁻¹ * h, hh, mul_inv_cancel_left x h⟩
  · rintro ⟨k, hk, rfl⟩
    simpa [Set.mem_preimage, inv_mul_cancel_left] using hk

variable [ContinuousMul G]

private theorem isLocallyConstant_translatedIndicator {K : Set G} (hK : IsClopen K) (x : G) :
    IsLocallyConstant (translatedIndicator K x) :=
  (isLocallyConstant_indicator_const_of_isClopen hK (1 : ℂ)).comp_continuous
    (continuous_const.mul continuous_id)

private theorem hasCompactSupport_translatedIndicator {K : Set G} (hKc : IsCompact K)
    (hKcl : IsClosed K) (x : G) : HasCompactSupport (translatedIndicator K x) := by
  have hcosetCpt : IsCompact ((fun h => x⁻¹ * h) ⁻¹' K) := by
    rw [preimage_mulLeft_inv_eq_image]
    exact hKc.image (continuous_const_mul x)
  have hcosetCl : IsClosed ((fun h => x⁻¹ * h) ⁻¹' K) :=
    hKcl.preimage (continuous_const.mul continuous_id)
  exact HasCompactSupport.intro' hcosetCpt hcosetCl fun h hh =>
    translatedIndicator_apply_of_notMem hh

omit [ContinuousMul G] in

private theorem translatedIndicator_right_invariant {K : Subgroup G} (x : G) :
    ∀ h : G, ∀ k ∈ K, translatedIndicator (K : Set G) x (h * k)
      = translatedIndicator (K : Set G) x h := by
  intro h k hk
  by_cases hh : x⁻¹ * h ∈ K
  · rw [translatedIndicator_apply_of_mem (K := (K : Set G)) hh,
      translatedIndicator_apply_of_mem (K := (K : Set G))
        (by rw [← mul_assoc]; exact (mul_mem_cancel_right hk).mpr hh)]
  · rw [translatedIndicator_apply_of_notMem (K := (K : Set G)) hh,
      translatedIndicator_apply_of_notMem (K := (K : Set G))
        (by rw [← mul_assoc]; exact fun hmem => hh ((mul_mem_cancel_right hk).mp hmem))]

omit [TopologicalSpace G] [ContinuousMul G] in

private theorem right_invariant_apply_of_mem_coset {K : Subgroup G} {f : G → ℂ}
    (hf : ∀ y : G, ∀ k ∈ K, f (y * k) = f y) {x h : G} (hh : x⁻¹ * h ∈ K) :
    f h = f x := by
  have h1 : f (x * (x⁻¹ * h)) = f x := hf x (x⁻¹ * h) hh
  rwa [mul_inv_cancel_left] at h1

private theorem isLocallyConstant_of_right_invariant {K : Subgroup G} (hKo : IsOpen (K : Set G))
    {f : G → ℂ} (hf : ∀ y : G, ∀ k ∈ K, f (y * k) = f y) : IsLocallyConstant f := by
  refine (IsLocallyConstant.iff_exists_open f).mpr fun x => ?_
  refine ⟨(fun h => x⁻¹ * h) ⁻¹' (K : Set G), hKo.preimage (continuous_const.mul continuous_id),
    ?_, fun h hh => right_invariant_apply_of_mem_coset hf hh⟩
  simp

end TranslatedIndicator
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"

section Collapse

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V]
variable (μ : Measure G)

omit [IsTopologicalGroup G] [BorelSpace G] in

private theorem heckeSmul_smul_translatedIndicator_of_forall_smul_eq {K : Set G} (c : ℂ) (x : G) {u : V}
    (hfix : ∀ k ∈ K, k • u = u) :
    heckeSmul μ (c • translatedIndicator K x) u
      = (measureCoeff ℂ μ ((fun h => x⁻¹ * h) ⁻¹' K) * c) • x • u := by
  have hint : (fun g => (c • translatedIndicator K x) g • g • u)
      = ((fun h => x⁻¹ * h) ⁻¹' K).indicator fun _ => c • x • u := by
    funext g
    by_cases hg : x⁻¹ * g ∈ K
    · rw [Pi.smul_apply, translatedIndicator_apply_of_mem hg, smul_eq_mul, mul_one,
        Set.indicator_of_mem (Set.mem_preimage.mpr hg)]
      have hgu : g • u = x • u := by
        have h1 : g • u = (x * (x⁻¹ * g)) • u := by rw [mul_inv_cancel_left]
        rw [h1, mul_smul, hfix (x⁻¹ * g) hg]
      rw [hgu]
    · rw [Pi.smul_apply, translatedIndicator_apply_of_notMem hg, smul_eq_mul, mul_zero,
        zero_smul, Set.indicator_of_notMem (fun hmem => hg (Set.mem_preimage.mp hmem))]
  rw [heckeSmul_def, hint, finiteRangeIntegral_indicator_const, smul_smul]

private theorem mulConv_smul_translatedIndicator_of_left_invariant {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) {f₂ : G → ℂ} (hf₂K : ∀ y : G, ∀ k ∈ K, f₂ (k * y) = f₂ y)
    (c : ℂ) (x : G) :
    mulConv μ (c • translatedIndicator (K : Set G) x) f₂
      = (measureCoeff ℂ μ ((fun h => x⁻¹ * h) ⁻¹' (K : Set G)) * c) •
          fun h => f₂ (x⁻¹ * h) := by
  funext h
  have hSmeas : MeasurableSet ((fun h' : G => x⁻¹ * h') ⁻¹' (K : Set G)) :=
    (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hint : (fun g => (c • translatedIndicator (K : Set G) x) g * f₂ (g⁻¹ * h))
      = ((fun h' : G => x⁻¹ * h') ⁻¹' (K : Set G)).indicator fun _ => c * f₂ (x⁻¹ * h) := by
    funext g
    by_cases hg : x⁻¹ * g ∈ (K : Set G)
    · have hk : (x⁻¹ * g)⁻¹ ∈ K := K.inv_mem hg
      have harg : g⁻¹ * h = (x⁻¹ * g)⁻¹ * (x⁻¹ * h) := by
        rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
      rw [Pi.smul_apply, translatedIndicator_apply_of_mem hg, smul_eq_mul, mul_one,
        Set.indicator_of_mem (Set.mem_preimage.mpr hg), harg, hf₂K (x⁻¹ * h) _ hk]
    · rw [Pi.smul_apply, translatedIndicator_apply_of_notMem hg, smul_eq_mul, mul_zero,
        zero_mul, Set.indicator_of_notMem (fun hmem => hg (Set.mem_preimage.mp hmem))]
  simp only [mulConv]
  rw [hint, integral_indicator_const _ hSmeas, Pi.smul_apply, smul_eq_mul, measureCoeff_complex]
  exact Complex.real_smul.trans (mul_assoc _ _ _).symm

end Collapse
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V]
variable (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]

private theorem smul_heckeSmul_of_left_invariant {K : Subgroup G} {f₂ : G → ℂ}
    (hf₂lc : IsLocallyConstant f₂) (hf₂cs : HasCompactSupport f₂)
    (hf₂K : ∀ y : G, ∀ k ∈ K, f₂ (k * y) = f₂ y) {v : V} (hv : HasOpenStabilizer G v)
    {k : G} (hk : k ∈ K) :
    k • heckeSmul μ f₂ v = heckeSmul μ f₂ v := by
  have htrans := heckeSmul_translate_left μ hf₂lc hf₂cs hv k
  have hfun : (fun h => f₂ (k⁻¹ * h)) = f₂ := by
    funext h
    exact hf₂K h k⁻¹ (K.inv_mem hk)
  rw [hfun] at htrans
  exact htrans.symm

private theorem hasOpenStabilizer_heckeSmul_of_left_invariant {K : Subgroup G} (hKo : IsOpen (K : Set G))
    {f₂ : G → ℂ} (hf₂lc : IsLocallyConstant f₂) (hf₂cs : HasCompactSupport f₂)
    (hf₂K : ∀ y : G, ∀ k ∈ K, f₂ (k * y) = f₂ y) {v : V} (hv : HasOpenStabilizer G v) :
    HasOpenStabilizer G (heckeSmul μ f₂ v) :=
  hasOpenStabilizer_iff_exists_isOpen_subgroup.mpr
    ⟨K, hKo, fun _k hk => smul_heckeSmul_of_left_invariant μ hf₂lc hf₂cs hf₂K hv hk⟩

private theorem heckeSmul_mulConv_smul_translatedIndicator {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) {f₂ : G → ℂ} (hf₂lc : IsLocallyConstant f₂)
    (hf₂cs : HasCompactSupport f₂) (hf₂K : ∀ y : G, ∀ k ∈ K, f₂ (k * y) = f₂ y)
    {v : V} (hv : HasOpenStabilizer G v) (c : ℂ) (x : G) :
    heckeSmul μ (mulConv μ (c • translatedIndicator (K : Set G) x) f₂) v
      = heckeSmul μ (c • translatedIndicator (K : Set G) x) (heckeSmul μ f₂ v) := by

  have htlc : IsLocallyConstant fun h => f₂ (x⁻¹ * h) :=
    hf₂lc.comp_continuous (continuous_const.mul continuous_id)
  have htcs : HasCompactSupport fun h => f₂ (x⁻¹ * h) := by
    have h := hf₂cs.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
    simpa only [Homeomorph.coe_mulLeft, Function.comp_def] using h

  have hLHS : heckeSmul μ (mulConv μ (c • translatedIndicator (K : Set G) x) f₂) v
      = (measureCoeff ℂ μ ((fun h => x⁻¹ * h) ⁻¹' (K : Set G)) * c) • x • heckeSmul μ f₂ v := by
    rw [mulConv_smul_translatedIndicator_of_left_invariant μ hKo hf₂K c x,
      heckeSmul_smul_left μ htlc htcs hv _, heckeSmul_translate_left μ hf₂lc hf₂cs hv x]

  have hRHS : heckeSmul μ (c • translatedIndicator (K : Set G) x) (heckeSmul μ f₂ v)
      = (measureCoeff ℂ μ ((fun h => x⁻¹ * h) ⁻¹' (K : Set G)) * c) • x • heckeSmul μ f₂ v :=
    heckeSmul_smul_translatedIndicator_of_forall_smul_eq μ c x
      (fun k hk => smul_heckeSmul_of_left_invariant μ hf₂lc hf₂cs hf₂K hv
        (SetLike.mem_coe.mp hk))
  rw [hLHS, hRHS]

variable [T2Space G]

private theorem heckeSmul_mulConv_of_support_subset_iUnion {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) {f₂ : G → ℂ}
    (hf₂lc : IsLocallyConstant f₂) (hf₂cs : HasCompactSupport f₂)
    (hf₂K : ∀ y : G, ∀ k ∈ K, f₂ (k * y) = f₂ y) {v : V} (hv : HasOpenStabilizer G v)
    (t : Finset G) :
    ∀ f₁ : G → ℂ, HasCompactSupport f₁ → (∀ y : G, ∀ k ∈ K, f₁ (y * k) = f₁ y) →
      Function.support f₁ ⊆ (⋃ x ∈ t, (fun h => x⁻¹ * h) ⁻¹' (K : Set G)) →
      heckeSmul μ (mulConv μ f₁ f₂) v = heckeSmul μ f₁ (heckeSmul μ f₂ v) := by
  classical
  have hKclopen : IsClopen (K : Set G) := ⟨Subgroup.isClosed_of_isOpen _ hKo, hKo⟩
  have husm : HasOpenStabilizer G (heckeSmul μ f₂ v) :=
    hasOpenStabilizer_heckeSmul_of_left_invariant μ hKo hf₂lc hf₂cs hf₂K hv
  induction t using Finset.induction_on with
  | empty =>
    intro f₁ _ _ hsupp
    have hzero : f₁ = (0 : G → ℂ) := by
      funext g
      rw [Pi.zero_apply]
      by_contra hg
      simpa using hsupp (Function.mem_support.mpr hg)
    rw [hzero, mulConv_zero_left, heckeSmul_zero_left, heckeSmul_zero_left]
  | insert x s hxs ih =>
    intro f₁ hf₁cs hf₁K hsupp

    have hAlc : IsLocallyConstant (f₁ x • translatedIndicator (K : Set G) x) :=
      (isLocallyConstant_translatedIndicator hKclopen x).comp fun z => f₁ x • z
    have hAcs : HasCompactSupport (f₁ x • translatedIndicator (K : Set G) x) := by
      refine (hasCompactSupport_translatedIndicator hKc hKclopen.1 x).mono ?_
      intro h hh
      rw [Function.mem_support] at hh ⊢
      intro h0
      exact hh (by rw [Pi.smul_apply, h0, smul_zero])
    have hAK : ∀ y : G, ∀ k ∈ K, (f₁ x • translatedIndicator (K : Set G) x) (y * k)
        = (f₁ x • translatedIndicator (K : Set G) x) y := by
      intro y k hk
      rw [Pi.smul_apply, Pi.smul_apply, translatedIndicator_right_invariant x y k hk]

    have hBK : ∀ y : G, ∀ k ∈ K, (f₁ - f₁ x • translatedIndicator (K : Set G) x) (y * k)
        = (f₁ - f₁ x • translatedIndicator (K : Set G) x) y := by
      intro y k hk
      rw [Pi.sub_apply, Pi.sub_apply, hf₁K y k hk, hAK y k hk]
    have hBlc : IsLocallyConstant (f₁ - f₁ x • translatedIndicator (K : Set G) x) :=
      isLocallyConstant_of_right_invariant hKo hBK
    have hBcs : HasCompactSupport (f₁ - f₁ x • translatedIndicator (K : Set G) x) :=
      hasCompactSupport_sub hf₁cs hAcs
    have hBsupp : Function.support (f₁ - f₁ x • translatedIndicator (K : Set G) x)
        ⊆ ⋃ y ∈ s, (fun h => y⁻¹ * h) ⁻¹' (K : Set G) := by
      intro h hh
      rw [Function.mem_support] at hh

      have hnotx : x⁻¹ * h ∉ (K : Set G) := by
        intro hmem
        apply hh
        rw [Pi.sub_apply, Pi.smul_apply, translatedIndicator_apply_of_mem hmem, smul_eq_mul,
          mul_one, right_invariant_apply_of_mem_coset hf₁K hmem, sub_self]

      have hf₁h : f₁ h ≠ 0 := by
        intro h0
        apply hh
        rw [Pi.sub_apply, Pi.smul_apply, translatedIndicator_apply_of_notMem hnotx, smul_eq_mul,
          mul_zero, h0, sub_zero]
      have hmem := hsupp (Function.mem_support.mpr hf₁h)
      rcases Set.mem_iUnion₂.mp hmem with ⟨y, hy, hmemy⟩
      rcases Finset.mem_insert.mp hy with rfl | hys
      · exact absurd hmemy hnotx
      · exact Set.mem_iUnion₂.mpr ⟨y, hys, hmemy⟩

    have hCAlc : IsLocallyConstant
        (mulConv μ (f₁ x • translatedIndicator (K : Set G) x) f₂) :=
      isLocallyConstant_mulConv μ _ f₂
        (LocallyConstantStabilizer.exists_mem_nhds_one_right_invariant hf₂lc hf₂cs)
    have hCAcs : HasCompactSupport
        (mulConv μ (f₁ x • translatedIndicator (K : Set G) x) f₂) :=
      hasCompactSupport_mulConv μ hAcs hf₂cs
    have hCBlc : IsLocallyConstant
        (mulConv μ (f₁ - f₁ x • translatedIndicator (K : Set G) x) f₂) :=
      isLocallyConstant_mulConv μ _ f₂
        (LocallyConstantStabilizer.exists_mem_nhds_one_right_invariant hf₂lc hf₂cs)
    have hCBcs : HasCompactSupport
        (mulConv μ (f₁ - f₁ x • translatedIndicator (K : Set G) x) f₂) :=
      hasCompactSupport_mulConv μ hBcs hf₂cs

    have hsplit : f₁ = f₁ x • translatedIndicator (K : Set G) x
        + (f₁ - f₁ x • translatedIndicator (K : Set G) x) := by
      abel
    have hsingle := heckeSmul_mulConv_smul_translatedIndicator μ hKo hf₂lc hf₂cs
      hf₂K hv (f₁ x) x
    have hih := ih (f₁ - f₁ x • translatedIndicator (K : Set G) x) hBcs hBK hBsupp
    rw [hsplit, mulConv_add_left hAlc hAcs hBlc hBcs hf₂lc,
      heckeSmul_add_left μ hCAlc hCAcs hCBlc hCBcs hv,
      heckeSmul_add_left μ hAlc hAcs hBlc hBcs husm, hsingle, hih]

private theorem heckeSmul_mulConv {K : Subgroup G} (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) {f₁ f₂ : G → ℂ} (hf₁cs : HasCompactSupport f₁)
    (hf₁K : ∀ y : G, ∀ k ∈ K, f₁ (y * k) = f₁ y) (hf₂lc : IsLocallyConstant f₂)
    (hf₂cs : HasCompactSupport f₂) (hf₂K : ∀ y : G, ∀ k ∈ K, f₂ (k * y) = f₂ y)
    {v : V} (hv : HasOpenStabilizer G v) :
    heckeSmul μ (mulConv μ f₁ f₂) v = heckeSmul μ f₁ (heckeSmul μ f₂ v) := by
  have hcpt : IsCompact (tsupport f₁) := hf₁cs
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover
    (fun x : G => (fun h => x⁻¹ * h) ⁻¹' (K : Set G))
    (fun x => hKo.preimage (continuous_const.mul continuous_id))
    (fun g _ => Set.mem_iUnion.mpr ⟨g, by simp⟩)
  exact heckeSmul_mulConv_of_support_subset_iUnion μ hKo hKc hf₂lc hf₂cs hf₂K hv t
    f₁ hf₁cs hf₁K ((subset_tsupport f₁).trans ht)

private theorem heckeSmul_mulConv_of_exists_subgroup {f₁ f₂ : G → ℂ}
    (hf₁cs : HasCompactSupport f₁) (hf₂lc : IsLocallyConstant f₂)
    (hf₂cs : HasCompactSupport f₂) {v : V} (hv : HasOpenStabilizer G v)
    (hlevel : ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G)
      ∧ (∀ y : G, ∀ k ∈ K, f₁ (y * k) = f₁ y) ∧ (∀ y : G, ∀ k ∈ K, f₂ (k * y) = f₂ y)) :
    heckeSmul μ (mulConv μ f₁ f₂) v = heckeSmul μ f₁ (heckeSmul μ f₂ v) := by
  obtain ⟨K, hKc, hKo, hf₁K, hf₂K⟩ := hlevel
  exact heckeSmul_mulConv μ hKo hKc hf₁cs hf₁K hf₂lc hf₂cs hf₂K hv

end Main
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"

end TestFunctionAction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"
end HeckeConvolutionLaw
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"

#print axioms InvariantFunctional.apply_funLeft_inv_smul_eq
#print axioms MatrixUnitsBasis.congruenceSubgroup_integers_eq
#print axioms SigmaCompactUnits.instSigmaCompactSpaceAdicCompletion
#print axioms LanglandsTunnell.CubicInduction.map_transposeInv3_eq_self
#print axioms Character.exists_eq_pairing_of_forall_open_subgroup
#print axioms TestFunctionAction.heckeSmul_mulConv_of_exists_subgroup
#print axioms Character.exists_isLevelGraph_of_forall_trace_eq

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.localMaximalCompact3 CubicInduction.mem_localMaximalCompact3_iff CubicInduction.transposeInv3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localMaximalCompact3 mem_localMaximalCompact3_iff transposeInv3 LocalGL3"
namespace Transposition
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.InvariantFunctional P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section Place

variable (v : HeightOneSpectrum (𝓞 ℚ))

private scoped instance charZero_adicCompletion : CharZero (v.adicCompletion ℚ) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective

private scoped instance measurableSpace_localGL3 : MeasurableSpace (LocalGL3 v) :=
  borel _

private scoped instance borelSpace_localGL3 : BorelSpace (LocalGL3 v) :=
  ⟨rfl⟩

private theorem character_pullback_transposeGL3_eq (μ : Measure (LocalGL3 v)) [IsHaarMeasure μ] [μ.InnerRegular]
    (hKb : ∀ U ∈ 𝓝 (1 : LocalGL3 v), ∃ K : Subgroup (LocalGL3 v),
      IsCompact (K : Set (LocalGL3 v)) ∧ IsOpen (K : Set (LocalGL3 v)) ∧ (K : Set (LocalGL3 v)) ⊆ U)
    {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*}
    {H : testSubmodule (LocalGL3 v) ℂ →ₗ[ℂ] Module.End ℂ V} {e : ι → testSubmodule (LocalGL3 v) ℂ}
    (L : IsLevelFamily H e)
    (hc : ∀ φ ψ, H (testConv μ (testSubmodule (LocalGL3 v) ℂ)
      (fun _ hf _ hh => mulConv_mem_testSubmodule μ hKb hf hh) φ ψ) = H φ * H ψ)
    (f : testSubmodule (LocalGL3 v) ℂ) :
    character L (pullback ℂ transposeGL3 continuous_transposeGL3 transposeGL3_involutive f) =
      character L f := by
  haveI : IsMulRightInvariant μ :=
    Unimodular.isMulRightInvariant_generalLinearGroup ⟨2, two_ne_zero, by norm_num⟩ μ
  have hY : ∀ (y : Fin 3 → v.adicCompletion ℚ) (U : Set (Fin 3 → v.adicCompletion ℚ)), IsOpen U → y ∈ U →
      ∃ W : Set (Fin 3 → v.adicCompletion ℚ), IsClopen W ∧ y ∈ W ∧ W ⊆ U :=
    fun y U hU hy => ClopenBasis.exists_isClopen_subset_pi y U hU hy
  have hμ : ∀ c : ConjAct (LocalGL3 v),
      character L ∘ₗ translationAction (ConjAct (LocalGL3 v)) (LocalGL3 v) ℂ c = character L := by
    intro c
    refine LinearMap.ext fun φ => ?_
    have hφ : translationAction (ConjAct (LocalGL3 v)) (LocalGL3 v) ℂ c φ =
        ⟨fun x => (φ : LocalGL3 v → ℂ) ((ConjAct.ofConjAct c)⁻¹ * x * ConjAct.ofConjAct c),
          conj_mem_testSubmodule φ.2 (ConjAct.ofConjAct c)⟩ := by
      refine Subtype.ext ?_
      rw [coe_translationAction]
      funext x
      rw [ConjAct.smul_def, ConjAct.ofConjAct_inv, inv_inv]
    rw [LinearMap.comp_apply, hφ]
    exact character_conj_eq_testSubmodule μ hKb L hc φ (ConjAct.ofConjAct c)
  exact LinearMap.congr_fun (comp_transpose_eq_of_forall_comp_conj_eq hKb hY (character L) hμ) f

end Place
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"

end LanglandsTunnell.CubicInduction.Transposition
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"

section PairingFromCharacters

open Character InvariantFunctional FLT.SmoothAdmissibleSchurCommutant Contragredient

variable {G : Type*} [Group G] [TopologicalSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*}

section LevelFamily

variable {K : ι → Subgroup G} {π : G →* Module.End ℂ V} {H : testSubmodule G ℂ →ₗ[ℂ] Module.End ℂ V}
  {e : ι → testSubmodule G ℂ}

private theorem finiteDimensional_range_of_forall_mem_fixedVectors (hadm : IsAdmissibleRep π) {i : ι}
    (hKo : IsOpen (K i : Set G)) (hKc : IsCompact (K i : Set G))
    (hrange : ∀ v : V, H (e i) v ∈ fixedVectors π (K i)) :
    FiniteDimensional ℂ (LinearMap.range (H (e i))) := by
  haveI := hadm (K i) hKc hKo
  refine Submodule.finiteDimensional_of_le (S₂ := fixedVectors π (K i)) ?_
  rintro _ ⟨v, rfl⟩
  exact hrange v

private theorem isLevelFamily_of_absorption (hadm : IsAdmissibleRep π) (hKo : ∀ i, IsOpen (K i : Set G))
    (hKc : ∀ i, IsCompact (K i : Set G)) (hmeet : ∀ i j, ∃ k, K k ≤ K i ∧ K k ≤ K j)
    (hcof : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ i, K i ≤ U)
    (conv : testSubmodule G ℂ → testSubmodule G ℂ → testSubmodule G ℂ)
    (hc : ∀ φ ψ, H (conv φ ψ) = H φ * H ψ)
    (hidem : ∀ i (v : V), H (e i) (H (e i) v) = H (e i) v)
    (hrange : ∀ i (v : V), H (e i) v ∈ fixedVectors π (K i))
    (habsL : ∀ i (φ : testSubmodule G ℂ), (∀ k ∈ K i, ∀ x, (φ : G → ℂ) (k * x) = (φ : G → ℂ) x) → conv (e i) φ = φ)
    (habsR : ∀ i (φ : testSubmodule G ℂ), (∀ k ∈ K i, ∀ x, (φ : G → ℂ) (x * k) = (φ : G → ℂ) x) → conv φ (e i) = φ)
    (hinvK : ∀ i, (∀ k ∈ K i, ∀ x, (e i : G → ℂ) (k * x) = (e i : G → ℂ) x) ∧
      (∀ k ∈ K i, ∀ x, (e i : G → ℂ) (x * k) = (e i : G → ℂ) x))
    (hbi : ∀ φ : testSubmodule G ℂ, ∃ U : Subgroup G, IsOpen (U : Set G) ∧
      (∀ k ∈ U, ∀ x, (φ : G → ℂ) (k * x) = (φ : G → ℂ) x) ∧
      (∀ k ∈ U, ∀ x, (φ : G → ℂ) (x * k) = (φ : G → ℂ) x)) :
    IsLevelFamily H e where
  idem i := show H (e i) * H (e i) = H (e i) from LinearMap.ext (hidem i)
  finite i := finiteDimensional_range_of_forall_mem_fixedVectors hadm (hKo i) (hKc i) (hrange i)
  directed i j := by
    obtain ⟨k, hki, hkj⟩ := hmeet i j
    refine ⟨k, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [← hc, habsL k (e i) fun x hx y => (hinvK i).1 x (hki hx) y]
    · rw [← hc, habsR k (e i) fun x hx y => (hinvK i).2 x (hki hx) y]
    · rw [← hc, habsL k (e j) fun x hx y => (hinvK j).1 x (hkj hx) y]
    · rw [← hc, habsR k (e j) fun x hx y => (hinvK j).2 x (hkj hx) y]
  exhaustive φ := by
    obtain ⟨U, hUo, hl, hr⟩ := hbi φ
    obtain ⟨i, hiU⟩ := hcof U hUo
    refine ⟨i, ?_⟩
    have h := map_conv_level (e := e) conv hc i φ
    rw [habsR i φ fun k hk x => hr k (hiU hk) x, habsL i φ fun k hk x => hl k (hiU hk) x] at h
    exact h

private theorem exists_level_apply_eq_self (hsm : IsSmoothRep π)
    (hcof : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ i, K i ≤ U)
    (hfix : ∀ i (v : V), (∀ k ∈ K i, π k v = v) → H (e i) v = v) (v : V) : ∃ i, H (e i) v = v := by
  obtain ⟨i, hi⟩ := hcof (repStabilizer π v) (hsm v)
  exact ⟨i, hfix i v fun k hk => (mem_repStabilizer π).mp (hi hk)⟩

private theorem isIrreducible_of_isIrreducibleRep (hirr : IsIrreducibleRep π) (hsm : IsSmoothRep π)
    (hcof : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ i, K i ≤ U)
    (hfix : ∀ i (v : V), (∀ k ∈ K i, π k v = v) → H (e i) v = v)
    (lam : G → testSubmodule G ℂ → testSubmodule G ℂ)
    (hC1 : ∀ (g : G) (φ : testSubmodule G ℂ) (v : V), π g (H φ v) = H (lam g φ) v) :
    Character.IsIrreducible H := by
  obtain ⟨⟨v₀, hv₀⟩, hW⟩ := hirr
  refine ⟨nontrivial_of_ne v₀ 0 hv₀, fun N hN => hW N fun g v hv => ?_⟩
  obtain ⟨i, hi⟩ := exists_level_apply_eq_self hsm hcof hfix v
  rw [← hi, hC1 g (e i) v]
  exact hN (lam g (e i)) v hv

end LevelFamily
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

section Twist

variable {S : Type*} [AddCommGroup S] [Module ℂ S] {H : S →ₗ[ℂ] Module.End ℂ V} {e : ι → S}
  {T : S →ₗ[ℂ] S}

private theorem isLevelFamily_comp (L : IsLevelFamily H e) (hTe : ∀ i, T (e i) = e i) :
    IsLevelFamily (H ∘ₗ T) e where
  idem i := by simpa only [LinearMap.comp_apply, hTe] using L.idem i
  finite i := by
    have h := L.finite i
    rw [← hTe i] at h
    exact h
  directed i j := by simpa only [LinearMap.comp_apply, hTe] using L.directed i j
  exhaustive φ := by
    obtain ⟨i, hi⟩ := L.exhaustive (T φ)
    refine ⟨i, ?_⟩
    simpa only [HasLevel, LinearMap.comp_apply, hTe] using hi

private theorem comp_conv (conv : S → S → S) (hc : ∀ φ ψ, H (conv φ ψ) = H φ * H ψ)
    (hTc : ∀ φ ψ, T (conv φ ψ) = conv (T φ) (T ψ)) (φ ψ : S) :
    (H ∘ₗ T) (conv φ ψ) = (H ∘ₗ T) φ * (H ∘ₗ T) ψ := by
  simp only [LinearMap.comp_apply, hTc, hc]

private theorem isIrreducible_comp (hTT : ∀ φ, T (T φ) = φ) (hirr : Character.IsIrreducible H) :
    Character.IsIrreducible (H ∘ₗ T) := by
  obtain ⟨hV, hirr⟩ := hirr
  refine ⟨hV, fun N hN => hirr N fun φ v hv => ?_⟩
  have h := hN (T φ) v hv
  rwa [LinearMap.comp_apply, hTT] at h

private theorem rankTrace_congr_submodule {A : Module.End ℂ V} {U U' : Submodule ℂ V} (hU : U = U')
    (hA : ∀ x, A x ∈ U) (hA' : ∀ x, A x ∈ U') [FiniteDimensional ℂ U] [FiniteDimensional ℂ U'] :
    rankTrace A U hA = rankTrace A U' hA' := by
  subst hU
  rfl

private theorem character_comp (L : IsLevelFamily H e) (hTe : ∀ i, T (e i) = e i) (φ : S) :
    character (isLevelFamily_comp L hTe) φ = character L (T φ) := by
  obtain ⟨i, hi⟩ := L.exhaustive (T φ)
  have hi' : HasLevel (H ∘ₗ T) e φ i := by
    simpa only [HasLevel, LinearMap.comp_apply, hTe] using hi
  rw [character_eq_rankTrace (isLevelFamily_comp L hTe) hi', character_eq_rankTrace L hi]
  have hrange : LinearMap.range ((H ∘ₗ T) (e i)) = LinearMap.range (H (e i)) := by
    rw [LinearMap.comp_apply, hTe]
  haveI := (isLevelFamily_comp L hTe).finite i
  haveI := L.finite i
  exact rankTrace_congr_submodule hrange hi'.apply_mem_range hi.apply_mem_range

end Twist
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

section Assembly

variable {K : ι → Subgroup G} [Nonempty ι]

private theorem exists_pairing_of_character_comp_eq (τ : G →* G) (hττ : ∀ z, τ (τ z) = z)
    {π : G →* Module.End ℂ V} (hirr : IsIrreducibleRep π) (hsm : IsSmoothRep π)
    (hcof : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ i, K i ≤ U)
    {H : testSubmodule G ℂ →ₗ[ℂ] Module.End ℂ V} {e : ι → testSubmodule G ℂ} (L : IsLevelFamily H e)
    (conv : testSubmodule G ℂ → testSubmodule G ℂ → testSubmodule G ℂ)
    (hc : ∀ φ ψ, H (conv φ ψ) = H φ * H ψ)
    (lam rho : G → testSubmodule G ℂ → testSubmodule G ℂ)
    (hlam : ∀ (g : G) (φ : testSubmodule G ℂ) (x : G), (lam g φ : G → ℂ) x = (φ : G → ℂ) (g⁻¹ * x))
    (hrho : ∀ (g : G) (φ : testSubmodule G ℂ) (x : G), (rho g φ : G → ℂ) x = (φ : G → ℂ) (x * g⁻¹))
    (T inv : testSubmodule G ℂ →ₗ[ℂ] testSubmodule G ℂ)
    (hT : ∀ (φ : testSubmodule G ℂ) (x : G), (T φ : G → ℂ) x = (φ : G → ℂ) (τ x))
    (hinv : ∀ (φ : testSubmodule G ℂ) (x : G), (inv φ : G → ℂ) x = (φ : G → ℂ) x⁻¹)
    (hTc : ∀ φ ψ, T (conv φ ψ) = conv (T φ) (T ψ))
    (hinvc : ∀ φ ψ, inv (conv φ ψ) = conv (inv ψ) (inv φ))
    (hTe : ∀ i, T (e i) = e i) (hinv_e : ∀ i, inv (e i) = e i)
    (hC1 : ∀ (g : G) (φ : testSubmodule G ℂ) (v : V), π g (H φ v) = H (lam g φ) v)
    (hC2 : ∀ (g : G) (φ : testSubmodule G ℂ) (v : V), H φ (π g v) = H (rho g φ) v)
    (hfix : ∀ i (v : V), (∀ k ∈ K i, π k v = v) → H (e i) v = v)
    (hlev : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ i : ι, ∀ l : Module.Dual ℂ V,
      (∀ u ∈ U, ∀ x : V, l (π u x) = l x) → l ∘ₗ H (e i) = l)
    (hchar : ∀ φ, character L (T φ) = character L (inv φ)) :
    ∃ P : V →ₗ[ℂ] V →ₗ[ℂ] ℂ,
      (∀ (g : G) (x y : V), P (π g x) (π (τ g) y) = P x y) ∧
      (∀ y : V, (∀ x : V, P x y = 0) → y = 0) ∧
      (∀ l : V →ₗ[ℂ] ℂ, (∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, ∀ x : V, l (π u x) = l x) →
        ∃ y : V, ∀ x : V, l x = P x y) := by

  have hTT : ∀ φ, T (T φ) = φ := fun φ => Subtype.ext (funext fun x => by rw [hT, hT, hττ])
  have hinv_inv : ∀ φ, inv (inv φ) = φ := fun φ => Subtype.ext (funext fun x => by rw [hinv, hinv, inv_inv])

  have hirrH : Character.IsIrreducible H :=
    isIrreducible_of_isIrreducibleRep hirr hsm hcof hfix lam hC1
  have hne : ∃ i, LinearMap.range (H (e i)) ≠ ⊥ := by
    obtain ⟨⟨v₀, hv₀⟩, -⟩ := hirr
    obtain ⟨i, hi⟩ := exists_level_apply_eq_self hsm hcof hfix v₀
    exact ⟨i, (Submodule.ne_bot_iff _).mpr ⟨v₀, LinearMap.mem_range.mpr ⟨v₀, hi⟩, hv₀⟩⟩
  obtain ⟨i₀, hi₀⟩ := hne
  have hne' : LinearMap.range ((H ∘ₗ T) (e i₀)) ≠ ⊥ := by rwa [LinearMap.comp_apply, hTe]
  have hcharT : character (isLevelFamily_comp L hTe) =
      character (isLevelFamily_heckeDual (L := L) (inv := inv) hinv_e) := by
    refine LinearMap.ext fun φ => ?_
    rw [character_comp L hTe φ, character_heckeDual (L := L) hinv_e φ, hchar φ]
  obtain ⟨f, hf⟩ := exists_equiv_of_character_eq (isLevelFamily_comp L hTe)
    (isLevelFamily_heckeDual (L := L) (inv := inv) hinv_e) conv (comp_conv conv hc hTc)
    (heckeDualAction_conv (L := L) (inv := inv) conv hc hinvc) (isIrreducible_comp hTT hirrH)
    (isIrreducible_heckeDual (L := L) (inv := inv) hinv_inv hinv_e hirrH ⟨i₀, hi₀⟩) hne' hcharT

  set j : V →ₗ[ℂ] Module.Dual ℂ V := (heckeDual H L).subtype ∘ₗ (f : V →ₗ[ℂ] heckeDual H L) with hj
  have hj_apply : ∀ (x y : V), pairingOf j x y = (f y : Module.Dual ℂ V) x := fun x y => rfl
  have hj_inj : Function.Injective j := (heckeDual H L).injective_subtype.comp f.injective

  have hf' : ∀ (φ : testSubmodule G ℂ) (y x : V),
      (f (H (T φ) y) : Module.Dual ℂ V) x = (f y : Module.Dual ℂ V) (H (inv φ) x) := by
    intro φ y x
    have h := congrArg (fun m : heckeDual H L => (m : Module.Dual ℂ V) x) (hf φ y)
    simpa only [LinearMap.comp_apply, heckeDualAction_apply_coe] using h
  refine ⟨pairingOf j, fun g x y => ?_, fun y hy => hj_inj ?_, fun l ⟨U, hUo, hl⟩ => ?_⟩
  ·
    obtain ⟨i, hi⟩ := exists_level_apply_eq_self hsm hcof hfix y
    have habs : ∀ z : V, (f y : Module.Dual ℂ V) (H (e i) z) = (f y : Module.Dual ℂ V) z := by
      intro z
      have h := hf' (e i) y z
      rw [hTe, hi, hinv_e] at h
      exact h.symm

    have htoken : rho g (inv (T (lam (τ g) (e i)))) = e i := by
      refine Subtype.ext (funext fun z => ?_)
      have heT : ∀ w, (e i : G → ℂ) (τ w) = (e i : G → ℂ) w := fun w => by
        have h := congrArg (fun ψ : testSubmodule G ℂ => (ψ : G → ℂ) w) (hTe i)
        simpa only [hT] using h
      have heinv : ∀ w, (e i : G → ℂ) w⁻¹ = (e i : G → ℂ) w := fun w => by
        have h := congrArg (fun ψ : testSubmodule G ℂ => (ψ : G → ℂ) w) (hinv_e i)
        simpa only [hinv] using h
      have harg : (τ g)⁻¹ * τ (z * g⁻¹)⁻¹ = τ z⁻¹ := by
        rw [mul_inv_rev, inv_inv, ← map_inv, ← map_mul, inv_mul_cancel_left]
      rw [hrho, hinv, hT, hlam, harg, heT, heinv]
    calc pairingOf j (π g x) (π (τ g) y)
        = (f (π (τ g) y) : Module.Dual ℂ V) (π g x) := hj_apply _ _
      _ = (f (H (T (T (lam (τ g) (e i)))) y) : Module.Dual ℂ V) (π g x) := by
          rw [hTT, ← hC1, hi]
      _ = (f y : Module.Dual ℂ V) (H (inv (T (lam (τ g) (e i)))) (π g x)) := hf' _ _ _
      _ = (f y : Module.Dual ℂ V) (H (e i) x) := by rw [hC2, htoken]
      _ = (f y : Module.Dual ℂ V) x := habs x
      _ = pairingOf j x y := (hj_apply _ _).symm
  ·
    refine LinearMap.ext fun x => ?_
    have h := hy x
    rw [hj_apply] at h
    simpa only [hj, LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, map_zero,
      LinearMap.zero_apply] using h
  ·
    obtain ⟨i, hi⟩ := hlev U hUo
    have hmem : l ∈ heckeDual H L := (mem_heckeDual_iff H L).mpr ⟨i, hi l hl⟩
    refine ⟨f.symm ⟨l, hmem⟩, fun x => ?_⟩
    rw [hj_apply, LinearEquiv.apply_symm_apply]

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

end PairingFromCharacters
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.localMaximalCompact3 CubicInduction.mem_localMaximalCompact3_iff CubicInduction.transposeInv3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localMaximalCompact3 mem_localMaximalCompact3_iff transposeInv3 LocalGL3"
namespace Transposition
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.InvariantFunctional P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character"

section StableLevels

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (τ : G →* G) (hτc : Continuous τ)
  (hττ : Function.Involutive τ)

private def stablePart (K : Subgroup G) : Subgroup G :=
  K ⊓ K.comap τ

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem mem_stablePart {K : Subgroup G} {g : G} : g ∈ stablePart τ K ↔ g ∈ K ∧ τ g ∈ K :=
  Iff.rfl

include hττ in
private theorem tau_mem_stablePart_iff (K : Subgroup G) (g : G) : τ g ∈ stablePart τ K ↔ g ∈ stablePart τ K := by
  rw [mem_stablePart, mem_stablePart, hττ g]
  exact and_comm

omit [IsTopologicalGroup G] in
include hτc in
private theorem isOpen_stablePart {K : Subgroup G} (hK : IsOpen (K : Set G)) : IsOpen (stablePart τ K : Set G) :=
  hK.inter (hK.preimage hτc)

include hτc in
private theorem isCompact_stablePart {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) :
    IsCompact (stablePart τ K : Set G) :=
  hKc.inter_right ((Subgroup.isClosed_of_isOpen K hKo).preimage hτc)

include hτc hττ in

private theorem exists_isCompact_isOpen_stable_le
    (hKb : ∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ (K : Set G) ⊆ U)
    (U : Subgroup G) (hU : IsOpen (U : Set G)) :
    ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ (∀ g, τ g ∈ K ↔ g ∈ K) ∧ K ≤ U := by
  obtain ⟨K, hKc, hKo, hKU⟩ := hKb U (hU.mem_nhds U.one_mem)
  exact ⟨stablePart τ K, isCompact_stablePart τ hτc hKc hKo, isOpen_stablePart τ hτc hKo,
    tau_mem_stablePart_iff τ hττ K, fun g hg => hKU ((mem_stablePart τ).1 hg).1⟩

private def StableLevel : Type _ :=
  {K : Subgroup G // IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ ∀ g, τ g ∈ K ↔ g ∈ K}

private def StableLevel.inf (i j : StableLevel τ) : StableLevel τ :=
  ⟨i.1 ⊓ j.1, i.2.1.inter_right (Subgroup.isClosed_of_isOpen j.1 j.2.2.1), i.2.2.1.inter j.2.2.1,
    fun g => and_congr (i.2.2.2 g) (j.2.2.2 g)⟩

private theorem StableLevel.inf_le_left (i j : StableLevel τ) : (StableLevel.inf τ i j).1 ≤ i.1 :=
  _root_.inf_le_left

private theorem StableLevel.inf_le_right (i j : StableLevel τ) : (StableLevel.inf τ i j).1 ≤ j.1 :=
  _root_.inf_le_right

include hτc hττ in
private theorem StableLevel.exists_le
    (hKb : ∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ (K : Set G) ⊆ U)
    (U : Subgroup G) (hU : IsOpen (U : Set G)) : ∃ i : StableLevel τ, i.1 ≤ U := by
  obtain ⟨K, hKc, hKo, hKτ, hKU⟩ := exists_isCompact_isOpen_stable_le τ hτc hττ hKb U hU
  exact ⟨⟨K, hKc, hKo, hKτ⟩, hKU⟩

include hτc hττ in
private theorem StableLevel.nonempty
    (hKb : ∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ (K : Set G) ⊆ U) :
    Nonempty (StableLevel τ) :=
  let ⟨i, _⟩ := StableLevel.exists_le τ hτc hττ hKb ⊤ isOpen_univ
  ⟨i⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in

private theorem indicator_comp_tau_of_stable {K : Subgroup G} (hK : ∀ g, τ g ∈ K ↔ g ∈ K) (c : ℂ) (g : G) :
    (c • (K : Set G).indicator (1 : G → ℂ)) (τ g) = (c • (K : Set G).indicator (1 : G → ℂ)) g := by
  by_cases hg : g ∈ K
  · have hτg : τ g ∈ (K : Set G) := (hK g).2 hg
    have hg' : g ∈ (K : Set G) := hg
    rw [Pi.smul_apply, Pi.smul_apply, Set.indicator_of_mem hτg, Set.indicator_of_mem hg']
    rfl
  · have hτg : τ g ∉ (K : Set G) := fun h => hg ((hK g).1 h)
    have hg' : g ∉ (K : Set G) := hg
    rw [Pi.smul_apply, Pi.smul_apply, Set.indicator_of_notMem hτg, Set.indicator_of_notMem hg']

omit [TopologicalSpace G] [IsTopologicalGroup G] in

private theorem indicator_inv_of_subgroup (K : Subgroup G) (c : ℂ) (g : G) :
    (c • (K : Set G).indicator (1 : G → ℂ)) g⁻¹ = (c • (K : Set G).indicator (1 : G → ℂ)) g := by
  by_cases hg : g ∈ K
  · have hig : g⁻¹ ∈ (K : Set G) := K.inv_mem hg
    have hg' : g ∈ (K : Set G) := hg
    rw [Pi.smul_apply, Pi.smul_apply, Set.indicator_of_mem hig, Set.indicator_of_mem hg']
    rfl
  · have hig : g⁻¹ ∉ (K : Set G) := fun h => hg (K.inv_mem_iff.1 h)
    have hg' : g ∉ (K : Set G) := hg
    rw [Pi.smul_apply, Pi.smul_apply, Set.indicator_of_notMem hig, Set.indicator_of_notMem hg']

end StableLevels
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

section TransposeInverse

variable {F : Type} [Field F]

private def transposeInv3Hom : GL (Fin 3) F →* GL (Fin 3) F where
  toFun := transposeInv3
  map_one' := TransposeTwist.transposeInv3_one
  map_mul' := TransposeTwist.transposeInv3_mul

private theorem transposeInv3Hom_apply (g : GL (Fin 3) F) : transposeInv3Hom g = transposeInv3 g :=
  rfl

private theorem transposeInv3Hom_involutive : Function.Involutive (transposeInv3Hom (F := F)) :=
  TransposeTwist.transposeInv3_transposeInv3

variable [TopologicalSpace F]

private theorem continuous_transposeInv3Hom : Continuous (transposeInv3Hom (F := F)) :=
  TransposeTwist.continuous_transposeInv3

end TransposeInverse
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

section Bridge

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem character_pullback_transposeInv3_eq (μ : Measure (LocalGL3 v)) [IsHaarMeasure μ] [μ.InnerRegular]
    (hKb : ∀ U ∈ 𝓝 (1 : LocalGL3 v), ∃ K : Subgroup (LocalGL3 v),
      IsCompact (K : Set (LocalGL3 v)) ∧ IsOpen (K : Set (LocalGL3 v)) ∧ (K : Set (LocalGL3 v)) ⊆ U)
    {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*}
    {H : testSubmodule (LocalGL3 v) ℂ →ₗ[ℂ] Module.End ℂ V} {e : ι → testSubmodule (LocalGL3 v) ℂ}
    (L : IsLevelFamily H e)
    (hc : ∀ φ ψ, H (testConv μ (testSubmodule (LocalGL3 v) ℂ)
      (fun _ hf _ hh => mulConv_mem_testSubmodule μ hKb hf hh) φ ψ) = H φ * H ψ)
    (φ : testSubmodule (LocalGL3 v) ℂ) :
    character L (pullback ℂ (transposeInv3Hom (F := v.adicCompletion ℚ)) continuous_transposeInv3Hom
        transposeInv3Hom_involutive φ) =
      character L (pullback ℂ (fun g : LocalGL3 v => g⁻¹) continuous_inv inv_involutive φ) := by
  have key : pullback ℂ (transposeInv3Hom (F := v.adicCompletion ℚ)) continuous_transposeInv3Hom
      transposeInv3Hom_involutive φ =
        pullback ℂ transposeGL3 continuous_transposeGL3 transposeGL3_involutive
          (pullback ℂ (fun g : LocalGL3 v => g⁻¹) continuous_inv inv_involutive φ) := by
    refine Subtype.ext (funext fun g => ?_)
    show (φ : LocalGL3 v → ℂ) (transposeInv3 g) = (φ : LocalGL3 v → ℂ) (transposeGL3 g)⁻¹
    rw [transposeGL3_apply, inv_inv]
  rw [key]
  exact character_pullback_transposeGL3_eq v μ hKb L hc _

end Bridge
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

end LanglandsTunnell.CubicInduction.Transposition
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.localMaximalCompact3 CubicInduction.mem_localMaximalCompact3_iff CubicInduction.transposeInv3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localMaximalCompact3 mem_localMaximalCompact3_iff transposeInv3 LocalGL3"
namespace Transposition
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open MeasureTheory MeasureTheory.Measure Topology TopologicalSpace
open InvariantFunctional FLT.SmoothAdmissibleSchurCommutant TestFunctionAction

section HeckeOperator

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] (π : G →* Module.End ℂ V)

private abbrev repAction : DistribMulAction G V :=
  DistribMulAction.compHom V π

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
private theorem repAction_smulCommClass : letI := repAction π; SMulCommClass G ℂ V := by
  letI := repAction π
  exact ⟨fun g c x => map_smul (π g) c x⟩

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in

private theorem hasOpenStabilizer_of_isSmoothRep (hsm : IsSmoothRep π) (x : V) :
    letI := repAction π; HasOpenStabilizer G x := by
  letI := repAction π
  show IsOpen ((MulAction.stabilizer G x : Subgroup G) : Set G)
  have h : ((MulAction.stabilizer G x : Subgroup G) : Set G) = (repStabilizer π x : Set G) :=
    Set.ext fun _ => Iff.rfl
  rw [h]
  exact hsm x

variable (hsm : IsSmoothRep π) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

private noncomputable def heckeOp : testSubmodule G ℂ →ₗ[ℂ] Module.End ℂ V :=
  letI := repAction π
  haveI := repAction_smulCommClass π
  { toFun := fun φ =>
      { toFun := fun x => heckeSmul μ (φ : G → ℂ) x
        map_add' := fun x y => heckeSmul_add_right μ (mem_testSubmodule.mp φ.2).1 (mem_testSubmodule.mp φ.2).2
          (hasOpenStabilizer_of_isSmoothRep π hsm x) (hasOpenStabilizer_of_isSmoothRep π hsm y)
        map_smul' := fun c x => heckeSmul_smul_right μ (mem_testSubmodule.mp φ.2).1 (mem_testSubmodule.mp φ.2).2
          (hasOpenStabilizer_of_isSmoothRep π hsm x) c }
    map_add' := fun φ ψ => by
      refine LinearMap.ext fun x => ?_
      show heckeSmul μ ((φ : G → ℂ) + (ψ : G → ℂ)) x = heckeSmul μ (φ : G → ℂ) x + heckeSmul μ (ψ : G → ℂ) x
      exact heckeSmul_add_left μ (mem_testSubmodule.mp φ.2).1 (mem_testSubmodule.mp φ.2).2
        (mem_testSubmodule.mp ψ.2).1 (mem_testSubmodule.mp ψ.2).2 (hasOpenStabilizer_of_isSmoothRep π hsm x)
    map_smul' := fun c φ => by
      refine LinearMap.ext fun x => ?_
      show heckeSmul μ (c • (φ : G → ℂ)) x = c • heckeSmul μ (φ : G → ℂ) x
      exact heckeSmul_smul_left μ (mem_testSubmodule.mp φ.2).1 (mem_testSubmodule.mp φ.2).2
        (hasOpenStabilizer_of_isSmoothRep π hsm x) c }

private theorem heckeOp_apply (φ : testSubmodule G ℂ) (x : V) :
    heckeOp π hsm μ φ x = (letI := repAction π; heckeSmul μ (φ : G → ℂ) x) :=
  rfl

private def rightTranslate (k : G) (φ : testSubmodule G ℂ) : testSubmodule G ℂ :=
  ⟨fun x => (φ : G → ℂ) (x * k⁻¹), mem_testSubmodule.mpr
    ⟨(mem_testSubmodule.mp φ.2).1.comp_continuous (continuous_mul_const k⁻¹),
      (mem_testSubmodule.mp φ.2).2.comp_homeomorph (Homeomorph.mulRight k⁻¹)⟩⟩

omit [MeasurableSpace G] [BorelSpace G] in
private theorem rightTranslate_apply (k : G) (φ : testSubmodule G ℂ) (x : G) :
    (rightTranslate k φ : G → ℂ) x = (φ : G → ℂ) (x * k⁻¹) :=
  rfl

private theorem rep_heckeOp_apply [μ.IsMulLeftInvariant] (g : G) (φ : testSubmodule G ℂ) (x : V) :
    π g (heckeOp π hsm μ φ x) = heckeOp π hsm μ (translationAction G G ℂ g φ) x := by
  letI := repAction π
  haveI := repAction_smulCommClass π
  show π g (heckeSmul μ (φ : G → ℂ) x) = heckeSmul μ (fun h => (φ : G → ℂ) (g⁻¹ * h)) x
  exact (heckeSmul_translate_left μ (mem_testSubmodule.mp φ.2).1 (mem_testSubmodule.mp φ.2).2
    (hasOpenStabilizer_of_isSmoothRep π hsm x) g).symm

private theorem heckeOp_apply_rep [μ.IsMulRightInvariant] (k : G) (φ : testSubmodule G ℂ) (x : V) :
    heckeOp π hsm μ φ (π k x) = heckeOp π hsm μ (rightTranslate k φ) x := by
  letI := repAction π
  haveI := repAction_smulCommClass π
  show heckeSmul μ (φ : G → ℂ) (k • x) = heckeSmul μ (fun h => (φ : G → ℂ) (h * k⁻¹)) x
  exact heckeSmul_smul_vector μ (mem_testSubmodule.mp φ.2).1 (mem_testSubmodule.mp φ.2).2
    (hasOpenStabilizer_of_isSmoothRep π hsm x) k

private noncomputable def level (K : Subgroup G) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) :
    testSubmodule G ℂ :=
  ⟨heckeIdempotent ℂ μ (K : Set G), mem_testSubmodule.mpr
    ⟨isLocallyConstant_heckeIdempotent ℂ μ ⟨Subgroup.isClosed_of_isOpen K hKo, hKo⟩,
      hasCompactSupport_heckeIdempotent ℂ μ hKc (Subgroup.isClosed_of_isOpen K hKo)⟩⟩

omit [BorelSpace G] [IsFiniteMeasureOnCompacts μ] in
private theorem coe_level (K : Subgroup G) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) :
    (level μ K hKc hKo : G → ℂ) = heckeIdempotent ℂ μ (K : Set G) :=
  rfl

private theorem coe_level_eq_smul_indicator (K : Subgroup G) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) :
    (level μ K hKc hKo : G → ℂ) = ((μ.real (K : Set G) : ℂ))⁻¹ • (K : Set G).indicator (1 : G → ℂ) := by
  funext g
  rw [coe_level, Pi.smul_apply, smul_eq_mul]
  by_cases hg : g ∈ (K : Set G)
  · rw [heckeIdempotent_apply_of_mem ℂ μ hg, Set.indicator_of_mem hg, Pi.one_apply, mul_one, measureReal_def,
      Complex.coe_algebraMap, Complex.ofReal_inv]
  · rw [heckeIdempotent_apply_of_notMem ℂ μ hg, Set.indicator_of_notMem hg, mul_zero]

variable [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure]

private theorem heckeOp_level_idem (K : Subgroup G) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (x : V) :
    heckeOp π hsm μ (level μ K hKc hKo) (heckeOp π hsm μ (level μ K hKc hKo) x) =
      heckeOp π hsm μ (level μ K hKc hKo) x := by
  letI := repAction π
  haveI := repAction_smulCommClass π
  exact heckeSmul_heckeIdempotent_idem μ hKo hKc (hKo.measure_ne_zero μ ⟨1, K.one_mem⟩)
    (hasOpenStabilizer_of_isSmoothRep π hsm x)

omit [μ.IsOpenPosMeasure] in

private theorem heckeOp_level_mem_fixedVectors (K : Subgroup G) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (x : V) :
    heckeOp π hsm μ (level μ K hKc hKo) x ∈ fixedVectors π K := by
  letI := repAction π
  haveI := repAction_smulCommClass π
  exact (mem_fixedPointsSubmodule_iff (𝕜 := ℂ)).mp
    (heckeSmul_heckeIdempotent_mem_fixedPoints μ hKo hKc (hasOpenStabilizer_of_isSmoothRep π hsm x))

omit [μ.IsMulLeftInvariant] in

private theorem heckeOp_level_apply_of_forall (K : Subgroup G) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {x : V} (hx : ∀ k ∈ K, π k x = x) :
    heckeOp π hsm μ (level μ K hKc hKo) x = x := by
  letI := repAction π
  haveI := repAction_smulCommClass π
  exact heckeSmul_heckeIdempotent_of_forall_smul_eq μ (hKo.measure_ne_zero μ ⟨1, K.one_mem⟩)
    hKc.measure_lt_top.ne hx

end HeckeOperator
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

end LanglandsTunnell.CubicInduction.Transposition
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.localMaximalCompact3 CubicInduction.mem_localMaximalCompact3_iff CubicInduction.transposeInv3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localMaximalCompact3 mem_localMaximalCompact3_iff transposeInv3 LocalGL3"
namespace Transposition
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.InvariantFunctional P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character FLT.SmoothAdmissibleSchurCommutant P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.MulConvolution"

section LevelMeasure

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) [μ.IsOpenPosMeasure]
  [IsFiniteMeasureOnCompacts μ]

private theorem measureReal_coe_ne_zero (K : Subgroup G) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) :
    μ.real (K : Set G) ≠ 0 := by
  rw [measureReal_def, ENNReal.toReal_ne_zero]
  exact ⟨hKo.measure_ne_zero μ ⟨1, K.one_mem⟩, hKc.measure_lt_top.ne⟩

end LevelMeasure
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

section Place

variable (v : HeightOneSpectrum (𝓞 ℚ))

private abbrev PlaceLevel : Type :=
  StableLevel (transposeInv3Hom (F := v.adicCompletion ℚ))

private noncomputable abbrev placeConv (μ : Measure (LocalGL3 v)) :
    testSubmodule (LocalGL3 v) ℂ → testSubmodule (LocalGL3 v) ℂ → testSubmodule (LocalGL3 v) ℂ :=
  testConv μ (testSubmodule (LocalGL3 v) ℂ) fun _ hf _ hh =>
    mulConv_mem_testSubmodule μ (MatrixUnitsBasis.exists_compact_open_subgroup_subset_adicCompletion ℚ v) hf hh

private theorem exists_pairing_of_conv_of_level (μ : Measure (LocalGL3 v)) [IsHaarMeasure μ] [μ.InnerRegular]
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : LocalGL3 v →* Module.End ℂ V)
    (hirr : IsIrreducibleRep π) (hsm : IsSmoothRep π) (hadm : IsAdmissibleRep π)
    (hc : ∀ φ ψ, heckeOp π hsm μ (placeConv v μ φ ψ) = heckeOp π hsm μ φ * heckeOp π hsm μ ψ)
    (hlev : ∀ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) → ∃ i : PlaceLevel v,
      ∀ l : Module.Dual ℂ V, (∀ u ∈ U, ∀ x : V, l (π u x) = l x) →
        l ∘ₗ heckeOp π hsm μ (level μ i.1 i.2.1 i.2.2.1) = l) :
    ∃ P : V →ₗ[ℂ] V →ₗ[ℂ] ℂ,
      (∀ (g : LocalGL3 v) (x y : V), P (π g x) (π (transposeInv3 g) y) = P x y) ∧
      (∀ y : V, (∀ x : V, P x y = 0) → y = 0) ∧
      (∀ L : V →ₗ[ℂ] ℂ,
        (∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧ ∀ u ∈ U, ∀ x : V, L (π u x) = L x) →
        ∃ y : V, ∀ x : V, L x = P x y) := by
  have hKb := MatrixUnitsBasis.exists_compact_open_subgroup_subset_adicCompletion ℚ v
  haveI : μ.IsMulRightInvariant :=
    Unimodular.isMulRightInvariant_generalLinearGroup ⟨2, two_ne_zero, by norm_num⟩ μ
  have hτc : Continuous (transposeInv3Hom (F := v.adicCompletion ℚ)) := continuous_transposeInv3Hom
  have hττ : Function.Involutive (transposeInv3Hom (F := v.adicCompletion ℚ)) := transposeInv3Hom_involutive
  haveI : Nonempty (PlaceLevel v) := StableLevel.nonempty _ hτc hττ hKb
  have hμτ : Measure.map (transposeInv3Hom (F := v.adicCompletion ℚ)) μ = μ := map_transposeInv3_eq_self μ
  have h0 : ∀ i : PlaceLevel v, μ.real (i.1 : Set (LocalGL3 v)) ≠ 0 := fun i =>
    measureReal_coe_ne_zero μ i.1 i.2.1 i.2.2.1

  have L : IsLevelFamily (heckeOp π hsm μ) fun i : PlaceLevel v => level μ i.1 i.2.1 i.2.2.1 :=
    isLevelFamily_of_absorption (K := fun i : PlaceLevel v => i.1) hadm (fun i => i.2.2.1) (fun i => i.2.1)
      (fun i j => ⟨StableLevel.inf _ i j, StableLevel.inf_le_left _ i j, StableLevel.inf_le_right _ i j⟩)
      (fun U hU => StableLevel.exists_le _ hτc hττ hKb U hU) (placeConv v μ) hc
      (fun i x => heckeOp_level_idem π hsm μ i.1 i.2.1 i.2.2.1 x)
      (fun i x => heckeOp_level_mem_fixedVectors π hsm μ i.1 i.2.1 i.2.2.1 x)
      (fun i φ hl => Subtype.ext (by
        show mulConv μ (level μ i.1 i.2.1 i.2.2.1 : LocalGL3 v → ℂ) φ = φ
        rw [coe_level_eq_smul_indicator]
        exact inv_measureReal_smul_indicator_mulConv_of_left_invariant μ i.2.2.1 (h0 i) _ hl))
      (fun i φ hr => Subtype.ext (by
        show mulConv μ φ (level μ i.1 i.2.1 i.2.2.1 : LocalGL3 v → ℂ) = φ
        rw [coe_level_eq_smul_indicator]
        exact mulConv_inv_measureReal_smul_indicator_of_right_invariant μ i.2.2.1 (h0 i) _ hr))
      (fun i => ⟨fun k hk x => by
          rw [coe_level_eq_smul_indicator]
          exact smul_indicator_left_invariant _ i.1 k hk x,
        fun k hk x => by
          rw [coe_level_eq_smul_indicator]
          exact smul_indicator_right_invariant _ i.1 k hk x⟩)
      (fun φ => by
        obtain ⟨K, -, hKo, hK⟩ := HomogeneousCells.exists_compact_open_subgroup_forall_apply_eq hKb
          (φ : LocalGL3 v → ℂ) (mem_testSubmodule.mp φ.2).1 (mem_testSubmodule.mp φ.2).2 1
        exact ⟨K, hKo, fun k hk x => ((hK k hk).1 x).1, fun k hk x => ((hK k hk).1 x).2⟩)

  exact exists_pairing_of_character_comp_eq (K := fun i : PlaceLevel v => i.1)
    (transposeInv3Hom (F := v.adicCompletion ℚ)) hττ hirr hsm (fun U hU => StableLevel.exists_le _ hτc hττ hKb U hU)
    L (placeConv v μ) hc (fun g φ => translationAction (LocalGL3 v) (LocalGL3 v) ℂ g φ) rightTranslate
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (pullback ℂ (transposeInv3Hom (F := v.adicCompletion ℚ)) hτc hττ)
    (pullback ℂ (fun g : LocalGL3 v => g⁻¹) continuous_inv inv_involutive) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun φ ψ => pullback_testConv μ _ (transposeInv3Hom (F := v.adicCompletion ℚ)) hτc hττ hμτ φ ψ)
    (fun φ ψ => pullback_inv_testConv μ _ φ ψ)
    (fun i => Subtype.ext (funext fun g => by
      show (level μ i.1 i.2.1 i.2.2.1 : LocalGL3 v → ℂ) (transposeInv3Hom g) =
        (level μ i.1 i.2.1 i.2.2.1 : LocalGL3 v → ℂ) g
      rw [coe_level_eq_smul_indicator]
      exact indicator_comp_tau_of_stable _ i.2.2.2 _ g))
    (fun i => Subtype.ext (funext fun g => by
      show (level μ i.1 i.2.1 i.2.2.1 : LocalGL3 v → ℂ) g⁻¹ = (level μ i.1 i.2.1 i.2.2.1 : LocalGL3 v → ℂ) g
      rw [coe_level_eq_smul_indicator]
      exact indicator_inv_of_subgroup i.1 _ g))
    (fun g φ x => rep_heckeOp_apply π hsm μ g φ x) (fun g φ x => heckeOp_apply_rep π hsm μ g φ x)
    (fun i x hx => heckeOp_level_apply_of_forall π hsm μ i.1 i.2.1 i.2.2.1 hx) hlev
    fun φ => character_pullback_transposeInv3_eq v μ hKb L hc φ

end Place
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

end LanglandsTunnell.CubicInduction.Transposition
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.localMaximalCompact3 CubicInduction.mem_localMaximalCompact3_iff CubicInduction.transposeInv3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localMaximalCompact3 mem_localMaximalCompact3_iff transposeInv3 LocalGL3"
namespace Transposition
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.InvariantFunctional FLT.SmoothAdmissibleSchurCommutant P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction"

section FunctionalLevel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] (π : G →* Module.End ℂ V) (hsm : IsSmoothRep π)
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

private theorem comp_heckeOp_level_eq_of_forall (K : Subgroup G) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (l : Module.Dual ℂ V) (hl : ∀ k ∈ K, ∀ x : V, l (π k x) = l x) :
    l ∘ₗ heckeOp π hsm μ (level μ K hKc hKo) = l := by
  letI := repAction π
  haveI := repAction_smulCommClass π
  refine LinearMap.ext fun x => ?_
  exact apply_heckeSmul_heckeIdempotent_of_forall_apply_smul_eq μ hKo hKc (hKo.measure_ne_zero μ ⟨1, K.one_mem⟩)
    l hl (hasOpenStabilizer_of_isSmoothRep π hsm x)

end FunctionalLevel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

section Place

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem exists_placeLevel_comp_heckeOp_eq (μ : Measure (LocalGL3 v)) [IsHaarMeasure μ]
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : LocalGL3 v →* Module.End ℂ V) (hsm : IsSmoothRep π)
    (U : Subgroup (LocalGL3 v)) (hU : IsOpen (U : Set (LocalGL3 v))) :
    ∃ i : PlaceLevel v, ∀ l : Module.Dual ℂ V, (∀ u ∈ U, ∀ x : V, l (π u x) = l x) →
      l ∘ₗ heckeOp π hsm μ (level μ i.1 i.2.1 i.2.2.1) = l := by
  obtain ⟨i, hi⟩ := StableLevel.exists_le (transposeInv3Hom (F := v.adicCompletion ℚ)) continuous_transposeInv3Hom
    transposeInv3Hom_involutive (MatrixUnitsBasis.exists_compact_open_subgroup_subset_adicCompletion ℚ v) U hU
  exact ⟨i, fun l hl => comp_heckeOp_level_eq_of_forall π hsm μ i.1 i.2.1 i.2.2.1 l fun k hk x => hl k (hi hk) x⟩

end Place
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

end LanglandsTunnell.CubicInduction.Transposition
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.localMaximalCompact3 CubicInduction.mem_localMaximalCompact3_iff CubicInduction.transposeInv3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "localMaximalCompact3 mem_localMaximalCompact3_iff transposeInv3 LocalGL3"
namespace Transposition
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.InvariantFunctional P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character FLT.SmoothAdmissibleSchurCommutant"
open TestFunctionAction MulConvolution

section ConvLaw

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G]
  [BorelSpace G] {V : Type*} [AddCommGroup V] [Module ℂ V] (π : G →* Module.End ℂ V) (hsm : IsSmoothRep π)
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

private theorem heckeOp_testConv
    (hKb : ∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ (K : Set G) ⊆ U)
    (φ ψ : testSubmodule G ℂ) :
    heckeOp π hsm μ (testConv μ (testSubmodule G ℂ) (fun _ hf _ hh => mulConv_mem_testSubmodule μ hKb hf hh) φ ψ) =
      heckeOp π hsm μ φ * heckeOp π hsm μ ψ := by
  letI := repAction π
  haveI := repAction_smulCommClass π
  refine LinearMap.ext fun x => ?_
  obtain ⟨K₁, hK₁c, hK₁o, hK₁⟩ := HomogeneousCells.exists_compact_open_subgroup_forall_apply_eq hKb (φ : G → ℂ)
    (mem_testSubmodule.mp φ.2).1 (mem_testSubmodule.mp φ.2).2 1
  obtain ⟨K₂, hK₂c, hK₂o, hK₂⟩ := HomogeneousCells.exists_compact_open_subgroup_forall_apply_eq hKb (ψ : G → ℂ)
    (mem_testSubmodule.mp ψ.2).1 (mem_testSubmodule.mp ψ.2).2 1
  show heckeSmul μ (mulConv μ (φ : G → ℂ) (ψ : G → ℂ)) x = heckeSmul μ (φ : G → ℂ) (heckeSmul μ (ψ : G → ℂ) x)
  exact heckeSmul_mulConv_of_exists_subgroup μ (mem_testSubmodule.mp φ.2).2 (mem_testSubmodule.mp ψ.2).1
    (mem_testSubmodule.mp ψ.2).2 (hasOpenStabilizer_of_isSmoothRep π hsm x)
    ⟨K₁ ⊓ K₂, hK₁c.inter_right (Subgroup.isClosed_of_isOpen K₂ hK₂o), hK₁o.inter hK₂o,
      fun y k hk => ((hK₁ k (Subgroup.mem_inf.mp hk).1).1 y).2,
      fun y k hk => ((hK₂ k (Subgroup.mem_inf.mp hk).2).1 y).1⟩

end ConvLaw
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

section Place

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem heckeOp_placeConv (μ : Measure (LocalGL3 v)) [IsHaarMeasure μ] {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : LocalGL3 v →* Module.End ℂ V) (hsm : IsSmoothRep π)
    (φ ψ : testSubmodule (LocalGL3 v) ℂ) :
    heckeOp π hsm μ (placeConv v μ φ ψ) = heckeOp π hsm μ φ * heckeOp π hsm μ ψ :=
  heckeOp_testConv π hsm μ (MatrixUnitsBasis.exists_compact_open_subgroup_subset_adicCompletion ℚ v) φ ψ

end Place
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

end LanglandsTunnell.CubicInduction.Transposition
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

open IsDedekindDomain NumberField FLT.SmoothAdmissibleSchurCommutant
p2m_open "MeasureTheory MeasureTheory.Measure TopologicalSpace LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction"
open LanglandsTunnell.CubicInduction.Transposition

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : LocalGL3 v →* Module.End ℂ V)
    (_hirr : IsIrreducibleRep π) (_hsm : IsSmoothRep π) (_hadm : IsAdmissibleRep π) :
    ∃ P : V →ₗ[ℂ] V →ₗ[ℂ] ℂ,
      (∀ (g : LocalGL3 v) (x y : V), P (π g x) (π (transposeInv3 g) y) = P x y) ∧
      (∀ y : V, (∀ x : V, P x y = 0) → y = 0) ∧
      (∀ L : V →ₗ[ℂ] ℂ,
        (∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧ ∀ u ∈ U, ∀ x : V, L (π u x) = L x) →
        ∃ y : V, ∀ x : V, L x = P x y) := by
  obtain ⟨K₀⟩ := (inferInstance : Nonempty (PositiveCompacts (LocalGL3 v)))
  exact exists_pairing_of_conv_of_level v (haarMeasure K₀) π _hirr _hsm _hadm (heckeOp_placeConv v _ π _hsm)
    (exists_placeLevel_comp_heckeOp_eq v _ π _hsm)

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.ConjOrbit P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.SigmaCompactUnits P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.TransposeTwist P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.ClassInvariance P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Strata P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Character P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.Contragredient P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.TestFunctionAction P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep.LanglandsTunnell.CubicInduction.Transposition"

#print axioms LanglandsTunnell.CubicInduction.Transposition.character_pullback_transposeGL3_eq
#print axioms exists_pairing_of_character_comp_eq
#print axioms LanglandsTunnell.CubicInduction.Transposition.character_pullback_transposeInv3_eq
#print axioms LanglandsTunnell.CubicInduction.Transposition.heckeOp_apply_rep
#print axioms LanglandsTunnell.CubicInduction.Transposition.heckeOp_level_apply_of_forall
#print axioms LanglandsTunnell.CubicInduction.Transposition.heckeOp_level_idem
#print axioms LanglandsTunnell.CubicInduction.Transposition.heckeOp_level_mem_fixedVectors
#print axioms LanglandsTunnell.CubicInduction.Transposition.rep_heckeOp_apply
#print axioms LanglandsTunnell.CubicInduction.Transposition.exists_pairing_of_conv_of_level
#print axioms LanglandsTunnell.CubicInduction.Transposition.exists_placeLevel_comp_heckeOp_eq
#print axioms LanglandsTunnell.CubicInduction.Transposition.heckeOp_placeConv
#print axioms solution

end S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_pairing_transposeInv3_of_isIrreducibleRep (solution)
