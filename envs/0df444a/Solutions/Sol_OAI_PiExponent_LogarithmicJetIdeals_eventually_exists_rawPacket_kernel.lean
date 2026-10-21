-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.eventually_exists_rawPacket_kernel
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:54:10.170172+00:00
-- url     : https://prove2.me/submissions/cd437ee8-90d9-4c97-9e94-ac4798d562dc

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open Filter Topology
open scoped BigOperators

set_option linter.unusedVariables false

/-- The exponent-vector map is injective. -/
lemma rpk_exponentVector_injective {d : ℕ} :
    Function.Injective (@InterpolationMatrix.exponentVector d) := by
  intro a b h
  funext i
  have hi := congrArg (fun v : Fin d →₀ ℕ => v i) h
  simpa only [InterpolationMatrix.exponentVector, Finsupp.coe_equivFunOnFinite_symm] using hi

/-- Membership in the real weighted simplex gives the weighted degree bound. -/
lemma rpk_realWeightedSimplex_weight_le {d : ℕ} {W : Fin d → ℝ} {N : ℝ} {a : Fin d → ℕ}
    (ha : a ∈ realWeightedSimplex W N) :
    (∑ i, W i * (a i : ℝ)) ≤ N := by
  unfold realWeightedSimplex at ha
  exact (Finset.mem_filter.mp ha).2

/-- Polynomial with prescribed coefficients on a finite set of exponents. -/
noncomputable def rpk_polyOfCoeffs {d : ℕ} (S : Finset (Fin d → ℕ)) :
    (↥S → ℂ) →ₗ[ℂ] MvPolynomial (Fin d) ℂ where
  toFun x := ∑ a : ↥S, MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) (x a)
  map_add' x y := by
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    exact map_add (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val)) (x a) (y a)
  map_smul' c x := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact map_smul (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val)) c (x a)

lemma rpk_polyOfCoeffs_coeff {d : ℕ} (S : Finset (Fin d → ℕ)) (x : ↥S → ℂ) (a : ↥S) :
    (rpk_polyOfCoeffs S x).coeff (InterpolationMatrix.exponentVector a.val) = x a := by
  classical
  simp only [rpk_polyOfCoeffs, LinearMap.coe_mk, AddHom.coe_mk]
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    have hne : InterpolationMatrix.exponentVector b.val ≠
        InterpolationMatrix.exponentVector a.val := by
      intro h
      exact hba (Subtype.ext (rpk_exponentVector_injective h))
    simp [MvPolynomial.coeff_monomial, hne]
  · intro h; simp at h

lemma rpk_polyOfCoeffs_injective {d : ℕ} (S : Finset (Fin d → ℕ)) :
    Function.Injective (rpk_polyOfCoeffs S) := by
  intro x y h
  funext a
  have := congrArg (fun p : MvPolynomial (Fin d) ℂ =>
    p.coeff (InterpolationMatrix.exponentVector a.val)) h
  simpa only [rpk_polyOfCoeffs_coeff] using this

lemma rpk_polyOfCoeffs_support {d : ℕ} (S : Finset (Fin d → ℕ)) (x : ↥S → ℂ) :
    (rpk_polyOfCoeffs S x).support ⊆
      S.image (InterpolationMatrix.exponentVector) := by
  classical
  intro e he
  by_contra hn
  have hzero : (rpk_polyOfCoeffs S x).coeff e = 0 := by
    simp only [rpk_polyOfCoeffs, LinearMap.coe_mk, AddHom.coe_mk]
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro a _
    have hne : InterpolationMatrix.exponentVector a.val ≠ e := by
      intro h
      exact hn (Finset.mem_image.mpr ⟨a.val, a.property, h⟩)
    simp [MvPolynomial.coeff_monomial, hne]
  exact (MvPolynomial.mem_support_iff.mp he) hzero

lemma rpk_polyOfCoeffs_weighted {d : ℕ} {W : Fin d → ℝ} {N : ℝ}
    (x : ↥(realWeightedSimplex W N) → ℂ) :
    ∀ u ∈ (rpk_polyOfCoeffs (realWeightedSimplex W N) x).support,
      (∑ i, W i * (u i : ℝ)) ≤ N := by
  intro u hu
  obtain ⟨a, ha, rfl⟩ :=
    Finset.mem_image.mp (rpk_polyOfCoeffs_support _ x hu)
  simpa only [InterpolationMatrix.exponentVector, Finsupp.coe_equivFunOnFinite_symm]
    using rpk_realWeightedSimplex_weight_le ha

/-- `rawPacketMap` is ℂ-linear in its polynomial argument. -/
noncomputable def rpk_packetLinearMap {m : ℕ} (K : ℕ) (v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) :
    MvPolynomial (Fin (m + 1)) ℂ →ₗ[ℂ]
      (InterpolationMatrix.Row K v0 theta w H → ℂ) where
  toFun := rawPacketMap K v0 theta w H r
  map_add' P Q := by
    funext ρ
    simp only [rawPacketMap, Pi.add_apply, map_add]
  map_smul' c P := by
    funext ρ
    simp only [rawPacketMap, Pi.smul_apply, RingHom.id_apply, map_smul, smul_eq_mul]

lemma rpk_exists_nonzero_kernel {C R : Type*} [Fintype C] [Fintype R]
    (E : (C → ℂ) →ₗ[ℂ] (R → ℂ)) (h : Fintype.card R < Fintype.card C) :
    ∃ x : C → ℂ, x ≠ 0 ∧ E x = 0 := by
  have hC : Module.finrank ℂ (C → ℂ) = Fintype.card C :=
    Module.finrank_fintype_fun_eq_card (R := ℂ) (η := C)
  have hR : Module.finrank ℂ (R → ℂ) = Fintype.card R :=
    Module.finrank_fintype_fun_eq_card (R := ℂ) (η := R)
  have hk : LinearMap.ker E ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by rw [hC, hR]; exact h)
  obtain ⟨x, hx, hn⟩ := (LinearMap.ker E).ne_bot_iff.mp hk
  exact ⟨x, hn, LinearMap.mem_ker.mp hx⟩

theorem solution {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (r : Fin m → ℂ)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a ^ (m + 1) *
        (∏ i, InterpolationMatrix.columnWeights w0 w i) /
        (∏ i, InterpolationMatrix.rowWeights v0 theta w i) < 1)
    (hcard : ∀ᶠ N : ℝ in atTop,
      K * (strictWeightedSimplex (InterpolationMatrix.rowWeights v0 theta w) (a * N)).card <
        (realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) N).card) :
    ∀ᶠ N : ℝ in atTop,
      ∃ P : MvPolynomial (Fin (m + 1)) ℂ, P ≠ 0 ∧
        (∀ u ∈ P.support,
          (∑ i, InterpolationMatrix.columnWeights w0 w i * (u i : ℝ)) ≤ N) ∧
        rawPacketMap K v0 theta w (a * N) r P = 0 := by
  classical
  filter_upwards [hcard] with N hN
  let E : MvPolynomial (Fin (m + 1)) ℂ →ₗ[ℂ]
      (InterpolationMatrix.Row K v0 theta w (a * N) → ℂ) :=
    rpk_packetLinearMap K v0 theta w (a * N) r
  let A : (↥(realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) N) → ℂ) →ₗ[ℂ]
      (InterpolationMatrix.Row K v0 theta w (a * N) → ℂ) :=
    E.comp (rpk_polyOfCoeffs (realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) N))
  have hlt : Fintype.card (InterpolationMatrix.Row K v0 theta w (a * N)) <
      Fintype.card ↥(realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) N) := by
    simp only [InterpolationMatrix.Row, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_coe]
    exact hN
  obtain ⟨x, hx, hAx⟩ := rpk_exists_nonzero_kernel A hlt
  refine ⟨rpk_polyOfCoeffs (realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) N) x,
    ?_, ?_, ?_⟩
  · intro hp
    exact hx (rpk_polyOfCoeffs_injective _ (by rw [hp, map_zero]))
  · exact rpk_polyOfCoeffs_weighted x
  · have : E (rpk_polyOfCoeffs (realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) N)
        x) = 0 := hAx
    simpa only [E, rpk_packetLinearMap, LinearMap.coe_mk, AddHom.coe_mk] using this
