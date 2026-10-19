-- Prove2me | solution 1 for OAI.Erdos3.exists_physical_stability_parameters_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:15:36.303546+00:00
-- url     : https://prove2.me/submissions/07bdef67-c876-417e-af74-6ab6e66cfc8c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B213
import Theorems.Thm_OAI_Erdos3_exists_physical_stack_record_descent_s2
import Theorems.Thm_OAI_Erdos3_exists_retained_affine_epoch_transition_s2
import Theorems.Thm_OAI_Erdos3_exists_retained_epoch_from_records_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution
namespace OAI


namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ τ υ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

theorem substitute_X (p : VectorPolynomial σ R V) :
    substitute (fun i => MvPolynomial.X i) p = p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v => simp only [substitute_tmul, MvPolynomial.aeval_X_left_apply]
  | add p q hp hq => simp only [map_add, hp, hq]

end Erdos3.VectorPolynomial


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueStrideRebase
namespace OAI

section

namespace Erdos3

theorem scalarAffinePolynomial_comp {σ : Type*} (r₀ r₁ : ℚ) (h₀ h₁ : σ → ℚ) (i : σ) :
    MvPolynomial.aeval (scalarAffinePolynomial r₁ h₁) (scalarAffinePolynomial r₀ h₀ i) =
      scalarAffinePolynomial (r₀ * r₁) (fun j => r₀ * h₁ j + h₀ j) i := by
  simp only [scalarAffinePolynomial, map_add, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RankAdaptedNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.AdaptedModelData

open Module CircleFourier
open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} (F : D.AdaptedModelData) (H : ℕ)
  (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H) {w : σ → ℕ}

theorem rebaseNiltest_unit_interval (T : D.Niltest w) (hT : T.UnitIntervalValued) :
    (F.rebaseNiltest H hH T).UnitIntervalValued := hT

end Erdos3.RationalFilteredNilmanifold.AdaptedModelData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledAdaptedRebase
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

theorem exists_controlled_adapted_rebase :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      ∃ (F : D.AdaptedModelData) (H : ℕ)
        (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H),
        p ≤ (p + C) ^ C ∧ F.model.GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ {σ : Type*} {w : σ → ℕ} (T : D.Niltest w), T.ComplexityLE p →
          (F.rebaseNiltest H hH T).ComplexityLE ((p + C) ^ C)) ∧
        ∀ eta : L →ₗ[ℚ] ℚ, (∀ i, rationalLogHeight (eta (D.basis i)) ≤ p) →
          ∀ j, rationalLogHeight (eta (F.model.basis j)) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 3) ^ 11 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + 2) ^ 2 + (X + 3) ^ 4 + X)
  refine ⟨C, hC, ?_⟩
  intro L _ _ s d _ _ _ _ D p hp hD
  obtain ⟨F, hF, hb⟩ := D.exists_adapted_model_data hp hD
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH (i j) : RationalHeightLE (D.basis.repr (F.basis i) j) H :=
    rationalHeightLE_ceil_exp (hb i j)
  let r := (p + 3) ^ 11 + p + 2
  have hpow : 0 ≤ (p + 3) ^ 11 := by positivity
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hfr : (p + 3) ^ 11 ≤ r := by dsimp [r]; linarith
  have hHbound : (H : ℝ) ≤ Real.exp r :=
    (ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)).trans
      (Real.exp_le_exp.mpr (by dsimp [r]; linarith))
  have hr : 0 ≤ r := hp.trans hpr
  have hbud : r + (r + 2) ^ 2 + (p + 3) ^ 4 + p ≤ (p + C) ^ C := by
    simpa [R, X, r, Polynomial.eval₂_pow] using hbudget p hp
  have hfreq0 : 0 ≤ (p + 3) ^ 4 := by positivity
  have hcomp : r + (r + 2) ^ 2 ≤ (p + C) ^ C := by linarith
  have hfreq : (p + 3) ^ 4 ≤ (p + C) ^ C := by nlinarith [sq_nonneg (r + 2)]
  have hbase : p ≤ (p + C) ^ C := hpr.trans ((le_add_of_nonneg_right (sq_nonneg _)).trans hcomp)
  have hgeom : F.model.GeometryComplexityLE r := hF.mono F.model hfr
  refine ⟨F, H, hH, hbase, hgeom.mono F.model
    ((le_add_of_nonneg_right (sq_nonneg _)).trans hcomp), ?_, ?_⟩
  · intro σ w T hT
    exact (F.rebaseNiltest_complexity H hH T hr (hT.mono hpr) hgeom hHbound).mono hcomp
  · intro eta heta j
    have hdim : (Fintype.card (Fin d) : ℝ) ≤ p + 1 := by
      simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith)
    have hval := rational_functional_value_logHeight D.basis eta
      (by linarith : 0 ≤ p + 1) hdim (fun i => (heta i).trans (by linarith : p ≤ p + 1))
      (F.basis j) (hb j)
    apply le_trans _ hfreq
    change rationalLogHeight (eta (F.basis j)) ≤ (p + 3) ^ 4
    simpa only [show p + 1 + 2 = p + 3 by ring] using hval

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FixedAffineResidueDescent
namespace OAI

section

namespace Erdos3

namespace NilpotentLieFiltration

theorem scalarAffineOrbitHom_comp {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (g : F.PolynomialOrbit (fun _ : σ => 1))
    (r₀ r₁ : ℚ) (h₀ h₁ : σ → ℚ) :
    F.scalarAffineOrbitHom r₁ h₁ (F.scalarAffineOrbitHom r₀ h₀ g) =
      F.scalarAffineOrbitHom (r₀ * r₁) (fun i => r₀ * h₁ i + h₀ i) g := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.substitute (scalarAffinePolynomial r₁ h₁)
      (VectorPolynomial.substitute (scalarAffinePolynomial r₀ h₀) g.log) =
    VectorPolynomial.substitute (scalarAffinePolynomial (r₀ * r₁) (fun i => r₀ * h₁ i + h₀ i)) g.log
  rw [VectorPolynomial.substitute_comp]
  simp only [scalarAffinePolynomial_comp]

end NilpotentLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptedAnchoredComparison
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

theorem AnchoredChildResidueComparison.rebase
    {σ K : Type*} [Fintype σ] [DecidableEq σ] [LieRing K] [LieAlgebra ℚ K] {t e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
    (V : RationalFilteredNilmanifold K t e) (F : V.AdaptedModelData) (H : ℕ)
    (hH : ∀ i j, RationalHeightLE (V.basis.repr (F.basis i) j) H)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (cost cost' η δ : ℝ) (lo : σ → ℤ) (N : σ → ℕ) (M P : ℕ) (u v : σ → ℤ) (J : σ → ℕ)
    (hcomplex : ∀ U : V.Niltest (fun _ : σ => 1), U.ComplexityLE cost →
      (F.rebaseNiltest H hH U).ComplexityLE cost')
    (hcomparison : AnchoredChildResidueComparison V child cost η δ lo N M P u v J) :
    AnchoredChildResidueComparison F.model child cost' η δ lo N M P u v J := by
  obtain ⟨lo', N', w, z, U, hsub, hpos, hlength, hw, hz, hwu, hzv, hzw,
    hbase, hfine, horbit, hunit, hcost, hgap⟩ := hcomparison
  exact ⟨lo', N', w, z, F.rebaseNiltest H hH U, hsub, hpos, hlength, hw, hz, hwu, hzv, hzw,
    hbase, hfine, horbit, F.rebaseNiltest_unit_interval H hH U hunit, hcomplex U hcost, hgap⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ControlledAdaptedEpochChild
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ L K : Type*} [Fintype σ] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {s d t e : ℕ}

theorem FixedAffineEpochTransition.rebase_child
    (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (T : D.Niltest (fun _ : σ => 1)) (A : σ → ℝ)
    (V : RationalFilteredNilmanifold K t e) (F : V.AdaptedModelData) (H : ℕ)
    (hH : ∀ i j, RationalHeightLE (V.basis.repr (F.basis i) j) H)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (work cost cost' : ℝ) (P C B : ℕ)
    (hcomplex : ∀ U : V.Niltest (fun _ : σ => 1), U.ComplexityLE cost →
      (F.rebaseNiltest H hH U).ComplexityLE cost')
    (htransition : FixedAffineEpochTransition D ω hF W T A V child work cost P C B) :
    FixedAffineEpochTransition D ω hF W T A F.model child work cost' P C B := by
  intro p hp hpwork r h A' hA' hh hr S hS hunit hcost q rho hpq hσ hfreq hrho hrhop
    lo N M hM u v J hJ hv hcop hsteplarge Δ ε δ hδ hδone hε hprojection hfreezing
    hlarge hphysical hcount hgap
  rcases htransition p hp hpwork r h A' hA' hh hr S hS hunit hcost q rho hpq hσ hfreq hrho hrhop
    lo N M hM u v J hJ hv hcop hsteplarge Δ ε δ hδ hδone hε hprojection hfreezing
    hlarge hphysical hcount hgap with hevent | hchild
  · exact Or.inl hevent
  · exact Or.inr (hchild.rebase V F H hH _ cost cost' (Δ / 4) δ lo N M P u v J hcomplex)

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

theorem exists_controlled_adapted_epoch_child :
    ∃ R : ℕ, 2 ≤ R ∧ ∀ {σ L K : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {s d t e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (T : D.Niltest (fun _ : σ => 1)) (A : σ → ℝ)
      (V : RationalFilteredNilmanifold K t e)
      (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
      (work cost : ℝ) (P C B : ℕ), 0 ≤ cost → V.GeometryComplexityLE cost →
      FixedAffineEpochTransition D ω hF W T A V child work cost P C B →
      ∃ F : V.AdaptedModelData,
        finrank ℚ K = e ∧ F.model.GeometryComplexityLE ((cost + R) ^ R) ∧
        FixedAffineEpochTransition D ω hF W T A F.model child work ((cost + R) ^ R) P C B := by
  obtain ⟨R, hR, hrebase⟩ := exists_controlled_adapted_rebase
  refine ⟨R, hR, ?_⟩
  intro σ L K _ _ _ _ _ _ _ _ _ _ _ _ _ _ s d t e D ω hF W T A V child work cost P C B
    hcost hV htransition
  obtain ⟨F, H, hH, _, hgeom, hcomplex, _⟩ := hrebase V hcost hV
  refine ⟨F, ?_, hgeom, ?_⟩
  · simpa only [Fintype.card_fin] using finrank_eq_card_basis V.basis
  · exact htransition.rebase_child D ω hF W T A V F H hH child work cost ((cost + R) ^ R)
      P C B (fun U hU => hcomplex U hU)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalOrbitRecovery
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

theorem scalarAffineOrbitHom_one_zero {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (g : F.PolynomialOrbit (fun _ : σ => 1)) :
    F.scalarAffineOrbitHom 1 (fun _ => 0) g = g := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.substitute (scalarAffinePolynomial 1 (fun _ => 0)) g.log = g.log
  have h : scalarAffinePolynomial (σ := σ) 1 (fun _ => 0) = fun i => MvPolynomial.X i := by
    funext i
    simp [scalarAffinePolynomial]
  rw [h, VectorPolynomial.substitute_X]

theorem scalarAffineOrbitHom_inverse_recover {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (g : F.PolynomialOrbit (fun _ : σ => 1))
    (M : ℕ) (hM : 0 < M) (u : σ → ℤ) :
    F.scalarAffineOrbitHom (M : ℚ) (fun i => (u i : ℚ))
      (F.scalarAffineOrbitHom (1 / (M : ℚ)) (fun i => -(u i : ℚ) / M) g) = g := by
  rw [scalarAffineOrbitHom_comp]
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hscale : (1 / (M : ℚ)) * M = 1 := by field_simp
  have hshift : (fun i => (1 / (M : ℚ)) * (u i : ℚ) + -(u i : ℚ) / M) = fun _ => 0 := by
    funext i
    ring
  rw [hscale, hshift, scalarAffineOrbitHom_one_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.UniformPhysicalFrameConstruction
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

universe u v

theorem exists_physical_epoch_frame (s : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {bound : ℕ}
      (base : PhysicalEpochSource.{u, v} σ (s + 1) bound) (state : PhysicalEpochRecords base)
      (M : ℕ), 0 < M → ∀ anchor : σ → ℤ,
      (∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i) →
      (∀ r ∈ state.records, r.modulus ∣ M) →
      ∀ inflate : ℝ → ℝ, (∀ p, 0 ≤ p → p ≤ inflate p) →
      (∀ i, Real.exp ((base.recordBudget + 2) ^ K) ≤ (base.sides i : ℝ) / M) →
      ∃ frame : PhysicalEpochFrame base,
        frame.state = state ∧ frame.modulus = M ∧ frame.anchor = anchor ∧
        frame.work ≤ (base.recordBudget + 2) ^ K ∧
        frame.child.incomingBudget ≤ (base.recordBudget + 2) ^ K ∧
        frame.child.recordBudget = inflate frame.child.incomingBudget ∧
        (frame.period : ℝ) ≤ Real.exp ((base.recordBudget + 2) ^ K) ∧
        frame.freezePower ≤ K ∧ frame.eventPower ≤ K := by
  obtain ⟨C, K₀, _, _, hretained⟩ := exists_retained_epoch_from_records_s2 s
  obtain ⟨B, _, htransition⟩ := exists_retained_affine_epoch_transition_s2 s
  obtain ⟨R, _, hadapted⟩ := exists_controlled_adapted_epoch_child
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ K₀ +
    ((Polynomial.X + 2) ^ K₀ + Polynomial.C R) ^ R + Polynomial.X + 16 +
    ((Polynomial.X + 2) ^ K₀ + 2) ^ C
  obtain ⟨K₁, hK₁, hbudget⟩ := exists_natPolynomial_fixed_power_budget Q
  let K := max K₁ (max B C)
  refine ⟨K, hK₁.trans (le_max_left _ _), ?_⟩
  intro σ _ _ bound base state M hM anchor hanchor hdiv inflate hinflate hlarge
  let p := base.recordBudget
  have hp : 0 ≤ p := base.incoming_nonneg.trans base.incoming_le_record
  have hK₁K : (p + 2) ^ K₁ ≤ (p + 2) ^ K :=
    pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (le_max_left _ _)
  have hsum : (p + 2) ^ K₀ + ((p + 2) ^ K₀ + R) ^ R + p + 16 +
      ((p + 2) ^ K₀ + 2) ^ C ≤ (p + 2) ^ K := by
    have h := hbudget p hp
    simp only [Q, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_ofNat, Polynomial.eval₂_C] at h
    exact h.trans hK₁K
  have hpow0 : 0 ≤ (p + 2) ^ K₀ := by positivity
  have hpowR : 0 ≤ ((p + 2) ^ K₀ + R) ^ R := by positivity
  have hperiodPow0 : 0 ≤ ((p + 2) ^ K₀ + 2) ^ C := by positivity
  have hsize : (p + 2) ^ K₀ ≤ (p + 2) ^ K := by linarith
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hspan : ∀ i, (M : ℝ) * ((base.sides i : ℝ) / M) ≤ (base.sides i : ℝ) := by
    intro i
    apply le_of_eq
    field_simp
  obtain ⟨work, cost, hpwork, hwork, hcost0, hcost, hepoch⟩ :=
    hretained base.model base.weights base.adapted base.fixedMap state.records state.history
      p hp (base.geometry.mono base.model base.incoming_le_record)
      (base.coordinates_le.trans base.incoming_le_record)
      (fun i => (base.sides i : ℝ)) state.controlled M hM hdiv
      (fun i => (base.sides i : ℝ) / M)
      (fun i => (Real.exp_le_exp.mpr hsize).trans (hlarge i)) hspan (fun i => (anchor i : ℚ))
  obtain ⟨P, hP, hPb, E, hE, n, hn, V₀, hV₀, hchild⟩ :=
    htransition base.model base.weights base.adapted (epochRecordIntersection state.records)
      (base.fixedMap.scalarAffinePullback (M : ℚ) (fun i => (anchor i : ℚ)))
      (fun i => (base.sides i : ℝ) / M) work cost C (by linarith) hepoch
  let N := (base.model.filtration.gradedRefiltrationSubalgebra (epochRecordIntersection state.records)) ⧸
    E.filtration.layerIdeal (s + 1)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
  let := realification_moduleTopology_t2 V₀.basis
  obtain ⟨V, _, _, hV, childOrbit, _, hstep⟩ := hchild
  obtain ⟨F, hdimension, hgeometry, hstep'⟩ := hadapted base.model base.weights base.adapted
    (epochRecordIntersection state.records)
    (base.fixedMap.scalarAffinePullback (M : ℚ) (fun i => (anchor i : ℚ)))
    (fun i => (base.sides i : ℝ) / M) V childOrbit work cost P C B hcost0 hV hstep
  let childCost := (cost + R) ^ R
  let next := base.incomingBudget + work + childCost + 16
  have hwork0 : 0 ≤ work := by linarith
  have hchildCost0 : 0 ≤ childCost := by dsimp only [childCost]; positivity
  have hnext0 : 0 ≤ next := by dsimp only [next]; linarith [base.incoming_nonneg]
  have hchildCost : childCost ≤ ((p + 2) ^ K₀ + R) ^ R := by
    dsimp only [childCost]
    gcongr
  have hnext : next ≤ (p + 2) ^ K := by
    dsimp only [next]
    linarith [base.incoming_le_record]
  let physicalOrbit := F.model.filtration.realification.scalarAffineOrbitHom (1 / (M : ℚ))
    (fun i => -(anchor i : ℚ) / M) childOrbit
  let child : PhysicalEpochSource.{u, v} σ s bound := {
    Carrier := N
    dimension := finrank ℚ N
    dimension_le := (by rw [hdimension]; exact hn.trans base.dimension_le)
    model := F.model
    weights := F.weight
    adapted := F.model_layers
    fixedMap := (RationalFilteredNilmanifold.Niltest.const F.model (fun _ : σ => 1) 0).withOrbit physicalOrbit
    lower := base.lower
    sides := base.sides
    sides_pos := base.sides_pos
    incomingBudget := next
    recordBudget := inflate next
    incoming_nonneg := hnext0
    incoming_le_record := hinflate next hnext0
    geometry := hgeometry.mono F.model (by change childCost ≤ next; dsimp only [next]; linarith [base.incoming_nonneg])
    coordinates_le := base.coordinates_le.trans (by dsimp only [next]; linarith) }
  have hrecover : (child.fixedMap.scalarAffinePullback (M : ℚ) (fun i => (anchor i : ℚ))).orbit = childOrbit := by
    change F.model.filtration.realification.scalarAffineOrbitHom (M : ℚ) (fun i => (anchor i : ℚ))
      (F.model.filtration.realification.scalarAffineOrbitHom (1 / (M : ℚ))
        (fun i => -(anchor i : ℚ) / M) childOrbit) = childOrbit
    exact F.model.filtration.realification.scalarAffineOrbitHom_inverse_recover childOrbit M hM anchor
  let frame : PhysicalEpochFrame base := {
    state := state
    modulus := M
    modulus_pos := hM
    anchor := anchor
    anchor_inside := hanchor
    record_moduli := hdiv
    work := work
    incoming_le_work := by linarith [base.incoming_le_record]
    record_le_work := hpwork
    period := P
    period_pos := hP
    freezePower := C
    eventPower := B
    period_le := hPb
    child := child
    child_lower := rfl
    child_sides := rfl
    child_dimension_le := by change finrank ℚ N ≤ base.dimension; rw [hdimension]; exact hn
    childCost := childCost
    childCost_nonneg := hchildCost0
    childCost_le := by change childCost ≤ next; dsimp only [next]; linarith [base.incoming_nonneg]
    incoming_le_child := by change base.incomingBudget + 16 ≤ next; dsimp only [next]; linarith
    work_le_child := by change work ≤ next; dsimp only [next]; linarith [base.incoming_nonneg]
    transition := by rw [hrecover]; exact hstep' }
  have hperiodWork : (work + 2) ^ C ≤ ((p + 2) ^ K₀ + 2) ^ C := by
    have hwork0 : 0 ≤ work := by linarith
    gcongr
  have hperiodBound : (P : ℝ) ≤ Real.exp ((p + 2) ^ K) :=
    hPb.trans (Real.exp_le_exp.mpr (hperiodWork.trans (by linarith)))
  exact ⟨frame, rfl, rfl, rfl, hwork.trans hsize, hnext, rfl, hperiodBound,
    (le_max_right B C).trans (le_max_right K₁ (max B C)),
    (le_max_left B C).trans (le_max_right K₁ (max B C))⟩

end Erdos3

end

section

namespace Erdos3

universe u v

theorem PhysicalFrameConstructionBound.mono {s K L : ℕ}
    (h : PhysicalFrameConstructionBound.{u, v} s K) (hKL : K ≤ L) :
    PhysicalFrameConstructionBound.{u, v} s L := by
  intro σ _ _ bound base state M hM anchor hanchor hmod inflate hinflate hlarge
  have hp : 0 ≤ base.recordBudget := base.incoming_nonneg.trans base.incoming_le_record
  have hpow : (base.recordBudget + 2) ^ K ≤ (base.recordBudget + 2) ^ L :=
    pow_le_pow_right₀ (by linarith) hKL
  obtain ⟨frame, hs, hm, ha, hw, hi, hr, hperiod, hf, he⟩ :=
    h base state M hM anchor hanchor hmod inflate hinflate
      (fun i => (Real.exp_le_exp.mpr hpow).trans (hlarge i))
  exact ⟨frame, hs, hm, ha, hw.trans hpow, hi.trans hpow, hr,
    hperiod.trans (Real.exp_le_exp.mpr hpow), hf.trans hKL, he.trans hKL⟩

theorem exists_uniform_physical_frame_construction (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ t : ℕ, t ≤ s → PhysicalFrameConstructionBound.{u, v} t C := by
  induction s with
  | zero =>
    obtain ⟨C, hC, hframe⟩ := exists_physical_epoch_frame 0
    refine ⟨C, hC, ?_⟩
    intro t ht
    have : t = 0 := by omega
    subst t
    exact @hframe
  | succ s ih =>
    obtain ⟨C, hC, hframes⟩ := ih
    obtain ⟨K, hK, htop⟩ := exists_physical_epoch_frame (s + 1)
    refine ⟨max C K, hC.trans (le_max_left _ _), ?_⟩
    intro t ht
    by_cases hts : t ≤ s
    · exact PhysicalFrameConstructionBound.mono (@hframes t hts) (le_max_left _ _)
    · have heq : t = s + 1 := by omega
      subst t
      exact PhysicalFrameConstructionBound.mono (@htop) (le_max_right _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScheduledPhysicalEpochStack
namespace OAI

section

namespace Erdos3

theorem physicalEpochBudget_nonneg (A C : ℕ) {b : ℝ} (hb : 0 ≤ b) (k : ℕ) :
    0 ≤ physicalEpochBudget A C b k := by
  induction k with
  | zero => exact hb
  | succ k ih => simp only [physicalEpochBudget]; positivity

theorem physicalEpochBudget_work_le {A C : ℕ} (hA : 1 ≤ A) {b : ℝ} (hb : 0 ≤ b) (k : ℕ) :
    (physicalEpochBudget A C b k + 2) ^ C ≤ physicalEpochBudget A C b (k + 1) := by
  have hx := physicalEpochBudget_nonneg A C hb k
  have hp : 0 ≤ (physicalEpochBudget A C b k + 2) ^ C := by positivity
  change (physicalEpochBudget A C b k + 2) ^ C ≤ ((physicalEpochBudget A C b k + 2) ^ C + 2) ^ A
  calc
    (physicalEpochBudget A C b k + 2) ^ C ≤ (physicalEpochBudget A C b k + 2) ^ C + 2 := by linarith
    _ = ((physicalEpochBudget A C b k + 2) ^ C + 2) ^ 1 := (pow_one _).symm
    _ ≤ ((physicalEpochBudget A C b k + 2) ^ C + 2) ^ A := pow_le_pow_right₀ (by linarith) hA

theorem physicalEpochBudget_mono {A C : ℕ} (hA : 1 ≤ A) (hC : 1 ≤ C) {b : ℝ} (hb : 0 ≤ b) :
    Monotone (physicalEpochBudget A C b) := by
  apply monotone_nat_of_le_succ
  intro k
  have hx := physicalEpochBudget_nonneg A C hb k
  calc
    physicalEpochBudget A C b k ≤ physicalEpochBudget A C b k + 2 := by linarith
    _ = (physicalEpochBudget A C b k + 2) ^ 1 := (pow_one _).symm
    _ ≤ (physicalEpochBudget A C b k + 2) ^ C := pow_le_pow_right₀ (by linarith) hC
    _ ≤ physicalEpochBudget A C b (k + 1) := physicalEpochBudget_work_le hA hb k

theorem exists_physicalEpochBudget_power (A C s : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ b : ℝ, 0 ≤ b → physicalEpochBudget A C b s ≤ (b + 2) ^ K := by
  induction s with
  | zero =>
    refine ⟨2, by omega, ?_⟩
    intro b hb
    simp only [physicalEpochBudget]
    nlinarith
  | succ s ih =>
    obtain ⟨K, _, hK⟩ := ih
    let P : Polynomial ℕ := (((Polynomial.X + 2) ^ K + 2) ^ C + 2) ^ A
    obtain ⟨L, hL, hP⟩ := exists_natPolynomial_fixed_power_budget P
    refine ⟨L, hL, ?_⟩
    intro b hb
    have hx := physicalEpochBudget_nonneg A C hb s
    calc
      physicalEpochBudget A C b (s + 1) ≤ (((b + 2) ^ K + 2) ^ C + 2) ^ A := by
        simp only [physicalEpochBudget]
        gcongr
        exact hK b hb
      _ ≤ (b + 2) ^ L := by simpa [P, Polynomial.eval₂_pow] using hP b hb

end Erdos3

end

section

namespace Erdos3.PhysicalEpochStack

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

theorem UniformAt.budgeted {A M : ℕ} {anchor : σ → ℤ} {budget : ℝ} {power : ℕ}
    {stack : PhysicalEpochStack base} (h : UniformAt A M anchor budget power stack)
    (hinflate : (base.incomingBudget + 2) ^ A ≤ base.recordBudget) : BudgetedAt A budget power stack := by
  induction stack with
  | zero => exact ⟨h.2, hinflate⟩
  | succ frame tail ih =>
    obtain ⟨_, hr, _, _, hw, hp, hf, he, hi, ht⟩ := h
    exact ⟨hr, hinflate, hw, hp, hf, he, ih ht (le_of_eq hi.symm)⟩

end Erdos3.PhysicalEpochStack

end

section

namespace Erdos3.PhysicalEpochStack

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

theorem ScheduledAt.record_le {A C depth : ℕ} {b : ℝ} {stack : PhysicalEpochStack base}
    (h : ScheduledAt A C b depth stack) : base.recordBudget ≤ physicalEpochBudget A C b depth := by
  cases stack <;> exact h.1

theorem ScheduledAt.inflation {A C depth : ℕ} {b : ℝ} {stack : PhysicalEpochStack base}
    (h : ScheduledAt A C b depth stack) : (base.incomingBudget + 2) ^ A ≤ base.recordBudget := by
  cases stack with
  | zero => exact h.2
  | succ => exact h.2.1

theorem ScheduledAt.budgeted {A C depth : ℕ} {b : ℝ} {stack : PhysicalEpochStack base}
    (h : ScheduledAt A C b depth stack) (hA : 1 ≤ A) (hC : 1 ≤ C) (hb : 0 ≤ b) :
    BudgetedAt A (physicalEpochBudget A C b (depth + s)) C stack := by
  induction stack generalizing depth with
  | zero => exact h
  | @succ s base frame tail ih =>
    obtain ⟨hr, hi, hw, hp, hf, he, ht⟩ := h
    have hmono := physicalEpochBudget_mono hA hC hb
    have hroot : physicalEpochBudget A C b depth ≤ physicalEpochBudget A C b (depth + (s + 1)) :=
      hmono (by omega)
    have hwork : (physicalEpochBudget A C b depth + 2) ^ C ≤
        physicalEpochBudget A C b (depth + (s + 1)) :=
      (physicalEpochBudget_work_le hA hb depth).trans (hmono (by omega))
    refine ⟨hr.trans hroot, hi, hw.trans hwork, hp.trans (Real.exp_le_exp.mpr hwork), hf, he, ?_⟩
    have hidx : depth + 1 + s = depth + (s + 1) := by omega
    simpa only [hidx] using ih ht

end Erdos3.PhysicalEpochStack

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalStabilityParameters
namespace OAI

section

namespace Erdos3

open PhysicalEpochStack

universe u v

theorem exists_scheduled_physical_epoch_stack (A C limit : ℕ) (hA : 1 ≤ A) (hC : 1 ≤ C)
    (hframes : ∀ t : ℕ, t ≤ limit → PhysicalFrameConstructionBound.{u, v} t C)
    (b : ℝ) (hb : 0 ≤ b) (s : ℕ) :
    s ≤ limit → ∀ depth : ℕ, ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {bound : ℕ}
      (base : PhysicalEpochSource.{u, v} σ s bound) (state : PhysicalEpochRecords base)
      (M : ℕ), 0 < M → ∀ anchor : σ → ℤ,
      (∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i) →
      (∀ r ∈ state.records, r.modulus ∣ M) →
      base.recordBudget ≤ physicalEpochBudget A C b depth →
      (base.incomingBudget + 2) ^ A ≤ base.recordBudget →
      (∀ i, Real.exp (physicalEpochBudget A C b (depth + s)) ≤ (base.sides i : ℝ) / M) →
      ∃ stack : PhysicalEpochStack base, RootState state stack ∧ RootCreatedAt M anchor stack ∧
        AlignedAt M anchor stack ∧ ScheduledAt A C b depth stack := by
  induction s with
  | zero =>
    intro hs depth σ _ _ bound base state M hM anchor hanchor hmod hcap hinflate hlarge
    exact ⟨.zero base, trivial, trivial, trivial, hcap, hinflate⟩
  | succ s ih =>
    intro hs depth σ _ _ bound base state M hM anchor hanchor hmod hcap hinflate hlarge
    have hp : 0 ≤ base.recordBudget := base.incoming_nonneg.trans base.incoming_le_record
    have hbudget := physicalEpochBudget_nonneg A C hb depth
    have hpow : (base.recordBudget + 2) ^ C ≤ (physicalEpochBudget A C b depth + 2) ^ C :=
      pow_le_pow_left₀ (by linarith) (by linarith) C
    have hbound : (physicalEpochBudget A C b depth + 2) ^ C ≤
        physicalEpochBudget A C b (depth + (s + 1)) :=
      (physicalEpochBudget_work_le hA hb depth).trans (physicalEpochBudget_mono hA hC hb (by omega))
    have hinflation : ∀ x : ℝ, 0 ≤ x → x ≤ (x + 2) ^ A := by
      intro x hx
      calc
        x ≤ x + 2 := by linarith
        _ = (x + 2) ^ 1 := (pow_one _).symm
        _ ≤ (x + 2) ^ A := pow_le_pow_right₀ (by linarith) hA
    obtain ⟨frame, hstate, hmodulus, hframeAnchor, hwork, hchildIncoming, hchildRecord, hperiod, hfreeze, hevent⟩ :=
      hframes s (by omega) base state M hM anchor hanchor hmod (fun x => (x + 2) ^ A) hinflation
        (fun i => (Real.exp_le_exp.mpr (hpow.trans hbound)).trans (hlarge i))
    have hchildCap : frame.child.recordBudget ≤ physicalEpochBudget A C b (depth + 1) := by
      rw [hchildRecord]
      change (frame.child.incomingBudget + 2) ^ A ≤ ((physicalEpochBudget A C b depth + 2) ^ C + 2) ^ A
      have hx := frame.child.incoming_nonneg
      have hcost := hchildIncoming.trans hpow
      gcongr
    have hchildInflate : (frame.child.incomingBudget + 2) ^ A ≤ frame.child.recordBudget := le_of_eq hchildRecord.symm
    have hchildAnchor : ∀ i, frame.child.lower i ≤ anchor i ∧ anchor i < frame.child.lower i + frame.child.sides i := by
      simpa only [frame.child_lower, frame.child_sides] using hanchor
    have hidx : depth + 1 + s = depth + (s + 1) := by omega
    have hchildLarge : ∀ i, Real.exp (physicalEpochBudget A C b (depth + 1 + s)) ≤
        (frame.child.sides i : ℝ) / M := by
      simpa only [frame.child_sides, hidx] using hlarge
    obtain ⟨tail, _, _, htailAlign, htailSchedule⟩ :=
      ih (by omega) (depth + 1) frame.child (PhysicalEpochRecords.empty frame.child) M hM anchor hchildAnchor
        (by simp [PhysicalEpochRecords.empty]) hchildCap hchildInflate hchildLarge
    refine ⟨.succ frame tail, hstate, ⟨hmodulus, hframeAnchor⟩, ?_, ?_⟩
    · exact ⟨hmodulus ▸ dvd_refl M, fun i => hframeAnchor ▸ Int.ModEq.refl (frame.anchor i), htailAlign⟩
    · exact ⟨hcap, hinflate, hwork.trans hpow, hperiod.trans (Real.exp_le_exp.mpr hpow),
        hfreeze, hevent, htailSchedule⟩

end Erdos3

end

section

namespace Erdos3

open PhysicalEpochStack

universe u v

theorem PhysicalEpochStack.RecordEvent.rebuild
    {A C limit : ℕ} (hA : 1 ≤ A) (hC : 1 ≤ C)
    (hframes : ∀ t : ℕ, t ≤ limit → PhysicalFrameConstructionBound.{u, v} t C)
    {b : ℝ} (hb : 0 ≤ b)
    {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m J : ℕ}
    {base : PhysicalEpochSource.{u, v} σ s bound} {stack : PhysicalEpochStack base}
    {selected : σ → ℤ} (hm : 0 < m) (hJ : 0 < J) (event : RecordEvent m J stack) :
    ∀ depth : ℕ, s ≤ limit → ScheduledAt A C b depth stack → AlignedAt m selected stack →
    ∀ anchor : σ → ℤ,
    (∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i) →
    (∀ i, anchor i ≡ selected i [ZMOD (m : ℤ)]) →
    (∀ i, Real.exp (physicalEpochBudget A C b (depth + s)) ≤ (base.sides i : ℝ) / (m * J : ℕ)) →
    ∃ next : PhysicalEpochStack base,
      Event stack next ∧ AlignedAt (m * J) anchor next ∧ ScheduledAt A C b depth next := by
  induction event with
  | @head s base frame tail state record moduli drop =>
    intro depth hs hschedule halign anchor hinside hcompat hlarge
    obtain ⟨next, hroot, hcreated, halignNext, hscheduleNext⟩ :=
      exists_scheduled_physical_epoch_stack A C limit hA hC (@hframes) b hb (s + 1)
        hs depth base state (m * J) (Nat.mul_pos hm hJ) anchor hinside moduli
        hschedule.record_le hschedule.inflation hlarge
    cases next with
    | succ newFrame newTail =>
      change newFrame.state = state at hroot
      change newFrame.modulus = m * J ∧ newFrame.anchor = anchor at hcreated
      obtain ⟨r, hr⟩ := record
      have hrecords : newFrame.state.records = r :: frame.state.records := by rw [hroot]; exact hr
      have hmodulus : frame.modulus ∣ newFrame.modulus := by
        rw [hcreated.1]
        exact halign.1.trans (Nat.dvd_mul_right m J)
      have hanchor : ∀ i, newFrame.anchor i ≡ frame.anchor i [ZMOD (frame.modulus : ℤ)] := by
        intro i
        rw [hcreated.2]
        exact (Int.ModEq.of_dvd (by exact_mod_cast halign.1) (hcompat i)).trans (halign.2.1 i)
      exact ⟨.succ newFrame newTail, .head r hrecords hmodulus hanchor tail newTail, halignNext, hscheduleNext⟩
  | @tail s base frame oldTail event ih =>
    intro depth hs hschedule halign anchor hinside hcompat hlarge
    obtain ⟨hr, hi, hw, hp, hf, he, htailSchedule⟩ := hschedule
    obtain ⟨hmframe, haframe, htailAlign⟩ := halign
    have hinsideChild : ∀ i, frame.child.lower i ≤ anchor i ∧ anchor i < frame.child.lower i + frame.child.sides i := by
      simpa only [frame.child_lower, frame.child_sides] using hinside
    have hidx : depth + 1 + s = depth + (s + 1) := by omega
    have hlargeChild : ∀ i, Real.exp (physicalEpochBudget A C b (depth + 1 + s)) ≤
        (frame.child.sides i : ℝ) / (m * J : ℕ) := by
      simpa only [frame.child_sides, hidx] using hlarge
    obtain ⟨newTail, htailEvent, htailAlignNext, htailScheduleNext⟩ :=
      ih (depth + 1) (by omega) htailSchedule htailAlign anchor hinsideChild hcompat hlargeChild
    refine ⟨.succ frame newTail, .tail frame htailEvent, ?_, ?_⟩
    · refine ⟨hmframe.trans (Nat.dvd_mul_right m J), ?_, htailAlignNext⟩
      intro i
      exact (Int.ModEq.of_dvd (by exact_mod_cast hmframe) (hcompat i)).trans (haframe i)
    · exact ⟨hr, hi, hw, hp, hf, he, htailScheduleNext⟩

end Erdos3

end

section

namespace Erdos3

open PhysicalEpochStack

universe u v

theorem exists_scheduled_physical_event_parameters (limit : ℕ) :
    ∃ C A Kf K : ℕ, 2 ≤ C ∧ 1 ≤ A ∧ 2 ≤ Kf ∧ 2 ≤ K ∧
    (∀ b : ℝ, 0 ≤ b → physicalEpochBudget A C b limit ≤ (b + 2) ^ K) ∧
    (∀ t : ℕ, t ≤ limit → PhysicalFrameConstructionBound.{u, v} t C) ∧
    ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap : ℝ}
      (b : ℝ) (depth : ℕ) (selected : σ → ℤ)
      {base : PhysicalEpochSource.{u, v} σ s bound}
      (stack : PhysicalEpochStack base) (c : PhysicalEpochComparison base m a J gap),
    0 ≤ b → depth + s ≤ limit → ScheduledAt A C b depth stack → AlignedAt m selected stack →
    c.Controlled → (∀ i, c.anchor i ≡ selected i [ZMOD (m : ℤ)]) →
    (m * a * stack.periods.prod).Coprime J →
    (∀ i, ((m * J : ℕ) : ℝ) * Real.exp
      (5 * physicalEpochBudget A C b (depth + s) +
        2 * (physicalEpochBudget A C b (depth + s) + 2) ^ Kf + 16) ≤ (base.sides i : ℝ)) →
    ∀ anchor : σ → ℤ,
    (∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i) →
    (∀ i, anchor i ≡ selected i [ZMOD (m : ℤ)]) →
    ∃ next : PhysicalEpochStack base,
      Event stack next ∧ AlignedAt (m * J) anchor next ∧ ScheduledAt A C b depth next := by
  obtain ⟨C, hC, hframes⟩ := exists_uniform_physical_frame_construction limit
  obtain ⟨A, Kf, hA, hKf, hdescent⟩ := exists_physical_stack_record_descent_s2 C
  obtain ⟨K, hK, hgrowth⟩ := exists_physicalEpochBudget_power A C limit
  refine ⟨C, A, Kf, K, hC, hA, hKf, hK, hgrowth, @hframes, ?_⟩
  intro σ _ _ s bound m a J gap b depth selected base stack c hb hs hschedule halign hc hanchor hcop hsource
    anchor hinside hcompat
  have hC1 : 1 ≤ C := by omega
  have hevent := hdescent selected stack c (hschedule.budgeted hA hC1 hb) halign hc hanchor hcop hsource
  let U := physicalEpochBudget A C b (depth + s)
  have hU : 0 ≤ U := physicalEpochBudget_nonneg A C hb (depth + s)
  have hNJ : (0 : ℝ) < ((m * J : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos c.selected_pos c.pending_pos
  have hpower : 0 ≤ (U + 2) ^ Kf := by positivity
  have hlarge : ∀ i, Real.exp U ≤ (base.sides i : ℝ) / (m * J : ℕ) := by
    intro i
    apply (le_div_iff₀ hNJ).mpr
    calc
      Real.exp U * ((m * J : ℕ) : ℝ) ≤
          Real.exp (5 * U + 2 * (U + 2) ^ Kf + 16) * ((m * J : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hNJ.le
      _ = ((m * J : ℕ) : ℝ) * Real.exp (5 * U + 2 * (U + 2) ^ Kf + 16) := mul_comm _ _
      _ ≤ (base.sides i : ℝ) := hsource i
  exact PhysicalEpochStack.RecordEvent.rebuild hA hC1 (@hframes) hb
    c.selected_pos c.pending_pos hevent depth (by omega) hschedule halign anchor hinside hcompat hlarge

end Erdos3

end

section

namespace Erdos3

open PhysicalEpochStack

universe u v

theorem exists_physical_stability_parameters_s2_oai (limit : ℕ) :
    Nonempty (PhysicalStabilityParameters.{u, v} limit) := by
  obtain ⟨C, A, Kf, K, hC, hA, hKf, hK, hgrowth, hframes, hevent⟩ :=
    exists_scheduled_physical_event_parameters limit
  exact ⟨⟨C, A, Kf, K, hC, hA, hKf, hK, hgrowth, @hframes, @hevent⟩⟩

end Erdos3

end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.Erdos3.exists_physical_stability_parameters_s2_oai.{u, v} := @OAI.Erdos3.exists_physical_stability_parameters_s2_oai.{u, v}
