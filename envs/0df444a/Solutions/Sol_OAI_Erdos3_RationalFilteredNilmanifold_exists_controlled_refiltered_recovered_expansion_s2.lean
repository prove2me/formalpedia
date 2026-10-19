-- Prove2me | solution 1 for OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_refiltered_recovered_expansion_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:20:33.374191+00:00
-- url     : https://prove2.me/submissions/7947757f-9a84-4bd4-8ddd-f812078e800b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B181
import Definitions.Def_OAIE3v2B192
import Definitions.Def_OAIE3v2B193
import Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_controlled_refiltered_residue_expansion_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FrozenCosetVariation
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsIsometricSMul Hᵐᵒᵖ H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (Γ : Subgroup G) (Λ : Subgroup H)
  (hΓ : IsClosed (Γ : Set G)) (hΛ : IsClosed (Λ : Set H))
  (φ : G →* H) (r : H) (h : ∀ γ ∈ Γ, r⁻¹ * φ γ * r ∈ Λ)

omit [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G] in
theorem frozenCosetMap_dist_left (a b : H) (x : G ⧸ Γ) :
    letI := rightCosetMetricSpace Λ hΛ
    dist (frozenCosetMap Γ Λ φ a r h x) (frozenCosetMap Γ Λ φ b r h x) ≤ dist a b := by
  let := rightCosetMetricSpace Λ hΛ
  induction x using Quotient.inductionOn with
  | h x =>
    have hLip := lipschitz_quotient_orbit Λ hΛ (QuotientGroup.mk (φ x * r))
    simpa only [NNReal.coe_one, one_mul, MulAction.Quotient.smul_mk, smul_eq_mul,
      mul_assoc, frozenCosetMap_mk] using hLip.dist_le_mul a b

theorem frozenCosetMap_dist_le (a b : H) {A C : ℝ≥0}
    (hφ : LipschitzWith C φ) (ha : LipschitzWith A (fun x => a * x)) (x y : G ⧸ Γ) :
    letI := rightCosetMetricSpace Γ hΓ
    letI := rightCosetMetricSpace Λ hΛ
    dist (frozenCosetMap Γ Λ φ a r h x) (frozenCosetMap Γ Λ φ b r h y) ≤
      (A * C : ℝ≥0) * dist x y + dist a b := by
  let := rightCosetMetricSpace Γ hΓ
  let := rightCosetMetricSpace Λ hΛ
  exact (dist_triangle _ (frozenCosetMap Γ Λ φ a r h y) _).trans
    (add_le_add ((lipschitz_frozenCosetMap Γ Λ hΓ hΛ φ a r h hφ ha).dist_le_mul x y)
      (frozenCosetMap_dist_left Γ Λ hΛ φ r h a b y))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSharedFrozenCorrelations
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem native_frozenCosetMap_dist_le {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (φ : L →ₗ⁅ℚ⁆ M) (r a b : E.RealGroup)
    (h : ∀ γ ∈ D.realLattice, r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice)
    {A C : ℝ≥0}
    (hφ :
      letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith C (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
    (ha :
      letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith A (fun x => a * x)) (x y : D.RealGroup) :
    letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
      (E.basis.baseChange ℝ)
    letI := D.metricSpace
    letI := E.metricSpace
    let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ
    dist (QuotientGroup.mk (a * ψ x * r) : E.Space) (QuotientGroup.mk (b * ψ y * r)) ≤
      (A * C : ℝ≥0) * dist (QuotientGroup.mk x : D.Space) (QuotientGroup.mk y) + dist a b := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] M) := (E.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
    (E.basis.baseChange ℝ)
  exact frozenCosetMap_dist_le D.realLattice E.realLattice D.realLattice_closed_discrete.1
    E.realLattice_closed_discrete.1 _ r h a b hφ ha (QuotientGroup.mk x) (QuotientGroup.mk y)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

theorem mapped_normal_conjugation_mem {G H : Type*} [Group G] [Group H]
    (Γ Λ : Subgroup G) (hle : Λ ≤ Γ) (hnormal : (Λ.subgroupOf Γ).Normal)
    (f : G →* H) {κ x : H} (hκ : κ ∈ Γ.map f) (hx : x ∈ Λ.map f) :
    κ * x * κ⁻¹ ∈ Λ.map f := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hκ
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨k * y * k⁻¹,
    (Subgroup.normal_subgroupOf_iff hle).mp hnormal y k hy hk, ?_⟩
  simp only [map_mul, map_inv]

namespace RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem normalized_right_compatibility {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (φ : L →ₗ⁅ℚ⁆ M) (q : ℕ) (hq : 0 < q) (Λ : Subgroup D.filtration.Group)
    (hconj : Λ ≤ D.conjugationPullback E φ q) (hle : Λ ≤ D.lattice)
    (hnormal : (Λ.subgroupOf D.lattice).Normal)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice) (r : E.RealGroup)
    (hr : (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q) :
    let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ
    ∀ x ∈ Λ.map realificationHom, (ψ κ⁻¹ * r)⁻¹ * ψ x * (ψ κ⁻¹ * r) ∈ E.realLattice := by
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  have hright := D.real_conjugationPullback_property E φ q hq Λ hconj r hr
  dsimp only
  intro x hx
  have hmem := mapped_normal_conjugation_mem D.lattice Λ hle hnormal realificationHom hκ hx
  have heq : (ψ κ⁻¹ * r)⁻¹ * ψ x * (ψ κ⁻¹ * r) = r⁻¹ * ψ (κ * x * κ⁻¹) * r := by
    simp only [map_mul, map_inv]
    group
  rw [heq]
  exact hright _ hmem

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RefilteredResidueExpansionSpec
namespace OAI

section

namespace Erdos3

theorem exists_residue_class_lattice_factors {σ G : Type*} [Group G]
    (Γ : Subgroup G) (f : (σ → ℤ) → G) (M : ℕ) (P : G → Prop)
    (hperiod : ∀ x y : σ → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
      ((QuotientGroup.mk (f x) : G ⧸ Γ) = QuotientGroup.mk (f y)) ∧
      ((QuotientGroup.mk (f x)⁻¹ : G ⧸ Γ) = QuotientGroup.mk (f y)⁻¹))
    (hrep : ∀ x : σ → ℤ,
      (∃ r : G, P r ∧ ∃ γ ∈ Γ, f x = r * γ) ∧
      (∃ r : G, P r ∧ ∃ γ ∈ Γ, f x = γ * r)) :
    ∃ rR rL : (σ → ZMod M) → G,
      (∀ c, P (rR c) ∧ P (rL c)) ∧
      ∀ x : σ → ℤ,
        (∃ γ ∈ Γ, f x = rR (fun j => (x j : ZMod M)) * γ) ∧
        (∃ γ ∈ Γ, f x = γ * rL (fun j => (x j : ZMod M))) := by
  classical
  let lift : (σ → ZMod M) → σ → ℤ := fun c j => Classical.choose (ZMod.intCast_surjective (c j))
  have hlift (c : σ → ZMod M) (j : σ) : (lift c j : ZMod M) = c j :=
    Classical.choose_spec (ZMod.intCast_surjective (c j))
  choose rR hrR γR hγR heqR using fun c => (hrep (lift c)).1
  choose rL hrL γL hγL heqL using fun c => (hrep (lift c)).2
  refine ⟨rR, rL, fun c => ⟨hrR c, hrL c⟩, ?_⟩
  intro x
  let c := fun j => (x j : ZMod M)
  have hxy (j : σ) : (M : ℤ) ∣ x j - lift c j :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (lift c j) (x j) M).mp (hlift c j)
  have h := hperiod x (lift c) hxy
  have hR : (QuotientGroup.mk (f x) : G ⧸ Γ) = QuotientGroup.mk (rR c) := by
    apply h.1.trans
    rw [heqR c]
    exact QuotientGroup.mk_mul_of_mem _ (hγR c)
  have hL : (QuotientGroup.mk (f x)⁻¹ : G ⧸ Γ) = QuotientGroup.mk (rL c)⁻¹ := by
    apply h.2.trans
    rw [heqL c, mul_inv_rev]
    exact QuotientGroup.mk_mul_of_mem _ (Γ.inv_mem (hγL c))
  constructor
  · refine ⟨(rR c)⁻¹ * f x, QuotientGroup.eq.mp hR.symm, ?_⟩
    change f x = rR c * ((rR c)⁻¹ * f x)
    group
  · have hmem : rL c * (f x)⁻¹ ∈ Γ := by
      simpa only [inv_inv] using QuotientGroup.eq.mp hL.symm
    refine ⟨f x * (rL c)⁻¹, ?_, ?_⟩
    · simpa only [mul_inv_rev, inv_inv] using Γ.inv_mem hmem
    · change f x = (f x * (rL c)⁻¹) * rL c
      group

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_native_residue_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ M m : ℕ, 0 < M ∧ 0 < m ∧
        (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
          D.filtration.PolynomialRationalGrid D.basis w q g →
          ∃ rR rL : (σ → ZMod M) → D.RealGroup,
            (∀ c, (∀ i, |(D.basis.baseChange ℝ).repr (rR c).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (D.basis.baseChange ℝ).equivFun (rR c).coord ∈ realDenominatorGrid m ∧
              (∀ i, |(D.basis.baseChange ℝ).repr (rL c).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (D.basis.baseChange ℝ).equivFun (rL c).coord ∈ realDenominatorGrid m) ∧
            ∀ x : σ → ℤ,
              (∃ γ ∈ D.realLattice,
                D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g =
                  rR (fun j => (x j : ZMod M)) * γ) ∧
              (∃ γ ∈ D.realLattice,
                D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g =
                  γ * rL (fun j => (x j : ZMod M))) := by
  obtain ⟨a, _, hperiod⟩ := exists_native_rational_period s
  obtain ⟨b, _, hrep⟩ := exists_native_rational_representatives s
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + (Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hD hσ q hq hqp
  obtain ⟨M, hM, hMb, hper⟩ := hperiod D w hw p hp hD hσ q hq hqp
  obtain ⟨m, hm, hmb, hreps⟩ := hrep D p hp hD q hq hqp
  have hsum : (p + a) ^ a + (p + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (p + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hp (Nat.cast_nonneg b)) _)).trans hsum
  have hbC : (p + b) ^ b ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (add_nonneg hp (Nat.cast_nonneg a)) _)).trans hsum
  refine ⟨M, m, hM, hm, hMb.trans (Real.exp_le_exp.mpr haC), hmb.trans (Real.exp_le_exp.mpr hbC), ?_⟩
  intro g hg
  let f := fun x : σ → ℤ => D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g
  let A := fun r : D.RealGroup =>
    (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
      (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m
  have hf (x : σ → ℤ) :
      (∃ r : D.RealGroup, A r ∧ ∃ γ ∈ D.realLattice, f x = r * γ) ∧
      (∃ r : D.RealGroup, A r ∧ ∃ γ ∈ D.realLattice, f x = γ * r) := by
    obtain ⟨⟨rR, hR, hRgrid, γR, hγR, heqR⟩, ⟨rL, hL, hLgrid, γL, hγL, heqL⟩⟩ :=
      hreps (f x) (D.filtration.polynomialRationalGrid_value D.basis w q g hg x)
    exact ⟨⟨rR, ⟨fun i => (hR i).trans (Real.exp_le_exp.mpr hbC), hRgrid⟩, γR, hγR, heqR⟩,
      ⟨rL, ⟨fun i => (hL i).trans (Real.exp_le_exp.mpr hbC), hLgrid⟩, γL, hγL, heqL⟩⟩
  obtain ⟨rR, rL, hA, heq⟩ := exists_residue_class_lattice_factors D.realLattice f M A (hper g hg) hf
  exact ⟨rR, rL, fun c => ⟨(hA c).1.1, (hA c).1.2, (hA c).2.1, (hA c).2.2⟩, heq⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSquareRecovery
namespace OAI

section

namespace Erdos3

theorem recover_middle_coset_of_left_class {G : Type*} [Group G] (Γ : Subgroup G)
    (e b r κ t z γ : G) (hfactor : e * b * r * κ = t)
    (hγ : γ ∈ Γ) (hr : r = γ * z) :
    (QuotientGroup.mk b : G ⧸ Γ) = QuotientGroup.mk (e⁻¹ * t * κ⁻¹ * z⁻¹) := by
  have heq : e⁻¹ * t * κ⁻¹ * z⁻¹ = b * γ := by
    rw [← hfactor, hr]
    group
  rw [heq]
  exact (QuotientGroup.mk_mul_of_mem b hγ).symm

theorem recover_mapped_middle_coset_of_left_class {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (Λ : Subgroup H) (e b r κ t : G) (z γ : H)
    (hfactor : e * b * r * κ = t) (hγ : γ ∈ Λ) (hr : φ r = γ * z) :
    (QuotientGroup.mk (φ b) : H ⧸ Λ) =
      QuotientGroup.mk ((φ e)⁻¹ * φ t * (φ κ)⁻¹ * z⁻¹) := by
  apply recover_middle_coset_of_left_class Λ (φ e) (φ b) (φ r) (φ κ) (φ t) z γ _ hγ hr
  simpa only [map_mul] using congrArg φ hfactor

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_normalized_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          let Q := D.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
            (E.basis.baseChange ℝ)
          letI := Q.metricSpace
          letI := E.metricSpace
          let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
          ∀ κ : D.RealGroup, κ ∈ D.realLattice → ∀ r : E.RealGroup,
            (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ a b : E.RealGroup,
              (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
              ∀ x y : D.RealGroup,
                dist (QuotientGroup.mk (a * ψ x * (ψ κ⁻¹ * r)) : E.Space)
                    (QuotientGroup.mk (b * ψ y * (ψ κ⁻¹ * r))) ≤
                  Real.exp ((p + C) ^ C) * dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) +
                    dist a b := by
  obtain ⟨c₀, _, hcover⟩ := exists_uniform_conjugated_source_cover s
  obtain ⟨c₁, _, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s k
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c₀) ^ c₀ + (X + 1 + Polynomial.C c₁) ^ c₁ + (X + 1 + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ⟩ :=
    hcover D E φ p hp hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let t := p + 1
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hsum : (p + c₀) ^ c₀ + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcoverC : (p + c₀) ^ c₀ ≤ (p + C) ^ C := by
    nlinarith [pow_nonneg (show 0 ≤ t + c₁ by positivity) c₁, sq_nonneg (t + 2)]
  have hmetricC : (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    nlinarith [pow_nonneg (show 0 ≤ p + c₀ by positivity) c₀]
  let H := ⌈Real.exp p⌉₊
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  obtain ⟨A, _, hA, hALip⟩ := hleft (E.basis.baseChange ℝ) (lieStructureConstants E.basis) H t
    E.filtration.realification.lowerCentralSeries_eq_bot
    (fun i j k => (realLieBasis_structure E.basis i j k).symm) ht
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt) (ceil_exp_le_exp_add_one hp)
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
  obtain ⟨B, _, hB, hBLip⟩ := exists_realificationMap_lipschitz_exp_bound
    (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot)
    D.basis E.basis φ H ht
    (by simpa only [Fintype.card_fin] using hD.1.trans hpt)
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt) (ceil_exp_le_exp_add_one hp)
    (fun i j => rationalHeightLE_ceil_exp (hφ i j))
  have hAB : ((A * B : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp ((t + c₁) ^ c₁) * Real.exp ((t + 2) ^ 2) := by push_cast; gcongr
      _ = Real.exp ((t + c₁) ^ c₁ + (t + 2) ^ 2) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hmetricC
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcoverC),
    N, hN, hin, hout, hQ.mono Q hcoverC, ?_⟩
  let := Q.metricSpace
  let := E.metricSpace
  dsimp only
  intro κ hκ r hr a b ha x y
  have ha' : LipschitzWith A (fun z => a * z) := hALip a (fun i =>
    (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by dsimp [t]; linarith) k)))
  have hcompat := D.normalized_right_compatibility E φ q hq Λ htarget hΛ hnormal κ hκ r hr
  have hdist := native_frozenCosetMap_dist_le Q E φ _ a b hcompat hBLip ha' x y
  exact hdist.trans (add_le_add (mul_le_mul_of_nonneg_right hAB dist_nonneg) le_rfl)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_left_class_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          let Q := D.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
            (E.basis.baseChange ℝ)
          letI := Q.metricSpace
          letI := E.metricSpace
          let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
          ∀ κ : D.RealGroup, κ ∈ D.realLattice → ∀ z : E.RealGroup,
            (E.basis.baseChange ℝ).equivFun z.coord ∈ realDenominatorGrid q →
            ∀ a a' b b' r r' x x' : D.RealGroup,
              a * b * r * κ = x → a' * b' * r' * κ = x' →
              (∃ γ ∈ E.realLattice, ψ r = γ * z) → (∃ γ ∈ E.realLattice, ψ r' = γ * z) →
              (∀ i, |(E.basis.baseChange ℝ).repr ((ψ a)⁻¹).coord i| ≤ Real.exp ((p + 2) ^ k)) →
              dist (QuotientGroup.mk (ψ b) : E.Space) (QuotientGroup.mk (ψ b')) ≤
                Real.exp ((p + C) ^ C) * dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk x') +
                  dist (ψ a)⁻¹ (ψ a')⁻¹ := by
  obtain ⟨C, hC, hrecovery⟩ := exists_uniform_normalized_recovery s k
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, hmetric⟩ :=
    hrecovery D E φ hp hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, ?_⟩
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := Q.metricSpace
  let := E.metricSpace
  dsimp only
  intro κ hκ z hz a a' b b' r r' x x' hfactor hfactor' hr hr' ha
  obtain ⟨γ, hγ, hr⟩ := hr
  obtain ⟨γ', hγ', hr'⟩ := hr'
  have hrecover := recover_mapped_middle_coset_of_left_class ψ E.realLattice a b r κ x z γ hfactor hγ hr
  have hrecover' := recover_mapped_middle_coset_of_left_class ψ E.realLattice a' b' r' κ x' z γ' hfactor' hγ' hr'
  have hzinv : (E.basis.baseChange ℝ).equivFun (z⁻¹).coord ∈ realDenominatorGrid q := by
    simpa only [coord_inv, map_neg] using realDenominatorGrid_neg q hz
  rw [hrecover, hrecover']
  simpa only [map_inv, mul_assoc] using hmetric κ hκ z⁻¹ hzinv (ψ a)⁻¹ (ψ a')⁻¹ ha x x'

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlowInverseControl
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_slow_inverse_control (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
        D.filtration.PolynomialSlowBound D.basis w T (Real.exp ((p + 2) ^ r)) g →
        (∀ (v : σ → ℝ), (∀ i, |v i| ≤ T i) → ∀ i,
          |(D.basis.baseChange ℝ).repr (D.filtration.adaptedPolynomialRealValueHom w v g)⁻¹.coord i| ≤
            Real.exp ((p + 2) ^ C)) ∧
        (∀ (v z : σ → ℝ) (δ : ℝ), 0 ≤ δ →
          (∀ i, |v i| ≤ T i) → (∀ i, |z i| ≤ T i) →
          (∀ i, |v i - z i| ≤ T i * δ) →
          letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            (D.basis.baseChange ℝ)
          dist (D.filtration.adaptedPolynomialRealValueHom w v g)⁻¹
            (D.filtration.adaptedPolynomialRealValueHom w z g)⁻¹ ≤
              Real.exp ((p + 2) ^ C) * δ) := by
  obtain ⟨A, _, hmetric⟩ := exists_polynomialSlowBound_dist_exp s r
  let X : Polynomial ℕ := Polynomial.X
  let P := Polynomial.C s * (X + 1) + (X + 2) ^ r + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hD hσ T hT g hg
  have hinv := (D.filtration.polynomialSlowBound_inv_iff D.basis w T _ g).mpr hg
  have hsum : (s : ℝ) * (p + 1) + (p + 2) ^ r + (p + A) ^ A ≤ (p + 2) ^ C := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  have hcoord : (s : ℝ) * (p + 1) + (p + 2) ^ r ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans hsum
  have hdist : (p + A) ^ A ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hsum
  constructor
  · intro v hv i
    have hvbound := D.filtration.polynomialSlowBound_value D.basis w hw T hT
      (Real.exp_pos _).le g⁻¹ hinv v hv i
    rw [map_inv] at hvbound
    apply hvbound.trans
    have hn1 : (Fintype.card σ : ℝ) + 1 ≤ Real.exp p := by
      linarith [Real.add_one_le_exp p]
    calc
      _ ≤ Real.exp s * (Real.exp p) ^ s * Real.exp ((p + 2) ^ r) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (Real.add_one_le_exp (s : ℝ))
            (pow_le_pow_left₀ (by positivity) hn1 _) (by positivity) (Real.exp_pos _).le)
          (Real.exp_pos _).le
      _ = Real.exp ((s : ℝ) * (p + 1) + (p + 2) ^ r) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hcoord
  · intro v z δ hδ hv hz hvz
    have hm := hmetric D w hw p hp hD hσ T hT g⁻¹ hinv v z δ hδ hv hz hvz
    simp only [map_inv] at hm
    exact hm.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hdist) hδ)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SlowResidueRecovery
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_residue_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L M : Type*} [Fintype σ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) (w : σ → ℕ), (∀ i, 0 < w i) → ∀ {p : ℝ},
      0 ≤ p → (Fintype.card σ : ℝ) ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ P m : ℕ, 0 < P ∧ 0 < m ∧
        (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
          (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
          (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ (N : ℕ) (hN : 0 < N)
            (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
            (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
            let Q := D.withLattice Λ N hN hin hout
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
              (E.basis.baseChange ℝ)
            letI := Q.metricSpace
            letI := E.metricSpace
            let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
              (hM := E.filtration.lowerCentralSeries_eq_bot) φ
            ∀ R : (E.filtration.realification.adaptedPolynomialFiltration w).Group,
              E.filtration.PolynomialRationalGrid E.basis w q R →
              ∃ z : (σ → ZMod P) → E.RealGroup,
                (∀ c, (∀ i, |(E.basis.baseChange ℝ).repr (z c).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
                  (E.basis.baseChange ℝ).equivFun (z c).coord ∈ realDenominatorGrid m) ∧
                ∀ κ : D.RealGroup, κ ∈ D.realLattice →
                  ∀ a b r f : (σ → ℤ) → D.RealGroup,
                    (∀ x, a x * b x * r x * κ = f x) →
                    (∀ x, ψ (r x) = E.filtration.adaptedPolynomialRealValueHom w
                      (fun i => (x i : ℝ)) R) →
                    (∀ x, (QuotientGroup.mk (ψ (b x)) : E.Space) =
                      QuotientGroup.mk ((ψ (a x))⁻¹ * ψ (f x) * (ψ κ)⁻¹ *
                        (z (fun i => (x i : ZMod P)))⁻¹)) ∧
                    ∀ x y, (fun i => (x i : ZMod P)) = (fun i => (y i : ZMod P)) →
                      (∀ i, |(E.basis.baseChange ℝ).repr ((ψ (a x))⁻¹).coord i| ≤
                        Real.exp ((p + 2) ^ k)) →
                      dist (QuotientGroup.mk (ψ (b x)) : E.Space) (QuotientGroup.mk (ψ (b y))) ≤
                        Real.exp ((p + C) ^ C) * dist (QuotientGroup.mk (f x) : Q.Space)
                          (QuotientGroup.mk (f y)) + dist (ψ (a x))⁻¹ (ψ (a y))⁻¹ := by
  obtain ⟨A, _, hresidue⟩ := exists_native_residue_representatives s
  obtain ⟨B, _, hrecovery⟩ := exists_uniform_left_class_recovery s k
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  let U := T + (T + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget U
  refine ⟨C, hC, ?_⟩
  intro σ L M _ _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ w hw p hp hσ hD hE hφ q hq hqp
  obtain ⟨P, m, hP, hm, hPb, hmb, hrepresentatives⟩ := hresidue E w hw p hp hE hσ q hq hqp
  let t := p + (p + A) ^ A
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, hmetric⟩ :=
    hrecovery D E φ ht (hD.mono D hpt) (hE.mono E hpt) (fun i j => (hφ i j).trans hpt)
      m hm (hmb.trans (Real.exp_le_exp.mpr hAt))
  let Q := D.withLattice Λ N hN hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  have hsum : t + (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [U, T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans hsum
  have hcost : (t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  refine ⟨P, m, hP, hm, hPb.trans (Real.exp_le_exp.mpr (hAt.trans htC)),
    hmb.trans (Real.exp_le_exp.mpr (hAt.trans htC)), Λ, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr hcost), N, hN, hin, hout, hQ.mono Q hcost, ?_⟩
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := Q.metricSpace
  let := E.metricSpace
  dsimp only
  intro R hR
  obtain ⟨_, z, hz, hclasses⟩ := hrepresentatives R hR
  refine ⟨z, fun c => ⟨fun i => ((hz c).2.2.1 i).trans
    (Real.exp_le_exp.mpr (hAt.trans htC)), (hz c).2.2.2⟩, ?_⟩
  intro κ hκ a b r f hfactor hvalue
  have hleft (x : σ → ℤ) : ∃ γ ∈ E.realLattice, ψ (r x) = γ * z (fun i => (x i : ZMod P)) := by
    obtain ⟨γ, hγ, heq⟩ := (hclasses x).2
    exact ⟨γ, hγ, (hvalue x).trans heq⟩
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨γ, hγ, heq⟩ := hleft x
    exact recover_mapped_middle_coset_of_left_class ψ E.realLattice
      (a x) (b x) (r x) κ (f x) _ γ (hfactor x) hγ heq
  · intro x y hxy ha
    have hy : ∃ γ ∈ E.realLattice, ψ (r y) = γ * z (fun i => (x i : ZMod P)) := by
      rw [hxy]
      exact hleft y
    have ha' : ∀ i, |(E.basis.baseChange ℝ).repr ((ψ (a x))⁻¹).coord i| ≤ Real.exp ((t + 2) ^ k) :=
      fun i => (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) k))
    have hdist := hmetric κ hκ (z (fun i => (x i : ZMod P))) ((hz _).2.2.2)
      (a x) (a y) (b x) (b y) (r x) (r y) (f x) (f y) (hfactor x) (hfactor y) (hleft x) hy ha'
    exact hdist.trans (add_le_add
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) dist_nonneg) le_rfl)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_slow_residue_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L M : Type*} [Fintype σ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) (w : σ → ℕ), (∀ i, 0 < w i) → ∀ {p : ℝ},
      0 ≤ p → (Fintype.card σ : ℝ) ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ P m : ℕ, 0 < P ∧ 0 < m ∧
        (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
          (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
          (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ (N : ℕ) (hN : 0 < N)
            (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
            (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
            let Q := D.withLattice Λ N hN hin hout
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            letI := Q.metricSpace
            letI := E.metricSpace
            let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
              (hM := E.filtration.lowerCentralSeries_eq_bot) φ
            ∀ R : (E.filtration.realification.adaptedPolynomialFiltration w).Group,
              E.filtration.PolynomialRationalGrid E.basis w q R →
              ∃ z : (σ → ZMod P) → E.RealGroup,
                (∀ c, (∀ i, |(E.basis.baseChange ℝ).repr (z c).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
                  (E.basis.baseChange ℝ).equivFun (z c).coord ∈ realDenominatorGrid m) ∧
                ∀ κ : D.RealGroup, κ ∈ D.realLattice →
                  ∀ a b r f : (σ → ℤ) → D.RealGroup,
                    (∀ x, a x * b x * r x * κ = f x) →
                    (∀ x, ψ (r x) = E.filtration.adaptedPolynomialRealValueHom w
                      (fun i => (x i : ℝ)) R) →
                    (∀ x, (QuotientGroup.mk (ψ (b x)) : E.Space) =
                      QuotientGroup.mk ((ψ (a x))⁻¹ * ψ (f x) * (ψ κ)⁻¹ *
                        (z (fun i => (x i : ZMod P)))⁻¹)) ∧
                    ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
                      ∀ S : (E.filtration.realification.adaptedPolynomialFiltration w).Group,
                        E.filtration.PolynomialSlowBound E.basis w T (Real.exp ((p + 2) ^ k)) S →
                        (∀ x, ψ (a x) = E.filtration.adaptedPolynomialRealValueHom w
                          (fun i => (x i : ℝ)) S) →
                        ∀ x y, (fun i => (x i : ZMod P)) = (fun i => (y i : ZMod P)) →
                          ∀ δ : ℝ, 0 ≤ δ →
                            (∀ i, |(x i : ℝ)| ≤ T i) → (∀ i, |(y i : ℝ)| ≤ T i) →
                            (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ T i * δ) →
                            dist (QuotientGroup.mk (ψ (b x)) : E.Space) (QuotientGroup.mk (ψ (b y))) ≤
                              Real.exp ((p + C) ^ C) *
                                (dist (QuotientGroup.mk (f x) : Q.Space) (QuotientGroup.mk (f y)) + δ) := by
  obtain ⟨A, _, hslow⟩ := exists_slow_inverse_control s k
  obtain ⟨B, _, hresidue⟩ := exists_uniform_residue_recovery s A
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C B) ^ B + (X + 2) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget U
  refine ⟨C, hC, ?_⟩
  intro σ L M _ _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ w hw p hp hσ hD hE hφ q hq hqp
  obtain ⟨P, m, hP, hm, hPb, hmb, Λ, hΛ, hchar, hnormal, hfinite, hindex,
    N, hN, hin, hout, hQ, hrecover⟩ := hresidue D E φ w hw hp hσ hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  have hsum : (p + B) ^ B + (p + 2) ^ A ≤ (p + C) ^ C := by
    simpa [U, X, Polynomial.eval₂_pow] using hbudget p hp
  have hBC : (p + B) ^ B ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans hsum
  have hAC : (p + 2) ^ A ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (by positivity) _)).trans hsum
  refine ⟨P, m, hP, hm, hPb.trans (Real.exp_le_exp.mpr hBC), hmb.trans (Real.exp_le_exp.mpr hBC),
    Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hBC),
    N, hN, hin, hout, hQ.mono Q hBC, ?_⟩
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := Q.metricSpace
  let := E.metricSpace
  dsimp only
  intro R hR
  obtain ⟨z, hz, heval⟩ := hrecover R hR
  refine ⟨z, fun c => ⟨fun i => ((hz c).1 i).trans (Real.exp_le_exp.mpr hBC), (hz c).2⟩, ?_⟩
  intro κ hκ a b r f hfactor hvalue
  obtain ⟨hexact, hmove⟩ := heval κ hκ a b r f hfactor hvalue
  refine ⟨hexact, ?_⟩
  intro T hT S hS hslowvalue x y hxy δ hδ hx hy hdelta
  obtain ⟨hcoords, hdist⟩ := hslow E w hw p hp hE hσ T hT S hS
  have hleft : ∀ i, |(E.basis.baseChange ℝ).repr ((ψ (a x))⁻¹).coord i| ≤ Real.exp ((p + 2) ^ A) := by
    rw [hslowvalue x]
    exact hcoords (fun i => (x i : ℝ)) hx
  have hinverse : dist (ψ (a x))⁻¹ (ψ (a y))⁻¹ ≤ Real.exp ((p + 2) ^ A) * δ := by
    rw [hslowvalue x, hslowvalue y]
    exact hdist _ _ δ hδ hx hy hdelta
  apply (hmove x y hxy hleft).trans
  calc
    _ ≤ Real.exp ((p + B) ^ B) *
        dist (QuotientGroup.mk (f x) : Q.Space) (QuotientGroup.mk (f y)) +
          Real.exp ((p + 2) ^ A) * δ := add_le_add le_rfl hinverse
    _ ≤ Real.exp ((p + C) ^ C) *
        dist (QuotientGroup.mk (f x) : Q.Space) (QuotientGroup.mk (f y)) +
          Real.exp ((p + C) ^ C) * δ :=
      add_le_add (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hBC) dist_nonneg)
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hAC) hδ)
    _ = _ := (mul_add _ _ _).symm

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledRefilteredRecoveredExpansion
namespace OAI

section

namespace Erdos3

theorem positive_cell_residue_recovery
    {I J X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {P N : ℕ} [NeZero N] (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ)
    (label : I → ZMod P) (f : ℤ → X) (b : ℤ → Y) {R K ρ : ℝ}
    (hR : 0 ≤ R) (hρ : 0 < ρ)
    (hA : ∀ i x, 0 ≤ A i x)
    (hres : ∀ i x, 0 < A i x → (x.val : ZMod P) = label i)
    (hcircle : ∀ i x y, 0 < A i x → 0 < A i y →
      dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ)
    (hrecover : ∀ n m : ℤ, (n : ZMod P) = (m : ZMod P) →
      ∀ δ : ℝ, 0 ≤ δ → |(n : ℝ)| ≤ N → |(m : ℝ)| ≤ N →
        |(n : ℝ) - m| ≤ (N : ℝ) * δ →
        dist (b n) (b m) ≤ R * (dist (f n) (f m) + δ))
    (h : ZMod N) (i : I) (j : J) (x y : ZMod N)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hxy : 0 < A i x * B j (x + h)) (hyy : 0 < A i y * B j (y + h))
    (hinput : dist (f x.val) (f y.val) ≤ K * ρ) :
    dist (b x.val) (b y.val) ≤ R * (K + 1) * ρ := by
  have hpositive (z : ZMod N) (hz : 0 < A i z * B j (z + h)) : 0 < A i z := by
    rcases mul_pos_iff.mp hz with hz | hz
    · exact hz.1
    · linarith [hA i z]
  have hAx := hpositive x hxy
  have hAy := hpositive y hyy
  have hmod : ((x.val : ℤ) : ZMod P) = ((y.val : ℤ) : ZMod P) := by
    simpa only [Int.cast_natCast] using (hres i x hAx).trans (hres i y hAy).symm
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hbound (z : ZMod N) : |((z.val : ℤ) : ℝ)| ≤ (N : ℝ) := by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (Nat.le_of_lt (ZMod.val_lt z))
  have hdiff := good_circle_observations_control_representatives h x y hρ hx hy
    (hcircle i x y hAx hAy)
  rw [← sub_div, abs_div, abs_of_pos hN] at hdiff
  have hdiff' : |((x.val : ℤ) : ℝ) - ((y.val : ℤ) : ℝ)| ≤ (N : ℝ) * ρ := by
    simpa only [Int.cast_natCast, mul_comm ρ (N : ℝ)] using (div_le_iff₀ hN).mp hdiff
  calc
    _ ≤ R * (dist (f x.val) (f y.val) + ρ) :=
      hrecover x.val y.val hmod ρ hρ.le (hbound x) (hbound y) hdiff'
    _ ≤ R * (K * ρ + ρ) := mul_le_mul_of_nonneg_left
      (by linarith : dist (f x.val) (f y.val) + ρ ≤ K * ρ + ρ) hR
    _ = _ := by ring

end Erdos3

end

section

universe u v w

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_cyclic_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeCyclicRecoverySpec.{u, v, w} s k C := by
  obtain ⟨C, hC, hrec⟩ := exists_slow_residue_recovery s k
  refine ⟨C, hC, ?_⟩
  dsimp only [NativeCyclicRecoverySpec]
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨P, m, hP, hm, hPb, hmb, Λ, hΛ, hchar, hnormal, hfinite, hindex,
      l, hl, hin, hout, hQ, hrecover⟩ :=
    hrec D E φ (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) hp0
      (by simpa only [Fintype.card_unit, Nat.cast_one] using hp) hD hE hφ q hq hqp
  let Q := D.withLattice Λ l hl hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  refine ⟨P, m, hP, hm, hPb, hmb, Λ, hΛ, hchar, hnormal, hfinite, hindex,
    l, hl, hin, hout, hQ, ?_⟩
  let := Q.metricSpace
  let := E.metricSpace
  intro R hR
  obtain ⟨z, hz, heval⟩ := hrecover R hR
  refine ⟨z, hz, ?_⟩
  intro κ hκ a b r f hfactor hvalue
  obtain ⟨hexact, hmove⟩ := heval κ hκ a b r f hfactor hvalue
  refine ⟨hexact, ?_⟩
  intro N _ S hS hSvalue I J A B label ρ K hρ hA hres hcircle h i j x y hx hy hxy hyy hinput
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  apply positive_cell_residue_recovery A B label
    (fun n => (QuotientGroup.mk (f (fun _ => n)) : Q.Space))
    (fun n => (QuotientGroup.mk (ψ (b (fun _ => n))) : E.Space))
    (Real.exp_pos _).le hρ hA hres hcircle ?_ h i j x y hx hy hxy hyy hinput
  intro n m hmod δ hδ hn hm hdiff
  exact hmove (fun _ : Unit => (N : ℝ)) (fun _ => hN) S hS hSvalue
    (fun _ => n) (fun _ => m) (funext (fun _ => hmod)) δ hδ
    (fun _ => hn) (fun _ => hm) (fun _ => hdiff)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem exists_refiltered_recovered_expansion (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
      [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
      (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
      (Q : RationalFilteredNilmanifold
        (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
      [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]
      {p b : ℝ} {q P₀ : ℕ}, 1 ≤ p → p ≤ b → (Fintype.card ι : ℝ) ≤ b →
      (∀ i, (D i).GeometryComplexityLE b) → 0 < q → (q : ℝ) ≤ Real.exp b →
      0 < P₀ → (P₀ : ℝ) ≤ Real.exp b →
      RefilteredResidueExpansionSpec D a W E Q p q r P₀ b →
      RefilteredRecoveredExpansionSpec D a W E Q p q r ((b + C) ^ C) := by
  obtain ⟨a₀, _, hrecover⟩ := exists_native_cyclic_recovery.{u, u, u} (s + 1) r
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + 2) ^ 2 + X + 1
  let R := (T + Polynomial.C a₀) ^ a₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + X + R)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ d D a W e n E Q _ _ _ _ p b q P₀ hp hpb hι hD hq hqb hP₀ hP₀b hbase
  classical
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := realification_moduleTopology_t2 Q.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨Q', hQF, hQb, hQle, hQ, Z, hZF, hZb, hZle, hZ, hbase⟩ := hbase
  let t := (b + 2) ^ 2 + b + 1
  let cost := (b + C) ^ C
  have hb : 0 ≤ b := by linarith
  have hbt : b ≤ t := by dsimp [t]; nlinarith [sq_nonneg (b + 2)]
  have ht : 0 ≤ t := hb.trans hbt
  have hsum : t + b + (t + a₀) ^ a₀ ≤ cost := by
    simpa [T, R, X, t, cost, Polynomial.eval₂_pow] using hbudget b hb
  have hrecpos : 0 ≤ (t + a₀) ^ a₀ := pow_nonneg (by positivity) _
  have hbCost : b ≤ cost := by linarith
  have hrecCost : (t + a₀) ^ a₀ ≤ cost := by linarith
  have hbothCost : b + (t + a₀) ^ a₀ ≤ cost := by linarith
  have hI₀ : (Fintype.card I₀ : ℝ) ≤ b :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hι
  have hZ₀ : Z₀.GeometryComplexityLE t :=
    (pi_geometry (fun i : I₀ => D i.val) hb hI₀ (fun i => hD i.val)).mono Z₀
      (by dsimp [t]; linarith)
  let idLie : (∀ i : I₀, L i.val) →ₗ⁅ℚ⁆ (∀ i : I₀, L i.val) := LieHom.id
  have hheight (i j : Fin (Fintype.card (Σ i : I₀, Fin (d i.val)))) :
      rationalLogHeight (Z.basis.repr (idLie (Z₀.basis j)) i) ≤ t := by
    rw [hZb]
    change rationalLogHeight (Z₀.basis.repr (Z₀.basis j) i) ≤ t
    rw [Basis.repr_self]
    by_cases h : j = i <;> simp [h, rationalLogHeight, ht]
  obtain ⟨P₁, _, hP₁, _, hP₁b, _, Λ, hΛ, hchar, hnormal, hfinite, hindex,
      l, hl, hin, hout, hV, hrec⟩ := hrecover Z₀ Z idLie (hp.trans (hpb.trans hbt))
        hZ₀ (hZ.mono Z hbt) hheight q hq (hqb.trans (Real.exp_le_exp.mpr hbt))
  have hP : ((P₀ * P₁ : ℕ) : ℝ) ≤ Real.exp cost := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp b * Real.exp ((t + a₀) ^ a₀) :=
        mul_le_mul hP₀b hP₁b (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (b + (t + a₀) ^ a₀) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hbothCost
  refine ⟨P₀ * P₁, Nat.mul_pos hP₀ hP₁, hP, Q', hQF, hQb, hQle, hQ.mono Q' hbCost,
    Z, hZF, hZb, hZle, hZ.mono Z hbCost, Λ, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr hrecCost), l, hl, hin, hout, hV.mono _ hrecCost, ?_⟩
  let V := Z₀.withLattice Λ l hl hin hout
  let := V.metricSpace
  let := Z.metricSpace
  let Ψ := realificationMap (hnil := Z₀.filtration.lowerCentralSeries_eq_bot)
    (hM := Z.filtration.lowerCentralSeries_eq_bot) idLie
  have hΨ (x : Z₀.RealGroup) : Ψ x = x := by
    apply NilpotentLieBCHGroup.ext
    exact realificationLieHom_id_apply x.coord
  dsimp only [Ψ] at hΨ
  dsimp only
  intro J₀ freq hfreq N _ I J _ _ A B label ρ K hρ hK hA hB hAsum hBsum hres hcircle
    S hS hpositive hinvariant slow middle rat κ g hκ hfactor hslow hrat hmiddle
    slowZ ratZ κZ fZ hκZ hfactorZ hslowZ hratZ hinput
  let w := fun _ : Unit => 1
  let ψ := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := Z.filtration.lowerCentralSeries_eq_bot)
    (liePiMap (fun i : I₀ => refilteredComponentMap D W i.val))
  let π₀ := ZMod.castHom (dvd_mul_right P₀ P₁) (ZMod P₀)
  let π₁ := ZMod.castHom (dvd_mul_left P₁ P₀) (ZMod P₁)
  let label₀ := fun i => π₀ (label i)
  let label₁ := fun i => π₁ (label i)
  have hres₀ (i : I) (x : ZMod N) (hx : 0 < A i x) : (x.val : ZMod P₀) = label₀ i := by
    simpa only [map_natCast] using congrArg π₀ (hres i x hx)
  have hres₁ (i : I) (x : ZMod N) (hx : 0 < A i x) : (x.val : ZMod P₁) = label₁ i := by
    simpa only [map_natCast] using congrArg π₁ (hres i x hx)
  have hslowZ' (h : ZMod N) : Z.filtration.PolynomialSlowBound Z.basis w
      (fun _ => (N : ℝ)) (Real.exp ((t + 2) ^ r)) (slowZ h) :=
    Z.filtration.polynomialSlowBound_mono Z.basis w (fun _ => (N : ℝ))
      (fun _ => Nat.cast_pos.mpr (NeZero.pos N))
      (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ p + 2)
        (by linarith : p + 2 ≤ t + 2) r)) (slowZ h) (hslowZ h)
  let η := Real.exp ((t + a₀) ^ a₀) * (K + 1) * ρ
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hdiam (i : I) (j : J) (h x y : ZMod N)
      (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
      (hxy : 0 < A i x * B j (x + h)) (hyy : 0 < A i y * B j (y + h)) :
      dist (QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w
        (fun _ => (x.val : ℤ)) (g h))) : Z.Space)
        (QuotientGroup.mk (ψ (E.filtration.realification.polynomialOrbitEval w
          (fun _ => (y.val : ℤ)) (g h)))) ≤ η := by
    obtain ⟨_, _, hmove⟩ := hrec (ratZ h) (hratZ h)
    obtain ⟨_, hcell⟩ := hmove (κZ h) (hκZ h)
      (fun x => Z.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (slowZ h))
      (fun x => ψ (E.filtration.realification.polynomialOrbitEval w x (g h)))
      (fun x => Z.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) (ratZ h))
      (fZ h) (hfactorZ h) (fun _ => hΨ _)
    have hd := hcell N (slowZ h) (hslowZ' h) (fun _ => hΨ _)
      A B label₁ hρ hA hres₁ hcircle h i j x y hx hy hxy hyy (hinput i j h x y hx hy hxy hyy)
    simpa only [hΨ] using hd
  obtain ⟨U, hU, hUcomplexity, hUempty, err, herr, hmean⟩ :=
    hbase freq hfreq N A B label₀ hρ hη hA hB hAsum hBsum hres₀ hcircle
      S hS hpositive hinvariant slow middle rat κ g hκ hfactor hslow hrat hmiddle hdiam
  refine ⟨U, hU, fun i j h => (hUcomplexity i j h).mono (by linarith), hUempty, err, herr, ?_⟩
  intro h
  have hρR : ρ ≤ Real.exp ((t + a₀) ^ a₀) * ρ := by
    nlinarith [Real.one_le_exp hrecpos]
  have hprod := mul_le_mul_of_nonneg_left
    (show ρ + η ≤ Real.exp ((t + a₀) ^ a₀) * ρ + η by linarith) (Real.exp_pos b).le
  calc
    _ ≤ Real.exp b * (ρ + η) + 6 * ρ + 3 / N := hmean h
    _ ≤ Real.exp b * (Real.exp ((t + a₀) ^ a₀) * ρ + η) + 6 * ρ + 3 / N := by linarith
    _ = Real.exp (b + (t + a₀) ^ a₀) * (K + 2) * ρ + 6 * ρ + 3 / N := by
      rw [Real.exp_add]
      dsimp [η]
      ring
    _ ≤ Real.exp cost * (K + 2) * ρ + 6 * ρ + 3 / N := by
      have hh := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbothCost)
        (show 0 ≤ (K + 2) * ρ by positivity)
      nlinarith

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_controlled_refiltered_recovered_expansion_s2_oai (s r : ℕ) :
    ∃ A B : ℕ, 2 ≤ A ∧ 2 ≤ B ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type u} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {κ : Type*} [Fintype κ] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
      (w : ∀ i, Fin (d i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j =
        Submodule.span ℚ ((D i).basis '' {b | j ≤ w i b}))
      (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v₀ : κ → (pi D).filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v₀) = W.toSubmodule) {p : ℝ},
      1 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i b, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis
        (productBasisWeight w) (pi_layer_span D w hF)).repr (v₀ i) b) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W)
          (s + 1) (finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = (pi D).filtration.gradedRefiltration W ∧
        E.lattice = (pi D).lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := ((pi D).filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            ((pi D).filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + A) ^ A) ∧
        ∃ n : ℕ, n ≤ finrank ℚ ((pi D).filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + A) ^ A) ∧
            (nativeRefilteredTarget D a W E Q).GeometryComplexityLE ((p + A) ^ A) ∧
            RefilteredRecoveredExpansionSpec D a W E Q p q r (((p + A) ^ A + B) ^ B) := by
  obtain ⟨A, hA, hmodels⟩ := exists_controlled_refiltered_residue_expansion_s2 s r
  obtain ⟨B, hB, hrecover⟩ := exists_refiltered_recovered_expansion s r
  refine ⟨A, B, hA, hB, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ κ _ d D a w hF W v₀ hspan p hp hι hD hκ hv q hq hqp
  obtain ⟨P, hP, hPb, E, hEF, hEL, hE, n, hn, Q, hQF, hQL, hQ, htarget, hbase⟩ :=
    hmodels D a w hF W v₀ hspan hp hι hD hκ hv q hq hqp
  have hAℝ : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hpA : p ≤ (p + A) ^ A :=
    (le_power_budget (by linarith) (by omega : 1 ≤ A)).trans
      (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ p + 2) (by linarith) A)
  refine ⟨E, hEF, hEL, hE, n, hn, Q, hQF, hQL, hQ, htarget, ?_⟩
  exact hrecover D a W E Q hp hpA (hι.trans hpA) (fun i => (hD i).mono (D i) hpA)
    hq (hqp.trans (Real.exp_le_exp.mpr hpA)) hP hPb hbase

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

theorem solution.{u, u_1} : type_of% @OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_refiltered_recovered_expansion_s2_oai.{u, u_1} := @OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_refiltered_recovered_expansion_s2_oai.{u, u_1}
