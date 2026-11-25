-- Prove2me | solution 1 for GlobalTheory.PlaceMono.place_monogenic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:21:23.149796+00:00
-- url     : https://prove2.me/submissions/d76b1bea-f744-4cee-a7de-49a98be288f6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueMaximalAbovePlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DifferentPowerUnramifiedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicUnitQuotientPrincipalBasis
import Theorems.Thm_Formalism_L2_Pj_AvAlg_exists_adjoin_eq_top
import Theorems.Thm_GlobalTheory_OnePrime_exists_prime_under
import Theorems.Thm_GlobalTheory_OnePrime_maximal_unique
import Theorems.Thm_GlobalTheory_OnePrime_nontrivial_Ow
import Theorems.Thm_GlobalTheory_Proof_different_power_unramified_iff_map_eq_top_of_coprime
import Theorems.Thm_GlobalTheory_Proof_different_power_unramified_iff_ow_p_torsionFree
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mul
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_mul
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
noncomputable section
namespace GlobalTheory.PlaceMono
section SlopeTestRemainingChoices
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
private theorem isDomain_of_span {A : Type} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {π : A} (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π}) (hreg : π ∈ nonZeroDivisors A) :
    IsDomain A := by
  classical
  have hkrull : ⨅ i : ℕ, (IsLocalRing.maximalIdeal A) ^ i = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top

  have hfac : ∀ a : A, a ≠ 0 → ∃ (k : ℕ) (u : A), IsUnit u ∧ a = π ^ k * u := by
    intro a ha
    have hex : ∃ n : ℕ, a ∉ (IsLocalRing.maximalIdeal A) ^ n := by
      by_contra h
      push_neg at h
      apply ha
      have hmem : a ∈ ⨅ i : ℕ, (IsLocalRing.maximalIdeal A) ^ i := Submodule.mem_iInf _ |>.2 h
      rwa [hkrull, Ideal.mem_bot] at hmem
    have hn : a ∉ (IsLocalRing.maximalIdeal A) ^ Nat.find hex := Nat.find_spec hex
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := by
      refine Nat.exists_eq_succ_of_ne_zero fun h0 => hn ?_
      rw [h0, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    have hak : a ∈ (IsLocalRing.maximalIdeal A) ^ k := by
      by_contra h
      exact Nat.find_min hex (by omega) h
    rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hak
    obtain ⟨u, hu⟩ := hak
    refine ⟨k, u, ?_, by rw [← hu, mul_comm]⟩
    by_contra hu'
    apply hn
    have hum : u ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal u).2 hu'
    rw [hπ, Ideal.mem_span_singleton'] at hum
    obtain ⟨c, hc⟩ := hum
    rw [hk, hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨c, by rw [← hu, ← hc, pow_succ]; ring⟩
  have hnzd : NoZeroDivisors A := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra h
    push_neg at h
    obtain ⟨k, u, hu, rfl⟩ := hfac a h.1
    obtain ⟨l, v, hv, rfl⟩ := hfac b h.2
    have h1 : (u * v) * π ^ (k + l) = 0 := by rw [← hab]; ring
    have h2 : u * v = 0 :=
      (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hreg (k + l))).1 h1
    exact (hu.mul hv).ne_zero h2
  exact NoZeroDivisors.to_isDomain A
variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]
private theorem exists_dvr [IsDedekindDomain R] [CharZero R] [Module.Finite ℤ R]
    (w : Place p R) : ∃ _ : IsDomain w.Ow, IsDiscreteValuationRing w.Ow := by
  classical
  have := GlobalTheory.OnePrime.nontrivial_Ow w
  obtain ⟨P, hP, hpP, hm, hQ⟩ := GlobalTheory.OnePrime.exists_prime_under p R w
  have : IsLocalRing w.Ow :=
    IsLocalRing.of_unique_max_ideal ⟨_, hm, fun N hN => GlobalTheory.OnePrime.maximal_unique w _ N hm hN⟩
  have : IsNoetherianRing w.Ow := IsNoetherianRing.of_finite ℤ_[p] w.Ow
  have hM : IsLocalRing.maximalIdeal w.Ow = P.map w.toOw := (IsLocalRing.eq_maximalIdeal hm).symm
  have hp0 : (p : R) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hP0 : P ≠ ⊥ := fun h => hp0 (by rwa [h, Ideal.mem_bot] at hpP)
  have hpow : ∀ a : R, a ≠ 0 → ∃ (k : ℕ) (Q : Ideal R), Ideal.span {a} = P ^ k * Q ∧ P ⊔ Q = ⊤ ∧
      Ideal.span {w.toOw a} = P.map w.toOw ^ k := by
    intro a ha
    have ha0 : Ideal.span {a} ≠ ⊥ := by simpa using ha
    obtain ⟨Q, hPQ, hQe⟩ := Ideal.eq_prime_pow_mul_coprime ha0 P
    generalize Multiset.count P _ = e at hQe
    have hQ0 : Q ≠ ⊥ := by rintro rfl; exact ha0 (by simpa using hQe)
    refine ⟨e, Q, hQe, hPQ, ?_⟩
    have := congrArg (Ideal.map w.toOw) hQe
    rwa [Ideal.map_span, Set.image_singleton, Ideal.map_mul, Ideal.map_pow,
      GlobalTheory.Proof.different_power_unramified_iff.map_eq_top_of_coprime _ P hP hQ Q hQ0 hPQ, Ideal.mul_top] at this
  obtain ⟨a, ha1, ha2⟩ := Ideal.exists_mem_pow_notMem_pow_succ P hP0 hP.ne_top 1
  have ha0 : a ≠ 0 := by rintro rfl; exact ha2 (zero_mem _)
  have hπ : IsLocalRing.maximalIdeal w.Ow = Ideal.span {w.toOw a} := by
    obtain ⟨k, Q, h1, h2, h3⟩ := hpow a ha0
    rw [pow_one] at ha1
    have hk : k ≤ 1 := by
      by_contra hk
      apply ha2
      refine (Ideal.span_singleton_le_iff_mem _).1 ?_
      rw [h1]
      exact Ideal.mul_le_left.trans (Ideal.pow_le_pow_right (Nat.succ_le_of_lt (not_le.1 hk)))
    rw [hM]
    apply le_antisymm
    · rw [h3]
      conv_lhs => rw [← pow_one (P.map w.toOw)]
      exact Ideal.pow_le_pow_right hk
    · exact (Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_map_of_mem _ ha1)
  have hpM : (p : w.Ow) ∈ IsLocalRing.maximalIdeal w.Ow := by
    rw [hM, ← map_natCast w.toOw]; exact Ideal.mem_map_of_mem _ hpP
  have hpreg : (p : w.Ow) ∈ nonZeroDivisors w.Ow :=
    mem_nonZeroDivisors_iff_left.2 (GlobalTheory.Proof.different_power_unramified_iff.ow_p_torsionFree p R w)
  have hreg : w.toOw a ∈ nonZeroDivisors w.Ow := by
    have h := hpM
    rw [hπ, Ideal.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    rw [hc] at hpreg
    exact (mul_mem_nonZeroDivisors.1 hpreg).1
  have hd := isDomain_of_span hπ hreg
  refine ⟨hd, ?_⟩
  have hnf : ¬ IsField w.Ow := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    intro h
    rw [h, Ideal.mem_bot] at hpM
    exact nonZeroDivisors.ne_zero hpreg hpM
  have hpr : (IsLocalRing.maximalIdeal w.Ow).IsPrincipal := ⟨_, hπ⟩
  exact ((IsDiscreteValuationRing.TFAE w.Ow hnf).out 0 4).2 hpr
private theorem cutEquiv_symm (w : Place p R) (a : Op p R) :
    ((cutEquiv w).symm (Ideal.Quotient.mk _ a) : Op p R) = w.e * a := by
  have : (cutEquiv w).symm (Ideal.Quotient.mk _ a) = ⟨w.e * a, a, rfl⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨a, ?_⟩)
    show a * (1 - w.e) = a - w.e * a
    ring
  rw [this]
private theorem exists_basis [IsDedekindDomain R] [CharZero R] [Module.Free ℤ R]
    [Module.Finite ℤ R] (w : Place p R) :
    ∃ (α : Op p R) (b : Module.Basis
      (Fin (Module.finrank ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)))) ℤ_[p]
      (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))), ∀ k, (b k : Op p R) = w.e * α ^ (k : ℕ) := by
  obtain ⟨_, _⟩ := exists_dvr w
  have : Module.Free ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)) := inferInstance
  have : Module.Free ℤ_[p] w.Ow := Module.Free.of_equiv (cutEquiv w)
  have : IsLocalHom (algebraMap ℤ_[p] w.Ow) := Algebra.IsIntegral.isLocalHom _ _
  have : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv _ (PadicInt.residueField (p := p)).toEquiv.symm
  obtain ⟨θ, hθ⟩ : ∃ θ : w.Ow, Algebra.adjoin ℤ_[p] {θ} = ⊤ :=
    Formalism.L2.Pj.AvAlg.exists_adjoin_eq_top (FaithfulSMul.algebraMap_injective _ _)
  obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective θ
  let pb := PowerBasis.ofAdjoinEqTop' (Algebra.IsIntegral.isIntegral _) hθ
  have hg : pb.gen = Ideal.Quotient.mk _ α := by simp [pb]
  have hn : pb.dim = Module.finrank ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)) := by
    rw [(cutEquiv w).finrank_eq, pb.finrank]
  refine ⟨α, (pb.basis.map (cutEquiv w).symm).reindex (finCongr hn), fun k => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.map_apply, pb.basis_eq_pow, hg, ← map_pow,
    cutEquiv_symm]
  rfl
end SlopeTestRemainingChoices
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
end GlobalTheory.PlaceMono
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PlaceMono
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
namespace GlobalTheory.PlaceMono
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE), IsDomain ((ℤ_[p] ⊗[ℤ] OE) ⧸ Ideal.span {1 - w.e}) ∧ IsPrincipalIdealRing ((ℤ_[p] ⊗[ℤ] OE) ⧸ Ideal.span {1 - w.e}) ∧ ∃ (α : ℤ_[p] ⊗[ℤ] OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))), ∀ k, (b k : ℤ_[p] ⊗[ℤ] OE) = w.e * α ^ (k : ℕ) := by
  intro p _ OE _ _ _ _ _ w
  let w' : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p OE := ⟨w.e, w.idem, w.ne_zero, w.prim⟩
  obtain ⟨h1, h2⟩ := exists_dvr w'
  exact ⟨h1, h2.toIsPrincipalIdealRing, exists_basis w'⟩
end GlobalTheory.PlaceMono
