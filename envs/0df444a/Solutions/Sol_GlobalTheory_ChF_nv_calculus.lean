-- Prove2me | solution 1 for GlobalTheory.ChF.nv_calculus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:16:33.853974+00:00
-- url     : https://prove2.me/submissions/9f5189fc-0ecd-4baa-b45d-66d1a02a1563

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteTorsOfFiniteTorsion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
import Theorems.Thm_GlobalTheory_evBasic_exists_pow
import Theorems.Thm_GlobalTheory_evBasic_nEval_eq_tEval
import Theorems.Thm_GlobalTheory_evBasic_nEval_sub_coeff_mem
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
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
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
private theorem nv_eq_sum {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ} (f : PS R n d)
    (a : Fin n → Fin d → S) (N : ℕ) (hN : ∀ q : Fin n × Fin d, a q.1 q.2 ^ N = 0) :
    nv s f a = ∑ e : Fin n × Fin d → Fin N, s (MvPowerSeries.coeff
      (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)) f) * ∏ i, a i.1 i.2 ^ (e i : ℕ) := by
  letI := s.toAlgebra
  exact evBasic_nEval_eq_tEval f (fun q : Fin n × Fin d => a q.1 q.2) N hN
private theorem nEval_sqZero {R S κ : Type} [CommRing R] [CommRing S] [Algebra R S] [Fintype κ] [DecidableEq κ]
    (f : MvPowerSeries κ R) (a : κ → S) (ha : ∀ i, IsNilpotent (a i)) (h : ∀ i j, a i * a j = 0) :
    nEval f a = algebraMap R S (MvPowerSeries.constantCoeff f) +
      ∑ q, algebraMap R S (MvPowerSeries.coeff (Finsupp.single q 1) f) * a q := by
  have h0 : ∀ i : κ, IsNilpotent ((0 : κ → S) i) := fun _ => IsNilpotent.zero
  have hm : ∀ i, a i ∈ Ideal.span (Set.range a) := fun i => Ideal.subset_span ⟨i, rfl⟩
  have h1 := ChartCompare.nEval_sub_mem f a 0 ha h0 _ _ hm (fun _ => Ideal.zero_mem _)
    (fun i => by simpa using hm i)
  have h2 : Ideal.span (Set.range a) * Ideal.span (Set.range a) ≤ ⊥ := by
    rw [Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact h i j
  have h3 := (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; simp) : Ideal.span _ ≤ (⊥ : Ideal S))
    (evBasic_nEval_sub_coeff_mem f (0 : κ → S) h0)
  have h4 := h2 h1
  rw [Ideal.mem_bot, sub_eq_zero] at h3 h4
  rw [h3, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, sub_eq_iff_eq_add'] at h4
  simpa [Algebra.smul_def] using h4
end GlobalTheory.ChF
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (R S : Type) [CommRing R] [CommRing S] (s : R →+* S) (n d : ℕ) (a : Fin n → Fin d → S), (∀ i j, IsNilpotent (a i j)) → (∃ ψ : PS R n d →+* S, (∀ f, ψ f = nv s f a) ∧ (∀ c, ψ (MvPowerSeries.C c) = s c) ∧ ∀ q : Fin n × Fin d, ψ (MvPowerSeries.X q) = a q.1 q.2) ∧ (∀ f : PS R n d, MvPowerSeries.constantCoeff f = 0 → IsNilpotent (nv s f a) ∧ nv s f a ∈ Ideal.span (Set.range fun q : Fin n × Fin d => a q.1 q.2)) ∧ (∀ (m e : ℕ) (b : Fin m → Fin e → PS R n d) (f : PS R m e), (∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) → nv s (sub b f) a = nv s f (fun i j => nv s (b i j) a)) ∧ (∀ (R' : Type) [CommRing R'] (β : R' →+* R) (f : PS R' n d), nv (s.comp β) f a = nv s (MvPowerSeries.map β f) a) ∧ (∀ (S' : Type) [CommRing S'] (t : S →+* S') (f : PS R n d), t (nv s f a) = nv (t.comp s) f (fun i j => t (a i j))) ∧ ((∀ i j i' j', a i j * a i' j' = 0) → ∀ f : PS R n d, nv s f a = s (MvPowerSeries.constantCoeff f) + ∑ q : Fin n × Fin d, s (MvPowerSeries.coeff (Finsupp.single q 1) f) * a q.1 q.2) := by
  intro R S _ _ s n d a ha
  have ha' : ∀ q : Fin n × Fin d, IsNilpotent (a q.1 q.2) := fun q => ha _ _
  obtain ⟨N, -, hN⟩ := evBasic_exists_pow (fun q : Fin n × Fin d => a q.1 q.2) ha'
  letI := s.toAlgebra
  refine ⟨?_, fun f hf => ⟨ChartCompare.isNilpotent_nEval f hf _ ha', ?_⟩, fun m e b f hb => ?_,
    fun R' _ β f => ?_, fun S' _ t f => ?_,
    fun h f => nEval_sqZero f (fun q : Fin n × Fin d => a q.1 q.2) ha' fun _ _ => h _ _ _ _⟩
  · let ψ : PS R n d →+* S := (MvPowerSeries.constantCoeff : MvPowerSeries Empty S →+* S).comp
      (MvPowerSeries.substAlgHom (R := R) (ChartCompare.hasSubst_C _ ha')).toRingHom
    have hψ : ∀ f, ψ f = nv s f a := fun f => by
      simp [ψ, nv, MvPowerSeries.coe_substAlgHom, ChartCompare.subst_C_eq f _ ha']
    refine ⟨ψ, hψ, fun c => ?_, fun q => (hψ _).trans (ChartCompare.nEval_X _ ha' q)⟩
    have := (MvPowerSeries.substAlgHom (R := R) (ChartCompare.hasSubst_C _ ha')).commutes c
    exact (congrArg MvPowerSeries.constantCoeff this).trans (by
      rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.constantCoeff_C]; rfl)
  · have := evBasic_nEval_sub_coeff_mem f _ ha'
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, map_zero, sub_zero] at this
    exact this
  · exact ChartCompare.nEval_subst (fun q : Fin m × Fin e => b q.1 q.2) (fun q => hb _ _) f _ ha'
  · rw [nv_eq_sum _ _ a N hN, nv_eq_sum _ _ a N hN]
    simp only [MvPowerSeries.coeff_map, RingHom.comp_apply]
  · rw [nv_eq_sum _ _ a N hN, nv_eq_sum _ _ _ N (fun q => by rw [← map_pow, hN q, map_zero])]
    simp only [map_sum, map_mul, map_prod, map_pow, RingHom.comp_apply]
end GlobalTheory.ChF
