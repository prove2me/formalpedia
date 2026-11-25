-- Prove2me | solution 1 for GlobalTheory.ChF.eq_of_nv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:08:40.745151+00:00
-- url     : https://prove2.me/submissions/ae06d1c2-8bf3-48e6-8a02-ad4e73057413

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteTorsOfFiniteTorsion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSeriesEqOfEvalAtNilpotentPointsEq
import Theorems.Thm_GlobalTheory_evBasic_nEval_eq_tEval
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
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
private theorem coeff_box {A κ : Type} [CommRing A] [Fintype κ] [DecidableEq κ] (N : ℕ) (c : (κ →₀ ℕ) → A)
    (e : κ →₀ ℕ) (he : ∀ i, e i < N) :
    MvPowerSeries.coeff e (∑ b : κ → Fin N, MvPowerSeries.C (c (Finsupp.equivFunOnFinite.symm fun i => (b i : ℕ))) *
      ∏ i, (MvPowerSeries.X i : MvPowerSeries κ A) ^ (b i : ℕ)) = c e := by
  have hm : ∀ b : κ → ℕ, ∏ i, (MvPowerSeries.X i : MvPowerSeries κ A) ^ b i =
      MvPowerSeries.monomial (Finsupp.equivFunOnFinite.symm b) 1 := fun b => by
    rw [MvPowerSeries.monomial_one_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  have he' : (Finsupp.equivFunOnFinite.symm fun i => ((⟨e i, he i⟩ : Fin N) : ℕ)) = e := by
    ext i; rfl
  rw [map_sum, Finset.sum_eq_single (fun i => (⟨e i, he i⟩ : Fin N))]
  · rw [hm, MvPowerSeries.coeff_C_mul, he', MvPowerSeries.coeff_monomial_same, _root_.mul_one]
  · intro b _ hb
    rw [hm, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_monomial_ne, mul_zero]
    intro h
    exact hb (funext fun i => Fin.ext (by simp [h]))
  · simp
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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (I : Ideal R), IsHausdorff I R → ∀ (n d : ℕ) (f f' : PS R n d), (∀ (S : Type) [CommRing S] [Algebra R S] (k : ℕ), Kills I k S → (IsLocalRing R → I ≠ ⊤ → IsLocalRing S ∧ IsLocalHom (algebraMap R S)) → ∀ a : Fin n → Fin d → S, (∀ i j, IsNilpotent (a i j)) → nv (algebraMap R S) f a = nv (algebraMap R S) f' a) → f = f' := by
  intro R _ I hI n d f f' H
  ext e
  rw [← sub_eq_zero]
  refine hI.haus _ fun k => ?_
  rw [smul_eq_mul, Ideal.mul_top, SModEq.zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ k) ?_
  let A := R ⧸ I ^ (k + 1)
  let J : Ideal (MvPowerSeries (Fin n × Fin d) A) := lowZero e
  let N : ℕ := (∑ i, e i) + 1
  have he : ∀ i, e i < N := fun i =>
    Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have halg : ∀ t : R, algebraMap R (MvPowerSeries (Fin n × Fin d) A ⧸ J) t =
      Ideal.Quotient.mk J (MvPowerSeries.C (Ideal.Quotient.mk (I ^ (k + 1)) t)) := fun t => by
    rw [← Ideal.Quotient.mk_algebraMap, MvPowerSeries.algebraMap_apply]; rfl
  have hN : ∀ q : Fin n × Fin d, (Ideal.Quotient.mk J (MvPowerSeries.X q)) ^ N = 0 := fun q => by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    intro e' h
    exact (MvPowerSeries.X_pow_dvd_iff.1 dvd_rfl) e' (lt_of_le_of_lt (h q) (he q))
  have hv : ∀ g : PS R n d, nv (algebraMap R (MvPowerSeries (Fin n × Fin d) A ⧸ J)) g
      (fun i j => Ideal.Quotient.mk J (MvPowerSeries.X (i, j))) =
      Ideal.Quotient.mk J (∑ b : Fin n × Fin d → Fin N, MvPowerSeries.C ((fun x => Ideal.Quotient.mk (I ^ (k + 1))
        (MvPowerSeries.coeff x g)) (Finsupp.equivFunOnFinite.symm fun i => (b i : ℕ))) *
        ∏ i, (MvPowerSeries.X i : MvPowerSeries (Fin n × Fin d) A) ^ (b i : ℕ)) := fun g => by
    letI := (algebraMap R (MvPowerSeries (Fin n × Fin d) A ⧸ J)).toAlgebra
    refine (evBasic_nEval_eq_tEval g (fun q : Fin n × Fin d => Ideal.Quotient.mk J (MvPowerSeries.X q)) N hN).trans ?_
    simp only [tEval, map_sum, map_mul, map_prod, map_pow]
    exact Finset.sum_congr rfl fun b _ => congrArg (· * _) (halg _)
  have h := H (MvPowerSeries (Fin n × Fin d) A ⧸ J) k (fun t ht => by
      rw [halg, Ideal.Quotient.eq_zero_iff_mem.2 ht, map_zero, map_zero]) (fun hR hne => ?_)
    (fun i j => Ideal.Quotient.mk J (MvPowerSeries.X (i, j))) (fun i j => ⟨N, hN (i, j)⟩)
  · rw [hv, hv, Ideal.Quotient.eq] at h
    have h2 := h e le_rfl
    rw [map_sub, sub_eq_zero] at h2
    exact Ideal.Quotient.eq.1 (((coeff_box N (fun x => Ideal.Quotient.mk (I ^ (k + 1))
      (MvPowerSeries.coeff x f)) e he).symm.trans h2).trans (coeff_box N (fun x => Ideal.Quotient.mk (I ^ (k + 1))
      (MvPowerSeries.coeff x f')) e he))
  · have hA : I ^ (k + 1) ≠ ⊤ := fun h => hne (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero k)))
    haveI : Nontrivial A := Ideal.Quotient.nontrivial_iff.2 hA
    haveI : IsLocalRing A := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have hJ : J ≠ ⊤ := fun h => by
      have : (1 : MvPowerSeries (Fin n × Fin d) A) ∈ J := h ▸ Submodule.mem_top
      have := this 0 zero_le
      simp at this
    haveI : Nontrivial (MvPowerSeries (Fin n × Fin d) A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
    refine ⟨IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective, ⟨fun t ht => ?_⟩⟩
    rw [halg] at ht
    have h1 := (IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).map_nonunit _ ht
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_C] at h1
    exact (IsLocalHom.of_surjective (Ideal.Quotient.mk (I ^ (k + 1))) Ideal.Quotient.mk_surjective).map_nonunit _ h1
end GlobalTheory.ChF
