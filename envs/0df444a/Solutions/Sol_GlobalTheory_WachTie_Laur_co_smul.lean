-- Prove2me | solution 1 for GlobalTheory.WachTie.Laur.co_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:27:41.096745+00:00
-- url     : https://prove2.me/submissions/975396e4-6947-40db-9a57-2e122a30ec74

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_GradedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfSumSmul
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GradedSeries_serMul_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open PowerSeries GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
namespace GlobalTheory.WachTie
namespace Laur
variable {L M M' : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']
private theorem coeff_ofPowerSeries_smul_eq_serMul (f : L⟦X⟧) (y : HahnModule ℤ L M) (k : ℤ) :
    ((HahnModule.of L).symm (HahnSeries.ofPowerSeries ℤ L f • y)).coeff k =
      serMul f ((HahnModule.of L).symm y).coeff k := by
  set F := HahnSeries.ofPowerSeries ℤ L f with hFdef
  have hF : ∀ j : ℕ, F.coeff (j : ℤ) = PowerSeries.coeff j f := fun j =>
    HahnSeries.ofPowerSeries_apply_coeff f j
  have hneg : ∀ i : ℤ, F.coeff i ≠ 0 → 0 ≤ i := by
    intro i hi
    by_contra hlt
    apply hi
    rw [hFdef, HahnSeries.ofPowerSeries_apply]
    apply HahnSeries.embDomain_notin_image_support
    rintro ⟨j, -, hj⟩
    change (j : ℤ) = i at hj
    omega
  have key : ∀ ij : ℤ × ℤ, F.coeff ij.1 ≠ 0 → ij.1 + ij.2 = k →
      ((ij.1.toNat : ℕ) : ℤ) = ij.1 ∧ k - ((ij.1.toNat : ℕ) : ℤ) = ij.2 := by
    intro ij h1 h3
    have := hneg _ h1
    constructor <;> omega
  have hlau : IsLaurent ((HahnModule.of L).symm y).coeff :=
    ⟨_, fun k hk => HahnSeries.coeff_eq_zero_of_lt_order hk⟩
  have hfin := serMul_finite f hlau k
  rw [HahnModule.coeff_smul]
  show _ = ∑ᶠ j : ℕ, PowerSeries.coeff j f • ((HahnModule.of L).symm y).coeff (k - (j : ℤ))
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by rw [Set.Finite.coe_toFinset])]
  apply Finset.sum_bij_ne_zero (fun ij _ _ => ij.1.toNat)
  · intro ij hij hne
    simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add] at hij
    obtain ⟨e1, e2⟩ := key ij hij.1 hij.2.2
    rw [Set.Finite.mem_toFinset, Function.mem_support, e2, ← hF, e1]
    exact hne
  · intro a ha _ b hb _ hab
    simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add] at ha hb
    obtain ⟨ea1, ea2⟩ := key a ha.1 ha.2.2
    obtain ⟨eb1, eb2⟩ := key b hb.1 hb.2.2
    apply Prod.ext <;> omega
  · intro j _ hne
    refine ⟨((j : ℤ), k - j), ?_, ?_, ?_⟩
    · simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add]
      refine ⟨?_, right_ne_zero_of_smul hne, by omega⟩
      rw [hF]
      exact left_ne_zero_of_smul hne
    · show F.coeff (j : ℤ) • ((HahnModule.of L).symm y).coeff (k - j) ≠ 0
      rw [hF]
      exact hne
    · show ((j : ℤ)).toNat = j
      simp
  · intro ij hij _
    simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add] at hij
    obtain ⟨e1, e2⟩ := key ij hij.1 hij.2.2
    show F.coeff ij.1 • ((HahnModule.of L).symm y).coeff ij.2 =
      PowerSeries.coeff ij.1.toNat f • ((HahnModule.of L).symm y).coeff (k - (ij.1.toNat : ℤ))
    rw [e2, ← hF, e1]
end Laur
end GlobalTheory.WachTie
end
end

set_option autoImplicit false
noncomputable section
open PowerSeries GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
open GlobalTheory GlobalTheory.WachTie
open GlobalTheory.WachTie.Laur
variable {L M M' : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']
namespace GlobalTheory.WachTie.Laur
theorem _root_.solution (f : L⟦X⟧) (x : Laur L M) : co (f • x) = serMul f (co x) := by
  funext k
  exact coeff_ofPowerSeries_smul_eq_serMul f x k
end GlobalTheory.WachTie.Laur
