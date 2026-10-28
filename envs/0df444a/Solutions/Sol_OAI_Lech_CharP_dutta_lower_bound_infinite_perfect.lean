-- Prove2me | solution 1 for OAI.Lech.CharP.dutta_lower_bound_infinite_perfect
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:58:51.842963+00:00
-- url     : https://prove2.me/submissions/11a12218-5850-4238-8cc8-2dbd1192dc47

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L004
import Definitions.Def_OAIQ032L005
import Definitions.Def_OAIQ032L006
import Definitions.Def_OAIQ032L009
import Theorems.Thm_OAI_Lech_CharP_dutta_minimal_estimate
import Theorems.Thm_OAI_Lech_Primary_multiplicity_nonneg
import Theorems.Thm_OAI_Lech_nonminimal_complex_reduction

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedLengthPiece
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.Primary
open Filter
open scoped Topology
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] in
lemma maximal_multiplicity_eq :
    multiplicity (IsLocalRing.maximalIdeal R) = Lech.multiplicity R := rfl
end Lech.Primary


open CategoryTheory
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaData
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]


omit [IsNoetherianRing R] [IsLocalRing R] in
lemma IsShortComplex.finiteHomology [IsNoetherianRing R] [IsLocalRing R]
    {F : CochainComplex (ModuleCat.{u} R) ℤ}
    (hF : IsShortComplex R F) : IsFiniteHomologyComplex R F :=
  ⟨hF.term_free,hF.term_finite,hF.bounded,hF.homology_finite_length⟩


end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_MinimalComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
theorem exists_minimal_complex (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : IsFiniteHomologyComplex R F) :
    ∃ G : CochainComplex (ModuleCat.{u} R) ℤ,
      IsFiniteHomologyComplex R G ∧ IsMinimalComplex G ∧ Nonempty (HomotopyEquiv F G) := by
  classical
  have H (b : ℕ) : ∀ (F : CochainComplex (ModuleCat.{u} R) ℤ), complexRankSum F = b →
      IsFiniteHomologyComplex R F →
      ∃ G : CochainComplex (ModuleCat.{u} R) ℤ,
        IsFiniteHomologyComplex R G ∧ IsMinimalComplex G ∧ Nonempty (HomotopyEquiv F G) := by
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro F hb hF
      by_cases hm : IsMinimalComplex F
      · exact ⟨F,hF,hm,⟨HomotopyEquiv.refl F⟩⟩
      obtain ⟨G,hG,⟨e⟩,hsize⟩ := nonminimal_complex_reduction F hF hm
      obtain ⟨K,hK,hmK,⟨e'⟩⟩ := ih (complexRankSum G) (hb ▸ hsize) G rfl hG
      exact ⟨K,hK,hmK,⟨e.trans e'⟩⟩
  exact H _ F rfl hF

theorem IsShortComplex.exists_minimal {F : CochainComplex (ModuleCat.{u} R) ℤ}
    (hF : IsShortComplex R F) :
    ∃ G : CochainComplex (ModuleCat.{u} R) ℤ,
      IsShortComplex R G ∧ IsMinimalComplex G ∧ Nonempty (HomotopyEquiv F G) := by
  obtain ⟨G,hG,hm,⟨e⟩⟩ := exists_minimal_complex F hF.finiteHomology
  refine ⟨G,⟨hG.term_free,hG.term_finite,hG.bounded,hG.homology_finite_length,?_⟩,hm,⟨e⟩⟩
  intro hz
  exact hF.homology_zero_nonzero (hz.of_iso (e.toHomologyIso 0))

omit [IsLocalRing R] [IsNoetherianRing R]
lemma shortEuler_eq_of_homotopyEquiv {F G : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : HomotopyEquiv F G) : shortEuler R F = shortEuler R G := by
  unfold shortEuler
  apply Finset.sum_congr rfl
  intro j _
  rw [(e.toHomologyIso (-(j:ℤ))).toLinearEquiv.length_eq]

lemma duttaSequence_eq_of_homotopyEquiv (p : ℕ) [Fact p.Prime] [CharP R p]
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} (e : HomotopyEquiv F G) :
    duttaSequence R p F = duttaSequence R p G := by
  funext n
  unfold duttaSequence frobeniusComplex
  rw [shortEuler_eq_of_homotopyEquiv
    ((ModuleCat.extendScalars (iterateFrobenius R p n)).mapHomotopyEquiv e)]

lemma duttaMultiplicity_eq_of_homotopyEquiv (p : ℕ) [Fact p.Prime] [CharP R p]
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} (e : HomotopyEquiv F G) :
    duttaMultiplicity R p F = duttaMultiplicity R p G := by
  unfold duttaMultiplicity
  rw [duttaSequence_eq_of_homotopyEquiv p e]
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaEstimateLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Lech
lemma dutta_estimate_limit (p d c : ℕ) (hp : 1<p) (e A b B L : ℝ)
    (H : ∀ n : ℕ,c < p^n →
      e*((p^n-c:ℕ):ℝ)^d*(b-A/((p^n-c:ℕ):ℝ)*B) ≤ ((p:ℝ)^n)^d*L) :
    e*b ≤ L := by
  have hpR : 1<(p:ℝ) := by exact_mod_cast hp
  have hp0 : 0<(p:ℝ) := lt_trans zero_lt_one hpR
  have hq : Tendsto (fun n : ℕ => (p:ℝ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hpR
  have hqc : Tendsto (fun n : ℕ => (p:ℝ)^n-(c:ℝ)) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(c:ℝ)) hq
  have hr : Tendsto (fun n : ℕ => ((p:ℝ)^n-(c:ℝ))/(p:ℝ)^n) atTop (𝓝 1) := by
    have hh := (hq.const_div_atTop (c:ℝ)).const_sub 1
    simp only [sub_zero] at hh
    apply hh.congr
    intro n
    have hn : (p:ℝ)^n ≠ 0 := (pow_pos hp0 n).ne'
    field_simp
  have hh := ((hr.pow d).mul
    ((hqc.const_div_atTop A).mul_const B |>.const_sub b)).const_mul e
  simp only [one_pow,zero_mul,sub_zero,one_mul] at hh
  apply le_of_tendsto hh
  have hqn : Tendsto (fun n : ℕ => p^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hp
  filter_upwards [hqn.eventually_ge_atTop (c+1)] with n hn
  have hn' : c < p^n := by omega
  have hh := H n hn'
  rw [Nat.cast_sub hn'.le,Nat.cast_pow] at hh
  have heq : e*(((p:ℝ)^n-(c:ℝ))/(p:ℝ)^n)^d*(b-A/((p:ℝ)^n-(c:ℝ))*B) =
      (e*((p:ℝ)^n-(c:ℝ))^d*(b-A/((p:ℝ)^n-(c:ℝ))*B))/((p:ℝ)^n)^d := by
    rw [div_pow]
    ring
  change e*(_*_ ) ≤ L
  rw [← mul_assoc,heq]
  apply (div_le_iff₀ (pow_pos (pow_pos hp0 n) d)).mpr
  simpa only [mul_comm L] using hh
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaInfinitePerfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing
open scoped Topology
namespace Lech.CharP
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]
  [Infinite (ResidueField D)]

 

theorem dutta_lower_bound_infinite_perfect_oai (hd : 0 < dimension D)
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsShortComplex D F) :
    multiplicity D ≤ duttaMultiplicity D p F := by
  obtain ⟨G,hG,hm,⟨e⟩⟩ := hF.exists_minimal
  rw [duttaMultiplicity_eq_of_homotopyEquiv p e]
  obtain ⟨A,c,_,H⟩ := dutta_minimal_estimate D p hd G hG.finiteHomology hm
  have hbound := dutta_estimate_limit p (dimension D) c (Fact.out : p.Prime).one_lt
    (multiplicity D) A (Module.finrank D (G.X 0))
    (∑ i∈Finset.range (dimension D+1),(Module.finrank D (G.X (-(i:ℤ))):ℝ))
    (duttaMultiplicity D p G) H
  have hpos : 0 < Module.finrank D (G.X 0) := by
    let := hG.term_free 0
    let := hG.term_finite 0
    apply (Module.finrank_pos_iff_of_free D (G.X 0)).mpr
    apply not_subsingleton_iff_nontrivial.mp
    intro hh
    exact hG.homology_zero_nonzero
      (ExactAt.of_isZero (ModuleCat.isZero_iff_subsingleton.mpr hh)).isZero_homology
  have hposR : (1:ℝ) ≤ Module.finrank D (G.X 0) := by exact_mod_cast hpos
  have hepos : 0 ≤ multiplicity D := by
    rw [← Primary.maximal_multiplicity_eq]
    exact Primary.multiplicity_nonneg _ (Ideal.IsPrime.radical inferInstance)
  exact le_trans (by nlinarith) hbound
end Lech.CharP

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.CharP.dutta_lower_bound_infinite_perfect_oai.{u} := @OAI.Lech.CharP.dutta_lower_bound_infinite_perfect_oai.{u}
