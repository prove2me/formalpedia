-- Prove2me | solution 1 for NumberField.PlaceDecomp.subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0d598487-29bd-5495-a161-48feeaae92a9

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_GroupCohomology_TateCohomology
import Theorems.Thm_NumberField_PlaceDecomp_decomp_eq_one_of_ramificationIdx_eq_one
import Theorems.Thm_NumberField_PlaceDecomp_subsingleton_tate_integerUnits_of_unramified
import Theorems.Thm_Rep_nonempty_tateCohomology_iso_add_two
import Theorems.Thm_NumberField_PlaceDecomp_isCyclic_decomp_of_ramificationIdx_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one

set_option autoImplicit false
p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_PlaceDecomp_subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one.NumberField"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one.NumberField.PlaceDecomp"

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_PlaceDecomp_subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one.NumberField CategoryTheory"

namespace NumberField
p2m_export "NumberField" "place PlaceDecomp.decomp PlaceDecomp.decomp_eq_one_of_ramificationIdx_eq_one PlaceDecomp.subsingleton_tate_integerUnits_of_unramified PlaceDecomp.isCyclic_decomp_of_ramificationIdx_eq_one"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp decomp_eq_one_of_ramificationIdx_eq_one subsingleton_tate_integerUnits_of_unramified isCyclic_decomp_of_ramificationIdx_eq_one"
namespace Ws25B1
p2m_open "NumberField.PlaceDecomp NumberField"

open CategoryTheory

theorem subsingleton_of_iso {k : Type} [CommRing k] {X Y : ModuleCat k} (e : X ≅ Y) [Subsingleton Y] : Subsingleton X :=
  e.toLinearEquiv.toEquiv.subsingleton

end NumberField.PlaceDecomp.Ws25B1

open NumberField.PlaceDecomp.Ws25B1 in
theorem solution (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (w : HeightOneSpectrum (𝓞 K))
    [Fintype (NumberField.PlaceDecomp.decomp E K w)]
    (hw : (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1) (q : ℤ) :
    Subsingleton ((Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletionIntegers K)ˣ).tateCohomology q) := by
  classical
  haveI : IsCyclic (NumberField.PlaceDecomp.decomp E K w) :=
    NumberField.PlaceDecomp.isCyclic_decomp_of_ramificationIdx_eq_one E K w hw
  have hur : ∀ σ : NumberField.PlaceDecomp.decomp E K w,
      (∀ a : w.adicCompletionIntegers K, σ • a - a ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers K)) → σ = 1 :=
    fun σ hσ => NumberField.PlaceDecomp.decomp_eq_one_of_ramificationIdx_eq_one E K w hw σ hσ
  obtain ⟨h0, h1⟩ := NumberField.PlaceDecomp.subsingleton_tate_integerUnits_of_unramified E K w hur

  letI : CommGroup (NumberField.PlaceDecomp.decomp E K w) := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := NumberField.PlaceDecomp.decomp E K w)
  have hper : ∀ q : ℤ, Subsingleton ((Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletionIntegers K)ˣ).tateCohomology q) ↔
      Subsingleton ((Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletionIntegers K)ˣ).tateCohomology (q + 2)) := by
    intro q
    obtain ⟨e⟩ := Rep.nonempty_tateCohomology_iso_add_two
      (Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletionIntegers K)ˣ) g hg q
    exact ⟨fun _ => subsingleton_of_iso e.symm, fun _ => subsingleton_of_iso e⟩

  have hP0 : Subsingleton ((Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletionIntegers K)ˣ).tateCohomology 0) := by
    rw [Rep.tateCohomology_zero]; exact h0
  have hPm1 : Subsingleton ((Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletionIntegers K)ˣ).tateCohomology (-1)) := by
    rw [Rep.tateCohomology_neg_one]; exact h1

  have hpos : ∀ n : ℕ, Subsingleton ((Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletionIntegers K)ˣ).tateCohomology (n : ℤ)) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => exact hP0
    | one => have := (hper (-1)).mp hPm1; simpa using this
    | more n ih _ =>
      have := (hper (n : ℤ)).mp ih
      push_cast
      exact this
  have hneg : ∀ n : ℕ, Subsingleton ((Rep.ofMulDistribMulAction (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletionIntegers K)ˣ).tateCohomology (-(n : ℤ) - 1)) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simpa using hPm1
    | one =>
      have := (hper (-2)).mpr (by simpa using hP0)
      simpa using this
    | more n ih _ =>
      have := (hper (-((n + 2 : ℕ) : ℤ) - 1)).mpr (by
        have e : -((n + 2 : ℕ) : ℤ) - 1 + 2 = -(n : ℤ) - 1 := by push_cast; ring
        rw [e]; exact ih)
      exact this
  rcases q with n | n
  · exact hpos n
  · rw [Int.negSucc_eq]
    have := hneg n
    rwa [show (-(n : ℤ) - 1) = -((n : ℤ) + 1) by ring] at this

end S_NumberField_PlaceDecomp_subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_NumberField_PlaceDecomp_subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one (solution)
