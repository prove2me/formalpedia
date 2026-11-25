-- Prove2me | solution 1 for GlobalTheory.SW.NbAvg.ccT_mem_carry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:49:06.479981+00:00
-- url     : https://prove2.me/submissions/57aaeccd-c59d-4444-9a65-5f73242e2fbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ClassSumNb
import Theorems.Thm_GlobalTheory_SW_Nbr_move_inv
import Theorems.Thm_GlobalTheory_SW_finite_cls_and_stab
import Theorems.Thm_GlobalTheory_SW_neighbours

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
namespace GlobalTheory.SW
namespace NbAvg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
private theorem eq_one_of_mem_DH_zero {h : Matrix (Fin n) (Fin n) E} (hh : h ∈ DH E n 0) : h = 1 := by
  obtain ⟨-, s, -, hs, y, -, e⟩ := hh
  rw [(Nat.coprime_zero_right _).1 hs] at e
  simpa [sub_eq_zero] using e
private theorem eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq {M : ℕ} {g : Matrix (Fin n) (Fin n) E} (hg : g ∈ DH E n M) :
    ccT g ∈ DH E n M ∧ ∀ h ∈ DH E n M, g * h ∈ DH E n M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · obtain rfl := eq_one_of_mem_DH_zero hg
    refine ⟨?_, fun h hh => by rw [one_mul]; exact hh⟩
    have hc := hg.1
    rw [mul_one] at hc
    rw [hc]
    exact hg
  · exact (finite_cls_and_stab E n M hM).2.2.2.1.2 g hg
end NbAvg
end GlobalTheory.SW
end

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW
open GlobalTheory.SW.NbAvg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.SW.NbAvg
theorem _root_.solution {M q : ℕ} {P : Ideal (𝓞 E)} (hM : 0 < M) (hP : GoodPrime M q P)
    {A B : Lt E n} (hA : A ∈ Vset E n M) (hB : B ∈ Vset E n M) {h : Matrix (Fin n) (Fin n) E}
    (hh : h ∈ carry M P A B) : ccT h ∈ carry M (conjI P) B A := by
  obtain ⟨hh, X, hXN, mh⟩ := hh
  have hh' : h * ccT h = 1 := mul_eq_one_comm.1 hh.1
  have hc : ccT h ∈ DH E n M := (eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq hh).1
  obtain ⟨Y, -, mY⟩ := (finite_cls_and_stab E n M hM).2.2.2.2 (ccT h) hc A hA
  have hX : X ∈ Vset E n M := hXN.1
  obtain ⟨hgc, -, hnb⟩ := neighbours E n M q P hM hP
  have hAX : A ∈ Nb M (conjI P) X := ((hnb A hA).2.2.1 X hX).1 hXN
  have hequiv := ((neighbours E n M q (conjI P) hM hgc).2.2 X hX).2.2.2.2.2
  have hmXB : Moves (ccT h) X B := Nbr.move_inv hh' mh
  show ccT h ∈ DH E n M ∧ ∃ Y ∈ Nb M (conjI P) B, Moves (ccT h) A Y
  exact ⟨hc, Y, (hequiv (ccT h) hc B hB hmXB A Y mY).1 hAX, mY⟩
end GlobalTheory.SW.NbAvg
