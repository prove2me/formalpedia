-- Prove2me | solution 1 for GlobalTheory.SW.NbAvg.transporter_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:57:56.058966+00:00
-- url     : https://prove2.me/submissions/e83f79dd-bdd5-464d-b3da-5f58f1d3529c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ClassSumNb
import Theorems.Thm_GlobalTheory_SW_finite_cls_and_stab

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
theorem _root_.solution {M : ℕ} {g : Matrix (Fin n) (Fin n) E} (hg : g ∈ DH E n M) {B X : Lt E n}
    (m : Moves g B X) :
    {h ∈ DH E n M | Moves h B X} = (fun h => g * h) '' {h ∈ DH E n M | Moves h B B} := by
  have hgg : g * ccT g = 1 := mul_eq_one_comm.1 hg.1
  ext h
  constructor
  · rintro ⟨hh, mh⟩
    refine ⟨ccT g * h, ⟨(eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq (eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq hg).1).2 h hh, fun v => ?_⟩, ?_⟩
    · rw [mh v, m ((ccT g * h) *ᵥ v), Matrix.mulVec_mulVec, ← mul_assoc, hgg, one_mul]
    · show g * (ccT g * h) = h
      rw [← mul_assoc, hgg, one_mul]
  · rintro ⟨k, ⟨hk, mk⟩, rfl⟩
    refine ⟨(eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq hg).2 k hk, fun v => ?_⟩
    show v ∈ B ↔ (g * k) *ᵥ v ∈ X
    rw [mk v, m (k *ᵥ v), Matrix.mulVec_mulVec]
end GlobalTheory.SW.NbAvg
