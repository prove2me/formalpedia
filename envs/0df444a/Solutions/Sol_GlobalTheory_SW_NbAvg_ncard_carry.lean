-- Prove2me | solution 1 for GlobalTheory.SW.NbAvg.ncard_carry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:11:00.204867+00:00
-- url     : https://prove2.me/submissions/51cc4bba-82f2-44fd-a645-49fe9c06e87c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ClassSumNb
import Theorems.Thm_GlobalTheory_SW_NbAvg_moves_unique
import Theorems.Thm_GlobalTheory_SW_NbAvg_transporter_eq
import Theorems.Thm_GlobalTheory_SW_NbAvg_mul_inj
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
theorem _root_.solution {M : ℕ} {P : Ideal (𝓞 E)} {A B : Lt E n} (hN : (Nb M P A).Finite)
    (hB : {h ∈ DH E n M | Moves h B B}.Finite) :
    (carry M P A B).ncard = (nbIn M P A B).ncard * {h ∈ DH E n M | Moves h B B}.ncard := by
  classical
  have memC : ∀ h, h ∈ carry M P A B ↔ h ∈ DH E n M ∧ ∃ X ∈ Nb M P A, Moves h B X :=
    fun _ => Iff.rfl
  have memN : ∀ X, X ∈ nbIn M P A B ↔ X ∈ Nb M P A ∧ ∃ h ∈ DH E n M, Moves h B X :=
    fun _ => Iff.rfl
  have hex : ∀ X ∈ nbIn M P A B, ∃ g ∈ DH E n M, Moves g B X := fun X hX => ((memN X).1 hX).2
  choose! g hg hgm using hex
  have hmv : ∀ X ∈ nbIn M P A B, ∀ k, Moves k B B → Moves (g X * k) B X := by
    intro X hX k mk v
    rw [mk v, hgm X hX (k *ᵥ v), Matrix.mulVec_mulVec]
  let F : Lt E n × Matrix (Fin n) (Fin n) E → Matrix (Fin n) (Fin n) E := fun p => g p.1 * p.2
  have himg : F '' (nbIn M P A B ×ˢ {h ∈ DH E n M | Moves h B B}) = carry M P A B := by
    ext h
    constructor
    · rintro ⟨⟨X, k⟩, ⟨hX, hk, mk⟩, rfl⟩
      exact (memC _).2 ⟨(eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq (hg X hX)).2 k hk, X, ((memN X).1 hX).1, hmv X hX k mk⟩
    · intro hh
      obtain ⟨hh, X, hXN, mh⟩ := (memC h).1 hh
      have hX : X ∈ nbIn M P A B := (memN X).2 ⟨hXN, h, hh, mh⟩
      obtain ⟨k, hk, rfl⟩ :=
        (Set.ext_iff.1 (transporter_eq (hg X hX) (hgm X hX)) h).1 ⟨hh, mh⟩
      exact ⟨(X, k), ⟨hX, hk⟩, rfl⟩
  have hinj : Set.InjOn F (nbIn M P A B ×ˢ {h ∈ DH E n M | Moves h B B}) := by
    rintro ⟨X, k⟩ ⟨hX, hk, mk⟩ ⟨Y, k'⟩ ⟨hY, hk', mk'⟩ e
    have e' : g X * k = g Y * k' := e
    have m1 := hmv X hX k mk
    have m2 := hmv Y hY k' mk'
    rw [e'] at m1
    have hXY : X = Y := moves_unique ((eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq (hg Y hY)).2 k' hk').1 m1 m2
    subst hXY
    exact Prod.ext rfl (mul_inj (hg X hX).1 e')
  rw [← himg, hinj.ncard_image, Set.ncard_prod]
end GlobalTheory.SW.NbAvg
